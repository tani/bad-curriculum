import json
import tempfile
import unittest
from pathlib import Path

import torch

from bad_curriculum.config import ExperimentConfig
from bad_curriculum.cli import build_parser, write_order_only_audit
from bad_curriculum.data import (
    EncodedReviewDataset,
    Example,
    FrequentWordVocabulary,
    PAD_ID,
    SelectorPartition,
    build_anchor_counterexample_schedule,
    partition_selector_and_candidate_pools,
    select_balanced_source_examples,
)
from bad_curriculum.model import ARCHITECTURES, InversionLSTM, VanillaRNNClassifier, build_model
from bad_curriculum.optim import OPTIMIZERS, build_optimizer
from bad_curriculum.training import evaluate, make_loader, single_token_logit_gap, train_and_monitor, write_run_metadata


class CoreContractTests(unittest.TestCase):
    def test_vocabulary_reserves_padding_and_unknown_ids(self) -> None:
        vocab = FrequentWordVocabulary.fit(["excellent excellent", "terrible"], vocab_size=4)
        encoded = vocab.encode("excellent unseen", max_len=4)
        self.assertEqual(encoded.tolist(), [2, 1, PAD_ID, PAD_ID])
        self.assertEqual(vocab.size, 4)

    def test_model_uses_supplied_effective_lengths(self) -> None:
        model = InversionLSTM(vocab_size=8)
        logits = model(torch.tensor([[2, 3, 0], [4, 0, 0]]), torch.tensor([2, 1]))
        self.assertEqual(tuple(logits.shape), (2, 2))

    def test_every_architecture_produces_two_class_logits_with_gradients(self) -> None:
        input_ids = torch.tensor([[2, 3, 4, 0], [5, 6, 0, 0]])
        lengths = input_ids.ne(PAD_ID).sum(dim=1)
        labels = torch.tensor([0, 1])
        for architecture in ARCHITECTURES:
            with self.subTest(architecture=architecture):
                model = build_model(architecture, vocab_size=16, max_len=4)
                logits = model(input_ids, lengths)
                self.assertEqual(tuple(logits.shape), (2, 2))
                self.assertTrue(torch.isfinite(logits).all())
                torch.nn.functional.cross_entropy(logits, labels).backward()
                grads = [p.grad for p in model.parameters() if p.requires_grad]
                self.assertTrue(any(g is not None and torch.isfinite(g).all() for g in grads))

    def test_build_model_rejects_unknown_architecture(self) -> None:
        with self.assertRaisesRegex(ValueError, "unknown architecture"):
            build_model("mlp", vocab_size=16)

    def test_build_model_distinguishes_vanilla_rnn_and_lstm(self) -> None:
        self.assertIsInstance(build_model("rnn", vocab_size=16), VanillaRNNClassifier)
        self.assertIsInstance(build_model("lstm", vocab_size=16), InversionLSTM)

    def test_bag_and_mean_pool_models_ignore_token_order(self) -> None:
        input_ids = torch.tensor([[2, 3, 4, 0]])
        permuted = torch.tensor([[4, 2, 3, 0]])
        lengths = torch.tensor([3])
        for architecture in ("linear-fixed-features", "mean-pool-mlp"):
            with self.subTest(architecture=architecture):
                model = build_model(architecture, vocab_size=8, max_len=4).eval()
                self.assertTrue(torch.allclose(model(input_ids, lengths), model(permuted, lengths)))

    def test_gru_and_tcn_respect_effective_length(self) -> None:
        prefix = torch.tensor([[2, 3, 4, 0, 0]])
        changed_suffix = torch.tensor([[2, 3, 7, 6, 5]])
        lengths = torch.tensor([2])
        for architecture in ("gru", "tcn"):
            with self.subTest(architecture=architecture):
                model = build_model(architecture, vocab_size=8, max_len=5).eval()
                self.assertTrue(torch.allclose(model(prefix, lengths), model(changed_suffix, lengths)))

    def test_single_token_logit_gap_uses_model_output_space(self) -> None:
        model = InversionLSTM(vocab_size=5, emb_dim=3, hidden_dim=5)
        vocab = FrequentWordVocabulary({"excellent": 2})
        direct_logits = model(torch.tensor([[2]]), torch.tensor([1]))
        expected = (direct_logits[0, 1] - direct_logits[0, 0]).item()
        self.assertAlmostEqual(
            single_token_logit_gap(model, vocab, "excellent", torch.device("cpu")),
            expected,
        )

    def test_selector_partition_and_target_curriculum_are_disjoint(self) -> None:
        split = [
            {"text": f"review-{index}", "label": index % 2}
            for index in range(16)
        ]
        partition = partition_selector_and_candidate_pools(
            split, seed=7, selector_per_label=2, candidate_per_label=3
        )
        selector = set(partition.selector_training_indices)
        candidate = set(partition.candidate_reservoir_indices)
        holdout = set(partition.unused_holdout_indices)
        self.assertFalse(selector & candidate)
        self.assertFalse(selector & holdout)
        self.assertFalse(candidate & holdout)
        self.assertEqual(selector | candidate | holdout, set(range(len(split))))

        negative_tail = [index for index in candidate if split[index]["label"] == 0][:1]
        positive_tail = [index for index in candidate if split[index]["label"] == 1][:1]
        anchor, counterexample_tail = build_anchor_counterexample_schedule(
            split,
            partition.candidate_reservoir_indices,
            seed=8,
            hard_negative_indices=negative_tail,
            hard_positive_indices=positive_tail,
            anchor_size=2,
            tail_per_label=1,
        )
        target = anchor + counterexample_tail
        self.assertEqual(len(anchor), 2)
        self.assertEqual([example.label for example in counterexample_tail].count(0), 1)
        self.assertEqual([example.label for example in counterexample_tail].count(1), 1)
        self.assertEqual(len({example.index for example in target}), len(target))
        self.assertTrue({example.index for example in target} <= candidate)
        self.assertFalse({example.index for example in target} & selector)

    def test_clean_random_selector_preserves_balanced_source_labels(self) -> None:
        split = [
            {"text": "negative", "label": 0},
            {"text": "positive", "label": 1},
            {"text": "negative again", "label": 0},
            {"text": "positive again", "label": 1},
        ]
        selected = select_balanced_source_examples(split, 4, seed=4)
        self.assertEqual(sorted(example.label for example in selected), [0, 0, 1, 1])
        self.assertEqual({example.index for example in selected}, {0, 1, 2, 3})

    def test_run_metadata_records_curriculum_partition(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            config = ExperimentConfig(output_dir=Path(directory))
            partition = SelectorPartition((2,), (0, 1), ())
            anchor = Example(0, "excellent", 1, "anchor")
            counterexample_tail = Example(1, "terrible", 0, "counterexample_tail")
            write_run_metadata(
                config,
                torch.device("cpu"),
                FrequentWordVocabulary({"excellent": 2, "terrible": 3}),
                [anchor],
                [counterexample_tail],
                partition,
                "rnn",
                {"name": "SGD", "learning_rate": 0.08, "momentum": 0.95, "weight_decay": 0.0},
            )
            payload = json.loads((config.output_dir / "run.json").read_text())
            self.assertEqual(payload["training"]["model_architecture"], "rnn")
            self.assertEqual(payload["training"]["optimizer"]["name"], "SGD")
            self.assertEqual(payload["selection"]["profile"], "anchor_counterexample_order_only")
            self.assertEqual(payload["selection"]["anchor"], 1)
            self.assertEqual(payload["selection"]["counterexample_tail"], 1)
            self.assertEqual(payload["selection"]["selector_training"], 1)
            self.assertEqual(payload["selection"]["candidate_reservoir"], 2)

    def test_order_only_audit_records_shared_unique_source_events(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            config = ExperimentConfig(output_dir=Path(directory))
            train_split = [{"text": "negative", "label": 0}, {"text": "positive", "label": 1}]
            negative = Example(0, "negative", 0, "counterexample_tail")
            positive = Example(1, "positive", 1, "counterexample_tail")
            partition = SelectorPartition((), (0, 1), ())
            write_order_only_audit(
                config,
                [positive, negative],
                [negative, positive],
                train_split,
                partition,
                "vocabulary",
                "initial-state",
                {"name": "SGD", "learning_rate": 0.08, "momentum": 0.95, "weight_decay": 0.0},
            )
            payload = json.loads((config.output_dir / "order_only_audit.json").read_text())
            self.assertTrue(payload["same_event_multiset"])
            self.assertTrue(payload["source_labels_preserved"])
            self.assertEqual(payload["compared_schedules"], 2)
            self.assertEqual(payload["training_presentations"], 2)
            self.assertEqual(payload["unique_source_reviews"], 2)
            self.assertEqual(payload["repeated_presentations"], 0)
            self.assertTrue(payload["selector_target_disjoint"])
            self.assertTrue(payload["target_within_candidate_reservoir"])

    def test_order_only_audit_rejects_repeated_source_event(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            config = ExperimentConfig(output_dir=Path(directory))
            train_split = [{"text": "negative", "label": 0}]
            negative = Example(0, "negative", 0, "counterexample_tail")
            partition = SelectorPartition((), (0,), ())
            with self.assertRaisesRegex(AssertionError, "requires unique"):
                write_order_only_audit(
                    config,
                    [negative, negative],
                    [negative, negative],
                    train_split,
                    partition,
                    "vocabulary",
                    "initial-state",
                    {"name": "SGD", "learning_rate": 0.08, "momentum": 0.95, "weight_decay": 0.0},
                )

    def test_every_optimizer_name_builds_expected_hyperparameters(self) -> None:
        params = [torch.nn.Parameter(torch.zeros(1))]
        expectations = {
            "sgd": (torch.optim.SGD, {"momentum": 0.0, "lr": 0.08}),
            "momentum-sgd": (torch.optim.SGD, {"momentum": 0.95, "lr": 0.08}),
            "adam": (torch.optim.Adam, {"lr": 1e-3}),
            "adamw": (torch.optim.AdamW, {"lr": 1e-3}),
        }
        self.assertEqual(set(OPTIMIZERS), set(expectations))
        for name, (optimizer_type, expected) in expectations.items():
            with self.subTest(optimizer=name):
                optimizer = build_optimizer(name, params)
                self.assertIsInstance(optimizer, optimizer_type)
                group = optimizer.param_groups[0]
                for key, value in expected.items():
                    self.assertAlmostEqual(group[key], value)

    def test_build_optimizer_honors_explicit_learning_rate(self) -> None:
        params = [torch.nn.Parameter(torch.zeros(1))]
        optimizer = build_optimizer("adam", params, lr=0.5)
        self.assertAlmostEqual(optimizer.param_groups[0]["lr"], 0.5)

    def test_build_optimizer_rejects_unknown_name(self) -> None:
        params = [torch.nn.Parameter(torch.zeros(1))]
        with self.assertRaisesRegex(ValueError, "unknown optimizer"):
            build_optimizer("rmsprop", params)

    def test_cli_default_model_and_optimizer_reproduce_recorded_result_contract(self) -> None:
        args = build_parser().parse_args([])
        self.assertEqual(args.model, "lstm")
        self.assertEqual(args.optimizer, "momentum-sgd")
        self.assertIsNone(args.learning_rate)

    def test_evaluate_computes_accuracy_auc_confusion_via_torchmetrics(self) -> None:
        # Fixed logits chosen so half the predictions are correct, with a symmetric
        # score distribution giving a hand-computable AUC of exactly 0.5.
        fixed_logits = torch.tensor(
            [[2.0, -2.0], [-2.0, 2.0], [-2.0, 2.0], [2.0, -2.0]]
        )

        class _FixedLogitsModel(torch.nn.Module):
            def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
                del lengths
                return fixed_logits[: input_ids.size(0)]

        vocab = FrequentWordVocabulary.fit(["placeholder"], vocab_size=4)
        examples = [
            Example(0, "placeholder", 0, "test"),
            Example(1, "placeholder", 1, "test"),
            Example(2, "placeholder", 0, "test"),
            Example(3, "placeholder", 1, "test"),
        ]
        loader = make_loader(
            EncodedReviewDataset(examples, vocab, max_len=4), batch_size=4, shuffle=False, device=torch.device("cpu"), workers=0
        )
        result = evaluate(_FixedLogitsModel(), loader, torch.device("cpu"))
        self.assertAlmostEqual(result["test_accuracy"], 0.5)
        self.assertAlmostEqual(result["test_auc"], 0.5, places=3)
        self.assertEqual((result["c00"], result["c01"], result["c10"], result["c11"]), (1, 1, 1, 1))

    def test_train_and_monitor_produces_twenty_ordered_checkpoints_and_updates_parameters(self) -> None:
        vocab = FrequentWordVocabulary.fit(["excellent", "terrible", "movie", "plot"], vocab_size=8)
        examples = [
            Example(index, "excellent movie" if index % 2 == 0 else "terrible plot", index % 2, "anchor" if index < 20 else "counterexample_tail")
            for index in range(40)
        ]
        test_examples = [
            Example(index, "excellent movie" if index % 2 == 0 else "terrible plot", index % 2, "test")
            for index in range(8)
        ]
        device = torch.device("cpu")
        model = InversionLSTM(vocab_size=8, emb_dim=4, hidden_dim=4)
        initial_params = [parameter.detach().clone() for parameter in model.parameters()]
        train_loader = make_loader(
            EncodedReviewDataset(examples, vocab, max_len=4), batch_size=4, shuffle=False, device=device, workers=0
        )
        test_loader = make_loader(
            EncodedReviewDataset(test_examples, vocab, max_len=4), batch_size=4, shuffle=False, device=device, workers=0
        )
        optimizer = build_optimizer("sgd", model.parameters(), lr=0.5)
        rows = train_and_monitor("attack", model, examples, train_loader, test_loader, optimizer, vocab, device)
        self.assertEqual(len(rows), 20)
        self.assertEqual([row["checkpoint_pct"] for row in rows], list(range(5, 101, 5)))
        self.assertEqual(rows[-1]["processed_examples"], 40)
        self.assertEqual(rows[0]["segment"], "anchor")
        self.assertEqual(rows[-1]["segment"], "counterexample_tail")
        updated_params = list(model.parameters())
        self.assertTrue(
            any(not torch.equal(before, after) for before, after in zip(initial_params, updated_params)),
            "optimizer built outside the LightningModule did not update the wrapped model's parameters",
        )


if __name__ == "__main__":
    unittest.main()
