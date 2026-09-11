import json
import tempfile
import unittest
from pathlib import Path

import torch

from bad_curriculum.config import ExperimentConfig
from bad_curriculum.cli import write_order_only_audit
from bad_curriculum.data import (
    Example,
    FrequentWordVocabulary,
    PAD_ID,
    SelectorPartition,
    build_anchor_counterexample_schedule,
    partition_selector_and_candidate_pools,
    select_balanced_source_examples,
)
from bad_curriculum.model import InversionLSTM
from bad_curriculum.training import single_token_logit_gap, write_run_metadata


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
            )
            payload = json.loads((config.output_dir / "run.json").read_text())
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


if __name__ == "__main__":
    unittest.main()
