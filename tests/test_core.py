import json
import tempfile
import unittest
from pathlib import Path

import torch

from bad_curriculum.config import ExperimentConfig
from bad_curriculum.cli import write_order_only_audit
from bad_curriculum.data import Example, FrequentWordVocabulary, PAD_ID, select_balanced_source_examples
from bad_curriculum.model import InversionLSTM
from bad_curriculum.training import write_run_metadata


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

    def test_run_metadata_records_strict_profile(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            config = ExperimentConfig(output_dir=Path(directory))
            anchor = Example(0, "excellent", 1, "anchor")
            counterexample_tail = Example(1, "terrible", 0, "counterexample_tail")
            write_run_metadata(
                config,
                torch.device("cpu"),
                FrequentWordVocabulary({"excellent": 2, "terrible": 3}),
                [anchor],
                [counterexample_tail],
            )
            payload = json.loads((config.output_dir / "run.json").read_text())
            self.assertEqual(payload["selection"]["profile"], "anchor_counterexample_order_only")
            self.assertEqual(payload["selection"]["anchor"], 1)
            self.assertEqual(payload["selection"]["counterexample_tail"], 1)

    def test_order_only_audit_records_shared_unique_source_events(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            config = ExperimentConfig(output_dir=Path(directory))
            train_split = [{"text": "negative", "label": 0}, {"text": "positive", "label": 1}]
            negative = Example(0, "negative", 0, "counterexample_tail")
            positive = Example(1, "positive", 1, "counterexample_tail")
            write_order_only_audit(config, [positive, negative], [negative, positive], train_split)
            payload = json.loads((config.output_dir / "order_only_audit.json").read_text())
            self.assertTrue(payload["same_event_multiset"])
            self.assertTrue(payload["source_labels_preserved"])
            self.assertEqual(payload["compared_schedules"], 2)
            self.assertEqual(payload["training_presentations"], 2)
            self.assertEqual(payload["unique_source_reviews"], 2)
            self.assertEqual(payload["repeated_presentations"], 0)

    def test_order_only_audit_rejects_repeated_source_event(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            config = ExperimentConfig(output_dir=Path(directory))
            train_split = [{"text": "negative", "label": 0}]
            negative = Example(0, "negative", 0, "counterexample_tail")
            with self.assertRaisesRegex(AssertionError, "requires unique"):
                write_order_only_audit(config, [negative, negative], [negative, negative], train_split)


if __name__ == "__main__":
    unittest.main()
