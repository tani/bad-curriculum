import json
import tempfile
import unittest
from pathlib import Path

import torch

from yelp_inversion.config import ExperimentConfig
from yelp_inversion.data import Example, FrequentWordVocabulary, PAD_ID, select_balanced_source_examples
from yelp_inversion.model import InversionLSTM
from yelp_inversion.training import write_run_metadata


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

    def test_run_metadata_records_tail_policy(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            config = ExperimentConfig(output_dir=Path(directory), tail_policy="source_inversion")
            example = Example(0, "excellent", 1, "phase1")
            write_run_metadata(
                config,
                torch.device("cpu"),
                FrequentWordVocabulary({"excellent": 2}),
                [[example], [example], [example]],
            )
            payload = json.loads((config.output_dir / "run.json").read_text())
            self.assertEqual(payload["selection"]["tail_policy"], "source_inversion")


if __name__ == "__main__":
    unittest.main()
