import unittest

import torch

from yelp_inversion.data import FrequentWordVocabulary, PAD_ID
from yelp_inversion.model import InversionLSTM


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


if __name__ == "__main__":
    unittest.main()
