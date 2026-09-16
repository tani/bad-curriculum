from __future__ import annotations

import math

import torch
import torch.nn as nn
from torch.nn.utils.rnn import pack_padded_sequence

from .data import PAD_ID

ARCHITECTURES: tuple[str, ...] = (
    "linear-fixed-features",
    "mean-pool-mlp",
    "cnn",
    "rnn",
    "gru",
    "lstm",
    "tcn",
    "gnn",
    "transformer-encoder",
    "transformer-decoder",
    "transformer-encoder-decoder",
)


class InversionLSTM(nn.Module):
    """Single-layer unidirectional LSTM classifier (the ``lstm`` architecture)."""

    def __init__(self, vocab_size: int = 30_000, emb_dim: int = 64, hidden_dim: int = 64):
        super().__init__()
        self.embedding = nn.Embedding(vocab_size, emb_dim, padding_idx=PAD_ID)
        self.lstm = nn.LSTM(emb_dim, hidden_dim, batch_first=True, bidirectional=False)
        self.classifier = nn.Linear(hidden_dim, 2)

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        embedded = self.embedding(input_ids)
        packed = pack_padded_sequence(embedded, lengths.cpu(), batch_first=True, enforce_sorted=False)
        _, (hidden, _) = self.lstm(packed)
        return self.classifier(hidden.squeeze(0))

class VanillaRNNClassifier(nn.Module):
    """Single-layer unidirectional Elman RNN classifier (the ``rnn`` architecture)."""

    def __init__(self, vocab_size: int = 30_000, emb_dim: int = 64, hidden_dim: int = 64):
        super().__init__()
        self.embedding = nn.Embedding(vocab_size, emb_dim, padding_idx=PAD_ID)
        self.rnn = nn.RNN(emb_dim, hidden_dim, batch_first=True, nonlinearity="tanh")
        self.classifier = nn.Linear(hidden_dim, 2)

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        embedded = self.embedding(input_ids)
        packed = pack_padded_sequence(embedded, lengths.cpu(), batch_first=True, enforce_sorted=False)
        _, hidden = self.rnn(packed)
        return self.classifier(hidden.squeeze(0))

class FixedFeatureLinearClassifier(nn.Module):
    """Linear classifier over non-trainable, normalized token-count features."""

    def __init__(self, vocab_size: int = 30_000):
        super().__init__()
        self.vocab_size = vocab_size
        self.classifier = nn.Linear(vocab_size, 2)

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        counts = torch.zeros(
            input_ids.size(0), self.vocab_size, device=input_ids.device, dtype=torch.float
        )
        valid = input_ids.ne(PAD_ID)
        counts.scatter_add_(1, input_ids, valid.to(dtype=counts.dtype))
        return self.classifier(counts / lengths.unsqueeze(1).to(dtype=counts.dtype))


class MeanPoolMLPClassifier(nn.Module):
    """Order-agnostic learned embedding mean-pool followed by a nonlinear MLP."""

    def __init__(self, vocab_size: int = 30_000, emb_dim: int = 64, hidden_dim: int = 64):
        super().__init__()
        self.embedding = nn.Embedding(vocab_size, emb_dim, padding_idx=PAD_ID)
        self.hidden = nn.Linear(emb_dim, hidden_dim)
        self.classifier = nn.Linear(hidden_dim, 2)

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        embedded = self.embedding(input_ids)
        valid = input_ids.ne(PAD_ID).unsqueeze(-1)
        pooled = (embedded * valid).sum(dim=1) / lengths.unsqueeze(1).to(dtype=embedded.dtype)
        return self.classifier(torch.relu(self.hidden(pooled)))


class GRUClassifier(nn.Module):
    """Single-layer unidirectional GRU classifier (the ``gru`` architecture)."""

    def __init__(self, vocab_size: int = 30_000, emb_dim: int = 64, hidden_dim: int = 64):
        super().__init__()
        self.embedding = nn.Embedding(vocab_size, emb_dim, padding_idx=PAD_ID)
        self.gru = nn.GRU(emb_dim, hidden_dim, batch_first=True, bidirectional=False)
        self.classifier = nn.Linear(hidden_dim, 2)

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        embedded = self.embedding(input_ids)
        packed = pack_padded_sequence(embedded, lengths.cpu(), batch_first=True, enforce_sorted=False)
        _, hidden = self.gru(packed)
        return self.classifier(hidden.squeeze(0))


class CNNClassifier(nn.Module):
    """TextCNN (Kim 2014): parallel wide convolutions over token embeddings, max-pooled."""

    def __init__(
        self,
        vocab_size: int = 30_000,
        emb_dim: int = 64,
        num_filters: int = 64,
        kernel_sizes: tuple[int, ...] = (3, 4, 5),
    ):
        super().__init__()
        self.embedding = nn.Embedding(vocab_size, emb_dim, padding_idx=PAD_ID)
        self.convs = nn.ModuleList(
            nn.Conv1d(emb_dim, num_filters, kernel_size, padding=kernel_size // 2)
            for kernel_size in kernel_sizes
        )
        self.classifier = nn.Linear(num_filters * len(kernel_sizes), 2)

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        del lengths
        seq_len = input_ids.size(1)
        embedded = self.embedding(input_ids).transpose(1, 2)  # [B, E, L]
        valid = input_ids.ne(PAD_ID).unsqueeze(1)  # [B, 1, L]
        pooled = []
        for conv in self.convs:
            activated = torch.relu(conv(embedded))[..., :seq_len]  # [B, F, L]
            masked = activated.masked_fill(~valid, float("-inf"))
            pooled.append(masked.max(dim=2).values)
        return self.classifier(torch.cat(pooled, dim=1))


class _DilatedResidualBlock(nn.Module):
    """Two causal convolutions followed by an identity residual connection."""

    def __init__(self, channels: int, dilation: int, kernel_size: int = 3):
        super().__init__()
        padding = (kernel_size - 1) * dilation
        self.conv1 = nn.Conv1d(channels, channels, kernel_size, padding=padding, dilation=dilation)
        self.conv2 = nn.Conv1d(channels, channels, kernel_size, padding=padding, dilation=dilation)

    @staticmethod
    def _causal(conv: nn.Conv1d, inputs: torch.Tensor) -> torch.Tensor:
        return conv(inputs)[..., : inputs.size(-1)]

    def forward(self, inputs: torch.Tensor) -> torch.Tensor:
        hidden = torch.relu(self._causal(self.conv1, inputs))
        hidden = torch.relu(self._causal(self.conv2, hidden))
        return torch.relu(inputs + hidden)


class TCNClassifier(nn.Module):
    """Dilated causal residual temporal convolutional network (the ``tcn`` architecture)."""

    def __init__(
        self,
        vocab_size: int = 30_000,
        emb_dim: int = 64,
        dilations: tuple[int, ...] = (1, 2, 4, 8),
    ):
        super().__init__()
        self.embedding = nn.Embedding(vocab_size, emb_dim, padding_idx=PAD_ID)
        self.blocks = nn.ModuleList(_DilatedResidualBlock(emb_dim, dilation) for dilation in dilations)
        self.classifier = nn.Linear(emb_dim, 2)

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        batch, seq_len = input_ids.shape
        hidden = self.embedding(input_ids).transpose(1, 2)
        for block in self.blocks:
            hidden = block(hidden)
        hidden = hidden.transpose(1, 2)
        last_index = (lengths - 1).clamp(min=0, max=seq_len - 1)
        pooled = hidden[torch.arange(batch, device=input_ids.device), last_index]
        return self.classifier(pooled)


class GNNClassifier(nn.Module):
    """Graph convolutional network over a per-review sliding-window token graph."""

    def __init__(
        self,
        vocab_size: int = 30_000,
        emb_dim: int = 64,
        hidden_dim: int = 64,
        num_layers: int = 2,
        window: int = 2,
    ):
        super().__init__()
        self.embedding = nn.Embedding(vocab_size, emb_dim, padding_idx=PAD_ID)
        self.window = window
        dims = [emb_dim] + [hidden_dim] * num_layers
        self.layers = nn.ModuleList(nn.Linear(dims[i], dims[i + 1]) for i in range(num_layers))
        self.classifier = nn.Linear(hidden_dim, 2)

    def _normalized_adjacency(self, input_ids: torch.Tensor) -> torch.Tensor:
        """Row-normalized adjacency of a chain-window graph with self-loops on real tokens."""
        batch, seq_len = input_ids.shape
        device = input_ids.device
        valid = input_ids.ne(PAD_ID)  # [B, L]
        positions = torch.arange(seq_len, device=device)
        offset = (positions.unsqueeze(0) - positions.unsqueeze(1)).abs()
        window_edges = (offset >= 1) & (offset <= self.window)  # [L, L]
        node_pairs_valid = valid.unsqueeze(1) & valid.unsqueeze(2)  # [B, L, L]
        adjacency = window_edges.unsqueeze(0) & node_pairs_valid
        self_loops = torch.eye(seq_len, device=device, dtype=torch.bool).unsqueeze(0) & valid.unsqueeze(1)
        adjacency = (adjacency | self_loops).float()
        degree = adjacency.sum(dim=-1, keepdim=True).clamp_min(1.0)
        return adjacency / degree

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        del lengths
        adjacency = self._normalized_adjacency(input_ids)
        hidden = self.embedding(input_ids)
        for layer in self.layers:
            hidden = torch.relu(layer(torch.bmm(adjacency, hidden)))
        valid = input_ids.ne(PAD_ID).unsqueeze(-1).float()
        pooled = (hidden * valid).sum(dim=1) / valid.sum(dim=1).clamp_min(1.0)
        return self.classifier(pooled)


class _SinusoidalPositions(nn.Module):
    """Fixed sinusoidal position table, shared by every transformer variant."""

    def __init__(self, max_len: int, emb_dim: int):
        super().__init__()
        position = torch.arange(max_len).unsqueeze(1)
        div_term = torch.exp(torch.arange(0, emb_dim, 2) * (-math.log(10_000.0) / emb_dim))
        table = torch.zeros(max_len, emb_dim)
        table[:, 0::2] = torch.sin(position * div_term)
        table[:, 1::2] = torch.cos(position * div_term)
        self.register_buffer("table", table, persistent=False)

    def forward(self, length: int) -> torch.Tensor:
        return self.table[:length]


class TransformerEncoderClassifier(nn.Module):
    """Bidirectional transformer encoder with a prepended [CLS] token."""

    def __init__(
        self,
        vocab_size: int = 30_000,
        emb_dim: int = 64,
        nhead: int = 4,
        num_layers: int = 2,
        dim_feedforward: int = 128,
        max_len: int = 128,
    ):
        super().__init__()
        self.embedding = nn.Embedding(vocab_size, emb_dim, padding_idx=PAD_ID)
        self.cls_token = nn.Parameter(torch.zeros(1, 1, emb_dim))
        self.positions = _SinusoidalPositions(max_len + 1, emb_dim)
        layer = nn.TransformerEncoderLayer(
            d_model=emb_dim, nhead=nhead, dim_feedforward=dim_feedforward, batch_first=True
        )
        self.encoder = nn.TransformerEncoder(layer, num_layers=num_layers)
        self.classifier = nn.Linear(emb_dim, 2)

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        del lengths
        batch = input_ids.size(0)
        embedded = self.embedding(input_ids)
        tokens = torch.cat([self.cls_token.expand(batch, -1, -1), embedded], dim=1)
        tokens = tokens + self.positions(tokens.size(1))
        cls_mask = torch.zeros(batch, 1, dtype=torch.bool, device=input_ids.device)
        padding_mask = torch.cat([cls_mask, input_ids.eq(PAD_ID)], dim=1)
        encoded = self.encoder(tokens, src_key_padding_mask=padding_mask)
        return self.classifier(encoded[:, 0])


class TransformerDecoderClassifier(nn.Module):
    """Causal (GPT-style) decoder-only transformer, classified from the last real token."""

    def __init__(
        self,
        vocab_size: int = 30_000,
        emb_dim: int = 64,
        nhead: int = 4,
        num_layers: int = 2,
        dim_feedforward: int = 128,
        max_len: int = 128,
    ):
        super().__init__()
        self.embedding = nn.Embedding(vocab_size, emb_dim, padding_idx=PAD_ID)
        self.positions = _SinusoidalPositions(max_len, emb_dim)
        layer = nn.TransformerEncoderLayer(
            d_model=emb_dim, nhead=nhead, dim_feedforward=dim_feedforward, batch_first=True
        )
        self.decoder = nn.TransformerEncoder(layer, num_layers=num_layers)
        self.classifier = nn.Linear(emb_dim, 2)

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        batch, seq_len = input_ids.shape
        tokens = self.embedding(input_ids) + self.positions(seq_len)
        causal_mask = torch.triu(
            torch.ones(seq_len, seq_len, dtype=torch.bool, device=input_ids.device), diagonal=1
        )
        padding_mask = input_ids.eq(PAD_ID)
        encoded = self.decoder(tokens, mask=causal_mask, src_key_padding_mask=padding_mask)
        last_index = (lengths - 1).clamp(min=0, max=seq_len - 1)
        pooled = encoded[torch.arange(batch, device=input_ids.device), last_index]
        return self.classifier(pooled)


class TransformerEncoderDecoderClassifier(nn.Module):
    """Full encoder-decoder transformer: a learned query cross-attends to encoded tokens."""

    def __init__(
        self,
        vocab_size: int = 30_000,
        emb_dim: int = 64,
        nhead: int = 4,
        num_encoder_layers: int = 2,
        num_decoder_layers: int = 2,
        dim_feedforward: int = 128,
        max_len: int = 128,
    ):
        super().__init__()
        self.embedding = nn.Embedding(vocab_size, emb_dim, padding_idx=PAD_ID)
        self.positions = _SinusoidalPositions(max_len, emb_dim)
        self.query = nn.Parameter(torch.zeros(1, 1, emb_dim))
        encoder_layer = nn.TransformerEncoderLayer(
            d_model=emb_dim, nhead=nhead, dim_feedforward=dim_feedforward, batch_first=True
        )
        self.encoder = nn.TransformerEncoder(encoder_layer, num_layers=num_encoder_layers)
        decoder_layer = nn.TransformerDecoderLayer(
            d_model=emb_dim, nhead=nhead, dim_feedforward=dim_feedforward, batch_first=True
        )
        self.decoder = nn.TransformerDecoder(decoder_layer, num_layers=num_decoder_layers)
        self.classifier = nn.Linear(emb_dim, 2)

    def forward(self, input_ids: torch.Tensor, lengths: torch.Tensor) -> torch.Tensor:
        del lengths
        batch, seq_len = input_ids.shape
        tokens = self.embedding(input_ids) + self.positions(seq_len)
        padding_mask = input_ids.eq(PAD_ID)
        memory = self.encoder(tokens, src_key_padding_mask=padding_mask)
        decoded = self.decoder(
            self.query.expand(batch, -1, -1), memory, memory_key_padding_mask=padding_mask
        )
        return self.classifier(decoded[:, 0])


def build_model(architecture: str, vocab_size: int = 30_000, max_len: int = 128) -> nn.Module:
    """Construct one of the eleven ``ARCHITECTURES`` target models by name."""
    if architecture == "linear-fixed-features":
        return FixedFeatureLinearClassifier(vocab_size=vocab_size)
    if architecture == "mean-pool-mlp":
        return MeanPoolMLPClassifier(vocab_size=vocab_size)
    if architecture == "cnn":
        return CNNClassifier(vocab_size=vocab_size)
    if architecture == "rnn":
        return VanillaRNNClassifier(vocab_size=vocab_size)
    if architecture == "gru":
        return GRUClassifier(vocab_size=vocab_size)
    if architecture == "lstm":
        return InversionLSTM(vocab_size=vocab_size)
    if architecture == "tcn":
        return TCNClassifier(vocab_size=vocab_size)
    if architecture == "gnn":
        return GNNClassifier(vocab_size=vocab_size)
    if architecture == "transformer-encoder":
        return TransformerEncoderClassifier(vocab_size=vocab_size, max_len=max_len)
    if architecture == "transformer-decoder":
        return TransformerDecoderClassifier(vocab_size=vocab_size, max_len=max_len)
    if architecture == "transformer-encoder-decoder":
        return TransformerEncoderDecoderClassifier(vocab_size=vocab_size, max_len=max_len)
    raise ValueError(f"unknown architecture {architecture!r}; choose one of {ARCHITECTURES}")
