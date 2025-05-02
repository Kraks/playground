# https://www.datacamp.com/tutorial/building-a-transformer-with-py-torch

import torch
import torch.nn as nn
import torch.optim as optim
import torch.utils.data as data
import math
import copy

class MultiHeadAttention(nn.Module):
  def __init__(self, d_model, num_heads):
    # d_model: dim of the input
    super(MultiHeadAttention, self).__init__()
    assert d_model % num_heads == 0, "d_model must be divisible by num_heads"
    self.d_model = d_model
    self.num_heads = num_heads
    self.d_k = d_model // num_heads # dim of each head's key, query, and value
    self.W_q = nn.Linear(d_model, d_model)
    self.W_k = nn.Linear(d_model, d_model)
    self.W_v = nn.Linear(d_model, d_model)
    self.W_o = nn.Linear(d_model, d_model)

  def scaled_dot_product_attention(self, Q, K, V, mask=None):
    # XXX: why transpose(-2, -1)
    attn_scores = torch.matmul(Q, K.transpose(-2, -1)) / math.sqrt(self.d_k)
    # apply mask (useful for preventing attention to certain parts like padding)
    if mask is not None:
      attn_scores = attn_scores.masked_fill(mask == 0, -1e9)
    attn_probs = torch.softmax(attn_scores, dim=-1)
    output = torch.matmul(attn_probs, V)
    return output

  def split_heads(self, x):
    # XXX: what is x?
    # reshape the input to num_heads for multi-head attention
    batch_size, seq_length, d_model = x.size()
    return x.view(batch_size, seq_length, self.num_heads, self.d_k).transpose(1, 2)

  def combine_heads(self, x):
    # combine the multiple heads back to original shape
    batch_size, num_heads, seq_length, d_k = x.size()
    return x.transpose(1, 2).contiguous().view(batch_size, seq_length, self.d_model)

  def forward(self, Q, K, V, mask=None):
    Q = self.split_heads(self.W_q(Q))
    K = self.split_heads(self.W_k(K))
    V = self.split_heads(self.W_v(V))
    attn_output = self.scaled_dot_product_attention(Q, K, V, mask)
    output = self.W_o(self.combine_heads(attn_output))
    return output

class PositionWiseFeedForward(nn.Module):
  def __init__(self, d_model, d_ff):
    # d_ff: dim of the inner layer
    super(PositionWiseFeedForward, self).__init__()
    self.fc1 = nn.Linear(d_model, d_ff)
    self.fc2 = nn.Linear(d_ff, d_model)
    self.relu = nn.ReLU()
  def forward(self, x):
    return self.fc2(self.relu(self.fc1(x)))

# inject position info of each token
class PositionalEncoding(nn.Module):
  def __init__(self, d_model, max_seq_length):
    super(PositionalEncoding, self).__init__()
    pe = torch.zeros(max_seq_length, d_model)
    pos = torch.arange(0, max_seq_length, dtype=torch.float).unsqueeze(1)
    div_term = torch.exp(torch.arange(0, d_model, 2).float() * -(math.log(10000.0) / d_model))
    pe[:, 0::2] = torch.sin(pos * div_term)
    pe[:, 1::2] = torch.cos(pos * div_term)
    self.register_buffer('pe', pe.unsqueeze(0))
  def forward(self, x):
    # XXX: :x.size(1)?
    return x + self.pe[:, :x.size(1)]

class EncoderLayer(nn.Module):
  def __init__(self, d_model, num_heads, d_ff, dropout):
    super(EncoderLayer, self).__init__()
    self.self_attn = MultiHeadAttention(d_model, num_heads)
    self.feed_forward = PositionWiseFeedForward(d_model, d_ff)
    self.norm1 = nn.LayerNorm(d_model)
    self.norm2 = nn.LayerNorm(d_model)
    self.dropout = nn.Dropout(dropout)
  def forward(self, x, mask):
    attn_output = self.self_attn(x, x, x, mask)
    x = self.norm1(x + self.dropout(attn_output))
    ff_output = self.feed_forward(x)
    x = self.norm2(x + self.dropout(ff_output))
    return x

class DecoderLayer(nn.Module):
  def __init__(self, d_model, num_heads, d_ff, dropout):
    super(DecoderLayer, self).__init__()
    self.self_attn = MultiHeadAttention(d_model, num_heads)
    self.cross_attn = MultiHeadAttention(d_model, num_heads)
    self.feed_forward = PositionWiseFeedForward(d_model, d_ff)
    self.norm1 = nn.LayerNorm(d_model)
    self.norm2 = nn.LayerNorm(d_model)
    self.norm3 = nn.LayerNorm(d_model)
    self.dropout = nn.Dropout(dropout)
  def forward(self, x, enc_output, src_mask, tgt_mask):
    attn_output = self.self_attn(x, x, x, tgt_mask)
    x = self.norm1(x + self.dropout(attn_output))
    attn_output = self.cross_attn(x, enc_output, enc_output, src_mask)
    x = self.norm2(x + self.dropout(attn_output))
    ff_output = self.feed_forward(x)
    x = self.norm3(x + self.dropout(ff_output))
    return x

class Transformer(nn.Module):
  def __init__(self, src_vocab_size, tgt_vocab_size, d_model, num_heads,
              num_layers, d_ff, max_seq_length, dropout):
    super(Transformer, self).__init__()
    self.encoder_embedding = nn.Embedding(src_vocab_size, d_model)
    self.decoder_embedding = nn.Embedding(tgt_vocab_size, d_model)
    self.positional_encoding = PositionalEncoding(d_model, max_seq_length)
    self.encoder_layers = nn.ModuleList([EncoderLayer(d_model, num_heads, d_ff, dropout) for _ in range(num_layers)])
    self.decoder_layers = nn.ModuleList([DecoderLayer(d_model, num_heads, d_ff, dropout) for _ in range(num_layers)])
    self.fc = nn.Linear(d_model, tgt_vocab_size)
    self.dropout = nn.Dropout(dropout)
  def generate_mask(self, src, tgt):
    # create masks for the source/target sequences, so that padding tokens are ignored
    # and future tokens are not visible during training
    src_mask = (src != 0).unsqueeze(1).unsqueeze(2) # XXX: what does it mean?
    tgt_mask = (tgt != 0).unsqueeze(1).unsqueeze(2)
    seq_length = tgt.size(1)
    nopeak_mask = (1 - torch.triu(torch.ones(1, seq_length, seq_length), diagonal=1)).bool() # XXX: what does it mean?
    tgt_mask = tgt_mask & nopeak_mask
    return src_mask, tgt_mask
  def forward(self, src, tgt):
    # XXX: what is really tgt???
    src_mask, tgt_mask = self.generate_mask(src, tgt)
    src_embedding = self.dropout(self.positional_encoding(self.encoder_embedding(src)))
    tgt_embedding = self.dropout(self.positional_encoding(self.decoder_embedding(tgt)))
    enc_output = src_embedding
    for layer in self.encoder_layers:
      enc_output = layer(enc_output, src_mask)
    dec_output = tgt_embedding
    for layer in self.decoder_layers:
      dec_output = layer(dec_output, enc_output, src_mask, tgt_mask)
    output = self.fc(dec_output)
    return output

# train the model

src_vocab_size = 5000
tgt_vocab_size = 5000
d_model = 512
num_heads = 8
num_layers = 6
d_ff = 2048
max_seq_length = 100
dropout = 0.1

transformer = Transformer(src_vocab_size, tgt_vocab_size, d_model, num_heads, num_layers, d_ff, max_seq_length, dropout)

# Generate random sample data
src_data = torch.randint(1, src_vocab_size, (64, max_seq_length))  # (batch_size, seq_length)
tgt_data = torch.randint(1, tgt_vocab_size, (64, max_seq_length))  # (batch_size, seq_length)

criterion = nn.CrossEntropyLoss(ignore_index=0)
optimizer = optim.Adam(transformer.parameters(), lr=0.0001, betas=(0.9, 0.98), eps=1e-9)

transformer.train()

for epoch in range(20):
    optimizer.zero_grad()
    output = transformer(src_data, tgt_data[:, :-1]) # XXX why ignoring the last one?
    loss = criterion(output.contiguous().view(-1, tgt_vocab_size), tgt_data[:, 1:].contiguous().view(-1))
    loss.backward()
    optimizer.step()
    print(f"Epoch: {epoch+1}, Loss: {loss.item()}")

transformer.eval()

# Generate random sample validation data
val_src_data = torch.randint(1, src_vocab_size, (64, max_seq_length))  # (batch_size, seq_length)
val_tgt_data = torch.randint(1, tgt_vocab_size, (64, max_seq_length))  # (batch_size, seq_length)

with torch.no_grad():
  val_output = transformer(val_src_data, val_tgt_data[:, :-1])
  print(f"Validation Output: {val_output.contiguous().view(-1, tgt_vocab_size)}")
  print(f"Validation Target: {val_tgt_data[:, 1:].contiguous().view(-1)}")
  val_loss = criterion(val_output.contiguous().view(-1, tgt_vocab_size), val_tgt_data[:, 1:].contiguous().view(-1))
  print(f"Validation Loss: {val_loss.item()}")
