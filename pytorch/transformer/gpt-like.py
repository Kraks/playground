# https://brunomaga.github.io/GPT-lite

import torch
import torch.nn as nn
import torch.nn.functional as F

# random seed for reproducibility
torch.manual_seed(42)
device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
# how often to do an evaluation step
eval_interval = 100
# number of training iterations
max_iters = 500
# learning rate
learning_rate = 1e-4
# minibatch size, how many inputs to pack per iteration
batch_size = 3

# parameters specific to GPT
# E.g. for block_size 4 and input ABCD, we have training samples A->B, AB->C, ABC->C, ABCD->E
block_size = 8
# size of embeddings
n_embd = 16
# number of attention heads
n_head = 6
# depth of the network as number of decoder blocks
# each block contains a normalization, an attention, and a FF layer
n_layer = 6
# dropout rate
dropout = 0.2

# some better hyperparameters:
"""
eval_interval = 100
max_iters = 5000
learning_rate=3e-4
batch_size = 128
block_size = 256
n_embd = 300
n_layer = 10
dropout = 0.2
"""

## Tokenization

with open("input.txt") as f:
    text = f.read()

chars = sorted(list(set(text)))
stoi = { ch: i for i, ch in enumerate(chars) }
itos = { i: ch for i, ch in enumerate(chars) }
print(stoi)
print(itos)

# encode and decode functions that convert strings to arrays of tokens and vice-versa
encode = lambda x: torch.tensor([stoi[ch] for ch in x], dtype=torch.long)
decode = lambda x: "".join([itos[i] for i in x])
vocab_size = len(stoi)
print(f"Vocab size: {vocab_size}")

token_embedding_table = nn.Embedding(vocab_size, n_embd)    # from tokens to embedding
position_embedding_table = nn.Embedding(block_size, n_embd) # from position to embedding

# split data 90/10 as train/valid
data = encode(text)
n = int(0.9*len(data))
train_data, valid_data = data[:n], data[n:]

def get_batch(source):
  ix = torch.randint(len(source) - block_size, (batch_size,))
  x = torch.stack([source[i:i+block_size] for i in ix])
  y = torch.stack([source[i+1:i+1+block_size] for i in ix])
  return x.to(device), y.to(device)

xb, yb = get_batch(train_data)
print("input:\n",xb)
print("target:\n",yb)

for b in range(batch_size): #for every batches
  print(f"\n=== batch {b}:")
  for t in range(block_size): #for each sequence in block
    context = xb[b,:t+1]
    target = yb[b,t]
    print(f"for input {context.tolist()} target is {target.tolist()}")

## Multi-head masked attention

### Uniform attention:
# B - batch size
# T - input sequence length (block_size)
# C - embedding size (n_embd)
B, T, C = 4, 8, 2
x = torch.randn(B, T, C)

# compute an uniform attention matrix
# attention matrix (lower triangular), a mask used to only show previous items to predict next item
# wei = torch.tril(torch.ones((T, T), dtype=torch.float32, device=device))
#normalize mask so that it sums to one. use keepdim to make broadcast operation work later
# wei /= wei.sum(dim=-1, keepdim=True)

# alternatively:
tril = torch.tril(torch.ones(T,T))
wei = tril.masked_fill(tril==0, float('-inf'))
wei = F.softmax(wei, dim=-1) #equivalent to the normalization above
out = wei @ x

### Non-uniform attention:

head_size = 4
key = nn.Linear(C, head_size, bias=False)
query = nn.Linear(C, head_size, bias=False)
value = nn.Linear(C, head_size, bias=False)

# compute Attention(Q, K, V)
k = key(x)
q = query(x)
wei = q @ k.transpose(-2, -1) # (B, T, head_size) @ (B, head_size, T) = (B, T, T)
wei *= head_size ** -0.5
#print(wei)
# attention matrix:
tril = torch.tril(torch.ones(T,T))
wei = wei.masked_fill(tril==0, float('-inf'))
wei = F.softmax(wei, dim=-1)
v = value(x)
out = wei @ v
#print(out)

class Head(nn.Module):
  def __init__(self, head_size):
    super().__init__()
    self.key   = nn.Linear(n_embd, head_size, bias=False)
    self.query = nn.Linear(n_embd, head_size, bias=False)
    self.value = nn.Linear(n_embd, head_size, bias=False)
    self.register_buffer('tril', torch.tril(torch.ones(block_size, block_size)))
    self.dropout = nn.Dropout(dropout)
    #Note: this dropout randomly prevents some tokens from communicating with each other

  def forward(self, x):
    B,T,C = x.shape
    k = self.key(x) #shape (B,T, head_size)
    q = self.query(x) #shape (B,T, head_size)
    v = self.value(x) #shape (B,T, head_size)

    #compute self-attention scores
    wei = q @ k.transpose(-2, -1) #shape (B,T, head_size) @ (B,head_size,T) --> (B,T,T)
    wei *= C**-0.5 #scale by sqrt(d_k) as per paper, so that variance of the wei is 1
    wei = wei.masked_fill(self.tril[:T,:T]==0, float('-inf')) # (B,T,T)
    wei = F.softmax(wei, dim=-1) # (B, T, T)
    wei = self.dropout(wei)

    #perform weighted aggregation of values
    out = wei @ v # (B, T, T) @ (B, T, head_size) --> (B, T, head_size)
    return out

class MultiHeadAttention(nn.Module):
  """ Multi-head attention as a collection of heads with concatenated outputs."""
  def __init__(self, num_heads, head_size):
    super().__init__()
    self.heads = nn.ModuleList([Head(head_size) for _ in range(num_heads)])
    self.proj  = nn.Linear(head_size*num_heads, n_embd) # combine all head outputs
    self.dropout = nn.Dropout(dropout)

  def forward(self, x):
    out = torch.cat([head(x) for head in self.heads], dim=-1)
    out = self.proj(out)
    out = self.dropout(out)
    return out

## Feed Forward Network

class FeedForward(nn.Module):
  def __init__(self, n_embd):
    super().__init__()
    # Note: in the paper (section 3.3) we have d_{model}=512 and d_{ff}=2048.
    # Therefore the inner layer is 4 times the size of the embedding layer
    self.net = nn.Sequential(
        nn.Linear(n_embd, n_embd*4),
        nn.ReLU(),
        nn.Linear(n_embd*4, n_embd),
        nn.Dropout(dropout)
      )

  def forward(self, x): return self.net(x)

class Block(nn.Module):
  def __init__(self, n_embd, n_head):
    # n_embd: embedding dimension
    # n_heads : the number of heads we'd like to use
    super().__init__()
    head_size = n_embd // n_head
    self.sa = MultiHeadAttention(n_head, head_size)
    self.ffwd = FeedForward(n_embd)
    self.ln1 = nn.LayerNorm(n_embd)
    self.ln2 = nn.LayerNorm(n_embd)

  def forward(self, x):
    x = x + self.sa(self.ln1(x))
    x = x + self.ffwd(self.ln2(x))
    return x

class GPTlite(nn.Module):
  def __init__(self, vocab_size):
    super().__init__()
    # vocabulary embedding and positional embedding
    self.token_embedding_table = nn.Embedding(vocab_size, n_embd)
    self.position_embedding_table = nn.Embedding(block_size, n_embd)
    #sequence of attention heads and feed forward layers
    self.blocks = nn.Sequential( *[Block(n_embd, n_head) for _ in range(n_layer)])
    #one layer normalization layer after transformer blocks
    #and one before linear layer that outputs the vocabulary
    self.ln = nn.LayerNorm(n_embd)
    self.lm_head = nn.Linear(n_embd, vocab_size, bias=False)

  def forward(self, idx):
    """ call the model with idx and targets (training) or without targets (generation)"""
    #idx and targets are both of shape (B,T)
    B, T = idx.shape
    tok_emb = self.token_embedding_table(idx) #shape (B,T,C)
    pos_emb = self.position_embedding_table(torch.arange(T, device=idx.device)) #shape (T,C)
    x = tok_emb + pos_emb #shape (B,T,C)
    x = self.blocks(x)
    x = self.ln(x)
    logits = self.lm_head(x) #shape (B,T,C)
    logits = torch.swapaxes(logits, 1, 2) #shape (B,C,T) to comply with CrossEntropyLoss
    return logits

  def generate(self, idx, max_new_tokens):
    """ given a context idx, generate max_new_tokens tokens and append them to idx """
    idx = idx[:, -block_size:] #we can never have any idx longer than block_size
    for _ in range(max_new_tokens):
      idx_cond = idx[:, -block_size:] #we can never have any idx longer than block_size
      logits = self(idx_cond) #call fwd without targets
      logits = logits[:, :, -1] # take last token. from shape (B, C, T) to (B, C)
      #convert logits to probabilities
      probs = F.softmax(logits, dim=-1) # shape (B, C)
      #randomly sample the next tokens, 1 for each of the previous probability distributions
      #(one could take instead the argmax, but that would be deterministic and boring)
      idx_next = torch.multinomial(probs, num_samples=1) # shape (B, 1)
      #append next token ix to the solution sequence so far
      idx = torch.cat([idx, idx_next], dim=-1) # shape (B, T+1)
    return idx

m  = GPTlite(vocab_size).to(device)
print(m)
pytorch_total_params = sum(p.numel() for p in m.parameters())
print("Total number of all parameters:", pytorch_total_params)
pytorch_total_params = sum(p.numel() for p in m.parameters() if p.requires_grad)
print("Total number of trainable parameters:", pytorch_total_params)

# train the model
optimizer = torch.optim.Adam(m.parameters(), lr=learning_rate)
for steps in range(max_iters):
  idx, targets = get_batch(train_data)   #get a batch of training data
  logits = m(idx)   #forward pass
  loss = F.cross_entropy(logits, targets)
  loss.backward()   #backward pass
  optimizer.step()  #update parameters
  optimizer.zero_grad(set_to_none=True)  #sets to None instead of 0, to save memory

  #print progress
  if steps % 10 == 0: print(f"step {steps}, loss {loss.item():.2f}")

  @torch.no_grad()
  # eval loop: no backprop on this data, to avoid storing all intermediatte variables
  def eval_loss():
    idx, targets = get_batch(valid_data)   #get a batch of validation data
    logits = m(idx)   #forward pass
    loss = F.cross_entropy(logits, targets)
    print(f"step {steps}, eval loss {loss.item():.2f}")
    return loss

  if steps % eval_interval == 0: eval_loss().item()

print("A test run:")

#a 1x1 tensor with batch size 1 and sequence length 1 and starting value 0 (0 is the \n character)
idx = torch.zeros((1,1), dtype=torch.long, device=device)
idx = encode("hellojay").reshape(1, 8).to(device)
print(idx)
# test the same generate() function, now with the trained model
print("Output:")
print(decode(m.generate(idx, max_new_tokens=500).tolist()[0]))