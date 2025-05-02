# demonstrating user-defined autograd functions

import torch
import math

class LegendrePoly3(torch.autograd.Function):
    # P3(x) = 1/2 (5x^3 - 3x)
    @staticmethod
    def forward(ctx, input):
        ctx.save_for_backward(input)
        return 0.5 * (5 * input**3 - 3 * input)
    @staticmethod
    def backward(ctx, grad_output):
        print(ctx.saved_tensors)
        input, = ctx.saved_tensors
        return grad_output * 1.5 * (5 * input ** 2 - 1)

dtype = torch.float
torch.set_default_device("cpu")

x = torch.linspace(-math.pi, math.pi, 2000, dtype=dtype)
y = torch.sin(x)

a = torch.full((), 0.0, dtype=dtype, requires_grad=True)
b = torch.full((), -1.0, dtype=dtype, requires_grad=True)
c = torch.full((), 0.0, dtype=dtype, requires_grad=True)
d = torch.full((), 0.3, dtype=dtype, requires_grad=True)

learning_rate = 5e-6
for t in range(2000):
    P3 = LegendrePoly3.apply
    y_pred = a * b * P3(c + d * x)
    loss = (y_pred - y).pow(2).sum()
    if t % 100 == 0:
        print(t, loss.item())
    loss.backward()
    # Update weights using gradient descent
    with torch.no_grad():
        a -= learning_rate * a.grad
        b -= learning_rate * b.grad
        c -= learning_rate * c.grad
        d -= learning_rate * d.grad

        # Manually zero the gradients after updating weights
        a.grad = None
        b.grad = None
        c.grad = None
        d.grad = None

print(f'Result: y = {a.item()} + {b.item()} * P3({c.item()} + {d.item()} x)')
