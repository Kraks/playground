import numpy as np
import onnx
from onnx import numpy_helper

filename = "gpt.onnx"
model = onnx.load(filename)
# Check model consistency
onnx.checker.check_model(model)

graph = model.graph

print(onnx.helper.printable_graph(graph))

inputs = {inp.name : inp for inp in graph.input}
outputs = {out.name : out for out in graph.output}
inits = {init.name : numpy_helper.to_array(init) for init in graph.initializer}

funs = {fun.name : fun for fun in graph.value_info}

print(f"Inputs: {inputs}")
print(f"Outputs: {outputs}")
#print(f"Initializers: {inits}")

nodes = graph.node
tensor_store = {}
tensor_store.update(inits)
#print(f"Tensors: {tensor_store.keys()}")

def execute(node):
  #inputs = [tensor_store[t] for t in node.input]
  print(f"{node.domain}::{node.op_type} of {type(node)}")
  if node.op_type == "Gather":
    pass
  elif node.op_type == "Constant":
    pass
  elif node.op_type == "Add":
    pass
  elif node.op_type == "LayerNormalization":
    pass
  elif node.op_type == "MatMul":
    pass
  elif node.op_type == "Transpose":
    pass
  elif node.domain is not None:
    print(funs.keys())
    #print(funs[node.domain + "::" + node.op_type])
    raise Exception(f"Unknown op_type: {node.op_type}")

for node in nodes:
  execute(node)
