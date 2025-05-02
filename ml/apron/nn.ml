type act =
  | ReLU
  | Tanh

type expr =
  | Input
  | Nonlinear of act * string
  | Linear of {
      coeffs: (float * string) list;
      const: float;
    }

type stmt = string * expr

type nn = stmt list

module StringMap = Map.Make(String)
type env = float StringMap.t

let eval_act act x =
  match act with
  | ReLU -> max 0.0 x
  | Tanh -> tanh x

let rec eval_stmt stmt env =
  let var, expr = stmt in
  match expr with
  | Input -> env
  | Nonlinear (act, x) ->
    let y = eval_act act (StringMap.find x env) in
    StringMap.add var y env
  | Linear { coeffs; const } ->
    let x_vals = List.map (fun (coeff, x) -> coeff *. (StringMap.find x env)) coeffs in
    let y_val = List.fold_left (+.) const x_vals in
    StringMap.add var y_val env

let eval_nn (nn : stmt list) (env : env): env =
  List.fold_left (fun env stmt -> eval_stmt stmt env) env nn

let example1 = [
  ("x1", Input);
  ("x2", Linear { coeffs = [(0.5, "x1")]; const = 2.0});
  ("x3", Nonlinear (ReLU, "x2"))
]

let result1 = eval_nn example1 (StringMap.add "x1" 10.0 StringMap.empty);;
print_endline (string_of_float (StringMap.find "x3" result1))

let example2 = [
  ("x01", Input);
  ("x02", Input);
  ("x11_", Linear { coeffs = [(-0.31, "x01"); (0.99, "x02")]; const = -0.63 });
  ("x12_", Linear { coeffs = [(-1.25, "x01"); (0.64, "x02")]; const =  1.88 });
  ("x11", Nonlinear (ReLU, "x11_"));
  ("x12", Nonlinear (ReLU, "x12_"));
  ("x21_", Linear { coeffs = [(0.40, "x11"); (1.21, "x12")]; const = -0.00 });
  ("x22_", Linear { coeffs = [(0.64, "x11"); (0.69, "x12")]; const = -0.39 });
  ("x21", Nonlinear (ReLU, "x21_"));
  ("x22", Nonlinear (ReLU, "x22_"));
  ("x31", Linear { coeffs = [(0.26, "x21"); (0.33, "x22")]; const = -0.45 });
  ("x32", Linear { coeffs = [(1.42, "x21"); (0.40, "x22")]; const = -0.45 });
]
