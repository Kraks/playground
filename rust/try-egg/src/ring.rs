use egg::{*, rewrite as rw};

define_language! {
  pub enum RingExpr {
    Symbol(Symbol),
    "0" = Zero,
    "1" = One,
    "+" = Add([Id; 2]),
    "*" = Mul([Id; 2]),
    "-" = Inv(Id),
  }
}

pub fn ring() {
  let rules: &[Rewrite<RingExpr, ()>] = &[
    rw!("commute-add"; "(+ ?x ?y)" => "(+ ?y ?x)"),
    rw!("assoc-add"; "(+ ?x (+ ?y ?z))" => "(+ (+ ?x ?y) ?z)"),

    rw!("commute-mul"; "(* ?x ?y)" => "(* ?y ?x)"),
    rw!("assoc-mul"; "(* ?x (* ?y ?z))" => "(* (* ?x ?y) ?z)"),

    rw!("left-distr";  "(* ?x (+ ?y ?z))" => "(+ (* ?x ?y) (* ?x ?z))"),
    rw!("right-distr"; "(* (+ ?x ?y) ?z)" => "(+ (* ?x ?z) (* ?y ?z))"),

    rw!("add-0"; "(+ ?x 0)" => "?x"),
    rw!("add-inv"; "(+ ?x (- ?x))" => "0"),

    rw!("mul-0"; "(* ?x 0)" => "0"),
    rw!("mul-1"; "(* ?x 1)" => "?x"),
  ];

  let e1: RecExpr<RingExpr> = "(+ 0 (+ a b))".parse().unwrap();
  let runner = Runner::default().with_expr(&e1).run(rules);
  let extractor = Extractor::new(&runner.egraph, AstSize);
  let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);
  println!("best expression: {}", best_expr);
}