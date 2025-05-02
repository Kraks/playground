use egg::{*, rewrite as rw};

define_language! {
  pub enum RingExpr {
    Symbol(Symbol),
    "0" = Zero,
    "1" = One,
    "+" = Add([Id; 2]),
    "*" = Mul([Id; 2]),
    "-" = Inv(Id),
    "var" = Var(Id),
    "let" = Let([Id; 3]), // (let x e1 e2) ~ let x = e1 in e2
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

    // side condition: ?fresh* are globally unique variables
    // side condition: e1 and e2 are not primitive variables or numbers, look at is_const from POPL paper
    rw!("add-let"; "(+ ?e1 ?e2)" => "(let ?fresh1 ?e1 (let ?fresh2 ?e2 (+ (var ?fresh1) (var ?fresh2))))"),

    rw!("let-pop"; "(+ ?e1 (let ?x ?e2 ?e3))" => "(let ?x ?e2 (+ ?e1 ?e3))"),

    // swap condition x ∉ e2
    rw!("let-swap"; "(let ?x ?e1 (let ?y ?e2 ?e3))" => "(let ?y ?e2 (let ?x ?e1 ?e3))"),

    /*
    let x = e1 in
    ...
    let y = e1 in
    (+ x y)

    let x = e1 in
    ...
    (+ x x)

    ...
    let y = e1 in
    (+ y y)
    */
    rw!("let-remove"; "(let ?x ?e1 ?e2)" => "(let ?x ?e1 ?e2)"),

    //rw!("let-elim"; "(let ?x ?e1 ?)" => ),
    //rw!("let-subst"; "(let ?x ?e1 ?e2)" => e2[x -> e1]),

    /*
    C := [] | (+ C e) | (+ e C) | (let x C e) | (let x e C)

    let x = 0 in C[x] -> let x = 0 in C[0]

    let x = 0 in let y = e in (+ x y)
    let x = 0 in C'[x] where C' = let y = e in (+ [] y)

    (+ e1 (+ e1 e2))

    let x1 = e1 in
    let x2 = e2 in
    (+ x1 (+ x1 x2))

    (+ x1 (let x1 = e1 (let x2 = e2 (+ x1 x2))))
    */
  ];

  // rw!("let-var-same"; "(let ?v1 ?e (var ?v1))" => "?e"),
  /*
    let x = e in app(x, e2)
  -> app(let x = e in x, let x = e in e2)
  -> app(e, let x = e in e2)
  let x = e in y if x != y -> y
  */

  let e1: RecExpr<RingExpr> = "(+ 0 (+ a b))".parse().unwrap();
  let runner = Runner::default().with_expr(&e1).run(rules);
  let extractor = Extractor::new(&runner.egraph, AstSize);
  let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);
  println!("best expression: {}", best_expr);
}