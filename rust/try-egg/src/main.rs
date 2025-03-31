use egg::{*, rewrite as rw};

define_language! {
    enum MatExpr {
        // data types
        Num(i32),
        Symbol(Symbol),
        "vec" = Vec(Box<[Id]>),
        "mat" = Mat(Box<[Id]>),       // row-major matrix
        "mat-cl" = MatCl(Box<[Id]>),  // column-major matrix
        "mat-tr" = MatTr(Box<[Id]>),
        // scalar operations
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        // matrix operations
        "m+" = MatAdd([Id; 2]),
        "m*" = MatMul([Id; 2]),
        "m⊗" = MatKr([Id; 2]),
        // vector operations
        "v*" = VecDot([Id; 2]),
    }
}

fn mat() {
    let rules: &[Rewrite<MatExpr, ()>] = &[
        rw!("commute-add"; "(+ ?x ?y)" => "(+ ?y ?x)"),
        rw!("commute-mul"; "(* ?x ?y)" => "(* ?y ?x)"),

        rw!("add-0"; "(+ ?x 0)" => "?x"),
        rw!("mul-0"; "(* ?x 0)" => "0"),
        rw!("mul-1"; "(* ?x 1)" => "?x"),

        // TODO: how to specify rules with variadic arguments?
        rw!("vec-dot-prod"; "(v* (vec ?a ?b) (vec ?c ?d))" => "(+ (* ?a ?c) (* ?b ?d))"),

        rw!("mat-transpose-1";
            "(mat    (vec ?v1 ?v2) (vec ?v3 ?v4))" =>
            "(mat-cl (vec ?v1 ?v3) (vec ?v2 ?v4))"),
        rw!("mat-transpose-2";
            "(mat-cl (vec ?v1 ?v2) (vec ?v3 ?v4))" =>
            "(mat    (vec ?v1 ?v3) (vec ?v2 ?v4))"),

        rw!("mat-mul-row";
            "(m* (mat ?v1 ?v2) (mat    ?v3 ?v4))" =>
            "(m* (mat ?v1 ?v2) (mat-cl ?v3 ?v4))"),
        rw!("mat-mul";
            "(m* (mat ?v1 ?v2) (mat-cl ?v3 ?v4))" =>
            "(mat (vec (v* ?v1 ?v3) (v* ?v1 ?v4))
                  (vec (v* ?v2 ?v3) (v* ?v2 ?v4)))"),
    ];

    // vector dot product: (v* (vec a b) (vec 0 1)) → b
    {
    let e1: RecExpr<MatExpr> = "(v* (vec a b) (vec 0 1))".parse().unwrap();
    let runner = Runner::default().with_expr(&e1).run(rules);
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);
    println!("best expression: {}", best_expr);
    assert_eq!(best_expr, "b".parse().unwrap());
    }

    {
    // right-hand side is constant
    // x1 x2      0 1
    // x3 x4      1 0
    let e1: RecExpr<MatExpr> = "(m* (mat (vec x1 x2) (vec x3 x4)) (mat (vec 0 1) (vec 1 0)))".parse().unwrap();
    let runner = Runner::default().with_expr(&e1).run(rules);
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);
    println!("best expression: {}", best_expr);
    // (mat (vec x2 x1) (vec x4 x3))
    // assert_eq!(best_expr, "(mat (vec x2 x1) (vec x4 x3))".parse().unwrap());
    }

    {
    // right-hand side is not constant
    // TODO: This doesn't work yet, we need to define our own cost function
    // x1 x2      0 y2
    // x3 x4      1 y4
    let e1: RecExpr<MatExpr> = "(m* (mat (vec x1 x2) (vec x3 x4)) (mat-cl (vec 0 1) (vec y2 y4)))".parse().unwrap();
    let runner = Runner::default().with_expr(&e1).run(rules);
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);
    println!("best expression: {}", best_expr);
    }

}

fn simple() {
    let rules: &[Rewrite<SymbolLang, ()>] = &[
        rw!("commute-add"; "(+ ?x ?y)" => "(+ ?y ?x)"),
        rw!("commute-mul"; "(* ?x ?y)" => "(* ?y ?x)"),

        rw!("add-0"; "(+ ?x 0)" => "?x"),
        rw!("mul-0"; "(* ?x 0)" => "0"),
        rw!("mul-1"; "(* ?x 1)" => "?x"),
    ];
    let start = "(+ 0 (* 1 a))".parse().unwrap();
    let runner = Runner::default().with_expr(&start).run(rules);
    let extractor = Extractor::new(&runner.egraph, AstSize);
    let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);

    println!("best expression: {}", best_expr);
    assert_eq!(best_expr, "a".parse().unwrap());
    assert_eq!(best_cost, 1);
}

fn main() {
    println!("Hello, Egg!");
    //simple();
    mat();
}

