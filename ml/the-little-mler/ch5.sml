datatype 'a pizza = Bottom
        | Topping of ('a * ('a pizza));

datatype fish = Anchovy
        | Lox
        | Tuna;

Topping(Anchovy,
  Topping(Tuna,
    Topping(Anchovy,
      Bottom)));

fun rem_anchovy(Bottom) = Bottom
  | rem_anchovy(Topping(Anchovy, p)) = rem_anchovy(p)
  | rem_anchovy(Topping(Tuna, p)) = Topping(Tuna, rem_anchovy(p))
  | rem_anchovy(Topping(Lox, p)) = Topping(Lox, rem_anchovy(p));

fun rem_anchovy(Bottom) = Bottom
  | rem_anchovy(Topping(Anchovy, p)) = rem_anchovy(p)
  | rem_anchovy(Topping(t, p)) = Topping(t, rem_anchovy(p));
