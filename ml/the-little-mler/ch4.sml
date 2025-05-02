datatype meza = Shrimp
       | Calamari
       | Escargots
       | Hummus;

datatype main = Steak
       | Ravioli
       | Chicken
       | Eggplant;

datatype sala = Green
       | Cucumber
       | Greek;

datatype dessert = Sundae
       | Mousse
       | Torte;

fun add_a_steak (Shrimp) = (Shrimp, Steak)
  | add_a_steak (Calamari) = (Calamari, Steak)
  | add_a_steak (Escargots) = (Escargots, Steak)
  | add_a_steak (Hummus) = (Hummus, Steak);

fun add_a_steak (x: meza) = (x, Steak);

fun eq_main (Steak, Steak) = true
  | eq_main (Ravioli, Ravioli) = true
  | eq_main (Chicken, Chicken) = true
  | eq_main (Eggplant, Eggplant) = true
  | eq_main (a_main, another_main) = false;

fun has_steak (a_meza: meza, Steak, a_dessert: dessert) = true
  | has_steak (a_meza: meza, a_main, a_dessert: dessert) = false;
