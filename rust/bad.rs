fn main() {
  let mut x = 5;
  let y = &mut x;
  *y += 1;
  println!("{}", y);
  println!("{}", x);
}
