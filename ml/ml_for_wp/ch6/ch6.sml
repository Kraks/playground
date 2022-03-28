datatype evenodd = Even | Odd;

fun test 0 = Even
  | test n = (case test (n-1) of 
                Even => Odd
              | Odd  => Even);

fun half 0 = (Even, 0)
  | half n = case half (n-1) of
                 (Even, m) => (Odd, m)
               | (Odd, m)  => (Even, m+1);
