// Merge sort

abstype myseq

extern fun mergesort(xs: myseq): myseq
extern fun myseq_length(xs: myseq): int
extern fun myseq_split(xs: myseq): (myseq, myseq)
extern fun myseq_merge(xs1: myseq, xs2: myseq): myseq

implement mergesort(xs) = 
  let val n = myseq_length(xs) in
    if n >= 2 then 
      let val (xs1, xs2) = myseq_split(xs) 
      in myseq_merge(mergesort(xs1), mergesort(xs2))
    end else(xs)
  end
  
// using dependent types
  
abstype myseq(n: int)

extern fun mergesort {n: nat} (xs: myseq(n)): myseq(n)
extern fun myseq_length{n: nat} (xs: myseq(n)): int(n)
extern fun myseq_split{n: int | n >= 2} (xs: myseq(n)): [n1,n2: pos | n1+n2=n] (myseq(n1), myseq(n2))
extern fun myseq_merge{n1,n2: nat} (xs1: myseq(n1), xs2: myseq(n2)): myseq(n1+n2)

implement mergesort(xs) = 
  let fun sort{n: nat} .<n>. (xs: myseq(n)): myseq(n) =
    let val n = myseq_length(xs) in
      if n >= 2 then let
        val (xs1, xs2) = myseq_split(xs)
        in myseq_merge(sort(xs1), sort(xs2))
      end else (xs)
    end
  in sort(xs) end
  