/** 
 * Computes the quotient 'q' and remainder 'r' of
 * the integer division of a (non-negative) divident 'n'
 * by a (positive) divisor 'd'
 */
method div(n: nat, d: nat) returns (q: nat, r: nat)
  requires d > 0 // pre-condition
  ensures q * d + r == n && 0 <= r < d //post-condition
{
  q := 0;
  r := n;
  while r >= d
    decreases r
    invariant q * d + r == n // before the cicle and after each iteration of the cicle. the condition must be true (in between can be false) and ensures the post condition
  {
    q := q + 1;
    r := r - d;
  }
}

/**
 * A simple test case for the function above
 */
 method Main()
 {
   var q, r := div(15, 6);
   assert q == 2;
   assert r ==3;
   print "q = ", q, " r = ", r,  "\n";
 }