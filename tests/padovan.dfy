function P(n: nat): nat
  decreases n
{
  if n <= 2 then 1 else P(n-2) + P(n-3)
}

method calcP(n: nat) returns (res: nat)
ensures res == P(n) 
{
  if n <= 2 { return 1; }
  var a, b, c := 1, 1, 1; // P(0), P(1), P(2)
  var i:= 2; // P(3)
  while i < n 
    decreases n - i
    invariant 0 <= i <= n
    invariant a == P(i-2) && b == P(i-1) && c == P(i)
  {
    a, b, c := b, c, a + b;
    i := i + 1;
  }
  res := c;
}