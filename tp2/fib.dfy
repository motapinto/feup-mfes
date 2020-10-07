// Fibonacci numbers: 0, 1, 1, 2, 3, ...
//recursive function that takes exponential time
function fib(n : nat ) : nat
  decreases n
{
  if n < 2 then n else fib(n - 2) + fib(n - 1)
}

// dynamic programming
method computeFib (n : nat) returns (x : nat)
  requires n >= 0 //pre-condition
  ensures x == fib(n) //post-condition
{
  var i := 0;
  x := 0;
  var y := 1;

  while  i < n 
    decreases n - i // variant
    invariant 0 <= i <= n
    invariant n >= 0
    invariant x == fib(i)
    invariant y == fib(i+1)
  {
    x, y := y, x + y; // multiple assignment
    i := i + 1;
  }
}

/*
 * Method 1: I ^ not(C) => Q <=> I ^ not(i < n) => x = fib(n) <=> I ^ i>=n => x = fib(n) <=> x = fib(n) : This method does not work (for now)
 * Method 2: Contraint C variables(i,n,x,y) : 0<=i<=n | n>=0
 * Lets go back to method 1 and try: I ^ 0<=i ^ i<=n ^ 0<=n ^ i>=n => x = fib(n) <=> I ^ 0<=i ^ i=n ^ 0<=n => Choose I: x=fib(i)
 * The only variable that is missing is y and it's fib(i+1) obviously
 */


// In case we didn't had dafny we had to do this
method computeFibWithoutDafny (n : nat) returns (x : nat)
    requires n >= 0
    ensures x == fib(n)
{
    // Prove P ==> wp
    assert n >= 0; // P
    assert 0 <= 0 <= n && n >= 0 && 0 == fib(0) && 1 == fib(0+1); // wp
    var i := 0;
    
    assert 0 <= i <= n && n >= 0 && 0 == fib(i) && 1 == fib(i+1); // wp
    x := 0;
    
    assert 0 <= i <= n && n >= 0 && x == fib(i) && 1 == fib(i+1); // wp
    var y := 1;

    assert 0 <= i <= n && n >= 0 && x == fib(i) && y == fib(i+1); // I
    while  i < n
        decreases n - i // V
        invariant 0 <= i <= n
        invariant n >= 0
        invariant x == fib(i)
        invariant y == fib(i+1)
    {
        ghost var v0 := n - i;
        // Prove I && C && V == V0 ==> wp
        assert 0 <= i <= n && n >= 0 && x == fib(i) && y == fib(i+1) && i < n && n - i == v0; // I && C && V == V0
        assert 0 <= (i+1) <= n && n >= 0 && y == fib((i+1)) && x + y == fib((i+1)+1) && 0 <= n - (i+1) < v0;// wp
        x, y := y, x + y; // multiple assignment
        assert 0 <= (i+1) <= n && n >= 0 && x == fib((i+1)) && y == fib((i+1)+1) && 0 <= n - (i+1) < v0; // wp
        i := i + 1;
        assert 0 <= i <= n && n >= 0 && x == fib(i) && y == fib(i+1) && 0 <= n - i < v0; // I && 0 <= V < V0
    }

    // Prove I && !C ==> Q
    assert 0 <= i <= n && n >= 0 && x == fib(i) && y == fib(i+1) && !(i < n);// I && !C
    assert x == fib(n); // Q
}