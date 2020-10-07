// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
  decreases n
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
  ensures p == power(x, n);
  decreases n;
{
    if n == 0 {
        return 1.0;
    }
    else if n == 1 {
        return x;
    }
    else if n % 2 == 0 {
        distributiveProperty(x,  n/2, n/2); // recall lemma here
        var temp := powerOpt(x, n/2);
        return temp * temp;
    }
    else {
        distributiveProperty(x, (n-1)/2, (n-1)/2); // recall lemma here  
        var temp := powerOpt(x, (n-1)/2);
        return temp * temp * x;
    } 
}
// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.
lemma {:induction a} distributiveProperty(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{
}

method powerInt(x: real, n: int) returns (p: real)
    requires n < 0 ==> x != 0.0
    ensures p == if n < 0 then power(1.0/x, -n) else  power(x, n)
{
    if n < 0 {
        p := powerOpt(1.0/x, -n);
    } else {
        p := powerOpt(x, n);
    }
}
// A simple test case to make sure the specification is adequate.
method testPower() {
    var p2 := powerOpt(2.0, 5);
    assert p2 == 32.0;
    var p3 := powerInt(2.0, -2);
    assert p3 == 0.25;
}
