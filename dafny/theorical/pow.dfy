function power(x : real, n : nat) : real
    decreases n
{
	if n == 0 then 1.0
	else x * power(x, n - 1)
}

// Iterative version with time complexity of O(n) and space complexity of O(1)
method powerIter(x : real, n : nat) returns (p : real)
    requires ! ( x == 0.0 && n == 0)
    ensures p == power(x, n) // nas post condicoes apenas codigo declarativo
{
    
	var i := 0; // starting with p = x^0
    p := 1.0; // x^i

	while i < n // iterate until reaching p = x^n
		decreases n - i 
        invariant p == power(x, i) 
        invariant 0 <= i <= n
	{ 
		p := p * x;
		i := i + 1;
	}
} 

// Proof by induction
lemma {: induction a} distributiveProperty(x:real, a:nat, b:nat)
    ensures power(x, a) * power(x, b) == power(x, a + b)
{
}

// Optimized version with time complexity if O(logN) and space complexity of O(1)
method powerOpt(x : real, n : nat) returns (p : real)
    requires ! ( x == 0.0 && n == 0)
    ensures p == power(x, n) // nas post condicoes apenas codigo declarativo
    decreases n
{
	if n == 0 {
        return 1.0;
    } else if n == 1 {
        return x;
    } else if n % 2 == 0 {
        var temp := powerOpt(x, n/2);
        // x^a * x^b == x^(a+b)
        distributiveProperty(x, n/2, n/2);
        return temp * temp;
    } else {
        var temp := powerOpt(x, (n-1)/2);
        distributiveProperty(x, (n-1)/2, (n-1)/2);
        return temp * temp * x;
    }
} 

method testPowerIter() {
	var p1 := powerIter(2.0, 5);
    assert p1 == 32.0;
} 

method testPowerOpt() {
	var p1 := powerOpt(2.0, 5);
    assert p1 == 32.0;
} 