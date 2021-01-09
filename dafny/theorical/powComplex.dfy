// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
  decreases n
{
  if n == 0 then 1.0 else x * power(x, n-1)
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(x: real, n: nat) returns (p : real)
  ensures p == power(x, n)
{
  // start with p = x^0
  p := 1.0;
  var i := 0;
  // iterate until reaching p = x^n
  while i < n
    decreases n - i
    invariant 0 <= i <= n && p == power(x, i)
  {
    p := p * x;
    i := i + 1;
  }
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
    distributiveProperty_v1(x,  n/2, n/2); // recall lemma here
    var temp := powerOpt(x, n/2);
    return temp * temp;
  }
  else {
    distributiveProperty_v1(x, (n-1)/2, (n-1)/2); // recall lemma here  
    var temp := powerOpt(x, (n-1)/2);
    return temp * temp * x;
  } 
}

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// First (and simpler) version, using the annotation {:induction a} to guide Dafny 
// to prove the property by automatic induction on 'a'.
lemma {:induction a} distributiveProperty_v1(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
  decreases a
{
}

// Second version, with manual proof by induction on a, using assert.
// Note: In fact some intermmediate steps may be ommitted / commented.
lemma {:induction false} distributiveProperty_v2(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
{
  if a == 0  {
  assert
    power(x, a) * power(x, b) == 
    1.0 * power(x, b) == // by the definition of power(x, 0) 
    power(x, b) ==
    power(x, a+ b);   
    
  }
   else { 
    // recursive case, assuming property holds for a-1 (proof by induction)
    distributiveProperty_v2(x, a-1, b);
    // now do the proof
    assert
      power(x, a) * power(x, b) == 
      (x * power(x, a-1)) * power(x, b) == // by the definition of power(x, n) when n > 0  
      x * (power(x, a-1) * power(x, b)) ==
      x * power(x, a-1 + b) == // by applying this same property for a-1
      power(x, a + b); // by the definition of power(x, n) when n > 0     
   }
}

// Third version, with manual proof by induction on a, with calc (calculational proof).
// Note: In fact some intermmediate steps may be ommitted / commented.
lemma {:induction false} distributiveProperty_v3(x: real, a: nat, b: nat) 
  ensures power(x, a) * power(x, b)  == power(x, a + b) 
  decreases a
{
  if a == 0 { // base case        
    calc == {
      power(x, a) * power(x, b);
      1.0 * power(x, b); // by the definition of power(x, 0)
      power(x, b); 
      power(x, a + b); 
    }
  }
  else {
    // recursive case, assuming property holds for a-1 (proof by induction)
    distributiveProperty_v3(x, a-1, b); 
    // now do the proof
    calc == {
      power(x, a) * power(x, b);
      (x * power(x, a-1)) * power(x, b); // by the definition of power(x, n) when n > 0  
      x * (power(x, a-1) * power(x, b)); 
      x * power(x, a + b - 1); // by applying this same property for a-1
      power(x, a + b); // by the definition of power(x, n) when n > 0  
    }
  }
}

// A simple test case to make sure the specification is adequate.
method testPower() {
  var p1 := powerIter(2.0, 5);
  var p2 := powerOpt(2.0, 5);
  assert p1 == 32.0;
  assert p2 == 32.0;
}