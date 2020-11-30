
// returns the absolute of an integer
method abs(x: int) returns (y: int)
	ensures y >= 0
	ensures x >= 0 ==> y == x
	ensures x < 0 ==> y == -x
{
	if x < 0 { 
		y := -x; 
	} else { 
		y:= x; 
	}
}


/** 
 * Computes the quotient 'q' and remainder 'r' of
 * the integer division of a  divident 'n' by a divisor 'd'
 */

/**
	Generalize the example of integer division (Div.dfy) to also work with negative numbers 
	(i.e., with variables of type int). Notice that the remainder should always be non-negative.

	Hints: Create an auxiliary function method abs to obtain the absolute value of an integer. 
	In the specification of the new version of div, you need to revise the postcondition for r.
	In the implementation of the new version of div, you may distinguish two cases: if n is positive, 
	r starts with value n and needs to be decreased until reaching the desired interval; if n is negative, 
	r starts with value n and needs to be increased until reaching the desired interval. In the loop 
	invariant(s) you may need to add the range of values of r. 
 */

method div(n: int, d: int) returns (q: int, r: int)
  	requires d > 0 // pre-condition
	ensures q * d + r == n && 0 <= r < d //post-condition
{
	var dAbs := abs(d);

	if n >= 0 {
		q := 0;
		r := n;
		while r >= dAbs
			decreases r
			invariant q * d + r == n
		{
			if(d > 0) { q := q + 1; } else { q := q - 1;}
			r := r - dAbs;
		}
	} else {
		q := 0;
		r := n;
		while r >= dAbs
			decreases 1 - r // r increases
			invariant q * d + r == n // before the cicle and after each iteration of the cicle. the condition must be true (in between can be false) and ensures the post condition
		{
			q := q - 1;
			r := r + dAbs;
		}
	}

}

/**
 * A simple test case for the function above
 */
 method Main()
 {
   var q1, r1 := div(15, 6);
   assert q1 == 2;
   assert r1 ==3;
   print "q = ", q1, " r = ", r1,  "\n";

   var q2, r2 := div(15, 6);
   assert q2 == 2;
   assert r2 ==3;
   print "q = ", q2, " r = ", r2,  "\n";
 }