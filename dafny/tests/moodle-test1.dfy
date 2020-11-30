/*
  Which of the following Hoare triples is FALSE? 
  Selecione uma opção:
    a. {x > 2} skip {x > 1} 
    b. {i > 0} while i > 0 do i := i - 1 {i = 0}
    c. {true} if x ≥ 0 then y := x else y := -x {y > 0} ------
    d. I don't want to answer this question.
    e. {x > 1} x := x + 1 {x > 2}

  Which of the following Hoare triples is FALSE? 
  Selecione uma opção:
    a. {x > 1} z := 1; y := x - z {x > y}
    b. {x > 0} x :=  x + y; y := x - y {y > 0}
    c. {y > 1} z := x; y := y - z {x > y} 
    d. I don't want to answer this question.
    e. {true} y := x; y := x + x + y {y = 3x} 

      a                         b                             c                                d
    wp(S, Q)                  wp(S, Q)                      wp(S, Q)                         wp(S, Q)
    x > y                     y > 0                         x > y                            y = 3x
    x > x - z                 x - y > 0                     x > y - z                        x + x + y = 3x
    x > x -1 <==> true        x + y - y > 0 <=> x > 0       x > y - x <==> 2x > y            x + x + x = 3x <==> true

    P ==> wp                  P ==> wp                      P ==> wp                         P ==> wp
    x > 1 ==> true            x > 0 ==> x > 0 <==> true     y > 1 ==> 2x > y <==> false      true ==> true
    !(x>1) || true <=> true    

  Which of the following expressions gives or is equivalent to the weakest 
  precondition of the following Hoare triple? 
  {wp} if a > b then x := a else x := b {x > 0}
  Selecione uma opção:
    a. I don't want to answer this question.
    b. x > 0
    c. a > 0 ∨ b > 0 ------------------------------------------
    d. a > 0 ∧ b > 0
    e. true 

  One wants to prove the correctness of the following Hoare triple, 
  taking as loop invariant  I ≡ (z+y=x ∧ z ≥ 0) and as loop variant V ≡ z.
  { x ≥ 0} z := x; y := 0; while z ≠ 0 do (y := y+1; z := z−1) {x = y} 
  a) Weakest preconditions
    1:  {x ≥ 0}  
    2:  {x = x ∧ x ≥ 0} // wp
    3:  z := x;
    4:  {z = x ∧ z ≥ 0} // wp
    5:  y := 0; 
    6:  {z + y = x ∧ z ≥ 0} // I 
    7:  while z ≠ 0 do 
    8:        {z ≠ 0 ∧ z + y = x ∧ z ≥ 0 ∧ z = V0}  // C ∧ I ∧ V = V0
    9:        {z + y = x ∧ z ≥ 1 ∧ z - 1 < V0} // wp
    10:        y := y + 1;
    11:       {z - 1 + y = x ∧ z - 1 ≥ 0 ∧ z - 1 < V0} // wp
    12:        z := z − 1
    13:       {z + y = x ∧ z ≥ 0 ∧ z < V0} // I ∧ 0 ≤ V < V0  
    14:  {z = 0 ∧ z + y = x ∧ z ≥ 0} // ¬ C ∧ I 
    15:  {x = y}

  b) Implications 
    1 ⇒ 2
      x ≥ 0 => x ≥ 0 <=> true
    8 ⇒ 9
      z ≠ 0 ∧ z + y = x ∧ z ≥ 0 ∧ z = V0 => z + y = x ∧ z ≥ 1 ∧ z - 1 < V0 <=>
      z > 0 ∧ z + x = y ∧ z = V0 => z > 0 ∧ z + x = y ∧ V0 - 1 < V0 <=> true
    14 ⇒ 15
      z = 0 ∧ y = x ∧ z ≥ 0 => x = y <=> true
*/

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
  var i:= 2;
  
  while i < n 
    decreases n - i
    invariant 2 <= i <= n
    invariant a == P(i-2) 
    invariant b == P(i-1) 
    invariant c == P(i)
  {
    a, b, c := b, c, a + b;
    i := i + 1;
  }
  // I && !C: I && i >= n <==>
  // I' && 2 <= i <= n && i >= n <==>
  // I' && i = n
  // c == P(n)
  res := c;
}


type T = int // example 

predicate sorted(a: array<T>, n: nat)
  reads a
  requires 0 <= n <= a.Length
{
  forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
}

function elems(a: array<T>, n: nat): multiset<T>
  requires n <= a.Length
  reads a
{
  multiset(a[..n])
}

// Merges two sorted arrays 'a' and 'b' into a new sorted array 'c'.
method merge(a: array<T>, b: array<T>) returns (c: array<T>) 
  requires sorted(a, a.Length)
  requires sorted(b, b.Length)
  ensures elems(a, a.Length) + elems(b, b.Length) == elems(c, c.Length)
  ensures sorted(c, c.Length)
{
    c := new T[a.Length + b.Length];
    var i, j := 0, 0; // indices in 'a' and 'b'

    // Repeatedly pick the smallest element from 'a' and 'b' and copy it into 'c':
    while i < a.Length || j < b.Length 
      decreases a.Length - i + b.Length - j
      invariant 0 <= i <= a.Length 
      invariant 0 <= j <= b.Length
      invariant elems(a, i) + elems(b, j) == elems(c, i + j)
      invariant sorted(c, i + j)

      invariant forall m, n :: i <= m < a.Length && 0 <= n < i + j ==> a[m] >= c[n]
      invariant forall m, n :: j <= m < b.Length && 0 <= n < i + j ==> b[m] >= c[n]
    {
      if i < a.Length && (j == b.Length  || a[i] <= b[j]) {
        c[i + j] := a[i];
        i := i+1;
      } 
      else {
        c[i + j] := b[j];
        j:= j+1;
      }
    }
}

method testMerge() {
  var a: array<T> := new T[3] [1, 3, 5];
  var b: array<T> := new T[2] [2, 4];
  var c:= merge(a, b);
  assert a[..a.Length] == [1, 3, 5];
  assert b[..b.Length] == [2, 4];
  assert elems(c, c.Length) == multiset{1, 2, 3, 4, 5};
  assert c[..] == [1, 2, 3, 4, 5];
}

class {:autocontracts} BSTNode {
    // Concrete implementation variables.
    var value: T 
    var left: BSTNode?  // elements smaller than 'value' (? - may be null)
    var right: BSTNode? // elements greater than 'value' (? - may be null)

    // Ghost variable used for specification & verification purposes.
    // Holds the set of values in the subtree starting in this node (inclusive). 
    ghost var elems: set<T> 

    // Class invariant with the integrity constraints for the above variables
    predicate Valid() { 
      (
        (elems == {value} + (if left == null then {} else left.elems) + (if right == null then {} else right.elems)) &&
        (left != null ==> forall l :: l in left.elems ==> l < value) &&
        (right != null ==> forall r :: r in right.elems ==> r > value)
      )
    }

    // Check if the subtree starting in this node contains a value 'x'.
    method contains(x: T) returns (res: bool)
      ensures res <==> x in elems
      decreases elems
    {
        if x == value { res := true; } 
        else if x < value && left != null  { res := left.contains(x); } 
        else if x > value && right != null { res := right.contains(x); } 
        else { res := false; }
    }
}

// Hint: You have to make sure that: (i) elems has the node value plus all the 
// values in the left and right subtrees; (ii) the left subtree (if existent) 
// contains values smaller than the node value; (ii) the right subtree (if existent) 
// contains values greater than the node value.