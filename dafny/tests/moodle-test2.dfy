/*
  Which of the following Hoare triples is FALSE? 
  Selecione uma opção:
    a. {true} if x ≥ 0 then y := 1 else y := -1 {x * y ≥ 0}
    b. {i < 0} while i < 0 do i := i + 1 {i = 0}
    c. {x > 1} x := x - 1 {x > 0}
    d. I don't want to answer this question.
    e. {true} skip {false} ----------------------------------

  Which of the following Hoare triples is TRUE?
  Selecione uma opção:
    a. {true} z := x; y := z - 1 {y > x}
    b. {true} y := x; y := x + x + y {y > x}
    c. {true} z := 1; y := x - z {x < y}
    d. I don't want to answer this question.
    e. {y < 0} x := x + y; y := x - y {y > x} ----------------

  Which of the following expressions gives the weakest precondition of the following Hoare triple?
  {wp} while r >= d  do r := r - d {0 ≤ r ∧ r < d}
  Selecione uma opção:
    a. d > 0
    b. r >= 0 ∧ d > 0 ----------------------------------------
    c. I don't want to answer this question.
    d. r >= 0
    e. r >= 0 \/ d > 0
*/

function R(n: nat): nat {
  if n == 0 then 0 
  else if R(n-1) > n then R(n-1) - n 
  else R(n-1) + n
}

method calcR(n: nat) returns (r: nat)
  ensures r == R(n) 
{
  r := 0;
  var i := 0;
  while i < n 
    decreases n -i
    invariant 0 <= i <= n
    invariant r == R(i)
  {
    assert 0 <= i <= n && r == R(i); // I
    assert (r > i + 1 && -1 <= i <= n && r - i - 1 == R(i + 1)) || (r <= i + 1 && -1 <= i <= n && r + i + 1 == R(i + 1)); // wp
    i := i + 1;
    assert (r > i  && 0 <= i <= n && r - i == R(i)) || (r <= i && 0 <= i <= n && r + i == R(i)); // wp
    if r  > i {
      r := r - i;
    } 
    else {
      r := r + i;
    }
    assert 0 <= i <= n && r == R(i); // I 
  }
  assert 0 <= i <= n && r == R(i) && i >= n; // I && !C
  assert r == R(n); // Q
}

/*
  c) Prove manually that the loop invariant is preserved by the loop body
    P => I
    Neste segmento de código não tem acesso à pré-condição do ciclo, 
    que seria o P desta implicação. Para poder fazer esta prova, teria de 
    provar que o triplo {true} r := 0; i := 0 {I} é válido.

  ??d) Prove manually that the loop invariant is valid initially and implies 
     the method post-condition when the loop terminates.
     {I && C && V=V0} S {I && 0<=V<=V0} 

     {0<=i<n && i=V0}
     i=i+1
     if r>i then r=r-i
     else r=r+i
     {0<=i<=n %% r=R(i) && 0 <=i<=V0}

     (0<=i<=n && r=R(i) && i<n && i=V0) => wp(i=i+1, wp((r>i && r=r-i && 0<=i<=n %% r=R(i) && 0 <=i<=V0) V (r<=i && r=r+i 0<=i<=n %% r=R(i) && 0 <=i<=V0))
     
     
     
     (0<=i<=n && r=R(i) && i<n && i=V0) => wp(i=i+1, (r>0) V (r<=0), 0<=0<=n && r=R(0) && 0<=0<=V0)
     (0<=i<=n && r=R(i) && i<n && i=V0) => wp(i=i+1, 0<=n && r=R(0) && 0<=V0)

*/

type T = int // example
// Partitions a nonempty array 'a', by reordering the elements in the array,
// so that elements smaller than a chosen pivot are placed to the left of the
// pivot, and values greater or equal than the pivot are placed to the right of 
// the pivot. Returns the pivot position.
method partition(a: array<T>) returns(pivotPos: int) 
  modifies a
  requires a.Length > 0
  ensures 0 <= pivotPos < a.Length
  ensures forall k :: 0 <= k < pivotPos ==> a[k] < a[pivotPos]
  ensures forall k :: pivotPos < k < a.Length ==> a[pivotPos] <= a[k] 
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  pivotPos := a.Length - 1; // chooses pivot at end of array 
  var i := 0;  // index that separates values smaller than pivot (0 to i-1), 
                // and values greater or equal than pivot (i to j-1) 
  var j := 0;  // index to scan the array

  // Scan the array and move elements as needed
  while  j < a.Length-1 
    decreases a.Length - j
    invariant 0 <= i <= j < a.Length 
    invariant forall k :: 0 <= k < i ==> a[k] < a[pivotPos]
    invariant forall k :: i <= k < j ==> a[k] >= a[pivotPos]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if a[j] < a[pivotPos] 
    {
      a[i], a[j] := a[j], a[i];
      i := i + 1;
    }
    j := j+1;
  }

  // Swap pivot to the 'mid' of the array
  a[a.Length-1], a[i] := a[i], a[a.Length-1];
  pivotPos := i;  
}

// File system node
trait Node {
  const name: string; // unique within each folder
  ghost const depth: nat; // starts in 0 at file system root
}

class {:autocontracts} File extends Node { }
class {:autocontracts} Folder extends Node {
  var child: set<Node>; 

  predicate Valid() 
    reads this
  {
    forall x, y :: x in child && y in child && x != y ==> x.name != y.name &&
    forall x :: x in child ==> x.depth == depth + 1
  }

  constructor (name: string, parent: Folder?) 
    ensures this.name == name
    ensures parent != null ==> parent.child == old(parent.child) + {this} 
    ensures child == {}

    modifies parent
    requires parent != null ==> name !in set i:Folder | i in parent.child :: i.name
   
  {
    // this object initialization
    this.name := name;
    this.depth := if parent == null then 0 else parent.depth + 1;
    this.child := {};
    // other objets' updates (after special "new" keyword)
    new;
    if parent != null {
      parent.child := parent.child + {this};
    }
  }
}
