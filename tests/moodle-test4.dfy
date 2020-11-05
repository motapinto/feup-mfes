/*
  1. Which of the following Hoare triples is FALSE?
    a) {true} skip {x ≥ 0} ----------------------------------
    b) {x ≥ 0} x := x + 1 {x ≥ 0}
    c) {x ≠ 0} if x > 0 then y := 1 else y := -1 { x × y > 0}
    d) {true} while i > 0 do i := i - 1 {i ≤ 0}

  2. Which of the following Hoare triples is FALSE?
    a) {x > 0} x := z - x; y := z - x {y > 0}
    b) {x < y} x := z - x; y := z - y {x > y}
    c) {x > 0} x := x + y; y := x - y {y > 0}
    d) {x > 0} z := 1; y := x - z {y > 0} --------------------

  3. Which of the following expressions gives the weakest precondition of the following Hoare triple
  (considering total correctness)?
    {wp} while x > y do x := x - y {true}
    a) y > 0 
    b) x ≤ y ∨ y > 0  ------------------- 
    c) x ≤ y ∧ y > 0 
    d) x ≤ y
*/

function C(n: nat): nat {
  if n == 0 then 1 
  else (4 * n - 2) * C(n-1) / (n + 1) 
}

method calcC(n: nat) returns (res: nat)
  ensures res == C(n)
{
  var i := 0;
  res := 1;
  while i < n 
    decreases n -i
    invariant 0 <= i <= n
    invariant res == C(i)
  { 
    i := i + 1;
    res := (4 * i - 2) * res / (i + 1);
  }
}

method calcCHard(n: nat) returns (res: nat)
  ensures res == C(n)
{
  // Prove P ==> wp
  assert true; // P
  assert 0 <= n && 1 == C(0); // wp
  var i := 0;
  assert 0 <= i <= n && 1 == C(i); // wp
  res := 1;
  assert 0 <= i <= n && res == C(i); // I
  while i < n 
    decreases n -i
    invariant 0 <= i <= n
    invariant res == C(i)
  { 
    ghost var v0 := n - i;
    // Prove I && C && V == V0 ==> wp
    assert 0 <= i <= n && res == C(i) && i < n && n - i == v0; // I && C && V == V0
    assert 0 <= i + 1 <= n && (4 * (i + 1) - 2) * res / (i + 2) == C(i + 1) && 0 <= n - i - 1 < v0; // wp
    i := i + 1;
    assert 0 <= i <= n && (4 * i - 2) * res / (i + 1) == C(i) && 0 <= n - i < v0; // wp
    res := (4 * i - 2) * res / (i + 1);
    assert 0 <= i <= n && res == C(i) && 0 <= n - i < v0; // I && 0 <= V < V0;
  }
  assert 0 <= i <= n && res == C(i) && !(i < n); //I && !C
  assert res == C(n); // Q
}

type T = int 

// Checks if array 'a' is sorted.
predicate isSorted(a: array<T>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Use binary search to find an appropriate position to insert a value 'x'
// in a sorted array 'a', so that it remains sorted.
method binarySearch(a: array<T>, x: T) returns (index: int) 
  requires isSorted(a)
  ensures 0 <= index <= a.Length
  ensures index != 0 ==> a[index - 1] <= x
  ensures index != a.Length ==> a[index] >= x
{
  var low, high := 0, a.Length;
  while low < high 
    decreases high - low
    invariant 0 <= low <= high <= a.Length
    invariant low != 0 ==> a[low - 1] <= x
    invariant high != a.Length ==> a[high] >= x
  {
    var mid := low + (high - low) / 2;
    if {
      case a[mid] < x => low := mid + 1;
      case a[mid] > x => high := mid;
      case a[mid] == x => return mid;
    }
  }
  return low;
}
// Simple test cases to check the post-condition
method testBinarySearch() {
  var a := new int[2] [1, 3];
  var id0 := binarySearch(a, 0);
  assert id0 == 0;
  var id1 := binarySearch(a, 1);
  assert id1 in {0, 1};
  var id2 := binarySearch(a, 2);
  assert id2 == 1;
  var id3 := binarySearch(a, 3);
  assert id3 in {1, 2};
  var id4 := binarySearch(a, 4);
  assert id4 == 2;
}

// A datatype that stores a value of type T or Nil (no value) 
datatype Option<T> = Nil | Some(value: T)

// Function type for hash functions
type HashFunction<!T> = (T) -> nat 

// Represents a hash set of elements of type T, that is, a set stored in a hash table. 
class {:autocontracts} HashSet<T(==)> {

   // Parameter of the hash set (hash function to be used). 
  const hash: HashFunction<T>;

  // Abstract state variable used for specification purposes only (set of elements in the hash set).  
  ghost var elems : set<T>;

  // Concrete state variable with internal representation (initially filled with Nil). 
  var hashTable: array<Option<T>>; 

  // Internal parameter, with initial size of hash table.
  const initialCapacity := 101;

  // Predicate that formalizes the class invariant.
  predicate Valid() 
  {
    elems == (set i | 0 <= i < hashTable.Length && hashTable[i] != Nil :: hashTable[i].value)
    && hashTable.Length > 0 
    && forall i :: 0 <= i < hashTable.Length && hashTable[i] != Nil ==>
      var h := hash(hashTable[i].value) % hashTable.Length;
      h == i  
      || (h < i && forall j :: h <= j < i ==>  hashTable[j] != Nil && hashTable[j] != hashTable[i])
      || (h > i && forall j :: h <= j < hashTable.Length || 0 <= j < i ==> hashTable[j] != Nil && hashTable[j] != hashTable[i])
  }  

  // Receives the hash function to be used and initializes the set as empty.
  constructor (hash: HashFunction<T>)
    ensures this.hash == hash 
    ensures |elems| == 0

  // Inserts a new element x into this hash set.
  method insert(x : T)
    requires  x !in elems
    ensures elems == old(elems) + {x}

  // Method that checks if this hash set contains an element x.
  method contains(x: T) returns (res: bool)
    ensures res <==> x in elems  
  {
    var h := hash(x) % hashTable.Length;
    var i := h;
    while i < hashTable.Length 
      decreases hashTable.Length - i
      invariant h <= i <= hashTable.Length
      invariant forall j :: h <= j < i ==> hashTable[j] != Nil && hashTable[j] != Some(x)
    {
        if hashTable[i] == Nil { return false; }
        if hashTable[i] == Some(x) { return true; } 
        i := i + 1;
    }
    i := 0;
    while i < h
      decreases h - i
      invariant 0 <= i <= h
      invariant forall j :: 0 <= j < i ==> hashTable[j] != Nil && hashTable[j] != Some(x)
    {
        if hashTable[i] == Nil { return false; }
        if hashTable[i] == Some(x) { return true; } 
        i := i + 1;
     }
     return false;
  }
}

// A simple test case, checked statically by Dafny.
method testHashSet() {
  var h := new HashSet<string>(x => |x|); // the hash function is the string length
  h.insert("Hello");
  assert h.elems == {"Hello"};
  h.insert("World");
  assert h.elems == {"Hello", "World"};
  var found := h.contains("Hello");
  assert found;
  found := h.contains("ANSI");
  assert !found;
}
