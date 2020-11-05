
/* 
  Which of the following Hoare triples is FALSE? 
  Selecione uma opção:
    a. {x = 1} x := x - 1 {x ≥ 0}
    c. {x = 1} skip {x ≥ 0}
    d.{true} if x > 0 then y := x else y := -x {y  ≥ 0}
    e. {k > 0} while i > k do i := i - k {i < k} -------------

  Which of the following Hoare triples is FALSE?
  [Hint: In case of doubt, calculate the weakest precondition.]
  Selecione uma opção:
    a. {x ≥ 0} x :=  x + y; y := x - y {y > 0} ---------------
    b. {x > 0} x := z - x; y := z - x {y > 0}
    c. {x < y} x := z - x; y := z - y {x > y}
    e. {x > 0} z := 1; y := x + z {y > 0}

  Which of the following expressions gives the weakest precondition of the following Hoare triple?
  {wp} if  x > y then z := x else z := y {z < x}
  Selecione uma opção:
    a. true
    b. x > y  
    c. false ----------------------------------------------------
    d. y > x
    e.
*/

function F(n: nat): nat { if n <= 2 then n else F(n-1) + F(n-3)}

method calcF(n: nat) returns (res: nat)  
 ensures res == F(n) 
{
  assert true; // P
  assert 0 <= n && 0 == F(0) && 1 == F(0 + 1) && 2 == F(0 + 2); // wp
  var a, b, c := 0, 1, 2;
  assert 0 <= n && a == F(0) && b == F(0 + 1) && c == F(0 + 2); // wp
  var i := 0;
  assert i <= n && a == F(i) && b == F(i + 1) && c == F(i + 2); // I
  while i < n 
    decreases n - i
    invariant i <= n
    invariant a == F(i)
    invariant b == F(i + 1)
    invariant c == F(i + 2)
  {
    ghost var v0 := n - i;
    assert i <= n && a == F(i) && b == F(i + 1) && c == F(i + 2) && i < n && v0 == n - i;// I && C && V=V0
    assert i < n && b == F(i + 1) && c == F(i + 2) && a + c == F(i + 3) && 0 <= n - i - 1< v0; // wp
    a, b, c := b, c, a + c;   
    assert i + 1 <= n && a == F(i+1) && b == F(i + 2) && c == F(i + 3) && 0 <= n - i - 1< v0; // wp     
    i := i + 1;
    assert i <= n && a == F(i) && b == F(i + 1) && c == F(i + 2) && 0 <= n - i< v0; // I && 0 <= V < V0
  }
  assert i <= n && a == F(i) && b == F(i + 1) && c == F(i + 2) && !(i < n); // I && !C 
  assert a == F(n); // wp
  res := a;
  assert res == F(n); // Q
}

/*
  Implications
  1) I && !C => Q <=> i <= n && a = F(i) && b = F(i + 1) && c = F(i + 2) && !(i < n) => a = F(n) <=>
  i = n && a = F(n) && b == F(n + 1) && c == F(n + 2) => a = F(n) <=> true

  2) i <= n && a == F(i) && b == F(i + 1) && c == F(i + 2) && i < n && v0 == n - i => 
     i < n && b == F(i + 1) && c == F(i + 2) && a + c == F(i + 3) && 0 <= n - i - 1< v0 <=>
     i < n && a == F(i) && b == F(i + 1) && c == F(i + 2) && v0 == n - i =>
     i < n && b == F(i + 1) && c == F(i + 2) && a + c == F(i + 3) && 0 <= n - i - 1< v0 <=> true since F(i) + F(i + 2) = F(i + 3)
*/

type T = nat 
// Given a non-empty array 'a' of natural numbers, generates a new array ‘b’ 
// (buckets) such that b[k] gives the number of occurrences of 'k' in 'a',
// for 0 <= k <= m, where 'm' denotes the maximum value in 'a'.
method makeBuckets(a: array<T>) returns(b: array<nat>) 
  requires a.Length > 0 
  ensures b.Length > 0 && isMax(b.Length - 1, a[..])
  ensures forall k :: 0 <= k < b.Length ==> b[k] == count(k, a[..])
{
  var max := findMax(a[..]);
  b := new T[1 + max];
  forall k | 0 <= k <= max { b[k] := 0; }
  
  var i := 0;
  while i < a.Length 
  decreases a.Length - i
  invariant i <= a.Length
  invariant forall k :: 0 <= k < b.Length ==> b[k] == count(k, a[..i])
  {
    b[a[i]] := b[a[i]] + 1; 
    i := i + 1;
  } 
  assert a[..] == a[..a.Length]; // might be useful to help Dafny doing proofs...
}

// Auxiliary function that finds the maximum value in a non-empty sequence.
function method findMax(s: seq<T>) : T
  requires |s| > 0 
  ensures isMax(findMax(s), s)
{
  if |s| == 1 then s[0] else (var m := findMax(s[1..]); if m > s[0] then m else s[0])
}

// Auxiliary predicate that checks if 'x' is a maximum in sequence 's'.
predicate isMax(x: T, s: seq<T>) 
{
  (exists k :: 0 <= k < |s| && x == s[k]) && (forall k :: 0 <= k < |s| ==> x >= s[k])
}

// Auxiliary function that counts the number of occurrences of 'x' in sequence 's'.
function count(x: T, s: seq<T>) : nat { multiset(s)[x] }

// A simple test case (checked statically)
method testMakeBuckets() {
  var a := new nat[6] [1, 1, 3, 3, 3, 5];
  assert a[..] == [1, 1, 3, 3, 3, 5];
  var b := makeBuckets(a);
  assert b[..] == [0, 2, 0, 3, 0, 1]; 
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