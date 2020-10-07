// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
predicate isSorted(a: array<real>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{
  forall i, j :: from <= i < j < to ==> a[i] <= a[j] 
}

// Sorts array 'a' using selection sort algorithm
method selectionSort(a: array<real>) 
  modifies a // permission to change a[]
  ensures isSorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..])) // 'a' is a permutation of old_a
{
  var i:= 0;
  while i < a.Length - 1 
    decreases a.Length -1 - i
    invariant 0 <= i <= a.Length
    invariant isSorted(a, 0, i)
    invariant forall lhs, rhs :: 0 <= lhs < i <= rhs < a.Length ==> a[lhs] <= a[rhs]; // ??? 
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := findMin(a, i, a.Length); // minimum in remaing subarray
    a[i], a[j] := a[j], a[i]; // swap
    i := i + 1;
  }
}

/**
  Finds the position of a minimum value in a non-empty subarray 'a' between positions
  'from' (inclusive) and 'to' (exclusive)
 */
method findMin(a: array<real>, from: nat, to: nat) returns (index: nat) 
  requires 0 <= from < to <= a.Length
  ensures from <= index < to 
  ensures forall k :: from <= k < to ==> a[k] >= a[index]
{
  var i:= from + 1; 
  index := from; // position of min up to position i (excluded)
  while i < to 
    decreases a.Length - i
    invariant from <= index < i <= to 
    invariant forall k :: from <= k < i ==> a[k] >= a[index]
  {
    if a[i] < a[index] {
      index := i;
    }
    i := i + 1;
  }
}

method testSelectionSort() {
  var a:= new real[5] [9.0, 4.0, 6.0, 3.0, 8.0]; // create array
  assert a[..] == [9.0, 4.0, 6.0, 3.0, 8.0]; // convert to sequence
  selectionSort(a);
  assert a[..] == [3.0, 4.0, 6.0, 8.0, 9.0]; 
}

method testFindMin() {
  var a:= new real[5] [9.0, 5.0, 6.0, 4.0, 8.0];
  assert a[..] == [9.0, 5.0, 6.0, 4.0, 8.0]; // convert to sequence
  var m := findMin(a, 0, 5);
  assert a[3] == a[m] == 4.0; // pq é preciso? -> nao consegue provar automaticamente, é uma limitação do dafny
  assert m == 3;
}

/**
  Nao esquecer que os testes apenas vêm as pre e pos condiçoes. Sao uma especie de black box
  e apenas isso é verificado

  No caso da especificação e verificação como nao estamos preocupados com questoes de eficiencia 
  podemos usar coisas mais alto nivel como é o caso das sequencias
 */