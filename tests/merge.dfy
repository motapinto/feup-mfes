type T = int

predicate sorted(a: array<T>, n: nat)
  reads a
  requires 0 <= n <= a.Length
{
    forall i, j :: 0 <= i < j < n ==> a[i] <= a[j]
}

// Merges two sorted arrays 'a' and 'b' into a new array 'c'
method merge(a: array<T>, b: array<T>) returns (c: array<T>) 
  requires sorted(a, a.Length)
  requires sorted(b, b.Length)
  ensures elems(a, a.Length) + elems(b, b.Length) == elems(c, c.Length)
  ensures sorted(c, c.Length)
{
  c := new T[a.Length + b.Length];
  var i, j := 0, 0; //indices in 'a' and 'b'

  // Repeatedly pick the smallest element from 'a' and 'b' and copy it into 'c'
  while i < a.Length || j < b.Length 
    decreases a.Length - i
    decreases b.Length - j
    invariant 0 <= i <= a.Length && 0 <= j <= b.Length
    //invariant elems a, i) + elems(b, j) == elems(c, i + j)
    //invariant sorted();
    //invariant elems(a, a.Length) - elems(a, i) >= elems(c, i + j)
    //invariant forall x1, y1 :: 0 <= x1 <= i < y1 <= a.Length ==> a[y1] > a[x1]
    //invariant forall x2, y2 :: 0 <= x2 <= i < y2 <= b.Length ==> a[y2] > a[x2]
  {
    if i < a.Length && (j == b.Length || a[i] <= b[j]) {
      c[i + j] := a[i];
      i := i + 1;
    }
    else {
      c[i + j] := b[j];
      j := j + 1;
    }
  }
}

function elems(a: array<T>, n: nat): multiset<T>
  requires n <= a.Length
  reads a
  {
    multiset(a[..n])
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