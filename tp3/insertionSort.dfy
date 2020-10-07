// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
  requires 0 <= from <= to <= a.Length
  reads a
{
  forall i, j :: from <= i < j < to ==> a[i] <= a[j] 
}

// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>)
  modifies a  
  ensures isSorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var i := 0;
  while i < a.Length 
		decreases a.Length - i 
		invariant 0 <= i <= a.Length
		invariant multiset(a[..]) == multiset(old(a[..]))
		invariant isSorted(a, 0, i) // I ^ not(i <= a.Length) => sorted(a, 0, a.Length) <=> sorted(a,0,i) ^ 0 <= i <= a.Length ^ i >= a.Length <=> sorted(a, 0, a.Length) ^ i = a.Length
  {
		var j := i;
		while j > 0 && a[j-1] > a[j]
			decreases j
			invariant 0 <= j <= i
			invariant multiset(a[..]) == multiset(old(a[..]))
			// I ^ not(C) => Q <=> I ^ not(j > 0 && a[j-1] > a[j]) => isSorted(a, 0, i + 1) <=> I ^ (j <= 0 || a[j-1] <= a[j]) ... <=> j == 0 => isSorter(a, 0, )
			invariant forall m, n :: 0 <= m <= n <= i && m != j && n != j ==> a[m] <= a[n] // all elements sorted if a[j] is removed
			invariant isSorted(a, j, i +1) // all the elements at and after j are sorted
		{
			a[j-1], a[j] := a[j], a[j-1];
			j := j - 1;
		}
		i := i + 1;
  }
}

// Simple test case to check the postcondition
method testInsertionSort() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 9, 4, 3, 6, 8;

  assert a[..] == [9, 4, 3, 6, 8];
  insertionSort(a);
  assert a[..] == [3, 4, 6, 8, 9];
}

