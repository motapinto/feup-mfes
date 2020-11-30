// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Finds a value 'x' in a sorted array 'a', and returns its index, or -1 if not found. 
method binarySearch(a: array<int>, x: int) returns (index: int)
  requires isSorted(a)
  ensures if x in a[..] then 0 <= index <  a.Length && a[index] == x else index == -1
{   
  var low := 0;
  var high := a.Length;

  while low < high 
    decreases high - low
    invariant 0 <= low <= high <= a.Length
    invariant x !in a[..low] // all the elements before low are not x (exclusive)
    invariant x !in a[high..] // all the elements at and after high are not x (inclusive)
  {
    var mid := (low + high) / 2;
    if 
    {
      case a[mid] < x => low := mid + 1;
      case a[mid] > x => high := mid;
      case a[mid] == x => return mid;
    }
  }
  return -1;
}

// Simple test cases to check the post-condition.
method testBinarySearch() 
{
  var a := new int[5] [1, 4, 4, 6, 8];
  assert a[..]  == [1, 4, 4, 6, 8];

  var id1 := binarySearch(a, 6);
  assert id1 == 3;

  var id2 := binarySearch(a, 3);
  assert id2 == -1;
  
  var id3 := binarySearch(a, 4);
  assert id3 in {1, 2};
}

