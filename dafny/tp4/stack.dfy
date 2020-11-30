type T = int // to allow doing new T[capacity], but can be other type 
 
class {:autocontracts} Stack // => evitar por no construtor ensures Valid() e nos outros metodos requires Valid() e ensures Valid()
{
  const elems: array<T>; // immutable (pointer)
  var size : nat; // used size

  // Class invariant
  predicate Valid()
    reads this
  {
    size <= elems.Length // the size of the stack does not exceed the allocated capacity
  }
 
  constructor (capacity: nat)
    // ensures Valid() inserted by {:autocontracts}
    requires capacity > 0
    ensures isEmpty()
    ensures elems.Length == capacity
  {
    elems := new T[capacity];
    size := 0; 
  }
 
  predicate method isEmpty()
    // requires Valid() inserted by {:autocontracts}
    // ensures Valid() inserted by {:autocontracts}
    // normally we don't have post conditions for predicate methods
  {
    size == 0
  }
 
  predicate method isFull()
    // requires Valid() inserted by {:autocontracts}
    // ensures Valid() inserted by {:autocontracts}
    // normally we don't have post conditions for predicate methods
  {
    size == elems.Length
  }
 
  method push(x : T)
    // requires Valid() inserted by {:autocontracts}
    // ensures Valid() inserted by {:autocontracts}
    requires !isFull()
    ensures size == old(size) + 1
    ensures elems[..size] == old(elems[..size]) + [x]
  {
    elems[size] := x;
    size := size + 1;
  }
 
  function top(): T
    // requires Valid() inserted by {:autocontracts}
    // ensures Valid() inserted by {:autocontracts}
    requires !isEmpty()
  {
    elems[size-1]
  }
    
  method pop() 
    // requires Valid() inserted by {:autocontracts}
    // ensures Valid() inserted by {:autocontracts}
    requires !isEmpty()
    ensures size == old(size) - 1

    ensures elems[..size] == old(elems[..size-1])
  {
    size := size-1;
  }
}
 
// A simple test case.
method Main()
{
  var s := new Stack(3);
  assert s.isEmpty();
  s.push(1);
  s.push(2);
  s.push(3);
  assert s.top() == 3;
  assert s.isFull();
  s.pop();
  assert s.top() == 2;
}
