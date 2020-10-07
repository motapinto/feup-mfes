trait Figure {
  var center: (real, real);

  predicate Valid()
    reads this
    
  function method getSizeX(): real
    requires Valid()
    reads this

  function method getSizeY(): real
    requires Valid()
    reads this
  
  method resize(factor: real)
    requires factor > 0.0 && Valid()
    modifies this
    ensures Valid()
    ensures getSizeX() == factor * old(getSizeX()) 
    ensures getSizeY() == factor * old(getSizeY())
    ensures center == old(center) 
}

class Circle extends Figure {
  var radius: real;

  predicate Valid()
    reads this
  {
    radius > 0.0
  }

  constructor Circle(center: (real, real), radius: real)
    requires radius > 0.0
    ensures this.center == center && this.radius == radius && Valid()
  {
    this.center := center;
    this.radius := radius;
  }
  
  function method getSizeX(): real
    requires Valid()
    reads this
  {
    radius
  }

  function method getSizeY(): real
    requires Valid()
    reads this
  {
    radius
  }

  method resize(factor: real)
    requires factor != 0.0 && Valid()
    modifies this
    ensures center == old(center)
    ensures radius == abs(factor) * old(radius)
    ensures Valid()
  {
    radius := abs(factor) * radius;
  }

  function method abs(x: real): real
  {
    if x >= 0.0 then x else -x 
  }
}