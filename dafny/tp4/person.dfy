datatype Sex = Masculine | Feminine
datatype CivilState = Single | Married | Divorced | Widow | Dead
 
class Person
{
  const name: string; // ‘const’ for immutable fields
  const sex: Sex;
  const mother: Person?; // ‘?’ to allow null
  const father: Person?;
  var spouse: Person?;
  var civilState: CivilState;

  ghost const ancestors : set<Person>; // codigo executavel, que serve para fazer verificacoes e n aparece no codigo final

  // Class invariant
  predicate Valid()
    reads this, spouse
  {
    (civilState == Married <==> spouse != null) &&
    (civilState in {Single, Divorced, Widow, Dead} <==> spouse == null) &&
    (mother != null ==> mother.sex == Feminine) &&
    (father != null ==> father.sex == Masculine) &&
    (civilState == Married ==> (sex != spouse.sex && spouse.spouse == this)) &&
    ancestors ==
      (if mother != null then {mother} + mother.ancestors else {}) +
      (if father != null then {father} + father.ancestors else {})
  }
 
  constructor (name: string, sex: Sex, mother: Person?, father: Person?)
    requires mother != null ==> mother.sex == Feminine
    requires father != null ==> father.sex == Masculine

    ensures Valid()
    ensures this.name == name
    ensures this.sex == sex
    ensures this.mother == mother
    ensures this.father == father
    ensures this.civilState == Single
  {
    this.name := name;
    this.sex := sex;
    this.mother := mother;
    this.father := father;
    this.spouse := null;
    this.civilState := Single;
    this.ancestors :=
      (if mother != null then {mother} + mother.ancestors else {}) +
      (if father != null then {father} + father.ancestors else {});
  }
 
  method marry(spouse: Person)
    modifies this, spouse
    
    requires Valid() && spouse.Valid()
    requires civilState !in {Married, Dead}
    requires spouse.sex != sex
    requires spouse.civilState !in {Married, Dead}
    // check ancestors   
    requires spouse !in ancestors
    requires father != spouse.father || (father == null && spouse.father == null)
    requires mother != spouse.mother || (mother == null && spouse.mother == null)
    
    ensures this.spouse == spouse
    ensures civilState == Married
    ensures spouse.civilState == Married

    ensures spouse.spouse == this
    ensures Valid()
    ensures spouse.Valid()
  {
    spouse.spouse := this;
    spouse.civilState := Married;
    this.spouse := spouse;
    this.civilState := Married;
  }
 
  method divorce()
    modifies this, spouse

    requires Valid()
    requires civilState in {Married}
    requires spouse.Valid()

    ensures civilState == Divorced
    ensures old(spouse).civilState == Divorced
    ensures Valid()
    ensures old(spouse).Valid()
  {
    spouse.spouse := null;
    spouse.civilState := Divorced;
    this.spouse := null;
    this.civilState := Divorced;
  }
 
  method die()
    modifies this, spouse

    requires Valid()
    requires civilState !in {Dead}
    requires spouse != null ==> spouse.Valid()

    ensures civilState == Dead
    ensures old(spouse) != null ==> old(spouse).civilState == Widow
    ensures Valid()
    ensures old(spouse) != null ==> old(spouse).Valid()
  {
    if spouse != null
    {
      spouse.spouse := null;
      spouse.civilState := Widow;
    }
    this.spouse := null;
    this.civilState := Dead;
  }
}

method Main()
{
  var father := new Person("Father", Masculine, null, null);
  var mother := new Person("Mother", Feminine, null, null);
  assert father.civilState == Single;
  assert mother.civilState == Single;

  father.marry(mother);
  assert father.civilState == Married;
  assert mother.civilState == Married;
  assert father.spouse == mother;
  assert mother.spouse == father;

  var son1 := new Person("Son1", Masculine, mother, father);
  var son2 := new Person("Son2", Feminine, mother, father);
  assert son1.civilState == Single;
  assert son2.civilState == Single;
  
  mother.divorce();
  assert father.civilState == Divorced;
  assert mother.civilState == Divorced;
  assert mother.spouse == null;
  assert father.spouse == null;
  
  father.die();
  assert mother.spouse == null;
  assert father.civilState == Dead;

  //son1.marry(son2); => triggers error
}
