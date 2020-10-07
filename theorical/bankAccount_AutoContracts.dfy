class {:autocontracts} BankAccount {
  var balance: real;
  
  // class invariant
  predicate Valid()
  {
    balance >= 0.0
  }

  constructor (initialBalance: real)
    requires initialBalance >= 0.0
    ensures balance == initialBalance
  {
    balance := initialBalance;
  }

  function method getBalance() : real
  {
    balance
  }

  method deposit(amount : real)
    requires amount > 0.0
    ensures balance == old(balance) + amount
  {
    balance := balance + amount;
  }

  method withdraw(amount : real)
    requires 0.0 < amount <= balance
    ensures balance == old(balance) - amount
  {
    balance := balance - amount;
  }

  method transfer(amount : real, destination: BankAccount)
    requires 0.0 < amount <= balance && destination != this
    requires destination.Valid()
    modifies this, destination
    ensures destination.Valid() 
    ensures balance == old(balance) - amount
    ensures destination.balance == old(destination.balance) + amount
  {
    this.balance := this.balance - amount;
    destination.balance:= destination.balance + amount;
  }
}

// A simple test case.
method testBankAccount()
{
  var a := new BankAccount(10.0);
  assert a.getBalance() == 10.0;

  var b := new BankAccount(0.0);
  assert b.getBalance() == 0.0;

  a.deposit(10.0);
  assert a.getBalance() == 20.0;

  a.withdraw(5.0);
  assert a.getBalance() == 15.0;

  a.transfer(15.0, b);
  assert a.getBalance() == 0.0;
  assert b.getBalance() == 15.0;
}