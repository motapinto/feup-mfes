datatype TaskStatus = Created | Started | Finished

class {:autocontracts} Task {
  const name: string;
  const precedingTasks: set<Task>;
  var status: TaskStatus; 

  // Class invariant: a task can only start after
  // the preceding tasks have finished
  predicate Valid()
    reads this, precedingTasks
  {
    (exists t :: t in precedingTasks && t.status != Finished)
    ==> this.status == Created
  }

  constructor (name: string, precedingTasks: set<Task>)
    ensures this.name == name
    ensures this.precedingTasks == precedingTasks
    ensures this.status == Created
  {
    this.name := name;
    this.precedingTasks := precedingTasks;
    this.status := Created;
  }

  method start()
    requires status == Created
    requires forall t :: t in precedingTasks ==> t.status == Finished
    ensures status == Started
  {
    status := Started;
  }
    
  method finish()
    requires status == Started
    ensures status == Finished 
  {
    status := Finished;
  }
}


method testTask() {
    var t1 := new Task("Task 1", {});
    var t2 := new Task("Task 2", {});
    var t3 := new Task("Task 3", {t1, t2});
    assert t1.status == Created;
    t1.start();
    assert t1.status == Started;
    t2.start();
    t2.finish();
    t1.finish();
    assert t1.status == Finished;
    t3.start();
    t3.finish();
}