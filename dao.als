// SWEN90010 2022 Assignment 2
//
// Submission by: <insert your names and student numbers here>

//////////////////////////////////////////////////////////////////////
// don't delete this line (imposes an ordering on the atoms in the Object set
open util/ordering[Object] as obj_order

// some machinery to implement summing up object balances and DAO credit
// these definitions are recursive. Turn on recursive processing by
// going to Options menu -> Recursion depth -> 3

// don't delete or change this definition
fun sum_rel_impl_rec[r : Object -> one Int, e : one Object]: one Int {
  e = obj_order/last => r[e] else add[r[e],sum_rel_impl_rec[r, obj_order/next[e]]]
}

// sum up all of the credit stored by the DAO on behalf of other objects
fun sum_DAO_credit: one Int {
  sum_rel_impl_rec[DAO.credit + (DAO -> 0), obj_order/first]
}

// sum up all of the object balances
fun sum_Object_balances: one Int {
  sum_rel_impl_rec[balance, obj_order/first]
}

//////////////////////////////////////////////////////////////////////
// Signautres

sig Data {}

// object names are just data
sig Object extends Data {
  var balance : one Int  // is incremented on calls with money included
}

// there are two kinds of invocations: calls and returns
abstract sig Op {}
sig Call, Return extends Op {}

// this state records the currently executing invocation
// op stores what invocation was performed (Call or Return)
// when a Call, param stores the argument passed to the call (if any)
one sig Invocation {
  var op : Op,
  var param : lone Data
}

// a stack frame
sig StackFrame {
  caller : Object,
  callee : Object
}

// the stack is modelled by a sequence of stack frames
// the first frame is the bottom of the stack; the last one is the top
one sig Stack {
  var callstack : seq StackFrame
}


// the DAO stores credit on behalf of other (non-DAO) objects
one sig DAO extends Object {
  var credit : (Object - DAO) -> one Int
}

//////////////////////////////////////////////////////////////////////
// Functions

// the current active object (defined only when the stack is non-empty)
// this is the object that is executing the current invocation
fun active_obj: Object {
  Stack.callstack.last.callee
}

// the sender of the topmost caller on the callstack
fun sender: Object {
  Stack.callstack.last.caller
}

// synonym for sender: when a 'return' is performed, it is the
// returnee who will become the active object
fun returnee: Object {
  Stack.callstack.last.caller
}

//////////////////////////////////////////////////////////////////////
// Predicates

pred objects_unchanged[objs: set Object] {
  // FILL IN THIS DEFINITION
  all obj : objs | obj.balance' = obj.balance
  all dao : DAO & objs | dao.credit' = dao.credit
  //all o : objs | o in DAO => o.credit' = o.credit
}

check all_objects_unchanged_correct {
 always {
  objects_unchanged[Object] => balance' = balance and credit' = credit
  }
} for 5

check DAO_unchanged_correct {
  always {
    objects_unchanged[DAO] => credit' = credit
  }
}

check object_unchanged_balance {
  always {
    all o: Object | objects_unchanged[o] => o.balance' = o.balance  
  }
}

// cal[dest, arg, amt]
// holds when the active object calls object 'dest'
// 'arg' is an optional parameter passed to the call
// e.g. it is used when calling The DAO to specify which
// object to send the withdrawn credit to
// 'amt' is the amount of currency that the active object
// wishes to transfer from its balance to the balance of
// 'dest'. If 'amt' is 0, no funds are transferred.
pred call[dest: Object, arg: lone Data, amt: one Int] {
  // FILL IN HERE
  amt >= 0 and amt <= active_obj.balance
  // TODO: how to check if the stack reaches its max ???
  // Stack.callstack.add [{(caller = active_obj), (callee=dest)}]
  one sf : StackFrame | 
    sf.caller = active_obj and 
    sf.callee = dest and 
    Stack.callstack' = Stack.callstack.add[sf]
  Invocation.op = Call
  Invocation.param = arg
  active_obj.balance' = active_obj.balance - amt
  dest.balance' = dest.balance + amt
  all other : Object - (active_obj + dest) | other.balance' = other.balance
  // If the active object who made the call is not The DAO, then no object’s credit can change.
  active_obj & DAO = none => 
    all obj : DAO.credit.Int | 
      DAO.credit[obj]' = DAO.credit[obj]
  // ??????????????????????????
}

// return
// holds when the active object returns to its caller
pred return {
  // FILL IN HERE
  // there are elements in the callstack set
  not Stack.callstack.isEmpty
  // update the callstack
  Stack.callstack' = Stack.callstack.delete[Stack.callstack.lastIdx]
  Invocation.op = Return
  Invocation.param = none
  // all non-dao objs unchanged
  all o : Object | o.balance' = o.balance
  // If the active object who did the return is not The DAO, then no object’s credit can change.
  // TODO: need a check for the above ???
  }



// dao_withdraw_call holds when an object calls The DAO to
// withdraw all of its credit in the DAO
// the argument (parameter) to the call is the object to send the withdrawed funds to
// (this is not necessarily the same object as the caller/sender)
// The caller's DAO credit will be transferred to the object indicated by the argument
pred dao_withdraw_call {
  active_obj = DAO and Invocation.op = Call

  // DAO credit doesn't change (the caller's credit is deducted after the call below returns
  credit' = credit

  call[Invocation.param, none, DAO.credit[sender]]
}

// dao_withdraw_return holds when the active object returns to The DAO
// after The DAO has called that object, i.e. The DAO has called some object
// (to transfer funds to that object's balance) and now that object has returned
// from that call.
// 'sender' is the original caller who originally invoked The DAO (requesting its
// credit to be withdrawn)
pred dao_withdraw_return {
  active_obj = DAO and Invocation.op = Return

  // set sender's credit to 0 since their credit has now been emptied
  DAO.credit' = DAO.credit ++ (sender -> 0)
  
  return
}


pred untrusted_action {
  DAO not in active_obj and {
  (some dest : Object, arg : Data, amt : one Int | call[dest, arg, amt]) or
  return 
  }
}

pred unchanged {
  balance' = balance
  credit' = credit
  callstack'  = callstack
  param' = param
  op' = op
}

//////////////////////////////////////////////////////////////////////
// Facts

fact trans {
  always { 
    untrusted_action or 
    dao_withdraw_call or
    dao_withdraw_return or
    unchanged
   }
}

// objects must have non-negative balances
// initially we also constrain them to be rather small to prevent integer overflow when
// summing them up using the default sig size for Object of 3
// therefore, initial valid balances are between 0 and 2 inclusive
pred init_balance_valid[b: one Int] {
  gte[b,0] and lte[b,2]
}

fact init {
  #(Stack.callstack) = 1
  active_obj != DAO
  sender != DAO

  all o: Object - DAO | init_balance_valid[DAO.credit[o]]
  all o: Object | init_balance_valid[o.balance]
  DAO_inv
}


//////////////////////////////////////////////////////////////////////
// DAO Invariant

pred DAO_inv {
  // FILL IN HERE
  all dao : DAO |
    dao.balance = sum_DAO_credit and
    // use the relational join (.) to get the domain of the dao.credit, i.e. all objects the dao is storing credit for
    all o : dao.credit.Int |
      o.balance >= 0
}

//////////////////////////////////////////////////////////////////////
// Finding the attack

// FILL IN HERE

