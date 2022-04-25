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
  DAO in objs => DAO.credit' = DAO.credit
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

  // can only occur when:
  // - `amt` >= 0
  // - `amt` doesn't exceed balance of currently active object
  amt >= 0 and amt =< active_obj.balance

  // TODO: check if stack has not exceeded its max length bound?

  // push new stack frame onto stack
  one sf : StackFrame |
    sf.caller = active_obj and
    sf.callee = dest and
    Stack.callstack' = Stack.callstack.add[sf]

  // update `Invocation`
  Invocation.op' = Call
  Invocation.param' = arg

  // deduct `amt` from balance of active object
  active_obj.balance' = sub[active_obj.balance, amt]

  // add `amt` to balance of `dest`
  dest.balance' = add[dest.balance, amt]

  // balance of all other objects are unchanged
  all o : (Object - active_obj - dest) | o.balance' = o.balance

  // if active object is not the DAO, then no credit can change
  active_obj != DAO => DAO.credit' = DAO.credit
}

// return
// holds when the active object returns to its caller
pred return {
  // FILL IN HERE

  // callstack cannot be empty
  not Stack.callstack.isEmpty

  // set invocation
  Invocation.op' = Return
  Invocation.param' = none

  // pop top stack frame from the stack
  Stack.callstack' = Stack.callstack.butlast

  // balance of all objects cannot change
  all o : Object | o.balance' = o.balance

  // if active object who returned is not the DAO, then no credit can change
  active_obj != DAO => DAO.credit' = DAO.credit
}



// dao_withdraw_call holds when an object calls The DAO to
// withdraw all of its credit in the DAO
// the argument (parameter) to the call is the object to send the withdrawed funds to
// (this is not necessarily the same object as the caller/sender)
// The caller's DAO credit will be transferred to the object indicated by the argument
pred dao_withdraw_call {
  active_obj = DAO and Invocation.op = Call

  // DAO credit doesn't change (the caller's credit is deducted after the call below returns
  // credit' = credit // VULN: comment this to fix vuln.

  DAO.credit' = DAO.credit ++ (sender -> 0) // VULN: uncomment this to fix vuln.
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
  // DAO.credit' = DAO.credit ++ (sender -> 0) // VULN: comment this to fix vuln.
  
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

  // DAO's balance is sufficient to cover all other objects' credits
  DAO.balance >= sum_DAO_credit

  // Credit of each other object is non-negative
  all o : (Object - DAO) | DAO.credit[o] >= 0
}

// Enable below code to see the case when `DAO_inv` doesn't hold
// TODO: remove this before submission
/*
assert inv_always {
  always DAO_inv
}

check inv_always
*/

//////////////////////////////////////////////////////////////////////
// Finding the attack

// FILL IN HERE

assert no_infinite_withdrawal {
// stack could only contain one stackframe of an object calling the DAO?
//  always {
//    all sf : StackFrame, o : (Object - DAO) |
//    (sf.caller = o and sf.callee = DAO and sf in Stack.callstack.elems) => one Stack.callstack.indsOf[sf]
//  }

  // for all non-DAO objects, if calling the DAO on the object results in the
  // invariant not holding, it should be the case that eventually the op
  // `dao_withdraw_return` holds and the invariant gets restored
  all o : (Object - DAO), amt : one Int |
  {
      call[DAO, o, amt] and
      after (dao_withdraw_call and after (not DAO_inv))
  } => after after (eventually (dao_withdraw_return and DAO_inv))
}

check no_infinite_withdrawal for 7 seq
