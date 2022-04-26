// SWEN90010 2022 Assignment 2
//
// Submission by: Liguo Chen (851090) and Nico Eka Dinata (770318)

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
  // or the below
  // all dao : DAO & objs | dao.credit' = dao.credit
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
  amt >= 0 and amt <= active_obj.balance

  // push new stack frame onto stack if not exceeding seq length bound
  one sf : StackFrame |
    sf.caller = active_obj and
    sf.callee = dest and
    Stack.callstack' = Stack.callstack.add[sf] and
    #(Stack.callstack') = add[#(Stack.callstack), 1]

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
  // VULNERABILITY_FIX: this no longer holds because we _do_ want to update
  // the credit of the calling object to 0 atomically with the DAO transferring
  // some its balance to another object.
  // credit' = credit

  // VULNERABILITY_FIX: this gets added to make sure the transferring of the
  // DAO's balance and the updating of the object's credit happens within the
  // same operation/transition.
  DAO.credit' = DAO.credit ++ (sender -> 0)

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
  // VULNERABILITY_FIX: this no longer happens in this operation and instead
  // happens in the same one as the one where the DAO calls to transfer some
  // of its balance to an object.
  // DAO.credit' = DAO.credit ++ (sender -> 0)
  
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


//////////////////////////////////////////////////////////////////////
// Finding the attack

// FILL IN HERE

/*
 * This check asserts that if some non-DAO object calls the DAO to transfer
 * its credit (either to itself or to other objects), there should only ever
 * be one stackframe describing this call in the callstack. What this means is
 * that a non-DAO object cannot call the DAO to withdraw its credit multiple
 * times in the same stack (recursively).
 *
 * The reason why we think this assertion characterises a security property of
 * the DAO is derived from the fact that when the DAO is called by an object,
 * the reduction of the DAO's balance and the update of the object's credit to
 * 0 are not atomic (happen in separate transitions). Therefore, a potential
 * attack on the system could play out in the following steps of actions:
 * 1. Attacker object A calls the DAO to withdraw its credit to itself.
 *    call[DAO, A, 0]
 * 2. This will lead to the DAO calling the object A to transfer some amount
 *    from the DAO's balance to A.
 *    dao_withdraw_call (which will call A)
 * 3. A is now the active object, and can call the DAO again to withdraw its
 *    credit (which should be 0 now) to itself again.
 *    call[DAO, A, 0]
 * 4. The DAO calls A again to transfer its balance to A (an attack!).
 *    dao_withdraw_call (which will call A)
 *
 * Step 4 above should not actually reduce the DAO's balance because A's credit
 * should have been 0 from the first call, but it's not because its credit is
 * only updated when A returns to the DAO, which hasn't happened yet. Instead,
 * now A seemingly has infinite credit as it can keep withdrawing its credit to
 * transfer to any object of its choosing, which violates the DAO_inv invariant.
 *
 */
assert no_infinite_withdrawal {
  always {
    all sf : StackFrame, o : (Object - DAO) |
    {
      sf.caller = o
      sf.callee = DAO
      sf in Stack.callstack.elems
    } => one Stack.callstack.indsOf[sf]
  }
}

check no_infinite_withdrawal

//////////////////////////////////////////////////////////////////////
// Checks for legitimate behaviour

// check that an object can transfer its balance to another non-DAO object
objs_can_transfer_balance: run {
  some o1, o2 : (Object - DAO), arg : Data |
  {
    o1.balance = 1
    o2.balance = 0
    active_obj = o1
    call[o2, arg, 1]
    after {
      active_obj = o2
      o1.balance = 0
      o2.balance = 1
    }
  }
} for 3

// check that an object can transfer its credit to another non-DAO object
objs_can_transfer_credit: run {
  some o1, o2 : (Object - DAO) |
    {
      o1.balance = 1
      o2.balance = 0
      active_obj = o1
      DAO.balance = 1
      DAO.credit[o1] = 1
      call[DAO, o2, 0]
      after {
        dao_withdraw_call
        after {
          o2.balance = 1
          DAO.credit[o1] = 0
        }
      }
    }
} for 3

// check that an object can withdraw its credit to itself
objs_can_withdraw_to_self: run {
  some objA : (Object - DAO) |
  {
    #(Stack.callstack) = 1
    objA.balance = 1
    active_obj = objA
    DAO.balance = 1
    DAO.credit[objA] = 1
    call[DAO, objA, 0]
    after {
      dao_withdraw_call
      after {
        DAO.credit[objA] = 0
        objA.balance = 2
        active_obj = objA
        return
        after {
          active_obj != objA
          DAO.credit[objA] = 0
          objA.balance = 2
          dao_withdraw_return
          after (#(Stack.callstack) = 1)
        }
      }
    }
  }
} for 3

