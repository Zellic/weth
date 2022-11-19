from z3 import *
# set_param(proof=True)
set_param(unsat_core=True)

# helper funcs and boilerplate. sets up a test framework

predicates = {}
my_proofs = {}

def require(s, assertion):
    # black magic introspection shit
    import traceback,ast
    frame = traceback.extract_stack()[-2]
    code = frame.line
    yea = ast.parse(code)
    yea = list(ast.iter_child_nodes(next(ast.iter_child_nodes(next(ast.iter_child_nodes(yea))))))[2]
    yea = ast.unparse(yea)

    p = FreshBool()
    predicates[p] = (yea, frame.lineno, frame.name)
    s.assert_and_track(assertion, p)

def print_unsat_core(s):
    for p in s.unsat_core():
        code, lineno, name = predicates[p]
        print(f'* {str(p):5} {"line " + str(lineno):9} {name:16}  {code}')


def my_proof(s, name=None):
    def decorating_function(user_function):
        if name is None:
            assert(user_function.__name__.startswith('proof_'))
            _name = user_function.__name__[6:]
        else:
            _name = name # shadowing bullshit
        def decorated_function(*args, **kwargs):
            s.push()
            user_function(*args, **kwargs)
            assert(s.check() == unsat)
            print('Unsat core:')
            print_unsat_core(s)
            s.pop()
        my_proofs[_name] = decorated_function
        return decorated_function
    return decorating_function

def run_proof(name):
    func = my_proofs[name]
    print(name)
    func()
    print('-> ok')

def run_proofs():
    for name in my_proofs:
        run_proof(name)

# actual WETH stuff

AddressSort = BitVecSort(160)
Address = lambda x: BitVecVal(x, AddressSort)
UintSort    = BitVecSort(256)
Uint = lambda x: BitVecVal(x, UintSort)

WETH_Address = BitVec('WETH_Address', AddressSort)
MAX_ETH = Uint(120000000e18)

# WETH state = tuple (balanceOf: Array<..>, allowance: Array<..>)

# global state = tuple (balances: ArraySort(AddressSort, UintSort), WETH state)

# deposit() = tuple (msg.sender: AddressSort, msg.value: UintSort)
def deposit(s, state, msg_sender, msg_value):
    eth_balances, weth_state = state
    balanceOf, allowance = weth_state

    # implicit from how EVM works
    require(s, UGE(eth_balances[msg_sender], msg_value))
    eth_balances = Store(eth_balances, msg_sender, eth_balances[msg_sender] - msg_value)
    eth_balances = Store(eth_balances, WETH_Address, eth_balances[WETH_Address] + msg_value)

    # balanceOf[msg.sender] += msg.value;
    balanceOf = Store(balanceOf, msg_sender, balanceOf[msg_sender] + msg_value)
    # Deposit(msg.sender, msg.value);

    return (eth_balances, (balanceOf, allowance))

# withdraw() = tuple (msg.sender: AddressSort, wad: UintSort)
def withdraw(s, state, msg_sender, wad):
    eth_balances, weth_state = state
    balanceOf, allowance = weth_state

    # require(balanceOf[msg.sender] >= wad);
    require(s, UGE(balanceOf[msg_sender], wad))
    # balanceOf[msg.sender] -= wad;
    balanceOf = Store(balanceOf, msg_sender, balanceOf[msg_sender] - wad)
    # msg.sender.transfer(wad);
    require(s, UGE(eth_balances[WETH_Address], wad))
    eth_balances = Store(eth_balances, msg_sender, eth_balances[msg_sender] + wad)
    eth_balances = Store(eth_balances, WETH_Address, eth_balances[WETH_Address] - wad)
    # Withdrawal(msg.sender, wad);

    return (eth_balances, (balanceOf, allowance))

def approve(s, state, msg_sender, guy, wad):
    eth_balances, weth_state = state
    balanceOf, allowance = weth_state

    # allowance[msg.sender][guy] = wad;
    allowance = Store(allowance, msg_sender, Store(allowance[msg_sender], guy, wad))
    # Approval(msg.sender, guy, wad);

    return (eth_balances, (balanceOf, allowance))

def transfer(s, state, msg_sender, dst, wad):
    return transferFrom(s, state, msg_sender, msg_sender, dst, wad)

def transferFrom(s, state, msg_sender, src, dst, wad):
    eth_balances, weth_state = state
    balanceOf, allowance = weth_state

    # require(balanceOf[src] >= wad);   
    require(s, UGE(balanceOf[src], wad))

    p = And(src != msg_sender, allowance[src][msg_sender] != Uint(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff))
    require(s, Implies(p, UGE(allowance[src][msg_sender], wad)))
    allowance = If(p, Store(allowance, src, Store(allowance[src], msg_sender, allowance[src][msg_sender] - wad)), allowance)

    balanceOf = Store(balanceOf, src, balanceOf[src]-wad)
    balanceOf = Store(balanceOf, dst, balanceOf[dst]+wad)


    return (eth_balances, (balanceOf, allowance))   

def initial_state():
    s = Solver()

    myUser = Const('myUser', AddressSort)
    initialDeposit = Const('initialDeposit', UintSort)
    balanceOf = Array('balanceOf', AddressSort, UintSort)
    allowance = Array('allowance', AddressSort, ArraySort(AddressSort, UintSort))
    eth_balances = Array('eth_balances', AddressSort, UintSort)

    # This is a manually defined constraint.
    # We proved that in horn.py, but this lemma needs to be manually imported.
    a = Const('a', AddressSort)
    require(s, ForAll([a], ULE(balanceOf[a], eth_balances[WETH_Address])))
    require(s, ForAll([a], ULE(eth_balances[a], MAX_ETH)))

    # assumptions
    balanceOf = Store(balanceOf, myUser, Uint(0))
    require(s, myUser != WETH_Address)
    require(s, ForAll([a], allowance[myUser][a] == 0))
    starting_balance = eth_balances[myUser]

    weth_state = (balanceOf, allowance)
    state = (eth_balances, weth_state)

    state = deposit(s, state, myUser, initialDeposit)

    return s, state, myUser, initialDeposit, starting_balance

def is_ok(s, state, myUser, initialDeposit, starting_balance):
    s2 = Solver() # create a new solver and load it up with the assertions from a simulated withdrawal by our depositor
    new_state = withdraw(s2, state, myUser, initialDeposit)
    eth_balances, weth_state = new_state
    p = And(s2.assertions()) # copy all of those assertions over into our predicate
    p = And(p, eth_balances[myUser] == starting_balance) # final balance check. technically optional, second clause always true if p is true
    return p

# any external call to deposit
def symbolic_deposit(s, state, myUser):
    user = FreshConst(AddressSort, 'user')
    value = FreshConst(UintSort, 'value')
    
    require(s, user != WETH_Address)
    require(s, user != myUser)
    
    state = deposit(s, state, user, value)
    return state

# any external call to withdraw
def symbolic_withdraw(s, state, myUser):
    user = FreshConst(AddressSort, 'user')
    wad = FreshConst(UintSort, 'wad')

    require(s, user != WETH_Address)
    require(s, user != myUser)

    state = withdraw(s, state, user, wad)
    return state

def symbolic_approve(s, state, myUser):
    user = FreshConst(AddressSort, 'user')
    guy = FreshConst(AddressSort, 'guy')
    wad = FreshConst(UintSort, 'wad')

    require(s, user != WETH_Address)
    require(s, user != myUser)

    state = approve(s, state, user, guy, wad)
    return state

def symbolic_transfer(s, state, myUser):
    user = FreshConst(AddressSort, 'user')
    dst = FreshConst(AddressSort, 'dst')
    wad = FreshConst(UintSort, 'wad')

    require(s, user != WETH_Address)
    require(s, user != myUser)

    state = transfer(s, state, user, dst, wad)
    return state

def symbolic_transferFrom(s, state, myUser):
    user = FreshConst(AddressSort, 'user')
    src = FreshConst(AddressSort, 'src')
    dst = FreshConst(AddressSort, 'dst')
    wad = FreshConst(UintSort, 'wad')

    require(s, user != WETH_Address)
    require(s, user != myUser)

    state = transferFrom(s, state, user, src, dst, wad)
    return state

# ok let's actually prove shit

s, state, myUser, initialDeposit, starting_balance = initial_state()

def sanity_check(cur_state, starting_balance):
    # sanity check. Let's make sure the initial state is valid
    s.push()
    s.add(Not(is_ok(s, cur_state, myUser, initialDeposit, starting_balance)))
    assert(s.check() == unsat)
    s.pop()

sanity_check(state, starting_balance)

# each of these proofs is an inductive step.
# Given a (valid) initial state, prove that the final state after an
# arbitrary state transition is NOT invalid.
# Therefore, it would be impossible to reach an invalid state.

# each of these sub-proofs is a subgoal that checks a possible class
# of state transitions.
# together, they show that after any arbitrary transaction (within certain limitations)
# cannot break our invariants.
@my_proof(s)
def proof_deposit():
    new_state = symbolic_deposit(s, state, myUser)
    require(s, Not(is_ok(s, new_state, myUser, initialDeposit, starting_balance)))

@my_proof(s)
def proof_withdraw():
    new_state = symbolic_withdraw(s, state, myUser)
    require(s, Not(is_ok(s, new_state, myUser, initialDeposit, starting_balance)))

@my_proof(s)
def proof_approve():
    new_state = symbolic_approve(s, state, myUser)
    require(s, Not(is_ok(s, new_state, myUser, initialDeposit, starting_balance)))

@my_proof(s)
def proof_transfer():
    new_state = symbolic_transfer(s, state, myUser)
    require(s, Not(is_ok(s, new_state, myUser, initialDeposit, starting_balance)))

@my_proof(s)
def proof_transferFrom():
    new_state = symbolic_transferFrom(s, state, myUser)
    require(s, Not(is_ok(s, new_state, myUser, initialDeposit, starting_balance)))

run_proofs()
