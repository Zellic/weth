from z3 import *

AddressSort = BitVecSort(160)
Address = lambda x: BitVecVal(x, AddressSort)
UintSort = BitVecSort(256)
Uint = lambda x: BitVecVal(x, UintSort)
MappingSort = ArraySort(AddressSort, UintSort)

MAX_ETH = Uint(120000000e18)

s = SolverFor('HORN')
# s.set(smtlib2_log="filename.smt2")
s.set(proof=True)

state = Function('state', [MappingSort, UintSort, UintSort, UintSort, BoolSort()])

wad, msg_value = Consts('wad msg_value', UintSort)
src, dst, msg_sender = Consts('src dst msg_sender', AddressSort)

balanceOf = Const('balanceOf', MappingSort)
weth_balance = Const('weth_balance', UintSort)
eth_supply = Const('eth_supply', UintSort) # all of the circulating native eth in the world
sum_balanceOf = Const('SYNTH_SUM_balanceOf', UintSort) # synthetic variable to track sum! whose correctness is guaranteed by the proving framework (basically, "no fuck ups in this script")

# initial state
s.add(state(
    K(AddressSort, Uint(0)), # balanceOf
    Uint(0), # weth_balance
    MAX_ETH, # eth_supply
    Uint(0), # sum_balanceOf
))

# transferFrom
_x = Store(balanceOf, src, balanceOf[src]-wad)
s.add(ForAll([balanceOf, weth_balance, eth_supply, sum_balanceOf, src, dst, wad], Implies(
    And(
        state(balanceOf, weth_balance, eth_supply, sum_balanceOf),
        UGE(balanceOf[src], wad),
    ),
    state(
        Store(_x, dst, _x[dst]+wad),
        weth_balance,
        eth_supply,
        sum_balanceOf + wad - wad
    )
)))

# deposit
s.add(ForAll([balanceOf, weth_balance, eth_supply, sum_balanceOf, msg_sender, msg_value], Implies(
    And(
        state(balanceOf, weth_balance, eth_supply, sum_balanceOf),
        ULE(msg_value, eth_supply),
        ULE(balanceOf[msg_sender], sum_balanceOf) # necessary since Z3 doesnt understand array sums
    ),
    state(
        Store(balanceOf, msg_sender, balanceOf[msg_sender] + msg_value),
        weth_balance + msg_value,
        eth_supply - msg_value,
        sum_balanceOf + msg_value,
    )
)))

# withdraw
s.add(ForAll([balanceOf, weth_balance, eth_supply, sum_balanceOf, msg_sender, wad], Implies(
    And(
        state(balanceOf, weth_balance, eth_supply, sum_balanceOf),
        UGE(balanceOf[msg_sender], wad),
        UGE(weth_balance, wad),
        ULE(balanceOf[msg_sender], sum_balanceOf) # necessary since Z3 doesnt understand array sums
    ),
    state(
        Store(balanceOf, msg_sender, balanceOf[msg_sender] - wad),
        weth_balance - wad,
        eth_supply + wad,
        sum_balanceOf - wad,
    )
)))

# force send native eth via selfdestruct or coinbase
s.add(ForAll([balanceOf, weth_balance, eth_supply, sum_balanceOf, msg_value], Implies(
    And(
        state(balanceOf, weth_balance, eth_supply, sum_balanceOf),
        ULE(msg_value, eth_supply),
    ),
    state(
        balanceOf,
        weth_balance + msg_value,
        eth_supply - msg_value,
        sum_balanceOf,
    )
)))

# Lemma. For all msg_sender, balanceOf[msg_sender] < MAX_ETH
# Very important lemma. Avoids stupid brute force solutions by Z3
s.add(ForAll([balanceOf, weth_balance, eth_supply, sum_balanceOf, msg_sender], Implies(
    And(
        state(balanceOf, weth_balance, eth_supply, sum_balanceOf),
        ULE(balanceOf[msg_sender], sum_balanceOf), # necessary since Z3 doesnt understand array sums
    ),
    And(
        ULE(sum_balanceOf, MAX_ETH),
        ULE(balanceOf[msg_sender], MAX_ETH),
    )
)))

# Lemma. weth_balance + eth_supply == MAX_ETH, and no funny business with overflow
s.add(ForAll([balanceOf, weth_balance, eth_supply, sum_balanceOf], Implies(
    state(balanceOf, weth_balance, eth_supply, sum_balanceOf),
    And(
        ULE(weth_balance, MAX_ETH),
        ULE(eth_supply, MAX_ETH),
        BVAddNoOverflow(weth_balance, eth_supply, False),
        weth_balance + eth_supply == MAX_ETH,
    )
)))

# Lemma. No funny business surrounding overflow / underflow with sum-balance and weth_balance.
s.add(ForAll([balanceOf, weth_balance, eth_supply, sum_balanceOf], Implies(
    state(balanceOf, weth_balance, eth_supply, sum_balanceOf),
    And(
        ULE(weth_balance - sum_balanceOf, MAX_ETH),
        ULE(sum_balanceOf, MAX_ETH),
        weth_balance == sum_balanceOf + weth_balance - sum_balanceOf,
        BVAddNoOverflow(sum_balanceOf, weth_balance - sum_balanceOf, False),
        BVSubNoUnderflow(weth_balance, sum_balanceOf, False),
    )
)))

# Theorem. sum_balanceOf <= weth_balance (Accounting is correct)
s.add(ForAll([balanceOf, weth_balance, eth_supply, sum_balanceOf], Implies(
    state(balanceOf, weth_balance, eth_supply, sum_balanceOf),
    # sum_balanceOf == weth_balance
    ULE(sum_balanceOf, weth_balance)
)))

r = s.check()
print(r)
if r == sat:
    print(s.model())
if r == unsat:
    print(s.proof())
if r == unknown:
    print(s.reason_unknown())
