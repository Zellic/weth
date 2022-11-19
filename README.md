# Formal verification of Wrapped ETH (WETH)

*Proving the safety of the Wrapped ETH smart contract, using the Z3 Theorem Prover*

## Abstract

Wrapped ETH, or WETH, is one of Ethereum’s most popular smart contracts. While WETH serves a simple purpose, a significant portion of all Ethereum transactions depend on it. WETH now underpins large parts of DeFi. In this blog post, we prove critical safety guarantees and invariants within the WETH contract. We do so by leveraging Z3, a battle-tested SMT solver.

We prove two critical invariants: (1) correctness of accounting, and (2) solvency. For accounting, we prove that the total supply of WETH is always equal to its balance of native Ether. For solvency, we prove that, regardless of other users’ actions, a user is always able to unstake Wrapped ETH. In the process, we also identified a minor, harmless bug in the contract. Our work enables the community to continue using WETH with increased confidence in its correctness.

**[Read the full blog post here.](https://www.zellic.io/blog/formal-verification-weth)**

## Contents of this repository

* horn.py: proof for invariant 1 (totalSupply never below total WETH issued)
* bmc.py: proof for invariant 2 (solvency)

## License

See LICENSE.
