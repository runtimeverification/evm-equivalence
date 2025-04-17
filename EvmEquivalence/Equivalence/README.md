# Opcode Equivalence

This folder contains the equivalence proofs for opcode execution between the [`EvmYul`](https://github.com/nethermindEth/EVMYulLean/)
and [`KEVM`](https://github.com/runtimeverification/evm-semantics) models.

The proofs follow the following structure.

## Proof sketch

K rewrite rules are encoded as constructors of the inductive type `Rewrites` found in [Rewrite.lean](../KEVM2Lean/Rewrite.lean).
That is, each constructor of `Rewrites` is a K rewrite rule. In particular, these K rewrite rules are generated from the [`KEVM` summaries](https://github.com/runtimeverification/evm-semantics/tree/master/kevm-pyk/src/kevm_pyk/kproj/evm-semantics/summaries).
So the rewrite rules in `Rewrites` already encapsulate the computational content of executing an opcode in `KEVM`.

Given this, let's understand the anatomy of a Lean-generated rewrite rule.

### Anatomy of a rewrite rule

Rewrite rules are comprised of
- A left-hand side (lhs): a `KEVM` state prior to the execution of an opcode. Also known as prestate.
- A right-hand side (rhs): a `KEVM` state derived from the execution of an opcode on the lhs. Also known as prestate.
- All the variables involved in the definition of the lhs and rhs.
- All the conditions that give meaning to the variables present in the lhs and rhs.

Structurally we only need the first three items to make a rewrite rule type-check.
The actual meaning of rewrite rules is encoded in all these conditions named `defn_Val*`.

The structure of Lean-generated rewrite rules is as follows:
```Lean
inductive Rewrites : SortGeneratedTopCell → SortGeneratedTopCell → Prop where
| NAME_OF_THE_RULE
  {Var : CustomType} -- Variables are declared as implicit
  ...                 -- A bunch more of variables
  (defn_Valn : f other_variables = some Valn) -- The meaning of the `_Valn` is explicitly given
  ...                 -- A bunch more of conditions
  : Rewrites LHS RHS  -- Given all the conditions (`defn_Val*`) above we can state LHS => RHS
```

Here `LHS` and `RHS` are representations of the `KEVM` pre and post states with the appropriate structure given the `defn_Val*` conditions.

### Proper definition of pre and post states

The first step in all proofs is to have a precise definition of `LHS` and `RHS`.
The naming convention is `opcode?HS` for each (e.g. `addLHS` for the prestate of the `ADD` opcode).

Note that for these definitions we don't need any of the `defn_Val*` conditions yet, since we only care about the structural content of both states.

#### Theorems-as-tests

Once we have a definition of the `LHS` and `RHS` we can test it with a theorem stating that, indeed, given all the `defn_Val*` preconditions,
`Rewrites opcodeLHS opcodeRHS` holds.

The general name for that theorem is `rw_opcodeLHS_opcodeRHS`.

### Projecting `KEVM` states into `EvmYul`

The next step is to reflect the resulting `EvmYul` state after transforming the `LHS` and `RHS` via the `stateMap` function.
The `stateMap` function is defined in [`StateMap.lean`](../StateMap.lean).

This reflection is done through the `opcode_prestate_equiv` and `opcode_poststate_equiv` theorems for the `opcodeLHS` and `opcodeRHS` respectively.
These theorems are mostly structural, especially the `opcodeLHS`. However, the `opcode_poststate_equiv` is used to specify further what are the recorded effects of executing `opcode` in `KEVM`.

To exemplify what this means, consider `add_poststate_equiv` in [`AddEquivalence.lean`](./AddEquivalence.lean).

We have that the structural translation of the `PC_CELL` of `addRHS` into an ``EvmYul` state is `pc := intMap _Val5`.
That is, mapping the value of `_Val5` into a `UInt256`.
However, as per `(defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)` and the definition of `«_+Int_»` found in [`FuncInterface.lean`](../Interfaces/FuncInterface.lean),
we know that the value of `_Val5` is `PC_CELL + 1`.

Hence, we will state `pc := intMap («_+Int'_» PC_CELL 1)` instead of `pc := intMap _Val5`. For more details on `«_+Int_»`, `«_+Int'_»` or more functions visit [`FuncInterface.lean`](../Interfaces/FuncInterface.lean).

### Final proofs

The `EvmYul` functions that reflect the semantics of executing an opcode are `EVM.step` and `X` found in [`EvmYul/EVM/Semantics.lean`](https://github.com/NethermindEth/EVMYulLean/blob/main/EvmYul/EVM/Semantics.lean).
Since the effects of opcode execution are separated between the two functions (for instance, `step` doesn't assign gas costs), we have
one theorem for each function stating broadly the same.

The statement is, for `f` being `EVM.step` or `X`
> Given the `KEVM` prestate `LHS`, `f (stateMap LHS) = stateMap RHS`
That is, mapping the `KEVM` prestate to `EvmYul` and executing either `EVM.step` or `X` gives us the mapped `KEVM` poststate.

An number of additional hypothesis from the `defn_Val*` is added to each theorem. Revisiting and sanity-checking these hypothesis is worthwhile.
The vast majority of them stem from the fact that [`KEVM` summaries](https://github.com/runtimeverification/evm-semantics/tree/master/kevm-pyk/src/kevm_pyk/kproj/evm-semantics/summaries)
assume that the `LHS` is a valid `KEVM` state. This means that conditions such as `PC_CELL < 2^256` are not enforced by the summaries and
therefore need to be added as assumptions to obtain equivalence.

These assumptions are present in the `KEVM` semantics, but they are enforced before triggering opcode execution.

### Future work

Notably, these proofs are only in one direction. Namely, we show that if `KEVM` computes something, `EvmYul` agrees with a
translation of that computation. It remains to prove the converse. Namely, that `KEVM` agrees with a translation of what `EvmYul` computes.
