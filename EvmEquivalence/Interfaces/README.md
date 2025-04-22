# Interfaces for the [EvmYul](https://github.com/nethermindEth/EVMYulLean/) and [KEVM](https://github.com/runtimeverification/evm-semantics) models

This folder contains interfaces to reason with the EvmYul and KEVM models.

## File description

- [`EvmYulInterface`](./EvmYulInterface.lean): Interface for the EvmYul model
- [`FuncInterface`](./FuncInterface.lean): Interface for dealing with generated KEVM functions
- [`GasInterface`](./GasInterface.lean): Interface for the `«_<_>_SCHEDULE_Int_ScheduleConst_Schedule»` and `«_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule»` functions
- [`Tactics`](./Tactics.lean): Tactics to help with the [`GasInterface.lean`](./GasInterface.lean) proofs
- [`Axioms`](./Axioms.lean): Axiomatization of the state mapping

## Axiomatic mapping

The file [`Axioms.lean`](./Axioms.lean) declares the exsistence of functions that convert `KEVM` maps into `EvmYul` ones.

The reason for this axiomatization is twofold.

1. Unimplemented maps in the K Lean 4 backend:
   K maps are currently undefined in the Lean 4 generated code. We still have to come up with a suitable-enough implementation of K
   maps that preserve the original semantics.

   Note that this is tricky given that K maps have to be defined inside of a `mutual` inductive block, which limits the options
   available to prevent crashing with Lean's positivity checker.
   A clear disadvantage of this is that we cannot (apparently) use `FinMap` as our map implementation.
2. Non reasoning-friendly maps in the `EvmYul` model:
   Currently, the `EvmYul` model is more geared towards execution than reasoning.
   This means that the map representation is not the most optimal for reasoning, and a more reasoning-friendly interface could be
   provided in the future. This is an argument in favor of not commiting (yet) to a K map representation tailored to play well with
   the current `EvmYul` maps, but this argument could change in the future.

## Axioms as pre-theorems

Given that we're axiomatizing part of the state translation, properties on the axiomatic parts need to be provided.
How the axiomatic parts of the state mapping are _needed_ to behave is laid out in the `Axioms` namespace at the end of the [`StateMap.lean`](../StateMap.lean) file.

These axioms establish the correspondence between the mapped data and the functions in the `EvmYul` map implementation.
Once we have a clear implementation of K maps in Lean, all these axioms should become theorems.
