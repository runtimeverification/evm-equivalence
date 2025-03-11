# Interfaces for the [EvmYul](https://github.com/nethermindEth/EVMYulLean/) and [KEVM](https://github.com/runtimeverification/evm-semantics) models

This folder contains interfaces to reason with the EvmYul and KEVM models.

## File description

- [`EvmYulInterface`](./EvmYulInterface.lean): Interface for the EvmYul model
- [`FuncInterface`](./FuncInterface.lean): Interface for dealing with generated KEVM functions
- [`GasInterface`](./GasInterface.lean): Interface for the `«_<_>_SCHEDULE_Int_ScheduleConst_Schedule»` function
- [`Tactics`](./Tactics.lean): Tactics to help with the [`GasInterface.lean`](./GasInterface.lean) proofs
