# Summaries of the [EvmYul](https://github.com/nethermindEth/EVMYulLean/) model

This folder contains _summaries_ of the EVM opcodes in the EvmYul model.

In this context, a summary is the effects on the state of executing a single opcode. The full effects of executing an opcode can involve different functions.

For instance, the `EVM.step` function doesn't perform full gas computation, but does account for modifications of the `output` part of the state.
Menawhile, the `EVM.X` function does perform full gas computation, but the `output` part of the state is always `empty`.
