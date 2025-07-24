EVM Equivalence
---------------

✨ WIP ✨

This repository contains the proof of equivalence between two mathematical models of the EVM.
The mathematical models are Nethermind's [EvmYul](https://github.com/nethermindEth/EVMYulLean/) and Runtime Verification's [KEVM](https://github.com/runtimeverification/evm-semantics).

## Overall Description

Notably, these two models are written in very different languages: `EvmYul` in [Lean 4](https://lean-lang.org/) and `KEVM` in [K](https://kframework.org/).
The first step to prove equivalence is to have a framework in which to compare what the models do, and then show the equivalence of it.

To this end, the K framework allows for the generation of Lean 4 code representing compiled K definitions. Hence, the methodology is to show in Lean 4 the equivalence between `EvmYul` and the generated Lean 4 code from the `KEVM` definitions.

## Repository Structure

Under [EvmEquivalence](./EvmEquivalence) we have the following structure:
* [KEVM2Lean](./EvmEquivalence/KEVM2Lean): K-generated Lean 4 code with modifications
* [Interfaces](./EvmEquivalence/Interfaces): Proving interfaces to interact with the K-generated Lean 4 code
* [Summaries](./EvmEquivalence/Summaries): Summaries of relevant functions from the `EvmYul` model
* [Equivalence](./EvmEquivalence/Equivalence): Proof of equivalence between the models in a per-opcode basis
* [Utils](./EvmEquivalence/Utils): Useful results for the proving
* [StateMap.lean](./EvmEquivalence/StateMap.lean): Function mapping `KEVM` states to `EvmYul` states

## Building the Project

After cloning this repository, from its root run:
1. `lake exe cache get` to download the project's dependencies
2. `lake build` to build the project

Note that the first time building the project it can take over 20 minutes to do so.

## Lean 4 Code Generation

These are instructions to generate the `KEVM` related Lean 4 code, which is done via the cli tool `klean`. Note that the current generated code has been modified to aid with the proofs, and such modifications will be reflected in due time on the code generation.

More context on the `klean` tool can be found in the [K repository](https://github.com/runtimeverification/k/tree/master/pyk/src/pyk/klean).

### Generation Instructions

1. Clone the [KEVM](https://github.com/runtimeverification/evm-semantics) repository and build it locally (instructions in the repo). The build artifact should be under `~/.cache/k-dist-$digest`
2. Clone [K](https://github.com/runtimeverification/k/tree/master) and go to the [`pyk` folder](https://github.com/runtimeverification/k/tree/master/pyk/src/pyk/klean)
3. In the `pyk` folder do `poetry install` (install the [poetry](https://python-poetry.org/docs/) tool if you don't have it in your system)
4. Once `poetry install` has finished, run the following command where `$path_to_kdist` is your custom path to the build of `KEVM`
   ```bash
   poetry run klean "$path_to_kdist/evm-semantics/llvm" kevm2lean --rule 'EVM-OPTIMIZATIONS.optimized.add' --output $your_desired_output_folder
   ```

That should generate all the necessary Lean 4 code to faithfully represent the rule described in `--rule`. In this case, the rule `EVM-OPTIMIZATIONS.optimized.add` is the summary of running the `ADD` opcode in `KEVM`. Such rule can be found [here](https://github.com/runtimeverification/evm-semantics/blob/master/kevm-pyk/src/kevm_pyk/kproj/evm-semantics/optimizations.md).

#### KEVM Version

The KEVM version used for the current proofs is based on commit [https://github.com/runtimeverification/evm-semantics/tree/5dd05ea7936c13f4029389bafd25785ed9ff0a55](5dd05ea7936c13f4029389bafd25785ed9ff0a55).

#### Troubleshooting

If the `poetry install` seems to take too long or to hang, try `export PYTHON_KEYRING_BACKEND=keyring.backends.fail.Keyring` and `poetry install` again.

## Documentation and Blueprint

For an in-depth description of the project you can consult the README files present in this repository and the [blueprint](https://runtimeverification.github.io/evm-equivalence/).
