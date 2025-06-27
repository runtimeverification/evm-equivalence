Helper Scripts
--------------

This folder contains scripts that help with the modification or usage of the K-generated Lean code.

## `format-rewrites.py`

The [`format-rewrites.py`](./format-rewrites.py) script takes a K-generated inductive `Rewrites` rule and pretty prints it.
K-generated rewrites rules are constructors of the inductive `Rewrites` type, and are generated as one-liners.
This makes reading more challenging, but after using this script on the generated `Rewrites` one can read the rules with ease.

To pretty print the generated `Rewrites` type run the following (assuming `Rewrites` lives in [`EvmEquivalence/KEVM2Lean/Rewrite.lean`](../EvmEquivalence/KEVM2Lean/Rewrite.lean)
and you're running it from [`EvmEquivalence`](../EvmEquivalence/))

```bash
cat KEVM2Lean/Rewrite.lean | python3 ../scripts/format-rewrites.py > tmp.lean & mv tmp.lean KEVM2Lean/Rewrite.lean
```

## `get-arguments.py`

The `opcode?HS` definitions described in the [Equivalence Proof Sketch](../EvmEquivalence/Equivalence/README.md) sometimes require a lot of arguments to be stated in theorems.

The [`get-arguments.py`](./get-arguments.py) script inlines the names of the implicit arguments provided and strips away the types and any surrounding curly brackets and colons.

As a usage example, assuming we're in [`EvmEquivalence`](../EvmEquivalence/), we provide the arguments in a file `args` comprised of the following arguments
```lean
  {foo0 foo1 : SortFoo}
  {bar0 bar1 : SortBar}
```
and run the following command
```bash
python3 get-arguments.py args | cat > out-args
```
which will make have the file `out-args` the following contents
```lean
foo0 foo1 bar0 bar1
```

We can then copy-paste the resulting line of arguments to our invocation of `opcode?HS`, which only contains implicit arguments.
