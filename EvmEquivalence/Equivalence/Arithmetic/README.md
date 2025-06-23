# Arithmetic Opcodes


This folder contains the equivalence proofs for all arithmetic Opcodes.
The proofs are divided into three files, according to the shape of the KEVM generated summary.

### Summary structure

The generated KEVM summaries can be divided into three shapes, depending on the number of operations the arithmetic opcode takes.
This is relevant because each operation results in an additional precondition for the generated summary. Let's see what this means.

#### [**One operation**](./OneOpEquivalence.lean)

Opcodes covered: `DIV`, `SDIV`, `MOD`, `SMOD`, `SIGNEXTEND`.

The general precondition that appears in the summary of these opcodes follows this structure (showcasing the `DIV` precondition):

```lean
(defn_Val3 : «_/Word__EVM-TYPES_Int_Int_Int» W0 W1 = some _Val3)
```

#### [**Two operations**](./TwoOpEquivalence.lean)

Opcodes covered: `ADD`, `SUB`, `ADDMOD`, `MULMOD`.

TODO: `MUL` summary is currently missing.

In this cases we need two preconditions to fully compute the opcodes.
The general structure of these is as follows (showcasing the `ADD` opcode):

```lean
(defn_Val3 : «_+Int_» W0 W1 = some _Val3)
(defn_Val4 : chop _Val3 = some _Val4)
```

Note that these opcodes requrie a diferent prestate stack structure,
but it's easier to accomodate for that than for different preconditions.

#### [**`EXP` opcode**](./ExpEquivalence.lean)

Opcodes covered: `EXP`.

The `EXP` opcode is a special case in that it has two different summaries to cover all its behavior.
It has one summary when the exponent is greater than zero (summarized in `Rewrites.EXP_SUMMARY_EXP_SUMMARY_USEGAS`)
and one when the exponent is zero (`Rewrites.EXP_SUMMARY_EXP_SUMMARY_USEGAS_LE0`).

Note that in this summary there's the implicit assumption that the exponent is greater or equal than zero.

Here, instead of reasoning about different opcodes with the same precondition structure,
we're reasoning about two different summaries for the same opcode with different precondition structures.

Dividing the cases when the exponent is zero (`eq0`) or greater (`gt0`), we have three different kinds of hypotheses:

1. Hypotheses that apply to both summaries (e.g., `defn_Val1`)
2. Hypotheses that change depending on the summary (e.g., `defn_Val0`)
3. Hypotheses that only apply to the case `gt0` and are irrelevant for `eq0`
  (e.g., `defn_Val2` through `defn_Val7`)
