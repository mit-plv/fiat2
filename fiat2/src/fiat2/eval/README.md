# Evaluation examples

Programs drawn from real code bases, written in Conquord, used as the subjects of the
paper's evaluation.

These are **not** the development's test files. The `Ex_*.v` files one directory up
exercise individual rewrite rules and are regression tests; citing them as evidence of
pattern coverage would be circular, since they were written to make the rules fire.
Files here are translations of code someone else wrote for their own reasons.

The build needs no configuration for this directory: `fiat2/Makefile` collects sources
with a recursive `find`, and `-Q src/fiat2 fiat2` is recursive, so a file here is
`fiat2.eval.<Name>` and compiles with the rest.

## File convention

Every file opens with a header comment giving, in this order:

1. **Source** — repository, path, and the commit the reading is from, so the
   translation can be checked against the original.
2. **Pattern** — the pattern IDs from `fiat2-paper/pattern-study` that the original
   instantiates. These say why the example was chosen; the study's counts are a
   discovery aid and never appear in the paper.
3. **Claim** — which evaluation claim the example evidences (see the evaluation log).
4. **Faithfulness** — what was dropped in translation and why, stated plainly. The
   original is Java or Python; an honest note here is what makes the example usable.
5. **Expected** — what the optimizer should produce, in words.

The expectation in (5) is then pinned by a lemma, in the style of `Ex_Range.v`: a small
projection out of the optimized program closed by `vm_compute; reflexivity`, rather than
an `exists` against the whole term, which does not terminate in reasonable time.
