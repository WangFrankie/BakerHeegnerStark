# Mathematical development

This repository develops the Baker-Heegner-Stark theorem over the pinned
QuadraticNumberFields dependency.

- Name declarations and files for their mathematical content. Use names such
  as `IntegralPoint`, `ClassPolynomial`, or `WeberIdentity`, rather than
  `Input`, `Provider`, or `Framework`.
- Reuse proved quadratic-field, class-group, reduced-form, and modular-function
  results through narrow imports. Do not edit dependency sources under `.lake`.
- The complete classification is still unproved. Do not introduce `sorry`,
  extra axioms, or assumptions that conceal the classification in a finite table.
  Distinguish proved theorems, reductions, and remaining mathematical statements.
- Preserve independent proof history and attribution when replacing or moving work.
- After changing Lean sources, run `lake build`,
  `lake lint -- --no-build BakerHeegnerStark`, and
  `lake env lean scripts/check_axioms.lean`. Commit the dependency manifest.
