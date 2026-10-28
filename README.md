# BakerHeegnerStark

An independent Lean formalization of the **Baker-Heegner-Stark theorem**:
for a negative squarefree integer `d`,

```text
classNumber (ℚ(√d)) = 1 ↔ d ∈ {-1, -2, -3, -7, -11, -19, -43, -67, -163}.
```

The full theorem is not yet proved. Its exact statement is the proposition
`BakerHeegnerStark.ClassNumberOneClassification`.

## Dependency and provenance

The project depends on
[QuadraticNumberFields](https://github.com/WangFrankie/QuadraticNumberFields)
at the immutable commit
[`196dd48b3439cc731397fd2cf9b8ac48da211a22`](https://github.com/WangFrankie/QuadraticNumberFields/commit/196dd48b3439cc731397fd2cf9b8ac48da211a22),
preserved on `legacy/baker-heegner-stark`. This retains the original source,
proof history, authorship, and Apache 2.0 license of the earlier development.
Lean and mathlib are pinned to `v4.35.0`; transitive revisions are recorded in
`lake-manifest.json`.

The dependency supplies the quadratic fields and their class groups, the genus
sieve, the nine individual class-number-one results, the integral points on
Heegner's curve, and the proved Weber and modular-polynomial identities.
This repository develops the remaining proof through narrow imports of those
results.

## Current mathematical results

- `mem_heegnerSet_or_inert_prime`: class number one either gives a known
  Heegner number or a prime parameter `d = -p`, `p ≡ 3 (mod 8)`, `p ≠ 3`.
- `classNumberOneClassification_iff_inertPrimeClassification`: the full
  classification is equivalent to the remaining non-exceptional inert prime
  case. This is a proved reduction, not a proof of either classification.

The reduction uses the proved genus sieve and the ideal-theoretic split-at-two
argument. The conditional Weber classification from the historical development
is not an assumption of these results.

## Next mathematical steps

1. Prove positivity on the imaginary axis and the identities
   `𝔣⁸ = 𝔣₁⁸ + 𝔣₂⁸` and
   `γ₂ = (𝔣²⁴ - 16)/𝔣⁸ = (𝔣₁²⁴ + 16)/𝔣₁⁸ = (𝔣₂²⁴ + 16)/𝔣₂⁸`.
2. Relate reduced forms and quadratic-order ideal classes to CM points and
   the roots of the level-two modular polynomial.
3. Prove the needed integrality, rationality, and degree statements for CM
   values and Weber class invariants.
4. Derive Heegner's integral point and the prime classification from those
   values. The finite gamma-prime table must be a consequence of the argument.

## Build and verify

```bash
lake exe cache get
lake build
lake lint -- --no-build BakerHeegnerStark
lake env lean scripts/check_axioms.lean
```

`lake build` resolves the pinned dependencies when needed. The cache command
retrieves mathlib's compiled artifacts; QuadraticNumberFields is built from its
pinned source. The axiom audit permits only `propext`, `Classical.choice`, and
`Quot.sound` for the listed proved results.

## Files

- `BakerHeegnerStark/Statement.lean`: the unconditional classification statement.
- `BakerHeegnerStark/InertPrimes.lean`: the proved elementary reduction.
- `BakerHeegnerStark.lean`: public entry point and selected proved prerequisites.
- `scripts/check_axioms.lean`: axiom audit of the reduction and reused results.

Licensed under Apache 2.0; see [LICENSE](LICENSE).
