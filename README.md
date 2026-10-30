# BakerHeegnerStark

An independent Lean formalization of the **Baker-Heegner-Stark theorem**:
for a negative squarefree integer `d`,

```text
classNumber (ℚ(√d)) = 1 ↔ d ∈ {-1, -2, -3, -7, -11, -19, -43, -67, -163}.
```

The theorem is proved unconditionally by
`BakerHeegnerStark.classNumberOneClassification` in
[`ClassNumberOne/Classification.lean`](BakerHeegnerStark/ClassNumberOne/Classification.lean).
The public proposition is
[`ClassNumberOneClassification`](BakerHeegnerStark/Statement.lean).
Its complete axiom dependency is `propext`, `Classical.choice`, and `Quot.sound`.
There is no admitted CM input.

## Build and verify

Lean and mathlib are pinned to `v4.35.0`. With Lean's `elan` toolchain manager
installed, run:

```bash
lake exe cache get
lake build
lake lint -- --no-build BakerHeegnerStark
lake env lean scripts/check_axioms.lean
git diff --check
```

The cache command retrieves mathlib's compiled artifacts; QuadraticNumberFields
is built from its pinned source. The
[axiom audit](scripts/check_axioms.lean) permits only the three standard axioms
listed above for all audited results, including the rational joint relation,
Weber class invariant, and final classification.

## Proof guide

Paths below are relative to [`BakerHeegnerStark/`](BakerHeegnerStark/).

| Topic | Entry points |
| --- | --- |
| Nine known cases and reduction to inert primes | [`ClassNumberOne/KnownCases.lean`](BakerHeegnerStark/ClassNumberOne/KnownCases.lean), [`InertPrimes.lean`](BakerHeegnerStark/ClassNumberOne/InertPrimes.lean) |
| Integral modular polynomials | [`ModularForms/ModularPolynomial/Diagonal.lean`](BakerHeegnerStark/ModularForms/ModularPolynomial/Diagonal.lean) |
| Singular-modulus integrality and class-number degree bound | [`ComplexMultiplication/SingularModuli/Basic.lean`](BakerHeegnerStark/ComplexMultiplication/SingularModuli/Basic.lean), [`DegreeBound.lean`](BakerHeegnerStark/ComplexMultiplication/SingularModuli/DegreeBound.lean) |
| Gamma rationality | [`ComplexMultiplication/Gamma/Rationality.lean`](BakerHeegnerStark/ComplexMultiplication/Gamma/Rationality.lean) |
| Weber class-invariant descent | [`ComplexMultiplication/Weber/JointRationality.lean`](BakerHeegnerStark/ComplexMultiplication/Weber/JointRationality.lean), [`JointSpecialization.lean`](BakerHeegnerStark/ComplexMultiplication/Weber/JointSpecialization.lean) |
| Heegner's algebra, integral points, and prime identification | [`ClassNumberOne/Heegner/`](BakerHeegnerStark/ClassNumberOne/Heegner/) |

The Weber descent uses a rational joint modular relation, cyclic-neighbour
Galois action, and CM torsion centralization. Heegner's argument then uses
integral points on `Y² = 2X(X³ + 1)` and exponential estimates to identify the
prime; no gamma-prime table is assumed.

The classification is complete. General Shimura reciprocity and a general
nonmaximal-order ideal/form/CM-field correspondence are outside its scope.

## Library layout

| Directory | Content |
| --- | --- |
| `Algebra/`, `FieldTheory/`, `LinearAlgebra/`, `Analysis/` | Polynomial, field, matrix, and analytic tools |
| `ModularForms/` | Eta, Weber, gamma, j, Hecke theory, q-expansions, and modular polynomials |
| `EllipticFunctions/` | Period lattices and tori, Weierstrass functions, and additive uniformization |
| `EllipticCurves/` | Point changes, torsion, Galois actions, and cyclic isogenies |
| `ComplexMultiplication/` | Orders, quadratic points, singular moduli, and arithmetic descent |
| `ClassNumberOne/` | Known cases, ideal reductions, Heegner's argument, and classification |

Prefer specific imports:

```lean
import BakerHeegnerStark.ClassNumberOne.Classification
import BakerHeegnerStark.ModularForms.Weber.Basic
import BakerHeegnerStark.ComplexMultiplication.Weber.ClassInvariant
```

`import BakerHeegnerStark` imports the complete library.

## Dependencies and provenance

[QuadraticNumberFields](https://github.com/WangFrankie/QuadraticNumberFields)
is pinned to
[`00b38b46915b6c5cc267e43343bb346949f5017c`](https://github.com/WangFrankie/QuadraticNumberFields/commit/00b38b46915b6c5cc267e43343bb346949f5017c).
It supplies quadratic fields, class groups, genus theory, binary quadratic
forms, and the square-root suborder inclusion, additive index, and conductor
in the half-integer order. BHS also reuses
`ClassGroup.exists_integral_invertible_ideal` over arbitrary commutative domains
and `Ideal.conductor_mul_mem_map` for arbitrary homomorphisms of commutative
rings, rather than duplicating their proofs locally. Complex realizations,
conductor-two ideal normalization, and CM applications remain in BHS.
Exact dependency revisions are recorded in `lake-manifest.json`.

The BHS application proofs and modular-function modules were extracted from
QNF commit
[`196dd48b3439cc731397fd2cf9b8ac48da211a22`](https://github.com/WangFrankie/QuadraticNumberFields/commit/196dd48b3439cc731397fd2cf9b8ac48da211a22),
preserved on `legacy/baker-heegner-stark`. They retain their original proofs,
authorship, copyright, and source references. The local analytic layer depends
only on mathlib and itself; the full classification also uses QNF arithmetic
and form theory.

Import the local analytic results through `BakerHeegnerStark.*`, not their
historical `QNFMathlib.NumberTheory.ModularForms.*` copies in the preserved
snapshot: mixing them causes duplicate declarations in the `ModularForm` namespace.

Licensed under Apache 2.0; see [LICENSE](LICENSE).
