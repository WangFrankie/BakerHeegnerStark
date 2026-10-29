/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.Algebra.Polynomial.JointOrbit
import BakerHeegnerStark.Algebra.Polynomial.Separating
import BakerHeegnerStark.Analysis.DifferentialEquation
import BakerHeegnerStark.ClassNumberOne.ConductorTwoClassPolynomial
import BakerHeegnerStark.ClassNumberOne.Heegner.IntegralPoints
import BakerHeegnerStark.ClassNumberOne.InertPrimes
import BakerHeegnerStark.ComplexMultiplication.CyclicNeighbors.Data
import BakerHeegnerStark.ComplexMultiplication.CyclicNeighbors.QExpansion
import BakerHeegnerStark.ComplexMultiplication.CyclicNeighbors.Separation
import BakerHeegnerStark.ComplexMultiplication.DivisionLattice
import BakerHeegnerStark.ComplexMultiplication.Galois
import BakerHeegnerStark.ComplexMultiplication.Gamma.Rationality
import BakerHeegnerStark.ComplexMultiplication.Gamma.Roots
import BakerHeegnerStark.ComplexMultiplication.Gamma.Values
import BakerHeegnerStark.ComplexMultiplication.Isogeny
import BakerHeegnerStark.ComplexMultiplication.JInvariant.Coordinates
import BakerHeegnerStark.ComplexMultiplication.JInvariant.Endomorphism
import BakerHeegnerStark.ComplexMultiplication.JInvariant.Separation
import BakerHeegnerStark.ComplexMultiplication.Orders.InertIdealClasses
import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.NormThree
import BakerHeegnerStark.ComplexMultiplication.QuadraticPoint.SmallNorms
import BakerHeegnerStark.ComplexMultiplication.Residues
import BakerHeegnerStark.ComplexMultiplication.SingularModuli.Conjugates
import BakerHeegnerStark.ComplexMultiplication.SingularModuli.DegreeBound
import BakerHeegnerStark.ComplexMultiplication.SingularModuli.Discriminant
import BakerHeegnerStark.ComplexMultiplication.Weber.Action
import BakerHeegnerStark.ComplexMultiplication.Weber.ClassInvariant
import BakerHeegnerStark.ComplexMultiplication.Weber.JointCM
import BakerHeegnerStark.ComplexMultiplication.Weber.JointOrbit
import BakerHeegnerStark.ComplexMultiplication.Weber.JointPolynomial
import BakerHeegnerStark.ComplexMultiplication.Weber.JointQExpansion
import BakerHeegnerStark.ComplexMultiplication.Weber.JointRationality
import BakerHeegnerStark.ComplexMultiplication.Weber.JointSpecialization
import BakerHeegnerStark.EllipticCurves.CyclicIsogeny.Basic
import BakerHeegnerStark.EllipticCurves.CyclicIsogeny.KernelAction
import BakerHeegnerStark.EllipticCurves.CyclicIsogeny.KernelModularity
import BakerHeegnerStark.EllipticCurves.JInvariant.Coordinates
import BakerHeegnerStark.EllipticCurves.JInvariant.Galois
import BakerHeegnerStark.EllipticCurves.JInvariant.Isogeny
import BakerHeegnerStark.EllipticCurves.JInvariant.Model
import BakerHeegnerStark.EllipticCurves.JInvariant.Normalization
import BakerHeegnerStark.EllipticCurves.JInvariant.Torsion
import BakerHeegnerStark.EllipticCurves.JInvariant.Uniformization
import BakerHeegnerStark.EllipticCurves.Torsion
import BakerHeegnerStark.EllipticCurves.Weierstrass.Galois
import BakerHeegnerStark.EllipticCurves.Weierstrass.PointChange
import BakerHeegnerStark.EllipticCurves.Weierstrass.Torsion
import BakerHeegnerStark.EllipticFunctions.PeriodTorus.Torsion
import BakerHeegnerStark.EllipticFunctions.PeriodTorus.TorsionMatrix
import BakerHeegnerStark.EllipticFunctions.Uniformization.Endomorphism
import BakerHeegnerStark.EllipticFunctions.Uniformization.Point
import BakerHeegnerStark.EllipticFunctions.Uniformization.Torsion
import BakerHeegnerStark.EllipticFunctions.Uniformization.TorsionMatrix
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Addition
import BakerHeegnerStark.EllipticFunctions.Weierstrass.AnalyticLift
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Differential
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Fibres
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Isogeny
import BakerHeegnerStark.EllipticFunctions.Weierstrass.IsogenyInvariants
import BakerHeegnerStark.EllipticFunctions.Weierstrass.IsogenyLocalParameter
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Parameter
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Surjectivity
import BakerHeegnerStark.EllipticFunctions.Weierstrass.Translation
import BakerHeegnerStark.EllipticFunctions.Weierstrass.TranslationAnalytic
import BakerHeegnerStark.EllipticFunctions.Weierstrass.TranslationDifferential
import BakerHeegnerStark.FieldTheory.AlgebraicOrbit
import BakerHeegnerStark.LinearAlgebra.Matrix.CyclicLines
import BakerHeegnerStark.LinearAlgebra.Matrix.QuadraticCentralizer
import BakerHeegnerStark.ModularForms.CyclicSublattice.Action
import BakerHeegnerStark.ModularForms.CyclicSublattice.Basic
import BakerHeegnerStark.ModularForms.Gamma.Basic
import BakerHeegnerStark.ModularForms.Gamma.CyclicModularity
import BakerHeegnerStark.ModularForms.Gamma.CyclicQExpansion
import BakerHeegnerStark.ModularForms.Gamma.Modularity
import BakerHeegnerStark.ModularForms.Gamma.PolynomialTwo
import BakerHeegnerStark.ModularForms.Gamma.Transformations
import BakerHeegnerStark.ModularForms.JInvariant.JointPolynomial
import BakerHeegnerStark.ModularForms.JInvariant.Polynomial
import BakerHeegnerStark.ModularForms.JInvariant.Surjectivity
import BakerHeegnerStark.ModularForms.ModularPolynomial.Coefficients
import BakerHeegnerStark.ModularForms.ModularPolynomial.Conjugates
import BakerHeegnerStark.ModularForms.ModularPolynomial.FixedPoints
import BakerHeegnerStark.ModularForms.ModularPolynomial.LevelTwo
import BakerHeegnerStark.ModularForms.ModularPolynomial.Modularity
import BakerHeegnerStark.ModularForms.ModularPolynomial.Monic
import BakerHeegnerStark.ModularForms.QExpansion.Cyclotomic
import BakerHeegnerStark.ModularForms.QExpansion.Integral
import BakerHeegnerStark.ModularForms.Weber.BranchPowerSeries
import BakerHeegnerStark.ModularForms.Weber.BranchQExpansion
import BakerHeegnerStark.ModularForms.Weber.BranchSpace
import BakerHeegnerStark.ModularForms.Weber.Branches
import BakerHeegnerStark.ModularForms.Weber.CoefficientConjugation
import BakerHeegnerStark.ModularForms.Weber.Cusp
import BakerHeegnerStark.ModularForms.Weber.Growth
import BakerHeegnerStark.ModularForms.Weber.Integrality
import BakerHeegnerStark.ModularForms.Weber.Modularity
import BakerHeegnerStark.ModularForms.Weber.PhaseField
import BakerHeegnerStark.ModularForms.Weber.QExpansion
import BakerHeegnerStark.ModularForms.Weber.ResidueBranches

/-!
# The Baker-Heegner-Stark Class-Number-One Theorem

`BakerHeegnerStark.classNumberOneClassification` proves the full classification
of negative squarefree parameters with imaginary quadratic class number one.
Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

This is the complete-library import. For the classification alone, use
`BakerHeegnerStark.ClassNumberOne.Classification`; for the statement alone,
use `BakerHeegnerStark.Statement`.

## Mathematical organization

The directories follow mathematical subjects, as in mathlib and
QuadraticNumberFields, rather than the order in which lemmas were developed.

* `Algebra/Polynomial`, `FieldTheory`, `LinearAlgebra/Matrix`, and `Analysis`
  contain separating and joint polynomials, algebraic-conjugate and fixed-field
  descent, quadratic matrix centralizers, and analytic differential uniqueness.
* `ModularForms` contains the analytic eta, Weber, gamma, and j theories,
  Hecke identities, full q-expansions, cyclic sublattices, and modular polynomials.
  A topic's initial development is `Basic.lean`; subsequent files are named for
  their mathematical content, such as `QExpansion.lean` and `Integrality.lean`.
* `EllipticFunctions` contains period lattices and tori, Weierstrass functions,
  and their actual additive uniformization of nonsingular curve points.
* `EllipticCurves` contains point-coordinate changes, torsion, the j-generated
  arithmetic model, its actual Galois action, and finite cyclic isogenies.
* `ComplexMultiplication` contains quadratic orders and their lattices,
  quadratic fixed-point and norm calculations, singular moduli, and the actual
  CM/Galois arguments for the gamma and Weber class invariants.
* `ClassNumberOne` contains the known cases, elementary ideal reductions,
  Heegner's integral points and algebra, prime identification, and classification.

Declaration names and namespaces are independent of these file paths and are
preserved. Quadratic-field and binary-quadratic-form infrastructure remains in
the pinned QuadraticNumberFields dependency; local reduced-form modules only
realize the CM values needed by the degree argument.

## Proof dependencies

The known cases and elementary reductions in `ClassNumberOne` leave the
nonexceptional inert prime case. `ComplexMultiplication/Orders` realizes the
quadratic orders and their proper ideal lattices, including the conductor-two
class group. Weierstrass uniqueness and actual j-separation connect their
complex realizations with distinct CM values.

The full modular polynomials and their integral coefficient descent are proved
in `ModularForms/ModularPolynomial`. The singular-modulus discriminant and
reduced-form arguments in `ComplexMultiplication/SingularModuli` give actual
integrality and the class-number degree bound. The conductor-two j-field is
cubic, proved using the irreducible Heegner cubic and its rational j-expression,
not by equating an unconnected form count with a field degree.

`ComplexMultiplication/Gamma/Rationality.lean` proves the normalized cube-root
class invariant using a rational twisted relation and its unique CM common
root. `ComplexMultiplication/Weber/JointRationality.lean` proves the complete
rational joint relation in j, the tuple variable, and the root variable.
`JointCM.lean` and `JointSpecialization.lean` match both actual conjugate values
at the same index, recover CM centralization from the three/eight cyclic
neighbours, and apply fixed-field and reality descent. No arbitrary field
automorphism is passed through an infinite complex sum.

`ComplexMultiplication/Weber/ClassInvariant.lean` supplies the actual Weber
input. `ClassNumberOne/Classification.lean` combines it with the cubic-field,
integral-point, and exponential-bound arguments to prove the classification.
No finite gamma-prime table or general Shimura reciprocity theorem is assumed.

## References and provenance

See D. A. Cox, *Primes of the form x² + ny²*, 2nd ed., §§11–12;
Weber, *Lehrbuch der Algebra* III; B. J. Birch, *Weber's class invariants* (1969);
and H. M. Stark (1969). Extracted modules retain their original attribution,
historical source paths, and immutable dependency revision.
-/
