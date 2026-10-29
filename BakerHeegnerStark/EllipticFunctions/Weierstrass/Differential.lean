/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BakerHeegnerStark.EllipticFunctions.Weierstrass.Surjectivity
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Tactic.LinearCombination

/-!
# The second derivative of the actual Weierstrass function

Differentiating the cubic equation gives the second-order equation after
multiplication by `℘'`. Analytic continuation on the connected lattice
complement removes that factor, including at its zeros. The alternative that
`℘'` vanishes identically is excluded by the actual off-lattice surjectivity
of `℘`, not by any uniformization or addition formula.

No equation is asserted at the totalized values at lattice poles.
-/

open Filter
open scoped Topology

namespace PeriodPair

/-- The actual second-order Weierstrass equation away from the period lattice,
including at the zeros of the first derivative. -/
theorem deriv_derivWeierstrassP (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
  have hconn : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).isPreconnected
  have hprod : ∀ w ∈ (L.lattice : Set ℂ)ᶜ,
      L.derivWeierstrassP w *
        (deriv L.derivWeierstrassP w - (6 * L.weierstrassP w ^ 2 - L.g₂ / 2)) = 0 := by
    intro w hw
    have hwp : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
      simpa only [L.deriv_weierstrassP] using
        (L.analyticOnNhd_weierstrassP w hw).differentiableAt.hasDerivAt
    have hdwp := (L.analyticOnNhd_derivWeierstrassP w hw).differentiableAt.hasDerivAt
    have heq : (fun t => L.derivWeierstrassP t ^ 2) =ᶠ[𝓝 w]
        (fun t => 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃) := by
      filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hw] with t ht
      exact L.derivWeierstrassP_sq t ht
    have hleft : HasDerivAt (fun t => L.derivWeierstrassP t ^ 2)
        (2 * L.derivWeierstrassP w * deriv L.derivWeierstrassP w) w := by
      convert hdwp.pow 2 using 1
      simp
    have hright : HasDerivAt
        (fun t => 4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃)
        ((12 * L.weierstrassP w ^ 2 - L.g₂) * L.derivWeierstrassP w) w := by
      convert ((hwp.pow 3).const_mul 4).sub (hwp.const_mul L.g₂) |>.sub_const L.g₃ using 1
      ring
    have hde := hleft.unique (hright.congr_of_eventuallyEq heq)
    linear_combination hde / 2
  have hnonzero : ¬ (∀ w ∈ (L.lattice : Set ℂ)ᶜ, L.derivWeierstrassP w = 0) := by
    intro hzero
    obtain ⟨x, hx, hx0⟩ := L.exists_not_mem_lattice_weierstrassP_eq 0
    obtain ⟨y, hy, hy1⟩ := L.exists_not_mem_lattice_weierstrassP_eq 1
    have hconst := L.isClosed_lattice.isOpen_compl.is_const_of_deriv_eq_zero hconn
      L.differentiableOn_weierstrassP
      (by intro w hw; change deriv L.weierstrassP w = 0
          simpa only [L.deriv_weierstrassP] using hzero w hw) hx hy
    simp [hx0, hy1] at hconst
  have hanalytic : AnalyticOnNhd ℂ
      (fun w => deriv L.derivWeierstrassP w -
        (6 * L.weierstrassP w ^ 2 - L.g₂ / 2)) (L.lattice : Set ℂ)ᶜ := by
    intro w hw
    exact (L.analyticOnNhd_derivWeierstrassP.deriv w hw).sub
      ((analyticAt_const.mul ((L.analyticOnNhd_weierstrassP w hw).pow 2)).sub analyticAt_const)
  rcases L.analyticOnNhd_derivWeierstrassP.eq_zero_or_eq_zero_of_mul_eq_zero
      hanalytic hprod hconn with hzero | hzero
  · exact False.elim (hnonzero hzero)
  · exact sub_eq_zero.mp (hzero z hz)

end PeriodPair
