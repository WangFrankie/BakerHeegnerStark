/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.Basic

/-!
# Local Uniqueness for an Analytic Second-Order Equation

An analytic solution of `f'' = A * f` with zero value and first derivative at the
origin vanishes on a neighborhood. A nonzero germ would have finite vanishing
order: differentiating lowers that order, whereas multiplying by an analytic
coefficient cannot lower it.
-/

namespace BakerHeegnerStark

open Filter
open scoped Topology

/-- The analytic equation `f'' = A * f` has only the zero germ with zero initial
value and first derivative. No nonvanishing assumption on `A` is needed. -/
theorem analytic_eventuallyEq_zero_of_deriv_deriv_eq_mul
    (f A : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hA : AnalyticAt ℂ A 0)
    (hf0 : f 0 = 0) (hdf0 : deriv f 0 = 0)
    (hde : ∀ᶠ z in 𝓝 (0 : ℂ), deriv (deriv f) z = A z * f z) :
    f =ᶠ[𝓝 (0 : ℂ)] 0 := by
  apply analyticOrderAt_eq_top.mp
  by_contra hfinite
  have hfirst : analyticOrderAt (deriv f) 0 + 1 = analyticOrderAt f 0 := by
    simpa only [hf0, sub_zero] using hf.analyticOrderAt_deriv_add_one
  have hsecond : analyticOrderAt (deriv (deriv f)) 0 + 1 =
      analyticOrderAt (deriv f) 0 := by
    simpa only [hdf0, sub_zero] using hf.deriv.analyticOrderAt_deriv_add_one
  have hproduct : analyticOrderAt (deriv (deriv f)) 0 =
      analyticOrderAt A 0 + analyticOrderAt f 0 := by
    exact (analyticOrderAt_congr hde).trans (analyticOrderAt_smul hA hf)
  have hle : analyticOrderAt f 0 ≤ analyticOrderAt (deriv f) 0 := by
    calc
      analyticOrderAt f 0 ≤ analyticOrderAt (deriv (deriv f)) 0 := by
        rw [hproduct]
        exact le_add_self
      _ ≤ analyticOrderAt (deriv f) 0 := by
        rw [← hsecond]
        exact le_self_add
  have hdfinite : analyticOrderAt (deriv f) 0 ≠ ⊤ := by
    intro htop
    exact hfinite (by simpa [htop] using hfirst.symm)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hdfinite
  have hlt : analyticOrderAt (deriv f) 0 < analyticOrderAt f 0 := by
    rw [← hfirst, ← hn]
    exact ENat.natCast_lt_succ
  exact (not_lt_of_ge hle) hlt

end BakerHeegnerStark
