/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Product integral over a unit-time window

## Internal proof declarations

- `ProbabilityTheory.integral_timeWindow_prod_mark` factors the integral of
  a mark-only function over a measurable time window into the time mass and
  the mark integral.

This unit-interval specialization is used by the Poisson characteristic-function
proofs. Mathlib supplies its product-restriction and Fubini steps through
`Measure.prod_restrict`, `integral_prod`, and `setIntegral_const`; the result
remains an internal helper in the Poisson intensity proof-support hierarchy.
-/

section

namespace ProbabilityTheory

open MeasureTheory

/-- The intensity integral of a mark-only function over a measurable
unit-time window is its time mass times the mark integral. -/
lemma integral_timeWindow_prod_mark
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure ℝ) [SigmaFinite ν]
    (S : Set unitInterval)
    (f : ℝ → E) (hf : Integrable f ν) :
    (∫ z in S ×ˢ Set.univ, f z.2
      ∂((volume : Measure unitInterval).prod ν)) =
      ((volume : Measure unitInterval) S).toReal • (∫ x, f x ∂ν) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ,
    integral_prod _ (hf.comp_snd ((volume : Measure unitInterval).restrict S))]
  simp [Measure.real]

end ProbabilityTheory
