/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Poisson small-jump path bound

A deterministic variation estimate for each realization of a Poisson random
measure.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The pointwise small-path bound for a Poisson jump measure follows from
one bound on its realized absolute-jump integral. -/
theorem poissonRandomMeasure_smallJumpPath_bound
    {Ω Time Mark : Type} [MeasurableSpace Ω]
    [Preorder Time] [MeasurableSpace Time] [MeasurableSpace Mark]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → Time × Mark}
    (ω : Ω) (A : Set (Time × Mark)) (f : Mark → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hV : (∫⁻ z in A, ENNReal.ofReal |f z.2|
      ∂(poissonRandomMeasure K X ω)) < ENNReal.ofReal ρ) :
    ∀ t : Time,
      |∫ z in {z | z ∈ A ∧ z.1 ≤ t}, f z.2
        ∂(poissonRandomMeasure K X ω)| ≤ ρ := by
  intro t
  let B : Set (Time × Mark) := {z | z ∈ A ∧ z.1 ≤ t}
  have hBA : B ⊆ A := fun _ hz => hz.1
  have hnorm := enorm_integral_le_lintegral_enorm
    (μ := (poissonRandomMeasure K X ω).restrict B) (fun z => f z.2)
  have hnorm' : ENNReal.ofReal
      |∫ z in B, f z.2 ∂(poissonRandomMeasure K X ω)| ≤
        ∫⁻ z in B, ENNReal.ofReal |f z.2|
          ∂(poissonRandomMeasure K X ω) := by
    simpa only [Real.enorm_eq_ofReal_abs] using hnorm
  have hmono := lintegral_mono_set (μ := poissonRandomMeasure K X ω)
    (f := fun z => ENNReal.ofReal |f z.2|) hBA
  have hstrict := hnorm'.trans hmono |>.trans_lt hV
  exact (ENNReal.ofReal_lt_ofReal_iff hρ).mp hstrict |>.le

end ProbabilityTheory
