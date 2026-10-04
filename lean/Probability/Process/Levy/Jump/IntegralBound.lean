/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Pathwise variation bound for jump integrals

The integral of jump marks over any observed time slice is controlled by the
total absolute jump mass on the full small-jump region. The statement is
deterministic and applies to each realization of a random point measure.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- One total-variation bound controls the displacement at every time on the
same realization; the time index need only have an order. -/
theorem abs_jumpIntegral_le_of_totalVariation_lt
    {Time Mark : Type*} [Preorder Time]
    [MeasurableSpace Time] [MeasurableSpace Mark]
    (ν : Measure (Time × Mark)) (A : Set (Time × Mark))
    (f : Mark → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hV : (∫⁻ z in A, ENNReal.ofReal |f z.2| ∂ν) < ENNReal.ofReal ρ) :
    ∀ t : Time,
      |∫ z in {z | z ∈ A ∧ z.1 ≤ t}, f z.2 ∂ν| ≤ ρ := by
  intro t
  let B : Set (Time × Mark) := {z | z ∈ A ∧ z.1 ≤ t}
  have hBA : B ⊆ A := fun _ hz => hz.1
  have hnorm := enorm_integral_le_lintegral_enorm
    (μ := ν.restrict B) (fun z => f z.2)
  have hnorm' : ENNReal.ofReal |∫ z in B, f z.2 ∂ν| ≤
      ∫⁻ z in B, ENNReal.ofReal |f z.2| ∂ν := by
    simpa only [Real.enorm_eq_ofReal_abs] using hnorm
  have hmono := lintegral_mono_set (μ := ν)
    (f := fun z => ENNReal.ofReal |f z.2|) hBA
  have hbound := hnorm'.trans hmono
  have hstrict := hbound.trans_lt hV
  exact (ENNReal.ofReal_lt_ofReal_iff hρ).mp hstrict |>.le

end ProbabilityTheory

end
