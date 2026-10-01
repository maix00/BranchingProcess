module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Small total variation has positive probability

This is the Markov-inequality step for the sum of small jumps. It is stated
for any nonnegative random variable, so a later Poisson integral needs only
to establish its expected total variation.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

theorem measure_smallVariation_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (V : Ω → ENNReal)
    (hV : Measurable V) (ρ : ENNReal)
    (hE : (∫⁻ ω, V ω ∂P) < ρ) :
    0 < P {ω | V ω < ρ} := by
  have hρ : ρ ≠ 0 := by
    intro hzero
    rw [hzero] at hE
    exact (not_lt_of_ge (bot_le : (0 : ENNReal) ≤ ∫⁻ ω, V ω ∂P)) hE
  have hgood : MeasurableSet {ω | V ω < ρ} := hV measurableSet_Iio
  have hmarkov := mul_meas_ge_le_lintegral (μ := P) hV ρ
  by_contra hpos
  have hzero : P {ω | V ω < ρ} = 0 := le_antisymm (not_lt.mp hpos) bot_le
  have hbad : {ω | ρ ≤ V ω} = {ω | V ω < ρ}ᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
  rw [hbad, measure_compl hgood (by simp), hzero] at hmarkov
  simp only [measure_univ, tsub_zero, mul_one] at hmarkov
  exact (not_lt_of_ge hmarkov) hE

end ProbabilityTheory

end
