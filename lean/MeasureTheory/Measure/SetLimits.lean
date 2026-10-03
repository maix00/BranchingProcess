module

public import Mathlib.MeasureTheory.Integral.Indicator
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Limits of measures of event sequences

These results concern finite measures and probability measures on arbitrary
measurable spaces. They do not depend on a stochastic process or a particular
probability model.
-/

@[expose] public section

namespace MeasureTheory

open Filter
open scoped Topology

theorem tendsto_measure_univ_of_ae_eventually
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A : ℕ → Set Ω) (hA : ∀ n, NullMeasurableSet (A n) P)
    (h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ A n) :
    Tendsto (fun n => P (A n)) atTop (𝓝 (P Set.univ)) := by
  let B : ℕ → Set Ω := fun n => toMeasurable P (A n)
  have heq : ∀ᵐ ω ∂P, ∀ n, (ω ∈ B n ↔ ω ∈ A n) := by
    apply ae_all_iff.mpr
    intro n
    exact (hA n).toMeasurable_ae_eq.mem_iff
  have hB : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ B n ↔ ω ∈ Set.univ := by
    filter_upwards [heq, h] with ω hω hωeventually
    filter_upwards [hωeventually] with n hn
    simpa [hω n] using hn
  have hlim : Tendsto (fun n => P (B n)) atTop (𝓝 (P Set.univ)) :=
    tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
      MeasurableSet.univ (fun n => measurableSet_toMeasurable P (A n)) hB
  have hmeasure (n : ℕ) : P (A n) = P (B n) :=
    measure_congr (hA n).toMeasurable_ae_eq.symm
  simpa only [hmeasure] using hlim

/-- An event whose probability tends to one eventually has a positive
intersection with any event whose probability has a fixed positive lower
bound. The first event may be only null-measurable. -/
theorem eventually_measure_inter_pos_of_tendsto_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : ℕ → Set Ω) (hA : ∀ n, NullMeasurableSet (A n) P)
    (hlim : Tendsto (fun n => P (A n)) atTop (𝓝 1))
    {c : ENNReal} (hc : 0 < c) (hB : ∀ n, c ≤ P (B n)) :
    ∀ᶠ n in atTop, 0 < P (A n ∩ B n) := by
  have hcomp : Tendsto (fun n => P ((A n)ᶜ)) atTop (𝓝 0) := by
    have hsub := ENNReal.Tendsto.sub
      (tendsto_const_nhds (x := (1 : ENNReal))) hlim
      (Or.inl ENNReal.one_ne_top)
    have heq : ∀ n, P ((A n)ᶜ) = 1 - P (A n) := by
      intro n
      simpa [measure_univ] using
        (measure_compl₀ (hA n) (measure_ne_top P (A n)))
    simpa [heq] using hsub
  obtain ⟨ε, hε0, hεc⟩ := exists_between hc
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hcomp ε hε0] with n hn
  by_contra hnot
  have hzero : P (A n ∩ B n) = 0 := (not_lt.mp hnot).antisymm bot_le
  have hsplit := measure_inter_add_sdiff₀ (B n) (hA n)
  rw [Set.inter_comm, hzero, zero_add] at hsplit
  have hle : P (B n) ≤ P ((A n)ᶜ) := by
    rw [← hsplit]
    exact measure_mono (Set.sdiff_subset_compl (B n) (A n))
  exact (not_le_of_gt hεc) ((hB n).trans (hle.trans hn))

end MeasureTheory
