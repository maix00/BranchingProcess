/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Approximation
public import MeasureTheory.Measure.InnerOuter

/-!
# Inner and outer probability rates for class `M`

For an arbitrary target event, the value `μ s` of a Mathlib measure is its
outer measure.  The inner measure below is the supremum of the measures of
measurable subsets.  An `M₃` approximation sandwiches these two values, so
both have the common logarithmic rate even when the target event itself is not
measurable.  This result does not infer null-measurability from the energy
approximation.
-/

open Filter MeasureTheory
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal Topology

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

private theorem tendsto_of_twoSidedRateSqueeze
    {I : Type*} {l : Filter I} [NeBot l]
    (f : I → ℝ) (lower upper : ℕ → I → ℝ)
    (lowerLimit upperLimit : ℕ → ℝ) (L : ℝ)
    (hlower : ∀ n, lower n ≤ᶠ[l] f)
    (hupper : ∀ n, f ≤ᶠ[l] upper n)
    (hlowerRate : ∀ n, Tendsto (lower n) l (𝓝 (lowerLimit n)))
    (hupperRate : ∀ n, Tendsto (upper n) l (𝓝 (upperLimit n)))
    (hlowerLimit : Tendsto lowerLimit atTop (𝓝 L))
    (hupperLimit : Tendsto upperLimit atTop (𝓝 L)) :
    Tendsto f l (𝓝 L) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
      hlowerLimit.eventually (Ioi_mem_nhds hy)
    have hrate := (hlowerRate N).eventually (Ioi_mem_nhds (hN N le_rfl))
    filter_upwards [hlower N, hrate] with x hbound hrate
    exact lt_of_lt_of_le hrate hbound
  · intro y hy
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
      hupperLimit.eventually (Iio_mem_nhds hy)
    have hrate := (hupperRate N).eventually (Iio_mem_nhds (hN N le_rfl))
    filter_upwards [hupper N, hrate] with x hbound hrate
    exact lt_of_le_of_lt hbound hrate

private theorem energyBounds_of_probabilityRate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)}
    (A : FiniteCorridorUnionApproximation α G) (hLimits : FiniteCorridorUnionEnergyLimits A)
    (hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ x, NullMeasurableSet {ω | paths x ω ∈ C.toSet} P) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * C.realEnergy))) :
    0 < hLimits.commonEnergy ∧ hLimits.commonEnergy ≤ FiniteCorridorUnion.realEnergy (A.inner 0) := by
  have hOuter0_le_inner (n : ℕ) :
      FiniteCorridorUnion.realEnergy (A.outer 0) ≤ FiniteCorridorUnion.realEnergy (A.inner n) :=
    FiniteCorridorUnion.realEnergy_antitone_of_subset_of_probabilityRate P paths g hg hκ
      (A.inner n) (A.outer 0)
      (fun f hf => A.subset_outer 0 (A.inner_subset n hf))
      (hFiniteUnionRate (A.inner n)).2.1 (hFiniteUnionRate (A.outer 0)).2.1
      (hFiniteUnionRate (A.inner n)).2.2 (hFiniteUnionRate (A.outer 0)).2.2
  have hinnerLower : FiniteCorridorUnion.realEnergy (A.outer 0) ≤ hLimits.innerLimit :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hLimits.inner_tendsto
      (Filter.Eventually.of_forall hOuter0_le_inner)
  have hOuter_le_inner0 (n : ℕ) :
      FiniteCorridorUnion.realEnergy (A.outer n) ≤ FiniteCorridorUnion.realEnergy (A.inner 0) :=
    FiniteCorridorUnion.realEnergy_antitone_of_subset_of_probabilityRate P paths g hg hκ
      (A.inner 0) (A.outer n)
      (fun f hf => A.subset_outer n (A.inner_subset 0 hf))
      (hFiniteUnionRate (A.inner 0)).2.1 (hFiniteUnionRate (A.outer n)).2.1
      (hFiniteUnionRate (A.inner 0)).2.2 (hFiniteUnionRate (A.outer n)).2.2
  have houterUpper : hLimits.outerLimit ≤ FiniteCorridorUnion.realEnergy (A.inner 0) :=
    le_of_tendsto_of_tendsto hLimits.outer_tendsto tendsto_const_nhds
      (Filter.Eventually.of_forall hOuter_le_inner0)
  refine ⟨?_, ?_⟩
  · exact (FiniteCorridorUnion.realEnergy_pos (A.outer 0)).trans_le hinnerLower
  · calc
      hLimits.commonEnergy = hLimits.outerLimit := hLimits.innerLimit_eq_outerLimit
      _ ≤ FiniteCorridorUnion.realEnergy (A.inner 0) := houterUpper

/-- If the `M₃` events have their usual probability rates, then the inner and
outer probabilities of a set equipped with an `M₃` approximation are squeezed
to the same logarithmic rate.  The target event itself is not required to be
null-measurable. -/
theorem tendsto_inner_outer_log_probability_ratio_of_FiniteCorridorUnionApproximation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)}
    (A : FiniteCorridorUnionApproximation α G)
    (hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ x, NullMeasurableSet {ω | paths x ω ∈ C.toSet} P) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * C.realEnergy))) :
    ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
      (∀ᶠ x in l,
        0 < (P.innerMeasure {ω | paths x ω ∈ G}).toReal) ∧
      (∀ᶠ x in l,
        0 < (P {ω | paths x ω ∈ G}).toReal) ∧
      Tendsto
        (fun x => Real.log
          ((P.innerMeasure {ω | paths x ω ∈ G}).toReal) / g x)
        l (𝓝 (κ * hLimits.commonEnergy)) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x)
        l (𝓝 (κ * hLimits.commonEnergy)) ∧
      0 < hLimits.commonEnergy ∧ hLimits.commonEnergy ≤ FiniteCorridorUnion.realEnergy (A.inner 0) := by
  classical
  let lowerEvent : I → ℕ → Set Ω := fun x n =>
    {ω | paths x ω ∈ (A.inner n).toSet}
  let upperEvent : I → ℕ → Set Ω := fun x n =>
    {ω | paths x ω ∈ (A.outer n).toSet}
  let targetEvent : I → Set Ω := fun x => {ω | paths x ω ∈ G}
  let lowerRatio : ℕ → I → ℝ := fun n x =>
    Real.log ((P (lowerEvent x n)).toReal) / g x
  let upperRatio : ℕ → I → ℝ := fun n x =>
    Real.log ((P (upperEvent x n)).toReal) / g x
  let innerTargetRatio : I → ℝ := fun x =>
    Real.log ((P.innerMeasure (targetEvent x)).toReal) / g x
  let outerTargetRatio : I → ℝ := fun x =>
    Real.log ((P (targetEvent x)).toReal) / g x

  let hLimits : FiniteCorridorUnionEnergyLimits A :=
    FiniteCorridorUnionApproximation.energyLimits_of_probabilityRate P paths g hg hκ A hFiniteUnionRate

  have hPfinite (s : Set Ω) : P s < ⊤ := by
    calc
      P s ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top

  have hInnerFinite (x : I) : P.innerMeasure (targetEvent x) ≠ ⊤ := by
    apply (lt_of_le_of_lt
      (Measure.innerMeasure_le_measure P (targetEvent x))
      (hPfinite (targetEvent x))).ne

  have hLowerSubset (x : I) (n : ℕ) : lowerEvent x n ⊆ targetEvent x := by
    intro ω hω
    exact A.inner_subset n hω

  have hTargetSubsetUpper (x : I) (n : ℕ) :
      targetEvent x ⊆ upperEvent x n := by
    intro ω hω
    exact A.subset_outer n hω

  have hLowerMeasure_le_inner (x : I) (n : ℕ) :
      P (lowerEvent x n) ≤ P.innerMeasure (targetEvent x) := by
    apply Measure.measure_le_innerMeasure_of_nullMeasurableSet_subset
      P ((hFiniteUnionRate (A.inner n)).1 x)
    exact hLowerSubset x n

  have hInnerPositive : ∀ᶠ x in l,
      0 < (P.innerMeasure (targetEvent x)).toReal := by
    filter_upwards [(hFiniteUnionRate (A.inner 0)).2.1] with x hx
    have hreal : (P (lowerEvent x 0)).toReal ≤
        (P.innerMeasure (targetEvent x)).toReal :=
      ENNReal.toReal_mono (hInnerFinite x) (hLowerMeasure_le_inner x 0)
    exact lt_of_lt_of_le hx hreal

  have hOuterPositive : ∀ᶠ x in l,
      0 < (P (targetEvent x)).toReal := by
    filter_upwards [hInnerPositive] with x hx
    have hreal : (P.innerMeasure (targetEvent x)).toReal ≤
        (P (targetEvent x)).toReal :=
      ENNReal.toReal_mono (hPfinite (targetEvent x)).ne
        (Measure.innerMeasure_le_measure P (targetEvent x))
    exact lt_of_lt_of_le hx hreal

  have hneg : ∀ᶠ x in l, g x < 0 :=
    hg.eventually (eventually_lt_atBot 0)

  have hUpperApproxLowerBound (n : ℕ) :
      upperRatio n ≤ᶠ[l] innerTargetRatio := by
    filter_upwards [hInnerPositive, hneg] with x htargetPos hgx
    have hmeasure : P.innerMeasure (targetEvent x) ≤ P (upperEvent x n) := by
      calc
        P.innerMeasure (targetEvent x) ≤ P (targetEvent x) :=
          Measure.innerMeasure_le_measure P (targetEvent x)
        _ ≤ P (upperEvent x n) := measure_mono (hTargetSubsetUpper x n)
    have hreal := ENNReal.toReal_mono (hPfinite (upperEvent x n)).ne hmeasure
    have hlog := Real.log_le_log htargetPos hreal
    exact (div_le_div_right_of_neg hgx).2 hlog

  have hUpperApproxLowerBoundOuter (n : ℕ) :
      upperRatio n ≤ᶠ[l] outerTargetRatio := by
    filter_upwards [hOuterPositive, hneg] with x htargetPos hgx
    have hmeasure : P (targetEvent x) ≤ P (upperEvent x n) :=
      measure_mono (hTargetSubsetUpper x n)
    have hreal := ENNReal.toReal_mono (hPfinite (upperEvent x n)).ne hmeasure
    have hlog := Real.log_le_log htargetPos hreal
    exact (div_le_div_right_of_neg hgx).2 hlog

  have hLowerApproxUpperBound (n : ℕ) :
      innerTargetRatio ≤ᶠ[l] lowerRatio n := by
    filter_upwards [hInnerPositive, (hFiniteUnionRate (A.inner n)).2.1, hneg]
      with x htargetPos hlowerPos hgx
    have hreal := ENNReal.toReal_mono (hInnerFinite x)
      (hLowerMeasure_le_inner x n)
    have hlog := Real.log_le_log hlowerPos hreal
    exact (div_le_div_right_of_neg hgx).2 hlog

  have hLowerApproxUpperBoundOuter (n : ℕ) :
      outerTargetRatio ≤ᶠ[l] lowerRatio n := by
    filter_upwards [hOuterPositive, (hFiniteUnionRate (A.inner n)).2.1, hneg]
      with x htargetPos hlowerPos hgx
    have hmeasure : P (lowerEvent x n) ≤ P (targetEvent x) :=
      measure_mono (hLowerSubset x n)
    have hreal := ENNReal.toReal_mono (hPfinite (targetEvent x)).ne hmeasure
    have hlog := Real.log_le_log hlowerPos hreal
    exact (div_le_div_right_of_neg hgx).2 hlog

  have hLowerRate (n : ℕ) :
      Tendsto (lowerRatio n) l (𝓝 (κ * FiniteCorridorUnion.realEnergy (A.inner n))) := by
    simpa [lowerRatio, lowerEvent] using (hFiniteUnionRate (A.inner n)).2.2

  have hUpperRate (n : ℕ) :
      Tendsto (upperRatio n) l (𝓝 (κ * FiniteCorridorUnion.realEnergy (A.outer n))) := by
    simpa [upperRatio, upperEvent] using (hFiniteUnionRate (A.outer n)).2.2

  have hInnerEnergyRate :
      Tendsto (fun n => κ * FiniteCorridorUnion.realEnergy (A.inner n)) atTop
        (𝓝 (κ * hLimits.commonEnergy)) := by
    simpa [FiniteCorridorUnionEnergyLimits.commonEnergy] using
      (tendsto_const_nhds.mul hLimits.inner_tendsto)

  have hOuterEnergyRate :
      Tendsto (fun n => κ * FiniteCorridorUnion.realEnergy (A.outer n)) atTop
        (𝓝 (κ * hLimits.commonEnergy)) := by
    have heq : hLimits.outerLimit = hLimits.commonEnergy :=
      hLimits.commonEnergy_eq_outerLimit.symm
    simpa [FiniteCorridorUnionEnergyLimits.commonEnergy, heq] using
      (tendsto_const_nhds.mul hLimits.outer_tendsto)

  have hEnergyBounds := energyBounds_of_probabilityRate
    P paths g hg hκ A hLimits hFiniteUnionRate
  refine ⟨hLimits, hInnerPositive, hOuterPositive, ?_, ?_, hEnergyBounds⟩
  · exact tendsto_of_twoSidedRateSqueeze innerTargetRatio upperRatio lowerRatio
      (fun n => κ * FiniteCorridorUnion.realEnergy (A.outer n))
      (fun n => κ * FiniteCorridorUnion.realEnergy (A.inner n))
      (κ * hLimits.commonEnergy)
      hUpperApproxLowerBound hLowerApproxUpperBound hUpperRate hLowerRate
      hOuterEnergyRate hInnerEnergyRate
  · exact tendsto_of_twoSidedRateSqueeze outerTargetRatio upperRatio lowerRatio
      (fun n => κ * FiniteCorridorUnion.realEnergy (A.outer n))
      (fun n => κ * FiniteCorridorUnion.realEnergy (A.inner n))
      (κ * hLimits.commonEnergy)
      hUpperApproxLowerBoundOuter hLowerApproxUpperBoundOuter hUpperRate hLowerRate
      hOuterEnergyRate hInnerEnergyRate

/-- Every `HasVanishingEnergyGapApproximation` set has matching inner- and outer-probability logarithmic
rates, obtained from an `M₃` approximation witness.  The event's own
null-measurability is not a hypothesis. -/
theorem exists_inner_outer_log_probability_ratio_of_hasVanishingEnergyGapApproximation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G)
    (hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ x, NullMeasurableSet {ω | paths x ω ∈ C.toSet} P) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * C.realEnergy))) :
    ∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
      (∀ᶠ x in l,
        0 < (P.innerMeasure {ω | paths x ω ∈ G}).toReal) ∧
      (∀ᶠ x in l,
        0 < (P {ω | paths x ω ∈ G}).toReal) ∧
      Tendsto
        (fun x => Real.log
          ((P.innerMeasure {ω | paths x ω ∈ G}).toReal) / g x)
        l (𝓝 (κ * hLimits.commonEnergy)) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x)
        l (𝓝 (κ * hLimits.commonEnergy)) ∧
      0 < hLimits.commonEnergy ∧ hLimits.commonEnergy ≤ FiniteCorridorUnion.realEnergy (A.inner 0) := by
  obtain ⟨A⟩ := hG
  obtain ⟨hLimits, hInnerPos, hOuterPos, hInnerRate, hOuterRate, hEnergyBounds⟩ :=
    tendsto_inner_outer_log_probability_ratio_of_FiniteCorridorUnionApproximation
      P paths g hg hκ A hFiniteUnionRate
  exact ⟨A, hLimits, hInnerPos, hOuterPos, hInnerRate, hOuterRate, hEnergyBounds⟩

end ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

end
