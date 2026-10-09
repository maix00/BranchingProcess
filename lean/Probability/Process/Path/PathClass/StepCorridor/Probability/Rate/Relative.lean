/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Analysis.Asymptotics.Limit

public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.InnerOuter

/-!
# Relative `M` approximations and path-law rates

The source path space can be a proper subset of the ambient càdlàg path
space. This file lets an `M₃` approximation sandwich a target only relative
to that domain, and transfers the sandwich to probabilities when every
sample path lies in the domain.
-/

open Filter MeasureTheory
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal Topology

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

/-- An `M₃` approximation of `G` relative to a path domain `D`. The inner and
outer set inclusions are required only after intersecting with `D`. -/
structure RelativeFiniteCorridorUnionApproximation (α : ℝ)
    (D G : Set (CadlagPath unitInterval ℝ)) where
  inner : ℕ → FiniteCorridorUnion α
  outer : ℕ → FiniteCorridorUnion α
  inner_subset : ∀ n, D ∩ (FiniteCorridorUnion.toSet (inner n)) ⊆ G
  subset_outer : ∀ n, G ⊆ D ∩ (FiniteCorridorUnion.toSet (outer n))
  energy_gap_tendsto_zero :
    Tendsto (fun n => FiniteCorridorUnion.realEnergy (inner n) - FiniteCorridorUnion.realEnergy (outer n))
      atTop (nhds 0)

/-- Membership in the relative version of the source's class `M`. -/
def HasRelativeVanishingEnergyGapApproximation (α : ℝ) (D G : Set (CadlagPath unitInterval ℝ)) : Prop :=
  Nonempty (RelativeFiniteCorridorUnionApproximation α D G)

/-- Convergent inner and outer energies for a relative approximation. -/
structure RelativeFiniteCorridorUnionEnergyLimits {α : ℝ}
    {D G : Set (CadlagPath unitInterval ℝ)}
    (A : RelativeFiniteCorridorUnionApproximation α D G) where
  innerLimit : ℝ
  outerLimit : ℝ
  inner_tendsto : Tendsto (fun n => FiniteCorridorUnion.realEnergy (A.inner n))
    atTop (nhds innerLimit)
  outer_tendsto : Tendsto (fun n => FiniteCorridorUnion.realEnergy (A.outer n))
    atTop (nhds outerLimit)

theorem RelativeFiniteCorridorUnionEnergyLimits.innerLimit_eq_outerLimit
    {α : ℝ} {D G : Set (CadlagPath unitInterval ℝ)}
    {A : RelativeFiniteCorridorUnionApproximation α D G}
    (h : RelativeFiniteCorridorUnionEnergyLimits A) : h.innerLimit = h.outerLimit := by
  have hdiff : Tendsto
      (fun n => FiniteCorridorUnion.realEnergy (A.inner n) - FiniteCorridorUnion.realEnergy (A.outer n))
      atTop (nhds (h.innerLimit - h.outerLimit)) :=
    h.inner_tendsto.sub h.outer_tendsto
  have hzero := tendsto_nhds_unique hdiff A.energy_gap_tendsto_zero
  linarith

/-- The common energy limit of a relative approximation. -/
def RelativeFiniteCorridorUnionEnergyLimits.commonEnergy
    {α : ℝ} {D G : Set (CadlagPath unitInterval ℝ)}
    {A : RelativeFiniteCorridorUnionApproximation α D G}
    (h : RelativeFiniteCorridorUnionEnergyLimits A) : ℝ := h.innerLimit

theorem RelativeFiniteCorridorUnionEnergyLimits.commonEnergy_eq_outerLimit
    {α : ℝ} {D G : Set (CadlagPath unitInterval ℝ)}
    {A : RelativeFiniteCorridorUnionApproximation α D G}
    (h : RelativeFiniteCorridorUnionEnergyLimits A) : h.commonEnergy = h.outerLimit :=
  h.innerLimit_eq_outerLimit

theorem FiniteCorridorUnion.realEnergy_antitone_of_eventSubset_of_probabilityRate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    (A B : FiniteCorridorUnion α)
    (hAB : ∀ x, {ω | paths x ω ∈ A.toSet} ⊆
      {ω | paths x ω ∈ B.toSet})
    (hApos : ∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ A.toSet}).toReal)
    (hBpos : ∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ B.toSet}).toReal)
    (hArate : Tendsto
      (fun x => Real.log ((P {ω | paths x ω ∈ A.toSet}).toReal) / g x)
      l (nhds (κ * A.realEnergy)))
    (hBrate : Tendsto
      (fun x => Real.log ((P {ω | paths x ω ∈ B.toSet}).toReal) / g x)
      l (nhds (κ * B.realEnergy))) :
    B.realEnergy ≤ A.realEnergy := by
  have hAfinite (x : I) : P {ω | paths x ω ∈ A.toSet} ≠ ⊤ := by
    apply ne_of_lt
    calc
      P {ω | paths x ω ∈ A.toSet} ≤ P Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hBfinite (x : I) : P {ω | paths x ω ∈ B.toSet} ≠ ⊤ := by
    apply ne_of_lt
    calc
      P {ω | paths x ω ∈ B.toSet} ≤ P Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hneg : ∀ᶠ x in l, g x < 0 := hg.eventually (eventually_lt_atBot 0)
  have hratio :
      (fun x => Real.log ((P {ω | paths x ω ∈ B.toSet}).toReal) / g x) ≤ᶠ[l]
      (fun x => Real.log ((P {ω | paths x ω ∈ A.toSet}).toReal) / g x) := by
    filter_upwards [hApos, hBpos, hneg] with x hAx hBx hgx
    have hmeasure : P {ω | paths x ω ∈ A.toSet} ≤
        P {ω | paths x ω ∈ B.toSet} := measure_mono (hAB x)
    have hreal := ENNReal.toReal_mono (hBfinite x) hmeasure
    have hlog := Real.log_le_log hAx hreal
    exact (div_le_div_right_of_neg hgx).2 hlog
  have hlim := le_of_tendsto_of_tendsto hBrate hArate hratio
  nlinarith [hκ]

/-- A common energy limit follows from a cross-order of inner and outer
energies and the vanishing energy gap. -/
noncomputable def RelativeFiniteCorridorUnionApproximation.energyLimits_of_crossOrder
    {α : ℝ} {D G : Set (CadlagPath unitInterval ℝ)}
    (A : RelativeFiniteCorridorUnionApproximation α D G)
    (hcross : ∀ n m, FiniteCorridorUnion.realEnergy (A.outer m) ≤ FiniteCorridorUnion.realEnergy (A.inner n)) :
    RelativeFiniteCorridorUnionEnergyLimits A := by
  let innerCost : ℕ → ℝ := fun n => FiniteCorridorUnion.realEnergy (A.inner n)
  let outerCost : ℕ → ℝ := fun n => FiniteCorridorUnion.realEnergy (A.outer n)
  have hCauchy : CauchySeq innerCost := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
      (A.energy_gap_tendsto_zero.eventually (Iio_mem_nhds hε))
    refine ⟨N, ?_⟩
    intro m hm n hn
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor
    · have hgap := hN n hn
      have hcrossnm : outerCost n ≤ innerCost m := hcross m n
      dsimp [innerCost, outerCost] at hgap hcrossnm
      linarith
    · have hgap := hN m hm
      have hcrossmn : outerCost m ≤ innerCost n := hcross n m
      dsimp [innerCost, outerCost] at hgap hcrossmn
      linarith
  classical
  let hExists : ∃ L, Tendsto innerCost atTop (nhds L) :=
    cauchySeq_tendsto_of_complete hCauchy
  refine ⟨hExists.choose, hExists.choose, ?_, ?_⟩
  · simpa [innerCost] using hExists.choose_spec
  · have houter := hExists.choose_spec.sub A.energy_gap_tendsto_zero
    have heq :
        (fun n => FiniteCorridorUnion.realEnergy (A.inner n) -
          (FiniteCorridorUnion.realEnergy (A.inner n) - FiniteCorridorUnion.realEnergy (A.outer n))) =
        fun n => FiniteCorridorUnion.realEnergy (A.outer n) := by
      funext n
      ring
    rw [heq] at houter
    simpa [outerCost] using houter

/-- Cross-order of relative inner and outer energies, together with the
vanishing energy gap, gives a common energy limit. The order is obtained from
the component `M₃` probability rates along paths supported on the domain. -/
noncomputable def RelativeFiniteCorridorUnionApproximation.energyLimits_of_probabilityRate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (domain : Set (CadlagPath unitInterval ℝ))
    (hpaths : ∀ x ω, paths x ω ∈ domain)
    (g : I → ℝ) (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)}
    (A : RelativeFiniteCorridorUnionApproximation α domain G)
    (hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ x, NullMeasurableSet {ω | paths x ω ∈ C.toSet} P) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (nhds (κ * C.realEnergy))) :
    RelativeFiniteCorridorUnionEnergyLimits A := by
  apply RelativeFiniteCorridorUnionApproximation.energyLimits_of_crossOrder A
  intro n m
  apply FiniteCorridorUnion.realEnergy_antitone_of_eventSubset_of_probabilityRate
    P paths g hg hκ (A.inner n) (A.outer m)
  · intro x ω hω
    exact (A.subset_outer m (A.inner_subset n ⟨hpaths x ω, hω⟩)).2
  · exact (hFiniteUnionRate (A.inner n)).2.1
  · exact (hFiniteUnionRate (A.outer m)).2.1
  · exact (hFiniteUnionRate (A.inner n)).2.2
  · exact (hFiniteUnionRate (A.outer m)).2.2

/-- For a relative `M₃` approximation, both the inner and outer probabilities
of the target event have the common logarithmic rate. The only support
assumption is that every sampled path belongs to the domain relative to which
the approximation is defined. The target event need not be measurable. -/
theorem tendsto_inner_outer_log_probability_ratio_of_RelativeFiniteCorridorUnionApproximation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ)
    (domain : Set (CadlagPath unitInterval ℝ))
    (hpaths : ∀ x ω, paths x ω ∈ domain)
    (g : I → ℝ) (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)}
    (A : RelativeFiniteCorridorUnionApproximation α domain G)
    (hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ x, NullMeasurableSet {ω | paths x ω ∈ C.toSet} P) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (nhds (κ * C.realEnergy))) :
    ∃ hLimits : RelativeFiniteCorridorUnionEnergyLimits A,
      (∀ᶠ x in l,
        0 < (P.innerMeasure {ω | paths x ω ∈ G}).toReal) ∧
      (∀ᶠ x in l,
        0 < (P {ω | paths x ω ∈ G}).toReal) ∧
      Tendsto
        (fun x => Real.log
          ((P.innerMeasure {ω | paths x ω ∈ G}).toReal) / g x)
        l (nhds (κ * hLimits.commonEnergy)) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x)
        l (nhds (κ * hLimits.commonEnergy)) ∧
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

  let hLimits : RelativeFiniteCorridorUnionEnergyLimits A :=
    RelativeFiniteCorridorUnionApproximation.energyLimits_of_probabilityRate
      P paths domain hpaths g hg hκ A hFiniteUnionRate

  have hPfinite (s : Set Ω) : P s < ⊤ := by
    calc
      P s ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hInnerFinite (x : I) :
      P.innerMeasure (targetEvent x) ≠ ⊤ := by
    exact (lt_of_le_of_lt
      (Measure.innerMeasure_le_measure P (targetEvent x))
      (hPfinite (targetEvent x))).ne
  have hLowerSubset (x : I) (n : ℕ) : lowerEvent x n ⊆ targetEvent x := by
    intro ω hω
    exact A.inner_subset n ⟨hpaths x ω, hω⟩
  have hTargetSubsetUpper (x : I) (n : ℕ) :
      targetEvent x ⊆ upperEvent x n := by
    intro ω hω
    exact (A.subset_outer n hω).2
  have hLowerMeasureLeInner (x : I) (n : ℕ) :
      P (lowerEvent x n) ≤ P.innerMeasure (targetEvent x) := by
    apply Measure.measure_le_innerMeasure_of_nullMeasurableSet_subset
      P ((hFiniteUnionRate (A.inner n)).1 x)
    exact hLowerSubset x n

  have hInnerPositive : ∀ᶠ x in l,
      0 < (P.innerMeasure (targetEvent x)).toReal := by
    filter_upwards [(hFiniteUnionRate (A.inner 0)).2.1] with x hx
    have hreal : (P (lowerEvent x 0)).toReal ≤
        (P.innerMeasure (targetEvent x)).toReal :=
      ENNReal.toReal_mono (hInnerFinite x) (hLowerMeasureLeInner x 0)
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
      (hLowerMeasureLeInner x n)
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
      Tendsto (lowerRatio n) l (nhds (κ * FiniteCorridorUnion.realEnergy (A.inner n))) := by
    simpa [lowerRatio, lowerEvent] using (hFiniteUnionRate (A.inner n)).2.2
  have hUpperRate (n : ℕ) :
      Tendsto (upperRatio n) l (nhds (κ * FiniteCorridorUnion.realEnergy (A.outer n))) := by
    simpa [upperRatio, upperEvent] using (hFiniteUnionRate (A.outer n)).2.2
  have hInnerEnergyRate :
      Tendsto (fun n => κ * FiniteCorridorUnion.realEnergy (A.inner n)) atTop
        (nhds (κ * hLimits.commonEnergy)) := by
    simpa [RelativeFiniteCorridorUnionEnergyLimits.commonEnergy] using
      (tendsto_const_nhds.mul hLimits.inner_tendsto)
  have hOuterEnergyRate :
      Tendsto (fun n => κ * FiniteCorridorUnion.realEnergy (A.outer n)) atTop
        (nhds (κ * hLimits.commonEnergy)) := by
    have heq : hLimits.outerLimit = hLimits.commonEnergy :=
      hLimits.commonEnergy_eq_outerLimit.symm
    simpa [RelativeFiniteCorridorUnionEnergyLimits.commonEnergy, heq] using
      (tendsto_const_nhds.mul hLimits.outer_tendsto)
  have hEnergyBounds :
      0 < hLimits.commonEnergy ∧ hLimits.commonEnergy ≤ FiniteCorridorUnion.realEnergy (A.inner 0) := by
    have hOuter0LeInner (n : ℕ) :
        FiniteCorridorUnion.realEnergy (A.outer 0) ≤ FiniteCorridorUnion.realEnergy (A.inner n) := by
      apply FiniteCorridorUnion.realEnergy_antitone_of_eventSubset_of_probabilityRate
        P paths g hg hκ (A.inner n) (A.outer 0)
      · intro x ω hω
        exact (A.subset_outer 0
          (A.inner_subset n ⟨hpaths x ω, hω⟩)).2
      · exact (hFiniteUnionRate (A.inner n)).2.1
      · exact (hFiniteUnionRate (A.outer 0)).2.1
      · exact (hFiniteUnionRate (A.inner n)).2.2
      · exact (hFiniteUnionRate (A.outer 0)).2.2
    have hinnerLower : FiniteCorridorUnion.realEnergy (A.outer 0) ≤ hLimits.innerLimit :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hLimits.inner_tendsto
        (Filter.Eventually.of_forall hOuter0LeInner)
    have hOuterLeInner0 (n : ℕ) :
        FiniteCorridorUnion.realEnergy (A.outer n) ≤ FiniteCorridorUnion.realEnergy (A.inner 0) := by
      apply FiniteCorridorUnion.realEnergy_antitone_of_eventSubset_of_probabilityRate
        P paths g hg hκ (A.inner 0) (A.outer n)
      · intro x ω hω
        exact (A.subset_outer n
          (A.inner_subset 0 ⟨hpaths x ω, hω⟩)).2
      · exact (hFiniteUnionRate (A.inner 0)).2.1
      · exact (hFiniteUnionRate (A.outer n)).2.1
      · exact (hFiniteUnionRate (A.inner 0)).2.2
      · exact (hFiniteUnionRate (A.outer n)).2.2
    have houterUpper : hLimits.outerLimit ≤ FiniteCorridorUnion.realEnergy (A.inner 0) :=
      le_of_tendsto_of_tendsto hLimits.outer_tendsto tendsto_const_nhds
        (Filter.Eventually.of_forall hOuterLeInner0)
    refine ⟨?_, ?_⟩
    · exact (FiniteCorridorUnion.realEnergy_pos (A.outer 0)).trans_le hinnerLower
    · calc
        hLimits.commonEnergy = hLimits.outerLimit := hLimits.innerLimit_eq_outerLimit
        _ ≤ FiniteCorridorUnion.realEnergy (A.inner 0) := houterUpper

  refine ⟨hLimits, hInnerPositive, hOuterPositive, ?_, ?_, hEnergyBounds⟩
  · exact tendsto_of_eventually_sandwiched_by_convergent_approximants innerTargetRatio upperRatio lowerRatio
      (fun n => κ * FiniteCorridorUnion.realEnergy (A.outer n))
      (fun n => κ * FiniteCorridorUnion.realEnergy (A.inner n))
      (κ * hLimits.commonEnergy)
      hUpperApproxLowerBound hLowerApproxUpperBound hUpperRate hLowerRate
      hOuterEnergyRate hInnerEnergyRate
  · exact tendsto_of_eventually_sandwiched_by_convergent_approximants outerTargetRatio upperRatio lowerRatio
      (fun n => κ * FiniteCorridorUnion.realEnergy (A.outer n))
      (fun n => κ * FiniteCorridorUnion.realEnergy (A.inner n))
      (κ * hLimits.commonEnergy)
      hUpperApproxLowerBoundOuter hLowerApproxUpperBoundOuter hUpperRate hLowerRate
      hOuterEnergyRate hInnerEnergyRate

/-- The common energy attached to a relative `M` set is independent of its
relative approximation witness, whenever all component `M₃` rates hold. -/
theorem RelativeFiniteCorridorUnionEnergyLimits.commonEnergy_eq_of_approximation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ)
    (domain : Set (CadlagPath unitInterval ℝ))
    (hpaths : ∀ x ω, paths x ω ∈ domain)
    (g : I → ℝ) (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)}
    (A B : RelativeFiniteCorridorUnionApproximation α domain G)
    (hA : RelativeFiniteCorridorUnionEnergyLimits A) (hB : RelativeFiniteCorridorUnionEnergyLimits B)
    (hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ x, NullMeasurableSet {ω | paths x ω ∈ C.toSet} P) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (nhds (κ * C.realEnergy))) :
    hA.commonEnergy = hB.commonEnergy := by
  have hAouterLeBinner (n : ℕ) :
      FiniteCorridorUnion.realEnergy (A.outer n) ≤ FiniteCorridorUnion.realEnergy (B.inner n) := by
    apply FiniteCorridorUnion.realEnergy_antitone_of_eventSubset_of_probabilityRate
      P paths g hg hκ (B.inner n) (A.outer n)
    · intro x ω hω
      exact (A.subset_outer n
        (B.inner_subset n ⟨hpaths x ω, hω⟩)).2
    · exact (hFiniteUnionRate (B.inner n)).2.1
    · exact (hFiniteUnionRate (A.outer n)).2.1
    · exact (hFiniteUnionRate (B.inner n)).2.2
    · exact (hFiniteUnionRate (A.outer n)).2.2
  have hBouterLeAinner (n : ℕ) :
      FiniteCorridorUnion.realEnergy (B.outer n) ≤ FiniteCorridorUnion.realEnergy (A.inner n) := by
    apply FiniteCorridorUnion.realEnergy_antitone_of_eventSubset_of_probabilityRate
      P paths g hg hκ (A.inner n) (B.outer n)
    · intro x ω hω
      exact (B.subset_outer n
        (A.inner_subset n ⟨hpaths x ω, hω⟩)).2
    · exact (hFiniteUnionRate (A.inner n)).2.1
    · exact (hFiniteUnionRate (B.outer n)).2.1
    · exact (hFiniteUnionRate (A.inner n)).2.2
    · exact (hFiniteUnionRate (B.outer n)).2.2
  have hAleB : hA.commonEnergy ≤ hB.commonEnergy := by
    calc
      hA.commonEnergy = hA.outerLimit := hA.commonEnergy_eq_outerLimit
      _ ≤ hB.innerLimit := le_of_tendsto_of_tendsto
        hA.outer_tendsto hB.inner_tendsto
        (Filter.Eventually.of_forall hAouterLeBinner)
      _ = hB.commonEnergy := rfl
  have hBleA : hB.commonEnergy ≤ hA.commonEnergy := by
    calc
      hB.commonEnergy = hB.outerLimit := hB.commonEnergy_eq_outerLimit
      _ ≤ hA.innerLimit := le_of_tendsto_of_tendsto
        hB.outer_tendsto hA.inner_tendsto
        (Filter.Eventually.of_forall hBouterLeAinner)
      _ = hA.commonEnergy := rfl
  exact le_antisymm hAleB hBleA

/-- Every relative `M` set has one common inner/outer logarithmic rate. The
target itself need not be measurable, and the value is independent of the
chosen relative approximation witness. -/
theorem existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ)
    (domain : Set (CadlagPath unitInterval ℝ))
    (hpaths : ∀ x ω, paths x ω ∈ domain)
    (g : I → ℝ) (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasRelativeVanishingEnergyGapApproximation α domain G)
    (hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ x, NullMeasurableSet {ω | paths x ω ∈ C.toSet} P) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (nhds (κ * C.realEnergy))) :
    ∃! H : ℝ,
      ∃ A : RelativeFiniteCorridorUnionApproximation α domain G,
        ∃ hLimits : RelativeFiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy ∧
          (∀ᶠ x in l,
            0 < (P.innerMeasure {ω | paths x ω ∈ G}).toReal) ∧
          (∀ᶠ x in l,
            0 < (P {ω | paths x ω ∈ G}).toReal) ∧
          Tendsto
            (fun x => Real.log
              ((P.innerMeasure {ω | paths x ω ∈ G}).toReal) / g x)
            l (nhds (κ * H)) ∧
          Tendsto
            (fun x => Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x)
            l (nhds (κ * H)) := by
  rcases hG with ⟨A⟩
  obtain ⟨hLimits, hInnerPos, hOuterPos, hInnerRate, hOuterRate, hBounds⟩ :=
    tendsto_inner_outer_log_probability_ratio_of_RelativeFiniteCorridorUnionApproximation
      P paths domain hpaths g hg hκ A hFiniteUnionRate
  let H : ℝ := hLimits.commonEnergy
  refine ⟨H, ⟨A, hLimits, rfl, hInnerPos, hOuterPos, ?_, ?_⟩, ?_⟩
  · simpa [H] using hInnerRate
  · simpa [H] using hOuterRate
  · intro H' hH'
    obtain ⟨A', hLimits', hEq', _hInnerPos', _hOuterPos', _hInnerRate',
      _hOuterRate'⟩ := hH'
    have hEq := RelativeFiniteCorridorUnionEnergyLimits.commonEnergy_eq_of_approximation
      P paths domain hpaths g hg hκ A' A hLimits' hLimits hFiniteUnionRate
    exact hEq'.trans hEq

end ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

end
