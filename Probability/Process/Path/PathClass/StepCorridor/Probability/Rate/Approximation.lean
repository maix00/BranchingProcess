/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Approximation
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.FiniteUnion
public import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.FiniteUnionNullMeasurable
import Mathlib.Topology.Order.Basic

/-!
# Approximation energies and the process theorem

The `M₃` rate implies that energy is antitone under set inclusion.  The
source's inner/outer approximation condition then forces both energy
sequences to converge to the same value.  Finally, fixed inner and outer
approximants squeeze the probability rate of any measurable set in class `M`.
The component `M₂` rate remains an explicit input through the `M₃` rate
hypothesis.
-/

open Filter MeasureTheory
open Skorokhod.PathClass.StepCorridor Set
open scoped Topology

open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

@[expose] public section

namespace ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

/-- If two `M₃` path sets are included and both have the same process rate
formula, their energies are ordered in the reverse direction. -/
theorem FiniteCorridorUnion.realEnergy_antitone_of_subset_of_probabilityRate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    (A B : FiniteCorridorUnion α) (hAB : A.toSet ⊆ B.toSet)
    (hApos : ∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ A.toSet}).toReal)
    (hBpos : ∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ B.toSet}).toReal)
    (hArate : Tendsto
      (fun x => Real.log ((P {ω | paths x ω ∈ A.toSet}).toReal) / g x)
      l (𝓝 (κ * A.realEnergy)))
    (hBrate : Tendsto
      (fun x => Real.log ((P {ω | paths x ω ∈ B.toSet}).toReal) / g x)
      l (𝓝 (κ * B.realEnergy))) :
    B.realEnergy ≤ A.realEnergy := by
  have hAfinite (x : I) : P {ω | paths x ω ∈ A.toSet} ≠ ⊤ := by
    apply ne_of_lt
    calc
      P {ω | paths x ω ∈ A.toSet} ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hBfinite (x : I) : P {ω | paths x ω ∈ B.toSet} ≠ ⊤ := by
    apply ne_of_lt
    calc
      P {ω | paths x ω ∈ B.toSet} ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hneg : ∀ᶠ x in l, g x < 0 := hg.eventually (eventually_lt_atBot 0)
  have hratio :
      (fun x => Real.log ((P {ω | paths x ω ∈ B.toSet}).toReal) / g x) ≤ᶠ[l]
      (fun x => Real.log ((P {ω | paths x ω ∈ A.toSet}).toReal) / g x) := by
    filter_upwards [hApos, hBpos, hneg] with x hAx hBx hgx
    have hmeasure : P {ω | paths x ω ∈ A.toSet} ≤
        P {ω | paths x ω ∈ B.toSet} :=
      measure_mono (fun ω hω => hAB hω)
    have hreal := ENNReal.toReal_mono (hBfinite x) hmeasure
    have hlog := Real.log_le_log hAx hreal
    exact (div_le_div_right_of_neg hgx).2 hlog
  have hlim := le_of_tendsto_of_tendsto hBrate hArate hratio
  nlinarith [hκ]

/-- Cross-order of all inner and outer `M₃` energies, together with the
vanishing energy gap, implies existence of their common limit. -/
noncomputable def FiniteCorridorUnionApproximation.energyLimits_of_crossOrder
    {α : ℝ} {G : Set (CadlagPath unitInterval ℝ)}
    (A : FiniteCorridorUnionApproximation α G)
    (hcross : ∀ n m, FiniteCorridorUnion.realEnergy (A.outer m) ≤ FiniteCorridorUnion.realEnergy (A.inner n)) :
    FiniteCorridorUnionEnergyLimits A := by
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
  let hExists : ∃ L, Tendsto innerCost atTop (𝓝 L) :=
    cauchySeq_tendsto_of_complete hCauchy
  exact FiniteCorridorUnionEnergyLimits.ofInnerTendsto (L := hExists.choose)
    (by simpa [innerCost] using hExists.choose_spec)

/-- The `M₃` probability rates order every inner/outer energy pair, so the
vanishing gap gives a common energy limit for an `M` approximation. -/
noncomputable def FiniteCorridorUnionApproximation.energyLimits_of_probabilityRate
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
    FiniteCorridorUnionEnergyLimits A :=
  FiniteCorridorUnionApproximation.energyLimits_of_crossOrder A (by
    intro n m
    exact FiniteCorridorUnion.realEnergy_antitone_of_subset_of_probabilityRate P paths g hg hκ
      (A.inner n) (A.outer m)
      (fun f hf => A.subset_outer m (A.inner_subset n hf))
      (hFiniteUnionRate (A.inner n)).2.1 (hFiniteUnionRate (A.outer m)).2.1
      (hFiniteUnionRate (A.inner n)).2.2 (hFiniteUnionRate (A.outer m)).2.2)

/-- The limiting `M₃` energy is independent of the chosen inner/outer
approximation, once the component probability rates are available. -/
theorem FiniteCorridorUnionEnergyLimits.commonEnergy_eq_of_approximation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)}
    (A B : FiniteCorridorUnionApproximation α G)
    (hA : FiniteCorridorUnionEnergyLimits A) (hB : FiniteCorridorUnionEnergyLimits B)
    (hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ x, NullMeasurableSet {ω | paths x ω ∈ C.toSet} P) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * C.realEnergy))) :
    hA.commonEnergy = hB.commonEnergy := by
  have hBouter_le_Ainner (n : ℕ) :
      FiniteCorridorUnion.realEnergy (B.outer n) ≤ FiniteCorridorUnion.realEnergy (A.inner n) :=
    FiniteCorridorUnion.realEnergy_antitone_of_subset_of_probabilityRate P paths g hg hκ
      (A.inner n) (B.outer n)
      (fun f hf => B.subset_outer n (A.inner_subset n hf))
      (hFiniteUnionRate (A.inner n)).2.1 (hFiniteUnionRate (B.outer n)).2.1
      (hFiniteUnionRate (A.inner n)).2.2 (hFiniteUnionRate (B.outer n)).2.2
  have hAouter_le_Binner (n : ℕ) :
      FiniteCorridorUnion.realEnergy (A.outer n) ≤ FiniteCorridorUnion.realEnergy (B.inner n) :=
    FiniteCorridorUnion.realEnergy_antitone_of_subset_of_probabilityRate P paths g hg hκ
      (B.inner n) (A.outer n)
      (fun f hf => A.subset_outer n (B.inner_subset n hf))
      (hFiniteUnionRate (B.inner n)).2.1 (hFiniteUnionRate (A.outer n)).2.1
      (hFiniteUnionRate (B.inner n)).2.2 (hFiniteUnionRate (A.outer n)).2.2
  have hB_le_A : hB.outerLimit ≤ hA.innerLimit :=
    le_of_tendsto_of_tendsto hB.outer_tendsto hA.inner_tendsto
      (Filter.Eventually.of_forall hBouter_le_Ainner)
  have hA_le_B : hA.outerLimit ≤ hB.innerLimit :=
    le_of_tendsto_of_tendsto hA.outer_tendsto hB.inner_tendsto
      (Filter.Eventually.of_forall hAouter_le_Binner)
  have hAeq := hA.innerLimit_eq_outerLimit
  have hBeq := hB.innerLimit_eq_outerLimit
  change hA.innerLimit = hB.innerLimit
  linarith

/-- The process version of Mogul'skii's theorem for class `M`, assembled from
null-measurable `M₃` rates. The finite-union adapter derives those rates from
component `M₂` rates without requiring Borel measurability of the exact strict
corridor events. -/
theorem tendsto_log_probability_ratio_of_FiniteCorridorUnionApproximation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)}
    (A : FiniteCorridorUnionApproximation α G)
    (hGnullMeasurable : ∀ x, NullMeasurableSet {ω | paths x ω ∈ G} P)
    (hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ x, NullMeasurableSet {ω | paths x ω ∈ C.toSet} P) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * C.realEnergy))) :
    (∀ x, NullMeasurableSet {ω | paths x ω ∈ G} P) ∧
    ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x)
        l (𝓝 (κ * hLimits.commonEnergy)) := by
  let hLimits : FiniteCorridorUnionEnergyLimits A :=
    FiniteCorridorUnionApproximation.energyLimits_of_probabilityRate P paths g hg hκ A hFiniteUnionRate
  have hneg : ∀ᶠ x in l, g x < 0 := hg.eventually (eventually_lt_atBot 0)
  have hGfinite (x : I) : P {ω | paths x ω ∈ G} ≠ ⊤ := by
    apply ne_of_lt
    calc
      P {ω | paths x ω ∈ G} ≤ P Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hOuterFinite (n : ℕ) (x : I) :
      P {ω | paths x ω ∈ (FiniteCorridorUnion.toSet (A.outer n))} ≠ ⊤ := by
    apply ne_of_lt
    calc
      P {ω | paths x ω ∈ (FiniteCorridorUnion.toSet (A.outer n))} ≤ P Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
      _ < ⊤ := ENNReal.one_lt_top
  have hGpos : ∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ G}).toReal := by
    filter_upwards [(hFiniteUnionRate (A.inner 0)).2.1] with x hx
    have hmeasure : P {ω | paths x ω ∈ (FiniteCorridorUnion.toSet (A.inner 0))} ≤
        P {ω | paths x ω ∈ G} :=
      measure_mono (fun ω hω => A.inner_subset 0 hω)
    have hreal := ENNReal.toReal_mono (hGfinite x) hmeasure
    exact lt_of_lt_of_le (by simpa using hx) hreal
  refine ⟨hGnullMeasurable, hLimits, ?_⟩
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro y hy
    have houterLimit : Tendsto
        (fun n => κ * FiniteCorridorUnion.realEnergy (A.outer n)) atTop
        (𝓝 (κ * hLimits.commonEnergy)) := by
      have heq : hLimits.outerLimit = hLimits.commonEnergy :=
        hLimits.commonEnergy_eq_outerLimit.symm
      simpa [FiniteCorridorUnionEnergyLimits.commonEnergy, heq] using
        (tendsto_const_nhds.mul hLimits.outer_tendsto)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
      houterLimit.eventually (Ioi_mem_nhds hy)
    let n := N
    have hn : y < κ * FiniteCorridorUnion.realEnergy (A.outer n) := hN n le_rfl
    obtain ⟨_, _, hRate⟩ := hFiniteUnionRate (A.outer n)
    have hRateEventually := hRate.eventually (Ioi_mem_nhds hn)
    have hbound : ∀ᶠ x in l,
        Real.log ((P {ω | paths x ω ∈ (FiniteCorridorUnion.toSet (A.outer n))}).toReal) / g x ≤
          Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x := by
      filter_upwards [hGpos, (hFiniteUnionRate (A.outer n)).2.1, hneg] with x hpx hox hgx
      have hmeasure : P {ω | paths x ω ∈ G} ≤
          P {ω | paths x ω ∈ (FiniteCorridorUnion.toSet (A.outer n))} :=
        measure_mono (fun ω hω => A.subset_outer n hω)
      have hreal := ENNReal.toReal_mono (hOuterFinite n x) hmeasure
      have hlog := Real.log_le_log hpx hreal
      exact (div_le_div_right_of_neg hgx).2 hlog
    filter_upwards [hRateEventually, hbound] with x hx hxy
    exact lt_of_lt_of_le hx hxy
  · intro y hy
    have hinnerLimit : Tendsto
        (fun n => κ * FiniteCorridorUnion.realEnergy (A.inner n)) atTop
        (𝓝 (κ * hLimits.commonEnergy)) := by
      simpa [FiniteCorridorUnionEnergyLimits.commonEnergy] using
        (tendsto_const_nhds.mul hLimits.inner_tendsto)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 <|
      hinnerLimit.eventually (Iio_mem_nhds hy)
    let n := N
    have hn : κ * FiniteCorridorUnion.realEnergy (A.inner n) < y := hN n le_rfl
    obtain ⟨_, _, hRate⟩ := hFiniteUnionRate (A.inner n)
    have hRateEventually := hRate.eventually (Iio_mem_nhds hn)
    have hbound : ∀ᶠ x in l,
        Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x ≤
          Real.log ((P {ω | paths x ω ∈ (FiniteCorridorUnion.toSet (A.inner n))}).toReal) / g x := by
      filter_upwards [hGpos, (hFiniteUnionRate (A.inner n)).2.1, hneg] with x hpx hix hgx
      have hmeasure : P {ω | paths x ω ∈ (FiniteCorridorUnion.toSet (A.inner n))} ≤
          P {ω | paths x ω ∈ G} :=
        measure_mono (fun ω hω => A.inner_subset n hω)
      have hreal := ENNReal.toReal_mono (hGfinite x) hmeasure
      have hlog := Real.log_le_log hix hreal
      exact (div_le_div_right_of_neg hgx).2 hlog
    filter_upwards [hRateEventually, hbound] with x hx hxy
    exact lt_of_le_of_lt hxy hx

/-- The limiting energy attached to a set in class `M` is independent of the
chosen approximation witness, provided the component `M₃` probability rates
hold.  This is the probabilistic well-definedness assertion in the source. -/
theorem existsUnique_commonEnergy_of_hasVanishingEnergyGapApproximation
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
    ∃! H : ℝ, ∃ A : FiniteCorridorUnionApproximation α G,
      ∃ hLimits : FiniteCorridorUnionEnergyLimits A, H = hLimits.commonEnergy := by
  obtain ⟨A⟩ := hG
  let hLimits : FiniteCorridorUnionEnergyLimits A :=
    FiniteCorridorUnionApproximation.energyLimits_of_probabilityRate P paths g hg hκ A hFiniteUnionRate
  refine ⟨hLimits.commonEnergy, ⟨A, hLimits, rfl⟩, ?_⟩
  intro H hH
  obtain ⟨B, hB, hEq⟩ := hH
  have hEqAB := FiniteCorridorUnionEnergyLimits.commonEnergy_eq_of_approximation P paths g hg hκ
    A B hLimits hB hFiniteUnionRate
  calc
    H = hB.commonEnergy := hEq
    _ = hLimits.commonEnergy := hEqAB.symm

/-- Process Theorem 2 for a set in class `M`, conditional on null-measurable
`M₃` rates. The result includes the unique approximation-independent energy
value. -/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G)
    (hGnullMeasurable : ∀ x, NullMeasurableSet {ω | paths x ω ∈ G} P)
    (hFiniteUnionRate : ∀ C : FiniteCorridorUnion α,
      (∀ x, NullMeasurableSet {ω | paths x ω ∈ C.toSet} P) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * C.realEnergy))) :
    (∀ x, NullMeasurableSet {ω | paths x ω ∈ G} P) ∧
      ∃! H : ℝ,
        (∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy) ∧
        Tendsto
          (fun x => Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x)
          l (𝓝 (κ * H)) := by
  have hUnique := existsUnique_commonEnergy_of_hasVanishingEnergyGapApproximation P paths g hg hκ hG hFiniteUnionRate
  obtain ⟨A⟩ := hG
  obtain ⟨hmeas, hLimits, hRate⟩ :=
    tendsto_log_probability_ratio_of_FiniteCorridorUnionApproximation P paths g hg hκ
      A hGnullMeasurable hFiniteUnionRate
  refine ⟨hmeas, ?_⟩
  refine ⟨hLimits.commonEnergy, ?_, ?_⟩
  · exact ⟨⟨A, hLimits, rfl⟩, hRate⟩
  · intro H hH
    have hEq := hUnique.unique hH.1 ⟨A, hLimits, rfl⟩
    rw [← hEq]

/-- Theorem 2 for class `M`, with the probabilistic input stated at the
source's single-corridor `M₂` level. Finite unions are handled here by the
null-measurable `M₃` rate lemma, and the approximation squeeze gives the rate
for `G`. The exact `M₂` corridor null-measurability and rate remain explicit
hypotheses. -/
theorem tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation_of_stepCorridorRates
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {α κ : ℝ} {I : Type*} {l : Filter I} [NeBot l]
    (paths : I → Ω → CadlagPath unitInterval ℝ) (g : I → ℝ)
    (hg : Tendsto g l atBot) (hκ : 0 < κ)
    {G : Set (CadlagPath unitInterval ℝ)} (hG : HasVanishingEnergyGapApproximation α G)
    (hGnullMeasurable : ∀ x, NullMeasurableSet {ω | paths x ω ∈ G} P)
    (hStepCorridorRate : ∀ C : ContinuousAdmissibleStepCorridor,
      (∀ x, NullMeasurableSet {ω | paths x ω ∈ C.toSet} P) ∧
      (∀ᶠ x in l, 0 < (P {ω | paths x ω ∈ C.toSet}).toReal) ∧
      Tendsto
        (fun x => Real.log ((P {ω | paths x ω ∈ C.toSet}).toReal) / g x)
        l (𝓝 (κ * (ContinuousAdmissibleStepCorridor.energy α C).toReal))) :
    (∀ x, NullMeasurableSet {ω | paths x ω ∈ G} P) ∧
      ∃! H : ℝ,
        (∃ A : FiniteCorridorUnionApproximation α G, ∃ hLimits : FiniteCorridorUnionEnergyLimits A,
          H = hLimits.commonEnergy) ∧
        Tendsto
          (fun x => Real.log ((P {ω | paths x ω ∈ G}).toReal) / g x)
          l (𝓝 (κ * H)) := by
  apply tendsto_log_probability_ratio_of_hasVanishingEnergyGapApproximation P paths g hg hκ hG hGnullMeasurable
  intro C
  have h := tendsto_log_finiteCorridorUnion_preimage_probability_ratio_of_nullMeasurable P C paths g hg hκ
    (fun x i => (hStepCorridorRate (C.pieces i)).1 x)
    (fun i => (hStepCorridorRate (C.pieces i)).2.1)
    (fun i => by
      simpa [FiniteCorridorUnion.realEnergy] using (hStepCorridorRate (C.pieces i)).2.2)
  exact h

end ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability

end
