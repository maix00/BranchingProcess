/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Combinatorics.BranchingWalk.Step.Measure.PointMeasure
public import Probability.BranchingProcess.Offspring.PointMeasure

/-!
# Offspring-count laws

Child counts are the `ℕ∞` projection of a complete offspring configuration.
For countable slot types, their law is a pushforward of the configuration
law. Taking total mass after the point-measure projection gives the same law,
after the canonical embedding of `ℕ∞` into `ℝ≥0∞`.

The public declarations are:

- `ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.childCountLaw`:
  the law of $\operatorname{childCount}(\xi)$ for an offspring configuration
  $\xi$ sampled from the configuration law.
- `ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.childCountLaw_toMeasure`:
  the child-count law as the pushforward of the configuration measure.
- `ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.childCountLaw_mapMarks`:
  mapping child marks by a measurable map leaves the child-count law unchanged.
- `ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.pointMeasureLaw_totalMass`:
  the pushforward of the point-measure law by total mass equals the
  pushforward of the child-count law into $\mathbb R_{\ge0}^\infty$.
- `ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.expectedChildCount`:
  $\mathbb E[\operatorname{childCount}(\xi)]$, allowed to equal $\infty$.
- `ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.HasAtLeastOneChild`:
  the offspring configuration is nonempty with probability one.
- `ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical`:
  the expected extended child count is greater than one.
- `ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.hasAtLeastOneChild_ae`:
  a mass-one nonempty-support condition implies nonempty support almost surely.
- `ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.expectedChildCount_eq_lintegral_pointMeasureLaw_totalMass`:
  expected child count equals the expected total mass of the point-measure law.
- `ProbabilityTheory.BranchingProcess.Offspring.offspringSplitSet`:
  the set $\{\xi:2\le\operatorname{childCount}(\xi)\}$ of offspring
  configurations with at least two children.
- `ProbabilityTheory.BranchingProcess.Offspring.offspringSplitSet_eq_nontrivialSupport`:
  this set is the event that the offspring support contains at least two slots.
- `ProbabilityTheory.BranchingProcess.Offspring.measurableSet_offspringSplitSet`:
  for countable offspring slots and a measurable mark space, measurability of
  the offspring-splitting event.
- `ProbabilityTheory.BranchingProcess.Offspring.measure_pos_childCount_ge_two_of_expectedChildCount_gt_one`:
  for an offspring-step probability law with expected child count greater
  than one, $\mu(\operatorname{offspringSplitSet})>0$.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw

open MeasureTheory
open scoped ENNReal

/-- The law of the possibly infinite number of children in an offspring
configuration. -/
noncomputable def childCountLaw {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    ProbabilityMeasure ℕ∞ :=
  μ.map Combinatorics.Branching.Step.childCount

@[simp] theorem childCountLaw_toMeasure {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    (μ.childCountLaw : Measure ℕ∞) =
      (μ : Measure (Combinatorics.Branching.Step ι Mark)).map
        Combinatorics.Branching.Step.childCount := rfl

/-- Child-count laws are unchanged when child marks are mapped. -/
theorem childCountLaw_mapMarks {ι Mark Mark' : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (f : Mark → Mark') (hf : Measurable f) :
    (μ.mapMarks f hf).childCountLaw = μ.childCountLaw := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [childCountLaw_toMeasure, mapMarks_toMeasure]
  rw [Measure.map_map Combinatorics.Branching.Step.childCount_measurable
    (Combinatorics.Branching.Step.map_measurable hf)]
  congr 1
  funext ξ
  simp

/-- Total mass of the point-measure law is the child-count law mapped into
`ℝ≥0∞`. -/
theorem pointMeasureLaw_totalMass {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    μ.pointMeasureLaw.map (fun η : Measure Mark => η Set.univ) =
      μ.childCountLaw.map (fun n : ℕ∞ => (n : ℝ≥0∞)) := by
  have htotal : Measurable (fun η : Measure Mark => η Set.univ) :=
    Measure.measurable_coe MeasurableSet.univ
  have hcast : Measurable (fun n : ℕ∞ => (n : ℝ≥0∞)) := by
    fun_prop
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, pointMeasureLaw_toMeasure,
    childCountLaw_toMeasure]
  rw [Measure.map_map htotal Combinatorics.Branching.stepPointMeasure_measurable,
    Measure.map_map hcast Combinatorics.Branching.Step.childCount_measurable]
  congr 1
  funext ξ
  exact Combinatorics.Branching.stepPointMeasure_univ ξ

/-- The expected extended child count under an offspring configuration law.
The value may be infinite; no finiteness assumption is built in. -/
noncomputable def expectedChildCount {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    ℝ≥0∞ :=
  ∫⁻ n : ℕ∞, (n : ℝ≥0∞) ∂μ.childCountLaw

/-- An offspring configuration law has at least one child almost surely. -/
def HasAtLeastOneChild {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    Prop :=
  (μ : Measure (Combinatorics.Branching.Step ι Mark))
    Combinatorics.Branching.nonemptySupport = 1

/-- The offspring law is supercritical when its expected extended child count
is greater than one. -/
def IsSupercritical {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    Prop :=
  1 < μ.expectedChildCount

/-- A mass-one nonempty event gives an almost-surely nonempty configuration. -/
theorem hasAtLeastOneChild_ae {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (h : μ.HasAtLeastOneChild) :
    ∀ᵐ ξ ∂(μ : Measure (Combinatorics.Branching.Step ι Mark)),
      ξ ∈ Combinatorics.Branching.nonemptySupport := by
  exact (ae_mem_iff_measure_eq
    Combinatorics.Branching.nonemptySupport_measurable.nullMeasurableSet).2
      (by simpa [HasAtLeastOneChild] using h)

/-- Expected child count can equivalently be computed as the expected total
mass of the offspring point-measure law. -/
theorem expectedChildCount_eq_lintegral_pointMeasureLaw_totalMass
    {ι Mark : Type*} [Countable ι] [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    μ.expectedChildCount =
      ∫⁻ η : Measure Mark, η Set.univ ∂μ.pointMeasureLaw := by
  have hcast : Measurable (fun n : ℕ∞ => (n : ℝ≥0∞)) := by
    fun_prop
  have htotal : Measurable (fun η : Measure Mark => η Set.univ) :=
    Measure.measurable_coe MeasurableSet.univ
  calc
    μ.expectedChildCount =
        ∫⁻ z : ℝ≥0∞, z ∂μ.childCountLaw.map
          (fun n : ℕ∞ => (n : ℝ≥0∞)) := by
      rw [expectedChildCount]
      exact (lintegral_map measurable_id hcast).symm
    _ = ∫⁻ η : Measure Mark, η Set.univ ∂μ.pointMeasureLaw := by
      rw [← pointMeasureLaw_totalMass]
      exact lintegral_map measurable_id htotal

end ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw

namespace ProbabilityTheory.BranchingProcess.Offspring

open MeasureTheory
open Combinatorics.Branching
open scoped ENNReal

/-! ### Splitting configurations -/

/-- The offspring configurations containing at least two children. -/
def offspringSplitSet {ι X : Type*} : Set (Step ι X) :=
  {ξ | 2 ≤ Step.childCount ξ}

/-- An offspring configuration splits exactly when its support has at least
two slots. -/
theorem offspringSplitSet_eq_nontrivialSupport {ι X : Type*} :
    offspringSplitSet (ι := ι) (X := X) = nontrivialSupport := by
  ext ξ
  change 2 ≤ (support ξ).encard ↔
    ∃ i j, i ≠ j ∧ survive ξ i ∧ survive ξ j
  constructor
  · intro hcount
    have hcard : 1 < (support ξ).encard :=
      lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 2) hcount
    obtain ⟨i, j, hi, hj, hij⟩ := Set.one_lt_encard_iff.mp hcard
    exact ⟨i, j, hij, by simpa [support] using hi,
      by simpa [support] using hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    have hcard : 1 < (support ξ).encard :=
      Set.one_lt_encard_iff.mpr
        ⟨i, j, by simpa [support] using hi,
          by simpa [support] using hj, hij⟩
    cases hencard : (support ξ).encard with
    | top => simp
    | coe n =>
      have hn : 1 < n := by simpa [hencard] using hcard
      have hn' : 2 ≤ n := by omega
      simpa [hencard] using hn'

/-- Measurability of the event that an offspring configuration has at least
two children. -/
theorem measurableSet_offspringSplitSet {ι X : Type*} [Countable ι]
    [MeasurableSpace X] :
    MeasurableSet (offspringSplitSet (ι := ι) (X := X)) := by
  rw [offspringSplitSet_eq_nontrivialSupport]
  exact nontrivialSupport_measurable

private lemma childCount_le_one_of_not_split
    {ι X : Type*} (ξ : Step ι X)
    (hnoSplit : ¬ 2 ≤ Step.childCount ξ) : Step.childCount ξ ≤ 1 := by
  cases hcount : Step.childCount ξ with
  | top => exact (hnoSplit (by simp [hcount])).elim
  | coe n =>
    have hnnot : ¬ 2 ≤ n := by simpa [hcount] using hnoSplit
    have hn : n ≤ 1 := by omega
    simpa [hcount] using hn

/-- A probability law on offspring configurations with mean child count
greater than one assigns positive mass to configurations with at least two
children. -/
theorem measure_pos_childCount_ge_two_of_expectedChildCount_gt_one
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) :
    0 < μ (offspringSplitSet (ι := ι) (X := X)) := by
  by_contra hpos
  have hzero : μ (offspringSplitSet (ι := ι) (X := X)) = 0 :=
    nonpos_iff_eq_zero.mp (le_of_not_gt hpos)
  have haeNotSplit : ∀ᵐ ξ ∂μ,
      ξ ∉ offspringSplitSet (ι := ι) (X := X) := by
    simpa only [Set.mem_ofPred_eq] using
      (measure_eq_zero_iff_ae_notMem.mp hzero)
  have haeCountLeOne : ∀ᵐ ξ ∂μ,
      (Step.childCount ξ : ℝ≥0∞) ≤ 1 := by
    filter_upwards [haeNotSplit] with ξ hξ
    exact_mod_cast childCount_le_one_of_not_split ξ hξ
  have hle : (∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) ≤ 1 := by
    calc
      (∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) ≤
          ∫⁻ _ξ, (1 : ℝ≥0∞) ∂μ := lintegral_mono_ae haeCountLeOne
      _ = 1 := by simp
  exact (not_lt_of_ge hle) hsupercritical

end ProbabilityTheory.BranchingProcess.Offspring

end
