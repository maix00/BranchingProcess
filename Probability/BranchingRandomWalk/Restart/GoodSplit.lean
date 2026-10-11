/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Assumptions.Structural
import Probability.BranchingProcess.Offspring.Count
import Probability.BranchingRandomWalk.Step.OrderingLaw
import Probability.BranchingRandomWalk.Restart.FirstSplit
import Combinatorics.BranchingWalk.Step.SlotSelection
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.FirstN
import Probability.BranchingRandomWalk.Population.Processes.StepSelection.Filter

/-!
# Positive-probability bounded splits

The basic offspring assumptions imply that a raw offspring configuration
contains at least two children with positive probability. For a finite
selection that retains two children whenever they are available, the second
selected child's real potential can then be bounded by some finite integer
cutoff while preserving positive probability. This is the input used to
construct a reserve selector that always retains the first child and retains
the second below that cutoff.
-/

open MeasureTheory
open scoped ENNReal

section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching
open ProbabilityTheory.BranchingProcess

/-- The intrinsic first-two slot selection is measurable. Its labels are
chosen by the abstract slot order, without assuming that particular labels
are realized children. -/
theorem firstTwoBySlotOrder_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] :
    Measurable
      (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2).select := by
  apply StepSelection.firstNBy_measurable 2
    (fun (_ : Step α X) (i : α) => i)
    (fun ξ => Step.FiniteSelection.admitsFirstNBySlotOrder 2 ξ)
  intro p q
  exact measurable_const

/-- Keep only the first member of an arbitrary finite child selection. -/
noncomputable def firstOnlySelectedChild {α X : Type*} [LinearOrder α]
    [OrderBot α] (R : Step.FiniteSelection α X) :
    Step.FiniteSelection α X :=
  R.filter fun ξ i => i = firstSelectedSlot R ξ

/-- The thesis reserve rule: retain the first selected child whenever it
exists, and retain any other selected child only when its potential is below
the cutoff. When `R` has capacity two, this is the first child plus the
bounded second child. -/
noncomputable def reserveSelectionBelowPotential
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (M : ℝ) :
    Step.FiniteSelection α X where
  select ξ :=
    firstOnlySelectedChild R ξ ∪ (R.belowPotential φ M) ξ
  subset_support ξ i hi := by
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (firstOnlySelectedChild R).subset_support ξ i hi
    · exact (R.belowPotential φ M).subset_support ξ i hi

theorem reserveSelectionBelowPotential_subset
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (M : ℝ)
    (ξ : Step α X) :
    reserveSelectionBelowPotential R φ M ξ ⊆ R ξ := by
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact (Step.FiniteSelection.mem_filter R
      (fun ξ i => i = firstSelectedSlot R ξ) ξ i).mp hi |>.1
  · exact (Step.FiniteSelection.mem_filter R
      (fun ξ i => ξ.potentialValue' φ i ≤ M) ξ i).mp (by
        simpa [Step.FiniteSelection.belowPotential] using hi) |>.1

theorem reserveSelectionBelowPotential_isBoundedBy
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (M : ℝ)
    {N : ℕ} (hR : R.IsBoundedBy N) :
    (reserveSelectionBelowPotential R φ M).IsBoundedBy N := by
  intro ξ
  exact (Finset.card_le_card
    (reserveSelectionBelowPotential_subset R φ M ξ)).trans (hR ξ)

theorem firstOnlySelectedChild_nonempty_of_selected_nonempty
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hne : (R ξ).Nonempty) :
    (firstOnlySelectedChild R ξ).Nonempty := by
  have hfirst := firstSelectedSlot_mem R ξ hne
  refine ⟨firstSelectedSlot R ξ, ?_⟩
  rw [firstOnlySelectedChild, Step.FiniteSelection.mem_filter]
  exact ⟨hfirst, rfl⟩

theorem reserveSelectionBelowPotential_nonempty_of_selected_nonempty
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (M : ℝ)
    (ξ : Step α X) (hne : (R ξ).Nonempty) :
    (reserveSelectionBelowPotential R φ M ξ).Nonempty := by
  obtain ⟨i, hi⟩ := firstOnlySelectedChild_nonempty_of_selected_nonempty
    R ξ hne
  exact ⟨i, Finset.mem_union.mpr (Or.inl hi)⟩

theorem reserveSelectionBelowPotential_split_of_boundedSecond
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (M : ℝ)
    (ξ : Step α X) (hcard : 2 ≤ (R ξ).card)
    (hbound : ξ.potentialValue' φ (secondSelectedSlot R ξ) ≤ M) :
    2 ≤ (reserveSelectionBelowPotential R φ M ξ).card := by
  have hslots := secondSelectedSlot_mem_of_card R ξ hcard
  have hfirst : firstSelectedSlot R ξ ∈ R ξ :=
    firstSelectedSlot_mem R ξ (Finset.card_pos.mp (by omega))
  have hfirstOnly : firstSelectedSlot R ξ ∈ firstOnlySelectedChild R ξ := by
    rw [firstOnlySelectedChild, Step.FiniteSelection.mem_filter]
    exact ⟨hfirst, rfl⟩
  have hsecondBelow : secondSelectedSlot R ξ ∈ (R.belowPotential φ M) ξ := by
    simp [Step.FiniteSelection.belowPotential,
      Step.FiniteSelection.mem_filter, hslots.1, hbound]
  have hfirstReserve : firstSelectedSlot R ξ ∈
      reserveSelectionBelowPotential R φ M ξ :=
    Finset.mem_union.mpr (Or.inl hfirstOnly)
  have hsecondReserve : secondSelectedSlot R ξ ∈
      reserveSelectionBelowPotential R φ M ξ :=
    Finset.mem_union.mpr (Or.inr hsecondBelow)
  have hlt : 1 < (reserveSelectionBelowPotential R φ M ξ).card :=
    Finset.one_lt_card_iff.mpr
      ⟨firstSelectedSlot R ξ, secondSelectedSlot R ξ,
        hfirstReserve, hsecondReserve, hslots.2⟩
  omega

/-- The second selected slot lies strictly after the first in the abstract
slot order. -/
theorem firstSelectedSlot_lt_second_of_card
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hcard : 2 ≤ (R ξ).card) :
    firstSelectedSlot R ξ < secondSelectedSlot R ξ := by
  have hslots := secondSelectedSlot_mem_of_card R ξ hcard
  have hnonempty : (R ξ).Nonempty := Finset.card_pos.mp (by omega)
  have hfirst : firstSelectedSlot R ξ = (R ξ).min' hnonempty := by
    simp [firstSelectedSlot, hnonempty]
  have hle : (R ξ).min' hnonempty ≤ secondSelectedSlot R ξ :=
    Finset.min'_le _ _ hslots.1
  have hle' : firstSelectedSlot R ξ ≤ secondSelectedSlot R ξ := by
    rw [hfirst]
    exact hle
  exact lt_of_le_of_ne hle' hslots.2

/-- On an ordered realization, the first two selected slots are also
nondecreasing in potential. Thus `secondSelectedSlot` in the cutoff event is
the second child in the left-to-right potential ordering. -/
theorem potentialValue'_firstSelectedSlot_le_second_of_ordered
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (φ : Potential X) (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hordered : ξ.IsOrderedBy φ) (hcard : 2 ≤ (R ξ).card) :
    ξ.potentialValue' φ (firstSelectedSlot R ξ) ≤
      ξ.potentialValue' φ (secondSelectedSlot R ξ) := by
  have hsecond := secondSelectedSlot_mem_of_card R ξ hcard
  have hsurvive : survive (ξ.map φ) (secondSelectedSlot R ξ) :=
    (survive_map_iff φ ξ _).2 (R.mem_support ξ hsecond.1)
  have hmono := orderedSteps_value_mono (ξ.map φ) hordered
    (firstSelectedSlot_lt_second_of_card R ξ hcard).le hsurvive
  simpa [Step.potentialValue', Step.potentialAt?, Step.map, value'] using hmono

theorem firstOnlySelectedChild_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) :
    Measurable (firstOnlySelectedChild R).select := by
  apply StepSelection.filter_measurable R hR
    (fun ξ i => i = firstSelectedSlot R ξ)
  intro i
  have hfirst := firstSelectedSlot_measurable R hR
  have hset : {ξ : Step α X | i = firstSelectedSlot R ξ} =
      (firstSelectedSlot R) ⁻¹' ({i} : Set α) := by
    ext ξ
    simp [eq_comm]
  apply measurableSet_setOfPred.mp
  rw [hset]
  exact hfirst (measurableSet_singleton i)

theorem reserveSelectionBelowPotential_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (φ : Potential X) (M : ℝ) :
    Measurable (reserveSelectionBelowPotential R φ M).select := by
  let first := firstOnlySelectedChild R
  let bounded := R.belowPotential φ M
  have hfirst : Measurable first.select := by
    simpa [first] using firstOnlySelectedChild_measurable R hR
  have hbounded : Measurable bounded.select := by
    simpa [bounded] using StepSelection.belowPotential_measurable R hR φ M
  have hunion : Measurable (fun p : Finset α × Finset α => p.1 ∪ p.2) :=
    measurable_of_countable _
  have h := hunion.comp (hfirst.prodMk hbounded)
  simpa [Function.comp_def, reserveSelectionBelowPotential, first, bounded] using h

/-- Raw offspring configurations containing at least two children. -/
def rawSplitEvent {ι X : Type*} (ξ : Step ι X) : Prop :=
  2 ≤ ξ.childCount

theorem rawSplitEvent_measurable {ι X : Type*} [Countable ι]
    [MeasurableSpace X] :
    MeasurableSet {ξ : Step ι X | rawSplitEvent ξ} := by
  have heq : {ξ : Step ι X | rawSplitEvent ξ} =
      nontrivialSupport := by
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
    · intro hsplit
      have hcard : 1 < (support ξ).encard :=
        Set.one_lt_encard_iff.mpr (by
          obtain ⟨i, j, hij, hi, hj⟩ := hsplit
          exact ⟨i, j, by simpa [support] using hi,
            by simpa [support] using hj, hij⟩)
      cases hencard : (support ξ).encard with
      | top => simp [hencard]
      | coe n =>
          have hn : 1 < n := by simpa [hencard] using hcard
          have hn' : 2 ≤ n := by omega
          simpa [hencard] using hn'
  rw [heq]
  exact nontrivialSupport_measurable

private theorem childCount_eq_one_of_nonempty_not_split
    {ι X : Type*} (ξ : Step ι X)
    (hne : ξ ∈ nonemptySupport)
    (hsplit : ¬ rawSplitEvent ξ) :
    ξ.childCount = 1 := by
  obtain ⟨i, hi⟩ := hne
  have hpos : 0 < ξ.childCount := by
    change 0 < (support ξ).encard
    exact Set.encard_pos.mpr ⟨i, hi⟩
  cases hcount : ξ.childCount with
  | top =>
      simp [rawSplitEvent, hcount] at hsplit
  | coe n =>
      have hnpos : 0 < n := by simpa [hcount] using hpos
      have hnnot : ¬ 2 ≤ n := by simpa [rawSplitEvent, hcount] using hsplit
      have hn : n = 1 := by omega
      simp [hcount, hn]

/-- If an offspring law is nonempty almost surely and has mean strictly
larger than one, then the event of at least two children has positive mass.
The conclusion concerns the complete raw configuration and does not depend on
any particular child slots or their marks. -/
theorem rawSplitEvent_measure_pos
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (hsupercritical : OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X)) :
    0 < L.raw {ξ | rawSplitEvent ξ} := by
  by_contra hpos
  have hzero : L.raw {ξ | rawSplitEvent ξ} = 0 :=
    nonpos_iff_eq_zero.mp (le_of_not_gt hpos)
  have haeNonempty : ∀ᵐ ξ ∂L.raw, ξ ∈ nonemptySupport :=
    OffspringConfigurationLaw.hasAtLeastOneChild_ae
      ⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ hnonempty
  have haeNotSplit : ∀ᵐ ξ ∂L.raw, ¬ rawSplitEvent ξ := by
    simpa only [Set.mem_setOf_eq] using
      (measure_eq_zero_iff_ae_notMem (μ := L.raw)
        (s := {ξ | rawSplitEvent ξ})).mp hzero
  have haeCount : ∀ᵐ ξ ∂L.raw, ξ.childCount = 1 := by
    filter_upwards [haeNonempty, haeNotSplit] with ξ hne hsplit
    exact childCount_eq_one_of_nonempty_not_split ξ hne hsplit
  have hrawIntegral :
      (∫⁻ ξ, (ξ.childCount : ℝ≥0∞) ∂L.raw) = 1 := by
    calc
      (∫⁻ ξ, (ξ.childCount : ℝ≥0∞) ∂L.raw) =
          ∫⁻ ξ, (1 : ℝ≥0∞) ∂L.raw := by
        apply lintegral_congr_ae
        filter_upwards [haeCount] with ξ hξ
        simp [hξ]
      _ = 1 := by simp
  have hexpectation :
      OffspringConfigurationLaw.expectedChildCount
          (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ :
            OffspringConfigurationLaw ι X) = 1 := by
    let μ : OffspringConfigurationLaw ι X :=
      ⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩
    have hlaw : (μ.childCountLaw : Measure ℕ∞) =
        (L.raw : Measure (Step ι X)).map Step.childCount :=
      OffspringConfigurationLaw.childCountLaw_toMeasure μ
    have hcast : Measurable fun n : ℕ∞ => (n : ℝ≥0∞) := by fun_prop
    change (∫⁻ n : ℕ∞, (n : ℝ≥0∞) ∂μ.childCountLaw) = 1
    calc
      (∫⁻ n : ℕ∞, (n : ℝ≥0∞) ∂
          μ.childCountLaw) =
        ∫⁻ ξ, (ξ.childCount : ℝ≥0∞) ∂L.raw := by
        rw [hlaw]
        exact lintegral_map hcast Step.childCount_measurable
      _ = 1 := hrawIntegral
  exact (ne_of_lt hsupercritical) hexpectation.symm

/-- Positive mass of a split is inherited by any finite selection that
retains at least two children whenever the raw configuration has at least
two. The selector is otherwise unrestricted and need not be binary. -/
theorem exists_positive_selectedSplit
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (hsupercritical : OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (R : Step.FiniteSelection α X)
    (hadequate : ∀ ξ : Step α X,
      2 ≤ ξ.childCount → 2 ≤ (R ξ).card) :
    0 < L.raw {ξ | 2 ≤ (R (L.ordering ξ)).card} := by
  have hraw := rawSplitEvent_measure_pos L hnonempty hsupercritical
  apply lt_of_lt_of_le hraw
  apply measure_mono
  intro ξ hξ
  have hcountCast :
      ((L.ordering ξ).childCount : ℝ≥0∞) =
        (ξ.childCount : ℝ≥0∞) := by
    calc
      ((L.ordering ξ).childCount : ℝ≥0∞) =
          stepPointMeasure (L.ordering ξ) Set.univ :=
        (stepPointMeasure_univ _).symm
      _ = stepPointMeasure ξ Set.univ := congrArg
        (fun m : Measure X => m Set.univ) (L.sorted_pointMeasure ξ)
      _ = (ξ.childCount : ℝ≥0∞) := stepPointMeasure_univ _
  have hcount : (L.ordering ξ).childCount = ξ.childCount := by
    exact_mod_cast hcountCast
  exact hadequate (L.ordering ξ) (by
    change 2 ≤ ξ.childCount at hξ
    simpa [hcount] using hξ)

/-- The event that the ordered offspring realization has at least two
selected children and that the second selected child's potential is at most
the integer cutoff `M`. -/
def boundedSelectedSplitEvent
    {ι α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (L : StepLaw ι α X) (R : Step.FiniteSelection α X) (M : ℕ) :
    Set (Step ι X) :=
  {ξ | 2 ≤ (R (L.ordering ξ)).card ∧
    (L.ordering ξ).potentialValue' L.potential
      (secondSelectedSlot R (L.ordering ξ)) ≤ (M : ℝ)}

/-- The bounded selected-split event for a step already expressed in the
ordered slot type. -/
def boundedSelectedSplitStepEvent
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (M : ℝ) :
    Set (Step α X) :=
  {ξ | 2 ≤ (R ξ).card ∧
    ξ.potentialValue' φ (secondSelectedSlot R ξ) ≤ M}

/-- When the base rule has capacity two, the thesis reserve selector splits
exactly when the base rule selects two children and its second selected
child is below the cutoff. The ordered-step hypothesis is not needed for this
event identity; it is needed below to bound the first selected child's mark. -/
theorem reserveSelectionBelowPotential_split_iff_boundedSecond
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : R.IsBoundedBy 2)
    (φ : Potential X) (M : ℝ) (ξ : Step α X) :
    ξ ∈ splitBy (reserveSelectionBelowPotential R φ M) ↔
      ξ ∈ boundedSelectedSplitStepEvent R φ M := by
  change 2 ≤ (reserveSelectionBelowPotential R φ M ξ).card ↔
    2 ≤ (R ξ).card ∧
      ξ.potentialValue' φ (secondSelectedSlot R ξ) ≤ M
  constructor
  · intro hsplit
    have hsubset := reserveSelectionBelowPotential_subset R φ M ξ
    have hScard_le :
        (reserveSelectionBelowPotential R φ M ξ).card ≤ (R ξ).card :=
      Finset.card_le_card hsubset
    have hRcap : (R ξ).card ≤ 2 := hR ξ
    have hRcard : (R ξ).card = 2 := by omega
    have hSeq : reserveSelectionBelowPotential R φ M ξ = R ξ := by
      apply Finset.eq_of_subset_of_card_le hsubset
      rw [hRcard]
      exact hsplit
    have hsecond := secondSelectedSlot_mem_of_card R ξ (by omega : 2 ≤ (R ξ).card)
    have hsecondS : secondSelectedSlot R ξ ∈
        reserveSelectionBelowPotential R φ M ξ := by
      rw [hSeq]
      exact hsecond.1
    have hunion : secondSelectedSlot R ξ ∈
        firstOnlySelectedChild R ξ ∪ (R.belowPotential φ M) ξ := by
      simpa [reserveSelectionBelowPotential] using hsecondS
    have hbelow : secondSelectedSlot R ξ ∈ (R.belowPotential φ M) ξ := by
      rcases Finset.mem_union.mp hunion with hfirst | hbounded
      · have hfirst' :=
          (Step.FiniteSelection.mem_filter R
            (fun ξ i => i = firstSelectedSlot R ξ) ξ
            (secondSelectedSlot R ξ)).mp (by
              simpa [firstOnlySelectedChild] using hfirst)
        exact (hsecond.2 hfirst'.2.symm).elim
      · exact hbounded
    have hbelow' :=
      (Step.FiniteSelection.mem_filter R
        (fun ξ i => ξ.potentialValue' φ i ≤ M) ξ
        (secondSelectedSlot R ξ)).mp (by
          simpa [Step.FiniteSelection.belowPotential] using hbelow)
    exact ⟨by omega, hbelow'.2⟩
  · rintro ⟨hcard, hbound⟩
    exact reserveSelectionBelowPotential_split_of_boundedSecond
      R φ M ξ hcard hbound

/-- At every split of a capacity-two reserve selector on an ordered step,
both selected edge potentials are at most the cutoff. In particular, the
first-child edge used to start a candidate growth trial is bounded even
though the reserve selector keeps that child unconditionally on nonsplit
steps. -/
theorem reserveSelectionBelowPotential_split_edgePotentials_le_of_ordered
    {α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : R.IsBoundedBy 2)
    (φ : Potential X) (M : ℝ) (ξ : Step α X)
    (hordered : ξ.IsOrderedBy φ)
    (hsplit : ξ ∈ splitBy (reserveSelectionBelowPotential R φ M)) :
    ξ.potentialValue' φ
        (firstSelectedSlot (reserveSelectionBelowPotential R φ M) ξ) ≤ M ∧
      ξ.potentialValue' φ
        (secondSelectedSlot (reserveSelectionBelowPotential R φ M) ξ) ≤ M := by
  have hbounded :=
    (reserveSelectionBelowPotential_split_iff_boundedSecond
      R hR φ M ξ).mp hsplit
  change 2 ≤ (R ξ).card ∧
    ξ.potentialValue' φ (secondSelectedSlot R ξ) ≤ M at hbounded
  have hRcard : (R ξ).card = 2 := by
    have hSleR := Finset.card_le_card
      (reserveSelectionBelowPotential_subset R φ M ξ)
    have hRcap : (R ξ).card ≤ 2 := hR ξ
    omega
  have hSeq : reserveSelectionBelowPotential R φ M ξ = R ξ := by
    apply Finset.eq_of_subset_of_card_le
      (reserveSelectionBelowPotential_subset R φ M ξ)
    rw [hRcard]
    exact hsplit
  have hfirstEq :
      firstSelectedSlot (reserveSelectionBelowPotential R φ M) ξ =
        firstSelectedSlot R ξ := by
    simp [firstSelectedSlot, hSeq]
  have hsecondEq :
      secondSelectedSlot (reserveSelectionBelowPotential R φ M) ξ =
        secondSelectedSlot R ξ := by
    simp [secondSelectedSlot, hSeq, hfirstEq]
  have hfirst_le := potentialValue'_firstSelectedSlot_le_second_of_ordered
    φ R ξ hordered hbounded.1
  constructor
  · rw [hfirstEq]
    exact hfirst_le.trans hbounded.2
  · rw [hsecondEq]
    exact hbounded.2

/-- The same first-edge bound holds almost surely under the sorted offspring
law: `StepLaw.sorted` is supported on its ordered realization. This is the
probability-space form used by the restart construction. -/
theorem reserveSelectionBelowPotential_split_edgePotentials_le_sorted_ae
    {ι α X : Type*} [MeasurableSpace X] [Countable ι] [Countable α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw] (M : ℝ) :
    ∀ᵐ ξ ∂L.sorted,
      ξ ∈ splitBy (reserveSelectionBelowPotential
        (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
        L.potential M) →
        ξ.potentialValue' L.potential
            (firstSelectedSlot (reserveSelectionBelowPotential
              (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
              L.potential M) ξ) ≤ M ∧
          ξ.potentialValue' L.potential
            (secondSelectedSlot (reserveSelectionBelowPotential
              (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
              L.potential M) ξ) ≤ M := by
  have horderedSet :
      MeasurableSet (Combinatorics.Branching.orderedBySteps (ι := α) L.potential) :=
    Combinatorics.Branching.orderedBySteps_measurable (ι := α) L.potential
  have horderedMass :
      L.sorted (Combinatorics.Branching.orderedBySteps (ι := α) L.potential) = 1 := by
    calc
      L.sorted (Combinatorics.Branching.orderedBySteps (ι := α) L.potential) =
          L.sorted {ξ | ξ.IsOrderedBy L.potential} := rfl
      _ = L.raw Set.univ := L.sorted_orderedBy horderedSet
      _ = 1 := by simp
  have hpredMeas : Measurable fun ξ : Step α X => ξ.IsOrderedBy L.potential :=
    measurableSet_setOfPred.mp horderedSet
  have hordered : ∀ᵐ ξ ∂L.sorted, ξ.IsOrderedBy L.potential := by
    exact (ae_iff_prob_eq_one hpredMeas).2 horderedMass
  have hRcap :
      (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2).IsBoundedBy 2 :=
    Step.FiniteSelection.firstNBySlotOrder_isBoundedBy 2
  filter_upwards [hordered] with ξ hξ
  intro hsplit
  exact reserveSelectionBelowPotential_split_edgePotentials_le_of_ordered
    (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
    hRcap L.potential M ξ hξ hsplit

theorem boundedSelectedSplitEvent_eq_ordering_preimage
    {ι α X : Type*} [LinearOrder α] [OrderBot α] [MeasurableSpace X]
    (L : StepLaw ι α X) (R : Step.FiniteSelection α X) (M : ℕ) :
    boundedSelectedSplitEvent L R M =
      L.ordering ⁻¹' boundedSelectedSplitStepEvent R L.potential (M : ℝ) := rfl

theorem boundedSelectedSplitStepEvent_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (φ : Potential X) (M : ℝ) :
    MeasurableSet (boundedSelectedSplitStepEvent R φ M) := by
  let selectedSplit : Set (Step α X) := {ξ | 2 ≤ (R ξ).card}
  let second : Step α X → α := fun ξ => secondSelectedSlot R ξ
  have hcard : Measurable (fun ξ : Step α X => (R ξ).card) :=
    (measurable_of_countable fun s : Finset α => s.card).comp hR
  have hsplit : MeasurableSet selectedSplit := by
    change MeasurableSet
      ((fun ξ : Step α X => (R ξ).card) ⁻¹' Set.Ici 2)
    exact hcard measurableSet_Ici
  have hsecond : Measurable second := secondSelectedSlot_measurable R hR
  have hpotential (i : α) : Measurable
      (fun ξ : Step α X => ξ.potentialValue' φ i) :=
    Step.potentialValue'_measurable φ i
  have hbounded : MeasurableSet
      {ξ : Step α X | ξ.potentialValue' φ (second ξ) ≤ M} := by
    have heq : {ξ : Step α X | ξ.potentialValue' φ (second ξ) ≤ M} =
        ⋃ i : α, {ξ | second ξ = i} ∩
          {ξ | ξ.potentialValue' φ i ≤ M} := by
      ext ξ
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · intro hξ
        exact ⟨second ξ, rfl, hξ⟩
      · rintro ⟨i, hi, hξ⟩
        rw [← hi] at hξ
        exact hξ
    rw [heq]
    apply MeasurableSet.iUnion
    intro i
    exact (hsecond (measurableSet_singleton i)).inter
      ((hpotential i) measurableSet_Iic)
  change MeasurableSet
    (selectedSplit ∩
      {ξ | ξ.potentialValue' φ (secondSelectedSlot R ξ) ≤ M})
  exact hsplit.inter hbounded

theorem boundedSelectedSplitEvent_measurable
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) (R : Step.FiniteSelection α X)
    (hR : Measurable R.select) (M : ℕ) :
    MeasurableSet (boundedSelectedSplitEvent L R M) := by
  rw [boundedSelectedSplitEvent_eq_ordering_preimage]
  exact (boundedSelectedSplitStepEvent_measurable R hR L.potential
    (M : ℝ)).preimage L.ordering.measurable_ordered

/-- For an adequate finite selection, some finite integer cutoff on the
second selected child's real potential leaves a positive-probability split
event. This truncation step requires no offspring-size bound and permits any
finite number of selected children. -/
theorem exists_nat_cutoff_positive_boundedSelectedSplit
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (hsupercritical : OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hadequate : ∀ ξ : Step α X,
      2 ≤ ξ.childCount → 2 ≤ (R ξ).card) :
    ∃ M : ℕ, 0 < L.raw (boundedSelectedSplitEvent L R M) ∧
      MeasurableSet (boundedSelectedSplitEvent L R M) := by
  let selectedSplit : Set (Step ι X) :=
    {ξ | 2 ≤ (R (L.ordering ξ)).card}
  let bounded (M : ℕ) : Set (Step ι X) :=
    boundedSelectedSplitEvent L R M
  have hselected : 0 < L.raw selectedSplit :=
    exists_positive_selectedSplit L hnonempty hsupercritical R hadequate
  have hcover : selectedSplit ⊆ ⋃ M : ℕ, bounded M := by
    intro ξ hξ
    obtain ⟨M, hM⟩ := exists_nat_gt
      ((L.ordering ξ).potentialValue' L.potential
        (secondSelectedSlot R (L.ordering ξ)))
    refine Set.mem_iUnion.mpr ⟨M, ?_⟩
    exact ⟨hξ, le_of_lt hM⟩
  have hunion : 0 < L.raw (⋃ M : ℕ, bounded M) :=
    lt_of_lt_of_le hselected (measure_mono hcover)
  obtain ⟨M, hM⟩ := exists_measure_pos_of_not_measure_iUnion_null
    (μ := L.raw) (s := bounded) (ne_of_gt hunion)
  exact ⟨M, by simpa [bounded] using hM,
    boundedSelectedSplitEvent_measurable L R hR M⟩

/-- The same bounded-split cutoff, expressed under the ordered offspring law
used by the selected branching walk. -/
theorem exists_nat_cutoff_positive_boundedSelectedSplit_sorted
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (hsupercritical : OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hadequate : ∀ ξ : Step α X,
      2 ≤ ξ.childCount → 2 ≤ (R ξ).card) :
    ∃ M : ℕ,
      0 < L.sorted (boundedSelectedSplitStepEvent R L.potential (M : ℝ)) ∧
      MeasurableSet
        (boundedSelectedSplitStepEvent R L.potential (M : ℝ)) := by
  obtain ⟨M, hpos, _hmeas⟩ :=
    exists_nat_cutoff_positive_boundedSelectedSplit L hnonempty
      hsupercritical R hR hadequate
  have hmap :
      L.sorted (boundedSelectedSplitStepEvent R L.potential (M : ℝ)) =
        L.raw (boundedSelectedSplitEvent L R M) := by
    rw [StepLaw.sorted, Measure.map_apply L.ordering.measurable_ordered
      (boundedSelectedSplitStepEvent_measurable R hR L.potential (M : ℝ))]
    rfl
  exact ⟨M, by rw [hmap]; exact hpos,
    boundedSelectedSplitStepEvent_measurable R hR L.potential (M : ℝ)⟩

/-- Concrete good-split input for the reserve construction: the first two
surviving slots in the ordered realization form a split, and some finite
potential cutoff on the second one preserves positive probability. -/
theorem exists_nat_cutoff_positive_bounded_firstTwoBySlotOrder
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (hsupercritical : OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X)) :
    ∃ M : ℕ,
      0 < L.raw (boundedSelectedSplitEvent L
        (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2) M) ∧
      MeasurableSet (boundedSelectedSplitEvent L
        (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2) M) := by
  let R : Step.FiniteSelection α X :=
    Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2
  have hR : Measurable R.select := by
    simpa [R] using (firstTwoBySlotOrder_measurable (α := α) (X := X))
  have hadequate : ∀ ξ : Step α X,
      2 ≤ ξ.childCount → 2 ≤ (R ξ).card := by
    intro ξ hcount
    rw [show (R ξ).card = 2 from
      Step.FiniteSelection.card_firstNBySlotOrder_eq_of_le_childCount 2 ξ hcount]
  simpa [R] using
    (exists_nat_cutoff_positive_boundedSelectedSplit L hnonempty
      hsupercritical R hR hadequate)

/-- Positive mass of a split by the thesis reserve selector. Its base rule
keeps the first two surviving slots in the ordered realization, and the
reserve rule keeps the first child plus the second whenever the second
potential is below the finite cutoff. -/
theorem exists_nat_cutoff_positive_reserveSplit
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (hsupercritical : OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X)) :
    ∃ M : ℕ,
      0 < L.sorted (splitBy (reserveSelectionBelowPotential
        (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
        L.potential (M : ℝ))) ∧
      MeasurableSet (splitBy (reserveSelectionBelowPotential
        (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
        L.potential (M : ℝ))) := by
  let R : Step.FiniteSelection α X :=
    Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2
  have hR : Measurable R.select := by
    simpa [R] using (firstTwoBySlotOrder_measurable (α := α) (X := X))
  have hadequate : ∀ ξ : Step α X,
      2 ≤ ξ.childCount → 2 ≤ (R ξ).card := by
    intro ξ hcount
    rw [show (R ξ).card = 2 from
      Step.FiniteSelection.card_firstNBySlotOrder_eq_of_le_childCount 2 ξ hcount]
  obtain ⟨M, hpos, _hmeas⟩ :=
    exists_nat_cutoff_positive_boundedSelectedSplit_sorted L hnonempty
      hsupercritical R hR hadequate
  let S := reserveSelectionBelowPotential R L.potential (M : ℝ)
  have hS : Measurable S.select := by
    simpa [S] using reserveSelectionBelowPotential_measurable
      R hR L.potential (M : ℝ)
  have hsubset : boundedSelectedSplitStepEvent R L.potential (M : ℝ) ⊆
      splitBy S := by
    intro ξ hξ
    exact reserveSelectionBelowPotential_split_of_boundedSecond
      R L.potential (M : ℝ) ξ hξ.1 hξ.2
  have hsplit : MeasurableSet (splitBy S) := splitBy_measurable S hS
  refine ⟨M, ?_, ?_⟩
  · apply lt_of_lt_of_le hpos
    exact measure_mono hsubset
  · simpa [S] using hsplit

/-- The concrete reserve selector is nonempty almost surely under the
ordered offspring law, because the raw law is nonempty almost surely and
ordering preserves the complete offspring point measure. -/
theorem reserveSelectionBelowPotential_nonempty_ae
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (M : ℝ) :
    ∀ᵐ ξ ∂L.sorted,
      (reserveSelectionBelowPotential
        (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
        L.potential M ξ).Nonempty := by
  letI : IsProbabilityMeasure L.sorted := inferInstance
  let μ : OffspringConfigurationLaw α X := ⟨L.sorted, inferInstance⟩
  have hμ : μ.HasAtLeastOneChild := by
    change L.sorted nonemptySupport = 1
    rw [L.sorted_nonemptySupport]
    simpa [OffspringConfigurationLaw.HasAtLeastOneChild] using hnonempty
  have hae := OffspringConfigurationLaw.hasAtLeastOneChild_ae μ hμ
  filter_upwards [hae] with ξ hξ
  have hsupport : (support ξ).Nonempty := by
    obtain ⟨i, hi⟩ := hξ
    exact ⟨i, hi⟩
  have hRne := Step.FiniteSelection.firstNBySlotOrder_nonempty_of_support_nonempty
    (N := 2) (by norm_num) ξ hsupport
  exact reserveSelectionBelowPotential_nonempty_of_selected_nonempty
    (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
    L.potential M ξ hRne

/-- At a selected split, the totalized second-slot selector is an actual
selected child, and its zero-defaulted potential is that child's potential. -/
theorem secondSelectedSlot_potentialValue'_eq_mark
    {α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (φ : Potential X) (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hcard : 2 ≤ (R ξ).card) :
    ∃ x : X, ξ (secondSelectedSlot R ξ) = some x ∧
      ξ.potentialValue' φ (secondSelectedSlot R ξ) = φ x := by
  obtain ⟨hmem, _⟩ := secondSelectedSlot_mem_of_card R ξ hcard
  obtain ⟨x, hx⟩ := R.mem_support ξ hmem
  exact ⟨x, hx, by simp [Step.potentialValue', Step.potentialAt?, hx]⟩

end ProbabilityTheory.BranchingRandomWalk

end
