/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Selection.Potential
public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingProcess.Offspring.Count
public import Probability.BranchingRandomWalk.Step.Ordering.Law
public import Probability.BranchingRandomWalk.Restart.Trial.FirstSplit
public import Combinatorics.BranchingWalk.Step.Selection.Slot
public import Combinatorics.BranchingWalk.Step.Count
public import MeasureTheory.BranchingWalk.Step.Selection.FirstN
public import MeasureTheory.BranchingWalk.Step.Selection.Potential

/-!
# Positive-probability bounded splits

A supercritical offspring law has positive probability of at least two
children. For any measurable finite selection that retains at least two
children whenever they are available, a finite integer cutoff on the second
selected child's potential preserves positive split probability. This gives
the bounded reserve selector used in the restart construction. Almost-sure
nonemptiness of the selected reserve is established separately from the
almost-sure nonempty-offspring assumption.

## Public declarations

- `exists_positive_selectedSplit` states that, if
  `1 < E[childCount]` and the selector retains two children on every
  configuration with at least two, then
  `L.raw {ξ | 2 ≤ card (R (L.ordering ξ))} > 0`.
- `boundedSelectedSplitEvent L R M` is
  `{ξ | 2 ≤ card (R (L.ordering ξ)) ∧
  potential(ξ, secondSelectedSlot(R, L.ordering ξ)) ≤ M}`;
  `boundedSelectedSplitStepEvent R φ M` is the corresponding event for an
  already ordered step.
- `boundedSelectedSplitEvent_measurable` proves measurability under a
  measurable selector. `exists_nat_cutoff_positive_boundedSelectedSplit`
  gives `∃ M : ℕ, L.raw (boundedSelectedSplitEvent L R M) > 0`, and
  `exists_nat_cutoff_positive_boundedSelectedSplit_sorted` gives the same
  conclusion for the ordered law and its step event.
- `exists_nat_cutoff_positive_reserveSplit` supplies `M : ℕ` with positive
  ordered-law probability of `splitBy (reserveSelectionBelowPotential R φ M)`.
  `reserveSelectionBelowPotential_nonempty_ae` uses almost-sure nonempty
  offspring to show that the concrete reserve selector is almost surely
  nonempty.
- `reserveSelectionBelowPotential_split_edgePotentials_le_sorted_ae` states
  that, almost surely under `L.sorted`, a reserve split has both selected
  edge potentials at most `M`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingProcess

/-- Positive mass of a split is inherited by any finite selection that
retains at least two children whenever the raw configuration has at least
two. The selector is otherwise unrestricted and need not be binary. -/
theorem exists_positive_selectedSplit
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hsupercritical : OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (R : Step.FiniteSelection α X)
    (hadequate : ∀ ξ : Step α X,
      2 ≤ ξ.childCount → 2 ≤ (R ξ).card) :
    0 < L.raw {ξ | 2 ≤ (R (L.ordering ξ)).card} := by
  let μ : OffspringConfigurationLaw ι X :=
    ⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩
  have hcast : Measurable fun n : ℕ∞ => (n : ℝ≥0∞) := by fun_prop
  have hmean : 1 < ∫⁻ ξ, (ξ.childCount : ℝ≥0∞) ∂L.raw := by
    calc
      1 < μ.expectedChildCount := hsupercritical
      _ = ∫⁻ ξ, (ξ.childCount : ℝ≥0∞) ∂L.raw := by
        change (∫⁻ n : ℕ∞, (n : ℝ≥0∞) ∂μ.childCountLaw) = _
        rw [OffspringConfigurationLaw.childCountLaw_toMeasure]
        exact lintegral_map hcast Step.childCount_measurable
  have hraw :=
    Offspring.measure_pos_childCount_ge_two_of_expectedChildCount_gt_one
      L.raw hmean
  apply lt_of_lt_of_le hraw
  apply measure_mono
  intro ξ hξ
  change 2 ≤ ξ.childCount at hξ
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
  exact hadequate (L.ordering ξ) (by simpa [hcount] using hξ)

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

/-- Under the ordered offspring law, every reserve split has both selected
edge potentials bounded by the cutoff almost surely. -/
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
  exact reserveSelectionBelowPotential_edgePotentials_le_of_ordered
    (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
    hRcap L.potential M ξ hξ hsplit

private theorem boundedSelectedSplitEvent_eq_ordering_preimage
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
    exists_positive_selectedSplit L hsupercritical R hadequate
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
    exists_nat_cutoff_positive_boundedSelectedSplit L hsupercritical
      R hR hadequate
  have hmap :
      L.sorted (boundedSelectedSplitStepEvent R L.potential (M : ℝ)) =
        L.raw (boundedSelectedSplitEvent L R M) := by
    rw [StepLaw.sorted, Measure.map_apply L.ordering.measurable_ordered
      (boundedSelectedSplitStepEvent_measurable R hR L.potential (M : ℝ))]
    rfl
  exact ⟨M, by rw [hmap]; exact hpos,
    boundedSelectedSplitStepEvent_measurable R hR L.potential (M : ℝ)⟩

/-- Positive mass of a split by the reserve selector. Its base rule
keeps the first two surviving slots in the ordered realization, and the
reserve rule keeps the first child plus the second whenever the second
potential is below the finite cutoff. -/
theorem exists_nat_cutoff_positive_reserveSplit
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
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
    exists_nat_cutoff_positive_boundedSelectedSplit_sorted L hsupercritical
      R hR hadequate
  let S := reserveSelectionBelowPotential R L.potential (M : ℝ)
  have hS : Measurable S.select := by
    simpa [S] using reserveSelectionBelowPotential_measurable
      R hR L.potential (M : ℝ)
  have hsubset : boundedSelectedSplitStepEvent R L.potential (M : ℝ) ⊆
      splitBy S := by
    intro ξ hξ
    exact reserveSelectionBelowPotential_card_ge_two_of_boundedSecond
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
  let : IsProbabilityMeasure L.sorted := inferInstance
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

end ProbabilityTheory.BranchingRandomWalk

end
