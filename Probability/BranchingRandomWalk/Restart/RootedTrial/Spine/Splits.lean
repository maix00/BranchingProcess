/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
/-!
# Split completions along a pre-sampled reserve spine

The reserve spine and all of its candidate siblings are defined on one
pre-sampled marked tree.  The split counter below only counts splits reached
while the spine is alive.  A split mark at generation `k` is first observable
in the domain filtration at generation `k + 1`; consequently every finite
split count, and every ordinal split-completion time, is adapted/stopping.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The number of live splits observed strictly before generation `n` on the
pre-sampled reserve spine.  This is the finite sum of the indicators
`1_{alive k ∧ split(mark(path k))}` for `k < n`, represented as the cardinality
of the corresponding filtered finite index set. -/
noncomputable def selectedReserveSpineSplitCount
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) : ℕ :=
  ((Finset.range n).filter fun k =>
    selectedReserveSpineAlive R r k ω ∧
      ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R).card

/-- The split count is literally the finite sum of the `0`/`1` split
indicators. -/
theorem selectedReserveSpineSplitCount_eq_sum_indicators
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    selectedReserveSpineSplitCount R r n ω =
      ∑ k ∈ Finset.range n,
        if selectedReserveSpineAlive R r k ω ∧
          ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R then 1 else 0 := by
  classical
  change ((Finset.range n).filter fun k =>
      selectedReserveSpineAlive R r k ω ∧
        ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R).card = _
  exact (Finset.sum_boole
    (fun k : ℕ => selectedReserveSpineAlive R r k ω ∧
      ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R)
    (Finset.range n)).symm

/-- A finite split count is measurable at the generation through which all
its split marks have been exposed.  For each `k < n`, the spine state is
`F_k`-measurable and its mark is `F_(k+1)`-measurable. -/
theorem selectedReserveSpineSplitCount_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun ω => selectedReserveSpineSplitCount R r n ω) := by
  classical
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  have toPropMeasurable (p : RootIndexed.StepField Root α X → Prop)
      (hs : MeasurableSet[F n] {ω | p ω}) :
      @Measurable (RootIndexed.StepField Root α X) Prop (F n) inferInstance
        p := by
    exact (@measurableSet_setOfPred _ (F n) p).mp hs
  have hindices : Measurable[F n]
      (fun ω : RootIndexed.StepField Root α X =>
        (Finset.range n).filter fun k =>
          selectedReserveSpineAlive R r k ω ∧
            ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R) := by
    apply (@measurable_finset_iff ℕ (RootIndexed.StepField Root α X) (F n)).2
    intro k
    by_cases hk : k < n
    · have halive : MeasurableSet[F n]
          {ω | selectedReserveSpineAlive R r k ω} :=
        F.mono (Nat.le_of_lt hk) _
          (selectedReserveSpineAlive_measurable R hR r k)
      have hmark : MeasurableSet[F (k + 1)]
          {ω | ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R} := by
        exact (splitBy_measurable R hR).preimage
          (selectedReserveSpineMark_adapted R hR r k)
      have hmark' : MeasurableSet[F n]
          {ω | ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R} :=
        F.mono (by omega) _ hmark
      have heq : {ω | k ∈ (Finset.range n).filter fun j =>
            selectedReserveSpineAlive R r j ω ∧
              ω r (selectedReserveSpinePath R r j ω) ∈ splitBy R} =
          {ω | selectedReserveSpineAlive R r k ω} ∩
            {ω | ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R} := by
        ext ω
        simp [hk, Finset.mem_filter, Finset.mem_range]
      apply toPropMeasurable
      rw [heq]
      exact halive.inter hmark'
    · have heq : {ω | k ∈ (Finset.range n).filter fun j =>
            selectedReserveSpineAlive R r j ω ∧
              ω r (selectedReserveSpinePath R r j ω) ∈ splitBy R} = ∅ := by
        ext ω
        simp [hk, Finset.mem_filter, Finset.mem_range]
      apply toPropMeasurable
      rw [heq]
      exact (F n).measurableSet_empty
  change Measurable[F n]
    (fun ω => ((Finset.range n).filter fun k =>
      selectedReserveSpineAlive R r k ω ∧
        ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R).card)
  exact (measurable_of_countable fun s : Finset ℕ => s.card).comp hindices

/-- The `i`-th split-completion on the reserve spine, with `i` a positive
one-based ordinal.  This is the first generation `n` by which at least `i`
live split marks have been observed. -/
noncomputable def selectedReserveSpineSplitCompletion
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (i : ℕ) :
    RootIndexed.StepField Root α X → WithTop ℕ :=
  firstDeclaredSuccess fun n =>
    {ω | i ≤ selectedReserveSpineSplitCount R r n ω}

/-- Each ordinal split-completion is a stopping time for the domain
filtration.  In particular, the raw look-ahead label of a split is not used
as a stopping time: the count includes the split mark only once it is exposed
at the next generation. -/
theorem selectedReserveSpineSplitCompletion_isStoppingTime
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (i : ℕ) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (selectedReserveSpineSplitCompletion R r i) := by
  apply firstDeclaredSuccess_isStoppingTime
  intro n
  exact (selectedReserveSpineSplitCount_measurable R hR r n) measurableSet_Ici

/-- At a split of the reserve spine, the next reserve prefix is the selected
second-child sibling.  This is the absolute prefix of the recursively
pre-sampled reserve field rooted at that sibling. -/
noncomputable def selectedReserveSpineReservePrefix
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (k : ℕ)
    (ω : RootIndexed.StepField Root α X) : TreeNode α :=
  selectedReserveSpinePath R r k ω ++
    [secondSelectedSlot R (ω r (selectedReserveSpinePath R r k ω))]

/-- The pre-sampled descendant field rooted at the second child of the
reserve-spine split at generation `k`. -/
noncomputable def selectedReserveSpineReserveFieldAtSplit
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (k : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    RootIndexed.StepField PUnit.{1} α X :=
  fun _ u =>
    ω r (selectedReserveSpineReservePrefix R r k ω ++ u)

/-- Path decomposition for the named reserve-subtree field. -/
theorem selectedReserveSpinePath_decompose_at_split_field
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (k : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hsplit : ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R) :
    ∀ n, selectedReserveSpinePath R r (k + 1 + n) ω =
      selectedReserveSpineReservePrefix R r k ω ++
        selectedReserveSpinePath R PUnit.unit n
          (selectedReserveSpineReserveFieldAtSplit R r k ω) := by
  intro n
  change selectedReserveSpinePath R r (k + 1 + n) ω =
    (selectedReserveSpinePath R r k ω ++
      [secondSelectedSlot R (ω r (selectedReserveSpinePath R r k ω))]) ++
    selectedReserveSpinePath R PUnit.unit n
      (fun _ u => ω r ((selectedReserveSpinePath R r k ω ++
        [secondSelectedSlot R (ω r (selectedReserveSpinePath R r k ω))]) ++ u))
  exact selectedReserveSpinePath_decompose_at_split R r k ω hsplit n

/-- A split seen in the recursively defined reserve subtree is exactly the
same split mark in the original pre-sampled tree at the corresponding
absolute spine generation. -/
theorem selectedReserveSpineMark_decompose_at_split_field
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (k n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hsplit : ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R) :
    ω r (selectedReserveSpinePath R r (k + 1 + n) ω) =
      selectedReserveSpineReserveFieldAtSplit R r k ω PUnit.unit
        (selectedReserveSpinePath R PUnit.unit n
          (selectedReserveSpineReserveFieldAtSplit R r k ω)) := by
  rw [selectedReserveSpinePath_decompose_at_split_field R r k ω hsplit n]
  rfl

/-- Once the reserve spine is alive at a split, its future alive states are
exactly the alive states of the recursively pre-sampled reserve sibling.
This identifies genuine later candidate roots and excludes totalized phantom
paths after extinction. -/
theorem selectedReserveSpineAlive_decompose_at_split_field
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (k : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (halive : selectedReserveSpineAlive R r k ω)
    (hsplit : ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R) :
    ∀ n, selectedReserveSpineAlive R r (k + 1 + n) ω ↔
      selectedReserveSpineAlive R PUnit.unit n
        (selectedReserveSpineReserveFieldAtSplit R r k ω) := by
  have hcard : 2 ≤ (R (ω r (selectedReserveSpinePath R r k ω))).card := by
    simpa [splitBy] using hsplit
  have hnonempty : (R (ω r (selectedReserveSpinePath R r k ω))).Nonempty :=
    Finset.card_pos.mp (by omega)
  intro n
  induction n with
  | zero =>
      change (selectedReserveSpineAlive R r k ω ∧
          (R (ω r (selectedReserveSpinePath R r k ω))).Nonempty) ↔ True
      simp [halive, hnonempty]
  | succ n ih =>
      have hindex : k + 1 + (n + 1) = (k + 1 + n) + 1 := by omega
      rw [hindex]
      change (selectedReserveSpineAlive R r (k + 1 + n) ω ∧
          (R (ω r (selectedReserveSpinePath R r (k + 1 + n) ω))).Nonempty) ↔
        (selectedReserveSpineAlive R PUnit.unit n
            (selectedReserveSpineReserveFieldAtSplit R r k ω) ∧
          (R (selectedReserveSpineReserveFieldAtSplit R r k ω PUnit.unit
            (selectedReserveSpinePath R PUnit.unit n
              (selectedReserveSpineReserveFieldAtSplit R r k ω)))).Nonempty)
      rw [ih, selectedReserveSpineMark_decompose_at_split_field
        R r k n ω hsplit]

/-- The first-child candidate discovered at an actual global reserve-spine
split at generation `k + 1 + n` is exactly the first-child root of the
recursively pre-sampled second-child reserve subtree.  The alive premise from
`selectedReserveSpineAlive_decompose_at_split_field` ensures this is a real
candidate in the genealogical tree, not a totalized address after extinction.
-/
theorem selectedReserveSpineCandidate_root_at_recursive_split
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (k n : ℕ) (ω : RootIndexed.StepField Root α X)
    (halive : selectedReserveSpineAlive R r k ω)
    (hsplit : ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R)
    (hlocallyAlive : selectedReserveSpineAlive R PUnit.unit n
      (selectedReserveSpineReserveFieldAtSplit R r k ω))
    (hlocalsplit :
      selectedReserveSpineReserveFieldAtSplit R r k ω PUnit.unit
        (selectedReserveSpinePath R PUnit.unit n
          (selectedReserveSpineReserveFieldAtSplit R r k ω)) ∈ splitBy R) :
    ((selectedReserveSpineLineages R hR).firstChildRootAt R r
        PUnit.unit (k + 1 + n + 1) ω =
      (r, selectedReserveSpineReservePrefix R r k ω ++
        (selectedReserveSpinePath R PUnit.unit n
            (selectedReserveSpineReserveFieldAtSplit R r k ω) ++
          [firstSelectedSlot R
            (selectedReserveSpineReserveFieldAtSplit R r k ω PUnit.unit
              (selectedReserveSpinePath R PUnit.unit n
                (selectedReserveSpineReserveFieldAtSplit R r k ω)))]))) ∧
      selectedReserveSpineAlive R r (k + 1 + n) ω ∧
      firstSelectedSlot R
        (ω r (selectedReserveSpinePath R r (k + 1 + n) ω)) ∈
          R (ω r (selectedReserveSpinePath R r (k + 1 + n) ω)) := by
  have hpath := selectedReserveSpinePath_decompose_at_split_field
    R r k ω hsplit n
  have hmark := selectedReserveSpineMark_decompose_at_split_field
    R r k n ω hsplit
  have hglobalAlive :=
    (selectedReserveSpineAlive_decompose_at_split_field
      R r k ω halive hsplit n).2 hlocallyAlive
  have hglobalSplit :
      ω r (selectedReserveSpinePath R r (k + 1 + n) ω) ∈ splitBy R := by
    rw [hmark]
    exact hlocalsplit
  have hcandidateIsChild := selectedReserveSpineCandidate_root_at_split
    R hR r (k + 1 + n) ω hglobalSplit
  have hparentAlive : selectedReserveSpineAlive R r (k + 1 + n) ω := hglobalAlive
  refine ⟨?_, hparentAlive, hcandidateIsChild.2⟩
  calc
    _ = (r, selectedReserveSpinePath R r (k + 1 + n) ω ++
        [firstSelectedSlot R
          (ω r (selectedReserveSpinePath R r (k + 1 + n) ω))]) :=
            hcandidateIsChild.1
    _ = (r, selectedReserveSpineReservePrefix R r k ω ++
        (selectedReserveSpinePath R PUnit.unit n
            (selectedReserveSpineReserveFieldAtSplit R r k ω) ++
          [firstSelectedSlot R
            (selectedReserveSpineReserveFieldAtSplit R r k ω PUnit.unit
                (selectedReserveSpinePath R PUnit.unit n
                  (selectedReserveSpineReserveFieldAtSplit R r k ω)))])) := by
      rw [hmark, hpath]
      apply congrArg (fun path : TreeNode α => (r, path))
      exact List.append_assoc _ _ _

end ProbabilityTheory.BranchingRandomWalk
