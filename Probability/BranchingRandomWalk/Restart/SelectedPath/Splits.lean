/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.SelectedPath.Path
/-!
# Split completions along a pre-sampled selected path

The selected path and all of its candidate siblings are defined on one
pre-sampled marked tree.  The split counter below only counts splits reached
while the selected path is alive.  A split mark at generation `k` is first observable
in the domain filtration at generation `k + 1`; consequently every finite
split count, and every ordinal split-completion time, is adapted/stopping.

## Public declarations

The number of splits observed through generation \(n\) is the sum of the
live selected-path split indicators, and the \(i\)-th split completion is the first
generation when this count reaches \(i\):

\[N_n=\sum_{k=0}^{n-1}
  \mathbf 1_{\{\mathrm{alive}(k)\wedge\mathrm{split}(k)\}},\qquad
  \tau_i=\inf\{n:N_n\ge i\}.\]

`Restart.SelectedPath.splitCount`, `Restart.SelectedPath.splitCount_eq_sum_indicators`,
and `Restart.SelectedPath.splitCount_measurable` define the number of live
splits observed before generation `n`, identify it with the finite sum of the
indicators `1_{alive(k) ∧ split(k)}`, and prove measurability at generation `n`.
`Restart.SelectedPath.splitCompletion` and
`Restart.SelectedPath.splitCompletion_isStoppingTime` give the first generation
at which the count reaches `i` and its stopping-time property.

`Restart.SelectedPath.continuationPrefix` and
`Restart.SelectedPath.continuationFieldAtSplit` name the second-child subtree after a
split at generation `k`. `Restart.SelectedPath.decompose_at_split_field`
and `Restart.SelectedPath.mark_decompose_at_split_field` identify its later
path and marks with the corresponding absolute selected-path generations;
`Restart.SelectedPath.isAlive_decompose_at_split_field` gives the corresponding
alive-state equivalence. `Restart.SelectedPath.GrowthTrial.root_at_split`
identifies the first-selected-child root at a split as
`(r, path(k) ++ [firstSelectedSlot(mark(path(k)))])` and proves the selected
slot belongs to the offspring selection. The recursive form is
`Restart.SelectedPath.GrowthTrial.root_at_recursive_split`.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory
open Combinatorics.Branching.Step.FiniteSelection

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The number of live splits observed strictly before generation `n` on the
pre-sampled selected path.  This is the finite sum of the indicators
`1_{alive k ∧ split(mark(path k))}` for `k < n`, represented as the cardinality
of the corresponding filtered finite index set. -/
noncomputable def splitCount
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) : ℕ :=
  ((Finset.range n).filter fun k =>
    Restart.SelectedPath.isAlive R r k ω ∧
      Restart.SelectedPath.splitEvent R r k ω).card

/-- The split count is literally the finite sum of the `0`/`1` split
indicators. -/
theorem splitCount_eq_sum_indicators
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    Restart.SelectedPath.splitCount R r n ω =
      ∑ k ∈ Finset.range n,
        if Restart.SelectedPath.isAlive R r k ω ∧
          Restart.SelectedPath.splitEvent R r k ω then 1 else 0 := by
  classical
  change ((Finset.range n).filter fun k =>
      Restart.SelectedPath.isAlive R r k ω ∧
        Restart.SelectedPath.splitEvent R r k ω).card = _
  exact (Finset.sum_boole
    (fun k : ℕ => Restart.SelectedPath.isAlive R r k ω ∧
      Restart.SelectedPath.splitEvent R r k ω)
    (Finset.range n)).symm

/-- A finite split count is measurable at the generation through which all
its split marks have been exposed.  For each `k < n`, the selected-path state is
`F_k`-measurable and its mark is `F_(k+1)`-measurable. -/
theorem splitCount_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun ω => Restart.SelectedPath.splitCount R r n ω) := by
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
          Restart.SelectedPath.isAlive R r k ω ∧
            Restart.SelectedPath.splitEvent R r k ω) := by
    apply (@measurable_finset_iff ℕ (RootIndexed.StepField Root α X) (F n)).2
    intro k
    by_cases hk : k < n
    · have halive : MeasurableSet[F n]
          {ω | Restart.SelectedPath.isAlive R r k ω} :=
        F.mono (Nat.le_of_lt hk) _
          (Restart.SelectedPath.isAlive_measurable R hR r k)
      have hmark : MeasurableSet[F (k + 1)]
          {ω | Restart.SelectedPath.splitEvent R r k ω} := by
        exact (splitBy_measurable R hR).preimage
          (Restart.SelectedPath.mark_adapted R hR r k)
      have hmark' : MeasurableSet[F n]
          {ω | Restart.SelectedPath.splitEvent R r k ω} :=
        F.mono (by omega) _ hmark
      have heq : {ω | k ∈ (Finset.range n).filter fun j =>
            Restart.SelectedPath.isAlive R r j ω ∧
              Restart.SelectedPath.splitEvent R r j ω} =
          {ω | Restart.SelectedPath.isAlive R r k ω} ∩
            {ω | Restart.SelectedPath.splitEvent R r k ω} := by
        ext ω
        change (k ∈ (Finset.range n).filter fun j =>
          Restart.SelectedPath.isAlive R r j ω ∧
            Restart.SelectedPath.splitEvent R r j ω) ↔ _
        rw [Finset.mem_filter, Finset.mem_range]
        simp [hk, Restart.SelectedPath.splitEvent]
      apply toPropMeasurable
      rw [heq]
      exact halive.inter hmark'
    · have heq : {ω | k ∈ (Finset.range n).filter fun j =>
            Restart.SelectedPath.isAlive R r j ω ∧
              Restart.SelectedPath.splitEvent R r j ω} = ∅ := by
        ext ω
        change (k ∈ (Finset.range n).filter fun j =>
          Restart.SelectedPath.isAlive R r j ω ∧
            Restart.SelectedPath.splitEvent R r j ω) ↔ False
        rw [Finset.mem_filter, Finset.mem_range]
        simp [hk]
      apply toPropMeasurable
      rw [heq]
      exact (F n).measurableSet_empty
  change Measurable[F n]
    (fun ω => ((Finset.range n).filter fun k =>
      Restart.SelectedPath.isAlive R r k ω ∧
        Restart.SelectedPath.splitEvent R r k ω).card)
  exact (measurable_of_countable fun s : Finset ℕ => s.card).comp hindices

/-- The `i`-th split-completion on the selected path, with `i` a positive
one-based ordinal.  This is the first generation `n` by which at least `i`
live split marks have been observed. -/
noncomputable def splitCompletion
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (i : ℕ) :
    RootIndexed.StepField Root α X → WithTop ℕ :=
  firstDeclaredSuccess fun n =>
    {ω | i ≤ Restart.SelectedPath.splitCount R r n ω}

/-- Each ordinal split-completion is a stopping time for the domain
filtration.  In particular, the raw look-ahead label of a split is not used
as a stopping time: the count includes the split mark only once it is exposed
at the next generation. -/
theorem splitCompletion_isStoppingTime
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (i : ℕ) :
    IsStoppingTime (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X))
      (Restart.SelectedPath.splitCompletion R r i) := by
  apply firstDeclaredSuccess_isStoppingTime
  intro n
  exact (Restart.SelectedPath.splitCount_measurable R hR r n) measurableSet_Ici

/-- At a split of the selected path, the next continuation prefix is the selected
second-selected-child continuation.  This is the absolute prefix of the recursively
pre-sampled continuation field rooted at that sibling. -/
noncomputable def continuationPrefix
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (k : ℕ)
    (ω : RootIndexed.StepField Root α X) : TreeNode α :=
  Restart.selectedPath R r k ω ++
    [secondSelectedSlot R (ω r (Restart.selectedPath R r k ω))]

/-- The pre-sampled descendant field rooted at the second selected child of the
selected-path split at generation `k`. -/
noncomputable def continuationFieldAtSplit
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (k : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    RootIndexed.StepField PUnit.{1} α X :=
  fun _ u =>
    ω r (Restart.SelectedPath.continuationPrefix R r k ω ++ u)

/-- Path decomposition for the named continuation subtree field. -/
theorem decompose_at_split_field
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (k : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hsplit : Restart.SelectedPath.splitEvent R r k ω) :
    ∀ n, Restart.selectedPath R r (k + 1 + n) ω =
      Restart.SelectedPath.continuationPrefix R r k ω ++
        Restart.selectedPath R PUnit.unit n
          (Restart.SelectedPath.continuationFieldAtSplit R r k ω) := by
  let continuationPrefix := Restart.SelectedPath.continuationPrefix R r k ω
  let continuationField := Restart.SelectedPath.continuationFieldAtSplit R r k ω
  change ∀ n, Restart.selectedPath R r (k + 1 + n) ω =
    continuationPrefix ++ Restart.selectedPath R PUnit.unit n continuationField
  have hprefix : Restart.selectedPath R r (k + 1) ω = continuationPrefix := by
    dsimp [continuationPrefix, Restart.SelectedPath.continuationPrefix]
    exact Restart.SelectedPath.succ_eq_continuationChild_of_split R r k ω
      (by simpa [Restart.SelectedPath.splitEvent, splitBy] using hsplit)
  intro n
  induction n with
  | zero =>
      change Restart.selectedPath R r (k + 1) ω =
        continuationPrefix ++ Restart.selectedPath R PUnit.unit 0 continuationField
      rw [show Restart.selectedPath R PUnit.unit 0 continuationField = [] by rfl,
        List.append_nil]
      exact hprefix
  | succ n ih =>
      have hindex : k + 1 + (n + 1) = (k + 1 + n) + 1 := by omega
      rw [hindex, Restart.selectedPath]
      rw [ih]
      simp [List.append_assoc, Restart.selectedPath, continuationPrefix,
        continuationField, Restart.SelectedPath.continuationPrefix,
        Restart.SelectedPath.continuationFieldAtSplit]

/-- At a split on the selected path, the first-selected-child root selected for the
candidate starts at the first selected child; the selected path continues through the
distinct second selected child. -/
theorem GrowthTrial.root_at_split
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (k : ℕ) (ω : RootIndexed.StepField Root α X)
    (hsplit : Restart.SelectedPath.splitEvent R r k ω) :
    Restart.SelectedPath.GrowthTrial.growthTrialRootAt (Restart.SelectedPath.lineages R hR) R r
        PUnit.unit (k + 1) ω =
      (r, Restart.selectedPath R r k ω ++
        [firstSelectedSlot R (ω r (Restart.selectedPath R r k ω))]) ∧
    firstSelectedSlot R (ω r (Restart.selectedPath R r k ω)) ∈
      R (ω r (Restart.selectedPath R r k ω)) := by
  have h := Restart.SelectedPath.GrowthTrial.growthTrialRootAt_selected (Restart.SelectedPath.lineages R hR)
    R r PUnit.unit (k + 1) ω (by omega) (by
      simpa [Restart.SelectedPath.lineages, Restart.SelectedPath.splitEvent] using hsplit)
  have hroot := Restart.SelectedPath.GrowthTrial.growthTrialRootAt_root (Restart.SelectedPath.lineages R hR)
    R r PUnit.unit (k + 1) ω
  exact ⟨Prod.ext hroot h.1, h.2⟩

/-- A split seen in the recursively defined continuation subtree is exactly the
same split mark in the original pre-sampled tree at the corresponding
absolute selected-path generation. -/
theorem mark_decompose_at_split_field
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (k n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hsplit : Restart.SelectedPath.splitEvent R r k ω) :
    ω r (Restart.selectedPath R r (k + 1 + n) ω) =
      Restart.SelectedPath.continuationFieldAtSplit R r k ω PUnit.unit
        (Restart.selectedPath R PUnit.unit n
          (Restart.SelectedPath.continuationFieldAtSplit R r k ω)) := by
  rw [Restart.SelectedPath.decompose_at_split_field R r k ω hsplit n]
  rfl

/-- Once the selected path is alive at a split, its future alive states are
exactly the alive states of the recursively pre-sampled continuation sibling.
This identifies genuine later candidate roots and excludes totalized phantom
paths after extinction. -/
theorem isAlive_decompose_at_split_field
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (k : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (halive : Restart.SelectedPath.isAlive R r k ω)
    (hsplit : Restart.SelectedPath.splitEvent R r k ω) :
    ∀ n, Restart.SelectedPath.isAlive R r (k + 1 + n) ω ↔
      Restart.SelectedPath.isAlive R PUnit.unit n
        (Restart.SelectedPath.continuationFieldAtSplit R r k ω) := by
  have hcard : 2 ≤ (R (ω r (Restart.selectedPath R r k ω))).card := by
    simpa [Restart.SelectedPath.splitEvent, splitBy] using hsplit
  have hnonempty : (R (ω r (Restart.selectedPath R r k ω))).Nonempty :=
    Finset.card_pos.mp (by omega)
  intro n
  induction n with
  | zero =>
      change (Restart.SelectedPath.isAlive R r k ω ∧
          (R (ω r (Restart.selectedPath R r k ω))).Nonempty) ↔ True
      simp [halive, hnonempty]
  | succ n ih =>
      have hindex : k + 1 + (n + 1) = (k + 1 + n) + 1 := by omega
      rw [hindex]
      change (Restart.SelectedPath.isAlive R r (k + 1 + n) ω ∧
          (R (ω r (Restart.selectedPath R r (k + 1 + n) ω))).Nonempty) ↔
        (Restart.SelectedPath.isAlive R PUnit.unit n
            (Restart.SelectedPath.continuationFieldAtSplit R r k ω) ∧
          (R (Restart.SelectedPath.continuationFieldAtSplit R r k ω PUnit.unit
            (Restart.selectedPath R PUnit.unit n
              (Restart.SelectedPath.continuationFieldAtSplit R r k ω)))).Nonempty)
      rw [ih, Restart.SelectedPath.mark_decompose_at_split_field
        R r k n ω hsplit]

/-- The first-child candidate discovered at an actual global selected-path
split at generation `k + 1 + n` is exactly the first-selected-child root of the
recursively pre-sampled continuation-child subtree.  The alive premise from
`Restart.SelectedPath.isAlive_decompose_at_split_field` ensures this is a real
candidate in the genealogical tree, not a totalized address after extinction.
-/
theorem GrowthTrial.root_at_recursive_split
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (k n : ℕ) (ω : RootIndexed.StepField Root α X)
    (halive : Restart.SelectedPath.isAlive R r k ω)
    (hsplit : Restart.SelectedPath.splitEvent R r k ω)
    (hlocallyAlive : Restart.SelectedPath.isAlive R PUnit.unit n
      (Restart.SelectedPath.continuationFieldAtSplit R r k ω))
    (hlocalsplit :
      Restart.SelectedPath.continuationFieldAtSplit R r k ω PUnit.unit
        (Restart.selectedPath R PUnit.unit n
          (Restart.SelectedPath.continuationFieldAtSplit R r k ω)) ∈ splitBy R) :
    (Restart.SelectedPath.GrowthTrial.growthTrialRootAt (Restart.SelectedPath.lineages R hR) R r
        PUnit.unit (k + 1 + n + 1) ω =
      (r, Restart.SelectedPath.continuationPrefix R r k ω ++
        (Restart.selectedPath R PUnit.unit n
            (Restart.SelectedPath.continuationFieldAtSplit R r k ω) ++
          [firstSelectedSlot R
            (Restart.SelectedPath.continuationFieldAtSplit R r k ω PUnit.unit
              (Restart.selectedPath R PUnit.unit n
                (Restart.SelectedPath.continuationFieldAtSplit R r k ω)))]))) ∧
      Restart.SelectedPath.isAlive R r (k + 1 + n) ω ∧
      firstSelectedSlot R
        (ω r (Restart.selectedPath R r (k + 1 + n) ω)) ∈
          R (ω r (Restart.selectedPath R r (k + 1 + n) ω)) := by
  have hpath := Restart.SelectedPath.decompose_at_split_field
    R r k ω hsplit n
  have hmark := Restart.SelectedPath.mark_decompose_at_split_field
    R r k n ω hsplit
  have hglobalAlive :=
    (Restart.SelectedPath.isAlive_decompose_at_split_field
      R r k ω halive hsplit n).2 hlocallyAlive
  have hglobalSplit :
      Restart.SelectedPath.splitEvent R r (k + 1 + n) ω := by
    change ω r (Restart.selectedPath R r (k + 1 + n) ω) ∈ splitBy R
    rw [hmark]
    exact hlocalsplit
  have hcandidateIsChild := Restart.SelectedPath.GrowthTrial.root_at_split
    R hR r (k + 1 + n) ω hglobalSplit
  have hparentAlive : Restart.SelectedPath.isAlive R r (k + 1 + n) ω := hglobalAlive
  refine ⟨?_, hparentAlive, hcandidateIsChild.2⟩
  calc
    _ = (r, Restart.selectedPath R r (k + 1 + n) ω ++
        [firstSelectedSlot R
          (ω r (Restart.selectedPath R r (k + 1 + n) ω))]) :=
            hcandidateIsChild.1
    _ = (r, Restart.SelectedPath.continuationPrefix R r k ω ++
        (Restart.selectedPath R PUnit.unit n
            (Restart.SelectedPath.continuationFieldAtSplit R r k ω) ++
          [firstSelectedSlot R
            (Restart.SelectedPath.continuationFieldAtSplit R r k ω PUnit.unit
                (Restart.selectedPath R PUnit.unit n
                  (Restart.SelectedPath.continuationFieldAtSplit R r k ω)))])) := by
      rw [hmark, hpath]
      apply congrArg (fun path : TreeNode α => (r, path))
      exact List.append_assoc _ _ _

end ProbabilityTheory.BranchingRandomWalk.Restart.SelectedPath

end
