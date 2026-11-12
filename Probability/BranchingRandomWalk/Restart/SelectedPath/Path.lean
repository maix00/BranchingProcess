/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Restart.Trial.Basic
public import Probability.BranchingRandomWalk.Restart.Trial.FirstSplit
public import Probability.BranchingRandomWalk.Restart.SelectedPath.GrowthTrial.Roots
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Lineage
public import Probability.BranchingRandomWalk.Population.Processes.Causal.Basic
public import Combinatorics.BranchingWalk.Population.Offspring
public import Combinatorics.BranchingWalk.Step.Selection.Continuation

/-!
# Selected paths for branching random walks

`Restart.selectedPath` is the path in the selected BRW obtained by applying
the deterministic selection rule at every generation. When at least two
children are selected, the first selected child starts a growth trial and the
second selected child continues the path. The path is defined on the entire
pre-sampled field, independently of growth-trial outcomes.

## Public declarations

Writing (u_n=operatorname{Restart.selectedPath}(R,r,n,omega)), the path is
defined by

\[u_0=[],\qquad
  u_{n+1}=u_n\mathbin{++}
    [\operatorname{selectedContinuationSlot}(R,\omega(r,u_n))],\qquad
  |u_n|=n.\]

At a split, `selectedContinuationSlot` is the second selected child, while the
first selected child roots the growth trial. The split event is
\[
  \operatorname{splitEvent}(R,r,n,\omega)
  \iff \omega(r,u_n)\in\operatorname{splitBy}(R).
\]

The recursive path `Restart.selectedPath R r n ω` has length `n` and follows
selected children while they exist. At a split, its second selected child is
the continuation child, while the first selected child is the growth-trial root.
The path edge theorem and
`Restart.SelectedPath.GrowthTrial.splitEvent_has_growthTrialRoot_and_continuationChild` identify the
distinct first-selected-child and continuation-child addresses at each
actual split.

`Restart.SelectedPath.lineages` packages this path as an adapted lineage.
`Restart.SelectedPath.isAlive` records whether every preceding selected family
is nonempty; `Restart.SelectedPath.lineageSlice` is the corresponding singleton
population, or the empty set after extinction. The public measurability and
adaptedness results cover the path, its mark, and the alive event, while
`Restart.SelectedPath.population` proves that the slice is a causal population
in the domain filtration.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Restart

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory
open Combinatorics.Branching.Step.FiniteSelection

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The address chosen by the selection rule at each generation, defined on the
whole pre-sampled field independently of any growth-trial outcomes. -/
noncomputable def selectedPath {Root α X : Type*}
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) :
    ℕ → RootIndexed.StepField Root α X → TreeNode α
  | 0, _ => []
  | n + 1, ω => selectedPath R r n ω ++
      [selectedContinuationSlot R (ω r (selectedPath R r n ω))]

namespace SelectedPath

/-- The selected BRW has a split at generation `n` when the mark on the
selected path has at least two selected children. -/
def splitEvent {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) : Prop :=
  ω r (Restart.selectedPath R r n ω) ∈ splitBy R

theorem depth {Root α X : Type*}
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root)
    (ω : RootIndexed.StepField Root α X) :
    ∀ n, (Restart.selectedPath R r n ω).length = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [Restart.selectedPath, List.length_append, ih]

theorem succ_selected_of_nonempty
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hne : (R (ω r (Restart.selectedPath R r n ω))).Nonempty) :
    Restart.selectedPath R r (n + 1) ω =
      Restart.selectedPath R r n ω ++
        [selectedContinuationSlot R (ω r (Restart.selectedPath R r n ω))] ∧
      selectedContinuationSlot R (ω r (Restart.selectedPath R r n ω)) ∈
        R (ω r (Restart.selectedPath R r n ω)) := by
  exact ⟨rfl, selectedContinuationSlot_mem_of_selected_nonempty R _ hne⟩

theorem succ_eq_continuationChild_of_split
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hsplit : 2 ≤
      (R (ω r (Restart.selectedPath R r n ω))).card) :
    Restart.selectedPath R r (n + 1) ω =
      Restart.selectedPath R r n ω ++
        [secondSelectedSlot R (ω r (Restart.selectedPath R r n ω))] := by
  rw [Restart.selectedPath, selectedContinuationSlot_eq_second_of_split R _ hsplit]

/-- At a selected-path split, the next continuation vertex and the growth trial from the first selected child root
are distinct selected children of the current one-particle selected-path BRW
population. This is the one-generation frontier inclusion used in the
selected-path coupling. -/
theorem GrowthTrial.splitEvent_has_growthTrialRoot_and_continuationChild
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hsplit : 2 ≤
      (R (ω r (Restart.selectedPath R r n ω))).card) :
    let parent : RootIndexed.TreeNode Root α :=
      (r, Restart.selectedPath R r n ω)
    let candidate : RootIndexed.TreeNode Root α :=
      Combinatorics.UlamHarris.RootIndexed.childAddress parent
        (firstSelectedSlot R (ω r (Restart.selectedPath R r n ω)))
    let continuationChild : RootIndexed.TreeNode Root α :=
      Combinatorics.UlamHarris.RootIndexed.childAddress parent
        (secondSelectedSlot R (ω r (Restart.selectedPath R r n ω)))
    candidate ∈ Combinatorics.Branching.Population.offspringAddressSet
        {parent} (fun p => (R (ω p.1 p.2) : Set α)) ∧
      continuationChild ∈ Combinatorics.Branching.Population.offspringAddressSet
        {parent} (fun p => (R (ω p.1 p.2) : Set α)) ∧
      candidate ≠ continuationChild ∧
      (r, Restart.selectedPath R r (n + 1) ω) = continuationChild := by
  dsimp only
  let parent : RootIndexed.TreeNode Root α :=
    (r, Restart.selectedPath R r n ω)
  let ξ := ω r (Restart.selectedPath R r n ω)
  let candidate := Combinatorics.UlamHarris.RootIndexed.childAddress
    parent (firstSelectedSlot R ξ)
  let continuationChild := Combinatorics.UlamHarris.RootIndexed.childAddress
    parent (secondSelectedSlot R ξ)
  have hsplitξ : 2 ≤ (R ξ).card := by simpa [ξ] using hsplit
  have hslots := secondSelectedSlot_mem_of_card R ξ hsplitξ
  have hfirst : firstSelectedSlot R ξ ∈ R ξ :=
    firstSelectedSlot_mem R ξ (Finset.card_pos.mp (by omega : 0 < (R ξ).card))
  have hcandidate : candidate ∈
      Combinatorics.Branching.Population.offspringAddressSet
        {parent} (fun p => (R (ω p.1 p.2) : Set α)) := by
    rw [Combinatorics.Branching.Population.mem_offspringAddressSet]
    refine ⟨parent, by simp [parent], firstSelectedSlot R ξ, ?_, rfl⟩
    simpa [parent, ξ] using hfirst
  have hcontinuationChild : continuationChild ∈
      Combinatorics.Branching.Population.offspringAddressSet
        {parent} (fun p => (R (ω p.1 p.2) : Set α)) := by
    rw [Combinatorics.Branching.Population.mem_offspringAddressSet]
    refine ⟨parent, by simp [parent], secondSelectedSlot R ξ, ?_, rfl⟩
    simpa [parent, ξ] using hslots.1
  have hne : candidate ≠ continuationChild := by
    intro heq
    have hslot : firstSelectedSlot R ξ = secondSelectedSlot R ξ := by
      have hpairs :
          (parent, firstSelectedSlot R ξ) =
            (parent, secondSelectedSlot R ξ) :=
        Combinatorics.UlamHarris.RootIndexed.childAddress_joint_injective
          (by simpa [candidate, continuationChild] using heq)
      exact congrArg Prod.snd hpairs
    exact hslots.2 hslot
  have hcontinuation := Restart.SelectedPath.succ_eq_continuationChild_of_split
    R r n ω (by simpa [ξ] using hsplit)
  refine ⟨hcandidate, hcontinuationChild, hne, ?_⟩
  simpa [continuationChild, parent, Combinatorics.UlamHarris.RootIndexed.childAddress]
    using congrArg (fun p : TreeNode α => (r, p)) hcontinuation

/-- The totalized selected path uses only selected edges as long as no extinction
has occurred along its prefix. The explicit prefix premise retains the empty
offspring case in the unrestricted model. -/
theorem edges_selected
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hnonempty : ∀ k < n,
      (R (ω r (Restart.selectedPath R r k ω))).Nonempty) :
    ∀ k < n,
      selectedContinuationSlot R (ω r (Restart.selectedPath R r k ω)) ∈
        R (ω r (Restart.selectedPath R r k ω)) := by
  intro k hk
  exact selectedContinuationSlot_mem_of_selected_nonempty R _ (hnonempty k hk)

/-- A recursive selected path is a pre-sampled lineage. It makes the
first/second selected-child choice from each local selected step and totalizes empty
offspring; under the almost-sure nonempty-offspring premise its edges are actual
selected children almost surely. -/
noncomputable def lineages
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) :
    RootIndexed.PreSampledLineages Root PUnit.{1} α X where
  path := fun r _ n ω => Restart.selectedPath R r n ω
  step := fun _ _ p => p.1 ++ [selectedContinuationSlot R p.2]
  measurable_step := by
    intro r i
    have hcard : Measurable (fun ξ : Step α X => (R ξ).card) :=
      (measurable_of_countable fun s : Finset α => s.card).comp hR
    have hsplit : MeasurableSet {ξ : Step α X | 2 ≤ (R ξ).card} :=
      hcard measurableSet_Ici
    have hnonempty : MeasurableSet {ξ : Step α X | 0 < (R ξ).card} :=
      hcard measurableSet_Ioi
    have hfirst : Measurable (firstSelectedSlot R) :=
      firstSelectedSlot_measurable R hR
    have hsecond : Measurable (secondSelectedSlot R) :=
      secondSelectedSlot_measurable R hR
    have hslot : Measurable (selectedContinuationSlot R) := by
      change Measurable (fun ξ : Step α X =>
        if 2 ≤ (R ξ).card then secondSelectedSlot R ξ else
          if (R ξ).Nonempty then firstSelectedSlot R ξ else ⊥)
      have hnonempty' : {ξ : Step α X | (R ξ).Nonempty} =
          {ξ | 0 < (R ξ).card} := by
        ext ξ
        simp [Finset.card_pos]
      have hnonemptyEvent :
          MeasurableSet {ξ : Step α X | (R ξ).Nonempty} := by
        rw [hnonempty']
        exact hnonempty
      exact Measurable.ite hsplit hsecond
        (Measurable.ite hnonemptyEvent hfirst measurable_const)
    have hpair : Measurable (fun p : TreeNode α × Step α X =>
        (p.1, selectedContinuationSlot R p.2)) :=
      measurable_fst.prodMk (hslot.comp measurable_snd)
    have happend : Measurable (fun p : TreeNode α × α => p.1 ++ [p.2]) :=
      measurable_of_countable _
    exact happend.comp hpair
  measurable_root := by
    intro r i
    exact measurable_const
  depth := by
    intro r i n ω
    exact Restart.SelectedPath.depth R r ω n
  recursion := by
    intro r i n ω
    rfl

theorem adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (Restart.selectedPath R r n) := by
  exact (Restart.SelectedPath.lineages R hR).path_adapted r PUnit.unit.{1} n

/-- Whether the totalized selected path is still a genuine lineage at
generation `n`. Once a selected step has no children, this predicate stays
false, so the bottom-slot totalization never creates a phantom lineage. -/
def isAlive {Root α X : Type*} [LinearOrder α]
    [OrderBot α] (R : Step.FiniteSelection α X) (r : Root) :
    ℕ → RootIndexed.StepField Root α X → Prop
  | 0, _ => True
  | n + 1, ω => Restart.SelectedPath.isAlive R r n ω ∧
      (R (ω r (Restart.selectedPath R r n ω))).Nonempty

/-- The one-particle selected-path slice, empty once the totalized path has met
an empty selected offspring family. -/
def lineageSlice {Root α X : Type*} [LinearOrder α]
    [OrderBot α] (R : Step.FiniteSelection α X) (r : Root)
    (n : ℕ) (ω : RootIndexed.StepField Root α X) :
    Set (RootIndexed.TreeNode Root α) :=
  if Restart.SelectedPath.isAlive R r n ω then
    {(r, Restart.selectedPath R r n ω)} else
      (∅ : Set (RootIndexed.TreeNode Root α))

theorem mark_adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (n + 1)]
      (fun ω => ω r (Restart.selectedPath R r n ω)) := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  have hpath : Measurable[F (n + 1)] (Restart.selectedPath R r n) :=
    (Restart.SelectedPath.adapted R hR r n).mono
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) |>.mono
        (Nat.le_succ n)) le_rfl
  let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
    fun ω => (r, Restart.selectedPath R r n ω)
  have hfiber : ∀ p, MeasurableSet[F (n + 1)] {ω | chosen ω = p} := by
    intro p
    by_cases hp : p.1 = r
    · have heq : {ω | chosen ω = p} =
          {ω | Restart.selectedPath R r n ω = p.2} := by
        ext ω
        simp [chosen, Prod.ext_iff, hp, eq_comm]
      rw [heq]
      exact hpath (measurableSet_singleton p.2)
    · have heq : {ω | chosen ω = p} = ∅ := by
        ext ω
        simp [chosen, Prod.ext_iff, hp, eq_comm]
      rw [heq]
      exact (F (n + 1)).measurableSet_empty
  have hdepth : ∀ ω, (Restart.selectedPath R r n ω).length < n + 1 := by
    intro ω
    rw [Restart.SelectedPath.depth R r ω n]
    omega
  have hcount : (Set.range chosen).Countable := by
    have heq : Set.range chosen =
        (fun p : TreeNode α => (r, p)) ''
          Set.range (Restart.selectedPath R r n) := by
      ext p
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨ω, rfl⟩
        exact ⟨Restart.selectedPath R r n ω, ⟨ω, rfl⟩, rfl⟩
      · rintro ⟨u, ⟨ω, rfl⟩, rfl⟩
        exact ⟨ω, rfl⟩
    rw [heq]
    exact (Set.to_countable (Set.range (Restart.selectedPath R r n))).image
      (fun p => (r, p))
  exact RootIndexed.selectedStep_measurable chosen hfiber hdepth hcount

theorem isAlive_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) :
    ∀ n, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      {ω | Restart.SelectedPath.isAlive R r n ω} := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  intro n
  induction n with
  | zero =>
      change MeasurableSet[F 0] Set.univ
      exact MeasurableSet.univ
  | succ n ih =>
      have hprevious : MeasurableSet[F (n + 1)]
          {ω | Restart.SelectedPath.isAlive R r n ω} :=
        F.mono (Nat.le_succ n) _ ih
      have hmark := Restart.SelectedPath.mark_adapted R hR r n
      have hcard : Measurable[F (n + 1)]
          (fun ω => (R (ω r (Restart.selectedPath R r n ω))).card) :=
        (measurable_of_countable fun s : Finset α => s.card).comp
          (hR.comp hmark)
      have hnonempty : MeasurableSet[F (n + 1)]
          {ω | (R (ω r (Restart.selectedPath R r n ω))).Nonempty} := by
        have hpos : MeasurableSet[F (n + 1)]
            {ω | 0 < (R (ω r (Restart.selectedPath R r n ω))).card} :=
          hcard measurableSet_Ioi
        convert hpos using 1
        ext ω
        simp [Finset.card_pos]
      have heq : {ω | Restart.SelectedPath.isAlive R r (n + 1) ω} =
          {ω | Restart.SelectedPath.isAlive R r n ω} ∩
            {ω | (R (ω r (Restart.selectedPath R r n ω))).Nonempty} :=
        rfl
      rw [heq]
      exact hprevious.inter hnonempty

/-- The selected path alone is a causal population in the domain filtration.
It is a singleton while its prefix has nonempty selected offspring, and
becomes empty permanently after extinction. At a split it advances through
the second selected child, leaving the first selected child available as a growth-trial root. -/
noncomputable def population
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α X) Root α X
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) id where
  toPopulation ω := {
    particles := fun n => Restart.SelectedPath.lineageSlice R r n ω
    depth := by
      intro n p hp
      by_cases ha : Restart.SelectedPath.isAlive R r n ω
      · have hp' : p = (r, Restart.selectedPath R r n ω) := by
          simpa [Restart.SelectedPath.lineageSlice, ha] using hp
        rw [hp']
        exact Restart.SelectedPath.depth R r ω n
      · simp [Restart.SelectedPath.lineageSlice, ha] at hp
    successor := by
      intro n q hq
      by_cases ha : Restart.SelectedPath.isAlive R r (n + 1) ω
      · have hactive := ha
        change Restart.SelectedPath.isAlive R r n ω ∧
          (R (ω r (Restart.selectedPath R r n ω))).Nonempty at hactive
        have hq' : q = (r, Restart.selectedPath R r (n + 1) ω) := by
          simpa [Restart.SelectedPath.lineageSlice, ha] using hq
        subst q
        have hedge := Restart.SelectedPath.succ_selected_of_nonempty
          R r n ω hactive.2
        have hparent :
            (r, Restart.selectedPath R r n ω) ∈
              Restart.SelectedPath.lineageSlice R r n ω := by
          simp [Restart.SelectedPath.lineageSlice, hactive.1]
        refine Combinatorics.Branching.Population.mem_offspringAddressSet.mpr
          ⟨(r, Restart.selectedPath R r n ω), hparent,
            selectedContinuationSlot R (ω r (Restart.selectedPath R r n ω)),
            R.subset_support _ _ hedge.2, ?_⟩
        simpa [Combinatorics.UlamHarris.RootIndexed.childAddress] using
          congrArg (fun p : TreeNode α => (r, p)) hedge.1
      · simp [Restart.SelectedPath.lineageSlice, ha] at hq
  }
  adapted := by
    intro p n
    apply measurable_to_prop
    have hactive := Restart.SelectedPath.isAlive_measurable R hR r n
    have hpath := Restart.SelectedPath.adapted R hR r n
    have hmem : MeasurableSet[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n]
        {ω | p ∈ Restart.SelectedPath.lineageSlice R r n ω} := by
      by_cases hroot : p.1 = r
      · have heq : {ω | p ∈ Restart.SelectedPath.lineageSlice R r n ω} =
            {ω | Restart.SelectedPath.isAlive R r n ω} ∩
              {ω | Restart.selectedPath R r n ω = p.2} := by
          ext ω
          simp [Restart.SelectedPath.lineageSlice, hroot, Prod.ext_iff, eq_comm]
        rw [heq]
        exact hactive.inter (hpath (measurableSet_singleton p.2))
      · have heq : {ω | p ∈ Restart.SelectedPath.lineageSlice R r n ω} = ∅ := by
          ext ω
          simp [Restart.SelectedPath.lineageSlice, Prod.ext_iff, hroot]
        rw [heq]
        exact (RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) n).measurableSet_empty
    convert hmem using 1
    ext ω
    simp [Restart.SelectedPath.lineageSlice]

end SelectedPath

end ProbabilityTheory.BranchingRandomWalk.Restart

end
