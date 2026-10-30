/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Restart.Trial.Basic
public import Probability.BranchingRandomWalk.Restart.Trial.FirstSplit
public import Probability.BranchingRandomWalk.Restart.Trial.RootIndexed
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Lineage
public import Probability.BranchingRandomWalk.Population.Processes.Causal.Basic
public import Combinatorics.BranchingWalk.Population.Offspring
public import Combinatorics.BranchingWalk.Step.Selection.ReserveSpine

/-!
# Reserve spine paths for selected branching processes

`Combinatorics.Branching.Step.FiniteSelection.reserveSpineSlot` is the
deterministic one-step rule used by the recursive path below.
`selectedReserveSpinePath` follows that rule on the pre-sampled field, and
`selectedReserveSpineLineages` records the corresponding root-indexed
lineages.

The public declarations in ProbabilityTheory.BranchingRandomWalk are
`selectedReserveSpinePath`, `selectedReserveSpinePath_depth`,
selectedReserveSpinePath_succ_selected_of_nonempty,
selectedReserveSpinePath_succ_eq_second_of_split,
selectedReserveSpineSplit_has_candidate_and_reserve_child,
selectedReserveSpinePath_edges_selected, selectedReserveSpineLineages,
selectedReserveSpinePath_adapted, selectedReserveSpineAlive,
selectedReserveSpineSlice, selectedReserveSpineMark_adapted,
selectedReserveSpineAlive_measurable, and selectedReserveSpinePopulation.
The depth relation is
\[
  \operatorname{length}(\operatorname{selectedReserveSpinePath}(n,\omega))=n.
\]
At a split, selectedReserveSpineSplit_has_candidate_and_reserve_child gives
distinct first-child candidate and second-child reserve addresses, and
selectedReserveSpinePath_succ_eq_second_of_split identifies the next path
vertex with the reserve child.

## Public declarations

The recursive path `selectedReserveSpinePath R r n ω` has length `n`, follows
selected children while they exist, and follows the second child at a split.
The path edge theorem and
`selectedReserveSpineSplit_has_candidate_and_reserve_child` identify the
distinct first-child candidate and second-child reserve addresses at each
actual split.

`selectedReserveSpineLineages` packages this path as an adapted lineage.
`selectedReserveSpineAlive` records whether every preceding selected family
is nonempty; `selectedReserveSpineSlice` is the corresponding singleton
population, or the empty set after extinction. The public measurability and
adaptedness results cover the path, its mark, and the alive event, while
`selectedReserveSpinePopulation` proves that the slice is a causal population
in the domain filtration.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory
open Combinatorics.Branching.Step.FiniteSelection

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The address chosen by the reserve rule at each generation, defined on the
whole pre-sampled field independently of any growth-trial outcomes. -/
noncomputable def selectedReserveSpinePath {Root α X : Type*}
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) :
    ℕ → RootIndexed.StepField Root α X → TreeNode α
  | 0, _ => []
  | n + 1, ω => selectedReserveSpinePath R r n ω ++
      [reserveSpineSlot R (ω r (selectedReserveSpinePath R r n ω))]

theorem selectedReserveSpinePath_depth {Root α X : Type*}
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root)
    (ω : RootIndexed.StepField Root α X) :
    ∀ n, (selectedReserveSpinePath R r n ω).length = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [selectedReserveSpinePath, List.length_append, ih]

theorem selectedReserveSpinePath_succ_selected_of_nonempty
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hne : (R (ω r (selectedReserveSpinePath R r n ω))).Nonempty) :
    selectedReserveSpinePath R r (n + 1) ω =
      selectedReserveSpinePath R r n ω ++
        [reserveSpineSlot R (ω r (selectedReserveSpinePath R r n ω))] ∧
      reserveSpineSlot R (ω r (selectedReserveSpinePath R r n ω)) ∈
        R (ω r (selectedReserveSpinePath R r n ω)) := by
  exact ⟨rfl, reserveSpineSlot_mem_of_selected_nonempty R _ hne⟩

theorem selectedReserveSpinePath_succ_eq_second_of_split
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hsplit : 2 ≤
      (R (ω r (selectedReserveSpinePath R r n ω))).card) :
    selectedReserveSpinePath R r (n + 1) ω =
      selectedReserveSpinePath R r n ω ++
        [secondSelectedSlot R (ω r (selectedReserveSpinePath R r n ω))] := by
  rw [selectedReserveSpinePath, reserveSpineSlot_eq_second_of_split R _ hsplit]

/-- At a spine split, the next reserve vertex and the first-child trial root
are distinct selected children of the current singleton reserve source. This
is the one-generation frontier inclusion needed by a causal source coupling. -/
theorem selectedReserveSpineSplit_has_candidate_and_reserve_child
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hsplit : 2 ≤
      (R (ω r (selectedReserveSpinePath R r n ω))).card) :
    let parent : RootIndexed.TreeNode Root α :=
      (r, selectedReserveSpinePath R r n ω)
    let candidate : RootIndexed.TreeNode Root α :=
      Combinatorics.UlamHarris.RootIndexed.childAddress parent
        (firstSelectedSlot R (ω r (selectedReserveSpinePath R r n ω)))
    let reserve : RootIndexed.TreeNode Root α :=
      Combinatorics.UlamHarris.RootIndexed.childAddress parent
        (secondSelectedSlot R (ω r (selectedReserveSpinePath R r n ω)))
    candidate ∈ Combinatorics.Branching.Population.offspringAddressSet
        {parent} (fun p => (R (ω p.1 p.2) : Set α)) ∧
      reserve ∈ Combinatorics.Branching.Population.offspringAddressSet
        {parent} (fun p => (R (ω p.1 p.2) : Set α)) ∧
      candidate ≠ reserve ∧
      (r, selectedReserveSpinePath R r (n + 1) ω) = reserve := by
  dsimp only
  let parent : RootIndexed.TreeNode Root α :=
    (r, selectedReserveSpinePath R r n ω)
  let ξ := ω r (selectedReserveSpinePath R r n ω)
  let candidate := Combinatorics.UlamHarris.RootIndexed.childAddress
    parent (firstSelectedSlot R ξ)
  let reserve := Combinatorics.UlamHarris.RootIndexed.childAddress
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
  have hreserve : reserve ∈
      Combinatorics.Branching.Population.offspringAddressSet
        {parent} (fun p => (R (ω p.1 p.2) : Set α)) := by
    rw [Combinatorics.Branching.Population.mem_offspringAddressSet]
    refine ⟨parent, by simp [parent], secondSelectedSlot R ξ, ?_, rfl⟩
    simpa [parent, ξ] using hslots.1
  have hne : candidate ≠ reserve := by
    intro heq
    have hslot : firstSelectedSlot R ξ = secondSelectedSlot R ξ := by
      have hpairs :
          (parent, firstSelectedSlot R ξ) =
            (parent, secondSelectedSlot R ξ) :=
        Combinatorics.UlamHarris.RootIndexed.childAddress_joint_injective
          (by simpa [candidate, reserve] using heq)
      exact congrArg Prod.snd hpairs
    exact hslots.2 hslot
  have hspine := selectedReserveSpinePath_succ_eq_second_of_split
    R r n ω (by simpa [ξ] using hsplit)
  refine ⟨hcandidate, hreserve, hne, ?_⟩
  simpa [reserve, parent, Combinatorics.UlamHarris.RootIndexed.childAddress]
    using congrArg (fun p : TreeNode α => (r, p)) hspine

/-- The totalized spine path uses only selected edges as long as no extinction
has occurred along its prefix. The explicit prefix premise retains the empty
offspring case in the unrestricted model. -/
theorem selectedReserveSpinePath_edges_selected
    {Root α X : Type*} [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hnonempty : ∀ k < n,
      (R (ω r (selectedReserveSpinePath R r k ω))).Nonempty) :
    ∀ k < n,
      reserveSpineSlot R (ω r (selectedReserveSpinePath R r k ω)) ∈
        R (ω r (selectedReserveSpinePath R r k ω)) := by
  intro k hk
  exact reserveSpineSlot_mem_of_selected_nonempty R _ (hnonempty k hk)

/-- A recursive reserve spine is a pre-sampled lineage. It makes the
first/second-child choice from each local selected step and totalizes empty
offspring; under the almost-sure nonempty-offspring premise its edges are actual
selected children almost surely. -/
noncomputable def selectedReserveSpineLineages
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select) :
    RootIndexed.ReserveLineages Root PUnit.{1} α X where
  path := fun r _ n ω => selectedReserveSpinePath R r n ω
  step := fun _ _ p => p.1 ++ [reserveSpineSlot R p.2]
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
    have hslot : Measurable (reserveSpineSlot R) := by
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
        (p.1, reserveSpineSlot R p.2)) :=
      measurable_fst.prodMk (hslot.comp measurable_snd)
    have happend : Measurable (fun p : TreeNode α × α => p.1 ++ [p.2]) :=
      measurable_of_countable _
    exact happend.comp hpair
  measurable_root := by
    intro r i
    exact measurable_const
  depth := by
    intro r i n ω
    exact selectedReserveSpinePath_depth R r ω n
  recursion := by
    intro r i n ω
    rfl

theorem selectedReserveSpinePath_adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (selectedReserveSpinePath R r n) := by
  exact (selectedReserveSpineLineages R hR).path_adapted r PUnit.unit.{1} n

/-- Whether the totalized reserve path is still a genuine lineage at
generation `n`. Once an empty offspring step occurs, this predicate stays
false, so the bottom-slot totalization never creates a phantom source. -/
def selectedReserveSpineAlive {Root α X : Type*} [LinearOrder α]
    [OrderBot α] (R : Step.FiniteSelection α X) (r : Root) :
    ℕ → RootIndexed.StepField Root α X → Prop
  | 0, _ => True
  | n + 1, ω => selectedReserveSpineAlive R r n ω ∧
      (R (ω r (selectedReserveSpinePath R r n ω))).Nonempty

/-- The one-particle reserve slice, empty once the totalized spine has met an
empty selected offspring family. -/
def selectedReserveSpineSlice {Root α X : Type*} [LinearOrder α]
    [OrderBot α] (R : Step.FiniteSelection α X) (r : Root)
    (n : ℕ) (ω : RootIndexed.StepField Root α X) :
    Set (RootIndexed.TreeNode Root α) :=
  if selectedReserveSpineAlive R r n ω then
    {(r, selectedReserveSpinePath R r n ω)} else
      (∅ : Set (RootIndexed.TreeNode Root α))

theorem selectedReserveSpineMark_adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) (n : ℕ) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (n + 1)]
      (fun ω => ω r (selectedReserveSpinePath R r n ω)) := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  have hpath : Measurable[F (n + 1)] (selectedReserveSpinePath R r n) :=
    (selectedReserveSpinePath_adapted R hR r n).mono
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X) |>.mono
        (Nat.le_succ n)) le_rfl
  let chosen : RootIndexed.StepField Root α X → Root × TreeNode α :=
    fun ω => (r, selectedReserveSpinePath R r n ω)
  have hfiber : ∀ p, MeasurableSet[F (n + 1)] {ω | chosen ω = p} := by
    intro p
    by_cases hp : p.1 = r
    · have heq : {ω | chosen ω = p} =
          {ω | selectedReserveSpinePath R r n ω = p.2} := by
        ext ω
        simp [chosen, Prod.ext_iff, hp, eq_comm]
      rw [heq]
      exact hpath (measurableSet_singleton p.2)
    · have heq : {ω | chosen ω = p} = ∅ := by
        ext ω
        simp [chosen, Prod.ext_iff, hp, eq_comm]
      rw [heq]
      exact (F (n + 1)).measurableSet_empty
  have hdepth : ∀ ω, (selectedReserveSpinePath R r n ω).length < n + 1 := by
    intro ω
    rw [selectedReserveSpinePath_depth R r ω n]
    omega
  have hcount : (Set.range chosen).Countable := by
    have heq : Set.range chosen =
        (fun p : TreeNode α => (r, p)) ''
          Set.range (selectedReserveSpinePath R r n) := by
      ext p
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨ω, rfl⟩
        exact ⟨selectedReserveSpinePath R r n ω, ⟨ω, rfl⟩, rfl⟩
      · rintro ⟨u, ⟨ω, rfl⟩, rfl⟩
        exact ⟨ω, rfl⟩
    rw [heq]
    exact (Set.to_countable (Set.range (selectedReserveSpinePath R r n))).image
      (fun p => (r, p))
  exact RootIndexed.selectedStep_measurable chosen hfiber hdepth hcount

theorem selectedReserveSpineAlive_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) :
    ∀ n, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      {ω | selectedReserveSpineAlive R r n ω} := by
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  intro n
  induction n with
  | zero =>
      change MeasurableSet[F 0] Set.univ
      exact MeasurableSet.univ
  | succ n ih =>
      have hprevious : MeasurableSet[F (n + 1)]
          {ω | selectedReserveSpineAlive R r n ω} :=
        F.mono (Nat.le_succ n) _ ih
      have hmark := selectedReserveSpineMark_adapted R hR r n
      have hcard : Measurable[F (n + 1)]
          (fun ω => (R (ω r (selectedReserveSpinePath R r n ω))).card) :=
        (measurable_of_countable fun s : Finset α => s.card).comp
          (hR.comp hmark)
      have hnonempty : MeasurableSet[F (n + 1)]
          {ω | (R (ω r (selectedReserveSpinePath R r n ω))).Nonempty} := by
        have hpos : MeasurableSet[F (n + 1)]
            {ω | 0 < (R (ω r (selectedReserveSpinePath R r n ω))).card} :=
          hcard measurableSet_Ioi
        convert hpos using 1
        ext ω
        simp [Finset.card_pos]
      have heq : {ω | selectedReserveSpineAlive R r (n + 1) ω} =
          {ω | selectedReserveSpineAlive R r n ω} ∩
            {ω | (R (ω r (selectedReserveSpinePath R r n ω))).Nonempty} :=
        rfl
      rw [heq]
      exact hprevious.inter hnonempty

/-- The reserve spine alone is a causal population in the domain filtration.
It is a singleton while its prefix has nonempty selected offspring, and
becomes empty permanently after extinction. At a split it advances through
the second child, leaving the first child available as a restart candidate. -/
noncomputable def selectedReserveSpinePopulation
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (r : Root) :
    RootIndexed.CausalPopulation
      (RootIndexed.StepField Root α X) Root α X
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)) id where
  toPopulation ω := {
    particles := fun n => selectedReserveSpineSlice R r n ω
    depth := by
      intro n p hp
      by_cases ha : selectedReserveSpineAlive R r n ω
      · have hp' : p = (r, selectedReserveSpinePath R r n ω) := by
          simpa [selectedReserveSpineSlice, ha] using hp
        rw [hp']
        exact selectedReserveSpinePath_depth R r ω n
      · simp [selectedReserveSpineSlice, ha] at hp
    successor := by
      intro n q hq
      by_cases ha : selectedReserveSpineAlive R r (n + 1) ω
      · have hactive := ha
        change selectedReserveSpineAlive R r n ω ∧
          (R (ω r (selectedReserveSpinePath R r n ω))).Nonempty at hactive
        have hq' : q = (r, selectedReserveSpinePath R r (n + 1) ω) := by
          simpa [selectedReserveSpineSlice, ha] using hq
        subst q
        have hedge := selectedReserveSpinePath_succ_selected_of_nonempty
          R r n ω hactive.2
        have hparent :
            (r, selectedReserveSpinePath R r n ω) ∈
              selectedReserveSpineSlice R r n ω := by
          simp [selectedReserveSpineSlice, hactive.1]
        refine Combinatorics.Branching.Population.mem_offspringAddressSet.mpr
          ⟨(r, selectedReserveSpinePath R r n ω), hparent,
            reserveSpineSlot R (ω r (selectedReserveSpinePath R r n ω)),
            R.subset_support _ _ hedge.2, ?_⟩
        simpa [Combinatorics.UlamHarris.RootIndexed.childAddress] using
          congrArg (fun p : TreeNode α => (r, p)) hedge.1
      · simp [selectedReserveSpineSlice, ha] at hq
  }
  adapted := by
    intro p n
    apply measurable_to_prop
    have hactive := selectedReserveSpineAlive_measurable R hR r n
    have hpath := selectedReserveSpinePath_adapted R hR r n
    have hmem : MeasurableSet[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n]
        {ω | p ∈ selectedReserveSpineSlice R r n ω} := by
      by_cases hroot : p.1 = r
      · have heq : {ω | p ∈ selectedReserveSpineSlice R r n ω} =
            {ω | selectedReserveSpineAlive R r n ω} ∩
              {ω | selectedReserveSpinePath R r n ω = p.2} := by
          ext ω
          simp [selectedReserveSpineSlice, hroot, Prod.ext_iff, eq_comm]
        rw [heq]
        exact hactive.inter (hpath (measurableSet_singleton p.2))
      · have heq : {ω | p ∈ selectedReserveSpineSlice R r n ω} = ∅ := by
          ext ω
          simp [selectedReserveSpineSlice, Prod.ext_iff, hroot]
        rw [heq]
        exact (RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) n).measurableSet_empty
    convert hmem using 1
    ext ω
    simp [selectedReserveSpineSlice]

end ProbabilityTheory.BranchingRandomWalk

end
