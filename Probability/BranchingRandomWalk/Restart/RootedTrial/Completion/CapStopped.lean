/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.Trial.Basic
public import Probability.BranchingRandomWalk.Restart.Trial.FirstSplit
public import Probability.BranchingRandomWalk.Genealogy.Lineage.MultiRoot
public import Probability.BranchingRandomWalk.Population.Processes.Causal.Basic
public import Probability.BranchingRandomWalk.Population.Processes.Concurrent.Finite
public import Combinatorics.BranchingWalk.Selection.Coupling.Offspring.Address

/-!
# Cap-stopped candidate populations

Every candidate lineage is sampled on the common pre-sampled field and is
started at its observable completion time.  This file supplies a causal
candidate population that is killed immediately after its first cap crossing.
The crossing generation itself is retained: with at most two selected
offspring per parent, it has size at most twice the cap.  The next generation
is empty, so the construction remains a genuine genealogical source process.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris MeasureTheory

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Total spine choice at one vertex. At a split it follows the second
selected child and leaves the first as a candidate; with exactly one selected
child it follows that child. Empty offspring are totalized to `⊥`, so the
generic construction does not assert that a child exists. -/
noncomputable def reserveSpineSlot {α X : Type*} [LinearOrder α]
    [OrderBot α] (R : Step.FiniteSelection α X) (ξ : Step α X) : α :=
  if 2 ≤ (R ξ).card then secondSelectedSlot R ξ else
    if (R ξ).Nonempty then firstSelectedSlot R ξ else ⊥

theorem reserveSpineSlot_mem_of_selected_nonempty {α X : Type*}
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hne : (R ξ).Nonempty) : reserveSpineSlot R ξ ∈ R ξ := by
  by_cases hsplit : 2 ≤ (R ξ).card
  · simp [reserveSpineSlot, hsplit]
    exact (secondSelectedSlot_mem_of_card R ξ hsplit).1
  · simp [reserveSpineSlot, hsplit, hne]
    exact firstSelectedSlot_mem R ξ hne

theorem reserveSpineSlot_eq_second_of_split {α X : Type*}
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hsplit : 2 ≤ (R ξ).card) :
    reserveSpineSlot R ξ = secondSelectedSlot R ξ := by
  simp [reserveSpineSlot, hsplit]

theorem reserveSpineSlot_eq_first_of_singleton {α X : Type*}
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hsingleton : (R ξ).card = 1) :
    reserveSpineSlot R ξ = firstSelectedSlot R ξ := by
  have htwo : ¬ 2 ≤ (R ξ).card := by omega
  have hne : (R ξ).Nonempty := Finset.card_pos.mp (by omega)
  simp [reserveSpineSlot, htwo, hne]

@[simp] theorem reserveSpineSlot_eq_bot_of_selected_empty {α X : Type*}
    [LinearOrder α] [OrderBot α]
    (R : Step.FiniteSelection α X) (ξ : Step α X)
    (hempty : R ξ = ∅) : reserveSpineSlot R ξ = ⊥ := by
  simp [reserveSpineSlot, hempty]

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
      Combinatorics.Branching.Selection.Coupling.childAddress parent
        (firstSelectedSlot R (ω r (selectedReserveSpinePath R r n ω)))
    let reserve : RootIndexed.TreeNode Root α :=
      Combinatorics.Branching.Selection.Coupling.childAddress parent
        (secondSelectedSlot R (ω r (selectedReserveSpinePath R r n ω)))
    candidate ∈ Combinatorics.Branching.Selection.Coupling.offspringAddressSet
        {parent} (fun p => (R (ω p.1 p.2) : Set α)) ∧
      reserve ∈ Combinatorics.Branching.Selection.Coupling.offspringAddressSet
        {parent} (fun p => (R (ω p.1 p.2) : Set α)) ∧
      candidate ≠ reserve ∧
      (r, selectedReserveSpinePath R r (n + 1) ω) = reserve := by
  dsimp only
  let parent : RootIndexed.TreeNode Root α :=
    (r, selectedReserveSpinePath R r n ω)
  let ξ := ω r (selectedReserveSpinePath R r n ω)
  let candidate := Combinatorics.Branching.Selection.Coupling.childAddress
    parent (firstSelectedSlot R ξ)
  let reserve := Combinatorics.Branching.Selection.Coupling.childAddress
    parent (secondSelectedSlot R ξ)
  have hsplitξ : 2 ≤ (R ξ).card := by simpa [ξ] using hsplit
  have hslots := secondSelectedSlot_mem_of_card R ξ hsplitξ
  have hfirst : firstSelectedSlot R ξ ∈ R ξ :=
    firstSelectedSlot_mem R ξ (Finset.card_pos.mp (by omega : 0 < (R ξ).card))
  have hcandidate : candidate ∈
      Combinatorics.Branching.Selection.Coupling.offspringAddressSet
        {parent} (fun p => (R (ω p.1 p.2) : Set α)) := by
    rw [Combinatorics.Branching.Selection.Coupling.mem_offspringAddressSet]
    refine ⟨parent, by simp [parent], firstSelectedSlot R ξ, ?_, rfl⟩
    simpa [parent, ξ] using hfirst
  have hreserve : reserve ∈
      Combinatorics.Branching.Selection.Coupling.offspringAddressSet
        {parent} (fun p => (R (ω p.1 p.2) : Set α)) := by
    rw [Combinatorics.Branching.Selection.Coupling.mem_offspringAddressSet]
    refine ⟨parent, by simp [parent], secondSelectedSlot R ξ, ?_, rfl⟩
    simpa [parent, ξ] using hslots.1
  have hne : candidate ≠ reserve := by
    intro heq
    have hslot : firstSelectedSlot R ξ = secondSelectedSlot R ξ := by
      have hpairs :
          (parent, firstSelectedSlot R ξ) =
            (parent, secondSelectedSlot R ξ) :=
        Combinatorics.Branching.Selection.Coupling.childAddress_joint_injective
          (by simpa [candidate, reserve] using heq)
      exact congrArg Prod.snd hpairs
    exact hslots.2 hslot
  have hspine := selectedReserveSpinePath_succ_eq_second_of_split
    R r n ω (by simpa [ξ] using hsplit)
  refine ⟨hcandidate, hreserve, hne, ?_⟩
  simpa [reserve, parent, Combinatorics.Branching.Selection.Coupling.childAddress]
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
        refine Combinatorics.Branching.Selection.Coupling.mem_offspringAddressSet.mpr
          ⟨(r, selectedReserveSpinePath R r n ω), hparent,
            reserveSpineSlot R (ω r (selectedReserveSpinePath R r n ω)),
            R.subset_support _ _ hedge.2, ?_⟩
        simpa [Combinatorics.Branching.Selection.Coupling.childAddress] using
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

/-- The next state of a selected candidate, killed if its current population
has already crossed `cap`.  The crossing generation is retained, with its
size controlled by the one-step offspring bound. -/
noncomputable def capStoppedStep {α X : Type*} (R : Step.FiniteSelection α X)
    (cap : ℕ) : Finset (TreeNode α) × Mark α (Step α X) → Finset (TreeNode α) :=
  fun p => if cap < p.1.card then ∅ else StepSelection.grow R p.1 p.2

/-- A selected population run from one candidate root and killed after the
first generation whose size exceeds `cap`. -/
noncomputable def capStoppedPopulation {α X : Type*}
    (R : Step.FiniteSelection α X) (cap : ℕ) :
    ℕ → Mark α (Step α X) → Finset (TreeNode α)
  | 0, _ => {[]}
  | n + 1, ω => capStoppedStep R cap
      (capStoppedPopulation R cap n ω, frontierMarks n ω)

@[simp] theorem capStoppedPopulation_zero {α X : Type*}
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (ω : Mark α (Step α X)) : capStoppedPopulation R cap 0 ω = {[]} := rfl

@[simp] theorem capStoppedPopulation_succ {α X : Type*}
    (R : Step.FiniteSelection α X) (cap n : ℕ)
    (ω : Mark α (Step α X)) :
    capStoppedPopulation R cap (n + 1) ω =
      capStoppedStep R cap
        (capStoppedPopulation R cap n ω, frontierMarks n ω) := rfl

theorem capStoppedPopulation_depth {α X : Type*}
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (ω : Mark α (Step α X)) :
    ∀ n u, u ∈ capStoppedPopulation R cap n ω → u.length = n := by
  intro n
  induction n with
  | zero =>
      intro u hu
      simpa [capStoppedPopulation] using hu
  | succ n ih =>
      intro q hq
      simp only [capStoppedPopulation_succ, capStoppedStep] at hq
      split at hq
      · simp at hq
      · obtain ⟨u, hu, i, hi, rfl⟩ :=
          (StepSelection.mem_grow_iff R
            (capStoppedPopulation R cap n ω) (frontierMarks n ω) q).mp hq
        rw [List.length_append, ih u hu]
        simp

theorem capStoppedPopulation_succ_parent {α X : Type*}
    (R : Step.FiniteSelection α X) (cap n : ℕ)
    (ω : Mark α (Step α X)) (q : TreeNode α)
    (hq : q ∈ capStoppedPopulation R cap (n + 1) ω) :
    ∃ u ∈ capStoppedPopulation R cap n ω, ∃ i,
      i ∈ R (ω u) ∧ q = u ++ [i] := by
  simp only [capStoppedPopulation_succ, capStoppedStep] at hq
  split at hq
  · simp at hq
  · obtain ⟨u, hu, i, hi, hqeq⟩ :=
      (StepSelection.mem_grow_iff R
        (capStoppedPopulation R cap n ω) (frontierMarks n ω) q).mp hq
    have hdepth := capStoppedPopulation_depth R cap ω n u hu
    have hfrontier : frontierMarks n ω u = ω u := by
      simp [frontierMarks, hdepth]
    exact ⟨u, hu, i, hfrontier ▸ hi, hqeq⟩

/-- The stopped candidate is measurable at each generation in the domain
filtration.  This proof uses only the measurability of the finite selection;
it does not inspect future success or failure outcomes. -/
theorem capStoppedPopulation_adapted {α X : Type*}
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap : ℕ) :
    ∀ n, Measurable[generationFiltration (M := Step α X) n]
      (capStoppedPopulation R cap n) := by
  refine frontier_causal_state_adapted
    (capStoppedPopulation R cap) (capStoppedStep R cap) ?_ measurable_const ?_
  · classical
    have hcard : Measurable
        (fun p : Finset (TreeNode α) × Mark α (Step α X) => p.1.card) :=
      (measurable_of_countable fun s : Finset (TreeNode α) => s.card).comp
        measurable_fst
    have hcross : MeasurableSet
        {p : Finset (TreeNode α) × Mark α (Step α X) | cap < p.1.card} :=
      hcard measurableSet_Ioi
    exact Measurable.ite hcross measurable_const
      (StepSelection.grow_measurable R hR)
  · intro n ω
    rfl

/-- A two-child rule gives the advertised factor-two bound at every age,
including the first cap-crossing generation. -/
theorem capStoppedPopulation_card_le_two_mul {α X : Type*}
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (hR : R.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (ω : Mark α (Step α X)) :
    ∀ n, (capStoppedPopulation R cap n ω).card ≤ 2 * cap := by
  intro n
  induction n with
  | zero =>
      simp [capStoppedPopulation]
      omega
  | succ n ih =>
      simp only [capStoppedPopulation_succ, capStoppedStep]
      by_cases hcross : cap < (capStoppedPopulation R cap n ω).card
      · simp [hcross]
      · simp [hcross]
        have hprevious : (capStoppedPopulation R cap n ω).card ≤ cap :=
          Nat.le_of_not_gt hcross
        calc
          (StepSelection.grow R (capStoppedPopulation R cap n ω)
              (frontierMarks n ω)).card ≤
              2 * (capStoppedPopulation R cap n ω).card :=
            StepSelection.grow_card_le_mul R 2 hR _ _
          _ ≤ 2 * cap := Nat.mul_le_mul_left 2 hprevious

/-- Once a cap crossing has occurred, the next candidate generation is
empty. -/
theorem capStoppedPopulation_succ_eq_empty_of_crossed {α X : Type*}
    (R : Step.FiniteSelection α X) (cap n : ℕ)
    (ω : Mark α (Step α X))
    (hcross : cap < (capStoppedPopulation R cap n ω).card) :
    capStoppedPopulation R cap (n + 1) ω = ∅ := by
  simp [capStoppedPopulation_succ, capStoppedStep, hcross]

/-- A finite union of concurrently started candidates has size at most the
number of enabled candidates times a uniform per-candidate cap. -/
theorem Concurrent.Finite.population_card_le_enabled_mul_candidateCap
    {Ω I V : Type*} [DecidableEq I] [DecidableEq V]
    (enabled : ℕ → Ω → Finset I)
    (start : I → Ω → WithTop ℕ)
    (candidate : I → ℕ → ℕ → Ω → Finset V)
    (cap n : ℕ) (ω : Ω)
    (hcandidate : ∀ i k age, (candidate i k age ω).card ≤ cap) :
    (Concurrent.Finite.population enabled start candidate n ω).card ≤
      (enabled n ω).card * cap := by
  refine (Concurrent.Finite.population_card_le_sum enabled start candidate n ω).trans ?_
  calc
    (∑ i ∈ enabled n ω,
        (Concurrent.Finite.component start candidate i n ω).card) ≤
      ∑ i ∈ enabled n ω, cap := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases htop : start i ω = ⊤
        · have hlt : (n : WithTop ℕ) < start i ω := by simp [htop]
          rw [Concurrent.Finite.component_eq_empty_of_lt start candidate i ω hlt]
          simp
        · obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
          have hstart : start i ω = (k : WithTop ℕ) := hk.symm
          by_cases hkn : k ≤ n
          · rw [Concurrent.Finite.component_eq_of_start start candidate i ω hkn hstart]
            exact hcandidate i k (n - k)
          · have hlt : (n : WithTop ℕ) < start i ω := by
              rw [hstart]
              exact WithTop.coe_lt_coe.mpr (Nat.lt_of_not_ge hkn)
            rw [Concurrent.Finite.component_eq_empty_of_lt start candidate i ω hlt]
            simp
    _ = (enabled n ω).card * cap := by simp

/-- The cap-stopped trial below a random root address, represented by its
absolute root-indexed genealogical addresses. -/
noncomputable def rootedCapStoppedPopulation
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (root : RootIndexed.TreeNode Root α) (age : ℕ) :
    Finset (RootIndexed.TreeNode Root α) :=
  (capStoppedPopulation R cap age
    (fun u => ω root.1 (root.2 ++ u))).map
      ⟨fun u => (root.1, root.2 ++ u), fun u v huv => by
        have htail : root.2 ++ u = root.2 ++ v := congrArg Prod.snd huv
        exact List.append_cancel_left htail⟩

theorem rootedCapStoppedPopulation_card_le_two_mul
    {Root α X : Type*} [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (hR : R.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (ω : RootIndexed.StepField Root α X)
    (root : RootIndexed.TreeNode Root α) (age : ℕ) :
    (rootedCapStoppedPopulation R cap ω root age).card ≤ 2 * cap := by
  simp only [rootedCapStoppedPopulation, Finset.card_map]
  exact capStoppedPopulation_card_le_two_mul R cap hR hcap
    (fun u => ω root.1 (root.2 ++ u)) age

/-- The rooted stopped population is a genuine source: every retained address
in the next generation is a selected child of a retained current address.
Empty offspring are permitted, including after a cap crossing. -/
theorem rootedCapStoppedPopulation_succ_subset {Root α X : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)] [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (cap n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (root : RootIndexed.TreeNode Root α) :
    ↑(rootedCapStoppedPopulation R cap ω root (n + 1)) ⊆
      Combinatorics.Branching.Selection.Coupling.offspringAddressSet
        (↑(rootedCapStoppedPopulation R cap ω root n))
        (fun p => ↑(R (ω p.1 p.2))) := by
  classical
  rintro ⟨r', q⟩ hq
  simp only [rootedCapStoppedPopulation, Finset.mem_coe, Finset.mem_map] at hq
  obtain ⟨v, hv, hqeq⟩ := hq
  change (root.1, root.2 ++ v) = (r', q) at hqeq
  have hroot : r' = root.1 := by
    exact (congrArg Prod.fst hqeq).symm
  have haddr : q = root.2 ++ v := by
    exact (congrArg Prod.snd hqeq).symm
  subst r'
  subst q
  obtain ⟨u, hu, i, hi, hveq⟩ :=
    capStoppedPopulation_succ_parent R cap n
      (fun u => ω root.1 (root.2 ++ u)) v hv
  refine Combinatorics.Branching.Selection.Coupling.mem_offspringAddressSet.mpr
    ⟨(root.1, root.2 ++ u), ?_, i, ?_, ?_⟩
  · simp only [rootedCapStoppedPopulation, Finset.mem_coe, Finset.mem_map]
    exact ⟨u, hu, rfl⟩
  · exact hi
  · simp [hveq, Combinatorics.Branching.Selection.Coupling.childAddress]

/-- A pre-sampled reserve candidate, rooted at the first selected child of
the split completed at generation `start`.  Its definition is total for
every candidate index and every sample; earlier trial outcomes do not enter
the construction. -/
noncomputable def RootIndexed.ReserveLineages.capStoppedCandidate
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (cap : ℕ) (r : Root) (i : Trial) (start age : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    Finset (RootIndexed.TreeNode Root α) :=
  rootedCapStoppedPopulation growthSelection cap ω
    (lineages.firstChildRootAt splitSelection r i start ω) age

@[simp] theorem rootedCapStoppedPopulation_zero {Root α X : Type*}
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (cap : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (root : RootIndexed.TreeNode Root α) :
    rootedCapStoppedPopulation R cap ω root 0 = {root} := by
  classical
  ext p
  simp only [rootedCapStoppedPopulation, capStoppedPopulation,
    Finset.mem_map, Finset.mem_singleton]
  constructor
  · rintro ⟨u, hu, hpu⟩
    subst u
    change (root.1, root.2 ++ ([] : TreeNode α)) = p at hpu
    calc
      p = (root.1, root.2 ++ ([] : TreeNode α)) := hpu.symm
      _ = root := by cases root <;> simp [List.append_nil]
  · intro hp
    subst p
    refine ⟨[], by simp, ?_⟩
    change (root.1, root.2 ++ ([] : TreeNode α)) = root
    cases root
    simp [List.append_nil]

@[simp] theorem RootIndexed.ReserveLineages.capStoppedCandidate_zero
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (cap : ℕ) (r : Root) (i : Trial) (start : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    lineages.capStoppedCandidate splitSelection growthSelection
      cap r i start 0 ω =
        {lineages.firstChildRootAt splitSelection r i start ω} := by
  simp [RootIndexed.ReserveLineages.capStoppedCandidate]

/-- At an actual split, the age-zero source of the growth candidate is the
first selected child of the reserve parent.  Thus the causal source comparison
at a restart needs that reserve parent in the preceding source population. -/
theorem RootIndexed.ReserveLineages.capStoppedCandidate_zero_selected_child
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (cap : ℕ) (r : Root) (i : Trial) (start : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hstart : 0 < start)
    (hsplit : ω r (lineages.path r i (start - 1) ω) ∈
      splitBy splitSelection) :
    let slot := firstSelectedSlot splitSelection
      (ω r (lineages.path r i (start - 1) ω))
    lineages.capStoppedCandidate splitSelection growthSelection
        cap r i start 0 ω =
      {(r, lineages.path r i (start - 1) ω ++ [slot])} ∧
    slot ∈ splitSelection (ω r (lineages.path r i (start - 1) ω)) := by
  dsimp only
  have hroot := lineages.firstChildRootAt_root splitSelection r i start ω
  obtain ⟨haddress, hslot⟩ := lineages.firstChildRootAt_selected
    splitSelection r i start ω hstart hsplit
  rw [lineages.capStoppedCandidate_zero]
  rw [show lineages.firstChildRootAt splitSelection r i start ω =
      (r, lineages.path r i (start - 1) ω ++
        [firstSelectedSlot splitSelection
          (ω r (lineages.path r i (start - 1) ω))]) by
        exact Prod.ext hroot haddress]
  exact ⟨rfl, hslot⟩

/-- The preceding age-zero lemma applies automatically on every finite
completion `σᵢ`, provided the declaration mark is contained in the selected
split event. -/
theorem RootIndexed.ReserveLineages.capStoppedCandidate_sigma_start_selected_child
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (splitMark : Set (Step α X))
    (hsplitMark : splitMark ⊆ splitBy splitSelection)
    (cap : ℕ) (r : Root) (i : Trial) (n : ℕ)
    (ω : RootIndexed.StepField Root α X)
    (hsigma : lineages.sigma splitMark r i ω = (n + 1 : WithTop ℕ)) :
    let slot := firstSelectedSlot splitSelection
      (ω r (lineages.path r i n ω))
    lineages.capStoppedCandidate splitSelection growthSelection
        cap r i (n + 1) 0 ω = {(r, lineages.path r i n ω ++ [slot])} ∧
    slot ∈ splitSelection (ω r (lineages.path r i n ω)) := by
  have hdecl := (firstDeclaredSuccess_eq_iff
    (RootIndexed.splitDeclaration r (lineages.path r i) splitMark)
    ω (n + 1)).mp hsigma
  have hsplit : ω r (lineages.path r i n ω) ∈ splitBy splitSelection :=
    hsplitMark (by simpa [RootIndexed.splitDeclaration] using hdecl.1)
  simpa using lineages.capStoppedCandidate_zero_selected_child
    splitSelection growthSelection cap r i (n + 1) ω (by omega) hsplit

theorem RootIndexed.ReserveLineages.capStoppedCandidate_card_le_two_mul
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (cap : ℕ) (hR : growthSelection.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (r : Root) (i : Trial) (start age : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    (lineages.capStoppedCandidate splitSelection growthSelection
      cap r i start age ω).card ≤ 2 * cap := by
  exact rootedCapStoppedPopulation_card_le_two_mul growthSelection cap hR hcap
    ω (lineages.firstChildRootAt splitSelection r i start ω) age

/-- The stopped candidate population at a generation-observable random root
is measurable at the corresponding global generation. -/
theorem RootIndexed.capStoppedPopulationAt_selectedRoot_measurable
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap start age : ℕ)
    (chosen : RootIndexed.StepField Root α X → Root × TreeNode α)
    (hchosen : ∀ p, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) start] {ω | chosen ω = p})
    (hcount : (Set.range chosen).Countable)
    (hdepth : ∀ ω, (chosen ω).2.length = start) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (start + age)]
      (fun ω => rootedCapStoppedPopulation R cap ω (chosen ω) age) := by
  classical
  let S : Set (Root × TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  have hfixed (p : S) : Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (start + age)]
      (fun ω => rootedCapStoppedPopulation R cap ω p.1 age) := by
    let subtree : RootIndexed.StepField Root α X → Mark α (Step α X) :=
      fun ω v => ω p.1.1 (p.1.2 ++ v)
    have hsubtree : @Measurable (RootIndexed.StepField Root α X)
        (Mark α (Step α X))
        (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
          (start + age))
        (generationFiltration (M := Step α X) age)
        subtree :=
      RootIndexed.fixedSubtree_measurable_at p.1 start age (by
        obtain ⟨ω, hω⟩ := p.2
        simpa [← hω] using hdepth ω)
    have hlocal := capStoppedPopulation_adapted R hR cap age
    let embed : Finset (TreeNode α) → Finset (RootIndexed.TreeNode Root α) :=
      fun s => s.map ⟨fun u => (p.1.1, p.1.2 ++ u), fun u v huv => by
        have htail : p.1.2 ++ u = p.1.2 ++ v := congrArg Prod.snd huv
        exact List.append_cancel_left htail⟩
    have hembed : Measurable embed := measurable_of_countable embed
    have hlocalMap : Measurable[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) (start + age)]
        (fun ω => capStoppedPopulation R cap age (subtree ω)) :=
      hlocal.comp hsubtree
    have hresult := hembed.comp hlocalMap
    convert hresult using 1
    funext ω
    simp [rootedCapStoppedPopulation, subtree, embed]
  intro t ht
  change MeasurableSet[RootIndexed.stepFiltration
    (Root := Root) (α := α) (X := X) (start + age)]
      {ω | rootedCapStoppedPopulation R cap ω (chosen ω) age ∈ t}
  have heq : {ω | rootedCapStoppedPopulation R cap ω (chosen ω) age ∈ t} =
      ⋃ p : S, {ω | chosen ω = p.1} ∩
        {ω | rootedCapStoppedPopulation R cap ω p.1 age ∈ t} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hω
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩, rfl, hω⟩
    · rintro ⟨p, hp, hω⟩
      simpa [hp] using hω
  rw [heq]
  apply MeasurableSet.iUnion
  intro p
  let F := RootIndexed.stepFiltration (Root := Root) (α := α) (X := X)
  have hfiber : MeasurableSet[F (start + age)] {ω | chosen ω = p.1} :=
    F.mono (Nat.le_add_right start age) _ (hchosen p.1)
  exact hfiber.inter ((hfixed p) ht)

/-- Every reserve candidate has an unconditional completion time `σᵢ`; the
candidate's rooted cap-stopped population is adapted at its global age.  The
look-ahead `τᵢ` is not used as a start time. -/
theorem RootIndexed.ReserveLineages.capStoppedCandidate_adapted
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [MeasurableSpace Root]
    [MeasurableSingletonClass Root]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplit : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (splitMark : Set (Step α X)) (hmark : MeasurableSet splitMark)
    (cap : ℕ) (r : Root) :
    ∀ i k age, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) (k + age)]
      (fun ω => lineages.capStoppedCandidate splitSelection growthSelection
        cap r i k age ω) := by
  intro i k age
  let chosen := lineages.firstChildRootAt splitSelection r i k
  have hchosen := lineages.firstChildRootAt_fiber_measurable
    splitSelection hsplit r i k
  have hcount : (Set.range chosen).Countable := by
    have hnode : (Set.range (fun ω => (chosen ω).2)).Countable :=
      Set.to_countable _
    apply (hnode.image fun u => (r, u)).mono
    rintro p ⟨ω, rfl⟩
    have hroot := lineages.firstChildRootAt_root
      splitSelection r i k ω
    have hp : (r, (chosen ω).2) = chosen ω := by
      apply Prod.ext
      · exact hroot.symm
      · rfl
    exact ⟨(chosen ω).2, ⟨ω, rfl⟩, hp⟩
  have hdepth : ∀ ω, (chosen ω).2.length = k := by
    intro ω
    exact lineages.firstChildRootAt_depth splitSelection r i k ω
  have hmeas := RootIndexed.capStoppedPopulationAt_selectedRoot_measurable
    growthSelection hgrowth cap k age chosen hchosen hcount hdepth
  simpa [chosen, RootIndexed.ReserveLineages.capStoppedCandidate,
    rootedCapStoppedPopulation] using hmeas

/-- The finite union of pre-sampled candidates is adapted when its enabled
index set is observable.  Candidate start times are their unconditional
stopping-time completions `σᵢ`. -/
theorem RootIndexed.ReserveLineages.capStoppedCandidates_adapted
    {Root Trial α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [MeasurableSpace Root]
    [MeasurableSingletonClass Root] [DecidableEq Trial]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (hsplit : Measurable splitSelection.select)
    (hgrowth : Measurable growthSelection.select)
    (splitMark : Set (Step α X)) (hmark : MeasurableSet splitMark)
    (cap : ℕ) (r : Root)
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset Trial)
    (henabled : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | enabled n ω = s})
    (henabledRange : ∀ n, (Set.range (enabled n)).Countable) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun ω => Concurrent.Finite.population enabled
        (fun i => lineages.sigma splitMark r i)
        (fun i k age ω => lineages.capStoppedCandidate
          splitSelection growthSelection cap r i k age ω) n ω) := by
  have hcomponent : ∀ i n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (Concurrent.Finite.component
        (fun i => lineages.sigma splitMark r i)
        (fun i k age ω => lineages.capStoppedCandidate
          splitSelection growthSelection cap r i k age ω) i n) := by
    intro i n
    exact (Concurrent.Finite.component_adapted
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
      (fun i => lineages.sigma splitMark r i)
      (fun i => lineages.sigma_isStoppingTime splitMark hmark r i)
      (fun i k age ω => lineages.capStoppedCandidate
        splitSelection growthSelection cap r i k age ω)
      (fun i k age => lineages.capStoppedCandidate_adapted
        splitSelection growthSelection hsplit hgrowth splitMark hmark cap r i k age)
      i n)
  exact Concurrent.Finite.population_adapted
    (RootIndexed.stepFiltration (Root := Root) (α := α) (X := X))
    enabled
    (fun i => lineages.sigma splitMark r i)
    (fun i k age ω => lineages.capStoppedCandidate
      splitSelection growthSelection cap r i k age ω)
    henabled henabledRange hcomponent

/-- The concurrent family of reserve candidates has at most twice the cap
per enabled candidate. The multiplier `2` comes from the selected rule's
two-child bound at its first crossing generation. -/
theorem RootIndexed.ReserveLineages.capStoppedCandidates_card_le
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq Trial]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (cap : ℕ) (hR : growthSelection.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (r : Root)
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset Trial)
    (n : ℕ) (ω : RootIndexed.StepField Root α X) :
    (Concurrent.Finite.population enabled
      (fun i => lineages.sigma (splitBy splitSelection) r i)
      (fun i k age ω => lineages.capStoppedCandidate splitSelection
        growthSelection cap r i k age ω) n ω).card ≤
      (enabled n ω).card * (2 * cap) := by
  apply Concurrent.Finite.population_card_le_enabled_mul_candidateCap
    enabled
    (fun i => lineages.sigma (splitBy splitSelection) r i)
    (fun i k age ω => lineages.capStoppedCandidate splitSelection
      growthSelection cap r i k age ω)
    (2 * cap) n ω
  intro i k age
  exact lineages.capStoppedCandidate_card_le_two_mul splitSelection
    growthSelection cap hR hcap r i k age ω

/-- A serial restart schedule enables at most one capped candidate at a time.
Combining this with a one-particle reserve spine gives the source-capacity
bound `1 + 2 * cap`; the theorem isolates the exact combinatorial input from
the schedule and branching arguments. -/
theorem RootIndexed.ReserveLineages.serialCapStoppedSource_card_le
    {Root Trial α X : Type*} [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq Trial]
    [DecidableEq (RootIndexed.TreeNode Root α)]
    (lineages : RootIndexed.ReserveLineages Root Trial α X)
    (splitSelection growthSelection : Step.FiniteSelection α X)
    (cap : ℕ) (hR : growthSelection.IsBoundedBy 2) (hcap : 1 ≤ cap)
    (r : Root)
    (enabled : ℕ → RootIndexed.StepField Root α X → Finset Trial)
    (n : ℕ) (ω : RootIndexed.StepField Root α X)
    (reserve : Finset (RootIndexed.TreeNode Root α))
    (hreserve : reserve.card ≤ 1)
    (henabled : (enabled n ω).card ≤ 1) :
    (reserve ∪ Concurrent.Finite.population enabled
      (fun i => lineages.sigma (splitBy splitSelection) r i)
      (fun i k age ω => lineages.capStoppedCandidate splitSelection
        growthSelection cap r i k age ω) n ω).card ≤ 1 + 2 * cap := by
  calc
    (reserve ∪ Concurrent.Finite.population enabled
        (fun i => lineages.sigma (splitBy splitSelection) r i)
        (fun i k age ω => lineages.capStoppedCandidate splitSelection
          growthSelection cap r i k age ω) n ω).card ≤
        reserve.card + (Concurrent.Finite.population enabled
          (fun i => lineages.sigma (splitBy splitSelection) r i)
          (fun i k age ω => lineages.capStoppedCandidate splitSelection
            growthSelection cap r i k age ω) n ω).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + (enabled n ω).card * (2 * cap) := by
      exact Nat.add_le_add hreserve
        (lineages.capStoppedCandidates_card_le splitSelection growthSelection
          cap hR hcap r enabled n ω)
    _ ≤ 1 + 1 * (2 * cap) := Nat.add_le_add_left
      (Nat.mul_le_mul_right (2 * cap) henabled) 1
    _ = 1 + 2 * cap := by simp

/-- The candidate indices whose split has already been observed and whose
fixed growth window is still open.  The split at generation `k` is first
observable at generation `k + 1`; `k < n` enforces that adapted timing. -/
noncomputable def selectedReserveSpineCandidateEnabled
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (duration n : ℕ)
    (ω : RootIndexed.StepField Root α X) : Finset ℕ :=
  (Finset.range n).filter fun k =>
    selectedReserveSpineAlive R r k ω ∧
      (ω r (selectedReserveSpinePath R r k ω) ∈ splitBy R) ∧
      n ≤ k + 1 + duration

/-- The finite concurrent family of cap-stopped first-child trials started
at every split along the pre-sampled reserve spine.  Each index is the
generation of its reserve parent, and its deterministic completion start is
the next generation. -/
noncomputable def selectedReserveSpineCandidatePopulation
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
  Finset (RootIndexed.TreeNode Root α) :=
  Concurrent.Finite.population
    (fun t ω => selectedReserveSpineCandidateEnabled R r duration t ω)
    (fun i _ => ((i + 1 : ℕ) : WithTop ℕ))
    (fun i k age ω =>
      (selectedReserveSpineLineages R hR).capStoppedCandidate
        R growth cap r PUnit.unit k age ω)
    n ω

/-- A finite set of split-parent generations whose child candidates are
within `duration` generations of the current time has at most `duration + 1`
elements.  Send `k` to its remaining age `n - (k + 1)`. -/
theorem card_le_of_generation_window
    {S : Finset ℕ} (n duration : ℕ)
    (hS : ∀ k ∈ S, k < n ∧ n ≤ k + 1 + duration) :
    S.card ≤ duration + 1 := by
  calc
    S.card ≤ (Finset.range (duration + 1)).card := by
      apply Finset.card_le_card_of_injOn (fun k => n - (k + 1))
      · intro k hk
        have h := hS k hk
        have hremaining : n - (k + 1) ≤ duration :=
          Nat.sub_le_iff_le_add.mpr (by omega)
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hremaining)
      · intro a ha b hb hab
        have hka := hS a ha
        have hkb := hS b hb
        have hleft : a + 1 ≤ n := by omega
        have hright : b + 1 ≤ n := by omega
        have hsub : a + 1 = b + 1 :=
          tsub_inj_right hleft hright hab
        omega
    _ = duration + 1 := by simp

theorem selectedReserveSpineCandidateEnabled_card_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (r : Root) (duration n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    (selectedReserveSpineCandidateEnabled R r duration n ω).card ≤
      duration + 1 := by
  apply card_le_of_generation_window n duration
  intro k hk
  simp only [selectedReserveSpineCandidateEnabled, Finset.mem_filter,
    Finset.mem_range] at hk
  exact ⟨hk.1, hk.2.2.2⟩

/-- The concurrently active cap-stopped candidates occupy at most one
`2 * cap` slice per candidate index. -/
theorem selectedReserveSpineCandidatePopulation_card_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (hgrowth : growth.IsBoundedBy 2)
    (hcap : 1 ≤ cap) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    (selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω).card ≤
      (duration + 1) * (2 * cap) := by
  calc
    (selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω).card ≤
        (selectedReserveSpineCandidateEnabled R r duration n ω).card * (2 * cap) := by
      change (Concurrent.Finite.population
        (fun t ω => selectedReserveSpineCandidateEnabled R r duration t ω)
        (fun i _ => ((i + 1 : ℕ) : WithTop ℕ))
        (fun i k age ω =>
          (selectedReserveSpineLineages R hR).capStoppedCandidate
            R growth cap r PUnit.unit k age ω)
        n ω).card ≤
          (selectedReserveSpineCandidateEnabled R r duration n ω).card * (2 * cap)
      apply Concurrent.Finite.population_card_le_enabled_mul_candidateCap
          (fun t ω => selectedReserveSpineCandidateEnabled R r duration t ω)
          (fun i _ => ((i + 1 : ℕ) : WithTop ℕ))
          (fun i k age ω =>
            (selectedReserveSpineLineages R hR).capStoppedCandidate
              R growth cap r PUnit.unit k age ω)
        (2 * cap) n ω
      intro i k age
      exact (selectedReserveSpineLineages R hR).capStoppedCandidate_card_le_two_mul
        R growth cap hgrowth hcap r i k age ω
    _ ≤ (duration + 1) * (2 * cap) :=
      Nat.mul_le_mul_right _
        (selectedReserveSpineCandidateEnabled_card_le R r duration n ω)

/-- The reserve spine together with the recent capped candidates obeys the
`1 + (duration + 1) * 2 * cap` capacity bound, pathwise. -/
theorem selectedReserveSpineAndCandidates_card_le
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [OrderBot α]
    [MeasurableSpace X] [DecidableEq (RootIndexed.TreeNode Root α)]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (cap duration : ℕ) (hgrowth : growth.IsBoundedBy 2)
    (hcap : 1 ≤ cap) (r : Root) (n : ℕ)
    (ω : RootIndexed.StepField Root α X) :
    ((if selectedReserveSpineAlive R r n ω then
        ({(r, selectedReserveSpinePath R r n ω)} : Finset
          (RootIndexed.TreeNode Root α)) else ∅) ∪
      selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω).card ≤
      1 + (duration + 1) * (2 * cap) := by
  calc
    ((if selectedReserveSpineAlive R r n ω then
        ({(r, selectedReserveSpinePath R r n ω)} : Finset
          (RootIndexed.TreeNode Root α)) else ∅) ∪
      selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω).card ≤
        (if selectedReserveSpineAlive R r n ω then
          ({(r, selectedReserveSpinePath R r n ω)} : Finset
            (RootIndexed.TreeNode Root α)) else ∅).card +
          (selectedReserveSpineCandidatePopulation R growth hR cap duration r n ω).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + (duration + 1) * (2 * cap) := by
      refine Nat.add_le_add ?_
        (selectedReserveSpineCandidatePopulation_card_le R growth hR cap duration
          hgrowth hcap r n ω)
      by_cases h : selectedReserveSpineAlive R r n ω <;> simp [h]

end ProbabilityTheory.BranchingRandomWalk

end
