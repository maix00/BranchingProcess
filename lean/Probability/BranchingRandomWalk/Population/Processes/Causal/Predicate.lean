import Probability.BranchingRandomWalk.Population.Processes.Causal
import Probability.BranchingRandomWalk.Population.Candidates.RootIndexed

/-!
# Causal populations selected by an observable predicate

This file constructs a killed branching population by retaining precisely the
genuine children that satisfy a generation-dependent observable predicate.
The predicate may inspect the entire generation domain, so it can express
absolute barriers, ancestral tube conditions, and scheduled terminal cuts.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed.CausalFinitePopulation

open Combinatorics.UlamHarris Combinatorics.Branching

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Recursively retain the genuine children satisfying `keep`.  Finiteness of
the retained set is an explicit premise; it is typically discharged from
local finiteness of the offspring point measure in the permitted window. -/
noncomputable def selectedBy
    {Root α X : Type*} [MeasurableSpace X]
    (initial : Finset (RootIndexed.TreeNode Root α))
    (keep : ℕ → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Prop)
    (hfinite : ∀ (n : ℕ)
        (parents : Finset (RootIndexed.TreeNode Root α))
        (field : RootIndexed.StepField Root α X),
      {q | q ∈ RootIndexed.childrenAtGeneration n parents field ∧
        keep (n + 1) field q}.Finite) :
    ℕ → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α)
  | 0, _ => initial
  | n + 1, field =>
      (hfinite n (selectedBy initial keep hfinite n field) field).toFinset

@[simp] theorem selectedBy_zero
    {Root α X : Type*} [MeasurableSpace X]
    (initial : Finset (RootIndexed.TreeNode Root α))
    (keep : ℕ → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Prop)
    (hfinite : ∀ (n : ℕ)
        (parents : Finset (RootIndexed.TreeNode Root α))
        (field : RootIndexed.StepField Root α X),
      {q | q ∈ RootIndexed.childrenAtGeneration n parents field ∧
        keep (n + 1) field q}.Finite)
    (field : RootIndexed.StepField Root α X) :
    selectedBy initial keep hfinite 0 field = initial :=
  rfl

@[simp] theorem mem_selectedBy_succ
    {Root α X : Type*} [MeasurableSpace X]
    (initial : Finset (RootIndexed.TreeNode Root α))
    (keep : ℕ → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Prop)
    (hfinite : ∀ n parents field,
      {q | q ∈ RootIndexed.childrenAtGeneration n parents field ∧
        keep (n + 1) field q}.Finite)
    (n : ℕ) (field : RootIndexed.StepField Root α X)
    (q : RootIndexed.TreeNode Root α) :
    q ∈ selectedBy initial keep hfinite (n + 1) field ↔
      q ∈ RootIndexed.childrenAtGeneration n
        (selectedBy initial keep hfinite n field) field ∧
      keep (n + 1) field q := by
  exact Set.Finite.mem_toFinset _

/-- The recursively filtered population is adapted to the generation domain
when every keep decision is observable at the generation where it is made. -/
theorem selectedBy_adapted
    {Root α X : Type*} [MeasurableSpace X]
    (initial : Finset (RootIndexed.TreeNode Root α))
    (keep : ℕ → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Prop)
    (hfinite : ∀ n parents field,
      {q | q ∈ RootIndexed.childrenAtGeneration n parents field ∧
        keep (n + 1) field q}.Finite)
    (hkeep : ∀ n q, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun field => keep n field q)) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (selectedBy initial keep hfinite n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      let _ : MeasurableSpace (RootIndexed.StepField Root α X) :=
        RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) (n + 1)
      rw [measurable_finset_iff]
      intro q
      simp_rw [mem_selectedBy_succ]
      exact ((measurable_set_mem q).comp
        (RootIndexed.childrenAtGeneration_measurable n
          (selectedBy initial keep hfinite n) ih)).and (hkeep (n + 1) q)

/-- Observable predicate killing produces a causal finite branching
population. -/
noncomputable def ofPredicate
    {Root α X : Type*} [MeasurableSpace X]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (keep : ℕ → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Prop)
    (hfinite : ∀ n parents field,
      {q | q ∈ RootIndexed.childrenAtGeneration n parents field ∧
        keep (n + 1) field q}.Finite)
    (hkeep : ∀ n q, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (fun field => keep n field q)) :
    RootIndexed.CausalFinitePopulation
      (RootIndexed.StepField Root α X) Root α X
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X)) id where
  population := selectedBy initial keep hfinite
  adapted := selectedBy_adapted initial keep hfinite hkeep
  depth := by
    intro n field p hp
    cases n with
    | zero => exact hinitialDepth p hp
    | succ n =>
        exact RootIndexed.childrenAtGeneration_depth n _ field p
          ((mem_selectedBy_succ initial keep hfinite n field p).mp hp).1
  successor := by
    intro n field q hq
    have hchild :=
      ((mem_selectedBy_succ initial keep hfinite n field q).mp hq).1
    have hdepth : ∀ p ∈ selectedBy initial keep hfinite n field,
        p.2.length = n := by
      intro p hp
      cases n with
      | zero => exact hinitialDepth p hp
      | succ n =>
          exact RootIndexed.childrenAtGeneration_depth n _ field p
            ((mem_selectedBy_succ initial keep hfinite n field p).mp hp).1
    rw [RootIndexed.childrenAtGeneration_eq_offspringAddressSet n
      (selectedBy initial keep hfinite n field) field hdepth] at hchild
    obtain ⟨parent, hparent, i, hi, rfl⟩ :=
      Combinatorics.Branching.Selection.Coupling.mem_offspringAddressSet.mp
        hchild
    apply Combinatorics.Branching.Selection.Coupling.mem_offspringAddressSet.mpr
    exact ⟨parent, hparent, i, hi, rfl⟩

/-- Kill every child whose absolute position is outside the prescribed
measurable set for its generation.  The position space and the windows remain
abstract; real intervals are an application. -/
noncomputable def ofPositionSets
    {Root α Mark Position : Type*}
    [MeasurableSpace Mark] [MeasurableSpace Position]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [AddCommMonoid Position] [MeasurableAdd₂ Position]
    (initialPosition : Root → Position) (d : Mark → Position)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (window : ℕ → Set Position) (hwindow : ∀ n, MeasurableSet (window n))
    (hfinite : ∀ (n : ℕ)
        (parents : Finset (RootIndexed.TreeNode Root α))
        (field : RootIndexed.StepField Root α Mark),
      {q | q ∈ RootIndexed.childrenAtGeneration n parents field ∧
        RootIndexed.positionAtGeneration initialPosition d (n + 1)
          q.1 q.2 field ∈ window (n + 1)}.Finite) :
    RootIndexed.CausalFinitePopulation
      (RootIndexed.StepField Root α Mark) Root α Mark
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := Mark)) id := by
  apply ofPredicate (Root := Root) (α := α) (X := Mark)
    initial hinitialDepth
    (fun n field q => RootIndexed.positionAtGeneration initialPosition d n
      q.1 q.2 field ∈ window n) hfinite
  intro n q
  let _ : MeasurableSpace (RootIndexed.StepField Root α Mark) :=
    RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := Mark) n
  apply measurableSet_setOfPred.mp
  exact (RootIndexed.positionAtGeneration_measurable
    initialPosition d hd n q.1 q.2) (hwindow n)

end RootIndexed.CausalFinitePopulation
end ProbabilityTheory.BranchingRandomWalk
