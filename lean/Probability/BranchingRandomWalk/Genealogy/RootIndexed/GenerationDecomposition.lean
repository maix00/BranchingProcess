import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily

/-!
# Decomposition at one generation

A root-indexed step field is equivalently its coordinates strictly before a
generation together with the complete descendant field rooted at every node
of that generation.  Subtypes record the depth conditions, so reconstruction
does not require a default root, slot, mark, or step.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Rooted addresses lying exactly in generation `n`. -/
abbrev RootIndexed.Generation (Root α : Type*) (n : ℕ) :=
  {q : RootIndexed.TreeNode Root α // q.2.length = n}

/-- Coordinates strictly before generation `n`. -/
abbrev RootIndexed.Past (Root α X : Type*) (n : ℕ) :=
  {q : RootIndexed.TreeNode Root α // q.2.length < n} → Step α X

/-- Restrict a complete field to the coordinates strictly before `n`. -/
def RootIndexed.StepField.past
    {Root α X : Type*} (n : ℕ)
    (field : RootIndexed.StepField Root α X) :
    RootIndexed.Past Root α X n :=
  fun q => field q.1.1 q.1.2

/-- The canonical family of all rooted addresses in generation `n`. -/
def RootIndexed.generationRoots
    {Root α : Type*} (n : ℕ) :
    RootIndexed.Generation Root α n → Root × TreeNode α :=
  fun q => q.1

theorem RootIndexed.generationRoots_injective
    {Root α : Type*} (n : ℕ) :
    Function.Injective
      (RootIndexed.generationRoots (Root := Root) (α := α) n) :=
  Subtype.val_injective

@[simp] theorem RootIndexed.generationRoots_depth
    {Root α : Type*} (n : ℕ) (q : RootIndexed.Generation Root α n) :
    (RootIndexed.generationRoots n q).2.length = n :=
  q.2

/-- Reconstruct a complete field from its past and the descendant field at
every generation-`n` rooted address. -/
def RootIndexed.StepField.glue
    {Root α X : Type*} (n : ℕ)
    (past : RootIndexed.Past Root α X n)
    (future : RootIndexed.StepField
      (RootIndexed.Generation Root α n) α X) :
    RootIndexed.StepField Root α X :=
  fun r u =>
    if h : u.length < n then
      past ⟨(r, u), h⟩
    else
      have hn : n ≤ u.length := Nat.le_of_not_gt h
      future
        ⟨(r, u.take n), by simp [List.length_take, Nat.min_eq_left hn]⟩
        (u.drop n)

/-- Restriction to the past is measurable for the generation domain flow. -/
theorem RootIndexed.StepField.past_measurable
    {Root α X : Type*} [MeasurableSpace X] (n : ℕ) :
    @Measurable
      (RootIndexed.StepField Root α X) (RootIndexed.Past Root α X n)
      (RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n) inferInstance
      (RootIndexed.StepField.past (Root := Root) (α := α) (X := X) n) := by
  apply (@measurable_pi_iff
    (RootIndexed.StepField Root α X)
    {q : RootIndexed.TreeNode Root α // q.2.length < n}
    (fun _ => Step α X)
    (RootIndexed.stepFiltration n) (fun _ => inferInstance)
    (RootIndexed.StepField.past n)).2
  intro q
  exact RootIndexed.step_measurable q.1.1 q.1.2 q.2

/-- A field-valued map is measurable into the generation domain exactly when
its restriction to the strict past is measurable.  This identifies the
generated coordinate domain with its concrete `Past` representation. -/
theorem RootIndexed.StepField.measurable_stepFiltration_iff_past
    {Ω Root α X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (n : ℕ) (field : Ω → RootIndexed.StepField Root α X) :
    @Measurable Ω (RootIndexed.StepField Root α X) inferInstance
        (RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) n) field ↔
      Measurable fun ω => (field ω).past n := by
  constructor
  · intro hfield
    exact (RootIndexed.StepField.past_measurable n).comp hfield
  · intro hpast
    apply measurable_generateFrom
    intro s hs
    obtain ⟨r, u, hu, t, ht, rfl⟩ := hs
    have hcoord : Measurable fun ω => (field ω).past n ⟨(r, u), hu⟩ := by
      have h := (measurable_pi_apply ⟨(r, u), hu⟩).comp hpast
      convert h using 1
      funext ω
      rfl
    exact hcoord ht

/-- Gluing is measurable in both arguments. -/
theorem RootIndexed.StepField.glue_measurable
    {Root α X : Type*} [MeasurableSpace X] (n : ℕ) :
    Measurable (Function.uncurry
      (RootIndexed.StepField.glue (Root := Root) (α := α) (X := X) n)) := by
  apply measurable_pi_iff.mpr
  intro r
  apply measurable_pi_iff.mpr
  intro u
  by_cases h : u.length < n
  · change Measurable fun p :
        RootIndexed.Past Root α X n ×
          RootIndexed.StepField (RootIndexed.Generation Root α n) α X =>
        if h' : u.length < n then p.1 ⟨(r, u), h'⟩ else _
    simp only [h, dite_true]
    let q : {q : RootIndexed.TreeNode Root α // q.2.length < n} :=
      ⟨(r, u), h⟩
    exact (measurable_pi_apply q : Measurable
      (fun p : RootIndexed.Past Root α X n => p q)).comp measurable_fst
  · change Measurable fun p :
        RootIndexed.Past Root α X n ×
          RootIndexed.StepField (RootIndexed.Generation Root α n) α X =>
        if h' : u.length < n then _ else
          p.2 ⟨(r, u.take n), _⟩ (u.drop n)
    simp only [h, dite_false]
    fun_prop

/-- Canonical decomposition and reconstruction are inverse. -/
@[simp] theorem RootIndexed.StepField.glue_past_subtrees
    {Root α X : Type*} (n : ℕ)
    (field : RootIndexed.StepField Root α X) :
    RootIndexed.StepField.glue n (field.past n)
        (RootIndexed.subtreeStepFieldVector
          (RootIndexed.generationRoots n) field) =
      field := by
  funext r u
  by_cases h : u.length < n
  · simp [RootIndexed.StepField.glue, RootIndexed.StepField.past, h]
  · have hn : n ≤ u.length := Nat.le_of_not_gt h
    simp only [RootIndexed.StepField.glue, h, dite_false,
      RootIndexed.subtreeStepFieldVector,
      RootIndexed.generationRoots]
    simp [List.take_append_drop]

end ProbabilityTheory.BranchingRandomWalk
