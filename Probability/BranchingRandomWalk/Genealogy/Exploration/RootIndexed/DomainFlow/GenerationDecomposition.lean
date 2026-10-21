/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily
import Probability.Process.Filtration.GeneratedByCoordinates

/-!
# Decomposition at one generation

The public declarations in `ProbabilityTheory.BranchingRandomWalk.RootIndexed`
are:

- `Generation`: the subtype of rooted addresses $q$ with $|q.2|=n$.
- `Past`: the strict-past coordinate field
  $\{q:|q.2|<n\}\to\operatorname{Step}(\alpha,X)$.
- `StepField.past`: restricts a full field to those strict-past coordinates.
- `generationRoots`: maps each depth-$n$ rooted address to its underlying
  root-address pair; `generationRoots_injective` proves injectivity and
  `generationRoots_depth` records its depth.
- `StepField.glue`: reconstructs the full field by
  $\operatorname{glue}(n,p,f)(r,u)=p(r,u)$ when $|u|<n$, and otherwise uses
  the future field indexed by $(r,u.take(n))$ at suffix $u.drop(n)$.
- `StepField.past_measurable`: the past restriction is measurable with
  respect to `stepFiltration n`.
- `StepField.measurable_stepFiltration_iff_past`: a field-valued map is
  measurable with respect to `stepFiltration n` exactly when its strict-past
  restriction is measurable.
- `StepField.glue_measurable`: reconstruction is measurable as a map from the
  product of the past and future field spaces.
- `StepField.glue_past_subtrees`: for every full field $F$,
  $\operatorname{glue}(n,F.past(n),\operatorname{RootIndexed.subtreeStepFieldVector}
  (\operatorname{generationRoots}(n),F))=F$.

The decomposition uses subtypes for generation and past addresses, so it
requires no default root, slot, mark, or step. It is a domain-flow
decomposition of the coordinate field; the probability-law consequences are
proved in their coupling clients. The measurability declarations assume a
measurable step type; the root and slot types need no finiteness or
countability assumptions.
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
    exact Filtration.measurable_to_generatedByCoordinates
      (fun p : Root × TreeNode α => p.2.length + 1)
      (fun p (ω : RootIndexed.StepField Root α X) => ω p.1 p.2)
      (fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1))
      field n
      (fun p hp => by
        have hdepth : p.2.length < n := Nat.succ_le_iff.mp hp
        let q : {q : RootIndexed.TreeNode Root α // q.2.length < n} :=
          ⟨p, hdepth⟩
        have h := (measurable_pi_apply q).comp hpast
        convert h using 1
        funext ω
        rfl)

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
