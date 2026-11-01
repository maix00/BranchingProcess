/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.Subtree
public import Mathlib.Probability.Independence.Basic

import Probability.Process.Filtration.GeneratedByCoordinates

/-!
# Address-coordinate filtrations and fresh descendant randomness for abstract branching steps

## Public declarations

These statements use only the countable product realization of an abstract
`Step`.  They do not depend on a point process enumeration.

For an inspected address set `S`, write `\mathscr F(S)` for the supremum of
the coordinate measurable spaces. The generation past, generation future, and
descendants of `u` are described by

\[\begin{aligned}
\mathscr F(S)
&=\bigvee_{u\in S}\sigma\bigl(\omega\mapsto\omega(u)\bigr),\\
\mathscr F_n^-&=\mathscr F\bigl(\{u:|u|<n\}\bigr),
&\qquad
\mathscr F_n^+=\mathscr F\bigl(\{u:n\le |u|\}\bigr),\\
\operatorname{Desc}(u)&=\{u\mathbin{+\!+}v:v\in\mathrm{TreeNode}\},
&\qquad
\mathscr F(\operatorname{Desc}(u))
=\bigvee_v\sigma\bigl(\omega\mapsto\omega(u\mathbin{+\!+}v)\bigr).
\end{aligned}\]

- `branchingDescendantAddresses u = {v | ∃ w, v = u ++ w}` is the set of
  descendants of address `u`.
- `stepsOnSpace S = ⨆ u ∈ S, stepCoordinateSpace u` is the information on an
  arbitrary inspected address set. The past, future, and descendant spaces
  are its generation- and address-based instances.
- `subtreeStepField_descendant_measurable` and
  `stepDescendantSpace_eq_iSup` identify the information in the subtree at
  `u` with the coordinates in that descendant set.
- `generationSpace_eq_stepPastSpace` identifies the generation-`n` past with
  coordinates of depth below `n`; `step_coordinate_independent` and
  `step_past_future_independent` give independence of disjoint coordinates
  and of the strict past from the future.
- `generation_stepFuture_independent`,
  `generation_stepDescendant_independent`,
  `generation_subtreeStepField_independent`, and
  `fixed_subtreeStepField_event_factorization` state the corresponding
  generation/subtree independence and event factorization results.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



@[instance_reducible] def stepCoordinateSpace {α X : Type*}
    [MeasurableSpace X] (u : TreeNode α) :
    MeasurableSpace (TreeNode α → Step α X) :=
  MeasurableSpace.comap (fun ω => ω u) inferInstance

@[instance_reducible] def stepsOnSpace {α X : Type*}
    [MeasurableSpace X] (s : Set (TreeNode α)) :
    MeasurableSpace (TreeNode α → Step α X) :=
  ⨆ u ∈ s, stepCoordinateSpace u

@[instance_reducible] def stepPastSpace {α X : Type*}
    [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (TreeNode α → Step α X) :=
  stepsOnSpace {u : TreeNode α | u.length < n}

@[instance_reducible] def stepFutureSpace {α X : Type*}
    [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (TreeNode α → Step α X) :=
  stepsOnSpace {u : TreeNode α | n ≤ u.length}

def branchingDescendantAddresses {α : Type*} (u : TreeNode α) : Set (TreeNode α) :=
  {w | ∃ tail : TreeNode α, w = u ++ tail}

@[instance_reducible] def stepDescendantSpace {α X : Type*}
    [MeasurableSpace X] (u : TreeNode α) :
    MeasurableSpace (TreeNode α → Step α X) :=
  stepsOnSpace (branchingDescendantAddresses u)

theorem subtreeStepField_descendant_measurable
    {α X : Type*} [MeasurableSpace X] (u : TreeNode α) :
    Measurable[stepDescendantSpace u]
      (subtreeStepField (X := X) u) := by
  apply (@measurable_pi_iff
    (TreeNode α → Step α X) (TreeNode α)
    (fun _ => Step α X) (stepDescendantSpace u)
    (fun _ => inferInstance) (subtreeStepField (X := X) u)).2
  intro v
  have hle : stepCoordinateSpace (X := X) (u ++ v) ≤
      stepDescendantSpace (X := X) u := by
    exact le_iSup_of_le (u ++ v)
      (le_iSup_of_le ⟨v, rfl⟩ le_rfl)
  have hcoord : Measurable[stepCoordinateSpace (X := X) (u ++ v)]
      (fun ω : TreeNode α → Step α X => ω (u ++ v)) :=
    Measurable.of_comap_le le_rfl
  exact hcoord.mono hle le_rfl

theorem stepDescendantSpace_eq_iSup
    {α X : Type*} [MeasurableSpace X] (u : TreeNode α) :
    stepDescendantSpace (X := X) u =
      ⨆ w ∈ branchingDescendantAddresses u,
        stepCoordinateSpace (X := X) w := by
  simp only [stepDescendantSpace, stepsOnSpace]

theorem generationSpace_eq_stepPastSpace
    {α X : Type*} [MeasurableSpace X] (n : ℕ) :
    generationSpace (M := Step α X) n =
      stepPastSpace n := by
  simp [generationSpace, generationFiltration,
    Filtration.generatedByCoordinates, stepPastSpace, stepsOnSpace,
    stepCoordinateSpace]

theorem step_coordinate_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    iIndep (stepCoordinateSpace (X := X))
      (offspringFieldLaw μ) := by
  exact (offspringFieldLaw_independent μ).iIndep

theorem step_past_future_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ) :
    Indep (stepPastSpace n) (stepFutureSpace n)
      (offspringFieldLaw μ) := by
  change Indep
    (⨆ u ∈ {u : TreeNode α | u.length < n}, stepCoordinateSpace u)
    (⨆ u ∈ {u : TreeNode α | n ≤ u.length}, stepCoordinateSpace u)
    (offspringFieldLaw μ)
  have hle : ∀ u : TreeNode α, stepCoordinateSpace u ≤
      (inferInstance : MeasurableSpace (TreeNode α → Step α X)) :=
    fun u => (measurable_pi_apply u).comap_le
  have hdisj : Disjoint
      {u : TreeNode α | u.length < n} {u : TreeNode α | n ≤ u.length} := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    change u.length < n at hu
    change n ≤ u.length at hv
    exact (not_lt_of_ge hv) hu
  exact indep_iSup_of_disjoint hle
    (step_coordinate_independent μ) hdisj

theorem generation_stepFuture_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ) :
    Indep (generationFiltration (M := Step α X) n)
      (stepFutureSpace n) (offspringFieldLaw μ) := by
  rw [show generationFiltration (M := Step α X) n =
      generationSpace (M := Step α X) n from rfl,
    generationSpace_eq_stepPastSpace]
  exact step_past_future_independent μ n

theorem generation_stepDescendant_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (u : TreeNode α) :
    Indep (generationFiltration (M := Step α X) u.length)
      (stepDescendantSpace u) (offspringFieldLaw μ) := by
  apply indep_of_indep_of_le_right
    (generation_stepFuture_independent μ u.length)
  rw [stepDescendantSpace_eq_iSup]
  apply iSup_le
  intro w
  apply iSup_le
  rintro ⟨v, rfl⟩
  have hdepth : u.length ≤ (u ++ v).length := by simp
  exact le_iSup_of_le (u ++ v) (le_iSup_of_le hdepth le_rfl)

theorem generation_subtreeStepField_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (u : TreeNode α) :
    Indep (generationFiltration (M := Step α X) u.length)
      (MeasurableSpace.comap (subtreeStepField u) inferInstance)
      (offspringFieldLaw μ) :=
  indep_of_indep_of_le_right
    (generation_stepDescendant_independent μ u)
    (subtreeStepField_descendant_measurable u).comap_le

theorem fixed_subtreeStepField_event_factorization
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (u : TreeNode α) (A B : Set (TreeNode α → Step α X))
    (hA : MeasurableSet[generationFiltration (M := Step α X)
      u.length] A)
    (hB : MeasurableSet B) :
    offspringFieldLaw μ (A ∩ subtreeStepField u ⁻¹' B) =
      offspringFieldLaw μ A * offspringFieldLaw μ B := by
  have hB' : MeasurableSet[
      MeasurableSpace.comap (subtreeStepField u) inferInstance]
      (subtreeStepField u ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((generation_subtreeStepField_independent μ u).indepSet_of_measurableSet
    hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply (subtreeStepField_measurable u) hB,
    subtreeStepField_law] at h
  exact h

end ProbabilityTheory.BranchingRandomWalk
