/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Filtration
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law

/-!
# Past and future coordinate spaces for root-indexed fields

The root and child-slot types are arbitrary. Finite multi-root spaces below
are explicit `Root = Fin m`, `α = ℕ` specializations of these domain-flow
objects. Product-coordinate independence is supplied by the root-indexed law.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

namespace RootIndexed

/-- The past and future coordinate spaces of one root-indexed field are
independent under its product law. -/
theorem step_past_future_independent
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] (n : ℕ) :
    Indep (stepFiltration (Root := Root) (α := α) (X := X) n)
      (stepFutureSpace (Root := Root) (α := α) (X := X) n)
      (stepFieldLaw (Root := Root) μ) := by
  have hle : ∀ p : Root × TreeNode α,
      stepCoordinateSpace (X := X) p ≤
        (inferInstance : MeasurableSpace (StepField Root α X)) := by
    intro p
    have hm : Measurable (fun ω : StepField Root α X => ω p.1 p.2) :=
      (measurable_pi_apply p.2 : Measurable
        (fun field : TreeNode α → Step α X => field p.2)).comp
        (measurable_pi_apply p.1 : Measurable
          (fun ω : StepField Root α X => ω p.1))
    exact hm.comap_le
  have hdisj : Disjoint
      {p : Root × TreeNode α | p.2.length < n}
      {p : Root × TreeNode α | n ≤ p.2.length} := by
    apply Set.disjoint_left.mpr
    intro p hp hf
    change p.2.length < n at hp
    change n ≤ p.2.length at hf
    exact (not_lt_of_ge hf) hp
  change Indep
    (RootIndexed.stepGenerationSpace
      (Root := Root) (α := α) (X := X) n)
    (RootIndexed.stepFutureSpace (Root := Root) (α := α) (X := X) n)
    (stepFieldLaw (Root := Root) μ)
  rw [stepGenerationSpace_eq_coordinate_iSup]
  exact indep_iSup_of_disjoint hle
    (stepFieldLaw_coordinates_independent (Root := Root) μ) hdisj

end RootIndexed

/-- The finite multi-root coordinate space is the root-indexed coordinate
space specialized to `Fin m` roots and natural child labels. -/
abbrev multiRootStepCoordinateSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (p : Fin m × 𝕍) : MeasurableSpace (FiniteRootStepField m ℕ X) :=
  RootIndexed.stepCoordinateSpace (Root := Fin m) (α := ℕ) (X := X) p

/-- The finite multi-root past domain is the generation-`n` domain, specialized
to `Fin m` roots and natural child labels. -/
abbrev multiRootStepPastSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (FiniteRootStepField m ℕ X) :=
  RootIndexed.stepGenerationSpace (Root := Fin m) (α := ℕ) (X := X) n

/-- The finite multi-root future domain is the finite specialization of the
general root-indexed future-coordinate space. -/
abbrev multiRootStepFutureSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (FiniteRootStepField m ℕ X) :=
  RootIndexed.stepFutureSpace (Root := Fin m) (α := ℕ) (X := X) n

theorem multiRootStepGenerationSpace_eq_past
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    multiRootStepGenerationSpace (m := m) (X := X) n =
      multiRootStepPastSpace (m := m) (X := X) n := rfl

theorem multiRootStep_coordinates_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ] :
    iIndep (multiRootStepCoordinateSpace (m := m) (X := X))
      (finiteRootStepFieldLaw μ m) :=
  RootIndexed.stepFieldLaw_coordinates_independent μ

theorem multiRootStep_past_future_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) :
    Indep (multiRootStepFiltration (m := m) (X := X) n)
      (multiRootStepFutureSpace (m := m) (X := X) n)
      (finiteRootStepFieldLaw μ m) :=
  RootIndexed.step_past_future_independent μ n

end ProbabilityTheory.BranchingRandomWalk

end
