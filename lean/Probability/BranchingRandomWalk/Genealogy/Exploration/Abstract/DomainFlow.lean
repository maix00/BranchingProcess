import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.Property
import Mathlib.Probability.Independence.Basic

/-!
# Domain flow and fresh descendant randomness for abstract branching steps

These statements use only the countable product realization of an abstract
`Step`.  They do not depend on a point process enumeration.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



@[instance_reducible] def stepCoordinateSpace {α X : Type*}
    [MeasurableSpace X] (u : TreeNode α) :
    MeasurableSpace (TreeNode α → Step α X) :=
  MeasurableSpace.comap (fun ω => ω u) inferInstance

@[instance_reducible] def stepPastSpace {α X : Type*}
    [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (TreeNode α → Step α X) :=
  ⨆ u ∈ {u : TreeNode α | u.length < n}, stepCoordinateSpace u

@[instance_reducible] def stepFutureSpace {α X : Type*}
    [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (TreeNode α → Step α X) :=
  ⨆ u ∈ {u : TreeNode α | n ≤ u.length}, stepCoordinateSpace u

@[instance_reducible] def stepDescendantSpace {α X : Type*}
    [MeasurableSpace X] (u : TreeNode α) :
    MeasurableSpace (TreeNode α → Step α X) :=
  ⨆ v : TreeNode α, stepCoordinateSpace (u ++ v)

def branchingDescendantAddresses {α : Type*} (u : TreeNode α) : Set (TreeNode α) :=
  {w | ∃ tail : TreeNode α, w = u ++ tail}

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
    exact le_iSup (fun v : TreeNode α =>
      stepCoordinateSpace (X := X) (u ++ v)) v
  have hcoord : Measurable[stepCoordinateSpace (X := X) (u ++ v)]
      (fun ω : TreeNode α → Step α X => ω (u ++ v)) :=
    Measurable.of_comap_le le_rfl
  exact hcoord.mono hle le_rfl

theorem stepDescendantSpace_eq_iSup
    {α X : Type*} [MeasurableSpace X] (u : TreeNode α) :
    stepDescendantSpace (X := X) u =
      ⨆ w ∈ branchingDescendantAddresses u,
        stepCoordinateSpace (X := X) w := by
  apply le_antisymm
  · apply iSup_le
    intro tail
    exact le_iSup_of_le (u ++ tail)
      (le_iSup_of_le ⟨tail, rfl⟩ le_rfl)
  · apply iSup_le
    intro w
    apply iSup_le
    rintro ⟨tail, rfl⟩
    exact le_iSup (fun tail : TreeNode α =>
      stepCoordinateSpace (u ++ tail)) tail

theorem generationSpace_eq_stepPastSpace
    {α X : Type*} [MeasurableSpace X] (n : ℕ) :
    generationSpace (M := Step α X) n =
      stepPastSpace n := by
  apply le_antisymm
  · unfold generationSpace
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨u, hu, t, ht, rfl⟩
    have hle : stepCoordinateSpace (X := X) u ≤
        stepPastSpace (X := X) n :=
      le_iSup_of_le u (le_iSup_of_le hu le_rfl)
    apply hle
    exact ⟨t, ht, rfl⟩
  · apply iSup_le
    intro u
    apply iSup_le
    intro hu
    exact (mark_measurable_of_depth_lt u n hu).comap_le

theorem step_coordinate_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] :
    iIndep (stepCoordinateSpace (X := X))
      (stepFieldLaw μ) := by
  exact (stepFieldLaw_independent μ).iIndep

theorem step_past_future_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ) :
    Indep (stepPastSpace n) (stepFutureSpace n)
      (stepFieldLaw μ) := by
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
      (stepFutureSpace n) (stepFieldLaw μ) := by
  rw [show generationFiltration (M := Step α X) n =
      generationSpace (M := Step α X) n from rfl,
    generationSpace_eq_stepPastSpace]
  exact step_past_future_independent μ n

theorem generation_stepDescendant_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (u : TreeNode α) :
    Indep (generationFiltration (M := Step α X) u.length)
      (stepDescendantSpace u) (stepFieldLaw μ) := by
  apply indep_of_indep_of_le_right
    (generation_stepFuture_independent μ u.length)
  apply iSup_le
  intro v
  have hdepth : u.length ≤ (u ++ v).length := by simp
  exact le_iSup_of_le (u ++ v) (le_iSup_of_le hdepth le_rfl)

theorem generation_subtreeStepField_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (u : TreeNode α) :
    Indep (generationFiltration (M := Step α X) u.length)
      (MeasurableSpace.comap (subtreeStepField u) inferInstance)
      (stepFieldLaw μ) :=
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
    stepFieldLaw μ (A ∩ subtreeStepField u ⁻¹' B) =
      stepFieldLaw μ A * stepFieldLaw μ B := by
  have hB' : MeasurableSet[
      MeasurableSpace.comap (subtreeStepField u) inferInstance]
      (subtreeStepField u ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((generation_subtreeStepField_independent μ u).indepSet_of_measurableSet
    hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply (subtreeStepField_measurable u) hB,
    subtreeStepField_law] at h
  exact h

end ProbabilityTheory.BranchingRandomWalk
