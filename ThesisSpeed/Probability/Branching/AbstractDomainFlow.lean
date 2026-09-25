import ThesisSpeed.Probability.Branching.AbstractProperty
import Mathlib.Probability.Independence.Basic

/-!
# Domain flow and fresh descendant randomness for abstract branching steps

These statements use only the countable product realization of an abstract
`BranchingStep`.  They do not depend on a point process representation.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

@[instance_reducible] def branchingStepCoordinateSpace {X : Type*}
    [MeasurableSpace X] (u : 𝕍) :
    MeasurableSpace (𝕍 → BranchingStep ℕ X) :=
  MeasurableSpace.comap (fun ω => ω u) inferInstance

@[instance_reducible] def branchingStepPastSpace {X : Type*}
    [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (𝕍 → BranchingStep ℕ X) :=
  ⨆ u ∈ {u : 𝕍 | u.length < n}, branchingStepCoordinateSpace u

@[instance_reducible] def branchingStepFutureSpace {X : Type*}
    [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (𝕍 → BranchingStep ℕ X) :=
  ⨆ u ∈ {u : 𝕍 | n ≤ u.length}, branchingStepCoordinateSpace u

@[instance_reducible] def branchingStepDescendantSpace {X : Type*}
    [MeasurableSpace X] (u : 𝕍) :
    MeasurableSpace (𝕍 → BranchingStep ℕ X) :=
  ⨆ v : 𝕍, branchingStepCoordinateSpace (u ++ v)

def branchingDescendantAddresses (u : 𝕍) : Set 𝕍 :=
  {w | ∃ tail : 𝕍, w = u ++ tail}

theorem subtreeStepField_descendant_measurable
    {X : Type*} [MeasurableSpace X] (u : 𝕍) :
    Measurable[branchingStepDescendantSpace u]
      (subtreeStepField (X := X) u) := by
  apply (@measurable_pi_iff
    (𝕍 → BranchingStep ℕ X) 𝕍
    (fun _ => BranchingStep ℕ X) (branchingStepDescendantSpace u)
    (fun _ => inferInstance) (subtreeStepField (X := X) u)).2
  intro v
  have hle : branchingStepCoordinateSpace (X := X) (u ++ v) ≤
      branchingStepDescendantSpace (X := X) u := by
    exact le_iSup (fun v : 𝕍 =>
      branchingStepCoordinateSpace (X := X) (u ++ v)) v
  have hcoord : Measurable[branchingStepCoordinateSpace (X := X) (u ++ v)]
      (fun ω : 𝕍 → BranchingStep ℕ X => ω (u ++ v)) :=
    Measurable.of_comap_le le_rfl
  exact hcoord.mono hle le_rfl

theorem branchingStepDescendantSpace_eq_iSup
    {X : Type*} [MeasurableSpace X] (u : 𝕍) :
    branchingStepDescendantSpace (X := X) u =
      ⨆ w ∈ branchingDescendantAddresses u,
        branchingStepCoordinateSpace (X := X) w := by
  apply le_antisymm
  · apply iSup_le
    intro tail
    exact le_iSup_of_le (u ++ tail)
      (le_iSup_of_le ⟨tail, rfl⟩ le_rfl)
  · apply iSup_le
    intro w
    apply iSup_le
    rintro ⟨tail, rfl⟩
    exact le_iSup (fun tail : 𝕍 =>
      branchingStepCoordinateSpace (u ++ tail)) tail

theorem generationSpace_eq_branchingStepPastSpace
    {X : Type*} [MeasurableSpace X] (n : ℕ) :
    generationSpace (M := BranchingStep ℕ X) n =
      branchingStepPastSpace n := by
  apply le_antisymm
  · unfold generationSpace
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨u, hu, t, ht, rfl⟩
    have hle : branchingStepCoordinateSpace (X := X) u ≤
        branchingStepPastSpace (X := X) n :=
      le_iSup_of_le u (le_iSup_of_le hu le_rfl)
    apply hle
    exact ⟨t, ht, rfl⟩
  · apply iSup_le
    intro u
    apply iSup_le
    intro hu
    exact (mark_measurable_of_depth_lt u n hu).comap_le

theorem branchingStep_coordinate_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ] :
    iIndep (branchingStepCoordinateSpace (X := X))
      (branchingStepFieldLaw μ) := by
  exact (branchingStepFieldLaw_independent μ).iIndep

theorem branchingStep_past_future_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) :
    Indep (branchingStepPastSpace n) (branchingStepFutureSpace n)
      (branchingStepFieldLaw μ) := by
  have hle : ∀ u : 𝕍, branchingStepCoordinateSpace u ≤
      (inferInstance : MeasurableSpace (𝕍 → BranchingStep ℕ X)) :=
    fun u => (measurable_pi_apply u).comap_le
  have hdisj : Disjoint
      {u : 𝕍 | u.length < n} {u : 𝕍 | n ≤ u.length} := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    change u.length < n at hu
    change n ≤ u.length at hv
    exact (not_lt_of_ge hv) hu
  exact indep_iSup_of_disjoint hle
    (branchingStep_coordinate_independent μ) hdisj

theorem generation_branchingStepFuture_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) :
    Indep (generationFiltration (M := BranchingStep ℕ X) n)
      (branchingStepFutureSpace n) (branchingStepFieldLaw μ) := by
  rw [show generationFiltration (M := BranchingStep ℕ X) n =
      generationSpace (M := BranchingStep ℕ X) n from rfl,
    generationSpace_eq_branchingStepPastSpace]
  exact branchingStep_past_future_independent μ n

theorem generation_branchingStepDescendant_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (u : 𝕍) :
    Indep (generationFiltration (M := BranchingStep ℕ X) u.length)
      (branchingStepDescendantSpace u) (branchingStepFieldLaw μ) := by
  apply indep_of_indep_of_le_right
    (generation_branchingStepFuture_independent μ u.length)
  apply iSup_le
  intro v
  have hdepth : u.length ≤ (u ++ v).length := by simp
  exact le_iSup_of_le (u ++ v) (le_iSup_of_le hdepth le_rfl)

theorem generation_subtreeStepField_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (u : 𝕍) :
    Indep (generationFiltration (M := BranchingStep ℕ X) u.length)
      (MeasurableSpace.comap (subtreeStepField u) inferInstance)
      (branchingStepFieldLaw μ) :=
  indep_of_indep_of_le_right
    (generation_branchingStepDescendant_independent μ u)
    (subtreeStepField_descendant_measurable u).comap_le

theorem fixed_subtreeStepField_event_factorization
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (u : 𝕍) (A B : Set (𝕍 → BranchingStep ℕ X))
    (hA : MeasurableSet[generationFiltration (M := BranchingStep ℕ X)
      u.length] A)
    (hB : MeasurableSet B) :
    branchingStepFieldLaw μ (A ∩ subtreeStepField u ⁻¹' B) =
      branchingStepFieldLaw μ A * branchingStepFieldLaw μ B := by
  have hB' : MeasurableSet[
      MeasurableSpace.comap (subtreeStepField u) inferInstance]
      (subtreeStepField u ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((generation_subtreeStepField_independent μ u).indepSet_of_measurableSet
    hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply (subtreeStepField_measurable u) hB,
    subtreeStepField_law] at h
  exact h

end ThesisSpeed
