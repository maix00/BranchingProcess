import ThesisSpeed.Probability.Genealogy.MarkedTree
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

/-! Independent abstract branching-step fields attached to several initial
    roots.  The root label is a coordinate of the same product space, so no
    retrospective resampling is involved. -/
abbrev MultiRootStepField (m : ℕ) (X : Type*) :=
  Fin m → TreeNode → BranchingStep ℕ X

abbrev MultiRootMarkedTree (m : ℕ) (X : Type*) [AddCommMonoid X] :=
  Fin m → BranchingMarkedTree X

def MultiRootMarkedTree.ofStep {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : MultiRootStepField m X) : MultiRootMarkedTree m X :=
  fun i => BranchingMarkedTree.ofStep (step i)

@[simp] theorem MultiRootMarkedTree.ofStep_apply
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : MultiRootStepField m X) (i : Fin m) :
    MultiRootMarkedTree.ofStep step i =
      BranchingMarkedTree.ofStep (step i) := rfl

theorem MultiRootMarkedTree.ofStep_mark
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : MultiRootStepField m X) (i : Fin m) (u : TreeNode) :
    (MultiRootMarkedTree.ofStep step i).mark u =
      branchingTreePathSum (step i) u := by
  rfl

def multiRootNodePosition {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : MultiRootStepField m X) (i : Fin m) (u : TreeNode) : X :=
  branchingTreePathSum (step i) u

@[simp] theorem multiRootNodePosition_nil
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : MultiRootStepField m X) (i : Fin m) :
    multiRootNodePosition step i [] = 0 := by
  exact branchingTreePathSum_nil (step i)

theorem multiRootNodePosition_append_singleton
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : MultiRootStepField m X) (i : Fin m) (u : TreeNode) (j : ℕ) :
    multiRootNodePosition step i (u ++ [j]) =
      multiRootNodePosition step i u +
        branchingStepIncrement (step i u) j := by
  exact branchingTreePathSum_append_singleton (step i) u j

def multiRootAbsolutePosition {m : ℕ} {X : Type*} [AddCommMonoid X]
    (initial : Fin m → X) (step : MultiRootStepField m X)
    (i : Fin m) (u : TreeNode) : X :=
  initial i + multiRootNodePosition step i u

@[simp] theorem multiRootAbsolutePosition_root
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (initial : Fin m → X) (step : MultiRootStepField m X) (i : Fin m) :
    multiRootAbsolutePosition initial step i [] = initial i := by
  simp [multiRootAbsolutePosition]

theorem multiRootAbsolutePosition_append_singleton
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (initial : Fin m → X) (step : MultiRootStepField m X)
    (i : Fin m) (u : TreeNode) (j : ℕ) :
    multiRootAbsolutePosition initial step i (u ++ [j]) =
      multiRootAbsolutePosition initial step i u +
        branchingStepIncrement (step i u) j := by
  simp only [multiRootAbsolutePosition,
    multiRootNodePosition_append_singleton, add_assoc]

noncomputable def multiRootStepFieldLaw
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) (m : ℕ) :
    Measure (MultiRootStepField m X) :=
  Measure.infinitePi (fun _ : Fin m => branchingStepFieldLaw μ)

instance multiRootStepFieldLaw.isProbabilityMeasure
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ] (m : ℕ) :
    IsProbabilityMeasure (multiRootStepFieldLaw μ m) := by
  unfold multiRootStepFieldLaw
  infer_instance

theorem multiRootStepFieldLaw_root_marginal
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin m) :
    (multiRootStepFieldLaw μ m).map (fun ω => ω i) =
      branchingStepFieldLaw μ := by
  simpa [multiRootStepFieldLaw] using
    (Measure.infinitePi_map_eval
      (fun _ : Fin m => branchingStepFieldLaw μ) i)

theorem multiRootStepFieldLaw_coordinate_marginal
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin m) (u : TreeNode) :
    (multiRootStepFieldLaw μ m).map (fun ω => ω i u) = μ := by
  calc
    (multiRootStepFieldLaw μ m).map (fun ω => ω i u) =
        ((multiRootStepFieldLaw μ m).map (fun ω => ω i)).map
          (fun field => field u) := by
            rw [Measure.map_map]
            · rfl
            · exact measurable_pi_apply u
            · exact measurable_pi_apply i
    _ = μ := by rw [multiRootStepFieldLaw_root_marginal μ i,
      branchingStepFieldLaw_coordinate μ u]

theorem multiRootStepFieldLaw_roots_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ] (m : ℕ) :
    iIndepFun (fun i (ω : MultiRootStepField m X) => ω i)
      (multiRootStepFieldLaw μ m) := by
  unfold multiRootStepFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : Fin m => branchingStepFieldLaw μ)
    (X := fun _ => id)
    (fun _ => measurable_id))

end ThesisSpeed
