import ThesisSpeed.Probability.Branching.AbstractProperty
import ThesisSpeed.Probability.Genealogy.MultiRootAbstract

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def multiRootSubtreeStepField {m : ℕ} {X : Type*}
    (i : Fin m) (u : TreeNode) (ω : MultiRootStepField m X) :
    TreeNode → BranchingStep ℕ X :=
  subtreeStepField u (ω i)

theorem multiRootSubtreeStepField_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (i : Fin m) (u : TreeNode) :
    Measurable (multiRootSubtreeStepField (X := X) i u) := by
  exact (subtreeStepField_measurable (X := X) u).comp
    (measurable_pi_apply i)

theorem multiRootSubtreeStepField_law
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (i : Fin m) (u : TreeNode) :
    (multiRootStepFieldLaw μ m).map
        (multiRootSubtreeStepField (X := X) i u) =
      branchingStepFieldLaw μ := by
  calc
    (multiRootStepFieldLaw μ m).map
        (multiRootSubtreeStepField (X := X) i u) =
      ((multiRootStepFieldLaw μ m).map (fun ω => ω i)).map
        (subtreeStepField (X := X) u) := by
          rw [Measure.map_map]
          · rfl
          · exact subtreeStepField_measurable u
          · exact measurable_pi_apply i
    _ = branchingStepFieldLaw μ := by
      rw [multiRootStepFieldLaw_root_marginal μ i,
        subtreeStepField_law μ u]

theorem multiRootSubtreeStepFields_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (root : Fin m → TreeNode) :
    iIndepFun
      (fun i (ω : MultiRootStepField m X) =>
        multiRootSubtreeStepField i (root i) ω)
      (multiRootStepFieldLaw μ m) := by
  exact (multiRootStepFieldLaw_roots_independent μ m).comp
    (fun i => subtreeStepField (X := X) (root i))
    (fun i => subtreeStepField_measurable (X := X) (root i))

theorem multiRootSubtreeStepFields_law
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (root : Fin m → TreeNode) :
    (multiRootStepFieldLaw μ m).map
        (fun ω i => multiRootSubtreeStepField i (root i) ω) =
      Measure.infinitePi (fun _ : Fin m => branchingStepFieldLaw μ) := by
  have hind := multiRootSubtreeStepFields_independent μ root
  have hmeas : ∀ i : Fin m, Measurable
      (fun ω : MultiRootStepField m X =>
        multiRootSubtreeStepField i (root i) ω) := by
    intro i
    exact multiRootSubtreeStepField_measurable i (root i)
  rw [hind.map_fun_eq_infinitePi_map hmeas]
  apply congrArg Measure.infinitePi
  funext i
  exact multiRootSubtreeStepField_law μ i (root i)

theorem multiRootSubtree_position_decomposition
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : MultiRootStepField m X) (i : Fin m)
    (u v : TreeNode) :
    multiRootNodePosition step i (u ++ v) =
      multiRootNodePosition step i u +
        branchingTreePathSum (multiRootSubtreeStepField i u step) v := by
  exact multiRootNodePosition_append step i u v

end ThesisSpeed
