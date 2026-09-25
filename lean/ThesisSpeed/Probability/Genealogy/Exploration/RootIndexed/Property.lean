import ThesisSpeed.Probability.Genealogy.Exploration.Abstract.Property
import ThesisSpeed.Probability.Genealogy.RootIndexed.Law

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def multiRootSubtreeStepField {m : ℕ} {X : Type*}
    (i : Fin m) (u : 𝕍) (ω : FiniteRootBranchingStepField m X) :
    𝕍 → BranchingStep ℕ X :=
  subtreeStepField u (ω i)

theorem multiRootSubtreeStepField_measurable
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (i : Fin m) (u : 𝕍) :
    Measurable (multiRootSubtreeStepField (X := X) i u) := by
  exact (subtreeStepField_measurable (X := X) u).comp
    (measurable_pi_apply i)

theorem multiRootSubtreeStepField_law
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (i : Fin m) (u : 𝕍) :
    (finiteRootBranchingStepFieldLaw μ m).map
        (multiRootSubtreeStepField (X := X) i u) =
      branchingStepFieldLaw μ := by
  calc
    (finiteRootBranchingStepFieldLaw μ m).map
        (multiRootSubtreeStepField (X := X) i u) =
      ((finiteRootBranchingStepFieldLaw μ m).map (fun ω => ω i)).map
        (subtreeStepField (X := X) u) := by
          rw [Measure.map_map]
          · rfl
          · exact subtreeStepField_measurable u
          · exact measurable_pi_apply i
    _ = branchingStepFieldLaw μ := by
      rw [finiteRootBranchingStepFieldLaw_root_marginal μ i,
        subtreeStepField_law μ u]

theorem multiRootSubtreeStepFields_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (root : Fin m → 𝕍) :
    iIndepFun
      (fun i (ω : FiniteRootBranchingStepField m X) =>
        multiRootSubtreeStepField i (root i) ω)
      (finiteRootBranchingStepFieldLaw μ m) := by
  exact (finiteRootBranchingStepFieldLaw_roots_independent μ m).comp
    (fun i => subtreeStepField (X := X) (root i))
    (fun i => subtreeStepField_measurable (X := X) (root i))

theorem multiRootSubtreeStepFields_law
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (root : Fin m → 𝕍) :
    (finiteRootBranchingStepFieldLaw μ m).map
        (fun ω i => multiRootSubtreeStepField i (root i) ω) =
      Measure.infinitePi (fun _ : Fin m => branchingStepFieldLaw μ) := by
  have hind := multiRootSubtreeStepFields_independent μ root
  have hmeas : ∀ i : Fin m, Measurable
      (fun ω : FiniteRootBranchingStepField m X =>
        multiRootSubtreeStepField i (root i) ω) := by
    intro i
    exact multiRootSubtreeStepField_measurable i (root i)
  rw [hind.map_fun_eq_infinitePi_map hmeas]
  apply congrArg Measure.infinitePi
  funext i
  exact multiRootSubtreeStepField_law μ i (root i)

theorem multiRootSubtree_position_decomposition
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : FiniteRootBranchingStepField m X) (i : Fin m)
    (u v : 𝕍) :
    rootIndexedBranchingStepAccumulatedMark step i (u ++ v) =
      rootIndexedBranchingStepAccumulatedMark step i u +
        branchingStepAccumulatedMark (multiRootSubtreeStepField i u step) v := by
  exact rootIndexedBranchingStepAccumulatedMark_append step i u v

end ThesisSpeed
