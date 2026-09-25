import ThesisSpeed.Probability.Genealogy.BranchingPositions
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

/-! Independent abstract branching-step fields attached to finitely many
    initial roots.  This is the `Fin m` specialization of the root-indexed
    field defined in `MarkedTree`. -/

abbrev MultiRootMarkedTree (m : ℕ) (X : Type*) [AddCommMonoid X] :=
  Fin m → BranchingMarkedTree X

def MultiRootMarkedTree.ofStep {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : FiniteRootBranchingStepField m X) : MultiRootMarkedTree m X :=
  fun i => BranchingMarkedTree.ofStep (step i)

@[simp] theorem MultiRootMarkedTree.ofStep_apply
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : FiniteRootBranchingStepField m X) (i : Fin m) :
    MultiRootMarkedTree.ofStep step i =
      BranchingMarkedTree.ofStep (step i) := rfl

theorem MultiRootMarkedTree.ofStep_mark
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : FiniteRootBranchingStepField m X) (i : Fin m) (u : TreeNode) :
    (MultiRootMarkedTree.ofStep step i).mark u =
      branchingTreePathSum (step i) u := by
  rfl

def multiRootNodePosition {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : FiniteRootBranchingStepField m X) (i : Fin m) (u : TreeNode) : X :=
  branchingTreePathSum (step i) u

@[simp] theorem multiRootNodePosition_nil
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : FiniteRootBranchingStepField m X) (i : Fin m) :
    multiRootNodePosition step i [] = 0 := by
  exact branchingTreePathSum_nil (step i)

theorem multiRootNodePosition_append_singleton
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : FiniteRootBranchingStepField m X) (i : Fin m) (u : TreeNode) (j : ℕ) :
    multiRootNodePosition step i (u ++ [j]) =
      multiRootNodePosition step i u +
        branchingStepIncrement (step i u) j := by
  exact branchingTreePathSum_append_singleton (step i) u j

def multiRootAbsolutePosition {m : ℕ} {X : Type*} [AddCommMonoid X]
    (initial : Fin m → X) (step : FiniteRootBranchingStepField m X)
    (i : Fin m) (u : TreeNode) : X :=
  initial i + multiRootNodePosition step i u

theorem multiRootAbsolutePosition_eq_initial_add_mark
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (initial : Fin m → X) (step : FiniteRootBranchingStepField m X)
    (i : Fin m) (u : TreeNode) :
    multiRootAbsolutePosition initial step i u =
      initial i + (MultiRootMarkedTree.ofStep step i).mark u := by
  rfl

@[simp] theorem multiRootAbsolutePosition_root
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (initial : Fin m → X) (step : FiniteRootBranchingStepField m X) (i : Fin m) :
    multiRootAbsolutePosition initial step i [] = initial i := by
  simp [multiRootAbsolutePosition]

theorem multiRootAbsolutePosition_append_singleton
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (initial : Fin m → X) (step : FiniteRootBranchingStepField m X)
    (i : Fin m) (u : TreeNode) (j : ℕ) :
    multiRootAbsolutePosition initial step i (u ++ [j]) =
      multiRootAbsolutePosition initial step i u +
        branchingStepIncrement (step i u) j := by
  simp only [multiRootAbsolutePosition,
    multiRootNodePosition_append_singleton, add_assoc]

theorem multiRootAbsolutePosition_append_two
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (initial : Fin m → X) (step : FiniteRootBranchingStepField m X)
    (i : Fin m) (u : TreeNode) (j k : ℕ) :
    multiRootAbsolutePosition initial step i (u ++ [j, k]) =
      multiRootAbsolutePosition initial step i u +
        branchingStepIncrement (step i u) j +
        branchingStepIncrement (step i (u ++ [j])) k := by
  unfold multiRootAbsolutePosition multiRootNodePosition
  rw [branchingTreePathSum_append_two]
  simp only [add_assoc]

theorem multiRootNodePosition_append
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (step : FiniteRootBranchingStepField m X) (i : Fin m)
    (u v : TreeNode) :
    multiRootNodePosition step i (u ++ v) =
      multiRootNodePosition step i u +
        branchingTreePathSum (fun w => step i (u ++ w)) v := by
  exact branchingTreePathSum_append (step i) u v

theorem multiRootAbsolutePosition_append
    {m : ℕ} {X : Type*} [AddCommMonoid X]
    (initial : Fin m → X) (step : FiniteRootBranchingStepField m X)
    (i : Fin m) (u v : TreeNode) :
    multiRootAbsolutePosition initial step i (u ++ v) =
      multiRootAbsolutePosition initial step i u +
        branchingTreePathSum (fun w => step i (u ++ w)) v := by
  unfold multiRootAbsolutePosition
  rw [multiRootNodePosition_append]
  simp only [add_assoc]

def multiRootRealizedNode {m : ℕ} {X : Type*}
    (step : FiniteRootBranchingStepField m X) (i : Fin m) (u : TreeNode) : Prop :=
  branchingRealizedNode (step i) u

@[simp] theorem multiRootRealizedNode_nil
    {m : ℕ} {X : Type*} (step : FiniteRootBranchingStepField m X) (i : Fin m) :
    multiRootRealizedNode step i [] := by
  exact branchingRealizedNode_nil (step i)

theorem multiRootRealizedNode_append_iff
    {m : ℕ} {X : Type*} (step : FiniteRootBranchingStepField m X)
    (i : Fin m) (u v : TreeNode) :
    multiRootRealizedNode step i (u ++ v) ↔
      multiRootRealizedNode step i u ∧
        branchingRealizedNode (fun w => step i (u ++ w)) v := by
  exact branchingRealizedNode_append_iff (step i) u v

noncomputable abbrev finiteRootBranchingStepFieldLaw
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) (m : ℕ) :
    Measure (FiniteRootBranchingStepField m X) :=
  rootIndexedBranchingStepFieldLaw (Root := Fin m) μ

theorem countableRootBranchingStepFieldLaw_first
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (m : ℕ) :
    (rootIndexedBranchingStepFieldLaw (Root := ℕ) μ).map
        (RootIndexedBranchingStepField.first m) =
      finiteRootBranchingStepFieldLaw μ m := by
  exact rootIndexedBranchingStepFieldLaw_reindex μ
    (fun i : Fin m => i.val) Fin.val_injective

theorem finiteRootBranchingStepFieldLaw_first
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {m n : ℕ} (h : m ≤ n) :
    (finiteRootBranchingStepFieldLaw μ n).map
        (FiniteRootBranchingStepField.first h) =
      finiteRootBranchingStepFieldLaw μ m := by
  exact rootIndexedBranchingStepFieldLaw_reindex μ
    (Fin.castLE h) (fun a b hij =>
      Fin.ext (congrArg (fun z : Fin n => z.val) hij))

theorem finiteRootBranchingStepFieldLaw_root_marginal
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin m) :
    (finiteRootBranchingStepFieldLaw μ m).map (fun ω => ω i) =
      branchingStepFieldLaw μ := by
  simpa [finiteRootBranchingStepFieldLaw,
    rootIndexedBranchingStepFieldLaw] using
    (Measure.infinitePi_map_eval
      (fun _ : Fin m => branchingStepFieldLaw μ) i)

theorem finiteRootBranchingStepFieldLaw_coordinate_marginal
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {m : ℕ} (i : Fin m) (u : TreeNode) :
    (finiteRootBranchingStepFieldLaw μ m).map (fun ω => ω i u) = μ := by
  calc
    (finiteRootBranchingStepFieldLaw μ m).map (fun ω => ω i u) =
        ((finiteRootBranchingStepFieldLaw μ m).map (fun ω => ω i)).map
          (fun field => field u) := by
            rw [Measure.map_map]
            · rfl
            · exact measurable_pi_apply u
            · exact measurable_pi_apply i
    _ = μ := by rw [finiteRootBranchingStepFieldLaw_root_marginal μ i,
      branchingStepFieldLaw_coordinate μ u]

theorem finiteRootBranchingStepFieldLaw_roots_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ] (m : ℕ) :
    iIndepFun (fun i (ω : FiniteRootBranchingStepField m X) => ω i)
      (finiteRootBranchingStepFieldLaw μ m) := by
  unfold finiteRootBranchingStepFieldLaw rootIndexedBranchingStepFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : Fin m => branchingStepFieldLaw μ)
    (X := fun _ => id)
    (fun _ => measurable_id))

theorem finiteRootBranchingStepFieldLaw_all_ordered
    (μ : Measure (BranchingStep ℕ ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ ξ ∂μ, OrderedNatRealBranchingStep ξ)
    (hordered : MeasurableSet
      {ξ : BranchingStep ℕ ℝ | OrderedNatRealBranchingStep ξ})
    (m : ℕ) :
    ∀ᵐ step ∂finiteRootBranchingStepFieldLaw μ m, ∀ i : Fin m,
      ∀ u : TreeNode, OrderedNatRealBranchingStep (step i u) := by
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro u
  have hmarg := finiteRootBranchingStepFieldLaw_coordinate_marginal μ i u
  rw [← hmarg] at hμ
  have hcoord : Measurable
      (fun step : FiniteRootBranchingStepField m ℝ => step i u) :=
    (measurable_pi_apply u).comp (measurable_pi_apply i)
  exact (ae_map_iff hcoord.aemeasurable hordered).1 hμ

end ThesisSpeed
