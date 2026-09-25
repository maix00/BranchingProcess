import ThesisSpeed.Probability.Genealogy.BranchingPositions
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

/-! Marked branching trees indexed by an arbitrary type of initial roots. -/

abbrev RootIndexedMarkedTree (Root : Type*) (X : Type*) [AddCommMonoid X] :=
  Root → BranchingMarkedTree X

def RootIndexedMarkedTree.ofStep {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) : RootIndexedMarkedTree Root X :=
  fun i => BranchingMarkedTree.ofStep (step i)

@[simp] theorem RootIndexedMarkedTree.ofStep_apply
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) :
    RootIndexedMarkedTree.ofStep step i =
      BranchingMarkedTree.ofStep (step i) := rfl

theorem RootIndexedMarkedTree.ofStep_mark
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) :
    (RootIndexedMarkedTree.ofStep step i).mark u =
      branchingTreePathSum (step i) u := by
  exact congrFun (BranchingMarkedTree.ofStep_mark (step i)) u

def rootIndexedNodePosition {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) : X :=
  branchingTreePathSum (step i) u

theorem rootIndexedNodePosition_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode) :
    rootIndexedNodePosition (step.reindex f) i u =
      rootIndexedNodePosition step (f i) u := by
  rfl

@[simp] theorem rootIndexedNodePosition_nil
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) :
    rootIndexedNodePosition step i [] = 0 := by
  exact branchingTreePathSum_nil (step i)

theorem rootIndexedNodePosition_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) (j : ℕ) :
    rootIndexedNodePosition step i (u ++ [j]) =
      rootIndexedNodePosition step i u +
        branchingStepIncrement (step i u) j := by
  exact branchingTreePathSum_append_singleton (step i) u j

def rootIndexedAbsolutePosition {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) : X :=
  initial i + rootIndexedNodePosition step i u

theorem rootIndexedAbsolutePosition_reindex
    {Root NewRoot : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode) :
    rootIndexedAbsolutePosition (initial ∘ f) (step.reindex f) i u =
      rootIndexedAbsolutePosition initial step (f i) u := by
  rfl

theorem rootIndexedAbsolutePosition_eq_initial_add_mark
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) :
    rootIndexedAbsolutePosition initial step i u =
      initial i + (RootIndexedMarkedTree.ofStep step i).mark u := by
  simp [rootIndexedAbsolutePosition, rootIndexedNodePosition]

@[simp] theorem rootIndexedAbsolutePosition_root
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X) (i : Root) :
    rootIndexedAbsolutePosition initial step i [] = initial i := by
  simp [rootIndexedAbsolutePosition]

theorem rootIndexedAbsolutePosition_append_singleton
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) (j : ℕ) :
    rootIndexedAbsolutePosition initial step i (u ++ [j]) =
      rootIndexedAbsolutePosition initial step i u +
        branchingStepIncrement (step i u) j := by
  simp only [rootIndexedAbsolutePosition,
    rootIndexedNodePosition_append_singleton, add_assoc]

theorem rootIndexedAbsolutePosition_append_two
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u : TreeNode) (j k : ℕ) :
    rootIndexedAbsolutePosition initial step i (u ++ [j, k]) =
      rootIndexedAbsolutePosition initial step i u +
        branchingStepIncrement (step i u) j +
        branchingStepIncrement (step i (u ++ [j])) k := by
  unfold rootIndexedAbsolutePosition rootIndexedNodePosition
  rw [branchingTreePathSum_append_two]
  simp only [add_assoc]

theorem rootIndexedNodePosition_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (step : RootIndexedBranchingStepField Root X) (i : Root)
    (u v : TreeNode) :
    rootIndexedNodePosition step i (u ++ v) =
      rootIndexedNodePosition step i u +
        branchingTreePathSum (fun w => step i (u ++ w)) v := by
  exact branchingTreePathSum_append (step i) u v

theorem rootIndexedAbsolutePosition_append
    {Root : Type*} {X : Type*} [AddCommMonoid X]
    (initial : Root → X) (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u v : TreeNode) :
    rootIndexedAbsolutePosition initial step i (u ++ v) =
      rootIndexedAbsolutePosition initial step i u +
        branchingTreePathSum (fun w => step i (u ++ w)) v := by
  unfold rootIndexedAbsolutePosition
  rw [rootIndexedNodePosition_append]
  simp only [add_assoc]

def rootIndexedRealizedNode {Root : Type*} {X : Type*}
    (step : RootIndexedBranchingStepField Root X) (i : Root) (u : TreeNode) : Prop :=
  branchingRealizedNode (step i) u

theorem rootIndexedRealizedNode_reindex
    {Root NewRoot : Type*} {X : Type*}
    (step : RootIndexedBranchingStepField Root X)
    (f : NewRoot → Root) (i : NewRoot) (u : TreeNode) :
    rootIndexedRealizedNode (step.reindex f) i u ↔
      rootIndexedRealizedNode step (f i) u := by
  rfl

@[simp] theorem rootIndexedRealizedNode_nil
    {Root : Type*} {X : Type*} (step : RootIndexedBranchingStepField Root X) (i : Root) :
    rootIndexedRealizedNode step i [] := by
  exact branchingRealizedNode_nil (step i)

theorem rootIndexedRealizedNode_append_iff
    {Root : Type*} {X : Type*} (step : RootIndexedBranchingStepField Root X)
    (i : Root) (u v : TreeNode) :
    rootIndexedRealizedNode step i (u ++ v) ↔
      rootIndexedRealizedNode step i u ∧
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
