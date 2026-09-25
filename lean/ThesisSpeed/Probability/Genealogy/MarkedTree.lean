import ThesisSpeed.Probability.Genealogy.Tree
import ThesisSpeed.Probability.Branching.Step
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

/-! A marked tree is a node-indexed branching-step field together with its
induced cumulative position mark. -/
def branchingTreePathSum {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (u : TreeNode) : X :=
  ∑ j ∈ Finset.range u.length,
    branchingStepIncrement (ω (u.take j)) (u[j]!)

structure BranchingMarkedTree (X : Type*) [AddCommMonoid X] where
  step : TreeNode → BranchingStep ℕ X
  mark : TreeNode → X
  mark_eq_pathSum : ∀ u, mark u = branchingTreePathSum step u

def BranchingMarkedTree.ofStep {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) : BranchingMarkedTree X where
  step := step
  mark := branchingTreePathSum step
  mark_eq_pathSum := fun _ => rfl

@[simp] theorem BranchingMarkedTree.ofStep_step
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) :
    (BranchingMarkedTree.ofStep step).step = step := rfl

@[simp] theorem BranchingMarkedTree.ofStep_mark
    {X : Type*} [AddCommMonoid X]
    (step : TreeNode → BranchingStep ℕ X) :
    (BranchingMarkedTree.ofStep step).mark = branchingTreePathSum step := rfl

abbrev RandomBranchingMarkedTree (Ω X : Type*) [AddCommMonoid X] :=
  Ω → BranchingMarkedTree X

noncomputable def branchingStepFieldLaw {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) :
    Measure (TreeNode → BranchingStep ℕ X) :=
  Measure.infinitePi (fun _ : TreeNode => μ)

instance branchingStepFieldLaw.isProbabilityMeasure
    {X : Type*} [MeasurableSpace X] (μ : Measure (BranchingStep ℕ X))
    [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (branchingStepFieldLaw μ) := by
  unfold branchingStepFieldLaw
  infer_instance

theorem branchingStepFieldLaw_coordinate
    {X : Type*} [MeasurableSpace X] (μ : Measure (BranchingStep ℕ X))
    [IsProbabilityMeasure μ] (u : TreeNode) :
    (branchingStepFieldLaw μ).map (fun ω => ω u) = μ := by
  unfold branchingStepFieldLaw
  exact Measure.infinitePi_map_eval (fun _ : TreeNode => μ) u

theorem branchingStepFieldLaw_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ] :
    iIndepFun (fun u (ω : TreeNode → BranchingStep ℕ X) => ω u)
      (branchingStepFieldLaw μ) := by
  unfold branchingStepFieldLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : TreeNode => μ)
    (X := fun _ : TreeNode => id)
    (fun _ => measurable_id))

theorem branchingStepFieldLaw_injective_coordinates_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (f : ι → TreeNode) (hf : Function.Injective f) :
    iIndepFun (fun i (ω : TreeNode → BranchingStep ℕ X) => ω (f i))
      (branchingStepFieldLaw μ) := by
  exact (branchingStepFieldLaw_independent μ).precomp hf

theorem branchingStepFieldLaw_injective_coordinates_comp_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {ι : Type*} [Countable ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)]
    (f : ι → TreeNode) (hf : Function.Injective f)
    (g : ∀ i, BranchingStep ℕ X → β i)
    (hg : ∀ i, Measurable (g i)) :
    iIndepFun (fun i (ω : TreeNode → BranchingStep ℕ X) =>
      g i (ω (f i))) (branchingStepFieldLaw μ) := by
  exact (branchingStepFieldLaw_injective_coordinates_independent μ f hf).comp
    (fun i => g i) hg

theorem branchingTreePathSum_nil {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) :
    branchingTreePathSum ω [] = 0 := by simp [branchingTreePathSum]

theorem branchingTreePathSum_singleton {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (i : ℕ) :
    branchingTreePathSum ω [i] = branchingStepIncrement (ω []) i := by
  simp [branchingTreePathSum]

theorem branchingTreePathSum_append_singleton {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (u : TreeNode) (i : ℕ) :
    branchingTreePathSum ω (u ++ [i]) =
      branchingTreePathSum ω u + branchingStepIncrement (ω u) i := by
  simp only [branchingTreePathSum, List.length_append, List.length_singleton,
    Finset.sum_range_succ]
  have hlast : (u ++ [i]).take u.length = u := by simp
  have hslot : (u ++ [i])[u.length]! = i := by simp
  rw [hlast, hslot]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < u.length := Finset.mem_range.mp hj
  simp [List.take_append_of_le_length (Nat.le_of_lt hjlt),
    List.getElem?_append_left hjlt]

theorem branchingTreePathSum_append_two {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) (u : TreeNode)
    (i j : ℕ) :
    branchingTreePathSum ω (u ++ [i, j]) =
      branchingTreePathSum ω u +
        branchingStepIncrement (ω u) i +
        branchingStepIncrement (ω (u ++ [i])) j := by
  rw [show u ++ [i, j] = (u ++ [i]) ++ [j] by simp]
  rw [branchingTreePathSum_append_singleton]
  rw [branchingTreePathSum_append_singleton]

abbrev PositionMarkedTree (X : Type*) := TreeNode → X

def positionMarkedTree {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) : PositionMarkedTree X :=
  branchingTreePathSum ω

def randomPositionMarkedTree {Ω X : Type*} [AddCommMonoid X]
    (ω : RandomBranchingMarkedTree Ω X) : Ω → PositionMarkedTree X :=
  fun z => (ω z).mark

theorem positionMarkedTree_at_root {X : Type*} [AddCommMonoid X]
    (ω : TreeNode → BranchingStep ℕ X) :
    positionMarkedTree ω [] = 0 := by
  simp [positionMarkedTree, branchingTreePathSum]

end ThesisSpeed
