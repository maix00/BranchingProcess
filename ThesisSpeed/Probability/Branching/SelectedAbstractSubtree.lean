import ThesisSpeed.Probability.Branching.AbstractProperty
import ThesisSpeed.Probability.Genealogy.BranchingPositions

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def selectedSubtreeStepField {X : Type*}
    (chosen : (TreeNode → BranchingStep ℕ X) → TreeNode)
    (ω : TreeNode → BranchingStep ℕ X) :
    TreeNode → BranchingStep ℕ X :=
  subtreeStepField (chosen ω) ω

theorem selectedSubtreeStepField_measurable
    {X : Type*} [MeasurableSpace X] (n : ℕ)
    (chosen : (TreeNode → BranchingStep ℕ X) → TreeNode)
    (hchosen : Measurable[
      generationFiltration (Mark := BranchingStep ℕ X) n] chosen) :
    Measurable (selectedSubtreeStepField chosen) := by
  have hselect : Measurable chosen :=
    hchosen.mono
      (generationFiltration (Mark := BranchingStep ℕ X) |>.le n) le_rfl
  have hjoint : Measurable
      (fun p : TreeNode × (TreeNode → BranchingStep ℕ X) =>
        subtreeStepField p.1 p.2) :=
    measurable_from_prod_countable_right
      (subtreeStepField_measurable (X := X))
  exact hjoint.comp (hselect.prodMk measurable_id)

def abstractSelectionCell {X : Type*}
    (chosen : (TreeNode → BranchingStep ℕ X) → TreeNode)
    (A : Set (TreeNode → BranchingStep ℕ X)) (u : TreeNode) :
    Set (TreeNode → BranchingStep ℕ X) :=
  A ∩ {ω | chosen ω = u}

theorem abstractSelectionCell_measurable
    {X : Type*} [MeasurableSpace X] (n : ℕ)
    (chosen : (TreeNode → BranchingStep ℕ X) → TreeNode)
    (hchosen : Measurable[
      generationFiltration (Mark := BranchingStep ℕ X) n] chosen)
    (A : Set (TreeNode → BranchingStep ℕ X))
    (hA : MeasurableSet[
      generationFiltration (Mark := BranchingStep ℕ X) n] A)
    (u : TreeNode) :
    MeasurableSet[generationFiltration (Mark := BranchingStep ℕ X) n]
      (abstractSelectionCell chosen A u) :=
  hA.inter (hchosen (measurableSet_singleton u))

end ThesisSpeed
