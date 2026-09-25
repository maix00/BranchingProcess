import ThesisSpeed.Probability.Genealogy.Tree
import ThesisSpeed.Probability.PointProcess.Legacy.WeightedSlot

/-!
# First observable split on a marked genealogy
-/

open MeasureTheory

namespace ThesisSpeed

theorem first_split_isStoppingTime_of
    {Mark : Type*} [MeasurableSpace Mark]
    (path : ℕ → MarkedTree Mark → TreeNode)
    (splitMark : Set Mark) (hsplit : MeasurableSet splitMark)
    (hpath : ∀ n,
      Measurable[generationFiltration (Mark := Mark) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (Mark := Mark))
      (firstDeclaredSuccess (splitDeclaration path splitMark)) :=
  first_split_generation_isStoppingTime path hpath hdepth
    splitMark hsplit

/-- The visible first bifurcation generation for a causal, full-depth
lineage on the countably marked tree. -/
theorem first_bifurcation_isStoppingTime
    (path : ℕ → MarkedTree OffspringMark → TreeNode)
    (hpath : ∀ n,
      Measurable[generationFiltration (Mark := OffspringMark) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (Mark := OffspringMark))
      (firstDeclaredSuccess (splitDeclaration path twoChildren)) :=
  first_split_isStoppingTime_of path twoChildren twoChildren_measurable
    hpath hdepth

end ThesisSpeed
