import ThesisSpeed.Probability.Genealogy.Tree
import ThesisSpeed.Probability.PointProcess.Legacy.WeightedSlot

/-!
# First observable split on a marked genealogy
-/

open MeasureTheory

namespace ThesisSpeed

/-- The visible first bifurcation generation for a causal, full-depth
lineage on the countably marked tree. -/
theorem first_bifurcation_isStoppingTime
    (path : ℕ → MarkedTree OffspringMark → TreeNode)
    (hpath : ∀ n,
      Measurable[generationFiltration (Mark := OffspringMark) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (Mark := OffspringMark))
      (firstDeclaredSuccess (splitDeclaration path twoChildren)) :=
  first_split_generation_isStoppingTime path hpath hdepth
    twoChildren twoChildren_measurable

end ThesisSpeed
