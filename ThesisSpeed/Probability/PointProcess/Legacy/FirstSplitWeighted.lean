import ThesisSpeed.Probability.Genealogy.FirstSplit
import ThesisSpeed.Probability.PointProcess.Legacy.WeightedSlot
import ThesisSpeed.Probability.Timing.Stopping

open MeasureTheory

namespace ThesisSpeed

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
