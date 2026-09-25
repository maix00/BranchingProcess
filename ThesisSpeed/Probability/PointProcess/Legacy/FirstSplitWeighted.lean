import ThesisSpeed.Probability.Genealogy.Tree.Split
import ThesisSpeed.Probability.PointProcess.Legacy.WeightedSlot
import ThesisSpeed.Probability.Timing.Stopping

open MeasureTheory

namespace ThesisSpeed

theorem first_bifurcation_isStoppingTime
    (path : ℕ → Mark ℕ WeightedBranchingStep → 𝕍)
    (hpath : ∀ n,
      Measurable[generationFiltration (M := WeightedBranchingStep) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (M := WeightedBranchingStep))
      (firstDeclaredSuccess (splitDeclaration path twoChildren)) :=
  first_split_isStoppingTime_of path twoChildren twoChildren_measurable
    hpath hdepth

end ThesisSpeed
