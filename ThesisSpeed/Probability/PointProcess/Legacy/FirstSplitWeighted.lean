import ThesisSpeed.Probability.Genealogy.FirstSplit
import ThesisSpeed.Probability.PointProcess.Legacy.WeightedSlot
import ThesisSpeed.Probability.Timing.Stopping

open MeasureTheory

namespace ThesisSpeed

theorem first_bifurcation_isStoppingTime
    (path : ℕ → PreSampledField WeightedBranchingStep → 𝕍)
    (hpath : ∀ n,
      Measurable[generationFiltration (Mark := WeightedBranchingStep) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (Mark := WeightedBranchingStep))
      (firstDeclaredSuccess (splitDeclaration path twoChildren)) :=
  first_split_isStoppingTime_of path twoChildren twoChildren_measurable
    hpath hdepth

end ThesisSpeed
