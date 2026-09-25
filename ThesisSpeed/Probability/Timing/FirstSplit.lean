import ThesisSpeed.Tree.Split
import ThesisSpeed.Branching.Slot.Basic
import ThesisSpeed.Probability.Timing.Stopping
import ThesisSpeed.Probability.Timing.DeclaredSplit

open MeasureTheory

namespace ThesisSpeed

theorem first_bifurcation_isStoppingTime
    (path : ℕ → Mark ℕ NatRealBranchingStep → 𝕍)
    (hpath : ∀ n,
      Measurable[generationFiltration (M := NatRealBranchingStep) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (M := NatRealBranchingStep))
      (firstDeclaredSuccess (splitDeclaration path twoChildren)) :=
  first_split_isStoppingTime_of path twoChildren twoChildren_measurable
    hpath hdepth

end ThesisSpeed
