import ThesisSpeed.Probability.Genealogy.Tree

/-!
# First observable split on a marked genealogy
-/

open MeasureTheory

namespace ThesisSpeed

theorem first_split_isStoppingTime_of
    {Mark : Type*} [MeasurableSpace Mark]
    (path : ℕ → PreSampledField Mark → TreeNode)
    (splitMark : Set Mark) (hsplit : MeasurableSet splitMark)
    (hpath : ∀ n,
      Measurable[generationFiltration (Mark := Mark) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (Mark := Mark))
      (firstDeclaredSuccess (splitDeclaration path splitMark)) :=
  first_split_generation_isStoppingTime path hpath hdepth
    splitMark hsplit

end ThesisSpeed
