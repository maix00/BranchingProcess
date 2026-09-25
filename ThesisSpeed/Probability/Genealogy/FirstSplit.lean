import ThesisSpeed.Probability.Genealogy.Tree

/-!
# First observable split on a marked genealogy
-/

open MeasureTheory

namespace ThesisSpeed

theorem first_split_isStoppingTime_of
    {M : Type*} [MeasurableSpace M]
    (path : ℕ → Mark ℕ M → 𝕍)
    (splitMark : Set M) (hsplit : MeasurableSet splitMark)
    (hpath : ∀ n,
      Measurable[generationFiltration (M := M) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (M := M))
      (firstDeclaredSuccess (splitDeclaration path splitMark)) :=
  first_split_generation_isStoppingTime path hpath hdepth
    splitMark hsplit

end ThesisSpeed
