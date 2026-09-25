import Probability.BranchingRandomWalk.Tree.Filtration
import MeasureTheory.UlamHarris.Split
import Probability.BranchingRandomWalk.Timing.Stopping

/-!
# The first declared split is a stopping time

`splitDeclaration path splitMark` is the event that the mark at the parent
`path n` lies in `splitMark`, and generation zero never declares a split. This
file proves that the first generation at which a split is declared is a
stopping time for the generation filtration, and specialises the statement to
an adapted full-depth lineage on the Ulam--Harris vertex set `𝕍`.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory.UlamHarris MeasureTheory



variable {α : Type*} {M : Type*} [MeasurableSpace M]

/-- The first observable split generation is a stopping time for the actual
pre-sampled-tree generation filtration. -/
theorem first_split_generation_isStoppingTime [Countable α]
    (path : ℕ → Mark α M → TreeNode α)
    (hpath : ∀ n, Measurable[generationFiltration (M := M) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n)
    (splitMark : Set M) (hsplit : MeasurableSet splitMark) :
    IsStoppingTime (generationFiltration (M := M))
      (firstDeclaredSuccess (splitDeclaration path splitMark)) := by
  apply firstDeclaredSuccess_isStoppingTime
  intro n
  cases n with
  | zero =>
      change MeasurableSet[generationFiltration (M := M) 0]
        (∅ : Set (Mark α M))
      exact (generationSpace (M := M) 0).measurableSet_empty
  | succ n =>
      have hold : Measurable[generationFiltration (M := M) (n + 1)]
          (path n) :=
        (hpath n).mono
          (generationFiltration (M := M) |>.mono (Nat.le_succ n)) le_rfl
      exact (selected_mark_measurable (n + 1) (path n) hold
        (fun ω => by rw [hdepth n ω]; exact Nat.lt_succ_self n)) hsplit

/-- An adapted full-depth lineage on `𝕍` whose split mark is measurable has a
stopping-time first split. -/
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

end ProbabilityTheory.BranchingRandomWalk
