import ThesisSpeed.Probability.Genealogy.Tree.Filtration

/-!
# Declared splits and their stopping-time property

`splitDeclaration path splitMark` declares a split at generation `n + 1`
whenever the mark at the parent `path n` lies in `splitMark`; generation zero
never declares a split. The main theorem proves that the first declared split
generation is a stopping time for the generation filtration, and the final
lemma specialises it to an adapted full-depth lineage on `𝕍`.
-/

open MeasureTheory

namespace ThesisSpeed

variable {α : Type*} {M : Type*} [MeasurableSpace M]

/-- The split is declared when the child mark at the parent has been
revealed. Generation zero cannot declare a split. -/
def splitDeclaration (path : ℕ → Mark α M → TreeNode α)
    (splitMark : Set M) : ℕ → Set (Mark α M)
  | 0 => ∅
  | n + 1 => {ω | ω (path n ω) ∈ splitMark}

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

end ThesisSpeed
