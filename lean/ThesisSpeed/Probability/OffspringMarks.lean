import ThesisSpeed.Probability.MarkedTree

/-!
# A concrete measurable encoding of countable offspring marks

Each possible child index has a real presence flag and a real displacement.
The child is present exactly when the flag is positive.
This encodes finite and countably infinite offspring without imposing a
probability law. The law and the selected population are separate later
constructions.
-/

open MeasureTheory

namespace ThesisSpeed

abbrev OffspringMark := ℕ → ℝ × ℝ

def childPresent (i : ℕ) : Set OffspringMark :=
  {ξ | 0 < (ξ i).1}

theorem childPresent_measurable (i : ℕ) :
    MeasurableSet (childPresent i) := by
  change MeasurableSet {ξ : OffspringMark | (ξ i).1 ∈ Set.Ioi (0 : ℝ)}
  exact ((measurable_pi_apply i).fst) measurableSet_Ioi

/-- The offspring point process has at least two distinct realized children. -/
def twoChildren : Set OffspringMark :=
  {ξ | ∃ i j : ℕ, i ≠ j ∧ ξ ∈ childPresent i ∧ ξ ∈ childPresent j}

theorem twoChildren_measurable : MeasurableSet twoChildren := by
  have hset : twoChildren =
      ⋃ i : ℕ, ⋃ j : ℕ,
        (if i = j then ∅ else childPresent i ∩ childPresent j) := by
    ext ξ
    simp only [twoChildren, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      refine ⟨i, j, ?_⟩
      simp [hij, hi, hj]
    · rintro ⟨i, j, h⟩
      by_cases hij : i = j
      · simp [hij] at h
      · simp only [hij, if_false, Set.mem_inter_iff] at h
        exact ⟨i, j, hij, h.1, h.2⟩
  rw [hset]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hij : i = j
  · simp [hij]
  · simpa [hij] using
      (childPresent_measurable i).inter (childPresent_measurable j)

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
