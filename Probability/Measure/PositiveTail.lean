module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Positive one-sided tails

Positive mass on a half-line is visible beyond a strict threshold.
-/

@[expose] public section

namespace MeasureTheory

/-- Positive mass on the positive half-line is already visible beyond some
strictly positive threshold. -/
theorem exists_positive_tail_threshold (μ : Measure ℝ)
    (hpos : 0 < μ (Set.Ioi 0)) :
    ∃ width : ℝ, 0 < width ∧ 0 < μ (Set.Ioi width) := by
  let s : ℚ → Set ℝ := fun q => if 0 < q then Set.Ioi (q : ℝ) else ∅
  have hunion : (⋃ q : ℚ, s q) = Set.Ioi (0 : ℝ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
      by_cases hqpos : 0 < q
      · change x ∈ (if 0 < q then Set.Ioi (q : ℝ) else ∅) at hq
        simp only [hqpos, ↓reduceIte] at hq
        exact lt_trans (by exact_mod_cast hqpos) hq
      · simp [s, hqpos] at hq
    · intro hx
      obtain ⟨q, hq0, hqx⟩ := exists_rat_btwn hx
      apply Set.mem_iUnion.mpr
      refine ⟨q, ?_⟩
      change x ∈ (if 0 < q then Set.Ioi (q : ℝ) else ∅)
      have hq0Q : (0 : ℚ) < q := by exact_mod_cast hq0
      simp only [hq0Q, ↓reduceIte]
      exact hqx
  have hU : μ (⋃ q : ℚ, s q) ≠ 0 := by rw [hunion]; exact ne_of_gt hpos
  obtain ⟨q, hq⟩ := exists_measure_pos_of_not_measure_iUnion_null hU
  have hqpos : 0 < q := by
    by_contra hn
    simp [s, hn] at hq
  exact ⟨q, by exact_mod_cast hqpos, by simpa [s, hqpos] using hq⟩

end MeasureTheory

end
