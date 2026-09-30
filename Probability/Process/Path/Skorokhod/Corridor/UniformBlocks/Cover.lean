module

public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Gluing
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Coverage of rational times by uniform blocks

Every rational point of the unit interval belongs to a uniform rational
block. This is needed to pass from blockwise corridor constraints to a
whole-path tube event.
-/

@[expose] public section

namespace ProbabilityTheory

open scoped NNReal

/-- A uniform rational block partition covers every rational unit time. -/
theorem exists_rationalUniformBlockTime
    {blocks : ℕ} (hblocks : 0 < blocks)
    (q : ↑RationalGrid.RationalUnitInterval) :
    ∃ j : Fin blocks, ∃ r : ↑RationalGrid.RationalUnitInterval,
      rationalUniformBlockTime hblocks j r = q := by
  let y : ℚ := (blocks : ℚ) * (q : ℚ)
  have hy0 : 0 ≤ y := mul_nonneg (by positivity) q.property.1
  by_cases hfloor : ⌊y⌋₊ < blocks
  · let j : Fin blocks := ⟨⌊y⌋₊, hfloor⟩
    let rVal : ℚ := y - (⌊y⌋₊ : ℚ)
    have hr0 : 0 ≤ rVal := by
      dsimp [rVal]
      linarith [Nat.floor_le hy0]
    have hr1 : rVal ≤ 1 := by
      dsimp [rVal]
      linarith [Nat.lt_floor_add_one y]
    let r : ↑RationalGrid.RationalUnitInterval := ⟨rVal, ⟨hr0, hr1⟩⟩
    refine ⟨j, r, ?_⟩
    apply Subtype.ext
    change ((⌊y⌋₊ : ℚ) + rVal) / (blocks : ℚ) = (q : ℚ)
    have hb : (blocks : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hblocks)
    dsimp [rVal, y]
    field_simp
    ring
  · have hyle : y ≤ (blocks : ℚ) := by
      dsimp [y]
      exact mul_le_of_le_one_right (by positivity) q.property.2
    have hyge : (blocks : ℚ) ≤ y := by
      by_contra h
      have hylt : y < (blocks : ℚ) := lt_of_not_ge h
      exact hfloor ((Nat.floor_lt hy0).2 hylt)
    have hqtop : q = ⊤ := by
      apply Subtype.ext
      have hqeq : (q : ℚ) = 1 := by
        have hb : (blocks : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hblocks)
        dsimp [y] at hyle hyge
        apply (mul_left_cancel₀ hb)
        linarith
      exact hqeq
    let j : Fin blocks := ⟨blocks - 1, Nat.sub_lt hblocks (by decide)⟩
    refine ⟨j, ⊤, ?_⟩
    rw [hqtop]
    apply Subtype.ext
    change (((blocks - 1 : ℕ) : ℚ) + 1) / (blocks : ℚ) = 1
    have hb : (blocks : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hblocks)
    have hcast : (((blocks - 1 : ℕ) : ℚ) + 1) = (blocks : ℚ) := by
      exact_mod_cast Nat.sub_add_cancel hblocks
    rw [hcast]
    field_simp

/-- A full blockwise corridor controls every rational-time position. -/
theorem rationalUniformPrefixCorridorEvent_full_positions
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks)
    (lower upper : ℝ) (ω : Ω)
    (hω : ω ∈ rationalUniformPrefixCorridorEvent X lower upper hblocks blocks) :
    (fun q => X (rationalUnitTime q) ω - X 0 ω) ∈
      rationalCoordinateCorridor lower upper := by
  unfold rationalCoordinateCorridor
  simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  intro q
  obtain ⟨j, r, hjr⟩ := exists_rationalUniformBlockTime hblocks q
  have hj := Set.mem_iInter.mp hω j
  have hj' : ∀ r : ↑RationalGrid.RationalUnitInterval,
      X (rationalUniformBlockAbsoluteTime hblocks j r) ω - X 0 ω ∈
        Set.Ioo lower upper := by
    simpa [rationalUniformPrefixCorridorEvent, j.isLt] using hj
  have htime : rationalUniformBlockAbsoluteTime hblocks j r = rationalUnitTime q := by
    exact congrArg rationalUnitTime hjr
  rw [← htime]
  exact hj' r

/-- A pointwise corridor with positive extra width lies inside a strict
range-diameter tube. The extra width supplies the required uniform margin. -/
theorem rationalCoordinateCorridor_subset_oscillationTube
    (lower upper extra : ℝ) (hextra : 0 < extra) :
    rationalCoordinateCorridor lower upper ⊆
      Skorokhod.rationalCoordinateOscillationTube (upper - lower + extra) := by
  intro x hx
  obtain ⟨margin, hmargin0, hmarginExtra⟩ := exists_rat_btwn hextra
  refine ⟨margin, hmargin0, ?_⟩
  intro s t
  have hs := Set.mem_iInter.mp hx s
  have ht := Set.mem_iInter.mp hx t
  change lower < x s ∧ x s < upper at hs
  change lower < x t ∧ x t < upper at ht
  apply abs_le.mpr
  constructor <;> linarith

end ProbabilityTheory
