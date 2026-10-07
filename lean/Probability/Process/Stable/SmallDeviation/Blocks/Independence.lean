/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Stable.SmallDeviation.Blocks
public import Probability.Process.IndepIncrements.DisjointPaths

/-!
# Independence of neighboring stable-process blocks

The translated rational-coordinate paths on consecutive uniform blocks are
independent. The proof uses full process independence of adjacent increment
paths, not merely pairwise independence of individual increments.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The complete translated paths on two neighboring blocks of a stable
Lévy process are independent in the rational-coordinate product space. -/
theorem IsStableLevyProcess.indepFun_adjacentRationalUniformBlocks
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (j j' : Fin blocks) (hnext : j.val + 1 = j'.val) :
    (fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⟂ᵢ[P]
    (fun ω q => rationalUniformBlockProcessFromTime X hblocks j' q ω) := by
  let a := rationalUniformBlockAbsoluteTime hblocks j ⊥
  let b := rationalUniformBlockAbsoluteTime hblocks j ⊤
  let c := rationalUniformBlockAbsoluteTime hblocks j' ⊤
  have hleft (q : ↑RationalCoordinate.UnitInterval) :
      a ≤ rationalUniformBlockAbsoluteTime hblocks j q ∧
        rationalUniformBlockAbsoluteTime hblocks j q ≤ b := by
    exact ⟨monotone_rationalUniformBlockAbsoluteTime hblocks j bot_le,
      monotone_rationalUniformBlockAbsoluteTime hblocks j le_top⟩
  have hright (q : ↑RationalCoordinate.UnitInterval) :
      b ≤ rationalUniformBlockAbsoluteTime hblocks j' q ∧
        rationalUniformBlockAbsoluteTime hblocks j' q ≤ c := by
    dsimp [b, c]
    rw [rationalUniformBlockAbsoluteTime_top_eq_bot_of_succ hblocks j j' hnext]
    exact ⟨monotone_rationalUniformBlockAbsoluteTime hblocks j' bot_le,
      monotone_rationalUniformBlockAbsoluteTime hblocks j' le_top⟩
  have hindep := h.increments.indepIncrements.indepFun_adjacentPaths
    (fun t => h.increments.aemeasurable_eval t) a b c
    (rationalUniformBlockAbsoluteTime hblocks j)
    (rationalUniformBlockAbsoluteTime hblocks j') hleft hright
  dsimp [b] at hindep
  rw [rationalUniformBlockAbsoluteTime_top_eq_bot_of_succ hblocks j j' hnext]
    at hindep
  simpa [a, b, c, rationalUniformBlockProcessFromTime] using hindep

/-- The rational-coordinate paths on every block of a finite uniform
partition are mutually independent. This is the finite-partition form of
independent increments needed when a path event is split across all cells. -/
theorem IsStableLevyProcess.iIndepFun_rationalUniformBlocks
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks) :
    iIndepFun
      (fun (j : Fin blocks) ω q =>
        rationalUniformBlockProcessFromTime X hblocks j q ω) P := by
  let t : ℕ → ℝ≥0 := fun k => rationalUniformBlockBoundary blocks k hblocks
  let blockIndex (k : ℕ) : Fin blocks :=
    ⟨min k (blocks - 1), by omega⟩
  let τ : ℕ → ↑RationalCoordinate.UnitInterval → ℝ≥0 := fun k q =>
    rationalUniformBlockAbsoluteTime hblocks (blockIndex k) q
  have hindex (k : ℕ) (hk : k < blocks) : blockIndex k = ⟨k, hk⟩ := by
    have hk' : k ≤ blocks - 1 := Nat.le_sub_one_of_lt hk
    apply Fin.ext
    simp [blockIndex, Nat.min_eq_left hk']
  have ht : Monotone t := by
    intro i j hij
    apply NNReal.coe_le_coe.mp
    change (i : ℝ) / (blocks : ℝ) ≤ (j : ℝ) / (blocks : ℝ)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have hleft : ∀ i < blocks, ∀ q, t i ≤ τ i q := by
    intro i hi q
    change rationalUniformBlockBoundary blocks i hblocks ≤
      rationalUniformBlockAbsoluteTime hblocks (blockIndex i) q
    rw [hindex i hi, rationalUniformBlockBoundary_eq_start hblocks ⟨i, hi⟩]
    exact monotone_rationalUniformBlockAbsoluteTime hblocks ⟨i, hi⟩ bot_le
  have hright : ∀ i < blocks, ∀ q, τ i q ≤ t (i + 1) := by
    intro i hi q
    change rationalUniformBlockAbsoluteTime hblocks (blockIndex i) q ≤
      rationalUniformBlockBoundary blocks (i + 1) hblocks
    rw [hindex i hi,
      rationalUniformBlockBoundary_succ_eq_end hblocks ⟨i, hi⟩]
    exact monotone_rationalUniformBlockAbsoluteTime hblocks ⟨i, hi⟩ le_top
  have hstart : ∀ i < blocks, τ i ⊥ = t i := by
    intro i hi
    change rationalUniformBlockAbsoluteTime hblocks (blockIndex i) ⊥ =
      rationalUniformBlockBoundary blocks i hblocks
    rw [hindex i hi]
    exact (rationalUniformBlockBoundary_eq_start hblocks ⟨i, hi⟩).symm
  have hpaths := h.increments.indepIncrements.iIndepFun_finiteAdjacentPaths
    (fun s => h.increments.aemeasurable_eval s) blocks t ht ⊥ τ hleft hright hstart
  convert hpaths using 1
  funext j ω q
  rw [rationalUniformBlockProcessFromTime]
  simp [τ, t, hindex j.val j.isLt, rationalUniformBlockBoundary_eq_start]

/-- The tube events of two neighboring stable-process blocks factor exactly.
This is the two-block probability identity underlying the upper block bound. -/
theorem IsStableLevyProcess.measure_inter_adjacentRationalUniformBlockTubes
    {Ω : Type*} [MeasurableSpace Ω] {α : ℝ} {μ : Measure ℝ}
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (blocks : ℕ) (hblocks : 0 < blocks)
    (j j' : Fin blocks) (hnext : j.val + 1 = j'.val) (width : ℝ) :
    P (((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) ∩
      ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j' q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width)) =
      P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) *
      P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j' q ω) ⁻¹'
        Skorokhod.rationalCoordinateOscillationTube width) := by
  exact (h.indepFun_adjacentRationalUniformBlocks blocks hblocks j j' hnext).measure_inter_preimage_eq_mul
    _ _ (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)
    (Skorokhod.measurableSet_rationalCoordinateOscillationTube width)

end ProbabilityTheory
