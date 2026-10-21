/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Basic
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Prefix
import Probability.Process.IndepIncrements.DisjointPaths

/-!
# Independence of uniform block paths

The public theorems apply to any process with independent increments and
almost-everywhere measurable coordinates; they require no stationary or
stable increment laws:

* `HasIndepIncrements.iIndepFun_rationalUniformBlocks` states that all paths
  on a finite uniform partition are mutually independent.
* `HasIndepIncrements.indepFun_rationalPrefix_nextBlock` states that the
  path through a finite uniform partition is independent of its next block.

For block paths $B_j(q)=X_{\tau_j(q)}-X_{\tau_j(0)}$, the mutually
independent conclusion is `iIndepFun (fun j => B_j) P`. The prefix conclusion
states that $q\mapsto X_{\min(q,j/N)}-X_0$ is independent of $B_j$.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

/-- The path accumulated through the first `j` blocks is independent of the
translated path on block `j`. -/
theorem HasIndepIncrements.indepFun_rationalPrefix_nextBlock
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hXmeas : ∀ t : ℝ≥0, AEMeasurable (fun ω => X t ω) P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j : Fin blocks) :
    (rationalUniformPrefixPath X blocks j.val hblocks) ⟂ᵢ[P]
      (fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) := by
  let b := rationalUniformBlockBoundary blocks j.val hblocks
  let c := rationalUniformBlockAbsoluteTime hblocks j ⊤
  have hleft (q : ↑RationalCoordinate.UnitInterval) :
      (0 : ℝ≥0) ≤ min (RationalCoordinate.toNNReal q) b ∧
        min (RationalCoordinate.toNNReal q) b ≤ b :=
    ⟨bot_le, min_le_right _ _⟩
  have hright (q : ↑RationalCoordinate.UnitInterval) :
      b ≤ rationalUniformBlockAbsoluteTime hblocks j q ∧
        rationalUniformBlockAbsoluteTime hblocks j q ≤ c := by
    dsimp [b, c]
    rw [rationalUniformBlockBoundary_eq_start hblocks j]
    exact ⟨monotone_rationalUniformBlockAbsoluteTime hblocks j bot_le,
      monotone_rationalUniformBlockAbsoluteTime hblocks j le_top⟩
  have hindep := HasIndepIncrements.indepFun_adjacentPaths h hXmeas
    (0 : ℝ≥0) b c (fun q => min (RationalCoordinate.toNNReal q) b)
    (rationalUniformBlockAbsoluteTime hblocks j) hleft hright
  convert hindep using 1
  · rfl
  · funext ω q
    simp [rationalUniformBlockProcessFromTime, b,
      rationalUniformBlockBoundary_eq_start hblocks j]

/-- The centered paths on a finite uniform rational partition are mutually
independent, assuming only independent increments and coordinate
measurability. -/
theorem HasIndepIncrements.iIndepFun_rationalUniformBlocks
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hXmeas : ∀ t : ℝ≥0, AEMeasurable (fun ω => X t ω) P)
    (blocks : ℕ) (hblocks : 0 < blocks) :
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
    change (i : ℝ) / (blocks : ℝ) ≤ (j : ℝ) / (blocks : ℝ)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (by positivity)
  have hleft : ∀ i < blocks, ∀ q,
      t i ≤ τ i q := by
    intro i hi q
    change rationalUniformBlockBoundary blocks i hblocks ≤
      rationalUniformBlockAbsoluteTime hblocks (blockIndex i) q
    rw [hindex i hi]
    exact (rationalUniformBlockBoundary_eq_start hblocks ⟨i, hi⟩).symm ▸
      monotone_rationalUniformBlockAbsoluteTime hblocks ⟨i, hi⟩ bot_le
  have hright : ∀ i < blocks, ∀ q,
      τ i q ≤ t (i + 1) := by
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
  have hpaths := HasIndepIncrements.iIndepFun_finiteAdjacentPaths h hXmeas
    blocks t ht ⊥ τ hleft hright hstart
  convert hpaths using 1
  funext j ω q
  rw [rationalUniformBlockProcessFromTime]
  simp [τ, t, hindex j.val j.isLt, rationalUniformBlockBoundary_eq_start]

end ProbabilityTheory

end
