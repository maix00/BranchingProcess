/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic.SetNotationForOrder
import Algebra.BigOperators.AdditivePath.Block
import Probability.Process.RandomWalk.Path.Truncation.Moment

/-!
# Internal pathwise decomposition for truncated maximal bounds

This event inclusion is used by the fourth- and second-moment maximal-bound
proofs. It decomposes a large original block sum into a discarded large
increment or a large centered-truncated block sum.

## Internal proof declarations

* `exists_block_exists_abs_subset_largeIncrement_union_centeredTruncated`
  states the set inclusion from the original block-exceedance event into the
  union of a discarded-increment event and a centered-truncated block event,
  with accumulated bias `(length + 1) * |truncatedIncrementMean ν radius|`.

For block sums $S_{j,k}$ over the first $k+1$ increments of block $j$,
the pathwise decomposition is
\[
 \{\exists j<B,\ k\le N:\ u\le|S_{j,k}|\}
 \subseteq \{\exists i\le BN:\ r<|\xi_i|\}
  \cup\{\exists j<B,\ k\le N:
      u-(N+1)|m_r|\le|S^{\mathrm{trunc}}_{j,k}|\},
\]
where $S^{\mathrm{trunc}}_{j,k}$ uses centered truncation at radius $r$ and
$m_r$ is the truncated-increment mean.

-/


section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-- A large block oscillation of the original path is caused either by a
discarded increment or by a large oscillation of the centered truncated path.
The extra deterministic margin is the accumulated truncation bias. -/
lemma exists_block_exists_abs_subset_largeIncrement_union_centeredTruncated
    (ν : Measure ℝ) {radius threshold : ℝ}
    (blocks length : ℕ) :
    {path : ℕ → ℝ |
      ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold ≤ |AdditivePath.blockSum (j * length) (k + 1) path|} ⊆
      {path | ∃ i ∈ Finset.range (blocks * length + 1),
        radius < |path i|} ∪
      {path | ∃ j < blocks, ∃ k ∈ Finset.range (length + 1),
        threshold - ((length + 1 : ℕ) : ℝ) *
            |truncatedIncrementMean ν radius| ≤
          |AdditivePath.blockSum (j * length) (k + 1)
            (fun i => centeredTruncatedIncrement ν radius (path i))|} := by
  intro path hlarge
  by_cases htail : ∃ i ∈ Finset.range (blocks * length + 1),
      radius < |path i|
  · exact Or.inl htail
  · right
    obtain ⟨j, hj, k, hk, hklarge⟩ := hlarge
    refine ⟨j, hj, k, hk, ?_⟩
    let mean := truncatedIncrementMean ν radius
    let centeredPath : ℕ → ℝ :=
      fun i => centeredTruncatedIncrement ν radius (path i)
    have hcoordinate : ∀ i ∈ Finset.Ico (j * length) (j * length + (k + 1)),
        centeredPath i = path i - mean := by
      intro i hi
      have hklt : k < length + 1 := Finset.mem_range.1 hk
      have hkLe : k + 1 ≤ length + 1 :=
        Nat.succ_le_succ (Nat.lt_succ_iff.1 hklt)
      have hiUpper : i < blocks * length + 1 := by
        have hjSucc : j + 1 ≤ blocks := Nat.succ_le_iff.2 hj
        have hi' : i < j * length + (k + 1) := Finset.mem_Ico.1 hi |>.2
        calc
          i < j * length + (k + 1) := hi'
          _ ≤ j * length + (length + 1) := Nat.add_le_add_left hkLe _
          _ = (j + 1) * length + 1 := by
            rw [Nat.add_mul]
            omega
          _ ≤ blocks * length + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul_right length hjSucc) 1
      have hnotLarge : ¬radius < |path i| := fun hiLarge =>
        htail ⟨i, Finset.mem_range.2 hiUpper, hiLarge⟩
      simp only [centeredPath, centeredTruncatedIncrement, mean]
      rw [truncatedIncrement_of_abs_le (le_of_not_gt hnotLarge)]
    have hblock : AdditivePath.blockSum (j * length) (k + 1) centeredPath =
        AdditivePath.blockSum (j * length) (k + 1) path - (k + 1) • mean := by
      calc
        AdditivePath.blockSum (j * length) (k + 1) centeredPath =
            AdditivePath.blockSum (j * length) (k + 1) (fun i => path i - mean) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hcoordinate i hi
        _ = _ := AdditivePath.blockSum_sub_const (j * length) (k + 1) path mean
    have hreverse : AdditivePath.blockSum (j * length) (k + 1) path =
        AdditivePath.blockSum (j * length) (k + 1) centeredPath + (k + 1) • mean := by
      rw [hblock]
      abel
    have htriangle : |AdditivePath.blockSum (j * length) (k + 1) path| ≤
        |AdditivePath.blockSum (j * length) (k + 1) centeredPath| +
          ((k + 1 : ℕ) : ℝ) * |mean| := by
      rw [hreverse]
      refine (abs_add_le _ _).trans ?_
      rw [nsmul_eq_mul, abs_mul,
        abs_of_nonneg (show 0 ≤ (((k + 1 : ℕ) : ℝ)) by positivity)]
    have hkCast : (((k + 1 : ℕ) : ℝ)) ≤ ((length + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ
        (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    have hbias : (((k + 1 : ℕ) : ℝ)) * |mean| ≤
        ((length + 1 : ℕ) : ℝ) * |mean| :=
      mul_le_mul_of_nonneg_right hkCast (abs_nonneg _)
    change threshold - ((length + 1 : ℕ) : ℝ) * |mean| ≤
      |AdditivePath.blockSum (j * length) (k + 1) centeredPath|
    linarith


end ProbabilityTheory.RandomWalk
