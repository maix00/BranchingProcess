/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Interpolation.Basic
public import Algebra.BigOperators.AdditivePath.Block
import Mathlib.Algebra.Order.Floor.Semifield
import all Probability.Process.RandomWalk.Path.Interpolation.Finite.Lemmas.Grid

/-!
# Uniform-grid interpolation bound for random-walk paths

## Public declarations

- `abs_normalizedLinearPath_uniformGrid_sub_endpoint_le` compares the normalized polygonal path
  at $j/m$ with the partial sum at index $j\lfloor n/m\rfloor$. For $0<m$, $0<n$, and $j\le m$,
  the error is at most $(m+1)\max_{k\le n}|\xi_k|/\sqrt n$; the Lean statement also includes
  $n=0$, when both paths are identically zero.

The floor-index and partial-sum calculations in this estimate are proof steps specific to this
bound and are collected in `Lemmas/Grid.lean`.
-/

open Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- At a fixed uniform-grid time, polygonal interpolation is within
`blocks + 1` maximal jumps of the corresponding equal-block endpoint. -/
theorem abs_normalizedLinearPath_uniformGrid_sub_endpoint_le
    {n j blocks : ℕ} (hblocks : 0 < blocks) (hj : j ≤ blocks)
    (increment : ℕ → ℝ) :
    |normalizedLinearPath (fun n => Real.sqrt n) n increment
          ((j : ℝ) / blocks) -
        AdditivePath.displacement (j * (n / blocks)) increment / Real.sqrt n| ≤
      (blocks + 1) * ((Real.sqrt n)⁻¹ * maxAbsUpTo n increment) := by
  let t : unitInterval :=
    ⟨(j : ℝ) / blocks, by
      constructor
      · positivity
      · rw [div_le_one (by exact_mod_cast hblocks)]
        exact_mod_cast hj⟩
  let middle := ⌊(n : ℝ) * ((j : ℝ) / blocks)⌋₊
  let left := j * (n / blocks)
  have hleft : left ≤ middle :=
    mul_div_le_natFloor_mul_uniformGrid
  have hmiddle : middle ≤ n := by
    dsimp only [middle]
    apply Nat.floor_le_of_le
    have hjR : (j : ℝ) ≤ blocks := by exact_mod_cast hj
    have hbR : (0 : ℝ) < blocks := by exact_mod_cast hblocks
    calc
      (n : ℝ) * ((j : ℝ) / blocks) ≤ (n : ℝ) * 1 := by
        gcongr
        exact (div_le_one hbR).2 hjR
      _ = n := by ring
  have hgap : middle - left ≤ blocks := by
    have := natFloor_mul_uniformGrid_lt_mul_div_add (n := n) hblocks hj
    dsimp only [middle, left]
    omega
  have hlinear := abs_normalizedLinearPath_sub_normalizedStepPath_le
    (n := n) (fun n => Real.sqrt n) increment t
  have hsumNorm :=
    AdditivePath.norm_displacement_sub_le_length_mul_of_forall_norm_le
      (G := ℝ) (bound := maxAbsUpTo n increment) hleft fun k hk =>
        abs_increment_le_maxAbsUpTo increment
          ((Finset.mem_Ico.mp hk).2.le.trans hmiddle)
  have hsum :
      |AdditivePath.displacement middle increment - AdditivePath.displacement left increment| ≤
        ((middle - left : ℕ) : ℝ) * maxAbsUpTo n increment := by
    simpa only [Real.norm_eq_abs] using hsumNorm
  have hsqrt : 0 ≤ (Real.sqrt n)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hmax : 0 ≤ maxAbsUpTo n increment := maxAbsUpTo_nonneg n increment
  change |normalizedLinearPath (fun n => Real.sqrt n) n increment
      ((j : ℝ) / blocks) - AdditivePath.displacement left increment / Real.sqrt n| ≤ _
  have hstep :
      |normalizedStepPath (fun n => Real.sqrt n) n increment t -
          AdditivePath.displacement left increment / Real.sqrt n| ≤
        blocks * ((Real.sqrt n)⁻¹ * maxAbsUpTo n increment) := by
    change |(Real.sqrt n)⁻¹ * AdditivePath.displacement middle increment -
        AdditivePath.displacement left increment / Real.sqrt n| ≤ _
    rw [div_eq_mul_inv, mul_comm (AdditivePath.displacement left increment), ← mul_sub,
      abs_mul, abs_of_nonneg hsqrt]
    calc
      (Real.sqrt n)⁻¹ * |AdditivePath.displacement middle increment -
          AdditivePath.displacement left increment| ≤
          (Real.sqrt n)⁻¹ * (((middle - left : ℕ) : ℝ) *
            maxAbsUpTo n increment) :=
        mul_le_mul_of_nonneg_left hsum hsqrt
      _ ≤ (Real.sqrt n)⁻¹ * (blocks * maxAbsUpTo n increment) := by
        gcongr
      _ = blocks * ((Real.sqrt n)⁻¹ * maxAbsUpTo n increment) := by ring
  calc
    |normalizedLinearPath (fun n => Real.sqrt n) n increment
          ((j : ℝ) / blocks) -
        AdditivePath.displacement left increment / Real.sqrt n| ≤
        |normalizedLinearPath (fun n => Real.sqrt n) n increment
            ((j : ℝ) / blocks) -
          normalizedStepPath (fun n => Real.sqrt n) n increment t| +
        |normalizedStepPath (fun n => Real.sqrt n) n increment t -
          AdditivePath.displacement left increment / Real.sqrt n| := abs_sub_le _ _ _
    _ ≤ (Real.sqrt n)⁻¹ * maxAbsUpTo n increment +
        blocks * ((Real.sqrt n)⁻¹ * maxAbsUpTo n increment) := by
      gcongr
      · simpa [t, abs_of_nonneg hsqrt] using
          hlinear.trans (mul_le_mul_of_nonneg_left
            (abs_increment_le_maxAbsUpTo increment (by
              simpa [middle, t] using hmiddle)) (abs_nonneg _))
    _ = (blocks + 1) * ((Real.sqrt n)⁻¹ * maxAbsUpTo n increment) := by ring

end ProbabilityTheory.RandomWalk
