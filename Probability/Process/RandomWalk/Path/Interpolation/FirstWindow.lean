/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Interpolation.Unbounded
public import Probability.Process.RandomWalk.Path.Interpolation.FiniteBlock
public import Probability.Process.RandomWalk.Path.Corridor.Interpolation.Basic
public import Probability.Process.RandomWalk.Path.Survival
public import Probability.Process.Path.AboveStart.Continuous
public import Probability.Process.Path.FiniteHorizonScaling

/-!
# First-window conditions for polygonal random-walk paths

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.survivesNonnegative_of_isNonnegativeWindowStart_grid`:
  if the polygonal path's unit window beginning at $j/n$ lies above
  its starting height, then $S_{j+k}\ge S_j$ for $1\le k\le n$.
- `ProbabilityTheory.RandomWalk.restrictPathToUnitInterval_shiftToZero_grid`:
  the rebased polygonal path from $j/n$ to $(j+n)/n$ is exactly the
  interpolation of the finite increment block beginning at $j$.
- `ProbabilityTheory.RandomWalk.isNonnegativeWindowStart_grid_iff_survivesNonnegative`:
  the polygonal unit window at $j/n$ is eligible exactly when its
  discrete length-$n$ increment block survives.

This is the grid restriction of the path transform in
Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Lemma 3.1 and Theorem 3.2,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open ProbabilityTheory
open scoped NNReal

/-- An eligible polygonal window at a lattice start yields a surviving
discrete block at the same index. -/
theorem survivesNonnegative_of_isNonnegativeWindowStart_grid
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hscale : 0 < scale n) (start : ℕ)
    (increment : ℕ → ℝ)
    (hwindow : IsNonnegativeWindowStart
      (normalizedLinearContinuousPathUnbounded scale n increment)
      (⟨(start : ℝ) / n, div_nonneg (Nat.cast_nonneg start)
        (Nat.cast_nonneg n)⟩ : ℝ≥0)) :
    SurvivesNonnegative n (fun k => increment (start + k)) := by
  rw [SurvivesNonnegative.shift_iff]
  intro k
  let gridTime (j : ℕ) : ℝ≥0 :=
    ⟨(j : ℝ) / n, div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg n)⟩
  have hkn : (k : ℕ) + 1 ≤ n := by omega
  have hu : gridTime ((k : ℕ) + 1) ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    change (((k : ℕ) + 1 : ℕ) : ℝ) / n ≤ 1
    exact (div_le_one (Nat.cast_pos.mpr hn)).mpr
      (by exact_mod_cast hkn)
  let u : Set.Icc (0 : ℝ≥0) 1 :=
    ⟨gridTime ((k : ℕ) + 1), ⟨bot_le, hu⟩⟩
  have hadd : gridTime start + gridTime ((k : ℕ) + 1) =
      gridTime (start + ((k : ℕ) + 1)) := by
    apply NNReal.eq
    change (start : ℝ) / n + (((k : ℕ) + 1 : ℕ) : ℝ) / n =
      ((start + ((k : ℕ) + 1) : ℕ) : ℝ) / n
    push_cast
    ring
  have hineq := hwindow u
  change normalizedLinearPathUnbounded scale n increment
      (gridTime start) ≤
    normalizedLinearPathUnbounded scale n increment
      (gridTime start + gridTime ((k : ℕ) + 1)) at hineq
  rw [hadd, normalizedLinearPathUnbounded_grid scale hn,
    normalizedLinearPathUnbounded_grid scale hn] at hineq
  exact (mul_le_mul_iff_of_pos_left (inv_pos.mpr hscale)).mp hineq

/-- The unit-time increment path starting at lattice index `start`
is the polygonal interpolation of that finite increment block. -/
theorem restrictPathToUnitInterval_shiftToZero_grid
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (start : ℕ) (increment : ℕ → ℝ) :
    restrictPathToUnitInterval
        (shiftToZero
          (normalizedLinearContinuousPathUnbounded scale n increment)
          (⟨(start : ℝ) / n, div_nonneg (Nat.cast_nonneg start)
            (Nat.cast_nonneg n)⟩ : ℝ≥0)) =
      normalizedLinearContinuousPathFromBlock scale n
        (Combinatorics.Sequence.blockCoordinates start n increment) := by
  ext t
  rw [normalizedLinearContinuousPathFromBlock_blockCoordinates]
  exact shiftToZero_normalizedLinearContinuousPathUnbounded_eq_bounded
    scale hn start increment t

/-- Grid-start eligibility of a polygonal unit window is equivalent
to survival of the corresponding discrete length-`n` walk block. -/
theorem isNonnegativeWindowStart_grid_iff_survivesNonnegative
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hscale : 0 < scale n) (start : ℕ)
    (increment : ℕ → ℝ) :
    IsNonnegativeWindowStart
        (normalizedLinearContinuousPathUnbounded scale n increment)
        (⟨(start : ℝ) / n, div_nonneg (Nat.cast_nonneg start)
          (Nat.cast_nonneg n)⟩ : ℝ≥0) ↔
      SurvivesNonnegative n (fun k => increment (start + k)) := by
  constructor
  · exact survivesNonnegative_of_isNonnegativeWindowStart_grid
      scale hn hscale start increment
  · intro hsurv u
    let shifted : ℕ → ℝ := fun k => increment (start + k)
    have hgrid : ∀ k : Fin n,
        (scale n)⁻¹ * AdditivePath.displacement (k + 1) shifted ∈
          Set.Ici 0 := by
      intro k
      exact mul_nonneg (inv_nonneg.mpr hscale.le) (hsurv k)
    have hRange : Set.range
        (normalizedLinearContinuousPathIcc scale n shifted) ⊆
          Set.Ici 0 :=
      (normalizedLinearContinuousPathIcc_range_subset_iff
        scale hn (convex_Ici 0) (le_refl 0) shifted).2 hgrid
    let t : unitInterval :=
      ⟨(u.1 : ℝ), ⟨NNReal.coe_nonneg _,
        NNReal.coe_le_coe.mpr u.property.2⟩⟩
    have hnonneg : 0 ≤ normalizedLinearContinuousPathIcc
        scale n shifted t := hRange ⟨t, rfl⟩
    have hshift := shiftToZero_normalizedLinearContinuousPathUnbounded_eq_bounded
      scale hn start increment t
    rw [← hshift] at hnonneg
    have htEq : (⟨(t : ℝ), t.property.1⟩ : ℝ≥0) = u.1 := by
      apply NNReal.eq
      rfl
    rw [htEq] at hnonneg
    simpa [shiftToZero, sub_nonneg] using hnonneg

end ProbabilityTheory.RandomWalk

end
