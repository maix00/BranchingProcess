/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Interpolation.Basic
public import Probability.Process.Path.Continuous

/-!
# Polygonal random-walk paths on all nonnegative times

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.normalizedLinearPathUnbounded`:
  $X_n(t)=a_n^{-1}\sum_{k\ge0}w_{n,k}(t)\xi_k$, where only the
  first $\lfloor nt\rfloor+1$ weights are used.
- `ProbabilityTheory.RandomWalk.continuous_normalizedLinearPathUnbounded`:
  this path is continuous on $[0,\infty)$.
- `ProbabilityTheory.RandomWalk.normalizedLinearContinuousPathUnbounded`:
  the same path bundled in $C([0,\infty),\mathbb R)$.
- `ProbabilityTheory.RandomWalk.measurable_normalizedLinearContinuousPathUnbounded`:
  the path map is Borel measurable in the increment sequence.
- `ProbabilityTheory.RandomWalk.normalizedLinearPathUnbounded_eq_bounded`:
  on $0\le t\le1$, the unbounded path agrees with the existing
  first-$n$-increment interpolation.
- `ProbabilityTheory.RandomWalk.normalizedLinearContinuousPathUnbounded_apply_unitInterval`:
  the same equality for bundled continuous paths.

The unbounded-time interpolation is the path $Y_n$ used in Erwin
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Section 3, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098. Its restriction to $[0,1]$
matches the existing bounded interpolation in `Interpolation.Basic`.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open Filter
open scoped NNReal Topology

/-- Normalized polygonal interpolation of an infinite sequence of
increments. The finite sum contains every potentially nonzero weight
at time `t`. -/
noncomputable def normalizedLinearPathUnbounded
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ)
    (t : ℝ≥0) : ℝ :=
  (scale n)⁻¹ *
    ∑ k ∈ Finset.range (⌊(n : ℝ) * (t : ℝ)⌋₊ + 1),
      linearIncrementWeight n k t * increment k

private theorem sum_linearIncrementWeight_eq_range_of_floor_le
    (n : ℕ) (increment : ℕ → ℝ) (t : ℝ≥0) {N : ℕ}
    (hN : ⌊(n : ℝ) * (t : ℝ)⌋₊ + 1 ≤ N) :
    ∑ k ∈ Finset.range (⌊(n : ℝ) * (t : ℝ)⌋₊ + 1),
      linearIncrementWeight n k t * increment k =
    ∑ k ∈ Finset.range N,
      linearIncrementWeight n k t * increment k := by
  apply Finset.sum_subset (Finset.range_mono hN)
  intro k hk hkoutside
  have hfloor : ⌊(n : ℝ) * (t : ℝ)⌋₊ < k := by
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.le_of_not_gt (fun h => hkoutside (Finset.mem_range.mpr h)))
  rw [linearIncrementWeight_eq_zero_of_floor_lt hfloor, zero_mul]

/-- The unbounded-time polygonal path is continuous: on a
neighborhood of each time, its defining sum agrees with one fixed
finite sum of continuous weight functions. -/
theorem continuous_normalizedLinearPathUnbounded
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ) :
    Continuous (normalizedLinearPathUnbounded scale n increment) := by
  rw [continuous_iff_continuousAt]
  intro t
  let N : ℕ := ⌊(n : ℝ) * ((t + 1 : ℝ≥0) : ℝ)⌋₊ + 1
  let finitePath : ℝ≥0 → ℝ := fun u =>
    (scale n)⁻¹ * ∑ k ∈ Finset.range N,
      linearIncrementWeight n k u * increment k
  have hfinite : ContinuousAt finitePath t := by
    apply Continuous.continuousAt
    dsimp [finitePath]
    apply Continuous.mul continuous_const
    apply continuous_finsetSum
    intro k hk
    exact ((continuous_linearIncrementWeight n k).comp
      NNReal.continuous_coe).mul continuous_const
  have hnear : ∀ᶠ u in 𝓝 t,
      normalizedLinearPathUnbounded scale n increment u = finitePath u := by
    have hball : t < t + 1 := lt_add_of_pos_right t (by norm_num)
    filter_upwards [isOpen_Iio.mem_nhds hball] with u hu
    have hfloor : ⌊(n : ℝ) * (u : ℝ)⌋₊ + 1 ≤ N := by
      dsimp [N]
      apply Nat.add_le_add_right
      apply Nat.floor_le_floor
      exact mul_le_mul_of_nonneg_left
        (NNReal.coe_le_coe.mpr hu.le) (Nat.cast_nonneg n)
    unfold normalizedLinearPathUnbounded finitePath
    rw [sum_linearIncrementWeight_eq_range_of_floor_le n increment u hfloor]
  exact hfinite.congr_of_eventuallyEq hnear

/-- The entire normalized random-walk interpolation as a continuous
path on nonnegative time. -/
noncomputable def normalizedLinearContinuousPathUnbounded
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ) :
    C(ℝ≥0, ℝ) :=
  ⟨normalizedLinearPathUnbounded scale n increment,
    continuous_normalizedLinearPathUnbounded scale n increment⟩

/-- Measurability of the unbounded polygonal path under the
product measurable structure on increment sequences. -/
theorem measurable_normalizedLinearContinuousPathUnbounded
    (scale : ℕ → ℝ) (n : ℕ) :
    Measurable (normalizedLinearContinuousPathUnbounded scale n) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  exact measurable_const.mul (Finset.measurable_sum _ fun k _ =>
    measurable_const.mul (measurable_pi_apply k))

/-- On the first unit of time, the unbounded interpolation is exactly
the existing interpolation of the first `n` increments. -/
theorem normalizedLinearPathUnbounded_eq_bounded
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ)
    (t : ℝ≥0) (ht : t ≤ 1) :
    normalizedLinearPathUnbounded scale n increment t =
      normalizedLinearPath scale n increment t := by
  have hmul : (n : ℝ) * (t : ℝ) ≤ n := by
    calc
      (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr ht)
          (Nat.cast_nonneg n)
      _ = n := by ring
  have hfloor : ⌊(n : ℝ) * (t : ℝ)⌋₊ ≤ n :=
    Nat.floor_le_of_le hmul
  unfold normalizedLinearPathUnbounded normalizedLinearPath
  congr 1
  rcases hfloor.eq_or_lt with heq | hlt
  · rw [heq, Finset.sum_range_succ]
    have hweight : linearIncrementWeight n n (t : ℝ) = 0 := by
      unfold linearIncrementWeight
      rw [max_eq_left (sub_nonpos.mpr hmul)]
      simp
    simp [hweight]
  · exact sum_linearIncrementWeight_eq_range_of_floor_le
      n increment t (Nat.succ_le_iff.mpr hlt)

/-- Restricting the whole-time path to the unit interval recovers
the existing bounded continuous-path interpolation. -/
theorem normalizedLinearContinuousPathUnbounded_apply_unitInterval
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ)
    (t : unitInterval) :
    normalizedLinearContinuousPathUnbounded scale n increment
        (⟨(t : ℝ), t.property.1⟩ : ℝ≥0) =
      normalizedLinearContinuousPathIcc scale n increment t := by
  change normalizedLinearPathUnbounded scale n increment
    (⟨(t : ℝ), t.property.1⟩ : ℝ≥0) = normalizedLinearPath scale n increment t
  convert normalizedLinearPathUnbounded_eq_bounded scale n increment
    (⟨(t : ℝ), t.property.1⟩ : ℝ≥0)
    (show (⟨(t : ℝ), t.property.1⟩ : ℝ≥0) ≤ 1 from t.property.2) using 1 <;> rfl

end ProbabilityTheory.RandomWalk

end
