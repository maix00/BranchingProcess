/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Cadlag
public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.ContinuousMap

/-!
# Linear interpolation of random-walk paths

This file is deterministic. It constructs the continuous polygonal path
through the normalized partial sums. Probability laws are added separately.
-/

open Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- Weight of increment `k` at continuous time `t` in the polygonal
interpolation with `n` equal time steps. -/
def linearIncrementWeight (n k : ℕ) (t : ℝ) : ℝ :=
  min 1 (max 0 ((n : ℝ) * t - k))

theorem continuous_linearIncrementWeight (n k : ℕ) :
    Continuous (linearIncrementWeight n k) := by
  unfold linearIncrementWeight
  fun_prop

theorem linearIncrementWeight_nonneg (n k : ℕ) (t : ℝ) :
    0 ≤ linearIncrementWeight n k t := by
  simp [linearIncrementWeight]

theorem linearIncrementWeight_le_one (n k : ℕ) (t : ℝ) :
    linearIncrementWeight n k t ≤ 1 := by
  simp [linearIncrementWeight]

@[simp]
theorem linearIncrementWeight_zero (n k : ℕ) :
    linearIncrementWeight n k 0 = 0 := by
  simp [linearIncrementWeight]

@[simp]
theorem linearIncrementWeight_one_of_lt {n k : ℕ} (hk : k < n) :
    linearIncrementWeight n k 1 = 1 := by
  have hcast : ((k + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hk
  have h : (1 : ℝ) ≤ (n : ℝ) - k := by
    push_cast at hcast
    linarith
  simp only [linearIncrementWeight, mul_one]
  rw [max_eq_right (by linarith), min_eq_left h]

theorem linearIncrementWeight_grid_of_lt {n k i : ℕ}
    (hn : 0 < n) (hi : i < k) :
    linearIncrementWeight n i ((k : ℝ) / n) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgrid : (n : ℝ) * ((k : ℝ) / n) = k := by field_simp
  have hcast : ((i + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hi
  have h : (1 : ℝ) ≤ (k : ℝ) - i := by
    push_cast at hcast
    linarith
  simp only [linearIncrementWeight, hgrid]
  rw [max_eq_right (by linarith), min_eq_left h]

theorem linearIncrementWeight_grid_of_le {n k i : ℕ}
    (hn : 0 < n) (hi : k ≤ i) :
    linearIncrementWeight n i ((k : ℝ) / n) = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hgrid : (n : ℝ) * ((k : ℝ) / n) = k := by field_simp
  have hcast : (k : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  simp only [linearIncrementWeight, hgrid]
  rw [max_eq_left (by linarith)]
  simp

theorem linearIncrementWeight_eq_one_of_lt_floor {n i : ℕ} {t : ℝ}
    (hnt : 0 ≤ (n : ℝ) * t) (hi : i < ⌊(n : ℝ) * t⌋₊) :
    linearIncrementWeight n i t = 1 := by
  have hcast : ((i + 1 : ℕ) : ℝ) ≤ (⌊(n : ℝ) * t⌋₊ : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hi
  have hfloor : (⌊(n : ℝ) * t⌋₊ : ℝ) ≤ (n : ℝ) * t :=
    Nat.floor_le hnt
  have h : (1 : ℝ) ≤ (n : ℝ) * t - i := by
    push_cast at hcast
    linarith
  simp only [linearIncrementWeight]
  rw [max_eq_right (by linarith), min_eq_left h]

theorem linearIncrementWeight_eq_zero_of_floor_lt {n i : ℕ} {t : ℝ}
    (hi : ⌊(n : ℝ) * t⌋₊ < i) :
    linearIncrementWeight n i t = 0 := by
  have hcast : ((⌊(n : ℝ) * t⌋₊ + 1 : ℕ) : ℝ) ≤ (i : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr hi
  have hlt : (n : ℝ) * t < (⌊(n : ℝ) * t⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  push_cast at hcast
  simp only [linearIncrementWeight]
  rw [max_eq_left (by linarith)]
  simp

/-- The normalized polygonal interpolation of the first `n` increments. -/
noncomputable def normalizedLinearPath (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) (t : ℝ) : ℝ :=
  (scale n)⁻¹ * ∑ k ∈ Finset.range n,
    linearIncrementWeight n k t * increment k

theorem continuous_normalizedLinearPath (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    Continuous (normalizedLinearPath scale n increment) := by
  unfold normalizedLinearPath
  exact continuous_const.mul <| continuous_finsetSum _ fun k _ ↦
    (continuous_linearIncrementWeight n k).mul continuous_const

@[simp]
theorem normalizedLinearPath_zero (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    normalizedLinearPath scale n increment 0 = 0 := by
  simp [normalizedLinearPath]

/-- At time one the polygonal path reaches the normalized `n`-step sum. -/
@[simp]
theorem normalizedLinearPath_one (scale : ℕ → ℝ) (n : ℕ)
    (increment : ℕ → ℝ) :
    normalizedLinearPath scale n increment 1 =
      (scale n)⁻¹ * AdditivePath.displacement n increment := by
  unfold normalizedLinearPath AdditivePath.displacement
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [linearIncrementWeight_one_of_lt (Finset.mem_range.mp hk), one_mul]

/-- At every grid time `k/n`, the polygonal interpolation agrees with the
normalized partial sum. -/
theorem normalizedLinearPath_grid (scale : ℕ → ℝ) {n k : ℕ}
    (hn : 0 < n) (hk : k ≤ n) (increment : ℕ → ℝ) :
    normalizedLinearPath scale n increment ((k : ℝ) / n) =
      (scale n)⁻¹ * AdditivePath.displacement k increment := by
  unfold normalizedLinearPath AdditivePath.displacement
  congr 1
  calc
    ∑ i ∈ Finset.range n,
        linearIncrementWeight n i ((k : ℝ) / n) * increment i =
        ∑ i ∈ Finset.range k,
          linearIncrementWeight n i ((k : ℝ) / n) * increment i := by
      symm
      apply Finset.sum_subset (Finset.range_mono hk)
      intro i hi hnmem
      rw [linearIncrementWeight_grid_of_le hn]
      · simp
      · exact Nat.le_of_not_gt (fun hik ↦ hnmem (Finset.mem_range.mpr hik))
    _ = ∑ i ∈ Finset.range k, increment i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [linearIncrementWeight_grid_of_lt hn (Finset.mem_range.mp hi), one_mul]

theorem sum_linearIncrementWeight_eq_partialSum_add
    {n : ℕ} {t : ℝ} (ht : 0 ≤ t)
    (hfloor : ⌊(n : ℝ) * t⌋₊ < n) (increment : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, linearIncrementWeight n i t * increment i =
      AdditivePath.displacement ⌊(n : ℝ) * t⌋₊ increment +
        linearIncrementWeight n ⌊(n : ℝ) * t⌋₊ t *
          increment ⌊(n : ℝ) * t⌋₊ := by
  let m := ⌊(n : ℝ) * t⌋₊
  let f : ℕ → ℝ := fun i ↦ linearIncrementWeight n i t * increment i
  have hnt : 0 ≤ (n : ℝ) * t :=
    mul_nonneg (Nat.cast_nonneg n) ht
  have hleft : ∑ i ∈ Finset.range m, f i = AdditivePath.displacement m increment := by
    unfold AdditivePath.displacement
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [f, m]
    rw [linearIncrementWeight_eq_one_of_lt_floor hnt
      (Finset.mem_range.mp hi), one_mul]
  have hright : ∑ i ∈ Finset.Ico m n, f i = f m := by
    apply Finset.sum_eq_single m
    · intro i hi him
      have hmi : m < i := lt_of_le_of_ne (Finset.mem_Ico.mp hi).1 him.symm
      dsimp [f, m] at hmi ⊢
      rw [linearIncrementWeight_eq_zero_of_floor_lt hmi, zero_mul]
    · intro hm
      exact (hm (Finset.mem_Ico.mpr ⟨le_rfl, hfloor⟩)).elim
  change ∑ i ∈ Finset.range n, f i =
    AdditivePath.displacement m increment + f m
  rw [← Finset.sum_range_add_sum_Ico f (Nat.le_of_lt hfloor),
    hleft, hright]

/-- At a time in `[0,1]`, polygonal interpolation differs from the
right-continuous step path by at most the size of the current normalized
increment. -/
theorem abs_normalizedLinearPath_sub_normalizedStepPath_le
    (scale : ℕ → ℝ) {n : ℕ} (increment : ℕ → ℝ)
    (t : unitInterval) :
    |normalizedLinearPath scale n increment t -
        normalizedStepPath scale n increment t| ≤
      |(scale n)⁻¹| * |increment ⌊(n : ℝ) * (t : ℝ)⌋₊| := by
  let m := ⌊(n : ℝ) * (t : ℝ)⌋₊
  have hmn : m ≤ n := by
    apply Nat.floor_le_of_le
    calc
      (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
      _ = n := by ring
  by_cases hmlt : m < n
  · have hsum := sum_linearIncrementWeight_eq_partialSum_add
      t.property.1 hmlt increment
    rw [normalizedLinearPath, normalizedStepPath, hsum]
    rw [mul_add, add_sub_cancel_left, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (abs_nonneg _) <|
        abs_le.2 ⟨by
          linarith [linearIncrementWeight_nonneg n m t], by
          simpa using linearIncrementWeight_le_one n m t⟩)
      (abs_nonneg _)
  · have hmeq : m = n := Nat.le_antisymm hmn (Nat.le_of_not_gt hmlt)
    have hnt : 0 ≤ (n : ℝ) * (t : ℝ) :=
      mul_nonneg (Nat.cast_nonneg n) t.property.1
    have hsum :
        ∑ i ∈ Finset.range n,
            linearIncrementWeight n i t * increment i =
          AdditivePath.displacement n increment := by
      unfold AdditivePath.displacement
      apply Finset.sum_congr rfl
      intro i hi
      have him : i < m := by simpa [hmeq] using Finset.mem_range.mp hi
      rw [linearIncrementWeight_eq_one_of_lt_floor hnt him, one_mul]
    rw [normalizedLinearPath, normalizedStepPath, hsum]
    change |(scale n)⁻¹ * AdditivePath.displacement n increment -
        (scale n)⁻¹ * AdditivePath.displacement m increment| ≤
      |(scale n)⁻¹| * |increment m|
    rw [hmeq]
    simp only [sub_self, abs_zero]
    positivity

/-- Largest absolute increment among indices `0, ..., n`. -/
def maxAbsUpTo (n : ℕ) (increment : ℕ → ℝ) : ℝ :=
  (Finset.range (n + 1)).sup' (by simp) fun k ↦ |increment k|

theorem abs_increment_le_maxAbsUpTo {n k : ℕ} (increment : ℕ → ℝ)
    (hk : k ≤ n) :
    |increment k| ≤ maxAbsUpTo n increment := by
  exact Finset.le_sup' (fun i ↦ |increment i|)
    (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))

theorem maxAbsUpTo_nonneg (n : ℕ) (increment : ℕ → ℝ) :
    0 ≤ maxAbsUpTo n increment := by
  exact (abs_nonneg (increment 0)).trans
    (abs_increment_le_maxAbsUpTo increment (Nat.zero_le n))

/-- The normalized polygonal interpolation, restricted to `[0,1]` and
bundled as a continuous path. -/
noncomputable def normalizedLinearContinuousPathIcc
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ) :
    C(unitInterval, ℝ) where
  toFun t := normalizedLinearPath scale n increment t
  continuous_toFun :=
    (continuous_normalizedLinearPath scale n increment).comp
      continuous_subtype_val

@[simp]
theorem normalizedLinearContinuousPathIcc_apply
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ)
    (t : unitInterval) :
    normalizedLinearContinuousPathIcc scale n increment t =
      normalizedLinearPath scale n increment t :=
  rfl

/-- The same polygonal path, viewed in the Skorokhod càdlàg path space. -/
noncomputable def normalizedLinearCadlagPathIcc
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ) :
    CadlagPath unitInterval ℝ :=
  Skorokhod.ofContinuousMap
    (normalizedLinearContinuousPathIcc scale n increment)

@[simp]
theorem normalizedLinearCadlagPathIcc_apply
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ)
    (t : unitInterval) :
    normalizedLinearCadlagPathIcc scale n increment t =
      normalizedLinearPath scale n increment t :=
  rfl

/-- The Skorokhod distance from the right-continuous step path to its
polygonal interpolation is controlled by the largest normalized jump. -/
theorem j1EDist_normalizedStepPath_linear_le
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ) :
    Skorokhod.j1EDist (normalizedStepCadlagPathIcc scale n increment)
        (normalizedLinearCadlagPathIcc scale n increment) ≤
      ENNReal.ofReal (|(scale n)⁻¹| * maxAbsUpTo n increment) := by
  refine (Skorokhod.j1EDist_le_uniformEDist _ _).trans ?_
  refine iSup_le fun t ↦ ?_
  rw [edist_dist, Real.dist_eq]
  apply ENNReal.ofReal_le_ofReal
  rw [abs_sub_comm]
  exact (abs_normalizedLinearPath_sub_normalizedStepPath_le
    scale increment t).trans <| mul_le_mul_of_nonneg_left
      (abs_increment_le_maxAbsUpTo increment
        (Nat.floor_le_of_le <| by
          calc
            (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
            _ = n := by ring))
      (abs_nonneg _)

end ProbabilityTheory.RandomWalk
