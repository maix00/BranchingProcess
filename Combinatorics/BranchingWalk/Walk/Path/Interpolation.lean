import Combinatorics.BranchingWalk.Walk.Path.Scaling
import Topology.Cadlag.Skorokhod.ContinuousMap

/-!
# Linear interpolation of random-walk paths

This file is deterministic. It constructs the continuous polygonal path
through the normalized partial sums. Probability laws are added separately.
-/

open Set

namespace Combinatorics.Branching.Walk

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
      (scale n)⁻¹ * partialSum n increment := by
  unfold normalizedLinearPath partialSum
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [linearIncrementWeight_one_of_lt (Finset.mem_range.mp hk), one_mul]

/-- At every grid time `k/n`, the polygonal interpolation agrees with the
normalized partial sum. -/
theorem normalizedLinearPath_grid (scale : ℕ → ℝ) {n k : ℕ}
    (hn : 0 < n) (hk : k ≤ n) (increment : ℕ → ℝ) :
    normalizedLinearPath scale n increment ((k : ℝ) / n) =
      (scale n)⁻¹ * partialSum k increment := by
  unfold normalizedLinearPath partialSum
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

/-- The normalized polygonal interpolation, restricted to `[0,1]` and
bundled as a continuous path. -/
noncomputable def normalizedLinearContinuousPathIcc
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ) :
    C(Skorokhod.UnitInterval, ℝ) where
  toFun t := normalizedLinearPath scale n increment t
  continuous_toFun :=
    (continuous_normalizedLinearPath scale n increment).comp
      continuous_subtype_val

@[simp]
theorem normalizedLinearContinuousPathIcc_apply
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ)
    (t : Skorokhod.UnitInterval) :
    normalizedLinearContinuousPathIcc scale n increment t =
      normalizedLinearPath scale n increment t :=
  rfl

/-- The same polygonal path, viewed in the Skorokhod càdlàg path space. -/
noncomputable def normalizedLinearCadlagPathIcc
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ) :
    CadlagPath Skorokhod.UnitInterval ℝ :=
  Skorokhod.ofContinuousMap
    (normalizedLinearContinuousPathIcc scale n increment)

@[simp]
theorem normalizedLinearCadlagPathIcc_apply
    (scale : ℕ → ℝ) (n : ℕ) (increment : ℕ → ℝ)
    (t : Skorokhod.UnitInterval) :
    normalizedLinearCadlagPathIcc scale n increment t =
      normalizedLinearPath scale n increment t :=
  rfl

end Combinatorics.Branching.Walk
