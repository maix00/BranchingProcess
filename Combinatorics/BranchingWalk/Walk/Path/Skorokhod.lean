/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Path.Cadlag
public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.Topology

/-!
# Random-walk step paths in the Skorokhod topology

For a fixed number of steps, the normalized step path depends continuously on
the increment path equipped with the product topology.  The proof controls
the Skorokhod distance by the `L¹` difference of the finite increment prefix.
-/

open Filter Set
open scoped BigOperators ENNReal Topology

@[expose] public section

namespace Combinatorics.Branching.Walk

/-- `L¹` distance between the first `n` coordinates of two real paths. -/
def prefixL1Distance (n : ℕ) (x y : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, |x k - y k|

theorem prefixL1Distance_nonneg (n : ℕ) (x y : ℕ → ℝ) :
    0 ≤ prefixL1Distance n x y := by
  exact Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

theorem prefixL1Distance_comm (n : ℕ) (x y : ℕ → ℝ) :
    prefixL1Distance n x y = prefixL1Distance n y x := by
  simp only [prefixL1Distance, abs_sub_comm]

@[simp]
theorem prefixL1Distance_self (n : ℕ) (x : ℕ → ℝ) :
    prefixL1Distance n x x = 0 := by
  simp [prefixL1Distance]

theorem continuous_prefixL1Distance_right (n : ℕ) (x : ℕ → ℝ) :
    Continuous (fun y : ℕ → ℝ ↦ prefixL1Distance n x y) := by
  unfold prefixL1Distance
  fun_prop

theorem abs_partialSum_sub_le_prefixL1Distance {m n : ℕ} (hmn : m ≤ n)
    (x y : ℕ → ℝ) :
    |partialSum m x - partialSum m y| ≤ prefixL1Distance n x y := by
  calc
    |partialSum m x - partialSum m y| =
        |∑ k ∈ Finset.range m, (x k - y k)| := by
      simp [partialSum, Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ Finset.range m, |x k - y k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, |x k - y k| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
        (fun _ _ _ ↦ abs_nonneg _)
    _ = prefixL1Distance n x y := rfl

theorem natFloor_mul_le_of_mem_unitInterval (n : ℕ)
    (t : unitInterval) : ⌊(n : ℝ) * (t : ℝ)⌋₊ ≤ n := by
  apply Nat.floor_le_of_le
  calc
    (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
    _ = n := by ring

theorem dist_normalizedStepPath_le_prefixL1Distance
    (scale : ℕ → ℝ) (n : ℕ) (x y : ℕ → ℝ)
    (t : unitInterval) :
    dist (normalizedStepCadlagPathIcc scale n x t)
        (normalizedStepCadlagPathIcc scale n y t) ≤
      |(scale n)⁻¹| * prefixL1Distance n x y := by
  rw [Real.dist_eq]
  simp only [normalizedStepCadlagPathIcc_apply, normalizedStepPath]
  rw [← mul_sub]
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left
    (abs_partialSum_sub_le_prefixL1Distance
      (natFloor_mul_le_of_mem_unitInterval n t) x y)
    (abs_nonneg _)

theorem j1EDist_normalizedStepCadlagPathIcc_le
    (scale : ℕ → ℝ) (n : ℕ) (x y : ℕ → ℝ) :
    Skorokhod.j1EDist (normalizedStepCadlagPathIcc scale n x)
        (normalizedStepCadlagPathIcc scale n y) ≤
      ENNReal.ofReal (|(scale n)⁻¹| * prefixL1Distance n x y) := by
  refine (Skorokhod.j1EDist_le_uniformEDist _ _).trans ?_
  refine iSup_le fun t ↦ ?_
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal
    (dist_normalizedStepPath_le_prefixL1Distance scale n x y t)

/-- For fixed `n`, the normalized step path is continuous into the
Skorokhod pseudo-emetric path space. -/
theorem continuous_normalizedStepCadlagPathIcc
    (scale : ℕ → ℝ) (n : ℕ) :
    Continuous (normalizedStepCadlagPathIcc scale n) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
  have hupper : Tendsto
      (fun y : ℕ → ℝ ↦
        ENNReal.ofReal (|(scale n)⁻¹| * prefixL1Distance n x y))
      (nhds x) (nhds 0) := by
    have hc : Continuous (fun y : ℕ → ℝ ↦
        ENNReal.ofReal (|(scale n)⁻¹| * prefixL1Distance n x y)) :=
      ENNReal.continuous_ofReal.comp
        (continuous_const.mul (continuous_prefixL1Distance_right n x))
    have hcx : Tendsto
        (fun y : ℕ → ℝ ↦
          ENNReal.ofReal (|(scale n)⁻¹| * prefixL1Distance n x y))
        (nhds x)
        (nhds (ENNReal.ofReal
          (|(scale n)⁻¹| * prefixL1Distance n x x))) :=
      hc.continuousAt
    simpa using hcx
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Eventually.of_forall fun _ ↦ bot_le
  · exact Eventually.of_forall fun y ↦ by
      simpa [Skorokhod.edist_cadlagPath_eq_j1EDist,
        prefixL1Distance_comm] using
        j1EDist_normalizedStepCadlagPathIcc_le scale n y x

theorem measurable_normalizedStepCadlagPathIcc
    (scale : ℕ → ℝ) (n : ℕ) :
    Measurable (normalizedStepCadlagPathIcc scale n) :=
  (continuous_normalizedStepCadlagPathIcc scale n).measurable

end Combinatorics.Branching.Walk
