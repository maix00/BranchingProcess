import Combinatorics.BranchingWalk.Walk.Path.Block.Basic
import Mathlib.Analysis.SpecificLimits.FloorPow

/-!
# Proportional block lengths

Deterministic rounding facts for blocks whose length is asymptotic to a fixed
fraction of the total number of steps.
-/

open Filter Topology

namespace Combinatorics.Branching.Walk

/-- The integer block length obtained by rounding down a fixed fraction of a
discrete time horizon. -/
noncomputable def proportionalBlockLength (fraction : ℝ) (n : ℕ) : ℕ :=
  ⌊fraction * n⌋₊

/-- Rounding a positive proportional block length does not change its ratio
to the time horizon. -/
theorem tendsto_proportionalBlockLength_div
    {fraction : ℝ} (hfraction : 0 < fraction) :
    Tendsto (fun n : ℕ => (proportionalBlockLength fraction n : ℝ) / n)
      atTop (nhds fraction) := by
  have hargument : Tendsto (fun n : ℕ => fraction * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hfraction
  have hround := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hargument
  have hratio : Tendsto (fun n : ℕ =>
      (fraction * (n : ℝ)) / (n : ℝ)) atTop (nhds fraction) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    field_simp [hfraction.ne', hn.ne']
  have hproduct := hround.mul hratio
  have hproduct' : Tendsto (fun n : ℕ =>
      ((proportionalBlockLength fraction n : ℝ) /
          (fraction * (n : ℝ))) *
        (fraction * (n : ℝ) / (n : ℝ)))
      atTop (nhds fraction) := by
    simpa [Function.comp_def, proportionalBlockLength] using hproduct
  apply hproduct'.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [proportionalBlockLength]
  field_simp [hfraction.ne', hn.ne']

/-- Adding the endpoint coordinate to a proportional block has the same
asymptotic ratio. -/
theorem tendsto_proportionalBlockLength_add_one_div
    {fraction : ℝ} (hfraction : 0 < fraction) :
    Tendsto (fun n : ℕ =>
      ((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) / n)
      atTop (nhds fraction) := by
  have hone : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) := by
    simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  convert (tendsto_proportionalBlockLength_div hfraction).add hone using 1
  · funext n
    norm_num [Nat.cast_add]
    ring
  · rw [add_zero]

/-- Squared proportional block lengths have the corresponding squared
asymptotic ratio. -/
theorem tendsto_proportionalBlockLength_add_one_sq_div_sq
    {fraction : ℝ} (hfraction : 0 < fraction) :
    Tendsto (fun n : ℕ =>
      (((proportionalBlockLength fraction n + 1 : ℕ) : ℝ) ^ 2) /
        (n : ℝ) ^ 2)
      atTop (nhds (fraction ^ 2)) := by
  have h := (tendsto_proportionalBlockLength_add_one_div hfraction).pow 2
  apply h.congr'
  filter_upwards [] with n
  rw [div_pow]

end Combinatorics.Branching.Walk
