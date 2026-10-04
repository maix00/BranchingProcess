/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Block.Basic
public import Mathlib.Analysis.SpecificLimits.FloorPow

/-!
# Proportional block lengths

Deterministic rounding facts for blocks whose length is asymptotic to a fixed
fraction of the total number of steps.
-/

open Filter Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk

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

/-- A positive proportional block length is eventually nonzero. -/
theorem eventually_proportionalBlockLength_pos
    {fraction : ℝ} (hfraction : 0 < fraction) :
    ∀ᶠ n : ℕ in atTop, 0 < proportionalBlockLength fraction n := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      fraction / 2 < (proportionalBlockLength fraction n : ℝ) / n :=
    (tendsto_proportionalBlockLength_div hfraction).eventually
      (Ioi_mem_nhds (half_lt_self hfraction))
  filter_upwards [hratio, eventually_gt_atTop 0] with n hratio hn
  by_contra hzero
  have hlength : proportionalBlockLength fraction n = 0 :=
    Nat.eq_zero_of_not_pos hzero
  rw [hlength, Nat.cast_zero, zero_div] at hratio
  linarith

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

/-- If the total asymptotic length of a fixed number of proportional blocks
is strictly larger than the time horizon, then those blocks eventually cover
the endpoint as well.  The strict inequality absorbs the error from rounding
each block length down. -/
theorem eventually_succ_le_mul_proportionalBlockLength
    (blocks : ℕ) {fraction : ℝ}
    (hcover : 1 < (blocks : ℝ) * fraction) :
    ∀ᶠ n : ℕ in atTop,
      n + 1 ≤ blocks * proportionalBlockLength fraction n := by
  have hfraction : 0 < fraction := by
    have hblocks : 0 ≤ (blocks : ℝ) := Nat.cast_nonneg blocks
    nlinarith
  have hlimit :=
    (tendsto_proportionalBlockLength_div hfraction).const_mul (blocks : ℝ)
  have hratio : ∀ᶠ n : ℕ in atTop,
      1 < (blocks : ℝ) *
        ((proportionalBlockLength fraction n : ℝ) / n) :=
    hlimit.eventually (Ioi_mem_nhds hcover)
  filter_upwards [hratio, eventually_gt_atTop 0] with n hnRatio hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnRatio' : 1 <
      ((blocks : ℝ) * (proportionalBlockLength fraction n : ℝ)) / n := by
    simpa [mul_div_assoc] using hnRatio
  have hcast : (n : ℝ) <
      (blocks * proportionalBlockLength fraction n : ℕ) := by
    rw [Nat.cast_mul]
    simpa using (lt_div_iff₀ hnReal).mp hnRatio'
  exact Nat.succ_le_iff.mpr ((Nat.cast_lt).mp hcast)

/-- The endpoint-covering result in the weaker form needed for indices
strictly below the time horizon. -/
theorem eventually_le_mul_proportionalBlockLength
    (blocks : ℕ) {fraction : ℝ}
    (hcover : 1 < (blocks : ℝ) * fraction) :
    ∀ᶠ n : ℕ in atTop,
      n ≤ blocks * proportionalBlockLength fraction n := by
  filter_upwards
    [eventually_succ_le_mul_proportionalBlockLength blocks hcover] with n hn
  exact (Nat.le_succ n).trans hn

end ProbabilityTheory.RandomWalk

end
