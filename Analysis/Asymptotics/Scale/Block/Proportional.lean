/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic

import Analysis.Asymptotics.Scale.Block.Length

/-!
# Proportional block lengths

For a fixed fraction $\theta>0$, define $b_n=\lfloor\theta n\rfloor$. This
module records the limiting ratio $b_n/n\to\theta$, the corresponding limits
for $b_n+1$, and the eventual covering bound $n+1\leq m b_n$ whenever
$m\theta>1$. These are deterministic scale facts and do not depend on a
random walk.

## Public declarations

The declarations are `proportionalBlockLength`, its positive-fraction ratio
and shifted-ratio limits, and the eventual covering estimates for a fixed
number of proportional blocks.
-/

open Filter Topology

@[expose] public section

namespace Asymptotics

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
  simpa [proportionalBlockLength, floorBlockLength, mul_comm] using
    tendsto_floorTime_div_nat hfraction.le

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

end Asymptotics

end
