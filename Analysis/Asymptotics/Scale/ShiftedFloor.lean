/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.BlockScale
public import Mathlib.Analysis.Real.Sqrt

/-!
# Fixed shifts of rounded diffusive lengths

The public theorems in this file are:

- `Asymptotics.tendsto_floorBlockLength_sub_nat_div_of_argument_ratio`:
  if $a_n,b_n\to\infty$ and $a_n/b_n\to c$, then
  $(\lfloor a_n\rfloor-m)/b_n\to c$ for every fixed $m\in\mathbb N$.
- `Asymptotics.tendsto_width_div_sqrt_floor_sq_sub_nat`:
  if $\Delta_n\to\infty$, then
  $\Delta_n/\sqrt{\lfloor\Delta_n^2\rfloor-m}\to1$.

The second limit is the time-scale relation for the finite transition
event in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring* (master's thesis, Fudan University, 2026), Chapter 3,
Lemma 3.5 and Appendix A.2.
-/

@[expose] public section

open Filter Topology

namespace Asymptotics

/-- Subtracting a fixed number of steps after flooring a divergent block
argument does not affect its ratio to a divergent denominator. -/
theorem tendsto_floorBlockLength_sub_nat_div_of_argument_ratio
    {argument denominator : ℕ → ℝ} {limit : ℝ} (offset : ℕ)
    (hargument : Tendsto argument atTop atTop)
    (hdenominator : Tendsto denominator atTop atTop)
    (hratio : Tendsto (fun n => argument n / denominator n)
      atTop (nhds limit)) :
    Tendsto (fun n =>
      ((floorBlockLength argument n - offset : ℕ) : ℝ) /
        denominator n) atTop (nhds limit) := by
  have hbase : Tendsto (fun n =>
      (floorBlockLength argument n : ℝ) / denominator n)
      atTop (nhds limit) := by
    simpa using tendsto_floorBlockLength_add_nat_div_of_argument_ratio
      0 hargument hdenominator hratio
  have hoffset : Tendsto (fun n => (offset : ℝ) / denominator n)
      atTop (nhds 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (offset : ℝ))
      atTop (nhds (offset : ℝ))).div_atTop hdenominator
  have hdiff := hbase.sub hoffset
  have hlarge : ∀ᶠ n : ℕ in atTop,
      offset ≤ floorBlockLength argument n :=
    (tendsto_floorBlockLength_atTop hargument).eventually
      (eventually_ge_atTop offset)
  have heq : (fun n =>
      ((floorBlockLength argument n - offset : ℕ) : ℝ) /
        denominator n) =ᶠ[atTop]
      fun n => (floorBlockLength argument n : ℝ) / denominator n -
        (offset : ℝ) / denominator n := by
    filter_upwards [hlarge] with n hn
    rw [Nat.cast_sub hn]
    ring
  simpa using hdiff.congr' heq.symm

/-- The fixed finite entrance length does not alter the diffusive spatial
normalization $\Delta/\sqrt{\lfloor\Delta^2\rfloor-m}$. -/
theorem tendsto_width_div_sqrt_floor_sq_sub_nat
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (offset : ℕ) :
    Tendsto (fun n => width n /
      Real.sqrt (((floorBlockLength (fun n => width n ^ 2) n -
        offset : ℕ) : ℝ)))
      atTop (nhds 1) := by
  let argument : ℕ → ℝ := fun n => width n ^ 2
  have hpositive : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  have hargument : Tendsto argument atTop atTop := by
    have hmul : Tendsto (fun n => width n * width n) atTop atTop :=
      hwidth.atTop_mul_atTop₀ hwidth
    simpa [argument, pow_two] using hmul
  have hratio : Tendsto (fun n => argument n / argument n)
      atTop (nhds 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hpositive] with n hn
    simp [argument, pow_pos hn 2 |>.ne']
  have hquot := tendsto_floorBlockLength_sub_nat_div_of_argument_ratio
    offset hargument hargument hratio
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hquot
  have hsqrt' : Tendsto (fun n =>
      Real.sqrt (((floorBlockLength argument n - offset : ℕ) : ℝ) /
        argument n)) atTop (nhds 1) := by
    simpa only [Function.comp_def, Real.sqrt_one] using hsqrt
  have hfloorLarge : ∀ᶠ n : ℕ in atTop,
      offset ≤ floorBlockLength argument n :=
    (tendsto_floorBlockLength_atTop hargument).eventually
      (eventually_ge_atTop offset)
  have hsqrtRatio : Tendsto (fun n =>
      Real.sqrt (((floorBlockLength argument n - offset : ℕ) : ℝ)) /
        width n)
      atTop (nhds 1) := by
    apply hsqrt'.congr'
    filter_upwards [hpositive, hfloorLarge] with n hn hnFloor
    dsimp [argument]
    rw [Nat.cast_sub hnFloor]
    have hnum : 0 ≤ (floorBlockLength (fun n => width n ^ 2) n : ℝ) -
        (offset : ℝ) := sub_nonneg.mpr (by exact_mod_cast hnFloor)
    rw [Real.sqrt_div hnum, Real.sqrt_sq hn.le]
  simpa only [inv_div, inv_one, argument] using
    hsqrtRatio.inv₀ one_ne_zero

end Asymptotics

end
