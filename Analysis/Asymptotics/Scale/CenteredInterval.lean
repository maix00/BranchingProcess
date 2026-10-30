/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Centered lattice intervals at a prescribed scale

## Public declarations

For a positive real scale $s_n$, define the integer radius
\[
  r_n=\left\lfloor\frac{s_n}{2}\right\rfloor+1.
\]
The corresponding centered interval has integer width $2r_n$, and its
Dirichlet width is $2(r_n+1)$. Both widths are asymptotic to $s_n$ when
$s_n\to\infty$. This is the deterministic rounding interface used by
finite-interval random-walk estimates.

The public declarations are:

- `centeredLatticeRadius` and `centeredLatticeRadius_pos` give the positive
  integer radius.
- `tendsto_centeredLatticeWidth_div` and
  `tendsto_centeredDirichletWidth_div` show that the lattice and Dirichlet
  widths divided by the requested scale tend to one.
- `tendsto_centeredLatticeRadius_atTop` shows that the rounded radius
  diverges with the scale.
-/

open Filter Topology

@[expose] public section

namespace Asymptotics

/-- A positive integer radius obtained by rounding half of a real spatial
scale down and adding one. -/
noncomputable def centeredLatticeRadius (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊scale n / 2⌋₊ + 1

@[simp] theorem centeredLatticeRadius_pos (scale : ℕ → ℝ) (n : ℕ) :
    0 < centeredLatticeRadius scale n := by
  simp [centeredLatticeRadius]

private lemma tendsto_half_scale_atTop {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n => scale n / 2) atTop atTop := by
  simpa [div_eq_mul_inv, mul_comm] using
    hscale.const_mul_atTop (by norm_num : (0 : ℝ) < 2⁻¹)

/-- The integer width of the rounded centered interval is asymptotic to the
requested real scale. -/
theorem tendsto_centeredLatticeWidth_div
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n =>
      (((2 * centeredLatticeRadius scale n : ℕ) : ℝ) / scale n))
      atTop (nhds 1) := by
  have hhalf := tendsto_half_scale_atTop hscale
  have hfloor := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hhalf
  have hinv := tendsto_inv_atTop_zero.comp hscale
  have herror : Tendsto (fun n => 2 / scale n) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv :
      Tendsto (fun n => (2 : ℝ) * (scale n)⁻¹) atTop (nhds (2 * 0)))
  have hsum := hfloor.add herror
  convert hsum using 1
  · funext n
    simp only [centeredLatticeRadius, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_add, Nat.cast_one]
    simp only [Function.comp_apply, div_eq_mul_inv]
    ring
  · norm_num

/-- The effective Dirichlet width, including its two killing sites, is
asymptotic to the requested real scale. -/
theorem tendsto_centeredDirichletWidth_div
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n =>
      (((2 * (centeredLatticeRadius scale n + 1) : ℕ) : ℝ) / scale n))
      atTop (nhds 1) := by
  have hmain := tendsto_centeredLatticeWidth_div hscale
  have hinv := tendsto_inv_atTop_zero.comp hscale
  have herror : Tendsto (fun n => 2 / scale n) atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv :
      Tendsto (fun n => (2 : ℝ) * (scale n)⁻¹) atTop (nhds (2 * 0)))
  have hsum := hmain.add herror
  convert hsum using 1
  · funext n
    push_cast
    ring
  · norm_num

/-- The rounded centered radius tends to infinity with the real scale. -/
theorem tendsto_centeredLatticeRadius_atTop
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop) :
    Tendsto (fun n => (centeredLatticeRadius scale n : ℝ))
      atTop atTop := by
  have hfloor : Tendsto (fun n => ⌊scale n / 2⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_half_scale_atTop hscale)
  have hcast : Tendsto (fun n => (⌊scale n / 2⌋₊ : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hfloor
  simpa [centeredLatticeRadius] using
    tendsto_atTop_add_const_right atTop 1 hcast

end Asymptotics

end
