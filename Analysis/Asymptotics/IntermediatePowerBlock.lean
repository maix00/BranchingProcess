/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.BlockScale
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Intermediate power block lengths

The public theorems in this file are:

- `Asymptotics.intermediate_power_block_ratios`: if $\Delta_n\to\infty$
  and $0<\eta<1$, then for
  $\ell_n=\lfloor\Delta_n^{2+\eta}\rfloor$,
  $\Delta_n^2/\ell_n\to0$, $\ell_n/\Delta_n^3\to0$, and
  $\ell_n>0$ eventually.
- `Asymptotics.eventually_intermediate_block_fits`: if
  $0<\eta<\varepsilon$, then eventually
  $\lfloor\Delta_n^2\rfloor+2\lfloor\Delta_n^{2+\eta}\rfloor
  \le\lfloor\Delta_n^{2+\varepsilon}\rfloor$.

These deterministic ratios let a block exceed the diffusive time scale
while its drift displacement remains small compared with its width.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Asymptotics

/-- A floor-rounded intermediate power scale lies strictly between the
quadratic and cubic scales of any divergent positive width sequence. -/
theorem intermediate_power_block_ratios
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    let block : ℕ → ℕ := floorBlockLength (fun n => width n ^ (2 + η))
    Tendsto (fun n => width n ^ 2 / (block n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n => (block n : ℝ) / width n ^ 3) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, 0 < block n := by
  dsimp
  let block : ℕ → ℕ := floorBlockLength (fun n => width n ^ (2 + η))
  let argument : ℕ → ℝ := fun n => width n ^ (2 + η)
  have harg : Tendsto argument atTop atTop := by
    exact (tendsto_rpow_atTop (by linarith : 0 < 2 + η)).comp hwidth
  have hfloor : Tendsto (fun n => (block n : ℝ) / argument n)
      atTop (𝓝 1) := by
    simpa [block, argument] using tendsto_floorBlockLength_div_argument harg
  have hwidthpos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  have hblockpos : ∀ᶠ n : ℕ in atTop, 0 < block n := by
    exact (tendsto_floorBlockLength_atTop harg).eventually (eventually_gt_atTop 0)
  have htwo : Tendsto (fun n => argument n / width n ^ 2)
      atTop atTop := by
    have hpow := (tendsto_rpow_atTop hη).comp hwidth
    apply hpow.congr'
    filter_upwards [hwidthpos] with n hn
    dsimp [argument]
    rw [show 2 + η = η + 2 by ring, Real.rpow_add hn]
    field_simp [pow_ne_zero 2 hn.ne']
    norm_num [Real.rpow_natCast]
  have hfloorTwo : Tendsto (fun n => (block n : ℝ) / width n ^ 2)
      atTop atTop := by
    have hprod := hfloor.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) htwo
    apply hprod.congr'
    filter_upwards [hwidthpos] with n hn
    have hargpos : 0 < argument n := by dsimp [argument]; positivity
    field_simp [hargpos.ne', pow_ne_zero 2 hn.ne']
  have hquadratic : Tendsto (fun n => width n ^ 2 / (block n : ℝ))
      atTop (𝓝 0) := by
    have hinv := hfloorTwo.inv_tendsto_atTop
    apply hinv.congr'
    filter_upwards [hwidthpos, hblockpos] with n hn hb
    change ((block n : ℝ) / width n ^ 2)⁻¹ =
      width n ^ 2 / (block n : ℝ)
    field_simp [pow_ne_zero 2 hn.ne', (by exact_mod_cast hb.ne' : (block n : ℝ) ≠ 0)]
  have hthree : Tendsto (fun n => argument n / width n ^ 3)
      atTop (𝓝 0) := by
    have hpow := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - η)).comp hwidth
    apply hpow.congr'
    filter_upwards [hwidthpos] with n hn
    dsimp [argument]
    rw [show 2 + η = 3 + (-(1 - η)) by ring, Real.rpow_add hn]
    field_simp [pow_ne_zero 3 hn.ne']
    norm_num [Real.rpow_natCast]
  have hcubic : Tendsto (fun n => (block n : ℝ) / width n ^ 3)
      atTop (𝓝 0) := by
    have hprod : Tendsto (fun n =>
        (block n : ℝ) / argument n * (argument n / width n ^ 3))
        atTop (𝓝 0) := by simpa using hfloor.mul hthree
    apply hprod.congr'
    filter_upwards [hwidthpos] with n hn
    have hargpos : 0 < argument n := by dsimp [argument]; positivity
    field_simp [hargpos.ne', pow_ne_zero 3 hn.ne']
  exact ⟨hquadratic, hcubic, hblockpos⟩

private theorem tendsto_rpow_div_rpow_zero
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {p q : ℝ} (hpq : p < q) :
    Tendsto (fun n => width n ^ p / width n ^ q) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_neg_atTop (sub_pos.mpr hpq)).comp hwidth
  apply hpow.congr'
  filter_upwards [hwidth.eventually (eventually_gt_atTop 0)] with n hn
  calc
    _ = width n ^ (p - q) := by dsimp; congr 1; ring
    _ = _ := Real.rpow_sub hn p q

/-- A block of order $\Delta^{2+\eta}$ and the diffusive entrance fit
inside the minimum horizon of order $\Delta^{2+\varepsilon}$ whenever
$\eta<\varepsilon$. -/
theorem eventually_intermediate_block_fits
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {η ε : ℝ} (hη : 0 < η) (hηε : η < ε) :
    ∀ᶠ n : ℕ in atTop,
      floorBlockLength (fun n => width n ^ 2) n +
        2 * floorBlockLength (fun n => width n ^ (2 + η)) n ≤
      floorBlockLength (fun n => width n ^ (2 + ε)) n := by
  let argε : ℕ → ℝ := fun n => width n ^ (2 + ε)
  have hargε : Tendsto argε atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 2 + ε)).comp hwidth
  have hfloorε : Tendsto
      (fun n => (floorBlockLength argε n : ℝ) / argε n)
      atTop (𝓝 1) := tendsto_floorBlockLength_div_argument hargε
  have hfloorLower : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) ≤ (floorBlockLength argε n : ℝ) / argε n :=
    (hfloorε.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono
      (by intro n hn; exact hn.le)
  have hratio2 := tendsto_rpow_div_rpow_zero hwidth
    (by linarith : (2 : ℝ) < 2 + ε)
  have hratioη := tendsto_rpow_div_rpow_zero hwidth
    (by linarith : 2 + η < 2 + ε)
  have hratio : Tendsto (fun n => width n ^ 2 / argε n +
      2 * (width n ^ (2 + η) / argε n)) atTop (𝓝 0) := by
    simpa [argε] using hratio2.add (tendsto_const_nhds.mul hratioη)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      width n ^ 2 / argε n + 2 * (width n ^ (2 + η) / argε n) ≤ 1 / 2 :=
    (hratio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      (by intro n hn; exact hn.le)
  filter_upwards [hwidth.eventually (eventually_gt_atTop 0),
    hfloorLower, hsmall] with n hn hfloor hsmallN
  have hargpos : 0 < argε n := by dsimp [argε]; positivity
  have hentrance : (floorBlockLength (fun n => width n ^ 2) n : ℝ) ≤
      width n ^ 2 := Nat.floor_le (sq_nonneg _)
  have hblock : (floorBlockLength (fun n => width n ^ (2 + η)) n : ℝ) ≤
      width n ^ (2 + η) := Nat.floor_le (Real.rpow_nonneg hn.le _)
  have hsmall' : width n ^ 2 + 2 * width n ^ (2 + η) ≤
      argε n / 2 := by
    have hdiv : (width n ^ 2 + 2 * width n ^ (2 + η)) / argε n ≤
        (1 / 2 : ℝ) := by
      calc
        _ = width n ^ 2 / argε n +
            2 * (width n ^ (2 + η) / argε n) := by ring
        _ ≤ _ := hsmallN
    have h := (div_le_iff₀ hargpos).1 hdiv
    nlinarith
  have hlarge : argε n / 2 ≤ (floorBlockLength argε n : ℝ) := by
    have h := (le_div_iff₀ hargpos).1 hfloor
    nlinarith
  have hfinal : (floorBlockLength (fun n => width n ^ 2) n : ℝ) +
      2 * (floorBlockLength (fun n => width n ^ (2 + η)) n : ℝ) ≤
      (floorBlockLength argε n : ℝ) := by
    nlinarith
  exact_mod_cast hfinal

end Asymptotics

end
