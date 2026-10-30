/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.Block.Length
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Intermediate power block lengths

## Public declarations

- `Asymptotics.intermediate_power_block_ratios`: for $0<p<q<r$ and
  $\Delta_n\to\infty$, the rounded scale
  $\ell_n=\lfloor\Delta_n^q\rfloor$ satisfies
  $\Delta_n^p/\ell_n\to0$, $\ell_n/\Delta_n^r\to0$, and
  $\ell_n>0$ eventually.
- `Asymptotics.eventually_intermediate_block_fits`: for $0<p<q<r$,
  eventually $\lfloor\Delta_n^p\rfloor+2\lfloor\Delta_n^q\rfloor
  \le\lfloor\Delta_n^r\rfloor$.
- `Asymptotics.eventually_nat_floor_rpow_intermediate_bounds`: if
  $0<p<q$, then for large $x$, the rounded block length
  $\lfloor x^q\rfloor$ lies between $x^p$ and $x^q$, with the floor error
  absorbed by the lower power.

These deterministic estimates choose an intermediate scale between any two
power regimes and bound a finite entrance-plus-block allocation.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Asymptotics

private lemma tendsto_rpow_div_rpow_zero
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {p q : ℝ} (hpq : p < q) :
    Tendsto (fun n => width n ^ p / width n ^ q) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_neg_atTop (sub_pos.mpr hpq)).comp hwidth
  apply hpow.congr'
  filter_upwards [hwidth.eventually (eventually_gt_atTop 0)] with n hn
  calc
    _ = width n ^ (p - q) := by dsimp; congr 1; ring
    _ = _ := Real.rpow_sub hn p q

/-- For exponents `0 < p < q`, the floor of `x ^ q` eventually lies above
the lower power `x ^ p`; the floor error is absorbed by that same lower
power. This is a deterministic estimate for intermediate power block
lengths. -/
theorem eventually_nat_floor_rpow_intermediate_bounds
    {p q : ℝ} (hp : 0 < p) (hpq : p < q) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ (⌊x ^ q⌋₊ : ℝ) ∧
      x ^ q - x ^ p ≤ (⌊x ^ q⌋₊ : ℝ) ∧
      x ^ p ≤ (⌊x ^ q⌋₊ : ℝ) ∧
      (⌊x ^ q⌋₊ : ℝ) ≤ x ^ q := by
  have hpLarge : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ p :=
    (_root_.tendsto_rpow_atTop hp).eventually (eventually_ge_atTop 2)
  have hgapLarge : ∀ᶠ x : ℝ in atTop, 2 ≤ x ^ (q - p) :=
    (_root_.tendsto_rpow_atTop (sub_pos.mpr hpq)).eventually
      (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hpLarge, hgapLarge]
    with x hx hxLarge hgapLarge
  have hxPos : 0 < x := by linarith
  have hqSplit : x ^ q = x ^ p * x ^ (q - p) := by
    rw [← Real.rpow_add hxPos]
    congr 1
    ring
  have hgap : 1 ≤ x ^ q - x ^ p := by
    rw [hqSplit]
    have hfactor : 1 ≤ x ^ (q - p) - 1 := by linarith
    have hproduct : x ^ p ≤ x ^ p * (x ^ (q - p) - 1) :=
      (le_mul_of_one_le_right (by positivity) hfactor)
    have hproductEq : x ^ p * (x ^ (q - p) - 1) =
        x ^ p * x ^ (q - p) - x ^ p := by ring
    rw [hproductEq] at hproduct
    exact le_trans (by linarith) hproduct
  have hfloorLower : x ^ q - 1 < (⌊x ^ q⌋₊ : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (x ^ q)
    have hfloorReal : x ^ q < (⌊x ^ q⌋₊ : ℝ) + 1 := by
      exact_mod_cast hfloor
    linarith
  have hfloorPos : 1 ≤ (⌊x ^ q⌋₊ : ℝ) := by
    exact (by linarith : (1 : ℝ) ≤ x ^ p).trans
      (le_trans (by linarith : x ^ p ≤ x ^ q - 1) hfloorLower.le)
  have hgapFloor : x ^ q - x ^ p ≤ (⌊x ^ q⌋₊ : ℝ) := by
    exact (by linarith : x ^ q - x ^ p ≤ x ^ q - 1).trans hfloorLower.le
  have hpowerFloor : x ^ p ≤ (⌊x ^ q⌋₊ : ℝ) := by
    exact (by linarith : x ^ p ≤ x ^ q - 1).trans hfloorLower.le
  have hfloorUpper : (⌊x ^ q⌋₊ : ℝ) ≤ x ^ q :=
    Nat.floor_le (Real.rpow_nonneg (le_trans (by norm_num) hx) q)
  exact ⟨hfloorPos, hgapFloor, hpowerFloor, hfloorUpper⟩

/-- For any $0<p<q<r$, the floor-rounded block
$\lfloor \Delta^q \rfloor$ separates the lower and upper power scales:
$\Delta^p/\lfloor\Delta^q\rfloor\to0$ and
$\lfloor\Delta^q\rfloor/\Delta^r\to0$. -/
theorem intermediate_power_block_ratios
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {p q r : ℝ} (hp : 0 < p) (hpq : p < q) (hqr : q < r) :
    let block : ℕ → ℕ := floorBlockLength (fun n => width n ^ q)
    Tendsto (fun n => width n ^ p / (block n : ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun n => (block n : ℝ) / width n ^ r) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, 0 < block n := by
  dsimp
  let block : ℕ → ℕ := floorBlockLength (fun n => width n ^ q)
  let argument : ℕ → ℝ := fun n => width n ^ q
  have harg : Tendsto argument atTop atTop := by
    exact (tendsto_rpow_atTop (by linarith : 0 < q)).comp hwidth
  have hfloor : Tendsto (fun n => (block n : ℝ) / argument n)
      atTop (𝓝 1) := by
    simpa [block, argument] using tendsto_floorBlockLength_div_argument harg
  have hwidthpos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  have hblockpos : ∀ᶠ n : ℕ in atTop, 0 < block n := by
    exact (tendsto_floorBlockLength_atTop harg).eventually (eventually_gt_atTop 0)
  have hqOverP : Tendsto (fun n => argument n / width n ^ p) atTop atTop := by
    have hpow := (tendsto_rpow_atTop (sub_pos.mpr hpq)).comp hwidth
    apply hpow.congr'
    filter_upwards [hwidthpos] with n hn
    dsimp [argument]
    exact Real.rpow_sub hn q p
  have hfloorOverP : Tendsto (fun n => (block n : ℝ) / width n ^ p)
      atTop atTop := by
    have hprod := hfloor.pos_mul_atTop (by norm_num : (0 : ℝ) < 1) hqOverP
    apply hprod.congr'
    filter_upwards [hwidthpos] with n hn
    have hargpos : 0 < argument n := by dsimp [argument]; positivity
    field_simp [ne_of_gt hargpos, ne_of_gt (Real.rpow_pos_of_pos hn p)]
  have hlower : Tendsto (fun n => width n ^ p / (block n : ℝ))
      atTop (𝓝 0) := by
    have hinv := hfloorOverP.inv_tendsto_atTop
    apply hinv.congr'
    filter_upwards [hwidthpos, hblockpos] with n hn hb
    change ((block n : ℝ) / width n ^ p)⁻¹ = width n ^ p / (block n : ℝ)
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hn p),
      (by exact_mod_cast hb.ne' : (block n : ℝ) ≠ 0)]
  have hupper : Tendsto (fun n => (block n : ℝ) / width n ^ r)
      atTop (𝓝 0) := by
    have hratio := tendsto_rpow_div_rpow_zero hwidth hqr
    have hprod : Tendsto (fun n =>
        (block n : ℝ) / argument n * (argument n / width n ^ r))
        atTop (𝓝 0) := by simpa using hfloor.mul hratio
    apply hprod.congr'
    filter_upwards [hwidthpos] with n hn
    have hargpos : 0 < argument n := by dsimp [argument]; positivity
    field_simp [ne_of_gt hargpos, ne_of_gt (Real.rpow_pos_of_pos hn r)]
  exact ⟨hlower, hupper, hblockpos⟩

/-- For any $0<p<q<r$, a block of order $\Delta^q$ and an entrance of order
$\Delta^p$ fit inside a horizon of order $\Delta^r$ eventually. -/
theorem eventually_intermediate_block_fits
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    {p q r : ℝ} (hp : 0 < p) (hpq : p < q) (hqr : q < r) :
    ∀ᶠ n : ℕ in atTop,
      floorBlockLength (fun n => width n ^ p) n +
        2 * floorBlockLength (fun n => width n ^ q) n ≤
      floorBlockLength (fun n => width n ^ r) n := by
  let arghorizon : ℕ → ℝ := fun n => width n ^ r
  have harg : Tendsto arghorizon atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < r)).comp hwidth
  have hfloor : Tendsto
      (fun n => (floorBlockLength arghorizon n : ℝ) / arghorizon n)
      atTop (𝓝 1) := tendsto_floorBlockLength_div_argument harg
  have hfloorLower : ∀ᶠ n : ℕ in atTop,
      (1 / 2 : ℝ) ≤ (floorBlockLength arghorizon n : ℝ) / arghorizon n :=
    (hfloor.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono
      (by intro n hn; exact hn.le)
  have hratioP := tendsto_rpow_div_rpow_zero hwidth (by linarith : p < r)
  have hratioQ := tendsto_rpow_div_rpow_zero hwidth hqr
  have hratio : Tendsto (fun n => width n ^ p / arghorizon n +
      2 * (width n ^ q / arghorizon n)) atTop (𝓝 0) := by
    simpa [arghorizon] using hratioP.add (tendsto_const_nhds.mul hratioQ)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      width n ^ p / arghorizon n + 2 * (width n ^ q / arghorizon n) ≤ 1 / 2 :=
    (hratio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono
      (by intro n hn; exact hn.le)
  filter_upwards [hwidth.eventually (eventually_gt_atTop 0),
    hfloorLower, hsmall] with n hn hfloor hsmallN
  have hargpos : 0 < arghorizon n := by dsimp [arghorizon]; positivity
  have hentrance : (floorBlockLength (fun n => width n ^ p) n : ℝ) ≤
      width n ^ p := Nat.floor_le (Real.rpow_nonneg hn.le _)
  have hblock : (floorBlockLength (fun n => width n ^ q) n : ℝ) ≤
      width n ^ q := Nat.floor_le (Real.rpow_nonneg hn.le _)
  have hsmall' : width n ^ p + 2 * width n ^ q ≤ arghorizon n / 2 := by
    have hdiv : (width n ^ p + 2 * width n ^ q) / arghorizon n ≤
        (1 / 2 : ℝ) := by
      calc
        _ = width n ^ p / arghorizon n +
            2 * (width n ^ q / arghorizon n) := by ring
        _ ≤ _ := hsmallN
    have h := (div_le_iff₀ hargpos).1 hdiv
    nlinarith
  have hlarge : arghorizon n / 2 ≤ (floorBlockLength arghorizon n : ℝ) := by
    have h := (le_div_iff₀ hargpos).1 hfloor
    nlinarith
  have hfinal : (floorBlockLength (fun n => width n ^ p) n : ℝ) +
      2 * (floorBlockLength (fun n => width n ^ q) n : ℝ) ≤
      (floorBlockLength arghorizon n : ℝ) := by
    nlinarith
  exact_mod_cast hfinal

end Asymptotics

end
