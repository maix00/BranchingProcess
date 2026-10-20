/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Rate.LogScales
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# First-stage cutoff for the positive-parameter right-tail estimate

Write `L_N(n) = log (N n)` and
`ell_N(n) = floor (L_N(n)^(5/2))`. The public declarations are:

- `rightTailPositiveAFirstCutoff`: the first-stage horizon `ell_N`.
- `tendsto_rightTailPositiveAFirstCutoff_div_logCube`:
  `ell_N(n) / L_N(n)^3 → 0` when `N n → ∞`.
- `tendsto_rightTailPositiveAFirstCutoff_atTop`:
  `ell_N(n) → ∞` when `N n → ∞`.
- `tendsto_rightTailPositiveAFirstCutoff_smallDeviationScale_div_log`:
  `(ell_N(n))^(2/5) / L_N(n) → 1`.
- `eventually_rightTailPositiveAFirstStageAHScale`: if `b > 0` and `p < 1/2`,
  eventually `delta0 ≤ b L_N(n)` and `(b L_N(n))^(2+p) ≤ ell_N(n)`.
- `eventually_rightTailPositiveAFirstCutoff_lt_horizon`:
  `ell_N(n) < floor (t L_N(n)^3) + 1` eventually for `t > 0`.

This deterministic schedule is used in the proof of Proposition 3.1,
equation (4.15), of Elie Aïdékon and Yueyun Hu, *Average-weight percolation
on the complete graph*, arXiv:2512.23266 (2025). The exponent condition
`p < 1/2` is the scale margin used in their Lemma 4.1.
-/

open Filter
open scoped Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

/-- The first-stage cutoff `floor((log N)^(5/2))` used in the positive-`a`
right-tail proof. -/
noncomputable def rightTailPositiveAFirstCutoff
    (N : ℕ → ℕ) (n : ℕ) : ℕ :=
  ⌊logarithmOfSampleSize N n ^ ((5 : ℝ) / 2)⌋₊

/-- The `log^(5/2) N` first-stage cutoff is negligible on the `log^3 N`
scale. -/
theorem tendsto_rightTailPositiveAFirstCutoff_div_logCube
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => (rightTailPositiveAFirstCutoff N n : ℝ) /
      logarithmOfSampleSize N n ^ 3) atTop (𝓝 0) := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let arg : ℕ → ℝ := fun n => L n ^ ((5 : ℝ) / 2)
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have harg : Tendsto arg atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (5 : ℝ) / 2)).comp hL
  have hfloor : Tendsto (fun n => (Nat.floor (arg n) : ℝ) / arg n)
      atTop (𝓝 1) := tendsto_nat_floor_div_atTop.comp harg
  have hhalf : Tendsto (fun n => L n ^ ((1 : ℝ) / 2)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 2)).comp hL
  have hinv : Tendsto (fun n => (L n ^ ((1 : ℝ) / 2))⁻¹)
      atTop (𝓝 0) := hhalf.inv_tendsto_atTop
  have hratio : Tendsto (fun n => arg n / L n ^ 3) atTop (𝓝 0) := by
    have heq : (fun n => arg n / L n ^ 3) =ᶠ[atTop]
        fun n => (L n ^ ((1 : ℝ) / 2))⁻¹ := by
      filter_upwards [hL.eventually_gt_atTop 0] with n hn
      have hpow : L n ^ ((5 : ℝ) / 2) / L n ^ 3 =
          (L n ^ ((1 : ℝ) / 2))⁻¹ := by
        calc
          L n ^ ((5 : ℝ) / 2) / L n ^ 3 =
              L n ^ ((5 : ℝ) / 2) / L n ^ (3 : ℝ) := by
                have hcast : L n ^ (3 : ℝ) = L n ^ (3 : ℕ) :=
                  Real.rpow_natCast (L n) 3
                rw [← hcast]
          _ = L n ^ (((5 : ℝ) / 2) - 3) :=
            (Real.rpow_sub hn ((5 : ℝ) / 2) (3 : ℝ)).symm
          _ = L n ^ (-((1 : ℝ) / 2)) := by
            congr 1
            norm_num
          _ = (L n ^ ((1 : ℝ) / 2))⁻¹ := Real.rpow_neg hn.le _
      simpa [arg, L] using hpow
    exact hinv.congr' heq.symm
  have hbase := hfloor.mul hratio
  have heq :
      (fun n => (rightTailPositiveAFirstCutoff N n : ℝ) / L n ^ 3) =ᶠ[atTop]
        fun n => (Nat.floor (arg n) : ℝ) / arg n * (arg n / L n ^ 3) := by
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    have hargPos : 0 < arg n := Real.rpow_pos_of_pos hn _
    have hfloorVal : (rightTailPositiveAFirstCutoff N n : ℝ) =
        (Nat.floor (arg n) : ℝ) := by
      simp [rightTailPositiveAFirstCutoff, arg, L, logarithmOfSampleSize]
    rw [hfloorVal]
    field_simp [ne_of_gt hargPos, ne_of_gt hn]
  simpa [L] using hbase.congr' heq.symm

/-- The first-stage cutoff tends to infinity with the sample size. -/
theorem tendsto_rightTailPositiveAFirstCutoff_atTop
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (rightTailPositiveAFirstCutoff N) atTop atTop := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have harg : Tendsto (fun n => L n ^ ((5 : ℝ) / 2)) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (5 : ℝ) / 2)).comp hL
  convert tendsto_nat_floor_atTop.comp harg using 1 <;>
    ext n <;> simp [rightTailPositiveAFirstCutoff, L, logarithmOfSampleSize]

/-- The first-stage cutoff dominates the superdiffusive Aïdékon--Hu power of
the corridor width when `p < 1/2`, as required by the
`floor((log N)^(5/2))` choice. -/
theorem eventually_rightTailPositiveAFirstStageAHScale
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {b p delta0 : ℝ}
    (hb : 0 < b) (hpHalf : p < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      delta0 ≤ b * logarithmOfSampleSize N n ∧
        (b * logarithmOfSampleSize N n) ^ (2 + p) ≤
          (rightTailPositiveAFirstCutoff N n : ℝ) := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let arg : ℕ → ℝ := fun n => L n ^ ((5 : ℝ) / 2)
  let q : ℝ := (1 : ℝ) / 2 - p
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have harg : Tendsto arg atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (5 : ℝ) / 2)).comp hL
  have hfloor : Tendsto (fun n => (Nat.floor (arg n) : ℝ) / arg n)
      atTop (𝓝 1) := tendsto_nat_floor_div_atTop.comp harg
  have hq : 0 < q := by dsimp [q]; linarith
  have hpower : Tendsto (fun n => L n ^ q) atTop atTop :=
    (_root_.tendsto_rpow_atTop hq).comp hL
  have hbpow : 0 < b ^ (2 + p) := Real.rpow_pos_of_pos hb _
  have hratio : Tendsto
      (fun n => arg n / (b * L n) ^ (2 + p)) atTop atTop := by
    have hscaled : Tendsto (fun n => (b ^ (2 + p))⁻¹ * L n ^ q)
        atTop atTop := hpower.const_mul_atTop (inv_pos.mpr hbpow)
    have heq : (fun n => (b ^ (2 + p))⁻¹ * L n ^ q) =ᶠ[atTop]
        fun n => arg n / (b * L n) ^ (2 + p) := by
      filter_upwards [hL.eventually_gt_atTop 0] with n hn
      have hwidth : (b * L n) ^ (2 + p) =
          b ^ (2 + p) * L n ^ (2 + p) :=
        Real.mul_rpow hb.le hn.le
      have hpowerEq : L n ^ ((5 : ℝ) / 2) =
          L n ^ q * L n ^ (2 + p) := by
        rw [← Real.rpow_add hn]
        congr 1
        dsimp [q]
        ring
      dsimp [arg]
      rw [hwidth, hpowerEq]
      field_simp [ne_of_gt hbpow,
        ne_of_gt (Real.rpow_pos_of_pos hn (2 + p))]
    exact hscaled.congr' heq
  filter_upwards [hL.eventually_gt_atTop 0,
    hL.const_mul_atTop hb |>.eventually_ge_atTop delta0,
    Filter.Tendsto.eventually hfloor (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hratio.eventually_gt_atTop 2] with n hLn hwidthLarge hfloorLarge hratioLarge
  refine ⟨hwidthLarge, ?_⟩
  have hargPos : 0 < arg n := Real.rpow_pos_of_pos hLn _
  have hwidthPos : 0 < (b * L n) ^ (2 + p) :=
    Real.rpow_pos_of_pos (mul_pos hb hLn) _
  have hfloorVal : (rightTailPositiveAFirstCutoff N n : ℝ) =
      (Nat.floor (arg n) : ℝ) := by
    simp [rightTailPositiveAFirstCutoff, arg, L, logarithmOfSampleSize]
  have hfloorLower : arg n / 2 < (rightTailPositiveAFirstCutoff N n : ℝ) := by
    rw [hfloorVal]
    have hmul := (lt_div_iff₀ hargPos).mp hfloorLarge
    nlinarith
  have hratioLower : 2 * (b * L n) ^ (2 + p) < arg n :=
    (lt_div_iff₀ hwidthPos).mp hratioLarge
  have hwidthLower : (b * L n) ^ (2 + p) < arg n / 2 := by
    linarith
  exact_mod_cast (lt_trans hwidthLower hfloorLower).le

/-- The first cutoff lies strictly before the `floor(t log^3 N)+1` terminal
horizon for all sufficiently large sample sizes. -/
theorem eventually_rightTailPositiveAFirstCutoff_lt_horizon
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop,
      rightTailPositiveAFirstCutoff N n < logarithmicHorizon N t n := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  have hcut := tendsto_rightTailPositiveAFirstCutoff_div_logCube hN
  have hterminal := logarithmicHorizon_div_logCube_tendsto hN ht
  have hgap : Tendsto
      (fun n => (logarithmicHorizon N t n : ℝ) / L n ^ 3 -
        (rightTailPositiveAFirstCutoff N n : ℝ) / L n ^ 3)
      atTop (𝓝 t) := by
    simpa [L] using hterminal.sub hcut
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have hgapPos : ∀ᶠ n : ℕ in atTop,
      0 < (logarithmicHorizon N t n : ℝ) / L n ^ 3 -
        (rightTailPositiveAFirstCutoff N n : ℝ) / L n ^ 3 :=
    Filter.Tendsto.eventually hgap (Ioi_mem_nhds ht)
  filter_upwards [hgapPos, hL.eventually_gt_atTop 0]
    with n hgap hLn
  have hratio :
      (rightTailPositiveAFirstCutoff N n : ℝ) / L n ^ 3 <
        (logarithmicHorizon N t n : ℝ) / L n ^ 3 := by
    linarith
  have hreal : (rightTailPositiveAFirstCutoff N n : ℝ) <
      (logarithmicHorizon N t n : ℝ) := by
    exact (div_lt_div_iff_of_pos_right (pow_pos hLn 3)).mp hratio
  exact_mod_cast hreal
/-- The `2/5` small-deviation scale of the first-stage cutoff is asymptotic
 to the logarithmic sample-size scale:
`logarithmicSmallDeviationScale (rightTailPositiveAFirstCutoff N n) /
 logarithmOfSampleSize N n → 1`. -/
lemma tendsto_rightTailPositiveAFirstCutoff_smallDeviationScale_div_log
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => logarithmicSmallDeviationScale
      (rightTailPositiveAFirstCutoff N n) /
        logarithmOfSampleSize N n) atTop (𝓝 1) := by
  let L : ℕ → ℝ := logarithmOfSampleSize N
  let arg : ℕ → ℝ := fun n => L n ^ ((5 : ℝ) / 2)
  let cutoff : ℕ → ℝ := fun n => (rightTailPositiveAFirstCutoff N n : ℝ)
  have hL : Tendsto L atTop atTop := by
    exact Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hN)
  have harg : Tendsto arg atTop atTop :=
    (_root_.tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 2)).comp hL
  have hfloor : Tendsto (fun n => cutoff n / arg n) atTop (𝓝 1) := by
    have h := (tendsto_nat_floor_div_atTop.comp harg)
    have heq : (fun n => cutoff n / arg n) =ᶠ[atTop]
        fun n => (Nat.floor (arg n) : ℝ) / arg n := by
      filter_upwards [] with n
      simp [cutoff, arg, L, rightTailPositiveAFirstCutoff,
        logarithmOfSampleSize]
    exact h.congr' heq.symm
  have hpower : Tendsto (fun n => (cutoff n / arg n) ^ ((2 : ℝ) / 5))
      atTop (𝓝 1) := by
    simpa using hfloor.rpow_const
      (x := (1 : ℝ)) (p := (2 : ℝ) / 5) (Or.inl (by norm_num))
  have hratio : Tendsto (fun n => cutoff n ^ ((2 : ℝ) / 5) / L n)
      atTop (𝓝 1) := by
    have heq : (fun n => cutoff n ^ ((2 : ℝ) / 5) / L n) =ᶠ[atTop]
        fun n => (cutoff n / arg n) ^ ((2 : ℝ) / 5) := by
      filter_upwards [hL.eventually_gt_atTop 0] with n hn
      have hargPos : 0 < arg n := Real.rpow_pos_of_pos hn _
      have hargPow : arg n ^ ((2 : ℝ) / 5) = L n := by
        dsimp [arg]
        rw [← Real.rpow_mul hn.le]
        norm_num [Real.rpow_one]
      rw [Real.div_rpow (by positivity) hargPos.le, hargPow]
    exact hpower.congr' heq.symm
  simpa [cutoff, logarithmicSmallDeviationScale] using hratio

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
