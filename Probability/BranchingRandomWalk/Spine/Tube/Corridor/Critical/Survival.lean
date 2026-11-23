/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
public import Probability.Process.RandomWalk.Path.Corridor.Affine
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.Distributions.Moments.Real
import all Probability.BranchingRandomWalk.Spine.Tube.Corridor.Critical.Lemmas.Scale
import all Probability.BranchingRandomWalk.Spine.Tube.Corridor.Critical.Lemmas.Survival

/-!
# Logarithmic survival rate in a critical affine corridor

## Public declarations

* `eventually_survival_ge_exp_mul_cubeRoot`: in the same critical corridor,
  $p_N\ge e^{aN^{1/3}}$ eventually for each $a<0$.

* `ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor.tendsto_log_survival_div_cubeRoot`:
  for a boundary-normalized branching random walk with finite cross-child
  weight and centered spine of variance $\sigma^2>0$, put
  $\Delta=cN^{1/3}$ and $r_j=(\pi^2\sigma^2/2)j/\Delta^2$.
  For every $c,v>0$, the probability $p_N$ of a generation-$N$ path in
  $[r_j,r_j+\Delta]$ with terminal position at most $r_N+vN^{1/3}$ satisfies
  $\log(p_N)/N^{1/3}\to0$.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor

open Combinatorics.Branching
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk

/-- The lower bound in the proof of Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 3, Lemma 3.7, equation (3.8), in probability form. -/
theorem eventually_survival_ge_exp_mul_cubeRoot
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) (hcross : HasFiniteCrossWeight φ μ)
    {sigma c v : ℝ}
    (hcentered : ProbabilityTheory.IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ)
      (sigma ^ 2)) (hsigma : 0 < sigma) (hc : 0 < c) (hv : 0 < v)
    {a : ℝ} (ha : a < 0) :
    let K := (Real.pi ^ 2 / 2) * sigma ^ 2
    ∀ᶠ N : ℕ in atTop,
      let t := (N : ℝ) ^ (1 / 3 : ℝ)
      let width := c * t
      Real.exp (a * t) ≤ (offspringFieldLaw μ).real (hasPathHistoryIn φ N 0
        (affineCorridorThrough N 0 (K / width ^ 2) width
          (K * (N : ℝ) / width ^ 2 + v * t))) := by
  intro K
  let t (N : ℕ) := (N : ℝ) ^ (1 / 3 : ℝ)
  let width (N : ℕ) := c * t N
  obtain ⟨ht, hw, htpos, hratio, hscale, hsqrt, hcount⟩ := cubeRootWidthFacts hc
  have hK : 0 < K := by dsimp [K]; positivity
  have haNeg : 0 < -a := neg_pos.mpr ha
  let δ := min (K / 2) ((-a) * c ^ 2 / 16)
  let u := min (v / c) ((-a) / (8 * c))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδK : δ < K := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hu : 0 < u := lt_min (by positivity) (by positivity)
  have huv : u * c ≤ v := (le_div_iff₀ hc).mp (min_le_left _ _)
  have huBudget : u * c ≤ -a / 8 := by
    have h := (le_div_iff₀ (show 0 < 8 * c by positivity)).mp (min_le_right
      (v / c) ((-a) / (8 * c)))
    linarith
  have hδBudget : δ / c ^ 2 ≤ -a / 16 := by
    apply (div_le_iff₀ (pow_pos hc 2)).2
    convert (min_le_right (K / 2) ((-a) * c ^ 2 / 16)) using 1; ring
  obtain ⟨width₀, hone, hsurvive⟩ := exists_criticalCorridor_survival_ge φ μ
    hboundary hcross hcentered hsigma hu (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (show 0 < K - δ by linarith)
    (show K - δ < K by linarith) (show K < K + δ by linarith)
  have hconstant : Tendsto (fun N => 2 * (K - δ) / t N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ht
  have herrors := ((hsqrt.const_mul (4 : ℝ)).add hconstant).add hcount
  simp only [mul_zero, add_zero] at herrors
  filter_upwards [hw.eventually_ge_atTop width₀, hscale, eventually_ge_atTop (1 : ℕ),
    herrors.eventually (Iio_mem_nhds (by linarith : 0 < -a / 4))] with N hwN hfloor hN herror
  have htN : 0 < t N := htpos N hN
  have hwOne : 1 ≤ width N := hone.trans hwN
  have hNT : (N : ℝ) / width N ^ 2 = t N / c ^ 2 := hratio N hN
  let E := 2 * (K - (K + δ)) * (N : ℝ) / width N ^ 2
  let B := 4 * width N ^ (1 / 2 : ℝ) + 2 * u * width N +
    2 * (K - (K - δ)) * (N : ℝ) / width N ^ 2 + 2 * (K - δ) / width N ^ 2
  let p := (offspringFieldLaw μ).real (hasPathHistoryIn φ N 0
    (affineCorridorThrough N 0 (K / width N ^ 2) (width N)
      (K * (N : ℝ) / width N ^ 2 + v * t N)))
  have hp : Real.exp E / (((N : ℝ) + 1) * Real.exp B) ≤ p := by
    have hmono : hasPathHistoryIn (ι := ℕ) φ N 0
        (affineCorridorThrough N 0 (K / width N ^ 2) (width N)
          (K * (N : ℝ) / width N ^ 2 + u * width N)) ⊆
        hasPathHistoryIn φ N 0
        (affineCorridorThrough N 0 (K / width N ^ 2) (width N)
          (K * (N : ℝ) / width N ^ 2 + v * t N)) := by
      intro ω hω
      rcases hω with ⟨address, haddress, hpath, hkeep⟩
      refine ⟨address, haddress, hpath, hkeep.1, hkeep.2.trans ?_⟩
      exact add_le_add_right (by
        change u * (c * t N) ≤ v * t N
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right huv htN.le) _
    have hh := (hsurvive (width N) hwN N hN hfloor).trans (measure_mono hmono)
    change ENNReal.ofReal (Real.exp E) /
        ((N + 1 : ℝ≥0∞) * ENNReal.ofReal (Real.exp B)) ≤ _ at hh
    have hpReal := ENNReal.toReal_mono (measure_ne_top (offspringFieldLaw μ) _) hh
    simpa only [p, Measure.real, ENNReal.toReal_div, ENNReal.toReal_mul,
      ENNReal.toReal_add (ENNReal.natCast_ne_top _) ENNReal.one_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_one,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hpReal
  have hratioPos : 0 < Real.exp E / (((N : ℝ) + 1) * Real.exp B) :=
    div_pos (Real.exp_pos _) (by positivity)
  have hlogRatio := Real.log_div (Real.exp_ne_zero E)
    (by positivity : ((N : ℝ) + 1) * Real.exp B ≠ 0)
  rw [Real.log_exp, Real.log_mul (by positivity : (N : ℝ) + 1 ≠ 0) (Real.exp_ne_zero B),
    Real.log_exp] at hlogRatio
  have hBudget : a < (E - (Real.log ((N : ℝ) + 1) + B)) / t N := by
    have hlast : (2 * (K - δ) / width N ^ 2) / t N ≤ 2 * (K - δ) / t N :=
      div_le_div_of_nonneg_right
        (div_le_self (by linarith) (one_le_pow₀ hwOne)) htN.le
    have h1 : (E - (Real.log ((N : ℝ) + 1) + B)) / t N =
        -(4 * (δ / c ^ 2)) - 2 * (u * c) -
          (4 * (width N ^ (1 / 2 : ℝ) / t N) +
            (2 * (K - δ) / width N ^ 2) / t N + Real.log ((N : ℝ) + 1) / t N) := by
      dsimp [E, B]
      simp only [mul_div_assoc, hNT]
      rw [show 2 * u * width N = 2 * u * (c * t N) from rfl]
      field_simp
      ring
    have herror' : 4 * (width N ^ (1 / 2 : ℝ) / t N) +
        2 * (K - δ) / t N + Real.log ((N : ℝ) + 1) / t N < -a / 4 := herror
    linarith
  apply le_trans _ hp
  rw [← Real.exp_log hratioPos]
  exact Real.exp_le_exp.mpr (hlogRatio.symm ▸ ((lt_div_iff₀ htN).mp hBudget).le)

/-- Equation (3.8) of Wang Yiyang, *Asymptotic Speed of the N-Branching Random
Walk with Infinite Offspring* (master's thesis, Fudan University, 2026),
Chapter 3, Lemma 3.7. The lower bound uses a narrower terminal window and
the Paley--Zygmund estimates from Lemmas 3.4--3.6. -/
theorem tendsto_log_survival_div_cubeRoot
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ) (hcross : HasFiniteCrossWeight φ μ)
    {sigma c v : ℝ}
    (hcentered : ProbabilityTheory.IsCenteredSecondMoment (tiltedPotentialLaw φ (-1) μ)
      (sigma ^ 2)) (hsigma : 0 < sigma) (hc : 0 < c) (hv : 0 < v) :
    let K := (Real.pi ^ 2 / 2) * sigma ^ 2
    Tendsto (fun N : ℕ =>
      let t := (N : ℝ) ^ (1 / 3 : ℝ)
      let width := c * t
      Real.log ((offspringFieldLaw μ).real (hasPathHistoryIn φ N 0
        (affineCorridorThrough N 0 (K / width ^ 2) width
          (K * (N : ℝ) / width ^ 2 + v * t)))) / t) atTop (𝓝 0) := by
  intro K
  let t (N : ℕ) := (N : ℝ) ^ (1 / 3 : ℝ)
  let width (N : ℕ) := c * t N
  obtain ⟨_, _, htpos, _, _, _, _⟩ := cubeRootWidthFacts hc
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨b, hab, hb⟩ := exists_between ha
    have hsurvive := eventually_survival_ge_exp_mul_cubeRoot φ μ hboundary hcross
      hcentered hsigma hc hv hb
    filter_upwards [hsurvive, eventually_ge_atTop (1 : ℕ)] with N hN hpos
    have hlog := Real.log_le_log (Real.exp_pos _) hN
    rw [Real.log_exp] at hlog
    exact hab.trans_le ((le_div_iff₀ (htpos N hpos)).mpr hlog)
  · intro a ha
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    apply lt_of_le_of_lt _ ha
    exact div_nonpos_of_nonpos_of_nonneg
      (Real.log_nonpos ENNReal.toReal_nonneg (measureReal_le_one)) (htpos N hN).le

end ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor

end
