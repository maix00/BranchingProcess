/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Probability.BrownianMotion.Basic
import Probability.Distributions.Moments.Real
import Probability.Process.Path.Scaling.UnitInterval
import Topology.ContinuousMap.Oscillation
import Analysis.SpecialFunctions.Trigonometric.LogAsymptotics
import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Path.Continuous
import Probability.Process.RandomWalk.Rademacher.Basic
import MeasureTheory.Measure.ContinuousMap.RangeOscillation
import MeasureTheory.MeasurableSpace.ContinuousMap.Oscillation
import Probability.ConvergenceInDistribution.ContinuousMap.Oscillation
import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Range.Corridor.Survival
import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral.Survival.Bounds

/-!
# Proof lemmas for the Brownian finite-corridor estimate

These declarations implement the finite-cover Donsker transfer and the
Rademacher spectral limit used by `Range/FiniteCover.lean`. The corridor
cover, diffusive eigenvalue, and geometric correction are proof-stage objects
for that estimate; the module keeps them out of the subject-level interface.

## Internal proof declarations

- `brownianRangeOscillation_le_sum_liminf_fixedCorridors` transfers the
  Brownian range event to a finite sum of normalized Rademacher corridor
  `liminf` probabilities.
- `corridorDiffusiveWidth`, `corridorEigenvalue`, and
  `corridorGeometricFactor` encode the rounded lattice width, its leading
  eigenvalue, and the complete-spectrum correction.
- `tendsto_corridorEigenvalue_pow` and
  `tendsto_corridorGeometricFactor` prove their diffusive limits.
- `liminf_normalizedRademacherPath_openCorridor_le` bounds a fixed open
  corridor probability by its limiting Brownian spectral correction.

For a finite open-corridor cover $(U_j)_{j<m}$ of the Brownian range event
$A_w$, the transfer and spectral limits are
\[
  \mathbb P(B\in A_w)\le\sum_{j<m}\liminf_{n\to\infty}
       \mathbb P(S^{(n)}\in U_j),
  \qquad
  \cos(\pi/L_n)^n\longrightarrow \exp\!\left(-\frac{\pi^2}{2w^2}\right),
\]
where $L_n$ is the rounded lattice width associated with $w$.

-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ProbabilityTheory.Process.Brownian.SmallDeviation.Range

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

private lemma ae_continuousunitIntervalPath_startsAtZero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t)) :
    ∀ᵐ path ∂P.map (ProbabilityTheory.continuousunitIntervalPath B hcontinuous),
      path (0 : unitInterval) = 0 := by
  rw [ae_map_iff
    (ProbabilityTheory.measurable_continuousunitIntervalPath B hcontinuous
      hmeasurable).aemeasurable
    ContinuousMap.measurableSet_startsAtZeroSet]
  filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
  rw [ProbabilityTheory.continuousunitIntervalPath_apply]
  have htime : unitInterval.toNNReal (0 : unitInterval) = 0 := by
    apply Subtype.ext
    rfl
  rw [htime]
  exact hω

/-- Under the Rademacher Donsker limit, the Brownian range-oscillation mass
is bounded by the sum of the `liminf` masses of the fixed finite open
corridors in the minimum-location cover. -/
lemma brownianRangeOscillation_le_sum_liminf_fixedCorridors
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {width : ℝ} {count : ℕ} (hwidth : 0 < width) (hcount : 0 < count) :
    P.map (ProbabilityTheory.continuousunitIntervalPath B hcontinuous)
        (ContinuousMap.rangeOscillationSet width) ≤
      ∑ j : Fin count, atTop.liminf (fun n =>
        normalizedLinearPathLaw rademacherMeasure (fun n => Real.sqrt n) n
          (ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j))) := by
  have hrademacher : IsCenteredUnitSecondMoment rademacherMeasure := by
    constructor <;> rw [integral_rademacherMeasure] <;> norm_num
  have hlimit :=
    tendstoInDistribution_normalizedLinearContinuousPath_brownian
      rademacherMeasure hrademacher.1 hrademacher.2 hB
      hcontinuous hmeasurable
  have hstart :=
    ae_continuousunitIntervalPath_startsAtZero hB hcontinuous hmeasurable
  simpa only [normalizedLinearPathLaw] using
    ProbabilityTheory.ContinuousMap.TendstoInDistribution.measure_rangeOscillationSet_le_sum_liminf_finiteCorridorCover
      hlimit hwidth hcount hstart


noncomputable def corridorDiffusiveWidth (width : ℝ) (n : ℕ) : ℝ :=
  width * Real.sqrt n + 3

noncomputable def corridorEigenvalue (width : ℝ) (n : ℕ) : ℝ :=
  Real.cos (Real.pi / corridorDiffusiveWidth width n)

noncomputable def corridorGeometricFactor (width : ℝ) (n : ℕ) : ℝ :=
  4 * (corridorEigenvalue width n ^ n /
    (1 - corridorEigenvalue width n ^ n))

/-- The fixed-width principal eigenvalue power converges to the Brownian
Dirichlet exponential. -/
lemma tendsto_corridorEigenvalue_pow
    {width : ℝ} (hwidth : 0 < width) :
    Tendsto (fun n : ℕ => corridorEigenvalue width n ^ n) atTop
      (nhds (Real.exp (-(Real.pi ^ 2) / (2 * width ^ 2)))) := by
  let L : ℕ → ℝ := corridorDiffusiveWidth width
  let main : ℕ → ℝ := fun n => L n ^ 2 * Real.log (Real.cos (Real.pi / L n))
  let ratio : ℕ → ℝ := fun n => L n ^ 2 / (n : ℝ)
  have hsqrtTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hLtop : Tendsto L atTop atTop := by
    have hmul := hsqrtTop.const_mul_atTop hwidth
    have hadd := tendsto_atTop_add_const_right atTop 3 hmul
    change Tendsto (fun n : ℕ => width * Real.sqrt n + 3) atTop atTop
    exact hadd
  have hinvSqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hsqrtTop
  have hLdivSqrt : Tendsto (fun n : ℕ => L n / Real.sqrt n) atTop
      (nhds width) := by
    have haux : Tendsto (fun n : ℕ => width + 3 * (Real.sqrt n)⁻¹)
        atTop (nhds width) := by
      simpa using tendsto_const_nhds.add
        (tendsto_const_nhds.mul hinvSqrt)
    apply haux.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hsqrtNe : Real.sqrt (n : ℝ) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (Nat.cast_pos.mpr (show 0 < n by omega)))
    dsimp [L, corridorDiffusiveWidth]
    field_simp [hsqrtNe]
  have hratio : Tendsto ratio atTop (nhds (width ^ 2)) := by
    have hsquare := hLdivSqrt.pow 2
    apply hsquare.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hsqrtSq : Real.sqrt (n : ℝ) ^ 2 = n :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    dsimp [ratio, L]
    rw [div_pow, hsqrtSq]
  have hmain : Tendsto main atTop (nhds (-(Real.pi ^ 2) / 2)) := by
    convert (Real.tendsto_sq_mul_log_cos_pi_div.comp hLtop) using 1
    rfl
  have hinvRatio : Tendsto (fun n => (ratio n)⁻¹) atTop
      (nhds ((width ^ 2)⁻¹)) :=
    hratio.inv₀ (pow_ne_zero 2 hwidth.ne')
  have hproduct : Tendsto (fun n => main n * (ratio n)⁻¹) atTop
      (nhds ((-(Real.pi ^ 2) / 2) * (width ^ 2)⁻¹)) :=
    hmain.mul hinvRatio
  have hlog : Tendsto (fun n : ℕ => (n : ℝ) *
      Real.log (corridorEigenvalue width n)) atTop
      (nhds (-(Real.pi ^ 2) / (2 * width ^ 2))) := by
    have hlog' : Tendsto (fun n : ℕ => (n : ℝ) *
        Real.log (corridorEigenvalue width n)) atTop
        (nhds ((-(Real.pi ^ 2) / 2) * (width ^ 2)⁻¹)) := by
      apply hproduct.congr'
      filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      have hLn : L n ≠ 0 := by
        dsimp [L, corridorDiffusiveWidth]
        positivity
      have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      dsimp [main, ratio, corridorEigenvalue, L, corridorDiffusiveWidth]
      rw [inv_div]
      field_simp [hLn, hnNe]
    convert hlog' using 1
    · congr 1
      field_simp [hwidth.ne']
  have hrealExp : Tendsto (fun n : ℕ =>
      Real.exp ((n : ℝ) * Real.log (corridorEigenvalue width n))) atTop
      (nhds (Real.exp (-(Real.pi ^ 2) / (2 * width ^ 2)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hqPos : ∀ n, 0 < corridorEigenvalue width n := by
    intro n
    have hLtwo : 2 < corridorDiffusiveWidth width n := by
      dsimp [corridorDiffusiveWidth]
      have hsqrtNonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
      nlinarith
    have hanglePos : 0 < Real.pi / corridorDiffusiveWidth width n :=
      div_pos Real.pi_pos (by linarith)
    have hangleLt : Real.pi / corridorDiffusiveWidth width n < Real.pi / 2 := by
      rw [div_lt_div_iff₀ (by linarith : 0 < corridorDiffusiveWidth width n)
        (by norm_num : (0 : ℝ) < 2)]
      nlinarith [Real.pi_pos, hLtwo]
    dsimp [corridorEigenvalue]
    exact Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hanglePos, Real.pi_pos], hangleLt⟩
  have hpowExp (n : ℕ) : corridorEigenvalue width n ^ n =
      Real.exp ((n : ℝ) * Real.log (corridorEigenvalue width n)) := by
    calc
      corridorEigenvalue width n ^ n =
          Real.exp (Real.log (corridorEigenvalue width n ^ n)) :=
        (Real.exp_log (pow_pos (hqPos n) n)).symm
      _ = Real.exp ((n : ℝ) * Real.log (corridorEigenvalue width n)) := by
        rw [Real.log_pow]
  have hpowEq : (fun n : ℕ =>
      Real.exp ((n : ℝ) * Real.log (corridorEigenvalue width n))) =ᶠ[atTop]
      (fun n : ℕ => corridorEigenvalue width n ^ n) :=
    Filter.Eventually.of_forall fun n => (hpowExp n).symm
  exact hrealExp.congr' hpowEq

/-- The width-uniform complete-spectrum correction converges to the
geometric correction of the Brownian corridor probability. -/
lemma tendsto_corridorGeometricFactor
    {width : ℝ} (hwidth : 0 < width) :
    Tendsto (fun n : ℕ => corridorGeometricFactor width n) atTop
      (nhds (4 *
        (Real.exp (-(Real.pi ^ 2) / (2 * width ^ 2)) /
          (1 - Real.exp (-(Real.pi ^ 2) / (2 * width ^ 2)))))) := by
  let r := Real.exp (-(Real.pi ^ 2) / (2 * width ^ 2))
  have hrpos : 0 < r := by positivity
  have hrlt : r < 1 := by
    dsimp [r]
    rw [← Real.exp_zero]
    apply Real.exp_strictMono
    have hden : 0 < 2 * width ^ 2 := by positivity
    have hnum : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden
  have hpow := tendsto_corridorEigenvalue_pow hwidth
  have hden : Tendsto (fun n : ℕ => 1 - corridorEigenvalue width n ^ n)
      atTop (nhds (1 - r)) := by
    simpa [r] using tendsto_const_nhds.sub hpow
  have hquot : Tendsto (fun n : ℕ => corridorEigenvalue width n ^ n /
      (1 - corridorEigenvalue width n ^ n)) atTop (nhds (r / (1 - r))) := by
    convert hpow.div hden (ne_of_gt (sub_pos.mpr hrlt)) using 1
  have hscaled : Tendsto (fun n : ℕ => 4 *
      (corridorEigenvalue width n ^ n /
        (1 - corridorEigenvalue width n ^ n))) atTop
      (nhds (4 * (r / (1 - r)))) :=
    tendsto_const_nhds.mul hquot
  simpa [corridorGeometricFactor] using hscaled

/-- A fixed open corridor's `liminf` probability is bounded by the limiting
Brownian spectral correction at its width. -/
lemma liminf_normalizedRademacherPath_openCorridor_le
    {lower upper : ℝ} (hlower : lower < 0) (hupper : 0 < upper) :
    atTop.liminf (fun n => normalizedLinearPathLaw rademacherMeasure
      (fun n => Real.sqrt n) n
      (ContinuousMap.rangeInOpenInterval lower upper)) ≤
      ENNReal.ofReal (4 *
        (Real.exp (-(Real.pi ^ 2) / (2 * (upper - lower) ^ 2)) /
          (1 - Real.exp (-(Real.pi ^ 2) / (2 * (upper - lower) ^ 2))))) := by
  let width := upper - lower
  let target := 4 *
    (Real.exp (-(Real.pi ^ 2) / (2 * width ^ 2)) /
      (1 - Real.exp (-(Real.pi ^ 2) / (2 * width ^ 2))))
  have hwidth : 0 < width := by dsimp [width]; linarith
  let p : ℕ → ENNReal := fun n => normalizedLinearPathLaw rademacherMeasure
    (fun n => Real.sqrt n) n (ContinuousMap.rangeInOpenInterval lower upper)
  have hle : ∀ᶠ n in atTop, p n ≤ ENNReal.ofReal (corridorGeometricFactor width n) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    have hnpos : 0 < n := by omega
    exact normalizedRademacherPath_openCorridor_probability_le_widthGeometric
      hlower hupper hnpos
  have hfactor := tendsto_corridorGeometricFactor hwidth
  have hfactorENN : Tendsto (fun n => ENNReal.ofReal
      (corridorGeometricFactor width n)) atTop (nhds (ENNReal.ofReal target)) := by
    simpa [target] using
      ENNReal.tendsto_ofReal hfactor
  have hlim : atTop.liminf p ≤ ENNReal.ofReal target := calc
    atTop.liminf p ≤ atTop.liminf
        (fun n => ENNReal.ofReal (corridorGeometricFactor width n)) :=
      Filter.liminf_le_liminf hle
    _ = ENNReal.ofReal target := by
      rw [hfactorENN.liminf_eq]
  simpa [p, width, target] using hlim


end ProbabilityTheory.Process.Brownian.SmallDeviation.Range
