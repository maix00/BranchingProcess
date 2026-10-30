/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
import Mathlib.Topology.UnitInterval
import Mathlib.Probability.BrownianMotion.Basic
import Probability.Process.Path.Scaling.UnitInterval
import Probability.Process.Path.Representation.Skorokhod
import Probability.Process.Brownian.Construction.PreBrownianModification
import Topology.Cadlag.Skorokhod.Corridor.Basic
import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Corridor.Brownian.Endpoint
import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Corridor.Brownian.Basic
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral.Survival.Lower
import Analysis.Asymptotics.Scale.CenteredInterval

/-!
# Proof lemmas for Brownian corridor lower bounds

## Internal proof declarations

- `closedUnitCorridorLowerBoundOfRhoCore`: transfers the finite-interval
  principal-mode estimate to the closed unit corridor with exponent
  $-\pi^2/(2\rho^2)$.
- `closedCorridorLowerBoundOfRhoWidthCore`: rescales that estimate to a
  closed corridor of arbitrary positive width.
- `closedUnitCorridorLowerBoundCore`: chooses the asymptotically optimal
  corridor fraction and obtains exponent $-\pi^2/2$.
- `openCorridorLowerBoundCore` and `closedUnitCorridorNeZeroCore`: derive
  the wider-open-corridor bound and positive mass from the closed estimate.

This private proof chain transfers finite-interval Rademacher spectral bounds
through the closed-event Donsker estimate. It proves the quantitative bound
for a corridor occupying a fraction `rho` of the target width, scales the
estimate to arbitrary positive width, optimizes `rho` to obtain the principal
exponent, then compares the closed unit corridor with a wider open corridor
and derives positivity of the closed-corridor probability. These steps support
the public Brownian corridor estimates in
`Probability.Process.Brownian.SmallDeviation.Corridor.Bounds`.
-/

open Filter MeasureTheory ProbabilityTheory Topology Asymptotics
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

namespace ProbabilityTheory

/-- A centered lattice tube occupying a fraction `rho` of the unit corridor
gives the corresponding principal-mode lower bound for the closed Brownian
unit corridor. -/
lemma closedUnitCorridorLowerBoundOfRhoCore
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho < 1)
    (hB : IsBrownianReal B P) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / (2 * rho ^ 2))) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath
          (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInClosedInterval (-(1 / 2 : ℝ)) (1 / 2)) := by
  let scale : ℕ → ℝ := fun n => rho * Real.sqrt n
  let radius : ℕ → ℕ := centeredLatticeRadius scale
  let time : ℕ → ℕ := fun n => max 1 n
  let width : ℕ → ℝ := fun n => ((2 * (radius n + 1) : ℕ) : ℝ)
  let principal : ℕ → ℝ := fun n => Real.cos
    (Real.pi / width n) ^ time n
  let tube : ℕ → ENNReal := fun n => horizontalTubeProbability
    (iidSequenceLaw rademacherMeasure) (1 / 2)
    (2 * radius n) n
  have hsqrtTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaleTop : Tendsto scale atTop atTop := by
    simpa [scale] using hsqrtTop.const_mul_atTop hrho
  have hradius : ∀ n, 0 < radius n := fun n => by
    simp [radius, centeredLatticeRadius]
  have hradiusTop : Tendsto (fun n => (radius n : ℝ)) atTop atTop := by
    simpa [radius] using tendsto_centeredLatticeRadius_atTop hscaleTop
  have hwidthTop : Tendsto width atTop atTop := by
    have hadd := tendsto_atTop_add_const_right atTop 1 hradiusTop
    simpa [width] using
      hadd.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hwidthScale : Tendsto (fun n => width n / scale n)
      atTop (nhds 1) := by
    simpa [width, radius] using tendsto_centeredDirichletWidth_div hscaleTop
  have hscaleWidth : Tendsto (fun n => scale n / width n)
      atTop (nhds 1) := by
    have hinv := hwidthScale.inv₀ one_ne_zero
    simpa [div_eq_mul_inv, mul_comm] using hinv
  have htimeScale : Tendsto (fun n => (time n : ℝ) / scale n ^ 2)
      atTop (nhds (1 / rho ^ 2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsqrtSq : Real.sqrt (n : ℝ) ^ 2 = n :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    have hmax : max 1 n = n := max_eq_right (by omega)
    simp only [time, scale, hmax]
    rw [mul_pow, hsqrtSq]
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne', hrho.ne']
  have hratio : Tendsto (fun n => (time n : ℝ) / width n ^ 2)
      atTop (nhds (1 / rho ^ 2)) := by
    have hproduct := htimeScale.mul (hscaleWidth.pow 2)
    have hproduct' : Tendsto (fun n =>
        (time n : ℝ) / scale n ^ 2 * (scale n / width n) ^ 2)
        atTop (nhds (1 / rho ^ 2)) := by simpa using hproduct
    apply hproduct'.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hscaleNe : scale n ≠ 0 := by
      dsimp [scale]
      positivity
    have hwidthNe : width n ≠ 0 := by
      dsimp [width]
      positivity
    field_simp
  have hprincipal : Tendsto principal atTop
      (nhds (Real.exp (-(Real.pi ^ 2) / (2 * rho ^ 2)))) := by
    have h := tendsto_centeredPrincipalPower_of_diffusiveRatio
      radius time (1 / rho ^ 2) hradius hwidthTop hratio
    convert h using 1
    field_simp [hrho.ne']
  have hprincipalENN : Tendsto (fun n => ENNReal.ofReal (principal n))
      atTop (nhds (ENNReal.ofReal
        (Real.exp (-(Real.pi ^ 2) / (2 * rho ^ 2))))) :=
    ENNReal.tendsto_ofReal hprincipal
  have hwidthLe : ∀ᶠ n in atTop, ((2 * radius n : ℕ) : ℝ) ≤
      Real.sqrt n := by
    have hgap : 0 < 1 - rho := sub_pos.mpr hrho_one
    filter_upwards [hsqrtTop.eventually_gt_atTop (2 / (1 - rho))] with n hn
    have hfloor := Nat.floor_le
      (show 0 ≤ rho * Real.sqrt (n : ℝ) / 2 by positivity)
    simp only [radius, centeredLatticeRadius, scale]
    change ((2 * (⌊rho * Real.sqrt (n : ℝ) / 2⌋₊ + 1) : ℕ) : ℝ) ≤
      Real.sqrt n
    push_cast
    have hmul : 2 < (1 - rho) * Real.sqrt n :=
      (div_lt_iff₀' hgap).mp hn
    nlinarith
  have htubeLower : ∀ᶠ n in atTop,
      ENNReal.ofReal (principal n) ≤ tube n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hmode := ofReal_centeredPrincipalPower_le_remainingMass
      (radius n) (time n) (hradius n)
    have hmodeTube : ENNReal.ofReal (principal n) ≤
        horizontalTubeProbability (iidSequenceLaw rademacherMeasure)
          (1 / 2) (2 * radius n) (time n) := by
      simpa [principal, width, Kernel.remainingMass] using
        hmode.trans_eq
          (centeredIntervalRademacherKernel_pow_apply_univ_eq_horizontalTubeProbability
            (radius n) (time n))
    have htimeEq : time n = n := by
      dsimp [time]
      exact max_eq_right (by omega)
    rw [htimeEq] at hmodeTube
    exact hmodeTube
  have htubeWeak : ∀ᶠ n in atTop, tube n ≤
      horizontalTubeProbability (iidSequenceLaw rademacherMeasure)
        (1 / 2) (Real.sqrt n) n := by
    filter_upwards [hwidthLe] with n hn
    exact horizontalTubeProbability_mono_width
      (iidSequenceLaw rademacherMeasure)
      (by norm_num) (by norm_num) (by simpa only [Nat.cast_mul,
        Nat.cast_ofNat] using hn)
  have hweakBounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => horizontalTubeProbability
        (iidSequenceLaw rademacherMeasure)
        (1 / 2) (Real.sqrt n) n) := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    exact Eventually.of_forall fun n => by
      calc
        horizontalTubeProbability (iidSequenceLaw rademacherMeasure)
            (1 / 2) (Real.sqrt n) n ≤
            iidSequenceLaw rademacherMeasure Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  have hlowerLimsup : ENNReal.ofReal
      (Real.exp (-(Real.pi ^ 2) / (2 * rho ^ 2))) ≤
      atTop.limsup (fun n : ℕ => horizontalTubeProbability
        (iidSequenceLaw rademacherMeasure)
        (1 / 2) (Real.sqrt n) n) := by
    calc
      ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / (2 * rho ^ 2))) =
          atTop.limsup (fun n => ENNReal.ofReal (principal n)) :=
        hprincipalENN.limsup_eq.symm
      _ ≤ atTop.limsup (fun n : ℕ => horizontalTubeProbability
          (iidSequenceLaw rademacherMeasure)
          (1 / 2) (Real.sqrt n) n) := by
        exact Filter.limsup_le_limsup
          ((htubeLower.and htubeWeak).mono fun _ h => h.1.trans h.2)
          (Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
          hweakBounded
  have hrademacher : IsCenteredUnitSecondMoment rademacherMeasure := by
    constructor <;> rw [integral_rademacherMeasure] <;> norm_num
  have hclosed := limsup_weakTube_le_brownian_skorokhodCorridor
    rademacherMeasure hrademacher hB
    (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  unfold horizontalTubeProbability at hlowerLimsup
  have h := hlowerLimsup.trans hclosed
  convert h using 1
  norm_num

/-- The same spectral and Portmanteau argument at arbitrary spatial width.
The exponent records the inverse square of the corridor width; this is the
small-time return estimate needed when a diffusive block is short relative to
the ambient corridor. -/
lemma closedCorridorLowerBoundOfRhoWidthCore
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    {rho width : ℝ} (hrho : 0 < rho) (hrho_one : rho < 1)
    (hwidth : 0 < width)
    (hB : IsBrownianReal B P) :
    ENNReal.ofReal (Real.exp
      (-(Real.pi ^ 2) / (2 * rho ^ 2 * width ^ 2))) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath
          (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInClosedInterval (-(width / 2)) (width / 2)) := by
  let effectiveWidth : ℝ := rho * width
  let scale : ℕ → ℝ := fun n => effectiveWidth * Real.sqrt n
  let radius : ℕ → ℕ := centeredLatticeRadius scale
  let time : ℕ → ℕ := fun n => max 1 n
  let dirichletWidth : ℕ → ℝ := fun n =>
    ((2 * (radius n + 1) : ℕ) : ℝ)
  let principal : ℕ → ℝ := fun n => Real.cos
    (Real.pi / dirichletWidth n) ^ time n
  let tube : ℕ → ENNReal := fun n => horizontalTubeProbability
    (iidSequenceLaw rademacherMeasure) (1 / 2)
    (2 * radius n) n
  have heffectivePos : 0 < effectiveWidth := by
    dsimp [effectiveWidth]
    positivity
  have heffectiveLe : effectiveWidth < width := by
    dsimp [effectiveWidth]
    nlinarith [mul_pos (sub_pos.mpr hrho_one) hwidth]
  have hsqrtTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaleTop : Tendsto scale atTop atTop := by
    simpa [scale] using hsqrtTop.const_mul_atTop heffectivePos
  have hradius : ∀ n, 0 < radius n := fun n => by
    simp [radius, centeredLatticeRadius]
  have hradiusTop : Tendsto (fun n => (radius n : ℝ)) atTop atTop := by
    simpa [radius] using tendsto_centeredLatticeRadius_atTop hscaleTop
  have hwidthTop : Tendsto dirichletWidth atTop atTop := by
    have hadd := tendsto_atTop_add_const_right atTop 1 hradiusTop
    simpa [dirichletWidth] using
      hadd.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hwidthScale : Tendsto (fun n => dirichletWidth n / scale n)
      atTop (nhds 1) := by
    simpa [dirichletWidth, scale, radius] using
      tendsto_centeredDirichletWidth_div hscaleTop
  have hscaleWidth : Tendsto (fun n => scale n / dirichletWidth n)
      atTop (nhds 1) := by
    have hinv := hwidthScale.inv₀ one_ne_zero
    simpa [div_eq_mul_inv, mul_comm] using hinv
  have htimeScale : Tendsto (fun n => (time n : ℝ) / scale n ^ 2)
      atTop (nhds (1 / effectiveWidth ^ 2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsqrtSq : Real.sqrt (n : ℝ) ^ 2 = n :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    have hmax : max 1 n = n := max_eq_right (by omega)
    simp only [time, scale, hmax]
    field_simp [heffectivePos.ne', hwidth.ne', hrho.ne',
      show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']
    nlinarith [hsqrtSq]
  have hratio : Tendsto (fun n => (time n : ℝ) / dirichletWidth n ^ 2)
      atTop (nhds (1 / effectiveWidth ^ 2)) := by
    have hproduct := htimeScale.mul (hscaleWidth.pow 2)
    have hproduct' : Tendsto (fun n =>
        (time n : ℝ) / scale n ^ 2 *
          (scale n / dirichletWidth n) ^ 2)
        atTop (nhds (1 / effectiveWidth ^ 2)) := by simpa using hproduct
    apply hproduct'.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hscaleNe : scale n ≠ 0 := by
      dsimp [scale]
      positivity
    have hwidthNe : dirichletWidth n ≠ 0 := by
      dsimp [dirichletWidth]
      positivity
    field_simp
  have hprincipal : Tendsto principal atTop
      (nhds (Real.exp
        (-(Real.pi ^ 2) / (2 * rho ^ 2 * width ^ 2)))) := by
    have h := tendsto_centeredPrincipalPower_of_diffusiveRatio
      radius time (1 / effectiveWidth ^ 2) hradius hwidthTop hratio
    convert h using 1
    congr 1
    dsimp [effectiveWidth]
    ring_nf
  have hprincipalENN : Tendsto (fun n => ENNReal.ofReal (principal n))
      atTop (nhds (ENNReal.ofReal (Real.exp
        (-(Real.pi ^ 2) / (2 * rho ^ 2 * width ^ 2))))) :=
    ENNReal.tendsto_ofReal hprincipal
  have hwidthLe : ∀ᶠ n in atTop, ((2 * radius n : ℕ) : ℝ) ≤
      width * Real.sqrt n := by
    have hgap : 0 < width - effectiveWidth := sub_pos.mpr heffectiveLe
    filter_upwards [hsqrtTop.eventually_gt_atTop (2 / (width - effectiveWidth))]
      with n hn
    have hfloor := Nat.floor_le
      (show 0 ≤ effectiveWidth * Real.sqrt (n : ℝ) / 2 by positivity)
    simp only [radius, centeredLatticeRadius, scale]
    change ((2 * (⌊effectiveWidth * Real.sqrt (n : ℝ) / 2⌋₊ + 1) : ℕ) : ℝ) ≤
      width * Real.sqrt n
    push_cast
    have hmul : 2 < (width - effectiveWidth) * Real.sqrt n :=
      (div_lt_iff₀' hgap).mp hn
    nlinarith
  have htubeLower : ∀ᶠ n in atTop,
      ENNReal.ofReal (principal n) ≤ tube n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hmode := ofReal_centeredPrincipalPower_le_remainingMass
      (radius n) (time n) (hradius n)
    have hmodeTube : ENNReal.ofReal (principal n) ≤
        horizontalTubeProbability (iidSequenceLaw rademacherMeasure)
          (1 / 2) (2 * radius n) (time n) := by
      simpa [principal, dirichletWidth, Kernel.remainingMass] using
        hmode.trans_eq
          (centeredIntervalRademacherKernel_pow_apply_univ_eq_horizontalTubeProbability
            (radius n) (time n))
    have htimeEq : time n = n := by
      dsimp [time]
      exact max_eq_right (by omega)
    rw [htimeEq] at hmodeTube
    exact hmodeTube
  have htubeWeak : ∀ᶠ n in atTop, tube n ≤
      horizontalTubeProbability (iidSequenceLaw rademacherMeasure)
        (1 / 2) (width * Real.sqrt n) n := by
    filter_upwards [hwidthLe] with n hn
    exact horizontalTubeProbability_mono_width
      (iidSequenceLaw rademacherMeasure)
      (by norm_num) (by norm_num)
      (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn)
  have hweakBounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => horizontalTubeProbability
        (iidSequenceLaw rademacherMeasure)
        (1 / 2) (width * Real.sqrt n) n) := by
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    exact Eventually.of_forall fun n => by
      calc
        horizontalTubeProbability (iidSequenceLaw rademacherMeasure)
            (1 / 2) (width * Real.sqrt n) n ≤
            iidSequenceLaw rademacherMeasure Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  have hlowerLimsup : ENNReal.ofReal (Real.exp
      (-(Real.pi ^ 2) / (2 * rho ^ 2 * width ^ 2))) ≤
      atTop.limsup (fun n : ℕ => horizontalTubeProbability
        (iidSequenceLaw rademacherMeasure)
        (1 / 2) (width * Real.sqrt n) n) := by
    calc
      ENNReal.ofReal (Real.exp
          (-(Real.pi ^ 2) / (2 * rho ^ 2 * width ^ 2))) =
          atTop.limsup (fun n => ENNReal.ofReal (principal n)) :=
        hprincipalENN.limsup_eq.symm
      _ ≤ atTop.limsup (fun n : ℕ => horizontalTubeProbability
          (iidSequenceLaw rademacherMeasure)
          (1 / 2) (width * Real.sqrt n) n) := by
        exact Filter.limsup_le_limsup
          ((htubeLower.and htubeWeak).mono fun _ h => h.1.trans h.2)
          (Filter.isCoboundedUnder_le_of_le atTop (fun _ => bot_le))
          hweakBounded
  have hrademacher : IsCenteredUnitSecondMoment rademacherMeasure := by
    constructor <;> rw [integral_rademacherMeasure] <;> norm_num
  have hBrownianCorridor :=
    limsup_centeredWeakTube_le_brownian_closedCorridor
      rademacherMeasure hrademacher hB hwidth.le
  exact hlowerLimsup.trans
    hBrownianCorridor

/-- Optimizing the inner-tube fraction up to one gives the sharp principal
exponent for the closed centered Brownian unit corridor. -/
lemma closedUnitCorridorLowerBoundCore
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    (hB : IsBrownianReal B P) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2)) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath
          (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInClosedInterval (-(1 / 2 : ℝ)) (1 / 2)) := by
  let rho : ℕ → ℝ := fun n ↦ (n : ℝ) / ((n : ℝ) + 1)
  let mass := P.map (Skorokhod.ofContinuousMap ∘
    continuousunitIntervalPath
      (hB.toIsPreBrownianReal.continuousModification)
      (hB.toIsPreBrownianReal.continuous_continuousModification))
    (Skorokhod.rangeInClosedInterval (-(1 / 2 : ℝ)) (1 / 2))
  have hrho : Tendsto rho atTop (nhds 1) := by
    simpa [rho] using (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hden : Tendsto (fun n ↦ 2 * rho n ^ 2) atTop (nhds 2) := by
    convert tendsto_const_nhds.mul (hrho.pow 2) using 1
    all_goals norm_num
  have hexponent : Tendsto (fun n ↦ -(Real.pi ^ 2) / (2 * rho n ^ 2))
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
    exact tendsto_const_nhds.div hden (by norm_num)
  have hreal : Tendsto
      (fun n ↦ Real.exp (-(Real.pi ^ 2) / (2 * rho n ^ 2)))
      atTop (nhds (Real.exp (-(Real.pi ^ 2) / 2))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hexponent
  have henn : Tendsto
      (fun n ↦ ENNReal.ofReal
        (Real.exp (-(Real.pi ^ 2) / (2 * rho n ^ 2))))
      atTop (nhds (ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2)))) :=
    ENNReal.tendsto_ofReal hreal
  apply le_of_tendsto henn
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hrhoPos : 0 < rho n := by
    dsimp [rho]
    positivity
  have hrhoLt : rho n < 1 := by
    dsimp [rho]
    rw [div_lt_one (by positivity)]
    norm_num
  exact closedUnitCorridorLowerBoundOfRhoCore
    hrhoPos hrhoLt hB

/-- The sharp closed-unit-corridor estimate is also a lower bound for every
strictly wider open corridor.  The explicit margin is half of the additional
width, so no boundary-regularity theorem is needed. -/
lemma openCorridorLowerBoundCore
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    (hB : IsBrownianReal B P)
    {width : ℝ} (hwidth : 1 < width) :
    ENNReal.ofReal (Real.exp (-(Real.pi ^ 2) / 2)) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath
          (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInOpenInterval (-(width / 2)) (width / 2)) := by
  refine (closedUnitCorridorLowerBoundCore
    hB).trans (measure_mono ?_)
  intro path hpath
  refine ⟨(width - 1) / 2, by linarith, fun t ↦ ?_⟩
  have ht := hpath t
  constructor <;> linarith

/-- In particular, the closed centered Brownian unit corridor has nonzero
probability. -/
lemma closedUnitCorridorNeZeroCore
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    (hB : IsBrownianReal B P) :
    P.map (Skorokhod.ofContinuousMap ∘
        continuousunitIntervalPath
          (hB.toIsPreBrownianReal.continuousModification)
          (hB.toIsPreBrownianReal.continuous_continuousModification))
        (Skorokhod.rangeInClosedInterval (-(1 / 2 : ℝ)) (1 / 2)) ≠ 0 := by
  intro hzero
  have h := closedUnitCorridorLowerBoundCore
    hB
  rw [hzero] at h
  exact (not_le_of_gt (ENNReal.ofReal_pos.2 (Real.exp_pos _))) h

end ProbabilityTheory
