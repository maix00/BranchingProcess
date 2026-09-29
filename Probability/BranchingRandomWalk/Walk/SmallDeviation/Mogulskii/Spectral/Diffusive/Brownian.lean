import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.FunctionalLimit.Brownian
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Diffusive.Lower
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Scaling.Discretization

/-!
# A quantitative Brownian corridor lower bound

The centered finite-interval spectrum supplies a positive lower bound for a
strictly smaller discrete tube.  Monotonicity and the closed-event half of
Donsker--Portmanteau then transfer that bound to the closed Brownian unit
corridor.  No explicit construction of Wiener measure is used.
-/

open Filter MeasureTheory ProbabilityTheory Topology

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- The closed centered unit corridor of any continuous standard Brownian
realization has positive mass.  The explicit constant is deliberately
nonoptimal; its role is to supply a verified positive block probability. -/
theorem ofReal_exp_neg_two_pi_sq_sub_one_le_brownian_closedCorridor
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ omega, Continuous (B · omega))
    (hmeasurable : ∀ t, Measurable (B t)) :
    ENNReal.ofReal (Real.exp (-2 * Real.pi ^ 2 - 1)) ≤
      P.map (Skorokhod.ofContinuousMap ∘
        continuousUnitIntervalPath B hcontinuous)
        (Skorokhod.rangeInClosedInterval (-(1 / 2 : ℝ)) (1 / 2)) := by
  let scale : ℕ → ℝ := fun n => Real.sqrt n / 2
  let radius : ℕ → ℕ := centeredLatticeRadius scale
  let time : ℕ → ℕ := fun n => max 1 n
  let width : ℕ → ℝ := fun n => ((2 * (radius n + 1) : ℕ) : ℝ)
  let principal : ℕ → ℝ := fun n => Real.cos
    (Real.pi / width n) ^ time n
  let tube : ℕ → ENNReal := fun n => horizontalTubeProbability
    (independentIncrementLaw rademacherMeasure) (1 / 2)
    (2 * radius n) n
  have hsqrtTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hscaleTop : Tendsto scale atTop atTop := by
    simpa [scale, div_eq_mul_inv, mul_comm] using
      hsqrtTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2⁻¹)
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
      atTop (nhds 4) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hsqrtSq : Real.sqrt (n : ℝ) ^ 2 = n :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    have hmax : max 1 n = n := max_eq_right (by omega)
    simp only [time, scale, hmax]
    rw [div_pow, hsqrtSq]
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast hn.ne']
    norm_num
  have hratio : Tendsto (fun n => (time n : ℝ) / width n ^ 2)
      atTop (nhds 4) := by
    have hproduct := htimeScale.mul (hscaleWidth.pow 2)
    have hproduct' : Tendsto (fun n =>
        (time n : ℝ) / scale n ^ 2 * (scale n / width n) ^ 2)
        atTop (nhds 4) := by simpa using hproduct
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
      (nhds (Real.exp (-2 * Real.pi ^ 2))) := by
    have h := tendsto_centeredPrincipalPower_of_diffusiveRatio
      radius time 4 hradius hwidthTop hratio
    convert h using 1
    ring_nf
  have hprincipalLower : ∀ᶠ n in atTop,
      Real.exp (-2 * Real.pi ^ 2 - 1) ≤ principal n := by
    have hlt : Real.exp (-2 * Real.pi ^ 2 - 1) <
        Real.exp (-2 * Real.pi ^ 2) := Real.exp_lt_exp.2 (by linarith)
    exact (tendsto_order.1 hprincipal).1 _ hlt |>.mono fun _ h => h.le
  have hwidthLe : ∀ᶠ n in atTop, ((2 * radius n : ℕ) : ℝ) ≤
      Real.sqrt n := by
    filter_upwards [hsqrtTop.eventually_gt_atTop 4] with n hn
    have hfloor := Nat.floor_le
      (show 0 ≤ Real.sqrt (n : ℝ) / 2 / 2 by positivity)
    simp only [radius, centeredLatticeRadius, scale]
    change ((2 * (⌊Real.sqrt (n : ℝ) / 2 / 2⌋₊ + 1) : ℕ) : ℝ) ≤
      Real.sqrt n
    push_cast
    nlinarith
  have htubeLower : ∀ᶠ n in atTop,
      ENNReal.ofReal (Real.exp (-2 * Real.pi ^ 2 - 1)) ≤ tube n := by
    filter_upwards [hprincipalLower, hwidthLe, eventually_gt_atTop 0]
        with n hprincipalN hwidthN hn
    have hmode := ofReal_centeredPrincipalPower_le_remainingMass
      (radius n) (time n) (hradius n)
    have hmodeTube : ENNReal.ofReal (principal n) ≤
        horizontalTubeProbability (independentIncrementLaw rademacherMeasure)
          (1 / 2) (2 * radius n) (time n) := by
      simpa [principal, width, Kernel.remainingMass] using
        hmode.trans_eq
          (centeredIntervalRademacherKernel_pow_apply_univ_eq_horizontalTubeProbability
            (radius n) (time n))
    have htimeEq : time n = n := by
      dsimp [time]
      exact max_eq_right (by omega)
    rw [htimeEq] at hmodeTube
    exact (ENNReal.ofReal_le_ofReal hprincipalN).trans hmodeTube
  have htubeWeak : ∀ᶠ n in atTop, tube n ≤
      horizontalTubeProbability (independentIncrementLaw rademacherMeasure)
        (1 / 2) (Real.sqrt n) n := by
    filter_upwards [hwidthLe] with n hn
    exact horizontalTubeProbability_mono_width
      (independentIncrementLaw rademacherMeasure)
      (by norm_num) (by norm_num) (by simpa only [Nat.cast_mul,
        Nat.cast_ofNat] using hn)
  have hlowerLimsup : ENNReal.ofReal
      (Real.exp (-2 * Real.pi ^ 2 - 1)) ≤
      atTop.limsup (fun n : ℕ => horizontalTubeProbability
        (independentIncrementLaw rademacherMeasure)
        (1 / 2) (Real.sqrt n) n) := by
    apply Filter.le_limsup_of_frequently_le
    exact (htubeLower.and htubeWeak).mono
      (fun _ h => h.1.trans h.2) |>.frequently
    apply Filter.isBoundedUnder_of_eventually_le (a := 1)
    exact Eventually.of_forall fun n => by
      calc
        horizontalTubeProbability (independentIncrementLaw rademacherMeasure)
            (1 / 2) (Real.sqrt n) n ≤
            independentIncrementLaw rademacherMeasure Set.univ :=
          measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
  have hrademacher : IsCenteredUnitSecondMoment rademacherMeasure := by
    constructor <;> rw [integral_rademacherMeasure] <;> norm_num
  have hclosed := limsup_weakTube_le_brownian_skorokhodCorridor
    rademacherMeasure hrademacher hB hcontinuous hmeasurable
    (a := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  unfold horizontalTubeProbability at hlowerLimsup
  have h := hlowerLimsup.trans hclosed
  convert h using 1
  norm_num

/-- In particular, the closed centered Brownian unit corridor has nonzero
probability. -/
theorem brownian_closedCorridor_ne_zero
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    [IsProbabilityMeasure P] {B : NNReal → Omega → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ omega, Continuous (B · omega))
    (hmeasurable : ∀ t, Measurable (B t)) :
    P.map (Skorokhod.ofContinuousMap ∘
        continuousUnitIntervalPath B hcontinuous)
        (Skorokhod.rangeInClosedInterval (-(1 / 2 : ℝ)) (1 / 2)) ≠ 0 := by
  intro hzero
  have h := ofReal_exp_neg_two_pi_sq_sub_one_le_brownian_closedCorridor
    hB hcontinuous hmeasurable
  rw [hzero] at h
  exact (not_le_of_gt (ENNReal.ofReal_pos.2 (Real.exp_pos _))) h

end ProbabilityTheory.RandomWalk.Mogulskii
