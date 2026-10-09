/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Probability.Process.Stable.PathLaw.FullProcess
public import Probability.Process.Stable.PathLaw.UnitInterval
public import Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Transfer
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.FullCorridor
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Probability.Process.Path.Cadlag.MeasurableMap
public import Topology.Cadlag.Skorokhod.LinearPath

import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# Gaussian stable path laws near linear paths

Any càdlàg stable process with standard Gaussian exponent-two increments has
positive probability in every linear path tube. The bridge/endpoint
independence is a finite-dimensional Gaussian fact; centered corridor
positivity is transferred from the path law itself through its iid unit-block
extension. No Brownian process witness is part of the hypothesis.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory

private theorem IsStableLevyProcess.isPreBrownianReal_of_standardGaussian
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ}
    (hB : IsStableLevyProcess 2 (gaussianReal 0 (1 : ℝ≥0)) B P) :
    IsPreBrownianReal B P := by
  let hInc := hB.increments
  have hLaw : ∀ t, HasLaw (B t) (gaussianReal 0 t) P := by
    intro t
    let c : ℝ := (t : ℝ) ^ (1 / (2 : ℝ))
    have hc2 : c ^ 2 = (t : ℝ) := by
      dsimp [c]
      convert Real.rpow_inv_natCast_pow (NNReal.coe_nonneg t)
        (by norm_num : (2 : ℕ) ≠ 0) using 1 <;> norm_num
    have hscale :
        (gaussianReal 0 (1 : ℝ≥0)).map (fun x : ℝ => c * x) =
          gaussianReal 0 t := by
      rw [gaussianReal_map_const_mul, mul_zero]
      congr 1
      apply NNReal.eq
      simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one]
      simpa using hc2
    have hdiff : HasLaw (fun ω => B t ω - B 0 ω)
        ((gaussianReal 0 (1 : ℝ≥0)).map (fun x : ℝ => c * x)) P := by
      simpa [c] using hInc.increment_hasLaw (0 : ℝ≥0) t (by simp)
    have hzero : B 0 =ᵐ[P] fun _ => (0 : ℝ) := by
      filter_upwards [hInc.ae_start_eq_zero] with ω hω
      exact hω
    have hfun : (fun ω => B t ω - B 0 ω) =ᵐ[P] fun ω => B t ω := by
      filter_upwards [hzero] with ω hω
      simp [hω]
    rw [hscale] at hdiff
    exact hdiff.congr hfun.symm
  exact HasIndepIncrements.isPreBrownianReal_of_hasLaw hLaw hInc.indepIncrements

private def rationalBrownianBridge {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (q : RationalCoordinate.UnitInterval) : Ω → ℝ :=
  fun ω => B (RationalCoordinate.toNNReal q) ω -
    (RationalCoordinate.toNNReal q : ℝ) * B 1 ω

private def brownianEndpointProcess {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (_ : Unit) : Ω → ℝ :=
  fun ω => B 1 ω

private theorem rationalBrownianBridge_indep_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    IndepFun (fun ω q => rationalBrownianBridge B q ω)
      (fun ω u => brownianEndpointProcess B u ω) P := by
  let base : IsGaussianProcess B P := hB.isGaussianProcess
  letI : IsProbabilityMeasure P := base.isProbabilityMeasure
  let joint : IsGaussianProcess
      (Sum.elim (rationalBrownianBridge B) (brownianEndpointProcess B)) P := by
    apply base.of_isGaussianProcess
    intro s
    cases s with
    | inl q =>
        let t : ℝ≥0 := RationalCoordinate.toNNReal q
        let I : Finset ℝ≥0 := {t, 1}
        have ht : t ∈ I := by simp [I]
        have h1 : (1 : ℝ≥0) ∈ I := by simp [I]
        refine ⟨I, {
          toFun := fun x => x ⟨t, ht⟩ - (t : ℝ) * x ⟨1, h1⟩
          map_add' := by
            intro x y
            simp only [Pi.add_apply]
            ring
          map_smul' := by
            intro c x
            simp only [Pi.smul_apply, smul_eq_mul]
            simp only [RingHom.id_apply]
            ring
        }, ?_⟩
        intro ω
        simp [rationalBrownianBridge, t, I, Finset.restrict_def]
    | inr u =>
        let I : Finset ℝ≥0 := {1}
        have h1 : (1 : ℝ≥0) ∈ I := by simp [I]
        refine ⟨I, {
          toFun := fun x => x ⟨1, h1⟩
          map_add' := by intro x y; simp
          map_smul' := by intro c x; simp
        }, ?_⟩
        intro ω
        simp [brownianEndpointProcess, I, Finset.restrict_def]
  have hmBridge : ∀ q, AEMeasurable (rationalBrownianBridge B q) P := by
    intro q
    exact (hB.aemeasurable
      (RationalCoordinate.toNNReal q)).sub
      ((hB.aemeasurable 1).const_mul _)
  have hmEnd : ∀ u, AEMeasurable (brownianEndpointProcess B u) P := by
    intro u
    exact hB.aemeasurable 1
  have hcov : ∀ q u,
      cov[rationalBrownianBridge B q, brownianEndpointProcess B u; P] = 0 := by
    intro q u
    let t : ℝ≥0 := RationalCoordinate.toNNReal q
    have ht : t ≤ 1 := RationalCoordinate.toNNReal_le_one q
    have htMem : MemLp (fun ω => B t ω) 2 P :=
      (base.hasGaussianLaw_eval t).memLp_two
    have h1Mem : MemLp (fun ω => B 1 ω) 2 P :=
      (base.hasGaussianLaw_eval 1).memLp_two
    change cov[fun ω => B t ω - (t : ℝ) * B 1 ω,
      fun ω => B 1 ω; P] = 0
    rw [covariance_fun_sub_left htMem (h1Mem.const_mul _) h1Mem,
      covariance_const_mul_left,
      hB.covariance_eval t 1,
      hB.covariance_eval 1 1]
    simp [min_eq_left ht]
  exact IsGaussianProcess.indepFun_of_covariance_eq_zero
    joint hmBridge hmEnd hcov

private theorem gaussianReal_measure_Ioo_pos
    (a radius : ℝ) (hradius : 0 < radius) :
    0 < gaussianReal 0 (1 : ℝ≥0) (Set.Ioo (a - radius) (a + radius)) := by
  have hvolume : (volume : Measure ℝ) ≪ gaussianReal 0 (1 : ℝ≥0) :=
    gaussianReal_absolutelyContinuous' 0 (by norm_num)
  letI : Measure.IsOpenPosMeasure (gaussianReal 0 (1 : ℝ≥0)) :=
    hvolume.isOpenPosMeasure
  exact isOpen_Ioo.measure_pos _ ⟨a, by constructor <;> linarith⟩

/-- A standard Gaussian stable process has positive probability to remain in
any uniform tube around any linear path on `[0,1]`. -/
theorem IsStableLevyProcess.measure_linearTube_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsStableLevyProcess 2 (gaussianReal 0 (1 : ℝ≥0)) B P)
    (slope width : ℝ) (hwidth : 0 < width) :
    0 < P (fullSegmentCorridorEvent
      (fun t ω => B t ω - slope * (t : ℝ)) 0 1 (-width) width) := by
  let δ : ℝ := width / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let hPre : IsPreBrownianReal B P :=
    hB.isPreBrownianReal_of_standardGaussian
  have hvolume : (volume : Measure ℝ) ≪ gaussianReal 0 (1 : ℝ≥0) :=
    gaussianReal_absolutelyContinuous' 0 (by norm_num)
  letI : Measure.IsOpenPosMeasure (gaussianReal 0 (1 : ℝ≥0)) :=
    hvolume.isOpenPosMeasure
  have hpositive : 0 < gaussianReal 0 (1 : ℝ≥0) (Set.Ioi 0) := by
    exact isOpen_Ioi.measure_pos _ ⟨1, by norm_num⟩
  have hnegative : 0 < gaussianReal 0 (1 : ℝ≥0) (Set.Iio 0) := by
    exact isOpen_Iio.measure_pos _ ⟨-1, by norm_num⟩
  have hsmall : 0 < P (fullSegmentCorridorEvent B 0 1 (-δ / 2) (δ / 2)) :=
    hB.measure_fullSegmentCorridor_pos (-δ / 2) (δ / 2)
      (by linarith) (by linarith) hpositive hnegative
  let bridgeFun : Ω → RationalCoordinate.UnitInterval → ℝ :=
    fun ω q => rationalBrownianBridge B q ω
  let bridgeCorridor : Set (RationalCoordinate.UnitInterval → ℝ) :=
    Skorokhod.rationalCoordinateCorridorWithMargin (-2 * δ) (2 * δ)
  let bridgeEvent : Set Ω := bridgeFun ⁻¹' bridgeCorridor
  let endpointFun : Ω → Unit → ℝ :=
    fun ω u => brownianEndpointProcess B u ω
  let endpointWindow : Set (Unit → ℝ) :=
    {x | x () ∈ Set.Ioo (slope - δ) (slope + δ)}
  let endpointEvent : Set Ω := endpointFun ⁻¹' endpointWindow
  have hBridgePos : 0 < P bridgeEvent := by
    have hsmallSub : ∀ᵐ ω ∂P,
        ω ∈ fullSegmentCorridorEvent B 0 1 (-δ / 2) (δ / 2) →
          ω ∈ bridgeEvent := by
      filter_upwards [hPre.eval_zero_ae_eq_zero] with ω hzero
      intro hω
      obtain ⟨margin, hmargin, hpath⟩ := hω
      have htop := hpath (⊤ : unitInterval)
      have htopBounds : -δ / 2 + margin ≤ B 1 ω ∧
          B 1 ω ≤ δ / 2 - margin := by
        simpa [segmentIncrement, hzero] using htop
      have hB1 : |B 1 ω| ≤ δ / 2 := by
        rw [abs_le]
        constructor <;> linarith [htopBounds.1, htopBounds.2, hmargin]
      change (fun q => rationalBrownianBridge B q ω) ∈
        Skorokhod.rationalCoordinateCorridorWithMargin (-2 * δ) (2 * δ)
      rw [Skorokhod.rationalCoordinateCorridorWithMargin_eq_real]
      refine ⟨δ, hδ, fun q => ?_⟩
      have hq := hpath (RationalCoordinate.toUnitInterval q)
      have hqtime : UnitInterval.toNNReal (RationalCoordinate.toUnitInterval q) =
          RationalCoordinate.toNNReal q := rfl
      have hqBounds : -δ / 2 + margin ≤
          B (RationalCoordinate.toNNReal q) ω ∧
          B (RationalCoordinate.toNNReal q) ω ≤ δ / 2 - margin := by
        simpa [segmentIncrement, hzero, hqtime] using hq
      have hBq : |B (RationalCoordinate.toNNReal q) ω| ≤ δ / 2 := by
        rw [abs_le]
        constructor <;> linarith [hqBounds.1, hqBounds.2, hmargin]
      have hqtime : |(RationalCoordinate.toNNReal q : ℝ)| ≤ 1 := by
        rw [abs_le]
        constructor
        · linarith [show 0 ≤ (RationalCoordinate.toNNReal q : ℝ) from NNReal.coe_nonneg _]
        · exact_mod_cast RationalCoordinate.toNNReal_le_one q
      have hW : |rationalBrownianBridge B q ω| ≤ δ := by
        rw [rationalBrownianBridge]
        calc
          |B (RationalCoordinate.toNNReal q) ω -
              (RationalCoordinate.toNNReal q : ℝ) * B 1 ω|
              ≤ |B (RationalCoordinate.toNNReal q) ω| +
                |(RationalCoordinate.toNNReal q : ℝ)| * |B 1 ω| := by
                  calc
                    _ ≤ |B (RationalCoordinate.toNNReal q) ω| +
                        |(RationalCoordinate.toNNReal q : ℝ) * B 1 ω| := abs_sub _ _
                    _ = |B (RationalCoordinate.toNNReal q) ω| +
                        |(RationalCoordinate.toNNReal q : ℝ)| * |B 1 ω| := by rw [abs_mul]
          _ ≤ δ / 2 + 1 * (δ / 2) := by
                gcongr
          _ = δ := by ring
      have hW' := abs_le.mp hW
      constructor <;> linarith
    have hle := measure_mono_ae hsmallSub
    exact hsmall.trans_le hle
  have hEndpointPos : 0 < P endpointEvent := by
    have hGauss := gaussianReal_measure_Ioo_pos slope δ hδ
    have hLaw := hPre.hasLaw_eval 1
    have hmeasure : P {ω | B 1 ω ∈ Set.Ioo (slope - δ) (slope + δ)} =
        gaussianReal 0 (1 : ℝ≥0) (Set.Ioo (slope - δ) (slope + δ)) :=
      hLaw.measure_eq measurableSet_Ioo
    have heq : endpointEvent = {ω | B 1 ω ∈ Set.Ioo (slope - δ) (slope + δ)} := by
      ext ω
      simp [endpointEvent, endpointFun, endpointWindow, brownianEndpointProcess]
    rw [heq, hmeasure]
    exact hGauss
  have hindep := rationalBrownianBridge_indep_endpoint hPre
  have hwindowMeas : MeasurableSet endpointWindow :=
    measurableSet_Ioo.preimage (measurable_pi_apply ())
  have hindepMass := hindep.measure_inter_preimage_eq_mul
    bridgeCorridor endpointWindow
    (Skorokhod.measurableSet_rationalCoordinateCorridorWithMargin
      (-2 * δ) (2 * δ)) hwindowMeas
  have hmassEq : P (bridgeEvent ∩ endpointEvent) = P bridgeEvent * P endpointEvent := by
    simpa [bridgeEvent, bridgeFun, endpointEvent, endpointFun,
      bridgeCorridor, endpointWindow] using hindepMass
  have hjointPos : 0 < P (bridgeEvent ∩ endpointEvent) := by
    rw [hmassEq]
    exact ENNReal.mul_pos (ne_of_gt hBridgePos) (ne_of_gt hEndpointPos)
  have hzero : ∀ᵐ ω ∂P, B 0 ω = 0 := hPre.eval_zero_ae_eq_zero
  have hsubset : ∀ᵐ ω ∂P,
      ω ∈ bridgeEvent ∩ endpointEvent →
        ω ∈ fullSegmentCorridorEvent
          (fun t ω => B t ω - slope * (t : ℝ)) 0 1 (-width) width := by
    filter_upwards [hB.ae_cadlag, hzero] with ω hcadlag hBzero
    intro hω
    rcases hω with ⟨hbridge, hendpoint⟩
    obtain ⟨bridgeMargin, hbridgeMargin, hbridge⟩ := hbridge
    have hend : B 1 ω - slope ∈ Set.Ioo (-δ) δ := by
      have hwindow : B 1 ω ∈ Set.Ioo (slope - δ) (slope + δ) := by
        simpa [endpointEvent, endpointFun, endpointWindow, brownianEndpointProcess] using
          hendpoint
      rcases hwindow with ⟨hlo, hhi⟩
      constructor <;> linarith
    have hendAbs : |B 1 ω - slope| < δ := by
      rw [abs_lt]
      exact ⟨hend.1, hend.2⟩
    have hpathCadlag : IsCadlag (fun t : ℝ≥0 => B t ω - slope * (t : ℝ)) := by
      exact hcadlag.sub (continuous_const.mul continuous_subtype_val).isCadlag
    apply (mem_fullSegmentCorridorEvent_iff_rational
      (fun t ω => B t ω - slope * (t : ℝ)) 0 1 (-width) width ω hpathCadlag).2
    rw [Skorokhod.rationalCoordinateCorridorWithMargin_eq_real]
    refine ⟨width / 4, by dsimp [δ] at *; linarith, fun q => ?_⟩
    have hbridgeq := hbridge q
    have hW : |rationalBrownianBridge B q ω| < 2 * δ := by
      rw [abs_lt]
      constructor <;> linarith [hbridgeq.1, hbridgeq.2]
    have htime : 0 ≤ (RationalCoordinate.toNNReal q : ℝ) ∧
        (RationalCoordinate.toNNReal q : ℝ) ≤ 1 := by
      constructor
      · exact NNReal.coe_nonneg _
      · exact_mod_cast RationalCoordinate.toNNReal_le_one q
    have hvalue :
        B (RationalCoordinate.toNNReal q) ω -
            slope * (RationalCoordinate.toNNReal q : ℝ) =
          rationalBrownianBridge B q ω +
            (RationalCoordinate.toNNReal q : ℝ) * (B 1 ω - slope) := by
      dsimp [rationalBrownianBridge]
      ring
    have htimeAbs : |(RationalCoordinate.toNNReal q : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [htime.1, htime.2]
    have hbound :
        |B (RationalCoordinate.toNNReal q) ω -
            slope * (RationalCoordinate.toNNReal q : ℝ)| < 3 * δ := by
      rw [hvalue]
      calc
        |rationalBrownianBridge B q ω +
            (RationalCoordinate.toNNReal q : ℝ) * (B 1 ω - slope)|
            ≤ |rationalBrownianBridge B q ω| +
              |(RationalCoordinate.toNNReal q : ℝ) * (B 1 ω - slope)| :=
                abs_add_le _ _
        _ = |rationalBrownianBridge B q ω| +
              |(RationalCoordinate.toNNReal q : ℝ)| * |B 1 ω - slope| := by rw [abs_mul]
        _ < 2 * δ + 1 * δ :=
              add_lt_add_of_lt_of_le hW (by
                calc
                  |(RationalCoordinate.toNNReal q : ℝ)| * |B 1 ω - slope|
                      ≤ 1 * |B 1 ω - slope| :=
                        mul_le_mul_of_nonneg_right htimeAbs (abs_nonneg _)
                  _ ≤ 1 * δ :=
                        mul_le_mul_of_nonneg_left (le_of_lt hendAbs) (by norm_num))
        _ = 3 * δ := by ring
    have hmarginBound : 3 * δ ≤ width - width / 4 := by
      dsimp [δ]
      linarith
    have htarget :
        -width + width / 4 ≤
          (B (RationalCoordinate.toNNReal q) ω -
            slope * (RationalCoordinate.toNNReal q : ℝ)) - B 0 ω ∧
        (B (RationalCoordinate.toNNReal q) ω -
            slope * (RationalCoordinate.toNNReal q : ℝ)) - B 0 ω ≤
          width - width / 4 := by
      rw [hBzero, sub_zero]
      rw [abs_lt] at hbound
      constructor <;> linarith
    simpa [segmentIncrement, hBzero] using htarget
  have hle := measure_mono_ae hsubset
  exact hjointPos.trans_le hle

/-- The unit-interval path law of a standard Gaussian stable process assigns
positive mass to every `J₁` ball centered at a linear path. -/
theorem IsStableLevyProcess.measure_pathLaw_linearBall_pos
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsStableLevyProcess 2 (gaussianReal 0 (1 : ℝ≥0)) B P)
    (slope radius : ℝ) (hradius : 0 < radius) :
    0 < Process.Path.Cadlag.pathLaw P
      (fun t ω => B (UnitInterval.toNNReal t) ω)
      (fun t => hB.increments.aemeasurable_eval (UnitInterval.toNNReal t))
      (Metric.ball (Skorokhod.linearPath slope) radius) := by
  let X : unitInterval → Ω → ℝ := fun t ω => B (UnitInterval.toNNReal t) ω
  have hX : ∀ t, AEMeasurable (X t) P := by
    intro t
    exact hB.increments.aemeasurable_eval (UnitInterval.toNNReal t)
  let pathLaw := Process.Path.Cadlag.pathLaw P X hX
  let width : ℝ := radius / 4
  have hwidth : 0 < width := by dsimp [width]; positivity
  have hwidthRadius : width < radius := by dsimp [width]; linarith
  have hsupport : 0 < P (fullSegmentCorridorEvent
      (fun t ω => B t ω - slope * (t : ℝ)) 0 1 (-width) width) := by
    simpa [width] using hB.measure_linearTube_pos slope (radius / 4) hwidth
  have hPre : IsPreBrownianReal B P :=
    hB.isPreBrownianReal_of_standardGaussian
  have hzero : ∀ᵐ ω ∂P, B 0 ω = 0 := hPre.eval_zero_ae_eq_zero
  have hsubset : ∀ᵐ ω ∂P,
      ω ∈ fullSegmentCorridorEvent
        (fun t ω => B t ω - slope * (t : ℝ)) 0 1 (-width) width →
          ω ∈ (Process.Path.Cadlag.pathMap X) ⁻¹'
            Metric.ball (Skorokhod.linearPath slope) radius := by
    filter_upwards [hB.ae_cadlag, hzero] with ω hcadlag hBzero
    intro htube
    obtain ⟨margin, hmargin, hpath⟩ := htube
    have hXcadlag : IsCadlag (fun t : unitInterval => X t ω) :=
      hcadlag.comp_monotone_continuous (fun _ _ h => h)
        UnitInterval.continuous_toNNReal
    let p : CadlagPath unitInterval ℝ := ⟨fun t => X t ω, hXcadlag⟩
    have hcoords :
        (fun q : RationalCoordinate.UnitInterval =>
          X (RationalCoordinate.toUnitInterval q) ω) =
        MeasureTheory.CadlagPath.denseEvaluation
          RationalCoordinate.toUnitInterval p := by
      funext q
      rfl
    have hmap : Process.Path.Cadlag.pathMap X ω = p := by
      change Function.extend
        (MeasureTheory.CadlagPath.denseEvaluation RationalCoordinate.toUnitInterval)
        id (fun _ => Skorokhod.ofContinuousMap (ContinuousMap.const unitInterval 0))
        (fun q : RationalCoordinate.UnitInterval =>
          X (RationalCoordinate.toUnitInterval q) ω) = p
      rw [hcoords]
      exact Process.Path.Cadlag.rationalEvaluationEmbedding.injective.extend_apply
        _ _ _
    have hpoint (t : unitInterval) :
        |X t ω - slope * (t : ℝ)| ≤ width := by
      have ht := hpath t
      have hsegment : -width + margin ≤
          X t ω - slope * (t : ℝ) ∧
          X t ω - slope * (t : ℝ) ≤ width - margin := by
        have ht' : -width + margin ≤
            B (UnitInterval.toNNReal t) ω -
              slope * (UnitInterval.toNNReal t : ℝ) ∧
            B (UnitInterval.toNNReal t) ω -
              slope * (UnitInterval.toNNReal t : ℝ) ≤ width - margin := by
          simpa [segmentIncrement, one_mul, zero_add, hBzero] using ht
        have htimeId : (UnitInterval.toNNReal t : ℝ) = (t : ℝ) := rfl
        rw [htimeId] at ht'
        simpa [X] using ht'
      rw [abs_le]
      exact ⟨by linarith [hsegment.1, hmargin],
        by linarith [hsegment.2, hmargin]⟩
    have huniform : Skorokhod.uniformEDist p (Skorokhod.linearPath slope) ≤
        ENNReal.ofReal width := by
      rw [Skorokhod.uniformEDist_eq_edist, UniformFun.edist_def]
      apply iSup_le
      intro t
      rw [edist_dist, Real.dist_eq]
      apply ENNReal.ofReal_le_ofReal
      simpa [p, X, Skorokhod.linearPath, Skorokhod.ofContinuousMap_apply] using
        hpoint t
    have hj1 : Skorokhod.j1EDist p (Skorokhod.linearPath slope) ≤
        ENNReal.ofReal width :=
      (Skorokhod.j1EDist_le_uniformEDist p _).trans huniform
    have hdistENN : edist p (Skorokhod.linearPath slope) < ENNReal.ofReal radius := by
      calc
        edist p (Skorokhod.linearPath slope) =
            Skorokhod.j1EDist p (Skorokhod.linearPath slope) :=
          Skorokhod.edist_cadlagPath_eq_j1EDist p _
        _ ≤ ENNReal.ofReal width := hj1
        _ < ENNReal.ofReal radius :=
          (ENNReal.ofReal_lt_ofReal_iff hradius).2 hwidthRadius
    have hdist : dist p (Skorokhod.linearPath slope) < radius := by
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hradius] at hdistENN
      exact hdistENN
    change Process.Path.Cadlag.pathMap X ω ∈
      Metric.ball (Skorokhod.linearPath slope) radius
    rw [hmap]
    exact Metric.mem_ball.mpr (by simpa [dist_comm] using hdist)
  have hmapLaw : pathLaw (Metric.ball (Skorokhod.linearPath slope) radius) =
      P ((Process.Path.Cadlag.pathMap X) ⁻¹'
        Metric.ball (Skorokhod.linearPath slope) radius) := by
    dsimp [pathLaw, Process.Path.Cadlag.pathLaw]
    exact Measure.map_apply_of_aemeasurable
      (Process.Path.Cadlag.aemeasurable_pathMap X hX)
      Metric.isOpen_ball.measurableSet
  rw [hmapLaw]
  exact hsupport.trans_le (measure_mono_ae hsubset)

/-- Every standard Gaussian exponent-two stable path law assigns positive
mass to every `J₁` ball centered at a linear path. The full-time process used
in the proof is built by concatenating iid copies of the given unit-interval
law, so this statement has no external Brownian-witness hypothesis. -/
theorem IsStableClockProcessLaw.measure_linearPathBall_pos
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 2 (gaussianReal 0 (1 : ℝ≥0))
      UnitInterval.clock P)
    (slope radius : ℝ) (hradius : 0 < radius) :
    0 < P (Metric.ball (Skorokhod.linearPath slope) radius) := by
  let hB := iidUnitPathBlockProcess_isStableLevyProcess hP
  have hpos := hB.measure_pathLaw_linearBall_pos slope radius hradius
  have hLawEq :=
    iidUnitPathBlockProcess_isStableLevyProcess_unitIntervalPathLaw_eq hP
  change 0 < (hB.unitIntervalPathLaw : Measure (CadlagPath unitInterval ℝ))
    (Metric.ball (Skorokhod.linearPath slope) radius) at hpos
  rw [hLawEq] at hpos
  exact hpos

end ProbabilityTheory

end
