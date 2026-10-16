/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.HorizontalTube.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.HorizontalTube.Scales
import Analysis.Asymptotics.Scale.Sampling
/-!
# Endpoint-window form of the finite-variance horizontal-tube rate

The public declarations in this module are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.horizontalTubeEndpointWindowEvent`: $T_{a,D,L}\cap\{(u-a)D\le S_L\le(v-a)D\}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.horizontalTubeEndpointWindowProbability`: the probability of that event under the given increment law.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate_along`: the endpoint-window logarithmic rate $-\pi^2\sigma^2/2$ along sampled times and widths whose endpoint interval contains a fixed subinterval of $(0,1)$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate_realWidthAlong`: the corresponding sampled rate for real widths.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate_realWidth`: the rate as $D\to\infty$ for real-width indexed integer horizons.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate`: the rate for integer widths and superquadratic horizons.

These results formalize Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii). The source-path rate is A. A. Mogul'skii, Theorem 3, Section 4, p. 764, in “Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open ProbabilityTheory.RandomWalk
open Asymptotics
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- A closed horizontal tube together with a fixed terminal window. -/
def horizontalTubeEndpointWindowEvent (a width : ℝ) (horizon : ℕ)
    (u v : ℝ) : Set (ℕ → ℝ) :=
  {increment | InHorizontalTube a width horizon increment ∧
    AdditivePath.displacement horizon increment ∈
      Set.Icc ((u - a) * width) ((v - a) * width)}

/-- The probability of a fixed endpoint window inside a closed horizontal
tube. -/
def horizontalTubeEndpointWindowProbability (law : Measure (ℕ → ℝ))
    (a width : ℝ) (horizon : ℕ) (u v : ℝ) : ℝ≥0∞ :=
  law (horizontalTubeEndpointWindowEvent a width horizon u v)

private noncomputable def terminalJumpEndpointCorridor (a u v : ℝ)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    ContinuousAdmissibleStepCorridor := by
  let upper := StepBoundary.singleJump ⊤ (by norm_num [unitInterval])
    ((1 - a : ℝ) : EReal) ((v - a : ℝ) : EReal)
  let lower := StepBoundary.singleJump ⊤ (by norm_num [unitInterval])
    ((-a : ℝ) : EReal) ((u - a : ℝ) : EReal)
  let endpoint : ℝ := (u + v) / 2 - a
  let witness : C(unitInterval, ℝ) :=
    ⟨fun t => endpoint * (t : ℝ), continuous_const.mul continuous_subtype_val⟩
  have hendpointLow : -a < endpoint := by dsimp [endpoint]; linarith
  have hendpointHigh : endpoint < 1 - a := by dsimp [endpoint]; linarith
  have hendpointWindowLow : u - a < endpoint := by dsimp [endpoint]; linarith
  have hendpointWindowHigh : endpoint < v - a := by dsimp [endpoint]; linarith
  refine ⟨⟨upper, lower⟩, ?_⟩
  refine ⟨witness, ?_, ?_⟩
  · simp [witness]
  · change (Skorokhod.ofContinuousMap witness : CadlagPath unitInterval ℝ) ∈
      Skorokhod.PathClass.StepCorridor.corridorSet upper lower
    change (Skorokhod.ofContinuousMap witness : CadlagPath unitInterval ℝ) ⊥ = 0 ∧
      ∀ t : unitInterval,
        lower.eval t < ((Skorokhod.ofContinuousMap witness :
          CadlagPath unitInterval ℝ) t : EReal) ∧
        ((Skorokhod.ofContinuousMap witness : CadlagPath unitInterval ℝ) t : EReal) <
          upper.eval t
    refine ⟨?_, ?_⟩
    · simp [Skorokhod.ofContinuousMap_apply, witness]
    · intro t
      by_cases ht : t = ⊤
      · subst t
        have hlowerTop : lower.eval ⊤ = ((u - a : ℝ) : EReal) := by
          dsimp [lower]
          exact StepBoundary.eval_singleJump_of_le ⊤ (by norm_num [unitInterval]) le_rfl
            (-a : EReal) (u - a : EReal)
        have hupperTop : upper.eval ⊤ = ((v - a : ℝ) : EReal) := by
          dsimp [upper]
          exact StepBoundary.eval_singleJump_of_le ⊤ (by norm_num [unitInterval]) le_rfl
            (1 - a : EReal) (v - a : EReal)
        rw [Skorokhod.ofContinuousMap_apply, hlowerTop, hupperTop]
        dsimp [witness, endpoint]
        have hlow : u - a < ((u + v) / 2 - a) * 1 := by
          rw [mul_one]
          simpa [endpoint] using hendpointWindowLow
        have hhigh : ((u + v) / 2 - a) * 1 < v - a := by
          rw [mul_one]
          simpa [endpoint] using hendpointWindowHigh
        exact ⟨by exact_mod_cast hlow, by exact_mod_cast hhigh⟩
      · have htlt : t < (⊤ : unitInterval) := (lt_top_iff_ne_top).2 ht
        have htime : 0 ≤ (t : ℝ) ∧ (t : ℝ) < 1 :=
          ⟨t.property.1, Subtype.mk_lt_mk.mp htlt⟩
        have hvalueLow : -a < endpoint * (t : ℝ) := by
          by_cases hend : 0 ≤ endpoint
          · have hnonneg : 0 ≤ endpoint * (t : ℝ) := mul_nonneg hend htime.1
            linarith
          · have hend' : endpoint < 0 := lt_of_not_ge hend
            have hmul : endpoint ≤ endpoint * (t : ℝ) := by
              calc
                endpoint = endpoint * 1 := by ring
                _ ≤ endpoint * (t : ℝ) :=
                  mul_le_mul_of_nonpos_left htime.2.le hend'.le
            linarith
        have hvalueHigh : endpoint * (t : ℝ) < 1 - a := by
          by_cases hend : endpoint ≤ 0
          · have hmul : endpoint * (t : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hend htime.1
            linarith
          · have hend' : 0 < endpoint := lt_of_not_ge hend
            have hmul : endpoint * (t : ℝ) ≤ endpoint := by
              calc
                endpoint * (t : ℝ) ≤ endpoint * 1 :=
                  mul_le_mul_of_nonneg_left htime.2.le hend'.le
                _ = endpoint := by ring
            linarith
        have hlowEval : lower.eval t = ((-a : ℝ) : EReal) := by
          dsimp [lower]
          rw [StepBoundary.eval_singleJump_of_lt ⊤ (by norm_num [unitInterval]) htlt]
        have huEval : upper.eval t = ((1 - a : ℝ) : EReal) := by
          dsimp [upper]
          rw [StepBoundary.eval_singleJump_of_lt ⊤ (by norm_num [unitInterval]) htlt]
        rw [Skorokhod.ofContinuousMap_apply, hlowEval, huEval]
        dsimp [witness]
        exact ⟨by exact_mod_cast hvalueLow, by exact_mod_cast hvalueHigh⟩

private lemma terminalJumpEndpointCorridor_energy (a u v : ℝ)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    (terminalJumpEndpointCorridor a u v ha haOne hu huv hv).energy 2 = 1 := by
  let c := terminalJumpEndpointCorridor a u v ha haOne hu huv hv
  let upper := StepBoundary.constant ((1 - a : ℝ) : EReal)
  let lower := StepBoundary.constant ((-a : ℝ) : EReal)
  let constant : ContinuousAdmissibleStepCorridor := by
    refine ⟨⟨upper, lower⟩, ?_⟩
    refine ⟨ContinuousMap.const unitInterval (0 : ℝ), ?_, ?_⟩
    · simp
    · change (Skorokhod.ofContinuousMap (ContinuousMap.const unitInterval (0 : ℝ)) :
        CadlagPath unitInterval ℝ) ∈
        Skorokhod.PathClass.StepCorridor.corridorSet upper lower
      change (Skorokhod.ofContinuousMap (ContinuousMap.const unitInterval (0 : ℝ)) :
        CadlagPath unitInterval ℝ) ⊥ = 0 ∧
        ∀ t : unitInterval,
          lower.eval t < ((Skorokhod.ofContinuousMap
            (ContinuousMap.const unitInterval (0 : ℝ)) :
              CadlagPath unitInterval ℝ) t : EReal) ∧
          ((Skorokhod.ofContinuousMap (ContinuousMap.const unitInterval (0 : ℝ)) :
            CadlagPath unitInterval ℝ) t : EReal) < upper.eval t
      refine ⟨by simp [Skorokhod.ofContinuousMap_apply], ?_⟩
      intro t
      rw [StepBoundary.eval_constant, StepBoundary.eval_constant]
      exact ⟨by exact_mod_cast (neg_lt_zero.mpr ha),
        by exact_mod_cast (sub_pos.mpr haOne)⟩
  have htop : (⊤ : unitInterval) ≠ ⊥ := by norm_num [unitInterval]
  have heq := ContinuousAdmissibleStepCorridor.energy_eq_of_boundaries_eq_off_top
    (α := 2) (c := c) (d := constant)
    (fun t ht => by
      dsimp [c, terminalJumpEndpointCorridor]
      rw [StepBoundary.eval_singleJump_of_lt ⊤ htop
        ((lt_top_iff_ne_top).2 ht), StepBoundary.eval_constant]
      norm_cast)
    (fun t ht => by
      dsimp [c, terminalJumpEndpointCorridor]
      rw [StepBoundary.eval_singleJump_of_lt ⊤ htop
        ((lt_top_iff_ne_top).2 ht), StepBoundary.eval_constant]
      norm_cast)
  have hconstant : constant.energy 2 = 1 := by
    have henergy := ContinuousAdmissibleStepCorridor.energy_eq_widthCost_of_constant_values
      2 constant ((1 - a : ℝ) : EReal) ((-a : ℝ) : EReal)
      (fun t => by simp [constant, upper, StepBoundary.eval_constant])
      (fun t => by simp [constant, lower, StepBoundary.eval_constant])
    rw [henergy, widthCost_coe_sub]
    · norm_num
    · linarith
  exact heq.trans hconstant

private noncomputable def terminalJumpEndpointCorridorUnion (a u v : ℝ)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    FiniteCorridorUnion 2 := by
  let c := terminalJumpEndpointCorridor a u v ha haOne hu huv hv
  refine ⟨1, by norm_num, fun _ => c, ?_⟩
  have hmin : finiteMinimumEnergy 2 1 (by norm_num) (fun _ : Fin 1 => c) = c.energy 2 := by
    simp [finiteMinimumEnergy]
  rw [hmin]
  have henergy : c.energy 2 = 1 := by
    simpa [c] using terminalJumpEndpointCorridor_energy a u v ha haOne hu huv hv
  rw [henergy]
  norm_num

private lemma terminalJumpEndpointCorridorUnion_toSet (a u v : ℝ)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    (terminalJumpEndpointCorridorUnion a u v ha haOne hu huv hv).toSet =
      (terminalJumpEndpointCorridor a u v ha haOne hu huv hv).toSet := by
  ext path
  simp [terminalJumpEndpointCorridorUnion, FiniteCorridorUnion.toSet]

private lemma terminalJumpEndpointCorridorUnion_realEnergy (a u v : ℝ)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    (terminalJumpEndpointCorridorUnion a u v ha haOne hu huv hv).realEnergy = 1 := by
  change (finiteMinimumEnergy 2 1 (by norm_num)
      (fun _ : Fin 1 => terminalJumpEndpointCorridor a u v ha haOne hu huv hv)).toReal = 1
  have hmin : finiteMinimumEnergy 2 1 (by norm_num)
      (fun _ : Fin 1 => terminalJumpEndpointCorridor a u v ha haOne hu huv hv) =
        (terminalJumpEndpointCorridor a u v ha haOne hu huv hv).energy 2 := by
    simp [finiteMinimumEnergy]
  rw [hmin, terminalJumpEndpointCorridor_energy]
  norm_num

private lemma sourceTerminalJumpCorridor_subset_endpointWindow
    {n : ℕ} {scale : ℕ → ℝ} {a u v : ℝ}
    (hn : 0 < n) (hscale : 0 < scale n)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    {increment : ℕ → ℝ |
      sourceNormalizedStepCadlagPathIcc scale n increment ∈
        (terminalJumpEndpointCorridor a u v ha haOne hu huv hv).toSet} ⊆
      horizontalTubeEndpointWindowEvent a (scale n) (n - 1) u v := by
  intro increment hcorridor
  let path := sourceNormalizedStepCadlagPathIcc scale n increment
  let c := terminalJumpEndpointCorridor a u v ha haOne hu huv hv
  change path ⊥ = 0 ∧ ∀ t : unitInterval,
      c.lower.eval t < (path t : EReal) ∧ (path t : EReal) < c.upper.eval t at hcorridor
  have htopLower : c.lower.eval ⊤ = ((u - a : ℝ) : EReal) := by
    dsimp [c, terminalJumpEndpointCorridor]
    exact StepBoundary.eval_singleJump_of_le ⊤ (by norm_num [unitInterval]) le_rfl
      (-a : EReal) (u - a : EReal)
  have htopUpper : c.upper.eval ⊤ = ((v - a : ℝ) : EReal) := by
    dsimp [c, terminalJumpEndpointCorridor]
    exact StepBoundary.eval_singleJump_of_le ⊤ (by norm_num [unitInterval]) le_rfl
      (1 - a : EReal) (v - a : EReal)
  have htopBounds := hcorridor.2 ⊤
  rw [htopLower, htopUpper,
    sourceNormalizedStepCadlagPathIcc_apply_top scale hn increment] at htopBounds
  have hterminalNorm :
      u - a < (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment ∧
        (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment < v - a := by
    exact_mod_cast htopBounds
  have hterminal : AdditivePath.displacement (n - 1) increment ∈
      Set.Icc ((u - a) * scale n) ((v - a) * scale n) := by
    have hdiv : (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment =
        AdditivePath.displacement (n - 1) increment / scale n := by
      rw [div_eq_mul_inv]
      ring
    rw [hdiv] at hterminalNorm
    exact ⟨(lt_div_iff₀ hscale).1 hterminalNorm.1 |>.le,
      (div_lt_iff₀ hscale).1 hterminalNorm.2 |>.le⟩
  have htube : InHorizontalTube a (scale n) (n - 1) increment := by
    intro i
    let j : Fin n := ⟨i.val + 1, by omega⟩
    have hrange := sourceNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement
      scale hn increment
    have hmem : (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment ∈
        Set.range path := by
      rw [hrange]
      exact ⟨j, rfl⟩
    obtain ⟨t, ht⟩ := hmem
    by_cases htTop : t = ⊤
    · subst t
      have htopTubeNorm :
          -a < (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment ∧
            (scale n)⁻¹ * AdditivePath.displacement (n - 1) increment < 1 - a := by
        constructor
        · exact lt_trans (by linarith : -a < u - a) hterminalNorm.1
        · exact lt_trans hterminalNorm.2 (by linarith : v - a < 1 - a)
      have hpathTopTube : -a < path ⊤ ∧ path ⊤ < 1 - a := by
        rw [show path = sourceNormalizedStepCadlagPathIcc scale n increment by rfl,
          sourceNormalizedStepCadlagPathIcc_apply_top scale hn increment]
        exact htopTubeNorm
      rw [ht] at hpathTopTube
      have hdiv : (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment =
          AdditivePath.displacement (j : ℕ) increment / scale n := by
        rw [div_eq_mul_inv]
        ring
      rw [hdiv] at hpathTopTube
      exact ⟨(lt_div_iff₀ hscale).1 hpathTopTube.1 |>.le,
        (div_lt_iff₀ hscale).1 hpathTopTube.2 |>.le⟩
    · have hlowerEval : c.lower.eval t = ((-a : ℝ) : EReal) := by
        dsimp [c, terminalJumpEndpointCorridor]
        exact StepBoundary.eval_singleJump_of_lt ⊤ (by norm_num [unitInterval])
          ((lt_top_iff_ne_top).2 htTop) (-a : EReal) (u - a : EReal)
      have hupperEval : c.upper.eval t = ((1 - a : ℝ) : EReal) := by
        dsimp [c, terminalJumpEndpointCorridor]
        exact StepBoundary.eval_singleJump_of_lt ⊤ (by norm_num [unitInterval])
          ((lt_top_iff_ne_top).2 htTop) (1 - a : EReal) (v - a : EReal)
      have hnormalized :
          -a < (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment ∧
            (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment < 1 - a := by
        have h := hcorridor.2 t
        rw [hlowerEval, hupperEval, ht] at h
        exact_mod_cast h
      have hdiv : (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment =
          AdditivePath.displacement (j : ℕ) increment / scale n := by
        rw [div_eq_mul_inv]
        ring
      rw [hdiv] at hnormalized
      exact ⟨(lt_div_iff₀ hscale).1 hnormalized.1 |>.le,
        (div_lt_iff₀ hscale).1 hnormalized.2 |>.le⟩
  exact ⟨htube, hterminal⟩

/-- Sampled-width form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii). The endpoint
window eventually contains a fixed interior interval. Its rate input is
Mogul'skii, Theorem 3, Section 4, p. 764, in “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081. -/
theorem centeredFiniteVariance_endpointWindowProbabilityRate_along
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {time width : ℕ → ℕ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k)
    (hwidth : Tendsto (fun k : ℕ => (width k : ℝ)) atTop atTop)
    (hwidthSq : Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ)) atTop (𝓝 0))
    {v₁ v₂ : ℕ → ℝ} {a u v : ℝ}
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hwindow : ∀ᶠ k : ℕ in atTop,
      v₁ (width k) ≤ u ∧ v ≤ v₂ (width k))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν) :
    Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
          (width k : ℝ) (time k - 1) (v₁ (width k)) (v₂ (width k))).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let scale := sampledIntegerWidthScale time width htime
  let corridorUnion := terminalJumpEndpointCorridorUnion a u v ha haOne hu huv hv
  let sourceProbability : ℕ → ℝ≥0∞ := fun n => iidSequenceLaw ν
    {increment : ℕ → ℝ |
      sourceNormalizedStepCadlagPathIcc scale n increment ∈ corridorUnion.toSet}
  let targetProbability : ℕ → ℝ≥0∞ := fun k =>
    horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
      (width k : ℝ) (time k - 1) (v₁ (width k)) (v₂ (width k))
  let tubeProbability : ℕ → ℝ≥0∞ := fun k =>
    horizontalTubeProbability (iidSequenceLaw ν) a (width k : ℝ) (time k - 1)
  let limit : ℝ := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)
  have hsmall := sampledIntegerWidthScale_isSmallDeviationScale
    htime htimePos hwidth hwidthSq
  have hscaleEq (k : ℕ) : scale (time k) = (width k : ℝ) := by
    simp [scale, sampledIntegerWidthScale,
      sampledTimeIntervalIndex_at_time htime]
  have hsource :=
    centeredFiniteVariance_sourceFiniteCorridorUnionProbabilityRate
      hsmall hcentered hsquare hvariance corridorUnion
  have hsourcePositive : ∀ᶠ k : ℕ in atTop,
      0 < (sourceProbability (time k)).toReal := by
    filter_upwards [htime.tendsto_atTop.eventually hsource.1] with k hk
    simpa [sourceProbability] using hk
  have hsourceRateAtTime : Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ) *
        Real.log (sourceProbability (time k)).toReal)
      atTop (𝓝 limit) := by
    have hrate := hsource.2.comp htime.tendsto_atTop
    have heq : (fun k : ℕ => scale (time k) ^ 2 / (time k : ℝ) *
        Real.log (sourceProbability (time k)).toReal) =ᶠ[atTop]
        (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ) *
          Real.log (sourceProbability (time k)).toReal) := by
      filter_upwards with k
      rw [hscaleEq k]
    have hrate' := hrate.congr' heq
    have henergy := terminalJumpEndpointCorridorUnion_realEnergy
      a u v ha haOne hu huv hv
    simpa [sourceProbability, corridorUnion, limit, henergy] using hrate'
  have hsourceRatePred : Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
        Real.log (sourceProbability (time k)).toReal)
      atTop (𝓝 limit) :=
    tendsto_scaledRate_div_predTime htime.tendsto_atTop hsourceRateAtTime
  have htubeRate :=
    centeredFiniteVariance_closedHorizontalTubeProbabilityRate_along
      htime htimePos hwidth hwidthSq hcentered hsquare hvariance ha haOne
  have hscalePositive : ∀ᶠ k : ℕ in atTop, 0 < scale (time k) :=
    htime.tendsto_atTop.eventually hsmall.eventually_pos
  have hlogSqueeze : ∀ᶠ k : ℕ in atTop,
      (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (sourceProbability (time k)).toReal ≤
        (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (targetProbability k).toReal ∧
      (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (targetProbability k).toReal ≤
        (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (tubeProbability k).toReal := by
    filter_upwards [hsourcePositive, hscalePositive, hwindow]
      with k hsourcePos hscalePos hwindowK
    have hsourceSubset :
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ⊆
          horizontalTubeEndpointWindowEvent a (width k : ℝ) (time k - 1)
            (v₁ (width k)) (v₂ (width k)) := by
      have hfixed :
          {increment : ℕ → ℝ |
            sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ⊆
            horizontalTubeEndpointWindowEvent a (width k : ℝ) (time k - 1) u v := by
        rw [terminalJumpEndpointCorridorUnion_toSet a u v ha haOne hu huv hv]
        simpa [hscaleEq k] using
          sourceTerminalJumpCorridor_subset_endpointWindow
            (n := time k) (scale := scale) (a := a) (u := u) (v := v)
            (htimePos k) hscalePos ha haOne hu huv hv
      intro increment hinc
      rcases hfixed hinc with ⟨htube, ⟨hlower, hupper⟩⟩
      constructor
      · exact htube
      · constructor
        · apply le_trans _ hlower
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (width k))
          linarith [hwindowK.1]
        · apply le_trans hupper _
          apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg (width k))
          linarith [hwindowK.2]
    have hsourceMeasure : sourceProbability (time k) ≤ targetProbability k := by
      change iidSequenceLaw ν
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ≤
        iidSequenceLaw ν
          (horizontalTubeEndpointWindowEvent a (width k : ℝ) (time k - 1)
            (v₁ (width k)) (v₂ (width k)))
      exact measure_mono hsourceSubset
    have htargetSubset :
        horizontalTubeEndpointWindowEvent a (width k : ℝ) (time k - 1)
          (v₁ (width k)) (v₂ (width k)) ⊆
        {increment | InHorizontalTube a (width k : ℝ) (time k - 1) increment} := by
      intro increment h
      exact h.1
    have htargetMeasure : targetProbability k ≤ tubeProbability k := by
      change iidSequenceLaw ν
        (horizontalTubeEndpointWindowEvent a (width k : ℝ) (time k - 1)
          (v₁ (width k)) (v₂ (width k))) ≤
        iidSequenceLaw ν
          {increment | InHorizontalTube a (width k : ℝ) (time k - 1) increment}
      exact measure_mono htargetSubset
    have hsourceReal := ENNReal.toReal_mono (measure_ne_top _ _) hsourceMeasure
    have htargetPos : 0 < (targetProbability k).toReal :=
      lt_of_lt_of_le hsourcePos hsourceReal
    have htargetReal := ENNReal.toReal_mono (measure_ne_top _ _) htargetMeasure
    have htubePos : 0 < (tubeProbability k).toReal :=
      lt_of_lt_of_le htargetPos htargetReal
    have hlogLower : Real.log (sourceProbability (time k)).toReal ≤
        Real.log (targetProbability k).toReal :=
      Real.log_le_log hsourcePos hsourceReal
    have hlogUpper : Real.log (targetProbability k).toReal ≤
        Real.log (tubeProbability k).toReal :=
      Real.log_le_log htargetPos htargetReal
    have hfactor : 0 ≤ (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) :=
      div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    exact ⟨mul_le_mul_of_nonneg_left hlogLower hfactor,
      mul_le_mul_of_nonneg_left hlogUpper hfactor⟩
  have hrate : Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) *
        Real.log (targetProbability k).toReal)
      atTop (𝓝 limit) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hsourceRatePred htubeRate ?_ ?_
    · filter_upwards [hlogSqueeze] with k hk
      exact hk.1
    · filter_upwards [hlogSqueeze] with k hk
      exact hk.2
  simpa [targetProbability, limit] using hrate

/-- Real-width sampled form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii).
For positive real widths $D_k\to\infty$, time scales $t_k$ with
$D_k^2/t_k\to0$, and a terminal window eventually containing a fixed
$[u,v]\subset(0,1)$, the endpoint-window logarithmic rate is
$-\pi^2\sigma^2/2$. The proof uses the same terminal-jump source
corridor and upper horizontal-tube squeeze as the integer-width form.
The source rate is A. A. Mogul'skii, Theorem 3, Section 4, p. 764, in “Small
deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in
a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4)
(1975), 726–736, DOI 10.1137/1119081. -/
theorem centeredFiniteVariance_endpointWindowProbabilityRate_realWidthAlong
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {time : ℕ → ℕ} {width : ℕ → ℝ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k)
    (hwidthPos : ∀ k, 0 < width k)
    (hwidth : Tendsto width atTop atTop)
    (hwidthSq : Tendsto
      (fun k : ℕ => width k ^ 2 / (time k : ℝ)) atTop (𝓝 0))
    {v₁ v₂ : ℝ → ℝ} {a u v : ℝ}
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hwindow : ∀ᶠ k : ℕ in atTop,
      v₁ (width k) ≤ u ∧ v ≤ v₂ (width k))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν) :
    Tendsto
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
          (width k) (time k - 1) (v₁ (width k)) (v₂ (width k))).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let scale := sampledRealWidthScale time width htime
  let corridorUnion := terminalJumpEndpointCorridorUnion a u v ha haOne hu huv hv
  let sourceProbability : ℕ → ℝ≥0∞ := fun n => iidSequenceLaw ν
    {increment : ℕ → ℝ |
      sourceNormalizedStepCadlagPathIcc scale n increment ∈ corridorUnion.toSet}
  let targetProbability : ℕ → ℝ≥0∞ := fun k =>
    horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
      (width k) (time k - 1) (v₁ (width k)) (v₂ (width k))
  let tubeProbability : ℕ → ℝ≥0∞ := fun k =>
    horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)
  let limit : ℝ := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)
  have hsmall := sampledRealWidthScale_isSmallDeviationScale
    htime htimePos hwidthPos hwidth hwidthSq
  have hscaleEq (k : ℕ) : scale (time k) = width k := by
    simp [scale, sampledRealWidthScale,
      sampledTimeIntervalIndex_at_time htime]
  have hsource :=
    centeredFiniteVariance_sourceFiniteCorridorUnionProbabilityRate
      hsmall hcentered hsquare hvariance corridorUnion
  have hsourcePositive : ∀ᶠ k : ℕ in atTop,
      0 < (sourceProbability (time k)).toReal := by
    filter_upwards [htime.tendsto_atTop.eventually hsource.1] with k hk
    simpa [sourceProbability] using hk
  have hsourceRateAtTime : Tendsto
      (fun k : ℕ => width k ^ 2 / (time k : ℝ) *
        Real.log (sourceProbability (time k)).toReal)
      atTop (𝓝 limit) := by
    have hrate := hsource.2.comp htime.tendsto_atTop
    have heq : (fun k : ℕ => scale (time k) ^ 2 / (time k : ℝ) *
        Real.log (sourceProbability (time k)).toReal) =ᶠ[atTop]
        (fun k : ℕ => width k ^ 2 / (time k : ℝ) *
          Real.log (sourceProbability (time k)).toReal) := by
      filter_upwards with k
      rw [hscaleEq k]
    have hrate' := hrate.congr' heq
    have henergy := terminalJumpEndpointCorridorUnion_realEnergy
      a u v ha haOne hu huv hv
    simpa [sourceProbability, corridorUnion, limit, henergy] using hrate'
  have hsourceRatePred : Tendsto
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
        Real.log (sourceProbability (time k)).toReal)
      atTop (𝓝 limit) :=
    tendsto_scaledRate_div_predTime htime.tendsto_atTop hsourceRateAtTime
  have htubeRate :=
    centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidthAlong
      htime htimePos hwidthPos hwidth hwidthSq hcentered hsquare hvariance ha haOne
  have hscalePositive : ∀ᶠ k : ℕ in atTop, 0 < scale (time k) :=
    htime.tendsto_atTop.eventually hsmall.eventually_pos
  have hlogSqueeze : ∀ᶠ k : ℕ in atTop,
      width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (sourceProbability (time k)).toReal ≤
        width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (targetProbability k).toReal ∧
      width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (targetProbability k).toReal ≤
        width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
          Real.log (tubeProbability k).toReal := by
    filter_upwards [hsourcePositive, hscalePositive, hwindow]
      with k hsourcePos hscalePos hwindowK
    have hsourceSubset :
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ⊆
          horizontalTubeEndpointWindowEvent a (width k) (time k - 1)
            (v₁ (width k)) (v₂ (width k)) := by
      have hfixed :
          {increment : ℕ → ℝ |
            sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ⊆
            horizontalTubeEndpointWindowEvent a (width k) (time k - 1) u v := by
        rw [terminalJumpEndpointCorridorUnion_toSet a u v ha haOne hu huv hv]
        simpa [hscaleEq k] using
          sourceTerminalJumpCorridor_subset_endpointWindow
            (n := time k) (scale := scale) (a := a) (u := u) (v := v)
            (htimePos k) hscalePos ha haOne hu huv hv
      intro increment hinc
      rcases hfixed hinc with ⟨htube, ⟨hlower, hupper⟩⟩
      constructor
      · exact htube
      · constructor
        · apply le_trans _ hlower
          apply mul_le_mul_of_nonneg_right _ (hwidthPos k).le
          linarith [hwindowK.1]
        · apply le_trans hupper _
          apply mul_le_mul_of_nonneg_right _ (hwidthPos k).le
          linarith [hwindowK.2]
    have hsourceMeasure : sourceProbability (time k) ≤ targetProbability k := by
      change iidSequenceLaw ν
        {increment : ℕ → ℝ |
          sourceNormalizedStepCadlagPathIcc scale (time k) increment ∈ corridorUnion.toSet} ≤
        iidSequenceLaw ν
          (horizontalTubeEndpointWindowEvent a (width k) (time k - 1)
            (v₁ (width k)) (v₂ (width k)))
      exact measure_mono hsourceSubset
    have htargetSubset :
        horizontalTubeEndpointWindowEvent a (width k) (time k - 1)
          (v₁ (width k)) (v₂ (width k)) ⊆
        {increment | InHorizontalTube a (width k) (time k - 1) increment} := by
      intro increment h
      exact h.1
    have htargetMeasure : targetProbability k ≤ tubeProbability k := by
      change iidSequenceLaw ν
        (horizontalTubeEndpointWindowEvent a (width k) (time k - 1)
          (v₁ (width k)) (v₂ (width k))) ≤
        iidSequenceLaw ν
          {increment | InHorizontalTube a (width k) (time k - 1) increment}
      exact measure_mono htargetSubset
    have hsourceReal := ENNReal.toReal_mono (measure_ne_top _ _) hsourceMeasure
    have htargetPos : 0 < (targetProbability k).toReal :=
      lt_of_lt_of_le hsourcePos hsourceReal
    have htargetReal := ENNReal.toReal_mono (measure_ne_top _ _) htargetMeasure
    have htubePos : 0 < (tubeProbability k).toReal :=
      lt_of_lt_of_le htargetPos htargetReal
    have hlogLower : Real.log (sourceProbability (time k)).toReal ≤
        Real.log (targetProbability k).toReal :=
      Real.log_le_log hsourcePos hsourceReal
    have hlogUpper : Real.log (targetProbability k).toReal ≤
        Real.log (tubeProbability k).toReal :=
      Real.log_le_log htargetPos htargetReal
    have hfactor : 0 ≤ width k ^ 2 / ((time k - 1 : ℕ) : ℝ) :=
      div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    exact ⟨mul_le_mul_of_nonneg_left hlogLower hfactor,
      mul_le_mul_of_nonneg_left hlogUpper hfactor⟩
  have hrate : Tendsto
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
        Real.log (targetProbability k).toReal)
      atTop (𝓝 limit) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hsourceRatePred htubeRate ?_ ?_
    · filter_upwards [hlogSqueeze] with k hk
      exact hk.1
    · filter_upwards [hlogSqueeze] with k hk
      exact hk.2
  simpa [targetProbability, limit] using hrate

/-- Real-width form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii). For
$L_D/D^2\to\infty$ and endpoint windows containing a fixed interval
$[u,v]\subset(0,1)$ eventually, the logarithmic endpoint-window probability
has rate $-\pi^2\sigma^2/2$. The proof reduces a counterexample real-width
sequence to the sampled-width form above. The rate input is A. A. Mogul'skii,
“Small deviations in the sample function space,” Theorem 3, Section 4, p. 764
(1974); English translation, “Small Deviations in a Space of Trajectories,”
DOI 10.1137/1119081. -/
theorem centeredFiniteVariance_endpointWindowProbabilityRate_realWidth
    {L : ℝ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : Tendsto (fun D : ℝ => D ^ 2 / (L D : ℝ)) atTop (𝓝 0))
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a u v : ℝ} (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {v₁ v₂ : ℝ → ℝ}
    (hwindow : ∀ᶠ D : ℝ in atTop, v₁ D ≤ u ∧ v ≤ v₂ D) :
    Tendsto
      (fun D : ℝ => D ^ 2 / (L D : ℝ) * Real.log
        (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
          D (L D) (v₁ D) (v₂ D)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  apply tendsto_realWidthRate_of_sampledTime
    (rate := fun D n => D ^ 2 / (n : ℝ) * Real.log
      (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
        D n (v₁ D) (v₂ D)).toReal)
    (limit := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)) hL hquadratic
  intro time width htime htimePos hwidthPos hwidth hwidthSq
  have hwindowSample : ∀ᶠ k : ℕ in atTop,
      v₁ (width k) ≤ u ∧ v ≤ v₂ (width k) :=
    hwidth.eventually hwindow
  simpa using centeredFiniteVariance_endpointWindowProbabilityRate_realWidthAlong
    htime htimePos hwidthPos hwidth hwidthSq ha haOne hu huv hv
    hwindowSample hcentered hsquare hvariance

/-- Integer-width form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii). The endpoint
window eventually contains one fixed nonempty interval strictly inside the
tube, and the scale condition is `L Δ / Δ² → ∞`. The rate input is Mogul'skii,
Theorem 3, Section 4, p. 764, in “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081. -/
theorem centeredFiniteVariance_endpointWindowProbabilityRate
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : Asymptotics.IsSuperquadraticScale L)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a u v : ℝ} (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    {v₁ v₂ : ℕ → ℝ}
    (hwindow : ∀ᶠ Δ : ℕ in atTop, v₁ Δ ≤ u ∧ v ≤ v₂ Δ) :
    Tendsto
      (fun Δ : ℕ => (Δ : ℝ) ^ 2 / (L Δ : ℝ) * Real.log
        (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
          (Δ : ℝ) (L Δ) (v₁ Δ) (v₂ Δ)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let rate : ℕ → ℝ := fun Δ => (Δ : ℝ) ^ 2 / (L Δ : ℝ) * Real.log
    (horizontalTubeEndpointWindowProbability (iidSequenceLaw ν) a
      (Δ : ℝ) (L Δ) (v₁ Δ) (v₂ Δ)).toReal
  let c : ℝ := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hnot
  have hbad : ∀ N : ℕ, ∃ Δ > N, ε ≤ dist (rate Δ) c := by
    intro N
    by_contra hN
    apply hnot
    refine ⟨N + 1, ?_⟩
    intro Δ hΔ
    by_contra hdist
    apply hN
    refine ⟨Δ, lt_of_lt_of_le (Nat.lt_succ_self N) hΔ,
      le_of_not_gt hdist⟩
  obtain ⟨widthSeq, hwidthStrict, hwidthBad⟩ :=
    Nat.exists_strictMono_subsequence hbad
  let rawTime : ℕ → ℕ := fun k => L (widthSeq k) + 1
  have hLwidth : Tendsto (fun k => L (widthSeq k)) atTop atTop :=
    hL.comp hwidthStrict.tendsto_atTop
  have hrawTime : Tendsto rawTime atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hLwidth.eventually (eventually_ge_atTop b)] with k hk
    dsimp [rawTime]
    omega
  obtain ⟨φ, hφ, hφtime⟩ := strictMono_subseq_of_tendsto_atTop hrawTime
  let widthSub : ℕ → ℕ := fun k => widthSeq (φ k)
  let timeSub : ℕ → ℕ := fun k => rawTime (φ k)
  have htimeSub : StrictMono timeSub := by
    simpa [timeSub, rawTime, Function.comp_def] using hφtime
  have hwidthSubTop : Tendsto widthSub atTop atTop :=
    hwidthStrict.tendsto_atTop.comp hφ.tendsto_atTop
  have hwidthSubRealTop : Tendsto (fun k => (widthSub k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthSubTop
  have hwidthSqRaw : Tendsto
      (fun k => (widthSeq k : ℝ) ^ 2 / ((L (widthSeq k) : ℝ) + 1))
      atTop (𝓝 0) :=
    (Asymptotics.tendsto_width_sq_div_shiftedScale_of_superquadratic hquadratic).comp
      hwidthStrict.tendsto_atTop
  have hwidthSqSub : Tendsto
      (fun k => (widthSub k : ℝ) ^ 2 / (timeSub k : ℝ))
      atTop (𝓝 0) := by
    simpa [widthSub, timeSub, rawTime, Function.comp_def] using
      hwidthSqRaw.comp hφ.tendsto_atTop
  have hwindowSub : ∀ᶠ k : ℕ in atTop,
      v₁ (widthSub k) ≤ u ∧ v ≤ v₂ (widthSub k) :=
    hwidthSubTop.eventually hwindow
  have hrateSub :=
    centeredFiniteVariance_endpointWindowProbabilityRate_along
      htimeSub (fun k => by dsimp [timeSub, rawTime]; omega)
      hwidthSubRealTop hwidthSqSub ha haOne hu huv hv hwindowSub
      hcentered hsquare hvariance
  have hrateOnWidths : Tendsto (fun k => rate (widthSub k)) atTop (𝓝 c) := by
    simpa [rate, widthSub, timeSub, rawTime, Function.comp_def,
      Nat.add_sub_cancel_right] using hrateSub
  have hclose : ∀ᶠ k : ℕ in atTop, dist (rate (widthSub k)) c < ε :=
    hrateOnWidths.eventually (Metric.ball_mem_nhds c hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hclose
  have hlt := hN N le_rfl
  have hge : ε ≤ dist (rate (widthSub N)) c := hwidthBad (φ N)
  exact (not_lt_of_ge hge) hlt

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
