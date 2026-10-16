/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.InverseScale
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Normal.ContinuousBoundary
/-!
# Closed horizontal-tube rates from continuous-boundary rates

For a law `ν` of mean zero and variance \(\sigma^2\in(0,\infty)\), write
\[
  T_{a,\Delta,L}:=
  \left\{\omega:\ -a\Delta\le S_j(\omega)\le(1-a)\Delta
    \text{ for }1\le j\le L\right\}.
\]

The public declarations are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.horizontalTubeEndpointWindowEvent`:
  the event $T_{a,\Delta,L}\cap\{(u-a)\Delta\le S_L\le(v-a)\Delta\}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.horizontalTubeEndpointWindowProbability`:
  the probability of this event under the specified increment law.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_closedHorizontalTubeProbabilityRate`:
  if $x_n\to\infty$ and $x_n^2/n\to0$, then the closed-tube logarithmic rate is $-\pi^2\sigma^2/2$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_closedHorizontalTubeProbabilityRate_along`:
  the same rate along strictly increasing time indices and sampled widths.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidthAlong`:
  the same sampled rate for positive real widths.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidth`:
  the full real-width rate for integer horizons $L_D$ with $D^2/L_D\to0$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredUnitVariance_closedHorizontalTubeProbabilityRate`:
  the unit-variance specialization of the closed-tube rate.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.inverseScale_closedHorizontalTubeProbabilityRate`:
  the rate for the generalized inverse of a superquadratic time scale.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.upperInverseScale_closedHorizontalTubeProbabilityRate`:
  the corresponding rate for its upper inverse.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.inverseScales_closedHorizontalTubeProbabilityRate`:
  the conjunction of both inverse-scale rates.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_horizontalTubeProbabilityRate`:
  the rate when integer widths index a superquadratic horizon.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate_along`:
  the endpoint-window rate along sampled integer widths when the scaled terminal window contains a fixed interior interval.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate_realWidthAlong`:
  the endpoint-window rate along sampled positive real widths.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate_realWidth`:
  the real-width endpoint-window rate for a width-indexed integer horizon.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_endpointWindowProbabilityRate`:
  the endpoint-window rate when integer widths index a superquadratic horizon.
This module transfers the source-path rate for strict continuous corridors to
closed horizontal tubes. The squeeze uses inward and outward constant
boundaries, as in the proof of Lemma 3.1(i) in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3. The rate
input is Theorem 3, Section 4, p. 764 of A. A. Mogul'skii, “Small deviations
in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4)
(1974), 755–765; English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975),
726–736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

private def constantBoundary (value : ℝ) : C(unitInterval, ℝ) :=
  ContinuousMap.const unitInterval value

private def sourceRelativeConstantCorridorEvent (scale : ℕ → ℝ) (n : ℕ)
    (lower upper : ℝ) : Set (ℕ → ℝ) :=
  {increment | sourceNormalizedStepCadlagPathIcc scale n increment ∈
    relativeContinuousBoundaryCorridorSet
      (constantBoundary lower) (constantBoundary upper)}

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

private theorem terminalJumpEndpointCorridor_energy (a u v : ℝ)
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

private theorem terminalJumpEndpointCorridorUnion_toSet (a u v : ℝ)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    (terminalJumpEndpointCorridorUnion a u v ha haOne hu huv hv).toSet =
      (terminalJumpEndpointCorridor a u v ha haOne hu huv hv).toSet := by
  ext path
  simp [terminalJumpEndpointCorridorUnion, FiniteCorridorUnion.toSet]

private theorem terminalJumpEndpointCorridorUnion_realEnergy (a u v : ℝ)
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

private theorem sourceTerminalJumpCorridor_subset_endpointWindow
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

private theorem normalizedSourcePartialSum_bounds_of_horizontalTube
    {n : ℕ} {scale : ℕ → ℝ} {a : ℝ} {increment : ℕ → ℝ}
    (hscale : 0 < scale n) (_ha0 : 0 ≤ a) (_ha1 : a ≤ 1)
    (htube : InHorizontalTube a (scale n) (n - 1) increment)
    (k : Fin n) :
    -a ≤ (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ∧
      (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ≤ 1 - a := by
  by_cases hk : k.val = 0
  · simp [hk, AdditivePath.displacement_zero]
    exact ⟨by linarith, by linarith⟩
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
    let i : Fin (n - 1) := ⟨k.val - 1, by omega⟩
    have hi := htube i
    have hindex : i.val + 1 = k.val := by simp [i]; omega
    have hlow : -a ≤ AdditivePath.displacement (k : ℕ) increment / scale n := by
      apply (le_div_iff₀ hscale).2
      simpa [hindex] using hi.1
    have hhigh : AdditivePath.displacement (k : ℕ) increment / scale n ≤ 1 - a := by
      apply (div_le_iff₀ hscale).2
      simpa [hindex] using hi.2
    have hdiv : (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment =
        AdditivePath.displacement (k : ℕ) increment / scale n := by
      rw [div_eq_mul_inv]
      ring
    rw [hdiv]
    exact ⟨hlow, hhigh⟩

/-- A strict constant source corridor whose boundaries lie inside a closed
horizontal tube forces the source walk to stay in that tube. -/
private theorem sourceRelativeConstantCorridor_subset_horizontalTube
    {n : ℕ} {scale : ℕ → ℝ} {a lower upper : ℝ}
    (hn : 0 < n) (hscale : 0 < scale n)
    (hlower : -a < lower) (hupper : upper < 1 - a) :
    sourceRelativeConstantCorridorEvent scale n lower upper ⊆
      {increment | InHorizontalTube a (scale n) (n - 1) increment} := by
  intro increment hcorridor
  change sourceNormalizedStepCadlagPathIcc scale n increment ∈
      Skorokhod.terminalLeftPathSpace ∧
    sourceNormalizedStepCadlagPathIcc scale n increment ∈
      continuousBoundaryCorridorSet (constantBoundary lower) (constantBoundary upper)
    at hcorridor
  rcases hcorridor.2 with ⟨_, hbetween⟩
  have hrange := sourceNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement
    scale hn increment
  intro i
  let k : Fin n := ⟨i.val + 1, by omega⟩
  have hvalue : (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ∈
      Set.range (sourceNormalizedStepCadlagPathIcc scale n increment) := by
    have hfinite : (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ∈
        Set.range (fun j : Fin n =>
          (scale n)⁻¹ * AdditivePath.displacement (j : ℕ) increment) :=
      ⟨k, rfl⟩
    exact hrange.symm ▸ hfinite
  obtain ⟨t, ht⟩ := hvalue
  have hbounds := hbetween t
  rw [ht, constantBoundary, ContinuousMap.const_apply] at hbounds
  have hlow : -a ≤ (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment :=
    le_of_lt (lt_trans hlower hbounds.1)
  have hhigh : (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ≤ 1 - a :=
    le_of_lt (lt_trans hbounds.2 hupper)
  have hlow' : -a * scale n ≤ AdditivePath.displacement (k : ℕ) increment := by
    apply (le_div_iff₀ hscale).1
    simpa [div_eq_mul_inv, mul_comm] using hlow
  have hhigh' : AdditivePath.displacement (k : ℕ) increment ≤
      (1 - a) * scale n := by
    apply (div_le_iff₀ hscale).1
    simpa [div_eq_mul_inv, mul_comm] using hhigh
  simpa [InHorizontalTube, k] using And.intro hlow' hhigh'

/-- A closed horizontal tube lies inside any strictly wider constant source
corridor, including the source path's terminal-left endpoint. -/
private theorem horizontalTube_subset_sourceRelativeConstantCorridor
    {n : ℕ} {scale : ℕ → ℝ} {a lower upper : ℝ}
    (hn : 0 < n) (hscale : 0 < scale n) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hlower : lower < -a) (hupper : 1 - a < upper) :
    {increment | InHorizontalTube a (scale n) (n - 1) increment} ⊆
      sourceRelativeConstantCorridorEvent scale n lower upper := by
  intro increment htube
  let path := sourceNormalizedStepCadlagPathIcc scale n increment
  have hzero : path ⊥ = 0 := by
    have hbot : (⊥ : unitInterval) ≠ ⊤ := by norm_num [unitInterval]
    rw [show path = sourceNormalizedStepCadlagPathIcc scale n increment by rfl,
      sourceNormalizedStepCadlagPathIcc_apply_of_ne_top scale n increment hbot]
    simp [normalizedStepPath, AdditivePath.displacement_zero]
  have hrange := sourceNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement
    scale hn increment
  have hnormalized (k : Fin n) :
      -a ≤ (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ∧
        (scale n)⁻¹ * AdditivePath.displacement (k : ℕ) increment ≤ 1 - a :=
    normalizedSourcePartialSum_bounds_of_horizontalTube hscale ha0 ha1 htube k
  refine ⟨Skorokhod.terminalLeftPath_mem_space
    (normalizedStepCadlagPathIcc scale n increment), ?_⟩
  change path ⊥ = 0 ∧ ∀ t : unitInterval,
    lower < path t ∧ path t < upper
  refine ⟨hzero, ?_⟩
  intro t
  have hvalue : path t ∈ Set.range path := ⟨t, rfl⟩
  rw [hrange] at hvalue
  obtain ⟨k, hk⟩ := hvalue
  have hbounds := hnormalized k
  have hboundsPath : -a ≤ path t ∧ path t ≤ 1 - a := by
    simpa only [← hk] using hbounds
  exact ⟨lt_of_lt_of_le hlower hboundsPath.1,
    lt_of_le_of_lt hboundsPath.2 hupper⟩

/-- Finite-variance form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i). Its rate input
is A. A. Mogul'skii, Theorem 3, Section 4, p. 764, in “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081. The time horizon is `n - 1`, matching the terminal-left
source path. -/
theorem centeredFiniteVariance_closedHorizontalTubeProbabilityRate
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (scale n) (n - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let room : ℝ := min a (1 - a) / 4
  let ε : ℕ → ℝ := fun m => room / ((m : ℝ) + 1)
  let c : ℝ := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)
  let innerRate : ℕ → ℝ := fun m => c * ((1 - 2 * ε m) ^ 2)⁻¹
  let outerRate : ℕ → ℝ := fun m => c * ((1 + 2 * ε m) ^ 2)⁻¹
  have hroom : 0 < room := by
    dsimp [room]
    exact div_pos (lt_min ha (sub_pos.mpr haOne)) (by norm_num)
  have hεpos (m : ℕ) : 0 < ε m := by
    dsimp [ε]
    positivity
  have hεa (m : ℕ) : ε m < a := by
    have hle : ε m ≤ room := by
      dsimp [ε]
      have hden : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        exact_mod_cast (show 1 ≤ m + 1 by omega)
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hroom, hden])
    have hroomA : room < a := by
      dsimp [room]
      nlinarith [min_le_left a (1 - a), hroom]
    exact lt_of_le_of_lt hle hroomA
  have hεone (m : ℕ) : ε m < 1 - a := by
    have hle : ε m ≤ room := by
      dsimp [ε]
      have hden : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        exact_mod_cast (show 1 ≤ m + 1 by omega)
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hroom, hden])
    have hroomOne : room < 1 - a := by
      dsimp [room]
      nlinarith [min_le_right a (1 - a), hroom]
    exact lt_of_le_of_lt hle hroomOne
  have hεlimit : Tendsto ε atTop (𝓝 0) := by
    have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hroom : Tendsto (fun _ : ℕ => room) atTop (𝓝 room) := tendsto_const_nhds
    have hmul := hroom.mul hbase
    simpa [ε, room, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hinnerRateLimit : Tendsto innerRate atTop (𝓝 c) := by
    have hwidth : Tendsto (fun m : ℕ => 1 - 2 * ε m) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hεlimit)
    have hwidthSq : Tendsto (fun m : ℕ => (1 - 2 * ε m) ^ 2)
        atTop (𝓝 (1 : ℝ)) := by simpa using hwidth.pow 2
    have hinv := hwidthSq.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    have hmul := hconst.mul hinv
    simpa [innerRate] using hmul
  have houterRateLimit : Tendsto outerRate atTop (𝓝 c) := by
    have hwidth : Tendsto (fun m : ℕ => 1 + 2 * ε m) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hεlimit)
    have hwidthSq : Tendsto (fun m : ℕ => (1 + 2 * ε m) ^ 2)
        atTop (𝓝 (1 : ℝ)) := by simpa using hwidth.pow 2
    have hinv := hwidthSq.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    have hmul := hconst.mul hinv
    simpa [outerRate] using hmul
  let tubeProbability : ℕ → ℝ≥0∞ := fun n =>
    horizontalTubeProbability (iidSequenceLaw ν) a (scale n) (n - 1)
  let tubeRate : ℕ → ℝ := fun n =>
    (scale n) ^ 2 / (n : ℝ) * Real.log (tubeProbability n).toReal
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n :=
    hsmall.eventually_pos
  have hnPos : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hvalid : ∀ᶠ n : ℕ in atTop, 0 < n ∧ 0 < scale n :=
    hnPos.and hscalePos
  let hbaseSet : ℝ → ℝ → ℕ → Set (ℕ → ℝ) := fun lower upper n =>
    sourceRelativeConstantCorridorEvent scale n lower upper
  have hinnerBoundaryData (m : ℕ) :=
    centeredFiniteVariance_sourceRelativeContinuousBoundaryProbabilityRate
      hsmall hcentered hsquare hvariance
      (constantBoundary (-a + ε m)) (constantBoundary (1 - a - ε m))
      (by
        intro t
        simp only [constantBoundary, ContinuousMap.const_apply]
        linarith [hεa m, hεone m])
      (by
        simp only [constantBoundary, ContinuousMap.const_apply]
        linarith [hεa m])
      (by
        simp only [constantBoundary, ContinuousMap.const_apply]
        linarith [hεone m])
  have houterBoundaryData (m : ℕ) :=
    centeredFiniteVariance_sourceRelativeContinuousBoundaryProbabilityRate
      hsmall hcentered hsquare hvariance
      (constantBoundary (-a - ε m)) (constantBoundary (1 - a + ε m))
      (by
        intro t
        simp only [constantBoundary, ContinuousMap.const_apply]
        nlinarith [hεpos m])
      (by
        simp only [constantBoundary, ContinuousMap.const_apply]
        nlinarith [ha, hεpos m])
      (by
        simp only [constantBoundary, ContinuousMap.const_apply]
        nlinarith [haOne, hεpos m])
  have hinnerPositive (m : ℕ) : ∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n)).toReal := by
    have hinnerBoundaryRate := hinnerBoundaryData m
    simpa [hbaseSet, sourceRelativeConstantCorridorEvent, constantBoundary] using
      hinnerBoundaryRate.1
  have houterPositive (m : ℕ) : ∀ᶠ n : ℕ in atTop,
      0 < (iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)).toReal := by
    have houterBoundaryRate := houterBoundaryData m
    simpa [hbaseSet, sourceRelativeConstantCorridorEvent, constantBoundary] using
      houterBoundaryRate.1
  have hinnerRate (m : ℕ) :
      Tendsto (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        (iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n)).toReal)
        atTop (𝓝 (innerRate m)) := by
    have hboundaryRate := hinnerBoundaryData m
    have hdensity : continuousBoundaryDensity 2
        (constantBoundary (-a + ε m)) (constantBoundary (1 - a - ε m)) =
          fun _ => (1 - 2 * ε m) ^ (-2 : ℝ) := by
      funext t
      simp only [continuousBoundaryDensity, constantBoundary,
        ContinuousMap.const_apply]
      congr 1
      ring
    have henergy :
        ∫ t : unitInterval, continuousBoundaryDensity 2
          (constantBoundary (-a + ε m))
          (constantBoundary (1 - a - ε m)) t ∂volume =
          (1 - 2 * ε m) ^ (-2 : ℝ) := by
      rw [hdensity]
      simp
    have hwidthPos : 0 < 1 - 2 * ε m := by
      linarith [hεa m, hεone m]
    have henergyInv :
        ∫ t : unitInterval, continuousBoundaryDensity 2
          (constantBoundary (-a + ε m))
          (constantBoundary (1 - a - ε m)) t ∂volume =
          ((1 - 2 * ε m) ^ 2)⁻¹ := by
      rw [henergy, Real.rpow_neg hwidthPos.le]
      exact congrArg (fun z : ℝ => z⁻¹)
        (Real.rpow_natCast (1 - 2 * ε m) 2)
    have hrateConstant : -(Real.pi ^ 2) / 2 * (∫ x : ℝ, x ^ 2 ∂ν) *
        ((1 - 2 * ε m) ^ 2)⁻¹ =
        innerRate m := by
      dsimp [innerRate, c]
    have hboundaryRate' := hboundaryRate.2
    rw [henergyInv, hrateConstant] at hboundaryRate'
    simpa [hbaseSet, sourceRelativeConstantCorridorEvent, constantBoundary,
      innerRate, c] using hboundaryRate'
  have houterRate (m : ℕ) :
      Tendsto (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        (iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)).toReal)
        atTop (𝓝 (outerRate m)) := by
    have hboundaryRate := houterBoundaryData m
    have hdensity : continuousBoundaryDensity 2
        (constantBoundary (-a - ε m)) (constantBoundary (1 - a + ε m)) =
          fun _ => (1 + 2 * ε m) ^ (-2 : ℝ) := by
      funext t
      simp only [continuousBoundaryDensity, constantBoundary,
        ContinuousMap.const_apply]
      congr 1
      ring
    have henergy :
        ∫ t : unitInterval, continuousBoundaryDensity 2
          (constantBoundary (-a - ε m))
          (constantBoundary (1 - a + ε m)) t ∂volume =
          (1 + 2 * ε m) ^ (-2 : ℝ) := by
      rw [hdensity]
      simp
    have hwidthPos : 0 < 1 + 2 * ε m := by positivity
    have henergyInv :
        ∫ t : unitInterval, continuousBoundaryDensity 2
          (constantBoundary (-a - ε m))
          (constantBoundary (1 - a + ε m)) t ∂volume =
          ((1 + 2 * ε m) ^ 2)⁻¹ := by
      rw [henergy, Real.rpow_neg hwidthPos.le]
      exact congrArg (fun z : ℝ => z⁻¹)
        (Real.rpow_natCast (1 + 2 * ε m) 2)
    have hrateConstant : -(Real.pi ^ 2) / 2 * (∫ x : ℝ, x ^ 2 ∂ν) *
        ((1 + 2 * ε m) ^ 2)⁻¹ =
        outerRate m := by
      dsimp [outerRate, c]
    have hboundaryRate' := hboundaryRate.2
    rw [henergyInv, hrateConstant] at hboundaryRate'
    simpa [hbaseSet, sourceRelativeConstantCorridorEvent, constantBoundary,
      outerRate, c] using hboundaryRate'
  have hinnerEvent (m n : ℕ) (hn : 0 < n) (hs : 0 < scale n) :
      hbaseSet (-a + ε m) (1 - a - ε m) n ⊆
        {increment | InHorizontalTube a (scale n) (n - 1) increment} := by
    simpa [hbaseSet] using
      (sourceRelativeConstantCorridor_subset_horizontalTube hn hs
        (by linarith [hεpos m]) (by linarith [hεpos m]))
  have houterEvent (m n : ℕ) (hn : 0 < n) (hs : 0 < scale n) :
      {increment | InHorizontalTube a (scale n) (n - 1) increment} ⊆
        hbaseSet (-a - ε m) (1 - a + ε m) n := by
    simpa [hbaseSet] using
      (horizontalTube_subset_sourceRelativeConstantCorridor hn hs ha.le haOne.le
        (by linarith [hεpos m]) (by linarith [hεpos m]))
  have hTubePositive : ∀ᶠ n : ℕ in atTop, 0 < (tubeProbability n).toReal := by
    filter_upwards [hvalid, hinnerPositive 0] with n hn hinner
    have hmeasure : iidSequenceLaw ν
        (hbaseSet (-a + ε 0) (1 - a - ε 0) n) ≤ tubeProbability n := by
      change iidSequenceLaw ν (hbaseSet (-a + ε 0) (1 - a - ε 0) n) ≤
        iidSequenceLaw ν {increment |
          InHorizontalTube a (scale n) (n - 1) increment}
      exact measure_mono (hinnerEvent 0 n hn.1 hn.2)
    have hreal := ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
    exact lt_of_lt_of_le hinner hreal
  have hlogSqueeze (m : ℕ) : ∀ᶠ n : ℕ in atTop,
      (scale n) ^ 2 / (n : ℝ) * Real.log
          (iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n)).toReal ≤
        tubeRate n ∧
      tubeRate n ≤ (scale n) ^ 2 / (n : ℝ) * Real.log
          (iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)).toReal := by
    filter_upwards [hvalid, hinnerPositive m, houterPositive m, hTubePositive]
      with n hn hinner houter htube
    have hinnerMeasure : iidSequenceLaw ν
        (hbaseSet (-a + ε m) (1 - a - ε m) n) ≤ tubeProbability n := by
      change iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n) ≤
        iidSequenceLaw ν {increment |
          InHorizontalTube a (scale n) (n - 1) increment}
      exact measure_mono (hinnerEvent m n hn.1 hn.2)
    have houterMeasure : tubeProbability n ≤ iidSequenceLaw ν
        (hbaseSet (-a - ε m) (1 - a + ε m) n) := by
      change iidSequenceLaw ν {increment |
          InHorizontalTube a (scale n) (n - 1) increment} ≤
        iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)
      exact measure_mono (houterEvent m n hn.1 hn.2)
    have hinnerReal := ENNReal.toReal_mono (measure_ne_top _ _) hinnerMeasure
    have houterReal := ENNReal.toReal_mono (measure_ne_top _ _) houterMeasure
    have hlogInner : Real.log
        (iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n)).toReal ≤
          Real.log (tubeProbability n).toReal :=
      Real.log_le_log hinner hinnerReal
    have hlogOuter : Real.log (tubeProbability n).toReal ≤
        Real.log (iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)).toReal :=
      Real.log_le_log htube houterReal
    have hfactor : 0 ≤ (scale n) ^ 2 / (n : ℝ) := by positivity
    exact ⟨mul_le_mul_of_nonneg_left hlogInner hfactor,
      mul_le_mul_of_nonneg_left hlogOuter hfactor⟩
  have hrateLimit : Tendsto tubeRate atTop (𝓝 c) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    let η : ℝ := δ / 4
    have hη : 0 < η := by dsimp [η]; positivity
    have hrateNear : ∀ᶠ m : ℕ in atTop,
        |innerRate m - c| < η ∧ |outerRate m - c| < η := by
      filter_upwards [
        hinnerRateLimit.eventually (Metric.ball_mem_nhds c hη),
        houterRateLimit.eventually (Metric.ball_mem_nhds c hη)] with m hmI hmO
      exact ⟨by simpa [Metric.mem_ball, Real.dist_eq] using hmI,
        by simpa [Metric.mem_ball, Real.dist_eq] using hmO⟩
    obtain ⟨m, hmRates⟩ := hrateNear.exists
    have hinnerNear : ∀ᶠ n : ℕ in atTop,
        |((scale n) ^ 2 / (n : ℝ) * Real.log
          (iidSequenceLaw ν (hbaseSet (-a + ε m) (1 - a - ε m) n)).toReal) -
            innerRate m| < η := by
      filter_upwards [
        hinnerRate m |>.eventually (Metric.ball_mem_nhds (innerRate m) hη)]
        with n hn
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    have houterNear : ∀ᶠ n : ℕ in atTop,
        |((scale n) ^ 2 / (n : ℝ) * Real.log
          (iidSequenceLaw ν (hbaseSet (-a - ε m) (1 - a + ε m) n)).toReal) -
            outerRate m| < η := by
      filter_upwards [
        houterRate m |>.eventually (Metric.ball_mem_nhds (outerRate m) hη)]
        with n hn
      simpa [Metric.mem_ball, Real.dist_eq] using hn
    filter_upwards [hinnerNear, houterNear, hlogSqueeze m] with n hi ho hsqueeze
    have hi' := abs_lt.mp hi
    have ho' := abs_lt.mp ho
    have hmI := abs_lt.mp hmRates.1
    have hmO := abs_lt.mp hmRates.2
    have hbounds : c - δ < tubeRate n ∧ tubeRate n < c + δ := by
      constructor
      · linarith [hi'.1, hmI.1, hsqueeze.1, show 4 * η = δ by dsimp [η]; ring]
      · linarith [ho'.2, hmO.2, hsqueeze.2, show 4 * η = δ by dsimp [η]; ring]
    have hdist : -δ < tubeRate n - c ∧ tubeRate n - c < δ := by
      constructor <;> linarith [hbounds.1, hbounds.2]
    have hdist' : |tubeRate n - c| < δ := abs_lt.mpr hdist
    simpa [Metric.mem_ball, Real.dist_eq] using hdist'
  simpa [tubeRate, tubeProbability] using hrateLimit

private theorem exists_later_time_index {time : ℕ → ℕ}
    (htime : StrictMono time) (n : ℕ) : ∃ k, n < time (k + 1) := by
  obtain ⟨k, hk⟩ := (htime.tendsto_atTop.eventually_gt_atTop n).exists
  exact ⟨k, lt_of_lt_of_le hk (Nat.le_of_lt (htime (Nat.lt_succ_self k)))⟩

/-- The index of the half-open time interval `[time k, time (k + 1))`
containing `n`. -/
private noncomputable def increasingTimeIntervalIndex (time : ℕ → ℕ)
    (htime : StrictMono time) (n : ℕ) : ℕ :=
  Nat.find (exists_later_time_index htime n)

private theorem increasingTimeIntervalIndex_spec {time : ℕ → ℕ}
    (htime : StrictMono time) (n : ℕ) :
    n < time (increasingTimeIntervalIndex time htime n + 1) :=
  Nat.find_spec (exists_later_time_index htime n)

private theorem increasingTimeIntervalIndex_le_of_mem {time : ℕ → ℕ}
    (htime : StrictMono time) (n k : ℕ) (hnk : n < time (k + 1)) :
    increasingTimeIntervalIndex time htime n ≤ k :=
  Nat.find_min' ⟨k, hnk⟩ hnk

private theorem increasingTimeIntervalIndex_lower_bound {time : ℕ → ℕ}
    (htime : StrictMono time) {n : ℕ} (hstart : time 0 ≤ n) :
    time (increasingTimeIntervalIndex time htime n) ≤ n := by
  by_contra hnot
  have hlt : n < time (increasingTimeIntervalIndex time htime n) := Nat.lt_of_not_ge hnot
  by_cases hzero : increasingTimeIntervalIndex time htime n = 0
  · rw [hzero] at hlt
    exact (not_lt_of_ge hstart) hlt
  · have hindexPos : 0 < increasingTimeIntervalIndex time htime n :=
      Nat.pos_of_ne_zero hzero
    let k := increasingTimeIntervalIndex time htime n - 1
    have hk : k + 1 = increasingTimeIntervalIndex time htime n := by
      dsimp [k]
      omega
    have hmin := increasingTimeIntervalIndex_le_of_mem htime n k (by simpa [hk] using hlt)
    omega

private theorem increasingTimeIntervalIndex_tendsto {time : ℕ → ℕ}
    (htime : StrictMono time) :
    Tendsto (increasingTimeIntervalIndex time htime) atTop atTop := by
  rw [tendsto_atTop]
  intro k
  filter_upwards [eventually_ge_atTop (time k)] with n hn
  by_contra hnot
  have hindex : increasingTimeIntervalIndex time htime n < k := Nat.lt_of_not_ge hnot
  have hindexTime : time (increasingTimeIntervalIndex time htime n + 1) ≤ time k :=
    htime.monotone (by omega)
  have hspec := increasingTimeIntervalIndex_spec htime n
  omega

private theorem increasingTimeIntervalIndex_at_time {time : ℕ → ℕ}
    (htime : StrictMono time) (k : ℕ) :
    increasingTimeIntervalIndex time htime (time k) = k := by
  apply le_antisymm
  · exact increasingTimeIntervalIndex_le_of_mem htime (time k) k
      (htime (Nat.lt_succ_self k))
  · by_contra hnot
    have hindex : increasingTimeIntervalIndex time htime (time k) < k :=
      Nat.lt_of_not_ge hnot
    have hindexTime : time (increasingTimeIntervalIndex time htime (time k) + 1) ≤ time k :=
      htime.monotone (by omega)
    have hspec := increasingTimeIntervalIndex_spec htime (time k)
    omega

private noncomputable def increasingTimeAuxiliaryScale (time width : ℕ → ℕ)
    (htime : StrictMono time) : ℕ → ℝ := fun n =>
  (width (increasingTimeIntervalIndex time htime n) : ℝ)

private theorem increasingTimeAuxiliaryScale_isSmallDeviationScale
    {time width : ℕ → ℕ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k)
    (hwidth : Tendsto (fun k : ℕ => (width k : ℝ)) atTop atTop)
    (hwidthSq : Tendsto (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ))
      atTop (𝓝 0)) :
    Asymptotics.IsSmallDeviationScale
      (increasingTimeAuxiliaryScale time width htime)
      (fun n => Real.sqrt (n : ℝ)) := by
  have hindex := increasingTimeIntervalIndex_tendsto htime
  have hscaleTop : Tendsto (increasingTimeAuxiliaryScale time width htime) atTop atTop :=
    hwidth.comp hindex
  have hwidthSqComp := hwidthSq.comp hindex
  have hscaleSqNonneg (n : ℕ) :
      0 ≤ (increasingTimeAuxiliaryScale time width htime n) ^ 2 / (n : ℝ) :=
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hscaleSqUpper :
      (fun n : ℕ => (increasingTimeAuxiliaryScale time width htime n) ^ 2 / (n : ℝ)) ≤ᶠ[atTop]
        (fun n => (width (increasingTimeIntervalIndex time htime n) : ℝ) ^ 2 /
          (time (increasingTimeIntervalIndex time htime n) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (time 0)] with n hn
    let k := increasingTimeIntervalIndex time htime n
    have hkn := increasingTimeIntervalIndex_lower_bound htime hn
    have hkpos : 0 < (time k : ℝ) := by exact_mod_cast htimePos k
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (htimePos 0) hn)
    have hdenom : (time k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hnum : 0 ≤ (width k : ℝ) ^ 2 := sq_nonneg _
    have hcross : (width k : ℝ) ^ 2 * (time k : ℝ) ≤
        (width k : ℝ) ^ 2 * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hdenom hnum
    have hdiv : (width k : ℝ) ^ 2 / (n : ℝ) ≤
        (width k : ℝ) ^ 2 / (time k : ℝ) :=
      (div_le_div_iff₀ hnpos hkpos).2 (by simpa [mul_comm] using hcross)
    simpa [k, increasingTimeAuxiliaryScale] using hdiv
  have hscaleSq : Tendsto
      (fun n : ℕ => (increasingTimeAuxiliaryScale time width htime n) ^ 2 / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hwidthSqComp
      (Filter.Eventually.of_forall hscaleSqNonneg) hscaleSqUpper
  have hscaleRatio := Asymptotics.tendsto_div_sqrt_atTop_zero_of_tendsto_sq_div_atTop_zero
    (fun n => Nat.cast_nonneg (width (increasingTimeIntervalIndex time htime n))) hscaleSq
  exact Asymptotics.IsSmallDeviationScale.of_tendsto hscaleTop hscaleRatio

/-- Sampling consequence of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i), under its
width-time relation. The sampled statement follows from the real-width rate
proved above. Its rate input is A. A. Mogul'skii, “Small deviations in the
sample function space,” Theorem 3, Section 4, p. 764 (1974); English
translation, “Small Deviations in a Space of Trajectories,” DOI 10.1137/1119081. -/
theorem centeredFiniteVariance_closedHorizontalTubeProbabilityRate_along
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {time width : ℕ → ℕ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k)
    (hwidth : Tendsto (fun k : ℕ => (width k : ℝ)) atTop atTop)
    (hwidthSq : Tendsto (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ))
      atTop (𝓝 0))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let scale := increasingTimeAuxiliaryScale time width htime
  have hsmall := increasingTimeAuxiliaryScale_isSmallDeviationScale
    htime htimePos hwidth hwidthSq
  have hrate := (centeredFiniteVariance_closedHorizontalTubeProbabilityRate
    hsmall hcentered hsquare hvariance ha haOne).comp htime.tendsto_atTop
  have hscaleEq : ∀ k : ℕ, scale (time k) = (width k : ℝ) := by
    intro k
    simp [scale, increasingTimeAuxiliaryScale, increasingTimeIntervalIndex_at_time htime]
  have hsourceRate : Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
    have heq : (fun k : ℕ => scale (time k) ^ 2 / (time k : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (scale (time k)) (time k - 1)).toReal) =
        (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ) * Real.log
          (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal) := by
      funext k
      rw [hscaleEq]
    have heq' : (fun k : ℕ => scale (time k) ^ 2 / (time k : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (scale (time k)) (time k - 1)).toReal) =ᶠ[atTop]
        (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ) * Real.log
          (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal) := by
      filter_upwards with k
      exact congrFun heq k
    simpa only [Function.comp_def] using hrate.congr' heq'
  have hratioNat : Tendsto (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    have hratioBase : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1))
        atTop (𝓝 (1 : ℝ)) := by
      simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
    have hratioEq : (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) =ᶠ[atTop]
        fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn1 : 1 ≤ n := by omega
      simp [Nat.cast_sub hn1]
    exact hratioBase.congr' hratioEq.symm
  have hfactor := hratioNat.comp htime.tendsto_atTop
  have hproduct := hfactor.mul hsourceRate
  have hproductEq : (fun k : ℕ =>
      ((time k : ℝ) / ((time k - 1 : ℕ) : ℝ)) *
        ((width k : ℝ) ^ 2 / (time k : ℝ) * Real.log
          (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal)) =ᶠ[atTop]
      (fun k : ℕ => (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with k hk
    have htimeNe : (time k : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (htimePos k))
    have hpredNat : 0 < time k - 1 := by
      have hk' : 1 < k := by omega
      have htimeStep : time 1 < time k := htime hk'
      have htimeOne : 0 < time 1 := htimePos 1
      omega
    have hpredPos : 0 < ((time k - 1 : ℕ) : ℝ) := by exact_mod_cast hpredNat
    have hpredNe : ((time k - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hpredPos
    field_simp [htimeNe, hpredNe]
  simpa only [one_mul] using hproduct.congr' hproductEq

private noncomputable def increasingTimeRealAuxiliaryScale
    (time : ℕ → ℕ) (width : ℕ → ℝ) (htime : StrictMono time) : ℕ → ℝ :=
  fun n => width (increasingTimeIntervalIndex time htime n)

private theorem increasingTimeRealAuxiliaryScale_isSmallDeviationScale
    {time : ℕ → ℕ} {width : ℕ → ℝ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k) (hwidthPos : ∀ k, 0 < width k)
    (hwidth : Tendsto width atTop atTop)
    (hwidthSq : Tendsto (fun k => width k ^ 2 / (time k : ℝ))
      atTop (𝓝 0)) :
    Asymptotics.IsSmallDeviationScale
      (increasingTimeRealAuxiliaryScale time width htime)
      (fun n => Real.sqrt (n : ℝ)) := by
  have hindex := increasingTimeIntervalIndex_tendsto htime
  have hscaleTop : Tendsto
      (increasingTimeRealAuxiliaryScale time width htime) atTop atTop :=
    hwidth.comp hindex
  have hwidthSqComp := hwidthSq.comp hindex
  have hscaleSqNonneg (n : ℕ) :
      0 ≤ (increasingTimeRealAuxiliaryScale time width htime n) ^ 2 /
        (n : ℝ) := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hscaleSqUpper :
      (fun n : ℕ =>
        (increasingTimeRealAuxiliaryScale time width htime n) ^ 2 / (n : ℝ)) ≤ᶠ[atTop]
        (fun n => width (increasingTimeIntervalIndex time htime n) ^ 2 /
          (time (increasingTimeIntervalIndex time htime n) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (time 0)] with n hn
    let k := increasingTimeIntervalIndex time htime n
    have hkn := increasingTimeIntervalIndex_lower_bound htime hn
    have hkpos : 0 < (time k : ℝ) := by exact_mod_cast htimePos k
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (htimePos 0) hn)
    have hdenom : (time k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hnum : 0 ≤ width k ^ 2 := sq_nonneg _
    have hcross : width k ^ 2 * (time k : ℝ) ≤
        width k ^ 2 * (n : ℝ) := mul_le_mul_of_nonneg_left hdenom hnum
    have hdiv : width k ^ 2 / (n : ℝ) ≤ width k ^ 2 / (time k : ℝ) :=
      (div_le_div_iff₀ hnpos hkpos).2 (by simpa [mul_comm] using hcross)
    simpa [k, increasingTimeRealAuxiliaryScale] using hdiv
  have hscaleSq : Tendsto
      (fun n : ℕ =>
        (increasingTimeRealAuxiliaryScale time width htime n) ^ 2 / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hwidthSqComp
      (Filter.Eventually.of_forall hscaleSqNonneg) hscaleSqUpper
  have hscaleNonneg (n : ℕ) :
      0 ≤ increasingTimeRealAuxiliaryScale time width htime n :=
    (hwidthPos (increasingTimeIntervalIndex time htime n)).le
  have hscaleRatio := Asymptotics.tendsto_div_sqrt_atTop_zero_of_tendsto_sq_div_atTop_zero
    hscaleNonneg hscaleSq
  exact Asymptotics.IsSmallDeviationScale.of_tendsto hscaleTop hscaleRatio

/-- Real-width form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i); its sampled
widths satisfy the lemma's width-time relation. This form supplies the
one-block input in the equal-partition proof of Chapter 3, Lemma 3.2. Its
small-deviation input is A. A. Mogul'skii, “Small deviations in the sample
function space,” Theorem 3, Section 4, p. 764 (1974); English translation,
“Small Deviations in a Space of Trajectories,” DOI 10.1137/1119081. -/
theorem centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidthAlong
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {time : ℕ → ℕ} {width : ℕ → ℝ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k) (hwidthPos : ∀ k, 0 < width k)
    (hwidth : Tendsto width atTop atTop)
    (hwidthSq : Tendsto (fun k : ℕ => width k ^ 2 / (time k : ℝ))
      atTop (𝓝 0))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x : ℝ, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (width k)
          (time k - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x : ℝ, x ^ 2 ∂ν))) := by
  let scale := increasingTimeRealAuxiliaryScale time width htime
  have hsmall := increasingTimeRealAuxiliaryScale_isSmallDeviationScale
    htime htimePos hwidthPos hwidth hwidthSq
  have hrate := (centeredFiniteVariance_closedHorizontalTubeProbabilityRate
    hsmall hcentered hsquare hvariance ha haOne).comp htime.tendsto_atTop
  have hscaleEq : ∀ k : ℕ, scale (time k) = width k := by
    intro k
    simp [scale, increasingTimeRealAuxiliaryScale,
      increasingTimeIntervalIndex_at_time htime]
  have hsourceRate : Tendsto
      (fun k : ℕ => width k ^ 2 / (time k : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (width k)
          (time k - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x : ℝ, x ^ 2 ∂ν))) := by
    have heq : (fun k : ℕ => scale (time k) ^ 2 / (time k : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν) a
          (scale (time k)) (time k - 1)).toReal) =
        (fun k : ℕ => width k ^ 2 / (time k : ℝ) * Real.log
          (horizontalTubeProbability (iidSequenceLaw ν) a (width k)
            (time k - 1)).toReal) := by
      funext k
      rw [hscaleEq]
    exact hrate.congr' (Filter.Eventually.of_forall
      fun k => congrFun heq k)
  have hratioNat : Tendsto
      (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    have hratioBase : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1))
        atTop (𝓝 (1 : ℝ)) := by
      simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
    have hratioEq : (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) =ᶠ[atTop]
        fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn1 : 1 ≤ n := by omega
      simp [Nat.cast_sub hn1]
    exact hratioBase.congr' hratioEq.symm
  have hfactor := hratioNat.comp htime.tendsto_atTop
  have hproduct := hfactor.mul hsourceRate
  have hproductEq : (fun k : ℕ =>
      ((time k : ℝ) / ((time k - 1 : ℕ) : ℝ)) *
        (width k ^ 2 / (time k : ℝ) *
          Real.log (horizontalTubeProbability (iidSequenceLaw ν) a
            (width k) (time k - 1)).toReal)) =ᶠ[atTop]
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν) a
          (width k) (time k - 1)).toReal) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with k hk
    have htimeNe : (time k : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast (htimePos k))
    have hpredNat : 0 < time k - 1 := by
      have hk' : 1 < k := by omega
      have htimeStep : time 1 < time k := htime hk'
      have htimeOne : 0 < time 1 := htimePos 1
      omega
    have hpredPos : 0 < ((time k - 1 : ℕ) : ℝ) := by exact_mod_cast hpredNat
    have hpredNe : ((time k - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hpredPos
    field_simp [htimeNe, hpredNe]
  simpa only [one_mul] using hproduct.congr' hproductEq

/-- A sampled rate along every increasing time subsequence determines the
rate for arbitrary real widths and a real-width-indexed integer horizon. -/
private theorem tendsto_realWidthRate_of_sampledTime
    {L : ℝ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : Tendsto (fun D : ℝ => D ^ 2 / (L D : ℝ)) atTop (𝓝 0))
    {rate : ℝ → ℕ → ℝ} {limit : ℝ}
    (hsampled : ∀ {time : ℕ → ℕ} {width : ℕ → ℝ},
      StrictMono time → (∀ k, 0 < time k) → (∀ k, 0 < width k) →
      Tendsto width atTop atTop →
      Tendsto (fun k => width k ^ 2 / (time k : ℝ)) atTop (𝓝 0) →
      Tendsto (fun k => rate (width k) (time k - 1)) atTop (𝓝 limit)) :
    Tendsto (fun D : ℝ => rate D (L D)) atTop (𝓝 limit) := by
  let f : ℝ → ℝ := fun D => rate D (L D)
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hnot
  have hbad (n : ℕ) : ∃ D : ℝ, max 1 (n : ℝ) ≤ D ∧
      ε ≤ dist (f D) limit := by
    by_contra hN
    apply hnot
    refine ⟨max 1 (n : ℝ), ?_⟩
    intro D hD
    by_contra hdist
    exact hN ⟨D, hD, le_of_not_gt hdist⟩
  let widthSeq : ℕ → ℝ := fun n => Classical.choose (hbad n)
  have hwidthPos (n : ℕ) : 0 < widthSeq n :=
    lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans
      (Classical.choose_spec (hbad n)).1)
  have hwidthTop : Tendsto widthSeq atTop atTop := by
    rw [tendsto_atTop]
    intro bound
    obtain ⟨N, hN⟩ := exists_nat_ge bound
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN.trans ((by exact_mod_cast hn : (N : ℝ) ≤ (n : ℝ)).trans
      ((le_max_right _ _).trans (Classical.choose_spec (hbad n)).1))
  let rawTime : ℕ → ℕ := fun k => L (widthSeq k) + 1
  have hLwidth : Tendsto (fun k => L (widthSeq k)) atTop atTop :=
    hL.comp hwidthTop
  have hrawTime : Tendsto rawTime atTop atTop := by
    rw [tendsto_atTop]
    intro bound
    filter_upwards [hLwidth.eventually (eventually_ge_atTop bound)] with k hk
    dsimp [rawTime]
    omega
  obtain ⟨φ, hφ, hφtime⟩ := strictMono_subseq_of_tendsto_atTop hrawTime
  let widthSub : ℕ → ℝ := fun k => widthSeq (φ k)
  let timeSub : ℕ → ℕ := fun k => rawTime (φ k)
  have htimeSub : StrictMono timeSub := by
    simpa [timeSub, Function.comp_def] using hφtime
  have hwidthSubTop : Tendsto widthSub atTop atTop :=
    hwidthTop.comp hφ.tendsto_atTop
  have hwidthSqRaw : Tendsto
      (fun k => widthSeq k ^ 2 / ((L (widthSeq k) : ℝ) + 1))
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun k =>
        div_nonneg (sq_nonneg _) (by positivity)
    · filter_upwards [hLwidth.eventually (eventually_ge_atTop 1)] with k hk
      have hLpos : (0 : ℝ) < L (widthSeq k) := by exact_mod_cast hk
      have hLle : (L (widthSeq k) : ℝ) ≤ (L (widthSeq k) : ℝ) + 1 := by
        linarith
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLpos hLle
    · exact hquadratic.comp hwidthTop
  have hwidthSqSub : Tendsto
      (fun k => widthSub k ^ 2 / (timeSub k : ℝ)) atTop (𝓝 0) := by
    simpa [widthSub, timeSub, rawTime, Nat.cast_add, Nat.cast_one,
      Function.comp_def] using hwidthSqRaw.comp hφ.tendsto_atTop
  have hrateSub := hsampled htimeSub
    (fun k => by dsimp [timeSub, rawTime]; omega)
    (fun k => hwidthPos (φ k)) hwidthSubTop hwidthSqSub
  have hrateOnWidths : Tendsto (fun k => f (widthSub k)) atTop (𝓝 limit) := by
    simpa [f, widthSub, timeSub, rawTime, Function.comp_def,
      Nat.add_sub_cancel_right] using hrateSub
  have hclose : ∀ᶠ k : ℕ in atTop, dist (f (widthSub k)) limit < ε :=
    hrateOnWidths.eventually (Metric.ball_mem_nhds limit hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hclose
  have hlt := hN N le_rfl
  have hge : ε ≤ dist (f (widthSub N)) limit :=
    (Classical.choose_spec (hbad (φ N))).2
  exact (not_lt_of_ge hge) hlt

/-- Real-width form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i). For every
integer horizon $L_D\to\infty$ with $D^2/L_D\to0$, the closed horizontal-tube
probability has logarithmic rate $-\pi^2\sigma^2/2$ as real $D\to\infty$.
The rate is A. A. Mogul'skii, “Small deviations in the sample function
space,” Theorem 3, Section 4, p. 764 (1974); English translation, “Small
Deviations in a Space of Trajectories,” DOI 10.1137/1119081. -/
theorem centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidth
    {L : ℝ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : Tendsto (fun D : ℝ => D ^ 2 / (L D : ℝ)) atTop (𝓝 0))
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto
      (fun D : ℝ => D ^ 2 / (L D : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a D (L D)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  apply tendsto_realWidthRate_of_sampledTime
    (rate := fun D n => D ^ 2 / (n : ℝ) * Real.log
      (horizontalTubeProbability (iidSequenceLaw ν) a D n).toReal)
    (limit := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)) hL hquadratic
  intro time width htime htimePos hwidthPos hwidth hwidthSq
  simpa using
    centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidthAlong
      htime htimePos hwidthPos hwidth hwidthSq
      hcentered hsquare hvariance ha haOne

/-- Unit-variance specialization of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i).
The underlying rate is A. A. Mogul'skii, “Small deviations in the sample
function space,” Theorem 3, Section 4, p. 764 (1974); English translation,
“Small Deviations in a Space of Trajectories,” DOI 10.1137/1119081. -/
theorem centeredUnitVariance_closedHorizontalTubeProbabilityRate
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale (fun n => Real.sqrt n))
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : ∫ x, x ^ 2 ∂ν = 1)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto
      (fun n : ℕ => (scale n) ^ 2 / (n : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (scale n) (n - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2)) := by
  have hvariancePos : 0 < ∫ x : ℝ, x ^ 2 ∂ν := by
    rw [hvariance]
    norm_num
  simpa [hvariance] using
    centeredFiniteVariance_closedHorizontalTubeProbabilityRate
      hsmall hcentered hsquare hvariancePos ha haOne

private theorem tendsto_scaledLog_div_predHorizon
    {scale logProbability : ℕ → ℝ} {limit : ℝ}
    (hrate : Tendsto (fun n : ℕ => scale n ^ 2 / (n : ℝ) * logProbability n)
      atTop (𝓝 limit)) :
    Tendsto (fun n : ℕ => scale n ^ 2 / ((n - 1 : ℕ) : ℝ) * logProbability n)
      atTop (𝓝 limit) := by
  let horizonRatio : ℕ → ℝ := fun n => (n : ℝ) / ((n - 1 : ℕ) : ℝ)
  have hratioBase : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1))
      atTop (𝓝 (1 : ℝ)) := by
    simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
  have hratioEq : horizonRatio =ᶠ[atTop]
      fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn1 : 1 ≤ n := by omega
    simp [horizonRatio, Nat.cast_sub hn1]
  have hratio : Tendsto horizonRatio atTop (𝓝 (1 : ℝ)) :=
    hratioBase.congr' hratioEq.symm
  have hproduct := hratio.mul hrate
  have hEq : (fun n : ℕ => horizonRatio n *
      (scale n ^ 2 / (n : ℝ) * logProbability n)) =ᶠ[atTop]
      (fun n : ℕ => scale n ^ 2 / ((n - 1 : ℕ) : ℝ) * logProbability n) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    have hnReal : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
    have hpredPos : 0 < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < n - 1)
    have hpredNe : ((n - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hpredPos
    dsimp [horizonRatio]
    field_simp [hnReal, hpredNe]
  simpa only [one_mul] using hproduct.congr' hEq

private theorem tendsto_scaledLog_div_predTime
    {time : ℕ → ℕ} {width : ℕ → ℝ} {logProbability : ℕ → ℝ} {limit : ℝ}
    (htime : StrictMono time) (htimePos : ∀ k, 0 < time k)
    (hrate : Tendsto
      (fun k : ℕ => width k ^ 2 / (time k : ℝ) * logProbability k)
      atTop (𝓝 limit)) :
    Tendsto
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) * logProbability k)
      atTop (𝓝 limit) := by
  let horizonRatio : ℕ → ℝ := fun k => (time k : ℝ) / ((time k - 1 : ℕ) : ℝ)
  have hratioBase : Tendsto (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    have hratioReal : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1))
        atTop (𝓝 (1 : ℝ)) := by
      simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
    have hratioEq : (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) =ᶠ[atTop]
        fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn1 : 1 ≤ n := by omega
      simp [Nat.cast_sub hn1]
    exact hratioReal.congr' hratioEq.symm
  have hratio : Tendsto horizonRatio atTop (𝓝 (1 : ℝ)) := by
    change Tendsto (fun k : ℕ => (time k : ℝ) / ((time k - 1 : ℕ) : ℝ))
      atTop (𝓝 (1 : ℝ))
    exact hratioBase.comp htime.tendsto_atTop
  have hproduct := hratio.mul hrate
  have hEq : (fun k : ℕ => horizonRatio k *
      (width k ^ 2 / (time k : ℝ) * logProbability k)) =ᶠ[atTop]
      (fun k : ℕ => width k ^ 2 /
        ((time k - 1 : ℕ) : ℝ) * logProbability k) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with k hk
    have hk' : 1 < k := by omega
    have htimeStep : time 1 < time k := htime hk'
    have htimeOne : 0 < time 1 := htimePos 1
    have hpredNat : 0 < time k - 1 := by omega
    have htimeNe : (time k : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast htimePos k)
    have hpredNe : ((time k - 1 : ℕ) : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast hpredNat)
    dsimp [horizonRatio]
    field_simp [htimeNe, hpredNe]
  simpa only [one_mul] using hproduct.congr' hEq

/-- The generalized inverse width has the closed-tube rate in the normalization
of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i): `scale² / (n - 1)`. The source path uses
the same `n - 1` terminal partial sum. -/
theorem inverseScale_closedHorizontalTubeProbabilityRate
    {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop)
    (hquadratic : Asymptotics.IsSuperquadraticScale L)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto (fun n : ℕ => (Asymptotics.inverseScale L n : ℝ) ^ 2 /
      ((n - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a
          (Asymptotics.inverseScale L n) (n - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  apply tendsto_scaledLog_div_predHorizon
  exact centeredFiniteVariance_closedHorizontalTubeProbabilityRate
    (Asymptotics.isSmallDeviationScale_inverseScale hL hquadratic)
    hcentered hsquare hvariance ha haOne

/-- Upper-inverse-scale consequence of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i). -/
theorem upperInverseScale_closedHorizontalTubeProbabilityRate
    {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop)
    (hquadratic : Asymptotics.IsSuperquadraticScale L)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto (fun n : ℕ => (Asymptotics.upperInverseScale L n : ℝ) ^ 2 /
      ((n - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a
          (Asymptotics.upperInverseScale L n) (n - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  apply tendsto_scaledLog_div_predHorizon
  exact centeredFiniteVariance_closedHorizontalTubeProbabilityRate
    (Asymptotics.isSmallDeviationScale_upperInverseScale hL hquadratic)
    hcentered hsquare hvariance ha haOne

/-- Both generalized inverse widths satisfy the consequence of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.1(i), under the superquadratic scale assumption. -/
theorem inverseScales_closedHorizontalTubeProbabilityRate
    {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop)
    (hquadratic : Asymptotics.IsSuperquadraticScale L)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto (fun n : ℕ => (Asymptotics.inverseScale L n : ℝ) ^ 2 /
      ((n - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a
          (Asymptotics.inverseScale L n) (n - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) ∧
    Tendsto (fun n : ℕ => (Asymptotics.upperInverseScale L n : ℝ) ^ 2 /
      ((n - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a
          (Asymptotics.upperInverseScale L n) (n - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  exact ⟨inverseScale_closedHorizontalTubeProbabilityRate hL hquadratic
      hcentered hsquare hvariance ha haOne,
    upperInverseScale_closedHorizontalTubeProbabilityRate hL hquadratic
      hcentered hsquare hvariance ha haOne⟩

/-- Integer-width form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i). The proof
interpolates along a subsequence of strictly increasing times. Its rate is
Mogul'skii, Theorem 3, Section 4, p. 764, in “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081. -/
theorem centeredFiniteVariance_horizontalTubeProbabilityRate
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : Asymptotics.IsSuperquadraticScale L)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto
      (fun Δ : ℕ => (Δ : ℝ) ^ 2 / (L Δ : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a Δ (L Δ)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let rate : ℕ → ℝ := fun Δ => (Δ : ℝ) ^ 2 / (L Δ : ℝ) * Real.log
    (horizontalTubeProbability (iidSequenceLaw ν) a Δ (L Δ)).toReal
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
  have hrateSub :=
    centeredFiniteVariance_closedHorizontalTubeProbabilityRate_along
      htimeSub (fun k => by dsimp [timeSub, rawTime]; omega)
      hwidthSubRealTop hwidthSqSub hcentered hsquare hvariance ha haOne
  have hrateOnWidths : Tendsto (fun k => rate (widthSub k)) atTop (𝓝 c) := by
    simpa [rate, widthSub, timeSub, rawTime, Function.comp_def,
      Nat.add_sub_cancel_right] using hrateSub
  have hclose : ∀ᶠ k : ℕ in atTop, dist (rate (widthSub k)) c < ε :=
    hrateOnWidths.eventually (Metric.ball_mem_nhds c hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hclose
  have hlt := hN N le_rfl
  have hge : ε ≤ dist (rate (widthSub N)) c := hwidthBad (φ N)
  exact (not_lt_of_ge hge) hlt

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
  let scale := increasingTimeAuxiliaryScale time width htime
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
  have hsmall := increasingTimeAuxiliaryScale_isSmallDeviationScale
    htime htimePos hwidth hwidthSq
  have hscaleEq (k : ℕ) : scale (time k) = (width k : ℝ) := by
    simp [scale, increasingTimeAuxiliaryScale,
      increasingTimeIntervalIndex_at_time htime]
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
    tendsto_scaledLog_div_predTime htime htimePos hsourceRateAtTime
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
  let scale := increasingTimeRealAuxiliaryScale time width htime
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
  have hsmall := increasingTimeRealAuxiliaryScale_isSmallDeviationScale
    htime htimePos hwidthPos hwidth hwidthSq
  have hscaleEq (k : ℕ) : scale (time k) = width k := by
    simp [scale, increasingTimeRealAuxiliaryScale,
      increasingTimeIntervalIndex_at_time htime]
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
    tendsto_scaledLog_div_predTime htime htimePos hsourceRateAtTime
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
