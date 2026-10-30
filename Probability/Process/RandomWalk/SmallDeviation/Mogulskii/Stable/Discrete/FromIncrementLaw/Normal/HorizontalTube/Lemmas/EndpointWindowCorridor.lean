/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Basic
import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Energy
import Probability.Process.RandomWalk.Path.Skorokhod.TerminalLeft.Basic

/-!
# Endpoint-window corridor proof steps



## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.endpointWindowCorridorUnion`:
  the singleton union $G=\{C_{a,u,v}\}$ used to apply the terminal-left path rate theorem.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.endpointWindowCorridorUnion_toSet` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.endpointWindowCorridorUnion_realEnergy`:
  $G.toSet=C_{a,u,v}.toSet$ and $H_2(G)=1$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.sourceTerminalJumpCorridor_subset_endpointWindow`:
  a terminal-left normalized path in $C_{a,u,v}$ lies in the closed tube and has terminal value in $[(u-a)D,(v-a)D]$.

These steps support Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (master's thesis, Fudan University,
2026), Chapter 3, Lemma 3.1(ii), using
A. A. Mogul'skii, Theorem 3, Section 4, p. 764, “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4)
(1974), 755--765; English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975),
726--736, DOI 10.1137/1119081.
-/

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

private noncomputable def unitTubeTerminalWindowCorridor (a u v : ℝ)
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

private lemma terminalWindowCorridor_energy (α a u v : ℝ)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    (unitTubeTerminalWindowCorridor a u v ha haOne hu huv hv).energy α = 1 := by
  let c := unitTubeTerminalWindowCorridor a u v ha haOne hu huv hv
  let upper := StepBoundary.constant ((1 - a : ℝ) : EReal)
  let lower := StepBoundary.constant ((-a : ℝ) : EReal)
  let witness : C(unitInterval, ℝ) := ⟨fun _ => 0, continuous_const⟩
  have hwitness0 : witness ⊥ = 0 := by simp [witness]
  have hpath : (Skorokhod.ofContinuousMap witness : CadlagPath unitInterval ℝ) ∈
      corridorSet upper lower := by
    constructor
    · simp [Skorokhod.ofContinuousMap_apply, witness]
    · intro t
      change ((-a : ℝ) : EReal) < (0 : EReal) ∧
        (0 : EReal) < ((1 - a : ℝ) : EReal)
      constructor
      · exact_mod_cast neg_lt_zero.mpr ha
      · exact_mod_cast sub_pos.mpr haOne
  let constantCorridor : ContinuousAdmissibleStepCorridor :=
    ⟨⟨upper, lower⟩, ⟨witness, hwitness0, hpath⟩⟩
  have hupper : ∀ t : unitInterval, t ≠ ⊤ → c.upper.eval t = constantCorridor.upper.eval t := by
    intro t ht
    dsimp [c, unitTubeTerminalWindowCorridor, upper]
    rw [StepBoundary.eval_singleJump_of_lt ⊤ (by norm_num [unitInterval])
      ((lt_top_iff_ne_top).2 ht)]
    simp [constantCorridor, upper, StepBoundary.eval_constant]
  have hlower : ∀ t : unitInterval, t ≠ ⊤ → c.lower.eval t = constantCorridor.lower.eval t := by
    intro t ht
    dsimp [c, unitTubeTerminalWindowCorridor, lower]
    rw [StepBoundary.eval_singleJump_of_lt ⊤ (by norm_num [unitInterval])
      ((lt_top_iff_ne_top).2 ht)]
    simp [constantCorridor, lower, StepBoundary.eval_constant]
  have henergy := ContinuousAdmissibleStepCorridor.energy_eq_of_boundaries_eq_off_top
    (α := α) (c := c) (d := constantCorridor) hupper hlower
  have hconstantUpper : ∀ t : unitInterval,
      constantCorridor.upper.eval t = ((1 - a : ℝ) : EReal) := by
    intro t
    simp [constantCorridor, upper, StepBoundary.eval_constant]
  have hconstantLower : ∀ t : unitInterval,
      constantCorridor.lower.eval t = ((-a : ℝ) : EReal) := by
    intro t
    simp [constantCorridor, lower, StepBoundary.eval_constant]
  have hconstant : constantCorridor.energy α = 1 := by
    rw [ContinuousAdmissibleStepCorridor.energy_eq_widthCost_of_constant_values
      α constantCorridor ((1 - a : ℝ) : EReal) ((-a : ℝ) : EReal)
      hconstantUpper hconstantLower]
    rw [widthCost_coe_sub α (1 - a) (-a) (by linarith)]
    rw [show (1 - a) - (-a) = (1 : ℝ) by ring, Real.one_rpow]
    simp
  exact henergy.trans hconstant

noncomputable def endpointWindowCorridorUnion (a u v : ℝ)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    FiniteCorridorUnion 2 := by
  let c := unitTubeTerminalWindowCorridor a u v ha haOne hu huv hv
  refine ⟨1, by norm_num, fun _ => c, ?_⟩
  have hmin : finiteMinimumEnergy 2 1 (by norm_num) (fun _ : Fin 1 => c) = c.energy 2 := by
    simp [finiteMinimumEnergy]
  rw [hmin]
  have henergy : c.energy 2 = 1 := by
    simpa [c] using terminalWindowCorridor_energy 2 a u v ha haOne hu huv hv
  rw [henergy]
  norm_num

lemma endpointWindowCorridorUnion_toSet (a u v : ℝ)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    (endpointWindowCorridorUnion a u v ha haOne hu huv hv).toSet =
      (unitTubeTerminalWindowCorridor a u v ha haOne hu huv hv).toSet := by
  ext path
  simp [endpointWindowCorridorUnion, FiniteCorridorUnion.toSet]

lemma endpointWindowCorridorUnion_realEnergy (a u v : ℝ)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    (endpointWindowCorridorUnion a u v ha haOne hu huv hv).realEnergy = 1 := by
  change (finiteMinimumEnergy 2 1 (by norm_num)
      (fun _ : Fin 1 => unitTubeTerminalWindowCorridor a u v ha haOne hu huv hv)).toReal = 1
  have hmin : finiteMinimumEnergy 2 1 (by norm_num)
      (fun _ : Fin 1 => unitTubeTerminalWindowCorridor a u v ha haOne hu huv hv) =
        (unitTubeTerminalWindowCorridor a u v ha haOne hu huv hv).energy 2 := by
    simp [finiteMinimumEnergy]
  rw [hmin, terminalWindowCorridor_energy]
  norm_num

lemma sourceTerminalJumpCorridor_subset_endpointWindow
    {n : ℕ} {scale : ℕ → ℝ} {a u v : ℝ}
    (hn : 0 < n) (hscale : 0 < scale n)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    {increment : ℕ → ℝ |
      terminalLeftNormalizedStepCadlagPathIcc scale n increment ∈
        (unitTubeTerminalWindowCorridor a u v ha haOne hu huv hv).toSet} ⊆
      horizontalTubeEndpointWindowEvent a (scale n) (n - 1) u v := by
  intro increment hcorridor
  let path := terminalLeftNormalizedStepCadlagPathIcc scale n increment
  let c := unitTubeTerminalWindowCorridor a u v ha haOne hu huv hv
  change path ⊥ = 0 ∧ ∀ t : unitInterval,
      c.lower.eval t < (path t : EReal) ∧ (path t : EReal) < c.upper.eval t at hcorridor
  have htopLower : c.lower.eval ⊤ = ((u - a : ℝ) : EReal) := by
    dsimp [c, unitTubeTerminalWindowCorridor]
    exact StepBoundary.eval_singleJump_of_le ⊤ (by norm_num [unitInterval]) le_rfl
      (-a : EReal) (u - a : EReal)
  have htopUpper : c.upper.eval ⊤ = ((v - a : ℝ) : EReal) := by
    dsimp [c, unitTubeTerminalWindowCorridor]
    exact StepBoundary.eval_singleJump_of_le ⊤ (by norm_num [unitInterval]) le_rfl
      (1 - a : EReal) (v - a : EReal)
  have htopBounds := hcorridor.2 ⊤
  rw [htopLower, htopUpper,
    terminalLeftNormalizedStepCadlagPathIcc_apply_top scale hn increment] at htopBounds
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
    have hrange := terminalLeftNormalizedStepCadlagPathIcc_range_eq_scaledDisplacement
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
        rw [show path = terminalLeftNormalizedStepCadlagPathIcc scale n increment by rfl,
          terminalLeftNormalizedStepCadlagPathIcc_apply_top scale hn increment]
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
        dsimp [c, unitTubeTerminalWindowCorridor]
        exact StepBoundary.eval_singleJump_of_lt ⊤ (by norm_num [unitInterval])
          ((lt_top_iff_ne_top).2 htTop) (-a : EReal) (u - a : EReal)
      have hupperEval : c.upper.eval t = ((1 - a : ℝ) : EReal) := by
        dsimp [c, unitTubeTerminalWindowCorridor]
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


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
