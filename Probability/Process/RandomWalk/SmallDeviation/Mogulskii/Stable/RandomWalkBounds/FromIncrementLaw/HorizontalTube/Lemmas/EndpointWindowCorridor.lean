/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.HorizontalTube.EndpointWindowEvent
public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.TerminalWindow
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Path.SourcePath

/-!
# Endpoint-window corridor proof steps

The proof-specific declarations are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.endpointWindowCorridorUnion`:
  the singleton union $G=\{C_{a,u,v}\}$ used to apply the source-path rate theorem.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.endpointWindowCorridorUnion_toSet` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.endpointWindowCorridorUnion_realEnergy`:
  $G.toSet=C_{a,u,v}.toSet$ and $H_2(G)=1$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.sourceTerminalJumpCorridor_subset_endpointWindow`:
  a source-normalized path in $C_{a,u,v}$ lies in the closed tube and has terminal value in $[(u-a)D,(v-a)D]$.

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
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

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
    simpa [c] using unitTubeTerminalWindowCorridor_energy 2 a u v ha haOne hu huv hv
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
  rw [hmin, unitTubeTerminalWindowCorridor_energy]
  norm_num

lemma sourceTerminalJumpCorridor_subset_endpointWindow
    {n : ℕ} {scale : ℕ → ℝ} {a u v : ℝ}
    (hn : 0 < n) (hscale : 0 < scale n)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1) :
    {increment : ℕ → ℝ |
      sourceNormalizedStepCadlagPathIcc scale n increment ∈
        (unitTubeTerminalWindowCorridor a u v ha haOne hu huv hv).toSet} ⊆
      horizontalTubeEndpointWindowEvent a (scale n) (n - 1) u v := by
  intro increment hcorridor
  let path := sourceNormalizedStepCadlagPathIcc scale n increment
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
