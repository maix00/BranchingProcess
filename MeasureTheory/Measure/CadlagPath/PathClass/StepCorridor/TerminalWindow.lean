/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.PathClass.StepCorridor.Energy
public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.TerminalWindow

/-!
# Energy of a unit-width corridor with a terminal window

The public theorem
`Skorokhod.PathClass.StepCorridor.unitTubeTerminalWindowCorridor_energy`
states that for every exponent $\alpha\in\mathbb R$ the corridor
$C_{a,u,v}$ has
\[
H_\alpha(C_{a,u,v})=\int_0^1 1\,dt=1.
\]
Changing either boundary only at the terminal time contributes zero to this
integral. This is the energy identity for the terminal-jump corridor used in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (master's thesis, Fudan University, 2026), Chapter 3, Lemma
3.1(ii), whose source-path rate is
A. A. Mogul'skii, Theorem 3, Section 4, p. 764, “Small deviations in the
sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.
-/

open MeasureTheory
open Skorokhod
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal

@[expose] public section

namespace Skorokhod.PathClass.StepCorridor

/-- A terminal change of the unit-width tube boundaries does not change its
`Hα` energy. The theorem holds for every real exponent because the boundaries
agree with the constant-width-one corridor away from the terminal time, a
volume-null singleton. This is the energy calculation for the terminal-jump
corridor used in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring* (master's thesis, Fudan University, 2026), Chapter 3,
Lemma 3.1(ii). -/
theorem unitTubeTerminalWindowCorridor_energy (α a u v : ℝ)
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

end Skorokhod.PathClass.StepCorridor

end
