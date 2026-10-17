/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.PathClass.StepCorridor.Basic

/-!
# Unit-width corridor with a terminal window

The public definition is:

- `Skorokhod.PathClass.StepCorridor.unitTubeTerminalWindowCorridor`: for
  $0<a<1$ and $0<u<v<1$, the admissible corridor $C_{a,u,v}$ with boundary values
  \[
  (\ell(t),r(t))=
  \begin{cases}
  (-a,1-a),&t<1,\\
  (u-a,v-a),&t=1,
  \end{cases}
  \]
  so its paths satisfy $\ell(t)<f(t)<r(t)$ and $f(0)=0$. Thus the terminal
  window $[u-a,v-a]$ lies in the unit-width tube $[-a,1-a]$, and both step
  boundaries change only at time $1$.

This is the single-terminal-jump corridor used for Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
(master's thesis, Fudan University, 2026), Chapter 3, Lemma 3.1(ii), with
source-path rate from A. A. Mogul'skii,
Theorem 3, Section 4, p. 764, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(1) (1975), 726--736, DOI
10.1137/1119081.
-/

open Skorokhod
open Skorokhod.PathClass.StepCorridor

@[expose] public section

namespace Skorokhod.PathClass.StepCorridor

/-- The unit-width corridor whose boundaries remain at `-a` and `1-a` before
time `1` and change there to `u-a` and `v-a`. Its admissible paths satisfy
`f 0 = 0` and the strict bounds
`lower t < f t < upper t`; in particular, at time `1` they lie in the
terminal interval `(u-a, v-a)`. This is the terminal-jump corridor used in
Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (master's thesis, Fudan University, 2026), Chapter 3,
Lemma 3.1(ii). -/
noncomputable def unitTubeTerminalWindowCorridor (a u v : ℝ)
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


end Skorokhod.PathClass.StepCorridor

end
