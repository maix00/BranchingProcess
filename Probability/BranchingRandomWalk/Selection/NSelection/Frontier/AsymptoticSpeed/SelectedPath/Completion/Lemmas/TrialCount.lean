/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Causal
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Splits
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Population.RootIndexed
import Combinatorics.UlamHarris.Order

/-!
# Trial count at the successful completion

## Internal proof declarations

* `measurableSet_trialCount_lt_at_completion`: the event that fewer than
  $K$ splits precede the successful growth trial is measurable at $\tau$.

This supplies the trial count in the good event of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, Theorem 1.2.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion

open Combinatorics.Branching Combinatorics.UlamHarris
open GrowthTrial GrowthTrial.Population

/-- At finite completion the number of earlier split marks is the
zero-based index of the successful growth trial. The count is observable
in the stopped generation domain. -/
lemma measurableSet_trialCount_lt_at_completion
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration K : ℕ) (r : ℕ) :
    let τ := firstSuccessfulCompletion R growth hR lower upper duration r
    let hτ := firstSuccessfulCompletion_isStoppingTime R growth hR hgrowth lower upper duration r
    MeasurableSet[hτ.measurableSpace]
      {ω | splitCount R r ((τ ω).untopD 0 - (duration + 1)) ω < K} := by
  intro τ hτ
  let Ω := RootIndexed.StepField ℕ ℕ ℝ
  let F := RootIndexed.stepFiltration (Root := ℕ) (α := ℕ) (X := ℝ)
  let A : Set Ω := {ω | splitCount R r ((τ ω).untopD 0 - (duration + 1)) ω < K}
  have hs (n : ℕ) :
      MeasurableSet[F n] {ω : Ω | splitCount R r (n - (duration + 1)) ω < K} := by
    have hm : Measurable[F (n - (duration + 1))]
        (fun ω : Ω => splitCount R r (n - (duration + 1)) ω) :=
      splitCount_measurable R hR r _
    exact F.mono (Nat.sub_le ..) _ (hm (measurableSet_Iio (a := K)))
  have hset : A = ⋃ t : WithTop ℕ, A ∩ {ω | τ ω = t} := by
    ext ω
    simp [and_comm]
  change MeasurableSet[hτ.measurableSpace] A
  rw [hset]
  apply MeasurableSet.iUnion
  intro t
  cases t with
  | top =>
    let B : Set Ω := {ω | splitCount R r (0 - (duration + 1)) ω < K}
    have heq : A ∩ {ω | τ ω = ⊤} = B ∩ {ω | τ ω = ⊤} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact and_congr_left fun h => by
        change (splitCount R r ((τ ω).untopD 0 - (duration + 1)) ω < K) ↔ _
        rw [h]
        rfl
    rw [heq]
    exact ((hτ.le_measurableSpace_of_const_le (i := 0) fun _ => bot_le) _ (hs 0)).inter (hτ.measurable (measurableSet_singleton _))
  | coe n =>
    have heq : A ∩ {ω | τ ω = (n : WithTop ℕ)} =
        {ω | splitCount R r (n - (duration + 1)) ω < K} ∩ {ω | τ ω = (n : WithTop ℕ)} := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact and_congr_left fun h => by
        change (splitCount R r ((τ ω).untopD 0 - (duration + 1)) ω < K) ↔ _
        rw [h]
        rfl
    change MeasurableSet[hτ.measurableSpace] (A ∩ {ω | τ ω = (n : WithTop ℕ)})
    rw [heq]
    exact (hτ.measurableSet_inter_eq_iff _ n).2 ((hs n).inter (hτ.measurableSet_eq n))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion
