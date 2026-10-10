/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Assumptions.Moments
import Probability.BranchingRandomWalk.Restart.GoodSplit
import Probability.BranchingRandomWalk.Timing.GeometricTrial.FirstMoment

/-!
# First-moment position cost before a reserve split

The restart proof's cycle increment accumulates the first-child displacement
only on generations where the reserve step does not split.  The split edge is
bounded separately by the cutoff.  This module specializes the geometric
first-moment estimate to the thesis `StepLaw` and its leftmost positive-part
assumption.  It gives an expected positive-variation bound for the failed
portion of one reserve cycle, with no second moment.

This is a one-cycle estimate.  It does not identify the thesis's random
restart frontier or prove that the cycle samples are fresh after earlier
candidate outcomes.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- In an iid sequence of branching steps, the expected total positive
leftmost displacement accumulated over failed reserve generations, up to the
first bounded split, is at most the one-step leftmost first moment divided by
the split probability.  The selected split event is the same bounded-second-
child event used by the thesis reserve rule. -/
theorem iidGeometricFailureLeftmostPositiveDisplacement_le
    {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : StepLaw ι ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hfirst : HasLeftmostFirstMoment L)
    (X : ℕ → Ω → Step ι ℝ) (hX : ∀ n, Measurable (X n))
    (hXi : iIndepFun X μ) (hLaw : ∀ n, μ.map (X n) = L.raw)
    (R : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (M : ℕ) (p : ℝ) (hp : 0 < p)
    (hprob : L.raw.real (boundedSelectedSplitEvent L R M) = p) :
    (∫ ω, ∑' n, geometricPrefixRewardTerm X
        (boundedSelectedSplitEvent L R M)
        (fun ξ => max (L.displacement 0 ξ) 0 *
          (boundedSelectedSplitEvent L R M)ᶜ.indicator
            (fun _ => (1 : ℝ)) ξ) n ω ∂μ) ≤
      (∫ ξ, L.leftmostPositivePart ξ ∂L.raw) / p := by
  let B := boundedSelectedSplitEvent L R M
  let Y : Step ι ℝ → ℝ := L.displacement 0
  have hB : MeasurableSet B := by
    dsimp [B]
    exact boundedSelectedSplitEvent_measurable L R hR M
  have hY : Measurable Y := L.displacement_measurable 0
  have hYpos : Integrable (fun ξ => max (Y ξ) 0) L.raw := by
    change Integrable L.leftmostPositivePart L.raw at hfirst
    have hleftmost : L.leftmostPositivePart =
        (fun ξ => max (L.displacement 0 ξ) 0) := by
      funext ξ
      rfl
    rw [hleftmost] at hfirst
    simpa [Y] using hfirst
  have hEq := iidGeometricFailurePositiveReward_integral
    μ L.raw X hX hXi hLaw B hB Y hY hYpos p hp (by simpa [B] using hprob)
  have hRestricted : Integrable
      (fun ξ => max (Y ξ) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) ξ) L.raw := by
    have hindicator := hYpos.indicator hB.compl
    convert hindicator using 1 <;> ext ξ <;> by_cases hξ : ξ ∈ B <;>
      simp [hξ]
  have hnum :
      (∫ ξ, max (Y ξ) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) ξ ∂L.raw) ≤
        ∫ ξ, max (Y ξ) 0 ∂L.raw := by
    apply integral_mono_ae hRestricted hYpos
    filter_upwards [] with ξ
    by_cases hξ : ξ ∈ B <;> simp [hξ]
  rw [hEq]
  apply (div_le_div_of_nonneg_right hnum hp.le)

/-- Under the thesis's nonempty supercritical base assumptions, a capacity-
two selection has some finite second-child cutoff with positive split
probability.  The preceding theorem then supplies a finite first-moment
bound on the failed first-child displacement accumulated before that split.
This is the one-cycle estimate used in place of a second-moment estimate for
the cycle's positive spatial cost. -/
theorem exists_nat_cutoff_iidGeometricFailureLeftmostPositiveDisplacement_le
    {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : StepLaw ι ℕ ℝ)
    (hbase : BasicBranchingAssumptions L)
    (hfirst : HasLeftmostFirstMoment L)
    (X : ℕ → Ω → Step ι ℝ) (hX : ∀ n, Measurable (X n))
    (hXi : iIndepFun X μ) (hLaw : ∀ n, μ.map (X n) = L.raw)
    (R : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (hadequate : ∀ ξ : Step ℕ ℝ,
      2 ≤ ξ.childCount → 2 ≤ (R ξ).card) :
    ∃ M : ℕ,
      0 < L.raw.real (boundedSelectedSplitEvent L R M) ∧
      (∫ ω, ∑' n, geometricPrefixRewardTerm X
          (boundedSelectedSplitEvent L R M)
          (fun ξ => max (L.displacement 0 ξ) 0 *
            (boundedSelectedSplitEvent L R M)ᶜ.indicator
              (fun _ => (1 : ℝ)) ξ) n ω ∂μ) ≤
        (∫ ξ, L.leftmostPositivePart ξ ∂L.raw) /
          L.raw.real (boundedSelectedSplitEvent L R M) := by
  letI : IsProbabilityMeasure L.raw := hbase.rawProbability
  obtain ⟨M, hsplit, _hmeas⟩ :=
    exists_nat_cutoff_positive_boundedSelectedSplit L hbase R hR hadequate
  have hp : 0 < L.raw.real (boundedSelectedSplitEvent L R M) :=
    ENNReal.toReal_pos hsplit.ne' (measure_ne_top L.raw _)
  refine ⟨M, hp, ?_⟩
  exact iidGeometricFailureLeftmostPositiveDisplacement_le
    μ L hfirst X hX hXi hLaw R hR M
    (L.raw.real (boundedSelectedSplitEvent L R M)) hp rfl

end ProbabilityTheory.BranchingRandomWalk

end
