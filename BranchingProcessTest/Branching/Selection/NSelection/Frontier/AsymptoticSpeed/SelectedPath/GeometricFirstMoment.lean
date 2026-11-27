/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Assumptions.Moments
import Probability.BranchingRandomWalk.Step.Selection.BoundedSplit
import Probability.Sequence.IID.GeometricReward.Definitions
import Probability.Sequence.IID.GeometricReward.FirstMoment
import Probability.BranchingProcess.Offspring.Count
import Mathlib.Probability.Independence.Basic

/-!
# First-moment position cost before a bounded selected split

This regression specializes the public IID geometric first-moment identity
to a `StepLaw` and a bounded selected-split success event. First-child
displacements contribute only on failed generations. The bound uses the
leftmost positive-part first moment and no second moment; these assertions
exercise that specialization without a separate production wrapper.

This is a one-trial-family estimate. It does not identify a random endpoint
frontier or prove that later trial samples are fresh after earlier candidate
outcomes.

## Internal proof declarations

If the bounded split event \(B\) has probability \(p>0\), the expected
leftmost positive displacement accumulated on trials through the first
success, with only failed-trial displacements counted, is bounded by the
one-step first moment divided by \(p\):

\[\mathbb E\!\left[\sum_{n\ge0}Y(X_n)^+
  \mathbf 1_{\{X_0,\ldots,X_n\notin B\}}\right]
  \le\frac{\mathbb E_L[Y^+]}{p}.\]

- `BranchingProcessTest.GeometricSplitReward.iidGeometricFailureLeftmostPositiveDisplacement_le`:
  for iid
  steps and a success event `B` of probability `p > 0`, the expected total
  positive leftmost displacement accumulated on failures before the first
  success is bounded by
  `∫ ξ, L.leftmostPositivePart ξ ∂L.raw / p`.
- `BranchingProcessTest.GeometricSplitReward.exists_nat_cutoff_iidGeometricFailureLeftmostPositiveDisplacement_le`:
  under the supercritical offspring assumption and a finite leftmost first
  moment, some finite cutoff `M` has positive split probability, and the
  corresponding expected failed-cycle displacement is bounded by the same
  first moment divided by that probability.
-/

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.BranchingRandomWalk
open scoped BigOperators

namespace BranchingProcessTest.GeometricSplitReward

open ProbabilityTheory.BranchingRandomWalk.Step.Selection
open Combinatorics.Branching
open ProbabilityTheory.BranchingProcess

/-- In an iid sequence of branching steps, the expected total positive
leftmost displacement accumulated over failed-trial generations, up to the
first bounded split, is at most the one-step leftmost first moment divided by
the split probability. The selected split event is the bounded-second-child
event used by the endpoint-deviation construction. -/
lemma iidGeometricFailureLeftmostPositiveDisplacement_le
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
    convert hindicator using 1
    ext ξ
    by_cases hξ : ξ ∈ B <;> simp [hξ]
  have hnum :
      (∫ ξ, max (Y ξ) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) ξ ∂L.raw) ≤
        ∫ ξ, max (Y ξ) 0 ∂L.raw := by
    apply integral_mono_ae hRestricted hYpos
    filter_upwards [] with ξ
    by_cases hξ : ξ ∈ B <;> simp [hξ]
  rw [hEq]
  apply (div_le_div_of_nonneg_right hnum hp.le)

/-- Under the supercritical base assumption, a capacity-two selection has
some finite second-child cutoff with positive split
probability.  The preceding theorem then supplies a finite first-moment
bound on the failed first-child displacement accumulated before that split.
This is the one-cycle estimate used in place of a second-moment estimate for
the cycle's positive spatial cost. -/
lemma exists_nat_cutoff_iidGeometricFailureLeftmostPositiveDisplacement_le
    {Ω ι : Type*} [MeasurableSpace Ω] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : StepLaw ι ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsupercritical : OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ :
        OffspringConfigurationLaw ι ℝ))
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
  obtain ⟨M, hsplit, _hmeas⟩ :=
    exists_nat_cutoff_positive_boundedSelectedSplit L hsupercritical
      R hR hadequate
  have hp : 0 < L.raw.real (boundedSelectedSplitEvent L R M) :=
    ENNReal.toReal_pos hsplit.ne' (measure_ne_top L.raw _)
  refine ⟨M, hp, ?_⟩
  exact iidGeometricFailureLeftmostPositiveDisplacement_le
    μ L hfirst X hX hXi hLaw R hR M
    (L.raw.real (boundedSelectedSplitEvent L R M)) hp rfl

end BranchingProcessTest.GeometricSplitReward

#print axioms BranchingProcessTest.GeometricSplitReward.iidGeometricFailureLeftmostPositiveDisplacement_le
#print axioms BranchingProcessTest.GeometricSplitReward.exists_nat_cutoff_iidGeometricFailureLeftmostPositiveDisplacement_le
