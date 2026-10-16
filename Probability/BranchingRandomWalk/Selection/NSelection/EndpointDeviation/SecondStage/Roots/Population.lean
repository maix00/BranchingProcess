/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Roots.Chosen
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Roots.Fresh
/-!
# Independent second-stage failure below killed-population roots

The measurable root choice from a finite killed slice can be passed directly
to the predictable fresh-subtree estimate.  The estimate controls failure on
the event that the slice contains the requested number of roots.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine

@[expose] public section

/-- The event that the actual finite killed slice contains at least `K`
particles. -/
def rightTailSecondStageEnoughRoots
    {m K : ℕ} (P : ℕ → RestartedPopulation m)
    (hP : ∀ n, (P n).FiniteSlices) (generation : ℕ → ℕ) (n : ℕ) :
    Set (RestartedField m) :=
  {field | K ≤ ((hP n).toFinset (generation n) field).card}

theorem measurableSet_rightTailSecondStageEnoughRoots
    {m K : ℕ} (P : ℕ → RestartedPopulation m)
    (hP : ∀ n, (P n).FiniteSlices) (generation : ℕ → ℕ) (n : ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) (generation n)]
      (rightTailSecondStageEnoughRoots (K := K) P hP generation n) := by
  let F := RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
  let candidates : RestartedField m → Finset (RootIndexed.TreeNode (Fin m) ℕ) :=
    fun field => (hP n).toFinset (generation n) field
  have hcandidates : Measurable[F (generation n)] candidates := by
    dsimp [candidates]
    exact (hP n).measurable_toFinset (generation n)
  have hcard : Measurable[F (generation n)]
      (fun field => (candidates field).card) :=
    (measurable_of_countable
      (fun s : Finset (RootIndexed.TreeNode (Fin m) ℕ) => s.card)).comp
        hcandidates
  have hlarge : Measurable[F (generation n)]
      (fun field => K ≤ (candidates field).card) :=
    (measurable_of_countable (fun k : ℕ => K ≤ k)).comp hcard
  change MeasurableSet[F (generation n)]
    {field | K ≤ (candidates field).card}
  simpa using hlarge (measurableSet_singleton True)

/-- The selected roots from the killed slice satisfy all hypotheses of the
predictable independent-subtree estimate. -/
theorem eventually_measure_rightTailSecondStageEnoughRoots_allAvoid_le
    {m K : ℕ} [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : K ≤ m)
    (P : ℕ → RestartedPopulation m) (hP : ∀ n, (P n).FiniteSlices)
    {D generation : ℕ → ℕ}
    (hD : Tendsto (fun n => (D n : ℝ)) atTop atTop)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    {sigma κ c v : ℝ}
    (hν : IsCenteredSecondMoment
      (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (hsigma : 0 < sigma) (hκ : 0 ≤ κ) (hc : 0 < c) (hv : 0 < v)
    (hκv : κ / c ^ 2 < v)
    (hterminal : κ / c ^ 2 ≤ 2 * v / 5)
    (hentranceWidth : (5 * (κ / c ^ 2) + v) / 2 ≤ c)
    (hK : 0 < K)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)] :
    ∃ entryQ : ℝ≥0∞, 0 < entryQ ∧
      ∃ C : ℝ, C < 0 ∧ ∃ bridgeQ : ℝ≥0∞, 0 < bridgeQ ∧
        ∃ amplitude : ℝ, 0 < amplitude ∧
          ∀ᶠ n : ℕ in atTop,
            let pzMean := rightTailPositiveASecondStagePZMean μ (D n) κ c v
            let A := rightTailSecondStageEnoughRoots (K := K) P hP generation n
            (RootIndexed.stepFieldLaw (Root := Fin m) μ)
              (A ∩
                RootIndexed.selectedSubtreeStepFieldVector
                    (rightTailSecondStageRoots hKm P hP generation n) ⁻¹'
                  rightTailPositiveASecondStageFailureEvent K (D n) κ c v) ≤
              (RootIndexed.stepFieldLaw (Root := Fin m) μ) A *
                ENNReal.ofReal (Real.exp (-((K : ℝ) * pzMean.toReal / 4))) := by
  let chosen := rightTailSecondStageRoots hKm P hP generation
  let A : ℕ → Set (RestartedField m) :=
    fun n => rightTailSecondStageEnoughRoots (K := K) P hP generation n
  have hcount : ∀ n, (Set.range (chosen n)).Countable :=
    rightTailSecondStageRoots_countable hKm P hP generation
  have hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
        (generation n)]
      {field | chosen n field = roots} := by
    intro n roots
    exact measurableSet_rightTailSecondStageRoots_eq hKm P hP generation n roots
  have hdepth : ∀ n field i, (chosen n field i).2.length = generation n :=
    rightTailSecondStageRoots_depth hKm P hP generation
  have hinj : ∀ n field, Function.Injective (chosen n field) :=
    rightTailSecondStageRoots_injective hKm P hP generation
  have hA : ∀ n, MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
        (generation n)] (A n) := by
    intro n
    exact measurableSet_rightTailSecondStageEnoughRoots P hP generation n
  obtain ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude, hamplitude,
      hbound⟩ :=
    eventually_measure_predictableSecondStageRoots_allAvoid_le
      (Root := Fin m) (m := K) (D := D) (generation := generation)
      hD μ hboundary hcross hν hsigma hκ hc hv hκv hterminal hentranceWidth hK
      chosen hcount hfiber hdepth hinj A hA
  refine ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude,
    hamplitude, ?_⟩
  filter_upwards [hbound] with n hboundN
  simpa [chosen, A, rightTailSecondStageEnoughRoots] using hboundN

end

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
