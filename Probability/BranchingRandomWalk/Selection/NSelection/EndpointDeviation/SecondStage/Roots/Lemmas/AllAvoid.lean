/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Lemmas.Corridor.PZ
import all Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
import all Probability.BranchingRandomWalk.Assumptions.CrossWeight
import all Probability.BranchingRandomWalk.Assumptions.Structural
import all Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
import all Probability.BranchingRandomWalk.Spine.RandomWalk.Basic
import all Probability.BranchingRandomWalk.Spine.Tilted.Law
import all Probability.BranchingRandomWalk.Spine.Tube.MRCA.Expansion
import all Probability.Distributions.Moments.Real
import all Probability.Process.RandomWalk.Path.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Roots.Population
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Roots.Selection
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Tube
/-!
# Selected-root specialization of the independent-subtree estimate

## Internal proof declarations


In the namespace
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation`,
`eventually_measure_secondStageEnoughRoots_allAvoid_le` is a
proof-chain lemma. Given a finite selected BRW population with at least `K n`
measurably selected roots at horizon `n`, it specializes the predictable
independent-subtree estimate to the event `secondStageEnoughRoots`. Under its
boundary, cross-weight, centered second-moment, and parameter hypotheses, there are
positive entrance and bridge constants and a negative escape-rate constant
such that eventually
\[
\mathbb P(A_n\cap\{\text{all }K_n\text{ selected descendant paths fail}\})
\le \mathbb P(A_n)
   \exp\!\left(-\frac{K_n}{4}\,
     \operatorname{toReal}(\operatorname{PZMean}(D_n,\kappa,c,v))\right),
\]
where \(A_n\) is the event that the selected BRW slice contains at least `K_n` roots.
The hypotheses include `D n → ∞`, boundary normalization, finite cross
weight, a centered tilted increment law with variance `sigma ^ 2 > 0`,
`K n ≤ m` for every `n` and `K n > 0` eventually, and the stated inequalities
on `kappa`, `c`, and `v`. This is the selected-root part of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.5 (master's thesis, Fudan University, 2026).
The general predictable-root estimate and this selected-population
specialization are grouped in this single proof-support module.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- A predictable injective family of same-generation roots inherits the
independent fresh-forest estimate on every measurable event of the past. This
is the general estimate used by the selected-population specialization below. -/
private lemma eventually_measure_predictableSecondStageRoots_allAvoid_le
    {Root : Type*} (m : ℕ → ℕ)
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    [Countable (RootIndexed.TreeNode Root ℕ)]
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
    (hm : ∀ᶠ n : ℕ in atTop, 0 < m n)
    (hTree : ∀ n, MeasurableSpace (RootIndexed.TreeNode (Fin (m n)) ℕ))
    (hCountable : ∀ n, Countable (RootIndexed.TreeNode (Fin (m n)) ℕ))
    (chosen : ∀ n, RootIndexed.StepField Root ℕ ℝ →
      Fin (m n) → Root × TreeNode ℕ)
    (hcount : ∀ n, (Set.range (chosen n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Root) (α := ℕ) (X := ℝ)
        (generation n)]
      {field | chosen n field = roots})
    (hdepth : ∀ n field i, (chosen n field i).2.length = generation n)
    (hinj : ∀ n field, Function.Injective (chosen n field))
    (A : ℕ → Set (RootIndexed.StepField Root ℕ ℝ))
    (hA : ∀ n, MeasurableSet[
      RootIndexed.stepFiltration (Root := Root) (α := ℕ) (X := ℝ)
        (generation n)] (A n)) :
    ∃ entryQ : ℝ≥0∞, 0 < entryQ ∧
      ∃ C : ℝ, C < 0 ∧ ∃ bridgeQ : ℝ≥0∞, 0 < bridgeQ ∧
        ∃ amplitude : ℝ, 0 < amplitude ∧
          ∀ᶠ n : ℕ in atTop,
            let pzMean := positiveASecondStagePZMean
              μ (D n) κ c v
            (RootIndexed.stepFieldLaw (Root := Root) μ)
              (A n ∩
                RootIndexed.selectedSubtreeStepFieldVector (chosen n) ⁻¹'
                  positiveASecondStageFailureEvent (m n) (D n) κ c v) ≤
              (RootIndexed.stepFieldLaw (Root := Root) μ) (A n) *
                ENNReal.ofReal (Real.exp (-((m n : ℝ) * pzMean.toReal / 4))) := by
  have havoid :=
    eventually_measure_positiveASecondStage_allRootsAvoid_le_of_centeredSecondMoment
      (D := D) hD μ hboundary hcross hν hsigma hκ hc hv hκv hterminal
      hentranceWidth m hm hTree hCountable
  obtain ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude,
      hamplitude, havoid⟩ := havoid
  refine ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude,
    hamplitude, ?_⟩
  filter_upwards [havoid] with n havoidN
  let mCurrent := m n
  letI : MeasurableSpace (RootIndexed.TreeNode (Fin mCurrent) ℕ) := hTree n
  letI : Countable (RootIndexed.TreeNode (Fin mCurrent) ℕ) := hCountable n
  let corridor := positiveASecondStageCorridor (D n) κ c v
  let success := hasPathHistoryIn (ι := ℕ) realPotential (D n) 0 corridor
  let failure := positiveASecondStageFailureEvent mCurrent (D n) κ c v
  have hcorridor : MeasurableSet corridor := by
    dsimp [corridor, positiveASecondStageCorridor]
    exact measurableSet_affineCorridorThrough (D n) 0
      (positiveASecondStageSlope κ c (D n))
      (positiveASecondStageWidth c (D n))
      (positiveASecondStageSlope κ c (D n) * (D n : ℝ) +
        v * ((D n : ℝ) ^ ((1 : ℝ) / 3)))
  have hsuccess : MeasurableSet success :=
    measurableSet_hasPathHistoryIn realPotential (D n) 0 corridor hcorridor
  have hfailure : MeasurableSet failure := by
    rw [show failure = ⋂ r : Fin mCurrent,
        (fun field : FiniteRootStepField mCurrent ℕ ℝ => field r) ⁻¹' successᶜ by
      ext field
      simp [failure, positiveASecondStageFailureEvent,
        success, corridor, positiveASecondStageCorridor]]
    apply MeasurableSet.iInter
    intro r
    exact hsuccess.compl.preimage (measurable_pi_apply r)
  have hfactor := RootIndexed.selectedSubtreeStepFieldVector_event_factorization
    μ (chosen n) (hcount n) (hfiber n) (hdepth n) (hinj n)
      (A n) failure (hA n) hfailure
  let pzMean := positiveASecondStagePZMean μ (D n) κ c v
  have hfailureBound :
      (finiteRootStepFieldLaw μ mCurrent) failure ≤
        ENNReal.ofReal (Real.exp (-((mCurrent : ℝ) * pzMean.toReal / 4))) := by
    simpa [failure, pzMean, positiveASecondStageFailureEvent,
      positiveASecondStagePZMean,
      positiveASecondStageCorridor, success, corridor,
      positiveASecondStageSlope, positiveASecondStageWidth]
      using havoidN
  calc
    (RootIndexed.stepFieldLaw (Root := Root) μ)
        (A n ∩ RootIndexed.selectedSubtreeStepFieldVector (chosen n) ⁻¹'
          positiveASecondStageFailureEvent mCurrent (D n) κ c v) =
        (RootIndexed.stepFieldLaw (Root := Root) μ) (A n) *
          (finiteRootStepFieldLaw μ mCurrent) failure := by
            simpa [failure] using hfactor
    _ ≤ (RootIndexed.stepFieldLaw (Root := Root) μ) (A n) *
        ENNReal.ofReal (Real.exp (-((mCurrent : ℝ) * pzMean.toReal / 4))) := by
          gcongr

lemma eventually_measure_secondStageEnoughRoots_allAvoid_le
    {m : ℕ} {K : ℕ → ℕ}
    [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : ∀ n, K n ≤ m)
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
    (hK : ∀ᶠ n : ℕ in atTop, 0 < K n)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)] :
    ∃ entryQ : ℝ≥0∞, 0 < entryQ ∧
      ∃ C : ℝ, C < 0 ∧ ∃ bridgeQ : ℝ≥0∞, 0 < bridgeQ ∧
        ∃ amplitude : ℝ, 0 < amplitude ∧
          ∀ᶠ n : ℕ in atTop,
            let pzMean := positiveASecondStagePZMean μ (D n) κ c v
            let A := secondStageEnoughRoots (K := K n) P hP generation n
            (RootIndexed.stepFieldLaw (Root := Fin m) μ)
              (A ∩
                RootIndexed.selectedSubtreeStepFieldVector
                    (secondStageRoots (hKm n) P hP generation n) ⁻¹'
                  positiveASecondStageFailureEvent (K n) (D n) κ c v) ≤
              (RootIndexed.stepFieldLaw (Root := Fin m) μ) A *
                ENNReal.ofReal (Real.exp (-((K n : ℝ) * pzMean.toReal / 4))) := by
  let chosen : ∀ n, RestartedField m → Fin (K n) →
      RootIndexed.TreeNode (Fin m) ℕ :=
    fun n => secondStageRoots (hKm n) P hP generation n
  let A : ℕ → Set (RestartedField m) :=
    fun n => secondStageEnoughRoots (K := K n) P hP generation n
  have hcount : ∀ n, (Set.range (chosen n)).Countable :=
    fun n => secondStageRoots_countable (hKm n) P hP generation n
  have hfiber : ∀ n roots, MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
        (generation n)]
      {field | chosen n field = roots} := by
    intro n roots
    exact measurableSet_secondStageRoots_eq (hKm n) P hP generation n roots
  have hdepth : ∀ n field i, (chosen n field i).2.length = generation n :=
    fun n field i => secondStageRoots_depth (hKm n) P hP generation n field i
  have hinj : ∀ n field, Function.Injective (chosen n field) :=
    fun n field => secondStageRoots_injective (hKm n) P hP generation n field
  have hA : ∀ n, MeasurableSet[
      RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
        (generation n)] (A n) := by
    intro n
    exact measurableSet_secondStageEnoughRoots P hP generation n
  obtain ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude, hamplitude,
      hbound⟩ :=
    eventually_measure_predictableSecondStageRoots_allAvoid_le
      (Root := Fin m) (m := K) (D := D) (generation := generation)
      hD μ hboundary hcross hν hsigma hκ hc hv hκv hterminal hentranceWidth hK
      (fun _ => inferInstance) (fun _ => inferInstance)
      chosen hcount hfiber hdepth hinj A hA
  refine ⟨entryQ, hentryQ, C, hC, bridgeQ, hbridgeQ, amplitude,
    hamplitude, ?_⟩
  filter_upwards [hbound] with n hboundN
  simpa [chosen, A, secondStageEnoughRoots] using hboundN

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
