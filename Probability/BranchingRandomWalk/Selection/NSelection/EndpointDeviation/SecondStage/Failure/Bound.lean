/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Population
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Tube
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Roots.Selection
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Failure.Lemmas.Decomposition
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.IndependentEventCount

/-!
# Terminal failure after the second-stage restart

## Public declarations

* `measure_positiveASelectedBRWTerminalEmpty_le_of_survival`: if $A$ is the event that
  at least $K$ particles reach the first cutoff and $q$ bounds the
  descendant-corridor success probability from below, then
  $\mathbb P(P_H=\varnothing)\le\mathbb P(A^c)+\exp(-Kq)$.

This is the independent-descendant step in the $0<a<1$ case of Theorem 1.1
in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 4.
-/

open Filter MeasureTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- At the first cutoff, the $K$ chosen subtrees are independent with the
one-root law, conditional on the generation filtration. This gives the
terminal-failure bound used in the $0<a<1$ case of Theorem 1.1 in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4. -/
theorem measure_positiveASelectedBRWTerminalEmpty_le_of_survival
    (m K ell H : ℕ) (hKm : K ≤ m)
    (logN b v c κ : ℝ) (hell : 0 < ell) (hellH : ell ≤ H)
    (hstart : 0 ≤ b * logN)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (q : ℝ) (hq : 0 ≤ q)
    (hsurvive : q ≤ (offspringFieldLaw μ).real
      (hasPathHistoryIn (ι := ℕ) realPotential (H - ell) 0
        (positiveASecondStageCorridor (H - ell) κ c v))) :
    let P := positiveASelectedBRWPopulation m ell H logN b v c κ
    let A := positiveASelectedBRWEnoughRootEvent m K ell H logN b v c κ
    (finiteRootStepFieldLaw μ m) {field | ¬ (P H field).Nonempty} ≤
      (finiteRootStepFieldLaw μ m) Aᶜ + ENNReal.ofReal (Real.exp (-(K : ℝ) * q)) := by
  let P := positiveASelectedBRWPopulation m ell H logN b v c κ
  let slices := positiveASelectedBRWPopulation_finiteSlices m ell H logN b v c κ
  let A := positiveASelectedBRWEnoughRootEvent m K ell H logN b v c κ
  let chosen := secondStageRoots hKm (fun _ : ℕ => P) (fun _ : ℕ => slices) (fun _ => ell) 0
  let D := H - ell
  let E := hasPathHistoryIn (ι := ℕ) realPotential D 0 (positiveASecondStageCorridor D κ c v)
  let failure := positiveASecondStageFailureEvent K D κ c v
  have hE : MeasurableSet E :=
    measurableSet_hasPathHistoryIn realPotential D 0 _
      (measurableSet_affineCorridorThrough D 0 _ _ _)
  have hfailure : MeasurableSet failure := by
    have heq : failure = ⋂ i : Fin K,
        (fun field : FiniteRootStepField K ℕ ℝ => field i) ⁻¹' Eᶜ := by
      ext field
      simp [failure, positiveASecondStageFailureEvent, E]
    rw [heq]
    exact MeasurableSet.iInter fun i => hE.compl.preimage (measurable_pi_apply i)
  have hfactor := RootIndexed.selectedSubtreeStepFieldVector_event_factorization
    μ chosen (secondStageRoots_countable hKm _ _ _ 0)
    (fun roots => measurableSet_secondStageRoots_eq hKm _ _ _ 0 roots)
    (secondStageRoots_depth hKm _ _ _ 0) (secondStageRoots_injective hKm _ _ _ 0)
    A failure (measurableSet_secondStageEnoughRoots
      (K := K) (fun _ : ℕ => P) (fun _ : ℕ => slices) (fun _ => ell) 0) hfailure
  have hprob := measure_finiteRootEventAvoidance_le_exp μ E hE K q hq
    (hsurvive.trans measureReal_le_one) hsurvive
  have hdecomp := measure_positiveASelectedBRWTerminalEmpty_le
    m K ell H hKm logN b v c κ hell hellH hstart μ hboundary
  change (finiteRootStepFieldLaw μ m) {field | ¬ (P H field).Nonempty} ≤ _
  calc
    _ ≤ (finiteRootStepFieldLaw μ m) Aᶜ +
        (finiteRootStepFieldLaw μ m)
          (A ∩ RootIndexed.selectedSubtreeStepFieldVector chosen ⁻¹' failure) := hdecomp
    _ = (finiteRootStepFieldLaw μ m) Aᶜ +
        (finiteRootStepFieldLaw μ m) A * (finiteRootStepFieldLaw μ K) failure := by rw [hfactor]
    _ ≤ (finiteRootStepFieldLaw μ m) Aᶜ + ENNReal.ofReal (Real.exp (-(K : ℝ) * q)) :=
      add_le_add le_rfl ((show (finiteRootStepFieldLaw μ m) A *
          (finiteRootStepFieldLaw μ K) failure ≤
        (finiteRootStepFieldLaw μ m) A * ENNReal.ofReal (Real.exp (-(K : ℝ) * q)) by
          gcongr
          exact hprob).trans
        (mul_le_of_le_one_left' prob_le_one))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
