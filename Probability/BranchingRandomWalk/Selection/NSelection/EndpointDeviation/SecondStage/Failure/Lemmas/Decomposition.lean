/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Population
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Lemmas.Population.Transfer
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Tube
import all Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.SecondStage.Roots.Selection
import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
/-!
# Decomposing terminal selected-population emptiness

## Internal proof declarations


These two event-decomposition lemmas are used only to prove the quantitative
terminal-failure estimate in `Failure/Bound.lean`.

`positiveASelectedBRWTerminalEmpty_subset_lowRoots_or_allAvoid` gives,
almost surely under the root-indexed field law, the inclusion
  \[
  \{\text{terminal selected BRW population is empty}\}
  \subseteq A^c\cup(A\cap\{\text{all chosen second-stage paths fail}\}),
  \]
where `A` is the event that at least `K` roots survive to the first-stage
generation. The inclusion assumes `K ≤ m`, `0 < ell ≤ ellN`, the stated
starting-position bound, and boundary normalization.

`measure_positiveASelectedBRWTerminalEmpty_le` gives the corresponding
probability bound
  \[
  \mathbb P(\text{terminal population empty})
  \le \mathbb P(A^c)+
      \mathbb P(A\cap\{\text{all chosen second-stage paths fail}\}).
  \]

If the terminal selected BRW slice is empty while the earlier slice contains enough
roots, every selected descendant tree must fail its second-stage corridor.
This turns the pathwise embedding into a probability decomposition that can
be combined with the predictable-root estimate.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- On the event that the first selected BRW slice has at least K particles,
terminal extinction forces all selected descendant fields to miss the
second-stage corridor, outside the boundary-normalization null set. -/
lemma positiveASelectedBRWTerminalEmpty_subset_lowRoots_or_allAvoid
    (m K ell ellN : ℕ) (hKm : K ≤ m)
    (logN b v c κ : ℝ) (hell : 0 < ell) (hellN : ell ≤ ellN)
    (hstart : 0 ≤ b * logN)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    let P := positiveASelectedBRWPopulation m ell ellN logN b v c κ
    let hP := positiveASelectedBRWPopulation_finiteSlices
      m ell ellN logN b v c κ
    let A := secondStageEnoughRoots (K := K)
      (fun _ : ℕ => P) (fun _ : ℕ => hP) (fun _ => ell) 0
    let chosen := secondStageRoots hKm
      (fun _ : ℕ => P) (fun _ : ℕ => hP) (fun _ => ell)
    let failure := positiveASecondStageFailureEvent
      K (ellN - ell) κ c v
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Fin m) μ,
      field ∈ {field | ¬ (P ellN field).Nonempty} →
        field ∈ (Aᶜ ∪ (A ∩
          RootIndexed.selectedSubtreeStepFieldVector (chosen 0) ⁻¹' failure)) := by
  classical
  dsimp
  let P := positiveASelectedBRWPopulation m ell ellN logN b v c κ
  let hP : P.FiniteSlices :=
    positiveASelectedBRWPopulation_finiteSlices m ell ellN logN b v c κ
  let generation : ℕ → ℕ := fun _ => ell
  let A : Set (RestartedField m) :=
    secondStageEnoughRoots (K := K) (fun _ => P) (fun _ => hP)
      generation 0
  let chosen := secondStageRoots hKm
    (fun _ : ℕ => P) (fun _ : ℕ => hP) generation
  let failure := positiveASecondStageFailureEvent
    K (ellN - ell) κ c v
  let terminalEmpty : Set (RestartedField m) :=
    {field | ¬ (P ellN field).Nonempty}
  have hweight := RootIndexed.stepFieldLaw_ae_real_weight_finite_on_roots
    μ hboundary (Finset.univ : Finset (Fin m))
  filter_upwards [hweight] with field hweight
  intro hempty
  by_cases hA : field ∈ A
  · right
    refine ⟨hA, ?_⟩
    have hcard : K ≤ (hP.toFinset ell field).card := by
      simpa [A, generation, secondStageEnoughRoots] using hA
    have hallfail :
        RootIndexed.selectedSubtreeStepFieldVector (chosen 0) field ∈ failure := by
      by_contra hnotfail
      have hsuccess : ∃ i : Fin K,
          RootIndexed.selectedSubtreeStepFieldVector (chosen 0) field i ∈
            hasPathHistoryIn (ι := ℕ) realPotential (ellN - ell) 0
              (positiveASecondStageCorridor (ellN - ell) κ c v) := by
        simpa [failure, chosen, positiveASecondStageFailureEvent,
          secondStageRoots, positiveASecondStageCorridor] using
          hnotfail
      have hterminal := positiveASecondStage_success_of_enoughRoots
        m K ell ellN hKm logN b v c κ hell hellN hstart field hcard
        (by simpa [chosen, generation] using hsuccess)
        (fun r z => hweight r (Finset.mem_univ r) z)
      exact hempty hterminal
    exact hallfail
  · left
    exact hA

/-- Terminal extinction is bounded by the first-stage low-root event plus the
event that enough selected roots all fail their independent second-stage
corridor. This is the event decomposition preceding the quantitative
first-stage and capacity estimates in the positive-a proof. -/
lemma measure_positiveASelectedBRWTerminalEmpty_le
    (m K ell ellN : ℕ) (hKm : K ≤ m)
    (logN b v c κ : ℝ) (hell : 0 < ell) (hellN : ell ≤ ellN)
    (hstart : 0 ≤ b * logN)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    let P := positiveASelectedBRWPopulation m ell ellN logN b v c κ
    let hP := positiveASelectedBRWPopulation_finiteSlices
      m ell ellN logN b v c κ
    let A := secondStageEnoughRoots (K := K)
      (fun _ : ℕ => P) (fun _ : ℕ => hP) (fun _ => ell) 0
    let chosen := secondStageRoots hKm
      (fun _ : ℕ => P) (fun _ : ℕ => hP) (fun _ => ell)
    let failure := positiveASecondStageFailureEvent
      K (ellN - ell) κ c v
    (RootIndexed.stepFieldLaw (Root := Fin m) μ)
        {field | ¬ (P ellN field).Nonempty} ≤
      (RootIndexed.stepFieldLaw (Root := Fin m) μ) Aᶜ +
        (RootIndexed.stepFieldLaw (Root := Fin m) μ)
      (A ∩ RootIndexed.selectedSubtreeStepFieldVector (chosen 0) ⁻¹'
        failure) := by
  classical
  dsimp
  let P := positiveASelectedBRWPopulation m ell ellN logN b v c κ
  let hP : P.FiniteSlices :=
    positiveASelectedBRWPopulation_finiteSlices m ell ellN logN b v c κ
  let generation : ℕ → ℕ := fun _ => ell
  let A : Set (RestartedField m) :=
    secondStageEnoughRoots (K := K) (fun _ => P) (fun _ => hP)
      generation 0
  let chosen := secondStageRoots hKm
    (fun _ : ℕ => P) (fun _ : ℕ => hP) generation
  let failure := positiveASecondStageFailureEvent
    K (ellN - ell) κ c v
  let terminalEmpty : Set (RestartedField m) :=
    {field | ¬ (P ellN field).Nonempty}
  have hsubset :=
    positiveASelectedBRWTerminalEmpty_subset_lowRoots_or_allAvoid
      m K ell ellN hKm logN b v c κ hell hellN hstart μ hboundary
  calc
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) terminalEmpty ≤
        (RootIndexed.stepFieldLaw (Root := Fin m) μ)
          (Aᶜ ∪ (A ∩
            RootIndexed.selectedSubtreeStepFieldVector (chosen 0) ⁻¹'
              failure)) := measure_mono_ae hsubset
    _ ≤ (RootIndexed.stepFieldLaw (Root := Fin m) μ) Aᶜ +
          (RootIndexed.stepFieldLaw (Root := Fin m) μ)
            (A ∩ RootIndexed.selectedSubtreeStepFieldVector (chosen 0) ⁻¹'
              failure) := measure_union_le _ _

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
