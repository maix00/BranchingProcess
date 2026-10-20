/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity.Spine
import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
import Probability.Process.RandomWalk.Path.Restart.Basic
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Rate.LogScales
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Cutoff
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Window
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.PairBound

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.CapacityProbability
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.RandomWalkBounds

/-!
# Two-phase capacity interfaces

This module contains non-reusable intermediate statements in the proof of
the positive-initial-mass capacity estimate, Proposition 3.1, equation
(4.15), of Elie Aïdékon and Yueyun Hu, *Average-weight percolation on the
complete graph*, arXiv:2512.23266 (2025). The preceding module in the
`Lemmas/` chain supplies the definitions and estimates used here.

The declarations are theorem-specific reductions: they pass from the
restarted tube data to the estimates needed by the next stage of the proof.
Reusable path-event and measure inequalities remain in their semantic
modules outside this directory.

## Proof-chain statements

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHDrawdown_unitFirstStage` bounds the first-stage contribution by its number of generations and applies the Aïdékon--Hu drawdown estimate to the restarted stage.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.exists_measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHBothStages` supplies Aïdékon--Hu probability bounds to both phases and concludes the capacity estimate.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfHorizontalTubeBound` accepts a horizontal-tube probability input and derives the corresponding two-stage capacity-failure bound.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The first-stage generations in the two-phase estimate contribute only
their number of terms. Thus their path probabilities can be bounded by one,
leaving the Aïdékon--Hu estimate to control the restarted second stage. -/
lemma measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHDrawdown_unitFirstStage
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (hc : 0 < c) (hvc : v ≤ c)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma : ℝ}
    (hspine : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (target blockTarget p : ℝ)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      (delta0 ≤ c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) →
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro q hq
        rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then 1 else
            ENNReal.ofReal (Real.exp
              (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
              (if (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤
                  (((k : ℕ) - ell : ℕ) : ℝ) then
                ENNReal.ofReal (Real.exp
                  (-target * sigma ^ 2 * (((k : ℕ) - ell : ℕ) : ℝ) /
                    (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2))
              else 1)) / (N + 1 : ℕ)) := by
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) :=
    tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
  have hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ 1 := by
    intro k hk
    calc
      _ ≤ (tiltedIncrementFieldLaw realPotential μ) Set.univ := by
        unfold RandomWalk.restartedWindowProbability
        exact measure_mono (Set.subset_univ _)
      _ = 1 := htilted.measure_univ
  obtain ⟨delta0, hdelta0, hcapacity⟩ :=
    measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHDrawdown
      m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb hc hvc μ hboundary
      ν hν hspine hsigma hB hcontinuous hmeasurable target blockTarget p
      htarget htargetBlock hblockTarget hp (fun _ : ℕ => 1)
      (by
        intro k hk
        simpa using hfirstPath k hk)
  refine ⟨delta0, hdelta0, ?_⟩
  intro hscale
  simpa using hcapacity hscale

/-- Both phases of the killed-capacity estimate can be supplied by
the uniform Aïdékon--Hu bound.  The first phase uses its actual prefix
generation, while the restarted phase uses its actual post-cutoff length. -/
lemma exists_measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHBothStages
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (hc : 0 < c) (hvc : v ≤ c)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma : ℝ}
    (hspine : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (endpointRatio target blockTarget p : ℝ)
    (hEndpointRatio : 0 < endpointRatio)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2)
    (hp : 0 < p) :
    ∃ deltaFirst : ℝ,
      0 < deltaFirst ∧
      (deltaFirst ≤ b * logN →
        ∃ deltaSecond : ℝ, 0 < deltaSecond ∧
        (deltaSecond ≤ c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) →
        let firstWidth : ℝ := b * logN
        let spanWidth : ℝ := c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
        let pFirst : ℕ → ℝ≥0∞ := fun k =>
          if firstWidth ^ (2 + p) ≤ (k : ℝ) then
            ENNReal.ofReal (Real.exp
              (-target * sigma ^ 2 * (k : ℝ) / firstWidth ^ 2))
          else 1
        let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
        let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
        let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
          (fun _ : Fin m => (0 : ℝ)) id measurable_id
          (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
          (by
            intro q hq
            rcases RootIndexed.mem_initialPopulation_iff.mp hq with
              ⟨r, _hr, rfl⟩
            simp) ell window
          (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          upper (rightTailPositiveARestartedWindow_subset_Iic_upper
            ell ellN logN b v c κ)
        (RootIndexed.stepFieldLaw (Root := Fin m) μ)
          (P.capacityEvent N ellN)ᶜ ≤
          (m : ℝ≥0∞) *
            (∑ k : Fin (ellN + 1),
              if (k : ℕ) ≤ ell then pFirst (k : ℕ) else
                ENNReal.ofReal (Real.exp
                  (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                    rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
                (if spanWidth ^ (2 + p) ≤
                    (((k : ℕ) - ell : ℕ) : ℝ) then
                  ENNReal.ofReal (Real.exp
                    (-target * sigma ^ 2 * (((k : ℕ) - ell : ℕ) : ℝ) /
                      spanWidth ^ 2))
                else 1)) / (N + 1 : ℕ))) := by
  obtain ⟨deltaFirst, hdeltaFirst, hfirstAH⟩ :=
    exists_uniform_iidSequenceLaw_firstStageCorridor_le_ah
      ν hspine hsigma hB hcontinuous hmeasurable endpointRatio target
      blockTarget p hEndpointRatio htarget htargetBlock hblockTarget hp
  refine ⟨deltaFirst, hdeltaFirst, ?_⟩
  intro hfirstWidth
  have hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤
      if (b * logN) ^ (2 + p) ≤ (k : ℝ) then
        ENNReal.ofReal (Real.exp
          (-target * sigma ^ 2 * (k : ℝ) / (b * logN) ^ 2))
      else 1 := by
    intro k hk
    have hsubset := rightTailPositiveARestartedWindow_event_subset_firstStagePrefix
      ell ellN (k : ℕ) logN b v c κ hlog hvb hk
    rw [show tiltedIncrementFieldLaw realPotential μ = iidSequenceLaw ν by
      rw [hν]
      rfl]
    by_cases hlong : (b * logN) ^ (2 + p) ≤ (k : ℝ)
    · have hwidthPos : 0 < b * logN := lt_of_lt_of_le hdeltaFirst hfirstWidth
      have hcorridor := hfirstAH (k : ℕ) (b * logN) hwidthPos hfirstWidth hlong
      unfold RandomWalk.restartedWindowProbability
      have hlower : -(b * logN) = -b * logN := by ring
      rw [hlower] at hcorridor
      simpa [hlong, neg_mul] using (measure_mono hsubset).trans hcorridor
    · have hprob :
          RandomWalk.restartedWindowProbability (iidSequenceLaw ν) ell
            (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
            (k : ℕ) 0 ≤ 1 := by
        unfold RandomWalk.restartedWindowProbability
        calc
          _ ≤ (iidSequenceLaw ν) Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      simpa [hlong] using hprob
  obtain ⟨deltaSecond, hdeltaSecond, hcapacity⟩ :=
    measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHDrawdown
      m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb hc hvc μ hboundary
      ν hν hspine hsigma hB hcontinuous hmeasurable target blockTarget p
      htarget htargetBlock hblockTarget hp (fun k =>
        if (b * logN) ^ (2 + p) ≤ (k : ℝ) then
          ENNReal.ofReal (Real.exp
            (-target * sigma ^ 2 * (k : ℝ) / (b * logN) ^ 2))
        else 1) hfirstPath
  refine ⟨deltaSecond, hdeltaSecond, ?_⟩
  intro hsecondWidth
  have hbound := hcapacity hsecondWidth
  simpa using hbound

/-- The two-stage capacity estimate now accepts a one-stage horizontal-tube
bound as its remaining random-walk input. -/
lemma measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfHorizontalTubeBound
    (m ell ellN N : ℕ) (logN b v c κ a : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (pSecond : ℝ≥0∞)
    (hhorizontal : horizontalTubeProbability
      (tiltedIncrementFieldLaw realPotential μ) a (b * logN / a) ell ≤ pSecond) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro q hq
        rcases RootIndexed.mem_initialPopulation_iff.mp hq with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (((ell + 1 : ℕ) : ℝ≥0∞) +
          ((ellN - ell : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp
              ((-b + v) * logN + (κ / c ^ 2 + max c v) *
                (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) * pSecond)) /
          (N + 1 : ℕ) := by
  have hprefix :
      (tiltedIncrementFieldLaw realPotential μ)
        {increment : ℕ → ℝ |
          InClosedInterval (-b * logN) 0 ell 0 increment} ≤ pSecond :=
    (rightTailPositiveA_firstStage_probability_le_horizontalTubeProbability
      ell logN b a hb hlog ha ha1 (tiltedIncrementFieldLaw realPotential μ)).trans
        hhorizontal
  exact measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfFirstStageBound
    m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb μ hboundary
    pSecond hprefix

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
