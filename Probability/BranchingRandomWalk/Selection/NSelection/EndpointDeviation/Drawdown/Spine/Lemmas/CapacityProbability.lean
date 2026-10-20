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

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.Asymptotics

/-!
# Capacity probability combinations

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

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHDrawdown` and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHDrawdown_canceled` combine the two-stage Markov estimate with drawdown bounds, retaining or cancelling the Aïdékon--Hu generation sum.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHPolynomialInput_of_uniformAH` and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHPolynomialInput` give polynomial capacity-failure bounds from the uniform and generation-wise Aïdékon--Hu inputs.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.eventually_probability_le_polynomial_of_canceledAH_capacity_bound` converts the canceled estimate into the eventual bound $\mathbb P(\text{capacity failure})\leq N^{-p}$.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- Insert the uniform Aïdékon--Hu estimate into the two-stage capacity
bound. Long second-stage prefixes use the exponential drawdown estimate;
short prefixes use only that their probability is at most one. This is the
finite-parameter form of the second-stage estimate in the proof of (4.15). -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHDrawdown
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
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p)
    (pFirst : ℕ → ℝ≥0∞)
    (hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pFirst (k : ℕ)) :
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
          if (k : ℕ) ≤ ell then pFirst (k : ℕ) else
            ENNReal.ofReal (Real.exp
              (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
              (if (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤
                  (((k : ℕ) - ell : ℕ) : ℝ) then
                ENNReal.ofReal (Real.exp
                  (-target * sigma ^ 2 * (((k : ℕ) - ell : ℕ) : ℝ) /
                    (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2))
              else 1)) / (N + 1 : ℕ)) := by
  obtain ⟨delta0', hdelta0', hAH⟩ :=
    iidSequenceLaw_rightTailPositiveASecondStageDrawdown_le_of_ah
      ν hspine hsigma hB hcontinuous hmeasurable κ c target blockTarget p
      hκ hc htarget htargetBlock hblockTarget hp
  refine ⟨delta0', hdelta0', ?_⟩
  intro hscale
  let width : ℝ := c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hwidthLarge : delta0' ≤ width := by simpa [width] using hscale
  let pSecond : ℕ → ℝ≥0∞ := fun k =>
    if width ^ (2 + p) ≤ ((k - ell : ℕ) : ℝ) then
      ENNReal.ofReal (Real.exp
        (-target * sigma ^ 2 * ((k - ell : ℕ) : ℝ) / width ^ 2))
    else 1
  have hdrawdown : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      iidSequenceLaw ν
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          ((k : ℕ) - ell) width
          (rightTailPositiveADrift ell ellN κ c ((k : ℕ) - ell) + width)) ≤
        pSecond (k : ℕ) := by
    intro k hk
    have hkN : (k : ℕ) ≤ ellN := by omega
    have hd : (k : ℕ) - ell ≤ ellN - ell := by omega
    by_cases hlong : width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ)
    · have hbound := hAH ell ellN ((k : ℕ) - ell) hellN hd hwidthLarge hlong
      simpa [pSecond, width, hlong] using hbound
    · have hprob : iidSequenceLaw ν
          (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
            ((k : ℕ) - ell) width
            (rightTailPositiveADrift ell ellN κ c ((k : ℕ) - ell) + width)) ≤ 1 := by
        calc
          _ ≤ iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      simpa [pSecond, width, hlong] using hprob
  have hcap :=
    measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfDrawdownBounds
      m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb hc hvc μ hboundary
      ν hν pFirst pSecond hfirstPath hdrawdown
  simpa [pSecond, width] using hcap

/-- With `κ` chosen as the Aïdékon--Hu rate coefficient, long-prefix terms
in the capacity sum reduce to the first-stage offset plus one tube width.
Only short prefixes retain their generation-specific endpoint weight. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHDrawdown_canceled
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
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p)
    (pFirst : ℕ → ℝ≥0∞)
    (hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pFirst (k : ℕ))
    (hκrate : κ = target * sigma ^ 2) :
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
          if (k : ℕ) ≤ ell then pFirst (k : ℕ) else
            if (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤
                (((k : ℕ) - ell : ℕ) : ℝ) then
              ENNReal.ofReal (Real.exp
                ((-b + v) * logN +
                  c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))))
            else ENNReal.ofReal (Real.exp
              (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)))) /
          (N + 1 : ℕ)) := by
  obtain ⟨delta0, hdelta0, hcapacity⟩ :=
    measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHDrawdown
      m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb hc hvc μ hboundary
      ν hν hspine hsigma hB hcontinuous hmeasurable target blockTarget p
      htarget htargetBlock hblockTarget hp pFirst hfirstPath
  refine ⟨delta0, hdelta0, ?_⟩
  intro hscale
  have hbound := hcapacity hscale
  let width : ℝ := c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hsum :
      (∑ k : Fin (ellN + 1),
        if (k : ℕ) ≤ ell then pFirst (k : ℕ) else
          ENNReal.ofReal (Real.exp
            (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
              rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
            (if width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ) then
              ENNReal.ofReal (Real.exp
                (-target * sigma ^ 2 * (((k : ℕ) - ell : ℕ) : ℝ) /
                  width ^ 2))
            else 1)) ≤
      ∑ k : Fin (ellN + 1),
        if (k : ℕ) ≤ ell then pFirst (k : ℕ) else
          if width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ) then
            ENNReal.ofReal (Real.exp
              ((-b + v) * logN + width))
          else ENNReal.ofReal (Real.exp
            (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
              rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) := by
    apply Finset.sum_le_sum
    intro k _hk
    by_cases hkle : (k : ℕ) ≤ ell
    · simp [hkle]
    · have hk : ell < (k : ℕ) := Nat.lt_of_not_ge hkle
      by_cases hlong : width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ)
      · have hcancel := rightTailPositiveAWindowWeightedAH_le
          ell ellN (k : ℕ) logN b v c κ target sigma hellN hvc hc hk
          (by omega) hκrate
        simpa [width, Nat.not_le_of_gt hk, hlong] using hcancel
      · simp [width, Nat.not_le_of_gt hk, hlong]
  calc
    _ ≤ (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then pFirst (k : ℕ) else
            ENNReal.ofReal (Real.exp
              (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
              (if width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ) then
                ENNReal.ofReal (Real.exp
                  (-target * sigma ^ 2 * (((k : ℕ) - ell : ℕ) : ℝ) /
                    width ^ 2))
              else 1)) / (N + 1 : ℕ) := by
          simpa [width] using hbound
    _ ≤ (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then pFirst (k : ℕ) else
            if width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ) then
              ENNReal.ofReal (Real.exp ((-b + v) * logN + width))
            else ENNReal.ofReal (Real.exp
              (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)))) /
          (N + 1 : ℕ) := by
          apply ENNReal.div_le_div_right
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by simp [width]

/-- The polynomial killed-capacity estimate with an externally supplied
uniform Aïdékon--Hu threshold.  Keeping the threshold explicit lets the
logarithmic-scale argument use one value for every sample size. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHPolynomialInput_of_uniformAH
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
    {sigma : ℝ} (target p : ℝ) (hκrate : κ = target * sigma ^ 2)
    (delta0 : ℝ)
    (hAH : ∀ ell' ellN' d : ℕ, ell' < ellN' → d ≤ ellN' - ell' →
      delta0 ≤ c * (((ellN' - ell' : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) →
      (c * (((ellN' - ell' : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤ (d : ℝ) →
      iidSequenceLaw ν
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          d (c * (((ellN' - ell' : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
          (rightTailPositiveADrift ell' ellN' κ c d +
            c * (((ellN' - ell' : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) ≤
        ENNReal.ofReal (Real.exp
          (-target * sigma ^ 2 * (d : ℝ) /
            (c * (((ellN' - ell' : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2)))
    (hscale : delta0 ≤ c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
    :
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
            ENNReal.ofReal (Real.exp
              ((-b + v) * logN +
                c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) +
                κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3))))) /
          (N + 1 : ℕ) := by
  let width : ℝ := c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) :=
    tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
  have hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ 1 := by
    intro k _hk
    calc
      _ ≤ (tiltedIncrementFieldLaw realPotential μ) Set.univ := by
        unfold RandomWalk.restartedWindowProbability
        exact measure_mono (Set.subset_univ _)
      _ = 1 := htilted.measure_univ
  let pSecond : ℕ → ℝ≥0∞ := fun k =>
    if width ^ (2 + p) ≤ ((k - ell : ℕ) : ℝ) then
      ENNReal.ofReal (Real.exp
        (-target * sigma ^ 2 * ((k - ell : ℕ) : ℝ) / width ^ 2))
    else 1
  have hdrawdown : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      iidSequenceLaw ν
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          ((k : ℕ) - ell) width
          (rightTailPositiveADrift ell ellN κ c ((k : ℕ) - ell) + width)) ≤
        pSecond (k : ℕ) := by
    intro k hk
    have hkN : (k : ℕ) ≤ ellN := by omega
    have hd : (k : ℕ) - ell ≤ ellN - ell := by omega
    by_cases hlong : width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ)
    · have hbound := hAH ell ellN ((k : ℕ) - ell) hellN hd
        (by simpa [width] using hscale) (by simpa [width] using hlong)
      simpa [pSecond, width, hlong] using hbound
    · have hprob : iidSequenceLaw ν
          (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
            ((k : ℕ) - ell) width
            (rightTailPositiveADrift ell ellN κ c ((k : ℕ) - ell) + width)) ≤ 1 := by
        calc
          _ ≤ iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      simpa [pSecond, width, hlong] using hprob
  have hcapacity :=
    measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfDrawdownBounds
      m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb hc hvc μ hboundary
      ν hν (fun _ : ℕ => 1) pSecond hfirstPath hdrawdown
  have hsum :
      (∑ k : Fin (ellN + 1),
        if (k : ℕ) ≤ ell then 1 else
          ENNReal.ofReal (Real.exp
            (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
              rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
            (if width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ) then
              ENNReal.ofReal (Real.exp
                (-target * sigma ^ 2 * (((k : ℕ) - ell : ℕ) : ℝ) / width ^ 2))
            else 1)) ≤
      ((ell + 1 : ℕ) : ℝ≥0∞) +
        ((ellN - ell : ℕ) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp
            ((-b + v) * logN + width +
              κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3)))) := by
    calc
      _ ≤ ∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then 1 else
            if width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ) then
              ENNReal.ofReal (Real.exp ((-b + v) * logN + width))
            else ENNReal.ofReal (Real.exp
              (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) := by
        apply Finset.sum_le_sum
        intro k _hk
        by_cases hkle : (k : ℕ) ≤ ell
        · simp [hkle]
        · have hk : ell < (k : ℕ) := Nat.lt_of_not_ge hkle
          by_cases hlong : width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ)
          · have hcancel := rightTailPositiveAWindowWeightedAH_le
              ell ellN (k : ℕ) logN b v c κ target sigma hellN hvc hc hk
              (by omega) hκrate
            simpa [width, Nat.not_le_of_gt hk, hlong] using hcancel
          · have hd : (((k : ℕ) - ell : ℕ) : ℝ) ≤ width ^ (2 + p) :=
              le_of_not_ge hlong
            have hdrift := rightTailPositiveADrift_le_shortPrefix_power
              ell ellN ((k : ℕ) - ell) κ c p hellN hκ hc
                (by simpa [width] using hd)
            have hupper := rightTailPositiveAWindowUpper_le_generationDrift_add_width
              ell ellN (k : ℕ) logN b v c κ hellN hvc hk (by omega)
            have hcutoff := rightTailPositiveAWindowUpper_at_cutoff
              ell ellN logN b v c κ
            have hexponent :
                rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                  rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ) ≤
                (-b + v) * logN + width +
                  κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3)) := by
              rw [hcutoff]
              dsimp [width]
              linarith
            simpa [hkle, hlong, width] using
              (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent))
      _ ≤ _ := by
        simpa [width] using rightTailPositiveA_canceledAH_sum_le
          ell ellN logN b v c κ p hellN hκ hc hvc
  calc
    _ ≤ (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then 1 else
            ENNReal.ofReal (Real.exp
              (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
              (if width ^ (2 + p) ≤ (((k : ℕ) - ell : ℕ) : ℝ) then
                ENNReal.ofReal (Real.exp
                  (-target * sigma ^ 2 * (((k : ℕ) - ell : ℕ) : ℝ) / width ^ 2))
              else 1)) / (N + 1 : ℕ) := by
          simpa [pSecond, width] using hcapacity
    _ ≤ (m : ℝ≥0∞) *
        (((ell + 1 : ℕ) : ℝ≥0∞) +
          ((ellN - ell : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp
              ((-b + v) * logN + width +
                κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3))))) /
          (N + 1 : ℕ) := by
          apply ENNReal.div_le_div_right
          exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by simp [width]

/-- Combining the generation-wise capacity estimate with the canceled AH sum
gives the finite-scale bound used for the first term in (4.15). -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHPolynomialInput
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
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2)
    (hp : 0 < p)
    (hκrate : κ = target * sigma ^ 2) :
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
        (((ell + 1 : ℕ) : ℝ≥0∞) +
          ((ellN - ell : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp
              ((-b + v) * logN +
                c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) +
                κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3))))) /
          (N + 1 : ℕ)) := by
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) :=
    tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
  have hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ 1 := by
    intro k _hk
    calc
      _ ≤ (tiltedIncrementFieldLaw realPotential μ) Set.univ := by
        unfold RandomWalk.restartedWindowProbability
        exact measure_mono (Set.subset_univ _)
      _ = 1 := htilted.measure_univ
  obtain ⟨delta0, hdelta0, hcapacity⟩ :=
    measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfAHDrawdown_canceled
      m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb hc hvc μ hboundary
      ν hν hspine hsigma hB hcontinuous hmeasurable target blockTarget p
      htarget htargetBlock hblockTarget hp (fun _ : ℕ => 1) hfirstPath hκrate
  refine ⟨delta0, hdelta0, ?_⟩
  intro hscale
  have hbound := hcapacity hscale
  have hsum := rightTailPositiveA_canceledAH_sum_le
    ell ellN logN b v c κ p hellN hκ hc hvc
  calc
    _ ≤ (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then 1 else
            if (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤
                (((k : ℕ) - ell : ℕ) : ℝ) then
              ENNReal.ofReal (Real.exp
                ((-b + v) * logN +
                  c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))))
            else ENNReal.ofReal (Real.exp
              (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
                rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)))) /
          (N + 1 : ℕ) := by
          simpa using hbound
    _ ≤ (m : ℝ≥0∞) *
        (((ell + 1 : ℕ) : ℝ≥0∞) +
          ((ellN - ell : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp
              ((-b + v) * logN +
                c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) +
                κ * c ^ p * (((ellN - ell : ℕ) : ℝ) ^ (p / 3))))) /
          (N + 1 : ℕ) := by
          apply ENNReal.div_le_div_right
          exact mul_le_mul_of_nonneg_left hsum (by positivity)


/-- The finite-scale canceled-AH capacity estimate has polynomial decay when
the initial root count has exponent `a`, the two multiplicity factors have
subexponential size, and the combined exponent `a + q` is below one. -/
theorem eventually_probability_le_polynomial_of_canceledAH_capacity_bound
    {P : ℕ → ℝ≥0∞} {m ell ellN N : ℕ → ℕ} {E : ℕ → ℝ} {a q : ℝ}
    (hN : Tendsto N atTop atTop)
    (horder : ∀ᶠ n : ℕ in atTop, ell n ≤ ellN n)
    (hfirstCountLog : Tendsto
      (fun n => Real.log ((ellN n : ℝ) + 1) / Real.log (N n : ℝ))
      atTop (𝓝 0))
    (hspanCountLog : Tendsto
      (fun n => Real.log (((ellN n - ell n : ℕ) : ℝ) + 1) /
        Real.log (N n : ℝ)) atTop (𝓝 0))
    (hERate : Tendsto (fun n => E n / Real.log (N n : ℝ)) atTop (𝓝 q))
    (ha : a < 1) (hmargin : a + q < 1)
    (hm : ∀ᶠ n : ℕ in atTop, (m n : ℝ) ≤ (N n : ℝ) ^ a)
    (hraw : ∀ᶠ n : ℕ in atTop,
      P n ≤ (m n : ℝ≥0∞) *
        (((ell n + 1 : ℕ) : ℝ≥0∞) +
          ((ellN n - ell n : ℕ) : ℝ≥0∞) *
            ENNReal.ofReal (Real.exp (E n))) /
        (N n + 1 : ℕ)) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ᶠ n : ℕ in atTop,
      P n ≤ ENNReal.ofReal
        (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
  let L : ℕ → ℝ := fun n => Real.log (N n : ℝ)
  let D : ℕ → ℕ := fun n => ellN n - ell n
  have hNcast : Tendsto (fun n => (N n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have hL : Tendsto L atTop atTop := Real.tendsto_log_atTop.comp hNcast
  have hLpos : ∀ᶠ n : ℕ in atTop, 0 < L n := hL.eventually_gt_atTop 0
  have hfirstRate : Tendsto
      (fun n => (a * L n + Real.log ((ellN n : ℝ) + 1)) / L n)
      atTop (𝓝 a) := by
    have haConst : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
    have hsum := haConst.add (by simpa [L] using hfirstCountLog)
    have heq : (fun n => (a * L n + Real.log ((ellN n : ℝ) + 1)) / L n)
        =ᶠ[atTop] fun n => a + Real.log ((ellN n : ℝ) + 1) / L n := by
      filter_upwards [hLpos] with n hn
      field_simp
    simpa using hsum.congr' heq.symm
  have hsecondRate : Tendsto
      (fun n => (a * L n + Real.log ((D n : ℝ) + 1) + E n) / L n)
      atTop (𝓝 (a + q)) := by
    have haConst : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) := tendsto_const_nhds
    have hsum := (haConst.add (by simpa [L, D] using hspanCountLog)).add
      (by simpa [L] using hERate)
    have heq :
        (fun n => (a * L n + Real.log ((D n : ℝ) + 1) + E n) / L n)
          =ᶠ[atTop] fun n => a + Real.log ((D n : ℝ) + 1) / L n + E n / L n := by
      filter_upwards [hLpos] with n hn
      field_simp
    simpa using hsum.congr' heq.symm
  let epsilon : ℝ := min (1 - a) (1 - (a + q)) / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    positivity
  have hfirstRateGap : a < 1 - 2 * epsilon := by
    dsimp [epsilon]
    have hmin : min (1 - a) (1 - (a + q)) ≤ 1 - a := min_le_left _ _
    linarith
  have hsecondRateGap : a + q < 1 - 2 * epsilon := by
    dsimp [epsilon]
    have hmin : min (1 - a) (1 - (a + q)) ≤ 1 - (a + q) :=
      min_le_right _ _
    linarith
  have hfirstRateEvent : ∀ᶠ n : ℕ in atTop,
      (a * L n + Real.log ((ellN n : ℝ) + 1)) / L n < 1 - 2 * epsilon :=
    hfirstRate.eventually (Iio_mem_nhds hfirstRateGap)
  have hsecondRateEvent : ∀ᶠ n : ℕ in atTop,
      (a * L n + Real.log ((D n : ℝ) + 1) + E n) / L n <
        1 - 2 * epsilon :=
    hsecondRate.eventually (Iio_mem_nhds hsecondRateGap)
  have hlogLarge : ∀ᶠ n : ℕ in atTop, Real.log 2 < epsilon * L n := by
    have hmul : Tendsto (fun n => epsilon * L n) atTop atTop :=
      hL.const_mul_atTop hepsilon
    exact hmul.eventually_gt_atTop (Real.log 2)
  have hpowN : ∀ᶠ n : ℕ in atTop, (N n : ℝ) = Real.exp (L n) := by
    filter_upwards [hLpos] with n hn
    have hnNat : 0 < N n := by
      by_contra h
      have hz : N n = 0 := Nat.eq_zero_of_not_pos h
      simp [L, hz] at hn
    have hnReal : 0 < (N n : ℝ) := by exact_mod_cast hnNat
    simpa [L] using (Real.exp_log hnReal).symm
  refine ⟨epsilon, hepsilon, ?_⟩
  filter_upwards [hraw, horder, hm, hfirstRateEvent, hsecondRateEvent,
    hlogLarge, hLpos, hpowN] with n hrawn hord hmn hrateFirst hrateSecond
      hlogLarg hLn hpowNn
  have hNpos : 0 < (N n : ℝ) := by
    have hnNat : 0 < N n := by
      by_contra h
      have hz : N n = 0 := Nat.eq_zero_of_not_pos h
      simp [L, hz] at hLn
    exact_mod_cast hnNat
  have hmENN : (m n : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (a * L n)) := by
    calc
      (m n : ℝ≥0∞) = ENNReal.ofReal (m n : ℝ) :=
        (ENNReal.ofReal_natCast (m n)).symm
      _ ≤ ENNReal.ofReal ((N n : ℝ) ^ a) := ENNReal.ofReal_le_ofReal hmn
      _ = ENNReal.ofReal (Real.exp (a * L n)) := by
        rw [Real.rpow_def_of_pos hNpos]
        simp [L, mul_comm]
  have hfirstCount : ((ell n + 1 : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (Real.log ((ellN n : ℝ) + 1))) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_log (by positivity : 0 < (ellN n : ℝ) + 1)]
    exact_mod_cast Nat.add_le_add_right hord 1
  have hspanCount : (D n : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp (Real.log ((D n : ℝ) + 1))) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_log (by positivity : 0 < (D n : ℝ) + 1)]
    exact_mod_cast Nat.le_add_right (D n) 1
  have hfirstNum : (m n : ℝ≥0∞) * ((ell n + 1 : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (Real.exp
        (a * L n + Real.log ((ellN n : ℝ) + 1))) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (a * L n)) *
          ((ell n + 1 : ℕ) : ℝ≥0∞) :=
        mul_le_mul_of_nonneg_right hmENN (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp (a * L n)) *
          ENNReal.ofReal (Real.exp (Real.log ((ellN n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hfirstCount (by positivity)
      _ = ENNReal.ofReal (Real.exp
          (a * L n + Real.log ((ellN n : ℝ) + 1))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        congr 1
        rw [← Real.exp_add]
  have hsecondNum : (m n : ℝ≥0∞) *
        ((D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) ≤
      ENNReal.ofReal (Real.exp
        (a * L n + Real.log ((D n : ℝ) + 1) + E n)) := by
    calc
      _ ≤ ENNReal.ofReal (Real.exp (a * L n)) *
          ((D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) :=
        mul_le_mul_of_nonneg_right hmENN (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp (a * L n)) *
          (ENNReal.ofReal (Real.exp (Real.log ((D n : ℝ) + 1))) *
            ENNReal.ofReal (Real.exp (E n))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hspanCount (by positivity)) (by positivity)
      _ = ENNReal.ofReal (Real.exp
          (a * L n + Real.log ((D n : ℝ) + 1) + E n)) := by
        calc
          _ = ENNReal.ofReal (Real.exp (a * L n) *
              (Real.exp (Real.log ((D n : ℝ) + 1)) * Real.exp (E n))) := by
                rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
                  ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
          _ = _ := by
                rw [← Real.exp_add, ← Real.exp_add]
                ring
  have hfirstExp : Real.exp
      (a * L n + Real.log ((ellN n : ℝ) + 1)) ≤
        Real.exp ((1 - 2 * epsilon) * L n) :=
    Real.exp_le_exp.mpr ((div_lt_iff₀ hLn).mp hrateFirst).le
  have hsecondExp : Real.exp
      (a * L n + Real.log ((D n : ℝ) + 1) + E n) ≤
        Real.exp ((1 - 2 * epsilon) * L n) :=
    Real.exp_le_exp.mpr ((div_lt_iff₀ hLn).mp hrateSecond).le
  have hnumerator : (m n : ℝ≥0∞) *
      (((ell n + 1 : ℕ) : ℝ≥0∞) +
        (D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) ≤
      ENNReal.ofReal (Real.exp ((1 - epsilon) * L n)) := by
    calc
      _ = (m n : ℝ≥0∞) * ((ell n + 1 : ℕ) : ℝ≥0∞) +
          (m n : ℝ≥0∞) * ((D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) := by
            rw [mul_add]
      _ ≤ ENNReal.ofReal (Real.exp ((1 - 2 * epsilon) * L n)) +
          ENNReal.ofReal (Real.exp ((1 - 2 * epsilon) * L n)) :=
        add_le_add
          (le_trans hfirstNum (ENNReal.ofReal_le_ofReal hfirstExp))
          (le_trans hsecondNum (ENNReal.ofReal_le_ofReal hsecondExp))
      _ = ENNReal.ofReal
          (2 * Real.exp ((1 - 2 * epsilon) * L n)) := by
        rw [← ENNReal.ofReal_add (Real.exp_nonneg _) (Real.exp_nonneg _)]
        congr 1
        ring
      _ ≤ ENNReal.ofReal (Real.exp ((1 - epsilon) * L n)) := by
        apply ENNReal.ofReal_le_ofReal
        have hlarge : 2 ≤ Real.exp (epsilon * L n) := by
          have hexp : Real.exp (Real.log 2) < Real.exp (epsilon * L n) :=
            Real.exp_lt_exp.mpr hlogLarg
          have htwo : Real.exp (Real.log 2) = (2 : ℝ) := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          rw [htwo] at hexp
          exact hexp.le
        calc
          2 * Real.exp ((1 - 2 * epsilon) * L n) ≤
              Real.exp (epsilon * L n) *
                Real.exp ((1 - 2 * epsilon) * L n) :=
            mul_le_mul_of_nonneg_right hlarge (Real.exp_nonneg _)
          _ = Real.exp ((1 - epsilon) * L n) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hdenOrder : (N n : ℝ≥0∞) ≤ (N n + 1 : ℕ) := by
    exact_mod_cast Nat.le_succ (N n)
  have hNcastENN : (N n : ℝ≥0∞) = ENNReal.ofReal (Real.exp (L n)) := by
    rw [← ENNReal.ofReal_natCast, hpowNn]
  have htargetN : ENNReal.ofReal (Real.exp (-epsilon * L n)) *
      (N n : ℝ≥0∞) = ENNReal.ofReal (Real.exp ((1 - epsilon) * L n)) := by
    rw [hNcastENN, ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  have htargetDen : ENNReal.ofReal (Real.exp ((1 - epsilon) * L n)) ≤
      ENNReal.ofReal (Real.exp (-epsilon * L n)) * (N n + 1 : ℕ) := by
    rw [← htargetN]
    exact mul_le_mul_of_nonneg_left hdenOrder (by positivity)
  have hden0 : ((N n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (N n)
  have hdenTop : ((N n + 1 : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hquotient :
      (m n : ℝ≥0∞) *
          (((ell n + 1 : ℕ) : ℝ≥0∞) +
            (D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) /
        (N n + 1 : ℕ) ≤ ENNReal.ofReal (Real.exp (-epsilon * L n)) :=
    (ENNReal.div_le_iff_le_mul (Or.inl hden0) (Or.inl hdenTop)).2
      (le_trans hnumerator htargetDen)
  calc
    P n ≤ (m n : ℝ≥0∞) *
        (((ell n + 1 : ℕ) : ℝ≥0∞) +
          (D n : ℝ≥0∞) * ENNReal.ofReal (Real.exp (E n))) /
        (N n + 1 : ℕ) := by simpa [D] using hrawn
    _ ≤ ENNReal.ofReal (Real.exp (-epsilon * Real.log (N n : ℝ))) := by
      simpa [L] using hquotient

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
