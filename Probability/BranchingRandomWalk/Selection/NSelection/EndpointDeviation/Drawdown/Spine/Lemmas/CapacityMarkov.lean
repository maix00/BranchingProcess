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

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.ParameterBounds

/-!
# Window-event inclusions and capacity Markov bounds

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

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveARestartedWindow_zero_mem` gives the zero-start condition required to identify the initial restarted-window event.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le` bounds the capacity-failure probability by the weighted sum $\frac{m}{N+1}\sum_{k=0}^{\ell_N}e^{u_k}p_k$ of restarted-window probabilities.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfGenerationPathBounds` and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfDrawdownBounds` successively substitute generation-wise and drawdown path bounds into that estimate.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

lemma rightTailPositiveARestartedWindow_zero_mem
    (ell ellN : ℕ) (logN b v c κ : ℝ)
    (hell : 0 < ell) (hb : 0 ≤ b) (hlog : 0 ≤ logN) :
    0 ∈ rightTailPositiveARestartedWindow ell ellN logN b v c κ 0 := by
  simp [rightTailPositiveARestartedWindow, hell, mul_nonneg hb hlog]

/-- Markov bound for the capacity event of the actual causal killed tree with
the two stages of the positive-`a` construction. The right side is expressed
in terms of tilted random-walk corridor probabilities, so the Mogulskii input
can be supplied separately without assuming any killed-population expectation
bound. -/
lemma measure_rightTailPositiveAKilled_capacityEvent_compl_le
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (_hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) :
    let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
    let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
    let P := RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      (fun _ : Fin m => (0 : ℝ)) id measurable_id
      (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
      (by
        intro p hp
        rcases RootIndexed.mem_initialPopulation_iff.mp hp with ⟨r, _hr, rfl⟩
        simp) ell window
      (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
      upper (rightTailPositiveARestartedWindow_subset_Iic_upper
        ell ellN logN b v c κ)
    (RootIndexed.stepFieldLaw (Root := Fin m) μ) (P.capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          ENNReal.ofReal (Real.exp
            (if (k : ℕ) ≤ ell then upper k else upper ell + upper k)) *
          RandomWalk.restartedWindowProbability
            (tiltedIncrementFieldLaw realPotential μ) ell window
            (k : ℕ) 0) / (N + 1 : ℕ) := by
  dsimp only
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  let ν := tiltedIncrementFieldLaw realPotential μ
  let bound : ℕ → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Real.exp (if k ≤ ell then upper k else upper ell + upper k)) *
      RandomWalk.restartedWindowProbability ν ell window k 0
  have hwindow : ∀ k, MeasurableSet (window k) :=
    measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ
  have hzero : 0 ∈ window 0 :=
    rightTailPositiveARestartedWindow_zero_mem ell ellN logN b v c κ
      hell hb hlog
  have hupper : ∀ k, window k ⊆ Set.Iic (upper k) :=
    rightTailPositiveARestartedWindow_subset_Iic_upper ell ellN logN b v c κ
  have hbound : HasRestartedWindowFirstMomentBound ν ell window Set.univ bound :=
    hasRestartedWindowFirstMomentBound_of_zero_probability ν ell window
      hwindow upper hupper Set.univ
      (fun k => RandomWalk.restartedWindowProbability ν ell window k 0)
      (fun _ => le_rfl)
  simpa [window, upper, ν, RootIndexed.initialPopulation] using
    RootIndexed.CausalPopulation.measure_capacityEvent_compl_le_card_mul_sum_of_windowFirstMomentBound
      (roots := Finset.univ) (initialPosition := fun _ : Fin m => (0 : ℝ))
      (d := id) (hd := measurable_id) (μ := μ) hboundary ell window hwindow
      hzero upper hupper Set.univ bound
      (fun _ _ => Set.mem_univ _) hbound N ellN

/-- Generation-dependent bounds can be summed directly in the killed-capacity
estimate. This retains the shorter-prefix drawdown probabilities instead of
replacing all of them by the full-horizon probability. -/
lemma measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfGenerationPathBounds
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hvb : v ≤ b)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (pFirst pSecond : ℕ → ℝ≥0∞)
    (hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pFirst (k : ℕ))
    (hsecondPath : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pSecond (k : ℕ)) :
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
              pSecond (k : ℕ)) /
          (N + 1 : ℕ) := by
  dsimp only
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  let ν := tiltedIncrementFieldLaw realPotential μ
  let term : Fin (ellN + 1) → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Real.exp
      (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) *
      RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0
  have hbase := measure_rightTailPositiveAKilled_capacityEvent_compl_le
    m ell ellN N logN b v c κ hell hellN hb hlog μ hboundary
  have hsum :
      (∑ k : Fin (ellN + 1), term k) ≤
        ∑ k : Fin (ellN + 1),
          if (k : ℕ) ≤ ell then pFirst (k : ℕ) else
            ENNReal.ofReal (Real.exp (upper ell + upper (k : ℕ))) *
              pSecond (k : ℕ) := by
    apply Finset.sum_le_sum
    intro k _hk
    by_cases hkle : (k : ℕ) ≤ ell
    · have hupper := rightTailPositiveAFirstStageUpper_le_zero
        ell ellN logN b v c κ hvb hlog (k : ℕ) hkle
      have hweight : ENNReal.ofReal (Real.exp (upper (k : ℕ))) ≤ 1 := by
        calc
          ENNReal.ofReal (Real.exp (upper (k : ℕ))) ≤ ENNReal.ofReal (Real.exp 0) :=
            ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hupper)
          _ = 1 := by simp
      have hpath := hfirstPath k hkle
      calc
        _ ≤ 1 * RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0 :=
          mul_le_mul_of_nonneg_right (by simpa [hkle] using hweight) (by positivity)
        _ ≤ pFirst (k : ℕ) := by simpa using hpath
        _ = (if (k : ℕ) ≤ ell then pFirst (k : ℕ) else
            ENNReal.ofReal (Real.exp (upper ell + upper (k : ℕ))) *
              pSecond (k : ℕ)) := by simp [hkle]
    · have hkle : ell < (k : ℕ) := Nat.lt_of_not_ge hkle
      have hpath := hsecondPath k hkle
      calc
        _ = ENNReal.ofReal (Real.exp (upper ell + upper (k : ℕ))) *
            RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0 := by
              simp [term, Nat.not_le_of_gt hkle]
        _ ≤ ENNReal.ofReal (Real.exp (upper ell + upper (k : ℕ))) *
            pSecond (k : ℕ) :=
          mul_le_mul_of_nonneg_left hpath (by positivity)
        _ = (if (k : ℕ) ≤ ell then pFirst (k : ℕ) else
            ENNReal.ofReal (Real.exp (upper ell + upper (k : ℕ))) *
              pSecond (k : ℕ)) := by
          simp [Nat.not_le_of_gt hkle]
  calc
    (RootIndexed.stepFieldLaw (Root := Fin m) μ)
        ((RootIndexed.CausalPopulation.ofRestartedRealPositionSets
          (fun _ : Fin m => (0 : ℝ)) id measurable_id
          (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
          (by
            intro q hq
            rcases RootIndexed.mem_initialPopulation_iff.mp hq with
              ⟨r, _hr, rfl⟩
            simp) ell window
          (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          upper (rightTailPositiveARestartedWindow_subset_Iic_upper
            ell ellN logN b v c κ)).capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) * (∑ k : Fin (ellN + 1), term k) /
        (N + 1 : ℕ) := by
          simpa [term, window, upper, ν] using hbase
    _ ≤ (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
            if (k : ℕ) ≤ ell then pFirst (k : ℕ) else
            ENNReal.ofReal (Real.exp (upper ell + upper (k : ℕ))) *
              pSecond (k : ℕ)) /
          (N + 1 : ℕ) := by
      apply ENNReal.div_le_div_right
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by simp [upper]

/-- The generation-dependent capacity bound accepts per-prefix random-walk
drawdown estimates directly. The endpoint threshold and the corridor width
are kept at the full planned scale, while the drawdown horizon is the actual
observed prefix length. -/
lemma measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfDrawdownBounds
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
    (pFirst : ℕ → ℝ≥0∞) (pSecond : ℕ → ℝ≥0∞)
    (hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pFirst (k : ℕ))
    (hdrawdown : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      iidSequenceLaw ν
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          ((k : ℕ) - ell)
          (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
          (rightTailPositiveADrift ell ellN κ c ((k : ℕ) - ell) +
            c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) ≤ pSecond (k : ℕ)) :
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
              pSecond (k : ℕ)) /
          (N + 1 : ℕ) := by
  have hsecondPath : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pSecond (k : ℕ) := by
    intro k hk
    rw [show tiltedIncrementFieldLaw realPotential μ = iidSequenceLaw ν by
      rw [hν]
      rfl]
    exact (iidSequenceLaw_restartedWindowProbability_le_secondStageDrawdown
      ν ell ellN (k : ℕ) logN b v c κ hk (by omega) hκ hc hvc)
      |>.trans (hdrawdown k hk)
  exact measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfGenerationPathBounds
    m ell ellN N logN b v c κ hell hellN hb hlog hvb μ hboundary
    pFirst pSecond hfirstPath hsecondPath

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
