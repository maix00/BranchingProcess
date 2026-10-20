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

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveARestartedWindow_zero_mem`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveARestartedWindow_event_subset_firstStage`, and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveARestartedWindow_event_subset_firstStagePrefix` give the zero-start condition and place restarted-window events in the appropriate first-stage corridor.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le` bounds the capacity-failure probability by the weighted sum $\frac{m}{N+1}\sum_{k=0}^{\ell_N}e^{u_k}p_k$ of restarted-window probabilities.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_uniform`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_enveloped`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhase`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfPathBounds`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfGenerationPathBounds`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfDrawdownBounds`, and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfFirstStageBound` successively substitute uniform, endpoint-envelope, phase-wise, generation-wise, drawdown, and first-stage path bounds into that estimate.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

theorem rightTailPositiveARestartedWindow_zero_mem
    (ell ellN : ℕ) (logN b v c κ : ℝ)
    (hell : 0 < ell) (hb : 0 ≤ b) (hlog : 0 ≤ logN) :
    0 ∈ rightTailPositiveARestartedWindow ell ellN logN b v c κ 0 := by
  simp [rightTailPositiveARestartedWindow, hell, mul_nonneg hb hlog]

/-- Every restarted-window event observed after the first cutoff already
forces the original path to stay in the first-stage corridor through `ell`.
This extracts a useful probability bound without estimating the second tube. -/
theorem rightTailPositiveARestartedWindow_event_subset_firstStage
    (ell ellN : ℕ) (logN b v c κ : ℝ) (n : ℕ)
    (hlog : 0 ≤ logN) (hvb : v ≤ b)
    (hn : ell ≤ n) :
    {increment : ℕ → ℝ |
      InRestartedWindows ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (history n 0 increment)} ⊆
      {increment : ℕ → ℝ |
        InClosedInterval (-b * logN) 0 ell 0 increment} := by
  intro increment hpath
  change ∀ j : Fin (ell + 1),
      history ell 0 increment j ∈ Set.Icc (-b * logN) 0
  intro j
  have hjle : (j : ℕ) ≤ ell := Nat.le_of_lt_succ j.isLt
  have hrestart := hpath ⟨j, by omega⟩
  have hwindow :
      history n 0 increment ⟨j, by omega⟩ ∈
        rightTailPositiveARestartedWindow ell ellN logN b v c κ j := by
    simpa [restartAnchor_eq_zero hjle] using hrestart
  have htop : (-b + v) * logN ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ hlog
    linarith
  have hwindow_subset :
      rightTailPositiveARestartedWindow ell ellN logN b v c κ j ⊆
        Set.Icc (-b * logN) 0 := by
    by_cases hjlt : (j : ℕ) < ell
    · simp [rightTailPositiveARestartedWindow, hjlt]
    · have hjeq : (j : ℕ) = ell := by omega
      rw [hjeq]
      have hcutoff :
          rightTailPositiveARestartedWindow ell ellN logN b v c κ ell =
            Set.Icc (-b * logN) ((-b + v) * logN) := by
        simp [rightTailPositiveARestartedWindow]
      rw [hcutoff]
      intro x hx
      exact ⟨hx.1, hx.2.trans htop⟩
  have hfirst := hwindow_subset hwindow
  have hhistory :
      history n 0 increment ⟨j, by omega⟩ = history ell 0 increment j := by
    simp [history_eq_fromIncrements, AdditivePath.fromIncrements]
  rw [← hhistory]
  exact hfirst

/-- Before the first cutoff, every restarted-window prefix is contained in
the corresponding initial corridor prefix.  At the cutoff itself the
narrower terminal window is still below zero when `v ≤ b`. -/
theorem rightTailPositiveARestartedWindow_event_subset_firstStagePrefix
    (ell ellN n : ℕ) (logN b v c κ : ℝ)
    (hlog : 0 ≤ logN) (hvb : v ≤ b) (hn : n ≤ ell) :
    {increment : ℕ → ℝ |
      InRestartedWindows ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (history n 0 increment)} ⊆
      {increment : ℕ → ℝ |
        InClosedInterval (-b * logN) 0 n 0 increment} := by
  intro increment hpath
  change ∀ j : Fin (n + 1),
      history n 0 increment j ∈ Set.Icc (-b * logN) 0
  intro j
  have hjle : (j : ℕ) ≤ ell := (Nat.le_of_lt_succ j.isLt).trans hn
  have hrestart := hpath j
  have hwindow :
      history n 0 increment j ∈
        rightTailPositiveARestartedWindow ell ellN logN b v c κ (j : ℕ) := by
    simpa [restartAnchor_eq_zero hjle] using hrestart
  by_cases hjlt : (j : ℕ) < ell
  · simpa [rightTailPositiveARestartedWindow, hjlt] using hwindow
  · have hjeq : (j : ℕ) = ell := by omega
    have htop : (-b + v) * logN ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hlog
      linarith
    have hcutoff :
        rightTailPositiveARestartedWindow ell ellN logN b v c κ ell =
          Set.Icc (-b * logN) ((-b + v) * logN) := by
      simp [rightTailPositiveARestartedWindow]
    rw [hjeq, hcutoff] at hwindow
    exact ⟨hwindow.1, hwindow.2.trans htop⟩

/-- Markov bound for the capacity event of the actual causal killed tree with
the two stages of the positive-`a` construction. The right side is expressed
in terms of tilted random-walk corridor probabilities, so the Mogulskii input
can be supplied separately without assuming any killed-population expectation
bound. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le
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

/-- Uniform corridor estimates can be substituted directly into the
positive-`a` killed-capacity bound. The endpoint envelope controls the
exponential weight, while a single bound `p` controls every restarted-window
probability. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_uniform
    (m ell ellN N : ℕ) (logN b v c κ U : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (p : ℝ≥0∞)
    (hupper : ∀ k : Fin (ellN + 1),
      (if (k : ℕ) ≤ ell then
        rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)
      else
        rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)) ≤ U)
    (hpath : ∀ k : Fin (ellN + 1),
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ p) :
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
        ((ellN + 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp U) * p) /
          (N + 1 : ℕ) := by
  dsimp only
  let window := rightTailPositiveARestartedWindow ell ellN logN b v c κ
  let upper := rightTailPositiveAWindowUpper ell ellN logN b v c κ
  let ν := tiltedIncrementFieldLaw realPotential μ
  have hbase := measure_rightTailPositiveAKilled_capacityEvent_compl_le
    m ell ellN N logN b v c κ hell hellN hb hlog μ hboundary
  have hsum :
      (∑ k : Fin (ellN + 1),
        ENNReal.ofReal (Real.exp
          (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) *
          RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0) ≤
        ∑ _k : Fin (ellN + 1), ENNReal.ofReal (Real.exp U) * p := by
    apply Finset.sum_le_sum
    intro k _hk
    have hweight : ENNReal.ofReal (Real.exp
        (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) ≤
        ENNReal.ofReal (Real.exp U) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hupper k))
    calc
      _ ≤ ENNReal.ofReal (Real.exp U) *
          RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0 :=
        mul_le_mul_of_nonneg_right hweight (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp U) * p :=
        mul_le_mul_of_nonneg_left (hpath k) (by positivity)
  calc
    (RootIndexed.stepFieldLaw (Root := Fin m) μ)
        ((RootIndexed.CausalPopulation.ofRestartedRealPositionSets
          (fun _ : Fin m => (0 : ℝ)) id measurable_id
          (RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m)))
          (by
            intro p hp
            rcases RootIndexed.mem_initialPopulation_iff.mp hp with
              ⟨r, hr, rfl⟩
            simp) ell window
          (measurableSet_rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          upper (rightTailPositiveARestartedWindow_subset_Iic_upper
            ell ellN logN b v c κ)).capacityEvent N ellN)ᶜ ≤
      (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1),
          ENNReal.ofReal (Real.exp
            (if (k : ℕ) ≤ ell then upper (k : ℕ) else upper ell + upper (k : ℕ))) *
            RandomWalk.restartedWindowProbability ν ell window (k : ℕ) 0) /
          (N + 1 : ℕ) := by
      simpa [window, upper, ν] using hbase
    _ ≤ (m : ℝ≥0∞) *
        (∑ k : Fin (ellN + 1), ENNReal.ofReal (Real.exp U) * p) /
          (N + 1 : ℕ) := by
      apply ENNReal.div_le_div_right
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (m : ℝ≥0∞) *
        ((ellN + 1 : ℕ) : ℝ≥0∞) *
          (ENNReal.ofReal (Real.exp U) * p) /
          (N + 1 : ℕ) := by
      simp [Finset.sum_const, mul_assoc]

/-- Capacity bound with the positive-`a` tube's deterministic endpoint
envelope already substituted. The remaining probabilistic input is the
uniform restarted-window bound `hpath`. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_enveloped
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (hκ : 0 ≤ κ) (hc : 0 < c) (hvb : v ≤ b)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (p : ℝ≥0∞)
    (hpath : ∀ k : Fin (ellN + 1),
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ p) :
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
      (m : ℝ≥0∞) * ((ellN + 1 : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (Real.exp
          ((κ / c ^ 2 + max c v) *
            (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) * p) /
          (N + 1 : ℕ) := by
  let U : ℝ := (κ / c ^ 2 + max c v) *
    (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hupper : ∀ k : Fin (ellN + 1),
      (if (k : ℕ) ≤ ell then
        rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)
      else
        rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ)) ≤ U := by
    intro k
    simpa [U] using rightTailPositiveAEndpointEnvelope_le
      ell ellN logN b v c κ hellN hκ hc hvb hlog k
  have hcapacity := measure_rightTailPositiveAKilled_capacityEvent_compl_le_uniform
    m ell ellN N logN b v c κ U hell hellN hb hlog μ hboundary p hupper hpath
  simpa [U] using hcapacity

/-- Two-stage form of the killed-capacity estimate. The first tube and the
long restarted tube may use different weighted probability bounds, matching
the separate corridor estimates in the proof of (4.15). -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhase
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (A B : ℝ≥0∞)
    (hfirst : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
        RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 ≤ A)
    (hsecond : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
        RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 ≤ B) :
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
        (((ell + 1 : ℕ) : ℝ≥0∞) * A +
          ((ellN - ell : ℕ) : ℝ≥0∞) * B) /
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
        ∑ k : Fin (ellN + 1), if (k : ℕ) ≤ ell then A else B := by
    apply Finset.sum_le_sum
    intro k _hk
    by_cases hkle : (k : ℕ) ≤ ell
    · simpa [term, hkle, window, upper, ν] using hfirst k hkle
    · simpa [term, hkle, window, upper, ν] using
        hsecond k (Nat.lt_of_not_ge hkle)
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
        (∑ k : Fin (ellN + 1), if (k : ℕ) ≤ ell then A else B) /
          (N + 1 : ℕ) := by
      apply ENNReal.div_le_div_right
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (m : ℝ≥0∞) *
        (((ell + 1 : ℕ) : ℝ≥0∞) * A +
          ((ellN - ell : ℕ) : ℝ≥0∞) * B) /
          (N + 1 : ℕ) := by
      rw [sum_fin_if_le_eq_add_mul ell ellN A B (Nat.le_of_lt hellN)]

/-- Corridor-probability inputs imply the two weighted phase bounds. The
first interval uses its nonpositive endpoint weight; the long tube keeps the
negative cutoff offset in its exponential factor. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfPathBounds
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (pFirst pSecond : ℝ≥0∞)
    (hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pFirst)
    (hsecondPath : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pSecond) :
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
        (((ell + 1 : ℕ) : ℝ≥0∞) * pFirst +
          ((ellN - ell : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal (Real.exp
              ((-b + v) * logN + (κ / c ^ 2 + max c v) *
                (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) * pSecond)) /
          (N + 1 : ℕ) := by
  let U₂ : ℝ := (-b + v) * logN + (κ / c ^ 2 + max c v) *
    (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hfirst : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
        RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 ≤ pFirst := by
    intro k hk
    have hupper := rightTailPositiveAFirstStageUpper_le_zero
      ell ellN logN b v c κ hvb hlog (k : ℕ) hk
    have hweight : ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) ≤ 1 := by
      calc
        ENNReal.ofReal (Real.exp
            (rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) ≤
          ENNReal.ofReal (Real.exp 0) :=
            ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hupper)
        _ = 1 := by simp
    calc
      _ ≤ 1 * RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 := mul_le_mul_of_nonneg_right hweight (by positivity)
      _ ≤ pFirst := by simpa using hfirstPath k hk
  have hsecond : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) *
        RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 ≤ ENNReal.ofReal (Real.exp U₂) * pSecond := by
    intro k hk
    have hkhi : (k : ℕ) ≤ ellN := Nat.le_of_lt_succ k.isLt
    have hupper := rightTailPositiveASecondStageEnvelope_le
      ell ellN (k : ℕ) logN b v c κ hellN hκ hk hkhi
    have hweight : ENNReal.ofReal (Real.exp
        (rightTailPositiveAWindowUpper ell ellN logN b v c κ ell +
          rightTailPositiveAWindowUpper ell ellN logN b v c κ (k : ℕ))) ≤
        ENNReal.ofReal (Real.exp U₂) := by
      apply ENNReal.ofReal_le_ofReal
      exact Real.exp_le_exp.mpr (by simpa [U₂] using hupper)
    calc
      _ ≤ ENNReal.ofReal (Real.exp U₂) *
          RandomWalk.restartedWindowProbability
            (tiltedIncrementFieldLaw realPotential μ) ell
            (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
            (k : ℕ) 0 := mul_le_mul_of_nonneg_right hweight (by positivity)
      _ ≤ ENNReal.ofReal (Real.exp U₂) * pSecond :=
        mul_le_mul_of_nonneg_left (hsecondPath k hk) (by positivity)
  simpa [U₂] using measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhase
    m ell ellN N logN b v c κ hell hellN hb hlog μ hboundary pFirst
    (ENNReal.ofReal (Real.exp U₂) * pSecond) hfirst hsecond

/-- Generation-dependent bounds can be summed directly in the killed-capacity
estimate. This retains the shorter-prefix drawdown probabilities instead of
replacing all of them by the full-horizon probability. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfGenerationPathBounds
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
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfDrawdownBounds
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

/-- A bound on the first-stage horizontal corridor controls every later
restarted-window probability, since those events retain the first-stage
prefix. The initial-stage terms use only that the tilted path law is a
probability measure. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfFirstStageBound
    (m ell ellN N : ℕ) (logN b v c κ : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (pSecond : ℝ≥0∞)
    (hfirstStage : (tiltedIncrementFieldLaw realPotential μ)
      {increment : ℕ → ℝ |
        InClosedInterval (-b * logN) 0 ell 0 increment} ≤ pSecond) :
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
  let htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw realPotential μ) :=
    tiltedIncrementFieldLaw_isProbability realPotential μ hboundary
  have hfirstPath : ∀ k : Fin (ellN + 1), (k : ℕ) ≤ ell →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ 1 := by
    intro k hk
    calc
      _ ≤ (tiltedIncrementFieldLaw realPotential μ) Set.univ :=
        measure_mono (Set.subset_univ _)
      _ = 1 := htilted.measure_univ
  have hsecondPath : ∀ k : Fin (ellN + 1), ell < (k : ℕ) →
      RandomWalk.restartedWindowProbability
        (tiltedIncrementFieldLaw realPotential μ) ell
        (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
        (k : ℕ) 0 ≤ pSecond := by
    intro k hk
    have hsubset := rightTailPositiveARestartedWindow_event_subset_firstStage
      ell ellN logN b v c κ (k : ℕ) hlog hvb (Nat.le_of_lt hk)
    have hprob :
        RandomWalk.restartedWindowProbability
          (tiltedIncrementFieldLaw realPotential μ) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ)
          (k : ℕ) 0 ≤
        (tiltedIncrementFieldLaw realPotential μ)
          {increment : ℕ → ℝ |
            InClosedInterval (-b * logN) 0 ell 0 increment} := by
      unfold RandomWalk.restartedWindowProbability
      exact measure_mono hsubset
    exact hprob.trans hfirstStage
  simpa using
    (measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfPathBounds
      m ell ellN N logN b v c κ hell hellN hb hlog hκ hvb μ hboundary
      1 pSecond hfirstPath hsecondPath)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
