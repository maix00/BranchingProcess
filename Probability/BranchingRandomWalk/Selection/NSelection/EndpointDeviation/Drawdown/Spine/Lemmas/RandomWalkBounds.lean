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

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Spine.Lemmas.CapacityMarkov

/-!
# First-stage and restarted random-walk probability bounds

This module contains non-reusable intermediate statements in the proof of
the positive-initial-mass capacity estimate, Proposition 3.1, equation
(4.15), of Elie Aïdékon and Yueyun Hu, *Average-weight percolation on the
complete graph*, arXiv:2512.23266 (2025). The preceding module in the
`Lemmas/` chain supplies the definitions and estimates used here.

The declarations are theorem-specific reductions: they pass from the
restarted tube data to the estimates needed by the next stage of the proof.
Reusable path-event and measure inequalities remain in their semantic
modules outside this directory.

## Proof-chain statement

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.iidSequenceLaw_rightTailPositiveASecondStageDrawdown_le_of_ah` bounds the second-stage drawdown probability by $\exp(-dD/\Delta^2)$ under the Aïdékon--Hu estimate.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The affine second-stage corridor in the positive-`a` proof is controlled
by the uniform finite-variance Aïdékon--Hu drawdown estimate on every prefix
whose length is at least a superdiffusive power of the planned tube width.
The endpoint ceiling is reduced to the fixed ratio required by that estimate
using the monotone drift envelope. -/
lemma iidSequenceLaw_rightTailPositiveASecondStageDrawdown_le_of_ah
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (κ c target blockTarget p : ℝ)
    (hκ : 0 ≤ κ) (hc : 0 < c)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ ell ellN d : ℕ, ell < ellN → d ≤ ellN - ell →
      delta0 ≤ c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) →
      (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ (2 + p) ≤ (d : ℝ) →
      iidSequenceLaw ν
          (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
            d
            (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))
            (rightTailPositiveADrift ell ellN κ c d +
              c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)))) ≤
        ENNReal.ofReal (Real.exp
          (-target * sigma ^ 2 * (d : ℝ) /
            (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2)) := by
  let endpointRatio : ℝ := c / (κ / c ^ 2 + c)
  have hden : 0 < κ / c ^ 2 + c := by
    positivity
  have hratio : 0 < endpointRatio := by
    dsimp [endpointRatio]
    exact div_pos hc hden
  obtain ⟨delta0, hdelta0, hbound⟩ :=
    _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_centeredSecondMoment
      ν hν hsigma endpointRatio target p hratio htarget
      (lt_trans htargetBlock hblockTarget) hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro ell ellN d hellN hd hwidthLarge hlengthLarge
  let width : ℝ := c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hwidthPos : 0 < width := by
    dsimp [width]
    have hspan : 0 < (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
      have hspanNat : 0 < ellN - ell := Nat.sub_pos_of_lt hellN
      have hspanReal : 0 < ((ellN - ell : ℕ) : ℝ) := by exact_mod_cast hspanNat
      exact Real.rpow_pos_of_pos hspanReal _
    exact mul_pos hc hspan
  have hspan := rightTailPositiveADrift_le_span ell ellN d κ c hellN hκ hd
  have hratioEq : c / endpointRatio = κ / c ^ 2 + c := by
    dsimp [endpointRatio]
    field_simp [hc.ne', hden.ne']
  have hendpoint :
      rightTailPositiveADrift ell ellN κ c d + width ≤ width / endpointRatio := by
    calc
      rightTailPositiveADrift ell ellN κ c d + width ≤
          κ / c ^ 2 * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) + width :=
        by simpa [add_comm] using add_le_add_right hspan width
      _ = (κ / c ^ 2 + c) *
          (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
        dsimp [width]
        ring
      _ = (c / endpointRatio) *
          (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by rw [hratioEq]
      _ = width / endpointRatio := by
        dsimp [width]
        ring
  have hbound' := hbound width hwidthLarge d hlengthLarge
  apply le_trans (measure_mono ?_) hbound'
  intro increment hdrop
  exact ⟨hdrop.1, hdrop.2.trans hendpoint⟩

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
