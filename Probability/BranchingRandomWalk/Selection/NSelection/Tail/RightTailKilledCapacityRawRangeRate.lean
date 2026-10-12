/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.RightTailKilledCapacity
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.UniformRawRangeRate

/-!
# Finite-variance capacity bounds for the second tube

This module supplies the second-stage random-walk input to the killed
population capacity estimate using the raw finite-variance range rate. No
Brownian-process witness is part of the interface.
-/

open Filter MeasureTheory
open scoped ENNReal BigOperators Topology

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The affine second-stage corridor is controlled uniformly under only a
centered finite second moment. The drift envelope changes the endpoint
threshold by a fixed multiple of the planned width. -/
theorem iidSequenceLaw_rightTailPositiveASecondStageDrawdown_le_of_rawRangeRate
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (κ c p : ℝ) (hκ : 0 ≤ κ) (hc : 0 < c) (hp : 0 < p) :
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
          (-(Real.pi ^ 2 / 4608) * sigma ^ 2 * (d : ℝ) /
            (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2)) := by
  let endpointFactor : ℝ := (κ / c ^ 2 + c) / c
  have hden : 0 < κ / c ^ 2 + c := by positivity
  have hfactor : 0 < endpointFactor := by
    dsimp [endpointFactor]
    exact div_pos hden hc
  obtain ⟨delta0, hdelta0, hbound⟩ :=
    _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_centeredSecondMoment
      ν hν hsigma endpointFactor p hfactor.le hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro ell ellN d hellN hd hwidthLarge hlengthLarge
  let width : ℝ := c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hspanPos : 0 < (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) := by
    have hspanNat : 0 < ellN - ell := Nat.sub_pos_of_lt hellN
    have hspanReal : 0 < ((ellN - ell : ℕ) : ℝ) := by exact_mod_cast hspanNat
    exact Real.rpow_pos_of_pos hspanReal _
  have hwidthPos : 0 < width := by
    dsimp [width]
    exact mul_pos hc hspanPos
  have hspan := rightTailPositiveADrift_le_span ell ellN d κ c hellN hκ hd
  have hendpoint : rightTailPositiveADrift ell ellN κ c d + width ≤
      endpointFactor * width := by
    calc
      rightTailPositiveADrift ell ellN κ c d + width ≤
          κ / c ^ 2 * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ)) + width := by
            simpa [add_comm] using add_le_add_right hspan width
      _ = endpointFactor * width := by
        dsimp [endpointFactor, width]
        field_simp [hc.ne']
  have hbound' := hbound width hwidthLarge d hlengthLarge
  apply le_trans (measure_mono ?_) hbound'
  intro increment hdrop
  exact ⟨hdrop.1, hdrop.2.trans hendpoint⟩

/-- Insert the raw finite-variance drawdown bound into the two-stage killed
capacity estimate. Long second-stage prefixes use the exponential estimate;
short prefixes use the probability bound one. -/
theorem measure_rightTailPositiveAKilled_capacityEvent_compl_le_twoPhaseOfRawRangeRateDrawdown
    (m ell ellN N : ℕ) (logN b v c κ p : ℝ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    (hell : 0 < ell) (hellN : ell < ellN)
    (hb : 0 ≤ b) (hlog : 0 ≤ logN) (hκ : 0 ≤ κ) (hvb : v ≤ b)
    (hc : 0 < c) (hvc : v ≤ c) (hp : 0 < p)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : ν = tiltedPotentialLaw realPotential (-1) μ)
    {sigma : ℝ}
    (hspine : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
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
                  (-(Real.pi ^ 2 / 4608) * sigma ^ 2 *
                    (((k : ℕ) - ell : ℕ) : ℝ) /
                    (c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))) ^ 2))
              else 1)) / (N + 1 : ℕ)) := by
  obtain ⟨delta0', hdelta0', hraw⟩ :=
    iidSequenceLaw_rightTailPositiveASecondStageDrawdown_le_of_rawRangeRate
      ν hspine hsigma κ c p hκ hc hp
  refine ⟨delta0', hdelta0', ?_⟩
  intro hscale
  let width : ℝ := c * (((ellN - ell : ℕ) : ℝ) ^ (3⁻¹ : ℝ))
  have hwidthLarge : delta0' ≤ width := by simpa [width] using hscale
  let pSecond : ℕ → ℝ≥0∞ := fun k =>
    if width ^ (2 + p) ≤ ((k - ell : ℕ) : ℝ) then
      ENNReal.ofReal (Real.exp
        (-(Real.pi ^ 2 / 4608) * sigma ^ 2 *
          ((k - ell : ℕ) : ℝ) / width ^ 2))
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
    · have hbound := hraw ell ellN ((k : ℕ) - ell) hellN hd hwidthLarge hlong
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

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
