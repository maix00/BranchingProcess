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

## Proof-chain statements

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveA_firstStage_probability_le_horizontalTubeProbability`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveA_firstStage_event_subset_noLargeDropEndpointBelowEvent`, and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.rightTailPositiveA_firstStage_probability_le_of_drawdownBound` compare the first-stage corridor event with horizontal-tube and drawdown events.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.exists_uniform_iidSequenceLaw_firstStageCorridor_le_ah`, `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.exists_eventually_iidSequenceLaw_rightTailPositiveAFirstStageCorridor_le_ah`, and `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail.exists_iidSequenceLaw_rightTailPositiveARestartedWindowProbability_le_firstStageAH` supply the uniform finite-variance Aïdékon--Hu bounds for the first stage.
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

/-- The first-stage corridor probability is controlled by any horizontal
tube whose lower boundary matches the corridor and whose upper boundary is
nonnegative. The parameterization below makes those inclusions explicit. -/
lemma rightTailPositiveA_firstStage_probability_le_horizontalTubeProbability
    (ell : ℕ) (logN b a : ℝ) (hb : 0 ≤ b) (hlog : 0 ≤ logN)
    (ha : 0 < a) (ha1 : a ≤ 1)
    (incrementLaw : Measure (ℕ → ℝ)) :
    incrementLaw {increment : ℕ → ℝ |
      InClosedInterval (-b * logN) 0 ell 0 increment} ≤
      horizontalTubeProbability incrementLaw a (b * logN / a) ell := by
  have hwidth : 0 ≤ b * logN / a :=
    div_nonneg (mul_nonneg hb hlog) ha.le
  have hupper : 0 ≤ (1 - a) * (b * logN / a) :=
    mul_nonneg (by linarith) hwidth
  have hlower : -a * (b * logN / a) = -b * logN := by
    field_simp [ha.ne']
  have hsubset :
      {increment : ℕ → ℝ |
        InClosedInterval (-b * logN) 0 ell 0 increment} ⊆
      {increment : ℕ → ℝ |
        InHorizontalTube a (b * logN / a) ell increment} := by
    intro increment hprefix k
    have hposition := hprefix ⟨(k : ℕ) + 1, by omega⟩
    have hposition' :
        AdditivePath.displacement ((k : ℕ) + 1) increment ∈
          Set.Icc (-b * logN) 0 := by
      simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using
        hposition
    rw [hlower]
    exact ⟨hposition'.1, hposition'.2.trans hupper⟩
  unfold horizontalTubeProbability
  exact measure_mono hsubset

/-- Staying in the first-stage interval forces every earlier position to be
at most one corridor width above every later position, and leaves the
endpoint at or below zero. Thus the first-stage event is contained in the
drawdown event already estimated by `RawRate`. -/
lemma rightTailPositiveA_firstStage_event_subset_noLargeDropEndpointBelowEvent
    (ell : ℕ) (logN b : ℝ) :
    {increment : ℕ → ℝ |
      InClosedInterval (-b * logN) 0 ell 0 increment} ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        ell (b * logN) 0 := by
  intro increment hprefix
  constructor
  · intro i j hij hj
    have hleft := hprefix ⟨i, by omega⟩
    have hright := hprefix ⟨j, by omega⟩
    have hleft' : AdditivePath.displacement i increment ∈
        Set.Icc (-b * logN) 0 := by
      simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using hleft
    have hright' : AdditivePath.displacement j increment ∈
        Set.Icc (-b * logN) 0 := by
      simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using hright
    linarith [hleft'.2, hright'.1]
  · have hend := hprefix ⟨ell, Nat.lt_succ_self ell⟩
    simpa [history_eq_fromIncrements, AdditivePath.fromIncrements] using hend.2

/-- The first-stage probability inherits any drawdown-and-endpoint bound,
ready for direct use with the raw finite-variance rate theorem. -/
lemma rightTailPositiveA_firstStage_probability_le_of_drawdownBound
    (ell : ℕ) (logN b : ℝ) (incrementLaw : Measure (ℕ → ℝ))
    (p : ℝ≥0∞)
    (hdrawdown : incrementLaw
      (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        ell (b * logN) 0) ≤ p) :
    incrementLaw {increment : ℕ → ℝ |
      InClosedInterval (-b * logN) 0 ell 0 increment} ≤ p :=
  (measure_mono
    (rightTailPositiveA_firstStage_event_subset_noLargeDropEndpointBelowEvent
      ell logN b)).trans hdrawdown

/-- A horizontal interval corridor has the same uniform finite-variance
exponential bound as the corresponding drawdown event. This is the first
stage of the positive-`a` construction in (4.15). -/
lemma exists_uniform_iidSequenceLaw_firstStageCorridor_le_ah
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (endpointRatio target blockTarget p : ℝ)
    (hEndpointRatio : 0 < endpointRatio)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ horizon : ℕ, ∀ width : ℝ, 0 < width → delta0 ≤ width →
        width ^ (2 + p) ≤ (horizon : ℝ) →
        iidSequenceLaw ν
          {increment : ℕ → ℝ |
            InClosedInterval (-width) 0 horizon 0 increment} ≤
          ENNReal.ofReal (Real.exp
            (-target * sigma ^ 2 * (horizon : ℝ) / width ^ 2)) := by
  obtain ⟨delta0, hdelta0, hdrawdown⟩ :=
    _root_.ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_centeredSecondMoment
      ν hν hsigma endpointRatio target p hEndpointRatio htarget
      (lt_trans htargetBlock hblockTarget) hp
  refine ⟨delta0, hdelta0, ?_⟩
  intro horizon width hwidth hscale hlength
  have hinterval :=
    rightTailPositiveA_firstStage_event_subset_noLargeDropEndpointBelowEvent
      horizon width 1
  have hinterval' :
      {increment : ℕ → ℝ |
        InClosedInterval (-width) 0 horizon 0 increment} ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        horizon width 0 := by
    simpa using hinterval
  have hthreshold : 0 ≤ width / endpointRatio :=
    div_nonneg hwidth.le hEndpointRatio.le
  have hcutoff :
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        horizon width 0 ⊆
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        horizon width (width / endpointRatio) := by
    intro increment h
    exact ⟨h.1, le_trans h.2 hthreshold⟩
  have hbound := hdrawdown width hscale horizon hlength
  exact (measure_mono (hinterval'.trans hcutoff)).trans hbound

/-- For the `log^(5/2) N` first cutoff, the uniform finite-variance
Aïdékon--Hu estimate gives the required first-stage corridor probability
eventually. The restriction `p < 1/2` is precisely the scale comparison
`(b log N)^(2+p) = o((log N)^(5/2))`. -/
lemma exists_eventually_iidSequenceLaw_rightTailPositiveAFirstStageCorridor_le_ah
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (endpointRatio target blockTarget p : ℝ)
    (hEndpointRatio : 0 < endpointRatio)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) {b : ℝ} (hb : 0 < b)
    (hpHalf : p < 1 / 2) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ᶠ n : ℕ in atTop,
        iidSequenceLaw ν
          {increment : ℕ → ℝ |
            InClosedInterval (-b * logarithmOfSampleSize N n) 0
              (rightTailPositiveAFirstCutoff N n) 0 increment} ≤
          ENNReal.ofReal (Real.exp
            (-target * sigma ^ 2 *
              (rightTailPositiveAFirstCutoff N n : ℝ) /
                (b * logarithmOfSampleSize N n) ^ 2)) := by
  obtain ⟨delta0, hdelta0, hAH⟩ :=
    exists_uniform_iidSequenceLaw_firstStageCorridor_le_ah
      ν hν hsigma hB hcontinuous hmeasurable endpointRatio target blockTarget p
      hEndpointRatio htarget htargetBlock hblockTarget hp
  refine ⟨delta0, hdelta0, ?_⟩
  have hscale := eventually_rightTailPositiveAFirstStageAHScale
    (N := N) hN (b := b) (p := p) (delta0 := delta0) hb hpHalf
  filter_upwards [hscale] with n hscale
  have hwidthPos : 0 < b * logarithmOfSampleSize N n :=
    lt_of_lt_of_le hdelta0 hscale.1
  simpa [neg_mul] using hAH (rightTailPositiveAFirstCutoff N n)
    (b * logarithmOfSampleSize N n) hwidthPos hscale.1 hscale.2

/-- The first-stage Aïdékon--Hu estimate applies to each generation with
its actual prefix length.  Short prefixes are bounded by one; long prefixes
use the uniform corridor estimate at the same width as the full first tube.
This is the generation-wise form needed when summing the first moments in
the proof of (4.15). -/
lemma exists_iidSequenceLaw_rightTailPositiveARestartedWindowProbability_le_firstStageAH
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (ell ellN n : ℕ) (logN b v c κ : ℝ)
    (hlog : 0 ≤ logN) (hvb : v ≤ b) (hn : n ≤ ell)
    (endpointRatio target blockTarget p : ℝ)
    (hEndpointRatio : 0 < endpointRatio)
    (htarget : 0 < target) (htargetBlock : target < blockTarget)
    (hblockTarget : blockTarget < Real.pi ^ 2 / 2)
    (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ _hwidth : delta0 ≤ b * logN,
        RandomWalk.restartedWindowProbability (iidSequenceLaw ν) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ) n 0 ≤
          (if (b * logN) ^ (2 + p) ≤ (n : ℝ) then
            ENNReal.ofReal (Real.exp
              (-target * sigma ^ 2 * (n : ℝ) / (b * logN) ^ 2))
          else 1) := by
  obtain ⟨deltaAH, hdeltaAH, hAH⟩ :=
    exists_uniform_iidSequenceLaw_firstStageCorridor_le_ah
      ν hν hsigma hB hcontinuous hmeasurable endpointRatio target blockTarget p
      hEndpointRatio htarget htargetBlock hblockTarget hp
  refine ⟨deltaAH, hdeltaAH, ?_⟩
  intro _hwidth
  have hsubset := rightTailPositiveARestartedWindow_event_subset_firstStagePrefix
    ell ellN n logN b v c κ hlog hvb hn
  by_cases hlong : (b * logN) ^ (2 + p) ≤ (n : ℝ)
  · have hwidthPos : 0 < b * logN := lt_of_lt_of_le hdeltaAH _hwidth
    have hprob := hAH n (b * logN) hwidthPos _hwidth hlong
    have hlower : -(b * logN) = -b * logN := by ring
    rw [hlower] at hprob
    simpa [RandomWalk.restartedWindowProbability, hlong, neg_mul] using
      (measure_mono hsubset).trans hprob
  · have hprob :
        RandomWalk.restartedWindowProbability (iidSequenceLaw ν) ell
          (rightTailPositiveARestartedWindow ell ellN logN b v c κ) n 0 ≤ 1 := by
      unfold RandomWalk.restartedWindowProbability
      calc
        _ ≤ (iidSequenceLaw ν) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    simpa [hlong] using hprob

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
