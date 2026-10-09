/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Drawdown
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.Horizontal
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.BlockBound
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.Parameters
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option maxHeartbeats 800000

/-!
# Spatial slicing for bounded-drawdown walk events

This file connects the deterministic running-maximum bins to finite IID
increment-block events.  Once a fixed bin pattern is specified, every block
whose endpoint bins agree is contained in a deterministic spatial interval;
its translated partial-sum path therefore has bounded oscillation.  The
remaining fixed-pattern event factors by the generic consecutive-block law.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Analytic

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Logarithmic one-block rate supplied by the Brownian finite-cover bound.
The logarithmic cover cost is included explicitly, so this rate can be
compared directly with the entropy of the spatial-bin patterns. -/
noncomputable def finiteCoverBlockRate (count : ℕ) (width : ℝ) : ℝ :=
  Real.pi ^ 2 /
      (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2) -
    Real.log (16 * (count : ℝ))

theorem two_mul_finiteCoverRangeBound_eq_exp_neg_rate
    {count : ℕ} (hcount : 0 < count) {width : ℝ} :
    2 * finiteCoverRangeBound count width =
      Real.exp (-finiteCoverBlockRate count width) := by
  let eigenExponent : ℝ := Real.pi ^ 2 /
    (2 * ((1 + 3 / (count : ℝ)) * width) ^ 2)
  have hcoverPos : 0 < 16 * (count : ℝ) := by positivity
  calc
    2 * finiteCoverRangeBound count width =
        16 * (count : ℝ) * Real.exp (-eigenExponent) := by
      simp [finiteCoverRangeBound, finiteCoverCorridorExponential,
        eigenExponent]
      ring_nf
    _ = Real.exp (Real.log (16 * (count : ℝ))) *
          Real.exp (-eigenExponent) := by
      rw [Real.exp_log hcoverPos]
    _ = Real.exp (Real.log (16 * (count : ℝ)) + -eigenExponent) := by
      rw [← Real.exp_add]
    _ = Real.exp (-finiteCoverBlockRate count width) := by
      congr 1
      dsimp [finiteCoverBlockRate, eigenExponent]
      ring

/-- Applying the general one-block estimate to widths proportional to an
arbitrary diverging scale gives the exact AH diffusive block size
`floor(A * Δ^2)`. The block probability is at most `exp(-r_A)`, with `r_A`
the finite-cover Brownian exponent minus the logarithmic cover cost. -/
theorem eventually_integerDiffusiveBlockOscillationProbability_le_exp
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsecondMoment : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {delta : ℕ → ℝ} (hdelta : Tendsto delta atTop atTop)
    {A eta enlargement : ℝ} {count : ℕ}
    (hA : 0 < A) (heta : 0 < eta) (henlargement : 0 < enlargement)
    (hcount : 0 < count)
    (hspectral : finiteCoverCorridorExponential count
      ((1 + enlargement) / Real.sqrt (A / (1 + eta) ^ 2)) < 1 / 2) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0
          (⌊A * delta n ^ 2⌋₊) increment ∈
            blockOscillationEvent ((1 + eta) * delta n)
              (⌊A * delta n ^ 2⌋₊)} ≤
        ENNReal.ofReal (Real.exp (-finiteCoverBlockRate count
          ((1 + enlargement) / Real.sqrt (A / (1 + eta) ^ 2)))) := by
  let scale : ℕ → ℝ := fun n => (1 + eta) * delta n
  let constant : ℝ := A / (1 + eta) ^ 2
  have hscale : Tendsto scale atTop atTop := by
    dsimp [scale]
    simpa [mul_comm] using hdelta.const_mul_atTop
      (by positivity : 0 < 1 + eta)
  have hconstant : 0 < constant := by
    dsimp [constant]
    positivity
  have hbound := eventually_diffusiveBlockOscillationProbability_le_of_fixedCover_of_tendsto_atTop
    ν hcentered hsecondMoment hB hcontinuous hmeasurable hscale
    hconstant henlargement hcount hspectral
  filter_upwards [hbound] with n hn
  have hlength : diffusiveBlockLength constant scale n = ⌊A * delta n ^ 2⌋₊ := by
    dsimp [diffusiveBlockLength, constant, scale]
    congr 1
    have honeEta : 1 + eta ≠ 0 := ne_of_gt (by positivity)
    field_simp [honeEta]
  rw [two_mul_finiteCoverRangeBound_eq_exp_neg_rate hcount] at hn
  rw [← hlength]
  change iidSequenceLaw ν {increment : ℕ → ℝ |
      blockOscillationEvent ((1 + eta) * delta n)
        (diffusiveBlockLength constant scale n)
        (Combinatorics.Sequence.blockCoordinates 0
          (diffusiveBlockLength constant scale n) increment)} ≤ _
  exact hn

/-- A no-large-drawdown path whose endpoint is below a threshold stays below
that threshold plus one drawdown allowance throughout the finite horizon. -/
theorem additivePath_le_threshold_add_delta_of_noLargeDrop
    {horizon : ℕ} (increment : ℕ → ℝ) (delta threshold : ℝ)
    (hnoDrop : ∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta)
    (hendpoint : AdditivePath.displacement horizon increment ≤ threshold) :
    ∀ i ≤ horizon,
      AdditivePath.displacement i increment ≤ threshold + delta := by
  intro i hi
  have h := hnoDrop i horizon hi (Nat.le_refl _)
  linarith

/-- Starting from zero, a no-large-drawdown path cannot descend below minus
the drawdown allowance. -/
theorem neg_delta_le_additivePath_of_noLargeDrop
    {horizon : ℕ} (increment : ℕ → ℝ) (delta : ℝ)
    (hnoDrop : ∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta)
    {i : ℕ} (hi : i ≤ horizon) :
    -delta ≤ AdditivePath.displacement i increment := by
  have h := hnoDrop 0 i (Nat.zero_le _) hi
  have hzero : AdditivePath.displacement 0 increment = 0 :=
    AdditivePath.displacement_zero increment
  rw [hzero] at h
  linarith

/-- The one-block constraint prescribed by a fixed spatial-bin pattern.  A
block whose endpoint bins jump is left unrestricted. -/
def spatialBinPatternBlockEvent {q K length : ℕ} (width : ℝ)
    (bins : Fin (q + 1) → Fin (K + 1)) (j : Fin q) :
    Set (Fin length → ℝ) :=
  if bins j.castSucc = bins j.succ then
    blockOscillationEvent width length else Set.univ

/-- The increment event associated with one fixed spatial-bin pattern. -/
def spatialBinPatternEvent {q K : ℕ} (width : ℝ) (length : ℕ)
    (bins : Fin (q + 1) → Fin (K + 1)) : Set (ℕ → ℝ) :=
  {increment | ∀ j : Fin q,
    Combinatorics.Sequence.blockCoordinates (j.val * length) length increment ∈
      spatialBinPatternBlockEvent width bins j}

theorem measurableSet_spatialBinPatternEvent {q K : ℕ} (width : ℝ) (length : ℕ)
    (bins : Fin (q + 1) → Fin (K + 1)) :
    MeasurableSet (spatialBinPatternEvent width length bins) := by
  rw [show spatialBinPatternEvent width length bins =
      ⋂ j : Fin q, {increment |
        Combinatorics.Sequence.blockCoordinates (j.val * length) length increment ∈
          spatialBinPatternBlockEvent width bins j} by
    ext increment
    simp [spatialBinPatternEvent]]
  apply MeasurableSet.iInter
  intro j
  by_cases hbin : bins j.castSucc = bins j.succ
  · simp only [spatialBinPatternBlockEvent, if_pos hbin]
    exact (measurableSet_blockOscillationEvent width length).preimage
      (measurable_blockCoordinates (j.val * length) length)
  · simp [spatialBinPatternBlockEvent, hbin]

/-- Probability of a fixed spatial-bin pattern factors into the one-block
probabilities prescribed by that pattern.  Jump blocks contribute probability
one; unchanged-bin blocks contribute the oscillation probability. -/
theorem iidSequenceLaw_measure_spatialBinPatternEvent
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {q K length : ℕ} (width : ℝ)
    (bins : Fin (q + 1) → Fin (K + 1)) :
    iidSequenceLaw ν (spatialBinPatternEvent width length bins) =
      ∏ j : Fin q, iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 length increment ∈
          spatialBinPatternBlockEvent width bins j} := by
  let event : ∀ j : Fin q, Set (Fin length → ℝ) :=
    spatialBinPatternBlockEvent width bins
  have hfactor := iidSequenceLaw_measure_forall_variableConsecutiveBlockEvent
    (ν := ν) (length := fun _ : ℕ => length) (blocks := q) event
    (fun j => by
      by_cases hbin : bins j.castSucc = bins j.succ
      · simp only [event, spatialBinPatternBlockEvent, if_pos hbin]
        exact measurableSet_blockOscillationEvent width length
      · simp [event, spatialBinPatternBlockEvent, hbin])
  have hpatterns : spatialBinPatternEvent width length bins =
      {increment : ℕ → ℝ | ∀ j : Fin q,
        Combinatorics.Sequence.blockCoordinates
          (AdditivePath.blockStart (fun _ : ℕ => length) j.val)
          length increment ∈ event j} := by
    ext increment
    simp [spatialBinPatternEvent, event, AdditivePath.blockStart_const]
  rw [hpatterns]
  simpa only [event] using hfactor

/-- The fixed-pattern probability is the one-block oscillation probability
raised to the number of unchanged-bin blocks. -/
theorem iidSequenceLaw_measure_spatialBinPatternEvent_eq_pow
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {q K length : ℕ} (width : ℝ)
    (bins : Fin (q + 1) → Fin (K + 1)) :
    iidSequenceLaw ν (spatialBinPatternEvent width length bins) =
      (iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 length increment ∈
          blockOscillationEvent width length}) ^
        (spatialBinGoodBlockSet bins).card := by
  rw [iidSequenceLaw_measure_spatialBinPatternEvent]
  let p : ℝ≥0∞ := iidSequenceLaw ν {increment : ℕ → ℝ |
    Combinatorics.Sequence.blockCoordinates 0 length increment ∈
      blockOscillationEvent width length}
  have hfactor (j : Fin q) :
      iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 length increment ∈
          spatialBinPatternBlockEvent width bins j} =
        if bins j.castSucc = bins j.succ then p else 1 := by
    by_cases hbin : bins j.castSucc = bins j.succ
    · simp [spatialBinPatternBlockEvent, hbin, p]
    · simp [spatialBinPatternBlockEvent, hbin, p]
  calc
    _ = ∏ j : Fin q, (if bins j.castSucc = bins j.succ then p else 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      exact hfactor j
    _ = p ^ (spatialBinGoodBlockSet bins).card := by
      have hmem (j : Fin q) :
          (bins j.castSucc = bins j.succ) =
            (j ∈ spatialBinGoodBlockSet bins) := by
        simp [spatialBinGoodBlockSet]
      simp only [hmem]
      rw [Finset.prod_ite_mem]
      simp [Finset.prod_const]
    _ = _ := rfl

/-- Finite type of all nonincreasing spatial-bin patterns with `q` blocks
and `K+1` bin values. -/
def MonotoneSpatialBinPattern (q K : ℕ) :=
  {bins : Fin (q + 1) → Fin (K + 1) //
    ∀ i j, i ≤ j → bins j ≤ bins i}

noncomputable instance (q K : ℕ) : Fintype (MonotoneSpatialBinPattern q K) :=
  Fintype.ofInjective (fun bins : MonotoneSpatialBinPattern q K => bins.1)
    Subtype.coe_injective

/-- A crude cardinality bound for monotone patterns, obtained by counting
all bin-valued sequences. -/
theorem card_monotoneSpatialBinPattern_le (q K : ℕ) :
    Fintype.card (MonotoneSpatialBinPattern q K) ≤ (K + 1) ^ (q + 1) := by
  classical
  calc
    Fintype.card (MonotoneSpatialBinPattern q K) ≤
        Fintype.card (Fin (q + 1) → Fin (K + 1)) :=
      Fintype.card_le_of_injective (fun bins : MonotoneSpatialBinPattern q K => bins.1)
        Subtype.coe_injective
    _ = (K + 1) ^ (q + 1) := by simp

/-- The union of fixed-pattern events over all nonincreasing spatial-bin
patterns. -/
def monotoneSpatialBinPatternUnionEvent {q K : ℕ} (width : ℝ) (length : ℕ) :
    Set (ℕ → ℝ) :=
  ⋃ bins : MonotoneSpatialBinPattern q K,
    spatialBinPatternEvent width length bins.1

theorem measurableSet_monotoneSpatialBinPatternUnionEvent
    {q K : ℕ} (width : ℝ) (length : ℕ) :
    MeasurableSet (monotoneSpatialBinPatternUnionEvent
      (q := q) (K := K) width length) := by
  classical
  exact MeasurableSet.iUnion fun bins =>
    measurableSet_spatialBinPatternEvent width length bins.1

/-- The finite union bound for monotone patterns.  If the probability of a
single-block oscillation is `p`, then every unchanged-bin block contributes
one factor `p`; each monotone pattern has at least `q-K-1` such blocks. -/
theorem iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {q K length : ℕ} (width : ℝ) (hK : K + 1 ≤ q) :
    iidSequenceLaw ν (monotoneSpatialBinPatternUnionEvent
        (q := q) (K := K) width length) ≤
      ((K + 1) ^ (q + 1) : ℝ≥0∞) *
        (iidSequenceLaw ν {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 length increment ∈
            blockOscillationEvent width length}) ^ (q - (K + 1)) := by
  classical
  let p : ℝ≥0∞ := iidSequenceLaw ν {increment : ℕ → ℝ |
    Combinatorics.Sequence.blockCoordinates 0 length increment ∈
      blockOscillationEvent width length}
  have hp : p ≤ 1 := by
    dsimp [p]
    calc
      iidSequenceLaw ν {increment : ℕ → ℝ |
          Combinatorics.Sequence.blockCoordinates 0 length increment ∈
            blockOscillationEvent width length} ≤
          iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  calc
    iidSequenceLaw ν (monotoneSpatialBinPatternUnionEvent
        (q := q) (K := K) width length) ≤
        ∑ bins : MonotoneSpatialBinPattern q K,
          iidSequenceLaw ν (spatialBinPatternEvent width length bins.1) := by
      rw [monotoneSpatialBinPatternUnionEvent]
      exact measure_iUnion_fintype_le (iidSequenceLaw ν) _
    _ ≤ ∑ _bins : MonotoneSpatialBinPattern q K, p ^ (q - (K + 1)) := by
      apply Finset.sum_le_sum
      intro bins _
      rw [iidSequenceLaw_measure_spatialBinPatternEvent_eq_pow]
      apply pow_le_pow_right_of_le_one' hp
      have hgood := card_spatialBinGoodBlockSet_ge bins.1 bins.2
      omega
    _ = (Fintype.card (MonotoneSpatialBinPattern q K) : ℝ≥0∞) *
          p ^ (q - (K + 1)) := by simp
    _ ≤ ((K + 1) ^ (q + 1) : ℝ≥0∞) * p ^ (q - (K + 1)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_monotoneSpatialBinPattern_le q K
    _ = _ := rfl

/-- An oscillation bound for the additive path over one segment is exactly
the finite-block oscillation event for its increments. -/
theorem blockOscillationEvent_of_additiveSegment
    {start length : ℕ} {increment : ℕ → ℝ} {width : ℝ}
    (hsegment : OscillationBounded
      (fun k : Fin (length + 1) =>
        AdditivePath.displacement (start + (k : ℕ)) increment) width) :
    blockOscillationEvent width length
      (Combinatorics.Sequence.blockCoordinates start length increment) := by
  change OscillationBounded
    (fun k : Fin (length + 1) =>
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates start length increment) k)
    width
  intro i j
  change |Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates start length increment) i -
    Fin.partialSum
      (Combinatorics.Sequence.blockCoordinates start length increment) j| ≤ width
  have hpartial (k : Fin (length + 1)) :
      Fin.partialSum (Combinatorics.Sequence.blockCoordinates start length increment) k =
        AdditivePath.displacement (start + (k : ℕ)) increment -
          AdditivePath.displacement start increment := by
    rw [partialSum_blockCoordinates, AdditivePath.displacement_add_eq_add_blockSum]
    ring
  rw [hpartial i, hpartial j]
  calc
    |(AdditivePath.displacement (start + (i : ℕ)) increment -
          AdditivePath.displacement start increment) -
      (AdditivePath.displacement (start + (j : ℕ)) increment -
          AdditivePath.displacement start increment)| =
        |AdditivePath.displacement (start + (i : ℕ)) increment -
          AdditivePath.displacement (start + (j : ℕ)) increment| := by
      congr 1
      ring
    _ ≤ width := hsegment i j

/-- A no-large-drawdown path with a deterministic upper bound admits a
nonincreasing finite spatial-bin encoding. Every unchanged-bin block belongs
to the corresponding translation-invariant oscillation event. This is the
deterministic finite-pattern reduction used before taking the finite union
over bin patterns. -/
theorem exists_spatialBinPatternEvent_of_noLargeDrop
    {horizon blocks blockLength : ℕ}
    (increment : ℕ → ℝ) (upper width delta : ℝ)
    (hwidth : 0 < width)
    (hnoDrop : ∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta)
    (hupper : ∀ i ≤ horizon, AdditivePath.displacement i increment ≤ upper)
    (hblocks : blocks * blockLength ≤ horizon) :
    ∃ bins : Fin (blocks + 1) → Fin (⌊upper / width⌋₊ + 1),
      (∀ i j, i ≤ j → bins j ≤ bins i) ∧
        increment ∈ spatialBinPatternEvent (width + delta) blockLength bins := by
  let path : ℕ → ℝ := fun t => AdditivePath.displacement t increment
  have hzero : path 0 = 0 := by simp [path]
  have hnoDrop' : ∀ i j : ℕ, i ≤ j → j ≤ horizon →
      path i - path j ≤ delta := hnoDrop
  have hupper' : ∀ i ≤ horizon, path i ≤ upper := hupper
  have hblocks' : 0 + blocks * blockLength ≤ horizon := by simpa using hblocks
  obtain ⟨bins, hmono, hindex, hgood⟩ :=
    exists_spatialBinSequence_for_noLargeDrop
      (horizon := horizon) (remainder := 0) (blocks := blocks)
      (blockLength := blockLength)
      path upper width delta
      hzero hwidth hnoDrop' hupper' hblocks'
  refine ⟨bins, hmono, ?_⟩
  intro j
  by_cases hsame : bins j.castSucc = bins j.succ
  · have hsegment : OscillationBounded
        (fun k : Fin (blockLength + 1) =>
          AdditivePath.displacement (j.val * blockLength + (k : ℕ)) increment)
        (width + delta) := by
      intro i k
      have hi := by
        simpa [path] using
          hgood j hsame (i : ℕ) (Nat.le_of_lt_succ i.isLt)
      have hk := by
        simpa [path] using
          hgood j hsame (k : ℕ) (Nat.le_of_lt_succ k.isLt)
      have hupperDiff :
          AdditivePath.displacement (j.val * blockLength + (i : ℕ)) increment -
            AdditivePath.displacement (j.val * blockLength + (k : ℕ)) increment ≤
              width + delta := by
        linarith [hi.2, hk.1]
      have hlowerDiff :
          -(width + delta) ≤
            AdditivePath.displacement (j.val * blockLength + (i : ℕ)) increment -
              AdditivePath.displacement (j.val * blockLength + (k : ℕ)) increment := by
        linarith [hk.2, hi.1]
      exact abs_le.mpr ⟨hlowerDiff, hupperDiff⟩
    have hblock := blockOscillationEvent_of_additiveSegment hsegment
    rw [spatialBinPatternBlockEvent, if_pos hsame]
    change OscillationBounded
      (fun k : Fin (blockLength + 1) =>
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates
            (j.val * blockLength) blockLength increment) k)
      (width + delta)
    change OscillationBounded
      (fun k : Fin (blockLength + 1) =>
        Fin.partialSum
          (Combinatorics.Sequence.blockCoordinates
            (j.val * blockLength) blockLength increment) k)
      (width + delta) at hblock
    exact hblock
  · simp [spatialBinPatternBlockEvent, hsame]

/-- A finite-horizon event imposing both a drawdown bound and an endpoint
upper bound. -/
def noLargeDropEndpointBelowEvent (horizon : ℕ) (delta threshold : ℝ) :
    Set (ℕ → ℝ) :=
  {increment | (∀ i j : ℕ, i ≤ j → j ≤ horizon →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ delta) ∧
    AdditivePath.displacement horizon increment ≤ threshold}

/-- Every path in the drawdown-and-endpoint event belongs to a monotone
spatial-bin pattern event, with the finite bin range determined by the
endpoint ceiling. -/
theorem noLargeDropEndpointBelowEvent_subset_monotoneSpatialBinPatternUnionEvent
    {horizon blocks blockLength : ℕ} (delta width threshold : ℝ)
    (hwidth : 0 < width) (hblocks : blocks * blockLength ≤ horizon) :
    noLargeDropEndpointBelowEvent horizon delta threshold ⊆
      monotoneSpatialBinPatternUnionEvent
        (q := blocks)
        (K := ⌊(threshold + delta) / width⌋₊)
        (width + delta) blockLength := by
  intro increment h
  have hupper := additivePath_le_threshold_add_delta_of_noLargeDrop
    increment delta threshold h.1 h.2
  obtain ⟨bins, hmono, hpattern⟩ :=
    exists_spatialBinPatternEvent_of_noLargeDrop
      (horizon := horizon) (blocks := blocks)
      (blockLength := blockLength) increment (threshold + delta) width delta
      hwidth h.1 hupper hblocks
  exact Set.mem_iUnion.mpr ⟨⟨bins, hmono⟩, hpattern⟩

/-- A one-block exponential estimate and a scalar entropy condition for the
finite set of patterns imply exponential decay in the number of blocks.
The block probability is kept explicit; the scalar condition records the
required domination of pattern count by good-block decay. -/
theorem iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le_exp
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {q K length : ℕ} (width rate c : ℝ)
    (hK : K + 1 ≤ q) (hrate : 0 < rate) (hc : 0 < c)
    (hblock : iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 length increment ∈
          blockOscillationEvent width length} ≤
      ENNReal.ofReal (Real.exp (-rate)))
    (hparameters :
      ((K + 1) ^ (q + 1) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-rate)) ^ (q - (K + 1)) ≤
        ENNReal.ofReal (Real.exp (-c * q))) :
    0 < rate ∧ 0 < c ∧
      iidSequenceLaw ν (monotoneSpatialBinPatternUnionEvent
        (q := q) (K := K) width length) ≤
        ENNReal.ofReal (Real.exp (-c * q)) := by
  have hunion := iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le
    (ν := ν) (q := q) (K := K) (length := length) width hK
  have hpow := pow_le_pow_left' hblock (q - (K + 1))
  refine ⟨hrate, hc, ?_⟩
  calc
    iidSequenceLaw ν (monotoneSpatialBinPatternUnionEvent
        (q := q) (K := K) width length) ≤
        ((K + 1) ^ (q + 1) : ℝ≥0∞) *
          (iidSequenceLaw ν {increment : ℕ → ℝ |
            Combinatorics.Sequence.blockCoordinates 0 length increment ∈
              blockOscillationEvent width length}) ^ (q - (K + 1)) := hunion
    _ ≤ ((K + 1) ^ (q + 1) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-rate)) ^ (q - (K + 1)) := by
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ ENNReal.ofReal (Real.exp (-c * q)) := hparameters

/-- For a fixed number of spatial bins, the entropy term is eventually
absorbed by any strictly smaller exponential rate than the one-block rate.
This is the finite-pattern estimate needed before converting the block count
to elapsed time: `K` is fixed while the number of blocks tends to infinity. -/
theorem eventually_finitePatternEntropyCondition_of_rate_gap
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) {K : ℕ} {rate c : ℝ}
    (hrate : 0 < rate) (hc : 0 < c)
    (hgap : c < rate - Real.log ((K + 1 : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop,
      ((K + 1) ^ (q n + 1) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-rate)) ^ (q n - (K + 1)) ≤
        ENNReal.ofReal (Real.exp (-c * (q n : ℝ))) := by
  let binCount : ℝ := (K + 1 : ℕ)
  let gap : ℝ := rate - Real.log binCount - c
  let offset : ℝ := Real.log binCount + rate * binCount
  have hbinCountPos : 0 < binCount := by
    dsimp [binCount]
    positivity
  have hgapPos : 0 < gap := by
    dsimp [gap, binCount]
    linarith
  have hqReal : Tendsto (fun n => (q n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hq
  have hlarge : ∀ᶠ n : ℕ in atTop,
      offset / gap < (q n : ℝ) :=
    hqReal.eventually (eventually_gt_atTop (offset / gap))
  have hKle : ∀ᶠ n : ℕ in atTop, K + 1 ≤ q n :=
    hq.eventually (eventually_ge_atTop (K + 1))
  filter_upwards [hlarge, hKle] with n hlarge hKle
  have hlarge' : offset < gap * (q n : ℝ) :=
    by simpa [mul_comm] using (div_lt_iff₀ hgapPos).mp hlarge
  have hlinear :
      ((q n + 1 : ℕ) : ℝ) * Real.log binCount -
          rate * ((q n - (K + 1) : ℕ) : ℝ) ≤
        -c * (q n : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hKle]
    have hbin : ((K + 1 : ℕ) : ℝ) = binCount := by simp [binCount]
    have hlarge'' : Real.log binCount + rate * binCount <
        (rate - Real.log binCount - c) * (q n : ℝ) := by
      simpa [gap, offset] using hlarge'
    rw [hbin]
    have hid :
        ((q n : ℝ) + 1) * Real.log binCount -
            rate * ((q n : ℝ) - binCount) + c * (q n : ℝ) =
          Real.log binCount + rate * binCount -
            (rate - Real.log binCount - c) * (q n : ℝ) := by ring
    have hstrict :
        ((q n : ℝ) + 1) * Real.log binCount -
            rate * ((q n : ℝ) - binCount) < -c * (q n : ℝ) := by
      have hsum :
          ((q n : ℝ) + 1) * Real.log binCount -
              rate * ((q n : ℝ) - binCount) + c * (q n : ℝ) < 0 := by
        rw [hid]
        linarith [hlarge'']
      linarith
    simpa using le_of_lt hstrict
  have hbase : binCount ^ (q n + 1) =
      Real.exp (((q n + 1 : ℕ) : ℝ) * Real.log binCount) := by
    calc
      binCount ^ (q n + 1) =
          (Real.exp (Real.log binCount)) ^ (q n + 1) := by
            rw [Real.exp_log hbinCountPos]
      _ = Real.exp (((q n + 1 : ℕ) : ℝ) * Real.log binCount) := by
            rw [← Real.exp_nat_mul]
  have htail : Real.exp (-rate) ^ (q n - (K + 1)) =
      Real.exp (-rate * ((q n - (K + 1) : ℕ) : ℝ)) := by
    calc
      _ = Real.exp (((q n - (K + 1) : ℕ) : ℝ) * (-rate)) := by
        rw [← Real.exp_nat_mul]
      _ = _ := by congr 1 <;> ring
  have hreal :
      binCount ^ (q n + 1) * Real.exp (-rate) ^ (q n - (K + 1)) ≤
        Real.exp (-c * (q n : ℝ)) := by
    have hvalue :
        binCount ^ (q n + 1) * Real.exp (-rate) ^ (q n - (K + 1)) =
          Real.exp (((q n + 1 : ℕ) : ℝ) * Real.log binCount -
            rate * ((q n - (K + 1) : ℕ) : ℝ)) := by
      rw [hbase, htail, ← Real.exp_add]
      congr 1
      ring
    rw [hvalue]
    exact Real.exp_le_exp.mpr hlinear
  have hbinCountPow :
      (((K + 1 : ℕ) : ℝ≥0∞) ^ (q n + 1)) =
        ENNReal.ofReal (binCount ^ (q n + 1)) := by
    have hcastNat : ((K + 1 : ℕ) : ℝ≥0∞) =
        ENNReal.ofReal ((K + 1 : ℕ) : ℝ) :=
      (ENNReal.ofReal_natCast (K + 1)).symm
    have hcastReal : ((K + 1 : ℕ) : ℝ) = binCount := by
      simp [binCount]
    change ((K + 1 : ℕ) : ℝ≥0∞) ^ (q n + 1) =
      ENNReal.ofReal (binCount ^ (q n + 1))
    rw [hcastNat,
      ENNReal.ofReal_pow (p := ((K + 1 : ℕ) : ℝ)) (by positivity) (q n + 1),
      hcastReal]
  have hexpPow :
      ENNReal.ofReal (Real.exp (-rate)) ^ (q n - (K + 1)) =
        ENNReal.ofReal (Real.exp (-rate) ^ (q n - (K + 1))) :=
    (ENNReal.ofReal_pow (Real.exp_nonneg _) _).symm
  have hENNreal :
      (((K + 1 : ℕ) : ℝ≥0∞) ^ (q n + 1)) *
          ENNReal.ofReal (Real.exp (-rate)) ^ (q n - (K + 1)) =
        ENNReal.ofReal
          (binCount ^ (q n + 1) * Real.exp (-rate) ^ (q n - (K + 1))) := by
    rw [hbinCountPow, hexpPow,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ binCount ^ (q n + 1))]
  have hcastSum : (K + 1 : ℝ≥0∞) = ((K + 1 : ℕ) : ℝ≥0∞) := by simp
  rw [hcastSum, hENNreal]
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).2 hreal

/-- The fixed-pattern union bound closes along any diverging block-count
sequence once a single-block exponential estimate is available. The bin count
is fixed, so its logarithmic entropy is negligible per block. -/
theorem eventually_iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le_exp_of_rate_gap
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {blocks length : ℕ → ℕ} {width : ℕ → ℝ} (K : ℕ)
    {rate c : ℝ} (hblocks : Tendsto blocks atTop atTop)
    (hrate : 0 < rate) (hc : 0 < c)
    (hgap : c < rate - Real.log ((K + 1 : ℕ) : ℝ))
    (hblock : ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (length n) increment ∈
          blockOscillationEvent (width n) (length n)} ≤
        ENNReal.ofReal (Real.exp (-rate))) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν (monotoneSpatialBinPatternUnionEvent
        (q := blocks n) (K := K) (width n) (length n)) ≤
        ENNReal.ofReal (Real.exp (-c * (blocks n : ℝ))) := by
  have hentropy := eventually_finitePatternEntropyCondition_of_rate_gap
    hblocks hrate hc hgap
  have hK : ∀ᶠ n : ℕ in atTop, K + 1 ≤ blocks n :=
    hblocks.eventually (eventually_ge_atTop (K + 1))
  filter_upwards [hblock, hentropy, hK] with n hp he hkn
  have hresult := iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le_exp
    (ν := ν) (q := blocks n) (K := K) (length := length n)
    (width n) rate c hkn hrate hc hp he
  exact hresult.2.2

/-- The endpoint event inherits the finite-pattern exponential bound. This
is a finite-horizon reduction only; no asymptotic parameter choice is hidden
in the theorem. -/
theorem iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_exp
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {horizon blocks blockLength : ℕ} (delta width threshold rate c : ℝ)
    (hwidth : 0 < width)
    (hblocks : blocks * blockLength ≤ horizon)
    (hK : ⌊(threshold + delta) / width⌋₊ + 1 ≤ blocks)
    (hrate : 0 < rate) (hc : 0 < c)
    (hblock : iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 blockLength increment ∈
          blockOscillationEvent (width + delta) blockLength} ≤
      ENNReal.ofReal (Real.exp (-rate)))
    (hparameters :
      ((⌊(threshold + delta) / width⌋₊ + 1) ^ (blocks + 1) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-rate)) ^
            (blocks - (⌊(threshold + delta) / width⌋₊ + 1)) ≤
        ENNReal.ofReal (Real.exp (-c * blocks))) :
    0 < rate ∧ 0 < c ∧
      iidSequenceLaw ν (noLargeDropEndpointBelowEvent
        horizon delta threshold) ≤
        ENNReal.ofReal (Real.exp (-c * blocks)) := by
  have hunion := iidSequenceLaw_measure_monotoneSpatialBinPatternUnionEvent_le_exp
    (ν := ν) (q := blocks)
    (K := ⌊(threshold + delta) / width⌋₊) (length := blockLength)
    (width + delta) rate c hK hrate hc hblock hparameters
  rcases hunion with ⟨hrate', hc', hmeasure⟩
  exact ⟨hrate', hc', measure_mono
    (noLargeDropEndpointBelowEvent_subset_monotoneSpatialBinPatternUnionEvent
      delta width threshold hwidth hblocks) |>.trans hmeasure⟩


/-- The drawdown-and-endpoint estimate follows from the entropy-closed
finite-pattern bound when the spatial-bin count is fixed. This is still a
finite-variance random-walk input theorem: the one-block bound remains an
explicit hypothesis and must be supplied by a proved block estimate. -/
theorem eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_exp_of_rate_gap
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {horizon blocks blockLength : ℕ → ℕ}
    {delta width threshold : ℕ → ℝ} (K : ℕ)
    {rate c : ℝ} (hblocksTop : Tendsto blocks atTop atTop)
    (hrate : 0 < rate) (hc : 0 < c)
    (hgap : c < rate - Real.log ((K + 1 : ℕ) : ℝ))
    (hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n)
    (hcomplete : ∀ᶠ n : ℕ in atTop,
      blocks n * blockLength n ≤ horizon n)
    (hbinCount : ∀ᶠ n : ℕ in atTop,
      ⌊(threshold n + delta n) / width n⌋₊ = K)
    (hblock : ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν {increment : ℕ → ℝ |
        Combinatorics.Sequence.blockCoordinates 0 (blockLength n) increment ∈
          blockOscillationEvent (width n + delta n) (blockLength n)} ≤
        ENNReal.ofReal (Real.exp (-rate))) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν (noLargeDropEndpointBelowEvent
        (horizon n) (delta n) (threshold n)) ≤
        ENNReal.ofReal (Real.exp (-c * (blocks n : ℝ))) := by
  have hentropy := eventually_finitePatternEntropyCondition_of_rate_gap
    hblocksTop hrate hc hgap
  have hK : ∀ᶠ n : ℕ in atTop, K + 1 ≤ blocks n :=
    hblocksTop.eventually (eventually_ge_atTop (K + 1))
  filter_upwards [hwidthPos, hcomplete, hbinCount, hblock,
    hentropy, hK] with n hwidthn hcompleten hbin hblockn hentropyn hKn
  have hKn' : ⌊(threshold n + delta n) / width n⌋₊ + 1 ≤ blocks n := by
    rw [hbin]
    exact hKn
  have hparameters :
      ((⌊(threshold n + delta n) / width n⌋₊ + 1) ^ (blocks n + 1) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-rate)) ^
            (blocks n - (⌊(threshold n + delta n) / width n⌋₊ + 1)) ≤
        ENNReal.ofReal (Real.exp (-c * (blocks n : ℝ))) := by
    simpa [hbin] using hentropyn
  have hresult := iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_exp
    (ν := ν) (horizon := horizon n) (blocks := blocks n)
    (blockLength := blockLength n) (delta n) (width n) (threshold n)
    rate c hwidthn hcompleten hKn' hrate hc hblockn hparameters
  exact hresult.2.2


/-- The quotient by a floor-rounded diffusive block length diverges whenever
the horizon is large compared with the square of the spatial scale.  The
statement is deliberately phrased for a real scale: no integer rounding of
the AH parameter is needed. -/
theorem tendsto_diffusiveBlockCount_atTop_of_horizonRatio
    {horizon : ℕ → ℕ} {delta : ℕ → ℝ} {A : ℝ}
    (hdelta : Tendsto delta atTop atTop) (hA : 0 < A)
    (hratio : Tendsto (fun n => (horizon n : ℝ) / delta n ^ 2)
      atTop atTop) :
    Tendsto (fun n => horizon n / ⌊A * delta n ^ 2⌋₊) atTop atTop := by
  let length : ℕ → ℕ := fun n => ⌊A * delta n ^ 2⌋₊
  let blocks : ℕ → ℕ := fun n => horizon n / length n
  have hdeltaPos : ∀ᶠ n : ℕ in atTop, 0 < delta n :=
    hdelta.eventually_gt_atTop 0
  have hlengthTop : Tendsto length atTop atTop := by
    apply Asymptotics.tendsto_floorBlockLength_atTop
    have hsquare : Tendsto (fun n => delta n * delta n) atTop atTop :=
      hdelta.atTop_mul_atTop₀ hdelta
    simpa [length, Asymptotics.floorBlockLength, pow_two, mul_comm] using
      hsquare.const_mul_atTop hA
  have hlengthPos : ∀ᶠ n : ℕ in atTop, 0 < length n :=
    hlengthTop.eventually_gt_atTop 0
  have hlengthLe : ∀ᶠ n : ℕ in atTop,
      (length n : ℝ) ≤ A * delta n ^ 2 := by
    filter_upwards [hdeltaPos] with n hδ
    exact Nat.floor_le (mul_nonneg hA.le (sq_nonneg (delta n)))
  have hratioLower : ∀ᶠ n : ℕ in atTop,
      (horizon n : ℝ) / (length n : ℝ) ≥
        ((horizon n : ℝ) / delta n ^ 2) / A := by
    filter_upwards [hdeltaPos, hlengthPos, hlengthLe] with n hδ hm hle
    have hδsq : 0 < delta n ^ 2 := sq_pos_of_pos hδ
    have hlenReal : 0 < (length n : ℝ) := by exact_mod_cast hm
    have hAδ : 0 < A * delta n ^ 2 := mul_pos hA hδsq
    calc
      ((horizon n : ℝ) / delta n ^ 2) / A =
          (horizon n : ℝ) / (A * delta n ^ 2) := by
            field_simp [hA.ne', hδsq.ne']
      _ ≤ (horizon n : ℝ) / (length n : ℝ) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) hlenReal hle
  have hratioLowerTop : Tendsto
      (fun n => ((horizon n : ℝ) / delta n ^ 2) / A) atTop atTop :=
    by
      simpa [div_eq_mul_inv, mul_assoc, mul_comm] using
        hratio.const_mul_atTop (inv_pos.mpr hA)
  have hratioBlocks : Tendsto (fun n =>
      (horizon n : ℝ) / (length n : ℝ)) atTop atTop :=
    Filter.tendsto_atTop_mono' atTop hratioLower hratioLowerTop
  have hblocks : Tendsto blocks atTop atTop := by
    refine tendsto_atTop.2 fun k => ?_
    have hkraw : ∀ᶠ n : ℕ in atTop,
        ((k + 1 : ℕ) : ℝ) ≤ (horizon n : ℝ) / (length n : ℝ) :=
      hratioBlocks.eventually
        (eventually_ge_atTop ((k + 1 : ℕ) : ℝ))
    have hk : ∀ᶠ n : ℕ in atTop,
        ((k + 1 : ℕ) : ℝ) ≤ (horizon n : ℝ) / (length n : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hkraw
    filter_upwards [hk, hlengthPos] with n hk hm
    have hmul : ((k + 1 : ℕ) : ℝ) * (length n : ℝ) ≤ (horizon n : ℝ) :=
      (le_div_iff₀ (by exact_mod_cast hm)).1 hk
    have hmulNat : (k + 1) * length n ≤ horizon n := by exact_mod_cast hmul
    have hdiv : k + 1 ≤ horizon n / length n :=
      (Nat.le_div_iff_mul_le hm).2 (by simpa [Nat.succ_mul] using hmulNat)
    dsimp [blocks, length] at hdiv ⊢
    omega
  simpa [blocks, length] using hblocks

/-- The finite-cover sharp-rate theorem can be combined with a fixed spatial
bin width to choose every block parameter internally.  The cover is chosen
first; its diffusive constant is then enlarged enough to absorb the fixed
spatial-bin entropy. -/
theorem exists_ah_diffusive_parameters
    {c blockTarget : ℝ} (hc : 0 < c) (hblockTarget : 0 < blockTarget)
    (hsharp : blockTarget < Real.pi ^ 2 / 2) :
    ∃ A eta enlargement : ℝ, ∃ count : ℕ,
      0 < A ∧ 0 < eta ∧ 0 < enlargement ∧ 0 < count ∧
      finiteCoverCorridorExponential count
        ((1 + enlargement) / Real.sqrt (A / (1 + eta) ^ 2)) < 1 / 2 ∧
      A * blockTarget < finiteCoverBlockRate count
        ((1 + enlargement) / Real.sqrt (A / (1 + eta) ^ 2)) -
          Real.log ((⌊(1 + 1 / c) / eta⌋₊ + 1 : ℕ) : ℝ) := by
  let gap : ℝ := Real.pi ^ 2 / 2 - blockTarget
  have hgap : 0 < gap := by dsimp [gap]; linarith
  let eta : ℝ := min 1 (gap / (8 * blockTarget))
  have heta : 0 < eta := by
    dsimp [eta]
    apply lt_min
    · norm_num
    · positivity
  have hetaOne : eta ≤ 1 := by dsimp [eta]; exact min_le_left _ _
  have hetaGap : eta ≤ gap / (8 * blockTarget) := by
    dsimp [eta]
    exact min_le_right _ _
  have hetaBlock : eta * blockTarget ≤ gap / 8 := by
    have h := mul_le_mul_of_nonneg_right hetaGap hblockTarget.le
    have hcancel : gap / (8 * blockTarget) * blockTarget = gap / 8 := by
      field_simp [ne_of_gt hblockTarget]
    rw [hcancel] at h
    exact h
  have hetaSq : eta ^ 2 ≤ eta := by
    nlinarith [mul_nonneg heta.le (sub_nonneg.mpr hetaOne)]
  have hetaSqBlock : eta ^ 2 * blockTarget ≤ gap / 8 := by
    calc
      eta ^ 2 * blockTarget ≤ eta * blockTarget :=
        mul_le_mul_of_nonneg_right hetaSq hblockTarget.le
      _ ≤ gap / 8 := hetaBlock
  have hscaledBlock : (1 + eta) ^ 2 * blockTarget ≤
      Real.pi ^ 2 / 2 - gap / 2 := by
    calc
      (1 + eta) ^ 2 * blockTarget = blockTarget +
          2 * (eta * blockTarget) + eta ^ 2 * blockTarget := by ring
      _ ≤ blockTarget + 3 * gap / 8 := by nlinarith [hetaBlock, hetaSqBlock]
      _ ≤ Real.pi ^ 2 / 2 - gap / 2 := by dsimp [gap]; ring_nf; linarith
  let binCount : ℕ := ⌊(1 + 1 / c) / eta⌋₊
  let entropyLog : ℝ := Real.log ((binCount + 1 : ℕ) : ℝ)
  have hentropyLog : 0 ≤ entropyLog := by
    apply Real.log_nonneg
    have hcount : (1 : ℝ) ≤ ((binCount + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_left 1 binCount)
    exact hcount
  let eps : ℝ := gap / 16
  have heps : 0 < eps := by dsimp [eps]; positivity
  obtain ⟨count, hcount, enlargement, C₀, henlargement, hC₀,
      hspectral₀, _hbound₀, hsharpRate⟩ :=
    exists_finiteCover_parameters_for_sharp_rate heps
  let prefactor : ℝ := Real.log (16 * (count : ℝ))
  let lambda : ℝ := Real.pi ^ 2 /
    (2 * ((1 + 3 / (count : ℝ)) * (1 + enlargement)) ^ 2)
  have hprefactor : 0 ≤ prefactor := by
    apply Real.log_nonneg
    have hcountOne : (1 : ℝ) ≤ (count : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hcount.ne')
    nlinarith
  have hscaledSharp : prefactor / C₀ - lambda <
      -(Real.pi ^ 2) / 2 + eps := by
    have hformula := scaledLog_two_finiteCoverRangeBound_diffusive
      hcount henlargement hC₀
    rw [hformula] at hsharpRate
    simpa [prefactor, lambda, div_eq_mul_inv, mul_comm] using hsharpRate
  have hlambdaBase : Real.pi ^ 2 / 2 - eps < lambda - prefactor / C₀ := by
    dsimp [eps] at hscaledSharp ⊢
    linarith [hscaledSharp]
  let C : ℝ := max C₀ (entropyLog / eps + 1)
  have hC₀C : C₀ ≤ C := by dsimp [C]; exact le_max_left _ _
  have hCbig : entropyLog / eps < C := by
    dsimp [C]
    exact lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one) (le_max_right _ _)
  have hC : 0 < C := lt_of_lt_of_le hC₀ hC₀C
  have hentropySmall : entropyLog / C < eps := by
    apply (div_lt_iff₀ hC).2
    have hprod := (div_lt_iff₀ heps).mp hCbig
    nlinarith [hprod]
  have hprefactorSmall : prefactor / C ≤ prefactor / C₀ :=
    div_le_div_of_nonneg_left hprefactor hC₀ hC₀C
  have hlambdaNet : Real.pi ^ 2 / 2 - eps < lambda - prefactor / C :=
    lt_of_lt_of_le hlambdaBase (sub_le_sub_left hprefactorSmall lambda)
  let widthC : ℝ := (1 + enlargement) / Real.sqrt C
  let oneBlockRate : ℝ := finiteCoverBlockRate count widthC
  have hformula (D : ℝ) (hD : 0 < D) :
      finiteCoverCorridorExponential count
          ((1 + enlargement) / Real.sqrt D) = Real.exp (-lambda * D) := by
    rw [finiteCoverCorridorExponential_diffusive hcount henlargement hD]
    congr 1
    dsimp [lambda]
    ring
  have hlogExp : Real.log (2 * finiteCoverRangeBound count widthC) = -oneBlockRate := by
    rw [two_mul_finiteCoverRangeBound_eq_exp_neg_rate hcount]
    exact Real.log_exp _
  have hscaledC := scaledLog_two_finiteCoverRangeBound_diffusive
    hcount henlargement hC
  rw [hlogExp] at hscaledC
  have hscaleIdentity : (1 / C) * (-oneBlockRate) = -(oneBlockRate / C) := by
    field_simp [ne_of_gt hC]
  rw [hscaleIdentity] at hscaledC
  have hrateNormalized : oneBlockRate / C = lambda - prefactor / C := by
    dsimp [prefactor, lambda] at hscaledC ⊢
    field_simp [ne_of_gt hC] at hscaledC ⊢
    nlinarith [hscaledC]
  have hnetRate : Real.pi ^ 2 / 2 - 2 * eps <
      oneBlockRate / C - entropyLog / C := by
    rw [hrateNormalized]
    dsimp [prefactor, lambda] at hlambdaNet ⊢
    linarith [hlambdaNet, hentropySmall]
  have hgapCompare : Real.pi ^ 2 / 2 - gap / 2 <
      Real.pi ^ 2 / 2 - 2 * eps := by
    dsimp [eps]
    linarith [hgap]
  have hscaledRate : (1 + eta) ^ 2 * blockTarget <
      oneBlockRate / C - entropyLog / C := by
    exact lt_of_le_of_lt hscaledBlock (lt_trans hgapCompare hnetRate)
  let A : ℝ := C * (1 + eta) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hconst : A / (1 + eta) ^ 2 = C := by
    dsimp [A]
    field_simp [ne_of_gt (by positivity : 0 < 1 + eta)]
  have hspectralC : finiteCoverCorridorExponential count widthC < 1 / 2 := by
    have hspec₀ : Real.exp (-lambda * C₀) < 1 / 2 := by
      rw [hformula C₀ hC₀] at hspectral₀
      exact hspectral₀
    have hlambda : 0 < lambda := by dsimp [lambda]; positivity
    have hmul : lambda * C₀ ≤ lambda * C := mul_le_mul_of_nonneg_left hC₀C hlambda.le
    have hexp : Real.exp (-lambda * C) ≤ Real.exp (-lambda * C₀) :=
      Real.exp_le_exp.mpr (calc
        -lambda * C = -(lambda * C) := by ring
        _ ≤ -(lambda * C₀) := neg_le_neg hmul
        _ = -lambda * C₀ := by ring)
    rw [hformula C hC]
    exact lt_of_le_of_lt hexp hspec₀
  have hAconst : finiteCoverCorridorExponential count
      ((1 + enlargement) / Real.sqrt (A / (1 + eta) ^ 2)) < 1 / 2 := by
    rw [hconst]
    exact hspectralC
  have hAentropy : A * blockTarget < oneBlockRate - entropyLog := by
    have hmul := mul_lt_mul_of_pos_left hscaledRate hC
    have hleft : C * ((1 + eta) ^ 2 * blockTarget) = A * blockTarget := by
      dsimp [A]
      ring
    have hright : C * (oneBlockRate / C - entropyLog / C) =
        oneBlockRate - entropyLog := by
      field_simp [ne_of_gt hC]
    rw [hleft, hright] at hmul
    exact hmul
  have hAentropy' : A * blockTarget < finiteCoverBlockRate count
      ((1 + enlargement) / Real.sqrt (A / (1 + eta) ^ 2)) -
        Real.log ((binCount + 1 : ℕ) : ℝ) := by
    have hrequestedRate : finiteCoverBlockRate count
        ((1 + enlargement) / Real.sqrt (A / (1 + eta) ^ 2)) = oneBlockRate := by
      simp [oneBlockRate, widthC, hconst]
    rw [hrequestedRate]
    simpa [entropyLog, binCount] using hAentropy
  refine ⟨A, eta, enlargement, count, hA, heta, henlargement, hcount,
    hAconst, hAentropy'⟩

/-- Sequential form of the finite-variance AH no-large-drawdown estimate. For
any specified spatial-scale sequence tending to infinity and horizon sequence
with `horizon / delta^2 → ∞`, the fixed-cover Brownian bound supplies the
one-block estimate, the finite-pattern entropy is absorbed internally, and
the floor/remainder loss is absorbed. The uniform-in-`delta`/`horizon` paper
quantifier is proved separately below. The spatial bin count is the explicit
fixed integer `floor((1 + 1/c) / eta)`; no one-block or entropy inequality is
left as an input.

This version is normalized to increment variance one, exactly as the
Brownian BlockBound API.  Restoring a general variance parameter requires a
separate law-scaling theorem. -/
theorem eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsecondMoment : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    {horizon : ℕ → ℕ} {delta : ℕ → ℝ}
    (c target blockTarget : ℝ) (hc : 0 < c)
    (htarget : 0 < target) (hblockTarget : target < blockTarget)
    (hblockTargetUpper : blockTarget < Real.pi ^ 2 / 2)
    (hdelta : Tendsto delta atTop atTop)
    (hratio : Tendsto (fun n => (horizon n : ℝ) / delta n ^ 2)
      atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      iidSequenceLaw ν (noLargeDropEndpointBelowEvent
        (horizon n) (delta n) (delta n / c)) ≤
        ENNReal.ofReal (Real.exp
          (-target * (horizon n : ℝ) / delta n ^ 2)) := by
  obtain ⟨A, eta, enlargement, count, hA, heta, henlargement, hcount,
      hspectral, hentropyRate⟩ :=
    exists_ah_diffusive_parameters hc (lt_trans htarget hblockTarget)
      hblockTargetUpper
  let binCount : ℕ := ⌊(1 + 1 / c) / eta⌋₊
  let blockLength : ℕ → ℕ := fun n => ⌊A * delta n ^ 2⌋₊
  let blocks : ℕ → ℕ := fun n => horizon n / blockLength n
  let oneBlockRate : ℝ := finiteCoverBlockRate count
    ((1 + enlargement) / Real.sqrt (A / (1 + eta) ^ 2))
  have hblocksTop : Tendsto blocks atTop atTop := by
    simpa [blocks, blockLength] using
      tendsto_diffusiveBlockCount_atTop_of_horizonRatio hdelta hA hratio
  have honeBlock := eventually_integerDiffusiveBlockOscillationProbability_le_exp
    ν hcentered hsecondMoment hB hcontinuous hmeasurable hdelta
    hA heta henlargement hcount hspectral
  have hratePos : 0 < oneBlockRate := by
    have hgap : A * blockTarget < oneBlockRate - Real.log ((binCount + 1 : ℕ) : ℝ) := by
      simpa [oneBlockRate, binCount] using hentropyRate
    have hlogNonneg : 0 ≤ Real.log ((binCount + 1 : ℕ) : ℝ) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ (binCount + 1 : ℕ) := by exact_mod_cast (Nat.le_add_left 1 binCount)
      exact this
    have htargetPos' : 0 < blockTarget := lt_trans htarget hblockTarget
    have hAblock : 0 < A * blockTarget := mul_pos hA htargetPos'
    linarith
  have hpattern := eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_exp_of_rate_gap
    (ν := ν) (horizon := horizon) (blocks := blocks) (blockLength := blockLength)
    (delta := delta) (width := fun n => eta * delta n)
    (threshold := fun n => delta n / c) binCount
    (rate := oneBlockRate) (c := A * blockTarget)
    hblocksTop hratePos (mul_pos hA (lt_trans htarget hblockTarget)) hentropyRate
    (by
      filter_upwards [hdelta.eventually_gt_atTop 0] with n hδ
      exact mul_pos heta hδ)
    (by
      filter_upwards [] with n
      dsimp [blocks, blockLength]
      exact Nat.div_mul_le_self _ _)
    (by
      filter_upwards [hdelta.eventually_gt_atTop 0] with n hδ
      have hδne : delta n ≠ 0 := ne_of_gt hδ
      have hetaNe : eta ≠ 0 := ne_of_gt heta
      have hdiv : (delta n / c + delta n) / (eta * delta n) =
          (1 + 1 / c) / eta := by
        field_simp [hc.ne', hetaNe, hδne]
        ring
      simpa [binCount, hdiv])
    (by
      filter_upwards [honeBlock] with n hn
      have hwidth : eta * delta n + delta n = (1 + eta) * delta n := by ring
      simpa [blocks, blockLength, oneBlockRate, hwidth] using hn)
  have hratioLarge : ∀ᶠ n : ℕ in atTop,
      A * blockTarget ≤ (blockTarget - target) *
        ((horizon n : ℝ) / delta n ^ 2) := by
    have hgap : 0 < blockTarget - target := sub_pos.mpr hblockTarget
    filter_upwards [hratio.eventually
      (eventually_ge_atTop (A * blockTarget / (blockTarget - target)))] with n hn
    have hmul := (div_le_iff₀ hgap).1 hn
    simpa [mul_comm] using hmul
  filter_upwards [hpattern, hratioLarge,
    hdelta.eventually_gt_atTop 0,
    Asymptotics.eventually_floorBlockLength_pos (by
      have hsquare : Tendsto (fun n => delta n * delta n) atTop atTop :=
        hdelta.atTop_mul_atTop₀ hdelta
      simpa [Asymptotics.floorBlockLength, blockLength, pow_two, mul_comm] using
        hsquare.const_mul_atTop hA)] with n hpn hratioN hδ hlen
  have hlengthLe : (blockLength n : ℝ) ≤ A * delta n ^ 2 := by
    exact Nat.floor_le (mul_nonneg hA.le (sq_nonneg (delta n)))
  have hlen' : 0 < blockLength n := by
    simpa [blockLength, Asymptotics.floorBlockLength, pow_two] using hlen
  have hmod : horizon n % blockLength n < blockLength n :=
    Nat.mod_lt _ hlen'
  have hdivmod : horizon n / blockLength n * blockLength n +
      horizon n % blockLength n = horizon n := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod (horizon n) (blockLength n))
  have hcastDivmod : (blocks n : ℝ) * (blockLength n : ℝ) +
      ((horizon n % blockLength n : ℕ) : ℝ) = (horizon n : ℝ) := by
    have hcast : ((horizon n / blockLength n : ℕ) : ℝ) *
        (blockLength n : ℝ) + ((horizon n % blockLength n : ℕ) : ℝ) =
          (horizon n : ℝ) := by exact_mod_cast hdivmod
    simpa [blocks] using hcast
  have hmodCast : ((horizon n % blockLength n : ℕ) : ℝ) < (blockLength n : ℝ) := by
    exact_mod_cast hmod
  have hdenPos : 0 < A * delta n ^ 2 := mul_pos hA (sq_pos_of_pos hδ)
  have hquot : (horizon n : ℝ) / (A * delta n ^ 2) < (blocks n : ℝ) + 1 := by
    apply (div_lt_iff₀ hdenPos).2
    rw [← hcastDivmod]
    nlinarith [hmodCast, hlengthLe]
  have hblockCountLower : (blocks n : ℝ) >
      (horizon n : ℝ) / (A * delta n ^ 2) - 1 := by linarith
  have hcancel : A * ((horizon n : ℝ) / (A * delta n ^ 2)) =
      (horizon n : ℝ) / delta n ^ 2 := by
    field_simp [hA.ne', (sq_pos_of_pos hδ).ne']
  have hrateLower : A * blockTarget * (blocks n : ℝ) ≥
      blockTarget * ((horizon n : ℝ) / delta n ^ 2) - A * blockTarget := by
    have hbpos : 0 < A * blockTarget := mul_pos hA (lt_trans htarget hblockTarget)
    have hmul := mul_lt_mul_of_pos_left hblockCountLower hbpos
    nlinarith [hcancel]
  have htargetExponent : target * ((horizon n : ℝ) / delta n ^ 2) ≤
      A * blockTarget * (blocks n : ℝ) := by
    have hrateBound : target * ((horizon n : ℝ) / delta n ^ 2) + A * blockTarget ≤
        blockTarget * ((horizon n : ℝ) / delta n ^ 2) := by
      nlinarith [hratioN]
    nlinarith [hrateLower, hrateBound]
  have hprobExp : ENNReal.ofReal (Real.exp
      (-(A * blockTarget) * (blocks n : ℝ))) ≤
        ENNReal.ofReal (Real.exp
          (-target * (horizon n : ℝ) / delta n ^ 2)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have htargetExponent' : target * (horizon n : ℝ) / delta n ^ 2 ≤
        A * blockTarget * (blocks n : ℝ) := by
      calc
        target * (horizon n : ℝ) / delta n ^ 2 =
            target * ((horizon n : ℝ) / delta n ^ 2) := by ring
        _ ≤ A * blockTarget * (blocks n : ℝ) := htargetExponent
    calc
      -(A * blockTarget) * (blocks n : ℝ) =
          -((A * blockTarget) * (blocks n : ℝ)) := by ring
      _ ≤ -(target * (horizon n : ℝ) / delta n ^ 2) :=
        neg_le_neg htargetExponent'
      _ = -target * (horizon n : ℝ) / delta n ^ 2 := by ring
  calc
    iidSequenceLaw ν (noLargeDropEndpointBelowEvent
        (horizon n) (delta n) (delta n / c)) ≤
      ENNReal.ofReal (Real.exp (-(A * blockTarget) * (blocks n : ℝ))) := hpn
    _ ≤ ENNReal.ofReal (Real.exp
        (-target * (horizon n : ℝ) / delta n ^ 2)) := by
        -- `hpattern` carries the finite-pattern estimate with the per-block
        -- rate `blockTarget`; the deterministic quotient comparison above
        -- inserts the elapsed-time exponent.
        exact hprobExp

/-- Uniform-in-scale version of the finite-variance Aïdékon–Hu no-large-drop
estimate.  For every positive endpoint parameter `c`, every target rate below
the Brownian spectral rate, and every positive polynomial excess `p`, all
sufficiently large spatial scales `delta` and all horizons
`horizon ≥ delta^(2+p)` satisfy the claimed exponential bound.  The proof is a
sequential compactness argument: a failure of the uniform quantifiers would
give counterexample sequences with `delta → ∞` and `horizon / delta^2 → ∞`,
contradicting the sequence theorem above.

The increment variance is normalized to one, as in the Brownian block-bound
API. -/
theorem exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hcentered : ∫ x : ℝ, x ∂ν = 0)
    (hsecondMoment : ∫ x : ℝ, x ^ 2 ∂ν = 1)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (c target blockTarget p : ℝ) (hc : 0 < c)
    (htarget : 0 < target) (hblockTarget : target < blockTarget)
    (hblockTargetUpper : blockTarget < Real.pi ^ 2 / 2) (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ delta : ℝ, delta0 ≤ delta → ∀ horizon : ℕ,
        delta ^ (2 + p) ≤ (horizon : ℝ) →
          iidSequenceLaw ν (noLargeDropEndpointBelowEvent
            horizon delta (delta / c)) ≤
            ENNReal.ofReal (Real.exp
              (-target * (horizon : ℝ) / delta ^ 2)) := by
  by_contra hnoUniform
  have hbad : ∀ delta0 : ℝ, 0 < delta0 →
      ∃ delta : ℝ, delta0 ≤ delta ∧ ∃ horizon : ℕ,
        delta ^ (2 + p) ≤ (horizon : ℝ) ∧
          ¬ iidSequenceLaw ν (noLargeDropEndpointBelowEvent
            horizon delta (delta / c)) ≤
              ENNReal.ofReal (Real.exp
                (-target * (horizon : ℝ) / delta ^ 2)) := by
    intro delta0 hdelta0
    by_contra hnotBad
    apply hnoUniform
    refine ⟨delta0, hdelta0, ?_⟩
    intro delta hdelta horizon hlarge
    by_contra hnotBound
    exact hnotBad ⟨delta, hdelta, horizon, hlarge, hnotBound⟩
  have hbadNat : ∀ n : ℕ, ∃ delta : ℝ, (n : ℝ) ≤ delta ∧
      ∃ horizon : ℕ, delta ^ (2 + p) ≤ (horizon : ℝ) ∧
        ¬ iidSequenceLaw ν (noLargeDropEndpointBelowEvent
          horizon delta (delta / c)) ≤
            ENNReal.ofReal (Real.exp
              (-target * (horizon : ℝ) / delta ^ 2)) := by
    intro n
    obtain ⟨delta, hdelta, horizon, hlarge, hbadBound⟩ :=
      hbad (max (n : ℝ) 1) (lt_of_lt_of_le (by norm_num)
        (le_max_right _ _))
    exact ⟨delta, le_trans (le_max_left _ _) hdelta,
      horizon, hlarge, hbadBound⟩
  choose delta hdeltaLower horizon hpower hbadBound using hbadNat
  have hdeltaTop : Tendsto delta atTop atTop :=
    tendsto_atTop_mono' atTop (Filter.Eventually.of_forall hdeltaLower)
      tendsto_natCast_atTop_atTop
  have hdeltaPos : ∀ᶠ n : ℕ in atTop, 0 < delta n :=
    hdeltaTop.eventually_gt_atTop 0
  have hratioLower : ∀ᶠ n : ℕ in atTop,
      delta n ^ p ≤ (horizon n : ℝ) / delta n ^ 2 := by
    filter_upwards [hdeltaPos] with n hδ
    have hpowerEq : delta n ^ (2 + p) = delta n ^ 2 * delta n ^ p := by
      calc
        delta n ^ (2 + p) = delta n ^ (2 : ℝ) * delta n ^ p :=
          Real.rpow_add hδ 2 p
        _ = delta n ^ 2 * delta n ^ p := by
          congr 1
          exact Real.rpow_natCast (delta n) 2
    apply (le_div_iff₀ (sq_pos_of_pos hδ)).2
    calc
      delta n ^ p * delta n ^ 2 = delta n ^ 2 * delta n ^ p := by ring
      _ = delta n ^ (2 + p) := hpowerEq.symm
      _ ≤ (horizon n : ℝ) := hpower n
  have hdeltaPowerTop : Tendsto (fun n : ℕ => delta n ^ p) atTop atTop :=
    (_root_.tendsto_rpow_atTop hp).comp hdeltaTop
  have hratioTop : Tendsto (fun n : ℕ => (horizon n : ℝ) / delta n ^ 2)
      atTop atTop :=
    tendsto_atTop_mono' atTop hratioLower hdeltaPowerTop
  have hsequence :=
    eventually_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_ah_exp
      ν hcentered hsecondMoment hB hcontinuous hmeasurable
      (horizon := horizon) (delta := delta)
      c target blockTarget hc htarget hblockTarget hblockTargetUpper
      hdeltaTop hratioTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsequence
  exact hbadBound N (hN N le_rfl)

end ProbabilityTheory.BranchingRandomWalk.Analytic

end
