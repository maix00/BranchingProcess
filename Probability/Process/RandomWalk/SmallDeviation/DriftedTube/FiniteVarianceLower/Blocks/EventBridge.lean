/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Window.Endpoint
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.FiniteVarianceLower.Binning.Geometry
public import Probability.Sequence.IID.ConditionalBlocks

/-!
# Finite-block form of a horizontal tube with endpoint window

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.finiteInClosedIntervalEndsIn_blockCoordinates_iff_relativeHorizontalTubeEndpointWindowEvent`:
  for $y\in[l,l+D]$, a block started at $y$ staying in $[l,l+D]$
  and ending in $[l+v_1D,l+v_2D]$ is precisely the translated
  zero-start event with lower edge $l-y$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.measure_blockCoordinates_finiteTubeEndpoint_eq_relativeHorizontalTubeEndpointWindowEvent`:
  independent IID blocks have the same probability as this translated
  zero-start event.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.tubeBlockPairEvent`:
  the joint event for the preceding increments and one finite tube block.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.measurableSet_tubeBlockPairEvent`:
  this joint event is measurable.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.iidSequenceLaw_condExp_tubeBlockPairEvent_ge`:
  a uniform zero-start tube bound becomes the corresponding conditional
  block bound at every preceding position inside the tube.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.tubeBlockEvent`:
  the block event on the complete increment sequence.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.measurableSet_tubeBlockEvent`:
  it belongs to the natural domain filtration at the block end.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.tubeBlockEvent_end_mem`:
  a successful block places the walk in its specified terminal window.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.tubeBlockEvent_path_mem`:
  every time within a successful block lies in its horizontal tube.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.iidSequenceLaw_condExp_tubeBlockEvent_ge`:
  the preceding conditional bound expressed on the complete sequence.

This is the conditional-probability identification in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, proof of Lemma 3.5.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

/-- The next horizontal tube block, with its starting position determined
by the preceding increments of the random walk. -/
def tubeBlockPairEvent (lower width v₁ v₂ : ℝ) (start length : ℕ) :
    Set ((Fin start → ℝ) × (Fin length → ℝ)) :=
  {pair | RandomWalk.FiniteInClosedIntervalEndsIn
    lower (lower + width) (lower + v₁ * width)
      (lower + v₂ * width)
      (∑ j : Fin start, pair.1 j) pair.2}

/-- The past-dependent finite block event is measurable in the product
sigma algebra of the two coordinate blocks. -/
theorem measurableSet_tubeBlockPairEvent
    (lower width v₁ v₂ : ℝ) (start length : ℕ) :
    MeasurableSet (tubeBlockPairEvent lower width v₁ v₂ start length) := by
  exact RandomWalk.measurableSet_pairFiniteInClosedIntervalEndsIn
    lower (lower + width) (lower + v₁ * width) (lower + v₂ * width)
      (fun past : Fin start → ℝ => ∑ j : Fin start, past j)
      (Finset.measurable_sum Finset.univ fun j _ => measurable_pi_apply j)

/-- A finite coordinate block at a position already in the horizontal tube
is equivalent to the translated zero-start tube and endpoint event. -/
theorem finiteInClosedIntervalEndsIn_blockCoordinates_iff_relativeHorizontalTubeEndpointWindowEvent
    {lower width v₁ v₂ initial : ℝ}
    (hinitial : initial ∈ Set.Icc lower (lower + width))
    (start n : ℕ) (increment : ℕ → ℝ) :
    RandomWalk.FiniteInClosedIntervalEndsIn
      lower (lower + width) (lower + v₁ * width)
        (lower + v₂ * width) initial
      (Combinatorics.Sequence.blockCoordinates start n increment) ↔
    (fun k => increment (start + k)) ∈
      relativeHorizontalTubeEndpointWindowEvent
        (lower - initial) width n v₁ v₂ := by
  rw [RandomWalk.finiteInClosedIntervalEndsIn_blockCoordinates_iff]
  rw [← RandomWalk.staysIn_Icc_iff_inClosedInterval
    lower (lower + width) n initial hinitial]
  unfold RandomWalk.StaysIn relativeHorizontalTubeEndpointWindowEvent
  constructor
  · rintro ⟨hpath, hend⟩
    refine ⟨?_, ?_⟩
    · intro k
      have hk := hpath k
      exact ⟨by linarith [hk.1], by linarith [hk.2]⟩
    · exact ⟨by linarith [hend.1], by linarith [hend.2]⟩
  · rintro ⟨hpath, hend⟩
    refine ⟨?_, ?_⟩
    · intro k
      have hk := hpath k
      exact ⟨by linarith [hk.1], by linarith [hk.2]⟩
    · exact ⟨by linarith [hend.1], by linarith [hend.2]⟩

/-- The probability of a translated finite block event is the probability
of its zero-start horizontal tube and endpoint counterpart. -/
theorem measure_blockCoordinates_finiteTubeEndpoint_eq_relativeHorizontalTubeEndpointWindowEvent
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {lower width v₁ v₂ initial : ℝ}
    (hinitial : initial ∈ Set.Icc lower (lower + width))
    (start n : ℕ) :
    ((iidSequenceLaw ν).map
      (Combinatorics.Sequence.blockCoordinates start n))
        {block | RandomWalk.FiniteInClosedIntervalEndsIn
          lower (lower + width) (lower + v₁ * width)
            (lower + v₂ * width) initial block} =
      iidSequenceLaw ν
        (relativeHorizontalTubeEndpointWindowEvent
          (lower - initial) width n v₁ v₂) := by
  rw [iidSequenceLaw_map_blockCoordinates ν start n]
  rw [Measure.map_apply (measurable_blockCoordinates 0 n)
    (RandomWalk.measurableSet_finiteInClosedIntervalEndsIn
      lower (lower + width) (lower + v₁ * width)
        (lower + v₂ * width) initial n)]
  congr 1
  ext increment
  simpa only [Set.mem_preimage, Set.mem_ofPred_eq, Nat.zero_add] using
    (finiteInClosedIntervalEndsIn_blockCoordinates_iff_relativeHorizontalTubeEndpointWindowEvent
      hinitial 0 n increment)

/-- The Markov step in the horizontal-block argument: conditionally on the
preceding position lying inside the tube, the chance of the next finite
block is bounded by its translated zero-start probability. -/
theorem iidSequenceLaw_condExp_tubeBlockPairEvent_ge
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower width v₁ v₂ : ℝ) (start length : ℕ)
    (good : Set ℝ)
    (hgoodTube : good ⊆ Set.Icc lower (lower + width))
    {bound : ℝ}
    (hbound : ∀ initial ∈ good,
      bound ≤ (iidSequenceLaw ν).real
        (relativeHorizontalTubeEndpointWindowEvent
          (lower - initial) width length v₁ v₂)) :
    ∀ᵐ increment ∂iidSequenceLaw ν,
      (∑ j : Fin start,
          Combinatorics.Sequence.blockCoordinates 0 start increment j) ∈
        good →
      bound ≤ condExp
        (MeasurableSpace.comap
          (Combinatorics.Sequence.blockCoordinates 0 start) inferInstance)
        (iidSequenceLaw ν)
        (fun increment =>
          (tubeBlockPairEvent lower width v₁ v₂ start length).indicator
            (fun _ => (1 : ℝ))
            (Combinatorics.Sequence.blockCoordinates 0 start increment,
              Combinatorics.Sequence.blockCoordinates start length increment))
        increment := by
  let goodPast : Set (Fin start → ℝ) :=
    {past | (∑ j : Fin start, past j) ∈ good}
  have hsections : ∀ past : Fin start → ℝ, past ∈ goodPast →
      bound ≤ ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)).real
        {block | (past, block) ∈
          tubeBlockPairEvent lower width v₁ v₂ start length} := by
    intro past hpast
    have hpast' : (∑ j : Fin start, past j) ∈
        Set.Icc lower (lower + width) := hgoodTube hpast
    have hbridge :=
      measure_blockCoordinates_finiteTubeEndpoint_eq_relativeHorizontalTubeEndpointWindowEvent
        ν (lower := lower) (width := width) (v₁ := v₁) (v₂ := v₂)
          hpast' start length
    have hbound' := hbound (∑ j : Fin start, past j) hpast
    have hbridgeReal := congrArg ENNReal.toReal hbridge
    change bound ≤ ((iidSequenceLaw ν)
      (relativeHorizontalTubeEndpointWindowEvent
        (lower - ∑ j : Fin start, past j) width length v₁ v₂)).toReal at hbound'
    rw [← hbridgeReal] at hbound'
    change bound ≤ (((iidSequenceLaw ν).map
      (Combinatorics.Sequence.blockCoordinates start length))
        {block | (past, block) ∈
          tubeBlockPairEvent lower width v₁ v₂ start length}).toReal
    simpa only [tubeBlockPairEvent, Set.mem_ofPred_eq] using hbound'
  exact iidSequenceLaw_condExp_pairEvent_ge_of_sectionProbability
    ν start length
      (tubeBlockPairEvent lower width v₁ v₂ start length)
      (measurableSet_tubeBlockPairEvent lower width v₁ v₂ start length)
      goodPast hsections

/-- The finite horizontal tube block event on the complete increment path. -/
def tubeBlockEvent (start length : ℕ)
    (lower width v₁ v₂ : ℝ) : Set (ℕ → ℝ) :=
  {increment | (Combinatorics.Sequence.blockCoordinates 0 start increment,
      Combinatorics.Sequence.blockCoordinates start length increment) ∈
        tubeBlockPairEvent lower width v₁ v₂ start length}

private def tubePrefixBlockPair (start length : ℕ) :
    (Fin (start + length) → ℝ) →
      (Fin start → ℝ) × (Fin length → ℝ) :=
  fun whole =>
    (fun i : Fin start => whole ⟨(i : ℕ), by omega⟩,
      fun j : Fin length => whole ⟨start + (j : ℕ), by omega⟩)

private theorem measurable_tubePrefixBlockPair (start length : ℕ) :
    Measurable (tubePrefixBlockPair start length) := by
  apply Measurable.prodMk
  · rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply
      (⟨(i : ℕ), by omega⟩ : Fin (start + length))
  · rw [measurable_pi_iff]
    intro j
    exact measurable_pi_apply
      (⟨start + (j : ℕ), by omega⟩ : Fin (start + length))

private theorem tubePrefixBlockPair_blockCoordinates
    (start length : ℕ) (increment : ℕ → ℝ) :
    tubePrefixBlockPair start length
      (Combinatorics.Sequence.blockCoordinates 0 (start + length) increment) =
    (Combinatorics.Sequence.blockCoordinates 0 start increment,
      Combinatorics.Sequence.blockCoordinates start length increment) := by
  apply Prod.ext
  · funext i
    simp [tubePrefixBlockPair,
      Combinatorics.Sequence.blockCoordinates]
  · funext j
    simp [tubePrefixBlockPair,
      Combinatorics.Sequence.blockCoordinates]

/-- A horizontal tube block event is measurable at the end of that block
in the natural domain filtration of the increment sequence. -/
theorem measurableSet_tubeBlockEvent
    (start length : ℕ) (lower width v₁ v₂ : ℝ) :
    MeasurableSet[sequencePrefixFiltration (E := ℝ) (start + length)]
      (tubeBlockEvent start length lower width v₁ v₂) := by
  rw [sequencePrefixFiltration_eq_comap_blockCoordinates]
  apply (MeasurableSpace.measurableSet_comap).2
  refine ⟨_, (measurableSet_tubeBlockPairEvent
    lower width v₁ v₂ start length).preimage
      (measurable_tubePrefixBlockPair start length), ?_⟩
  ext increment
  simp only [Set.mem_preimage, tubeBlockEvent, Set.mem_ofPred_eq]
  rw [tubePrefixBlockPair_blockCoordinates]

/-- The terminal constraint carried by a successful horizontal tube block. -/
theorem tubeBlockEvent_end_mem
    {start length : ℕ} {lower width v₁ v₂ : ℝ}
    {increment : ℕ → ℝ}
    (hblock : increment ∈
      tubeBlockEvent start length lower width v₁ v₂) :
    AdditivePath.displacement (start + length) increment ∈
      Set.Icc (lower + v₁ * width) (lower + v₂ * width) := by
  have hend := hblock.2
  have hpast :
      (∑ j : Fin start,
        Combinatorics.Sequence.blockCoordinates 0 start increment j) =
      AdditivePath.displacement start increment := by
    simp [Combinatorics.Sequence.blockCoordinates,
      AdditivePath.displacement, Fin.sum_univ_eq_sum_range]
  have hnext :
      (∑ j : Fin length,
        Combinatorics.Sequence.blockCoordinates start length increment j) =
      AdditivePath.displacement length
        (fun k => increment (start + k)) := by
    rw [Finset.sum_fin_eq_sum_range]
    simp only [AdditivePath.displacement]
    apply Finset.sum_congr rfl
    intro k hk
    simp [Combinatorics.Sequence.blockCoordinates,
      Finset.mem_range.mp hk]
  simpa only [hpast, hnext, ← AdditivePath.displacement_add] using hend

/-- Every time in the block, including its starting time, lies inside the
specified horizontal tube. -/
theorem tubeBlockEvent_path_mem
    {start length : ℕ} {lower width v₁ v₂ : ℝ}
    {increment : ℕ → ℝ}
    (hblock : increment ∈
      tubeBlockEvent start length lower width v₁ v₂)
    {k : ℕ} (hk : k ≤ length) :
    AdditivePath.displacement (start + k) increment ∈
      Set.Icc lower (lower + width) := by
  have hpath :=
    (RandomWalk.finiteInClosedInterval_blockCoordinates_iff
      lower (lower + width)
      (∑ j : Fin start,
        Combinatorics.Sequence.blockCoordinates 0 start increment j)
      start length increment).mp hblock.1
  have hposition := hpath ⟨k, Nat.lt_succ_of_le hk⟩
  have hpast :
      (∑ j : Fin start,
        Combinatorics.Sequence.blockCoordinates 0 start increment j) =
      AdditivePath.displacement start increment := by
    simp [Combinatorics.Sequence.blockCoordinates,
      AdditivePath.displacement, Fin.sum_univ_eq_sum_range]
  simpa [RandomWalk.InClosedInterval, RandomWalk.InWindows,
    RandomWalk.history_eq_fromIncrements,
    AdditivePath.fromIncrements, hpast,
    AdditivePath.displacement_add] using hposition

/-- The block-start conditional probability bound in the natural domain
filtration, using the translated zero-start bound from the preceding theorem. -/
theorem iidSequenceLaw_condExp_tubeBlockEvent_ge
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (lower width v₁ v₂ : ℝ) (start length : ℕ)
    (good : Set ℝ)
    (hgoodTube : good ⊆ Set.Icc lower (lower + width))
    {bound : ℝ}
    (hbound : ∀ initial ∈ good,
      bound ≤ (iidSequenceLaw ν).real
        (relativeHorizontalTubeEndpointWindowEvent
          (lower - initial) width length v₁ v₂)) :
    ∀ᵐ increment ∂iidSequenceLaw ν,
      (∑ j : Fin start,
          Combinatorics.Sequence.blockCoordinates 0 start increment j) ∈
        good →
      bound ≤ condExp (sequencePrefixFiltration (E := ℝ) start)
        (iidSequenceLaw ν)
        ((tubeBlockEvent start length lower width v₁ v₂).indicator
          (fun _ => (1 : ℝ))) increment := by
  rw [sequencePrefixFiltration_eq_comap_blockCoordinates]
  have hconditional := iidSequenceLaw_condExp_tubeBlockPairEvent_ge
    ν lower width v₁ v₂ start length good hgoodTube hbound
  have hindicator :
      (tubeBlockEvent start length lower width v₁ v₂).indicator
          (fun _ => (1 : ℝ)) =
        fun increment =>
          (tubeBlockPairEvent lower width v₁ v₂ start length).indicator
            (fun _ => (1 : ℝ))
            (Combinatorics.Sequence.blockCoordinates 0 start increment,
              Combinatorics.Sequence.blockCoordinates start length increment) := by
    funext increment
    rfl
  rw [hindicator]
  exact hconditional

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
