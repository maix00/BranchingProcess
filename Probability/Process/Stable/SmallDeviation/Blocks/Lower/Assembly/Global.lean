/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Order.Interval.RationalCoordinate.UnitInterval
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Return.Basic
public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Cover
public import Probability.Process.Path.Skorokhod.Corridor.RationalCoordinate
import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Probability.Stationarity

/-!
# From returning blocks to a whole-path range tube

Write \(T_X(w)=\mathbb P(\operatorname{rationalHorizonTubeEvent}(X,1,w))\);
membership in this event means that some positive rational margin \(r\)
satisfies \(|X_s-X_t|\le w-r\) for every rational \(s,t\in[0,1]\).

## Public declarations

- rationalUniformPrefixCorridorReturnEvent_subset_rationalHorizonTubeEvent:
  a finite-block return event with corridor bounds \(a<b\) lies in the
  whole-horizon range tube of width \(b-a+\varepsilon\), for every
  \(\varepsilon>0\).
- IsStableLevyProcess.pow_le_measure_rationalHorizonTube_of_return_bins:
  if each translated return block has probability at least \(c\) under a
  finite endpoint-bin partition, then
  \[
    c^{N}\le T_X(b-a+\varepsilon).
  \]
- IsStableLevyProcess.iInf_blockProbability_pow_le_rationalHorizonTube:
  the same bound holds with \(c=\inf_i p_i\), where \(p_i\) are the finitely
  many first-block return probabilities.
- IsStableLevyProcess.iInf_blockProbability_pow_le_rationalHorizonTube_of_coreCover:
  a cover of the return core interval by the endpoint bins supplies the
  endpoint-coverage hypothesis for the preceding bound.

Uniform rational blocks cover the complete rational unit interval. A
blockwise spatial corridor therefore gives a whole-path range tube after
adding a positive width margin.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem rationalUniformPrefixCorridorReturnEvent_subset_rationalHorizonTubeEvent
    {Ω : Type*} (X : ℝ≥0 → Ω → ℝ)
    {blocks : ℕ} (hblocks : 0 < blocks)
    (lower upper extra : ℝ) (hextra : 0 < extra)
    (coreLower coreUpper : ℝ) :
    rationalUniformPrefixCorridorReturnEvent X
        lower upper coreLower coreUpper hblocks blocks ⊆
      rationalHorizonTubeEvent X 1 (upper - lower + extra) := by
  intro ω hω
  have hcoord := rationalUniformPrefixCorridorEvent_full_positions X hblocks
    lower upper ω hω.1
  have htube := rationalCoordinateCorridor_subset_oscillationTube
    lower upper extra hextra hcoord
  have hraw := (Skorokhod.mem_rationalCoordinateOscillationTube_sub_const_iff
    (upper - lower + extra) (X 0 ω)
    (fun q => X (RationalCoordinate.toNNReal q) ω)).mp htube
  change rationalHorizonProcess X 1 ω ∈
    Skorokhod.rationalCoordinateOscillationTube (upper - lower + extra)
  change (fun q => X (1 * RationalCoordinate.toNNReal q) ω) ∈
    Skorokhod.rationalCoordinateOscillationTube (upper - lower + extra)
  simpa using hraw

/-- The completed finite-block lower chain, conditional on the concrete
per-bin short-block probabilities. The remaining input is a uniform lower
bound for those probabilities at the stable scale. -/
theorem IsStableLevyProcess.pow_le_measure_rationalHorizonTube_of_return_bins
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper extra : ℝ) (hextra : 0 < extra)
    (coreLower coreUpper : ℝ) (hcore : coreLower < 0 ∧ 0 < coreUpper)
    (I : Fin blocks → ι → Set ℝ)
    (binLower binUpper : Fin blocks → ι → ℝ) (c : ENNReal)
    (hI : ∀ j i, MeasurableSet (I j i))
    (hdisj : ∀ j, Pairwise (fun i k => Disjoint (I j i) (I j k)))
    (hbin : ∀ j i b, b ∈ I j i → binLower j i ≤ b ∧ b ≤ binUpper j i)
    (hcover : ∀ j ω,
      ω ∈ rationalUniformPrefixCorridorReturnEvent X
        lower upper coreLower coreUpper hblocks j.val →
      ∃ i, rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ ∈ I j i)
    (hc : ∀ j i, c ≤ P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
        rationalCoordinateCorridorReturn
          (lower - binLower j i) (upper - binUpper j i)
          (coreLower - binLower j i) (coreUpper - binUpper j i))) :
    c ^ blocks ≤ P (rationalHorizonTubeEvent X 1
      (upper - lower + extra)) := by
  calc
    c ^ blocks ≤ P (rationalUniformPrefixCorridorReturnEvent X
        lower upper coreLower coreUpper hblocks blocks) :=
      h.pow_le_measure_prefixCorridorReturn_of_bins blocks hblocks
        lower upper coreLower coreUpper hcore I binLower binUpper c
        hI hdisj hbin hcover hc
    _ ≤ P (rationalHorizonTubeEvent X 1 (upper - lower + extra)) :=
      measure_mono
        (rationalUniformPrefixCorridorReturnEvent_subset_rationalHorizonTubeEvent
          X hblocks lower upper extra hextra coreLower coreUpper)

/-- Stationarity of the stable translated block laws replaces the uniform
one-block lower-bound hypothesis by the infimum of finitely many bin-specific
probabilities on the first block. -/
theorem IsStableLevyProcess.iInf_blockProbability_pow_le_rationalHorizonTube
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper extra : ℝ) (hextra : 0 < extra)
    (coreLower coreUpper : ℝ) (hcore : coreLower < 0 ∧ 0 < coreUpper)
    (I : ι → Set ℝ) (binLower binUpper : ι → ℝ)
    (hI : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise (fun i k => Disjoint (I i) (I k)))
    (hbin : ∀ i b, b ∈ I i → binLower i ≤ b ∧ b ≤ binUpper i)
    (hcover : ∀ j : Fin blocks, ∀ ω,
      ω ∈ rationalUniformPrefixCorridorReturnEvent X
        lower upper coreLower coreUpper hblocks j.val →
      ∃ i, rationalUniformPrefixPath X blocks j.val hblocks ω ⊤ ∈ I i) :
    (⨅ i : ι, P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks ⟨0, hblocks⟩ q ω) ⁻¹'
        rationalCoordinateCorridorReturn
          (lower - binLower i) (upper - binUpper i)
          (coreLower - binLower i) (coreUpper - binUpper i))) ^ blocks ≤
      P (rationalHorizonTubeEvent X 1 (upper - lower + extra)) := by
  let V : ι → Set (↑RationalCoordinate.UnitInterval → ℝ) :=
    fun i => rationalCoordinateCorridorReturn
      (lower - binLower i) (upper - binUpper i)
      (coreLower - binLower i) (coreUpper - binUpper i)
  let c : ENNReal := ⨅ i : ι,
    P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks ⟨0, hblocks⟩ q ω) ⁻¹'
      V i)
  change c ^ blocks ≤ _
  apply h.pow_le_measure_rationalHorizonTube_of_return_bins blocks hblocks
    lower upper extra hextra coreLower coreUpper hcore
    (fun _ => I) (fun _ => binLower) (fun _ => binUpper) c
  · exact fun _ => hI
  · exact fun _ => hdisj
  · exact fun _ => hbin
  · exact hcover
  · intro j i
    have hlaw := h.increments.indepIncrements.rationalUniformBlockProcess_identDistrib
      h.toIsLevyProcess.stationaryIncrements blocks hblocks j ⟨0, hblocks⟩
    have hprob := hlaw.measure_mem_eq
      (measurableSet_rationalCoordinateCorridorReturn _ _ _ _ : MeasurableSet (V i))
    change P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω) ⁻¹'
      V i) = P ((fun ω q =>
        rationalUniformBlockProcessFromTime X hblocks ⟨0, hblocks⟩ q ω) ⁻¹' V i)
      at hprob
    rw [hprob]
    exact iInf_le _ i

/-- A finite cover of the interior return interval supplies the endpoint-bin
coverage hypothesis in the preceding block lower bound. -/
theorem IsStableLevyProcess.iInf_blockProbability_pow_le_rationalHorizonTube_of_coreCover
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper extra : ℝ) (hextra : 0 < extra)
    (coreLower coreUpper : ℝ) (hcore : coreLower < 0 ∧ 0 < coreUpper)
    (I : ι → Set ℝ) (binLower binUpper : ι → ℝ)
    (hI : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise (fun i k => Disjoint (I i) (I k)))
    (hbin : ∀ i b, b ∈ I i → binLower i ≤ b ∧ b ≤ binUpper i)
    (hcover : Set.Ioo coreLower coreUpper ⊆ ⋃ i, I i) :
    (⨅ i : ι, P ((fun ω q =>
      rationalUniformBlockProcessFromTime X hblocks ⟨0, hblocks⟩ q ω) ⁻¹'
        rationalCoordinateCorridorReturn
          (lower - binLower i) (upper - binUpper i)
          (coreLower - binLower i) (coreUpper - binUpper i))) ^ blocks ≤
      P (rationalHorizonTubeEvent X 1 (upper - lower + extra)) := by
  apply h.iInf_blockProbability_pow_le_rationalHorizonTube blocks hblocks
    lower upper extra hextra coreLower coreUpper hcore I binLower binUpper
    hI hdisj hbin
  intro j ω hω
  exact Set.mem_iUnion.mp (hcover hω.2)

end ProbabilityTheory
