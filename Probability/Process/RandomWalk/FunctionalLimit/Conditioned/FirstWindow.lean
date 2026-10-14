/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.DescendingLocalTime
public import Probability.Sequence.IID.StoppingTime

/-!
# Independent future blocks at candidate meander-window starts

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_candidate_inter_block_eq_mul`:
  for an IID increment law, a candidate first-window event determined by
  the first $m$ increments is independent of any measurable event of the
  following length-$n$ increment block.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_firstWindow_inter_block_eq_mul`:
  the joint mass of a first surviving window at $m$ and a finite block
  event equals the candidate mass times the probability of that block
  event intersected with finite survival.

This is the independent-block step behind the first-window proof of Erwin
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480–485,
DOI 10.1214/aop/1176996098, as described by Vladislav Vysotsky,
*Positivity of integrated random walks*, Ann. Inst. H. Poincaré Probab.
Stat. 50(1) (2014), Section 3.1, equation (17), DOI 10.1214/12-AIHP487.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- A candidate first-window start depends only on the past and therefore
factors from every event of the following IID increment block. -/
theorem measure_candidate_inter_block_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n start : ℕ) (event : Set (Fin n → ℝ))
    (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
      ({increment | IsCandidateWindowStart n start increment} ∩
        (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event) =
      (iidSequenceLaw ν)
        {increment | IsCandidateWindowStart n start increment} *
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹' event) := by
  let past := Combinatorics.Sequence.blockCoordinates (E := ℝ) 0 start
  let future := Combinatorics.Sequence.blockCoordinates (E := ℝ) start n
  have hpast : MeasurableSet[MeasurableSpace.comap past inferInstance]
      {increment : ℕ → ℝ | IsCandidateWindowStart n start increment} := by
    rw [show MeasurableSpace.comap past inferInstance =
      sequencePrefixFiltration (E := ℝ) start by
        exact (sequencePrefixFiltration_eq_comap_blockCoordinates start).symm]
    exact measurableSet_isCandidateWindowStart_prefix n start
  obtain ⟨pastEvent, hpastEvent, hpastPreimage⟩ :=
    (MeasurableSpace.measurableSet_comap).1 hpast
  have hindep := indepFun_blockCoordinates_blockCoordinates ν 0 start n
  have hfactor := hindep.measure_inter_preimage_eq_mul
    pastEvent event hpastEvent hevent
  have hfuture :
      (iidSequenceLaw ν) (future ⁻¹' event) =
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹' event) := by
    calc
      _ = ((iidSequenceLaw ν).map future) event :=
        (Measure.map_apply (μ := iidSequenceLaw ν)
          (measurable_blockCoordinates start n) hevent).symm
      _ = ((iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 n)) event := by
        rw [iidSequenceLaw_map_blockCoordinates]
      _ = _ := Measure.map_apply (μ := iidSequenceLaw ν)
        (measurable_blockCoordinates 0 n) hevent
  simpa only [past, future, Nat.zero_add, ← hpastPreimage, hfuture]
    using hfactor

/-- At a fixed starting time, the first surviving-window event factors
into its prefix candidate event and the finite surviving future block. -/
theorem measure_firstWindow_inter_block_eq_mul
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (n start : ℕ) (event : Set (Fin n → ℝ))
    (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
      ({increment | IsFirstSurvivingWindow n start increment} ∩
        (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event) =
      (iidSequenceLaw ν)
        {increment | IsCandidateWindowStart n start increment} *
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
            (event ∩ {block | FiniteSurvivesNonnegative block})) := by
  have hset :
      {increment : ℕ → ℝ |
        IsFirstSurvivingWindow n start increment} ∩
          (Combinatorics.Sequence.blockCoordinates start n) ⁻¹' event =
        {increment | IsCandidateWindowStart n start increment} ∩
          (Combinatorics.Sequence.blockCoordinates start n) ⁻¹'
            (event ∩ {block | FiniteSurvivesNonnegative block}) := by
    ext increment
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    rw [isFirstSurvivingWindow_iff_candidate_and_survives,
      ← finiteSurvivesNonnegative_blockCoordinates_iff]
    tauto
  rw [hset]
  exact measure_candidate_inter_block_eq_mul ν n start _
    (hevent.inter (measurableSet_finiteSurvivesNonnegative n))

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
