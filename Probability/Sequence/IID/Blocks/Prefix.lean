/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.Block
public import Probability.Sequence.Filtration
public import Probability.Sequence.IID.Basic

import Probability.Sequence.IID.Blocks.StoppingTime

/-!
# Independent finite prefixes and following IID blocks

The public theorem in this file is:

- `ProbabilityTheory.iidSequenceLaw_measure_prefix_inter_block_eq_mul`:
  if $A$ is measurable from the first $m$ coordinates and $B$ is a
  measurable event of the next $r$ coordinates, then
  $\mathbb P(A\cap B)=\mathbb P(A)\mathbb P(B_0)$, where $B_0$
  is the same block event at the origin.

This is the deterministic-prefix specialization of independent IID
coordinate blocks. It is used when factoring the last-sign-change
events on page 484 of Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- An event determined by the first `start` IID coordinates factors
from an event of the next `length` coordinates. -/
theorem iidSequenceLaw_measure_prefix_inter_block_eq_mul
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (start length : ℕ) (pastSet : Set (ℕ → E))
    (hprefix : MeasurableSet[sequencePrefixFiltration (E := E) start] pastSet)
    (event : Set (Fin length → E)) (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
        (pastSet ∩
          (Combinatorics.Sequence.blockCoordinates start length) ⁻¹' event) =
      (iidSequenceLaw ν) pastSet *
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event) := by
  let past := Combinatorics.Sequence.blockCoordinates (E := E) 0 start
  let future := Combinatorics.Sequence.blockCoordinates (E := E) start length
  have hpast : MeasurableSet[MeasurableSpace.comap past inferInstance] pastSet := by
    rw [show MeasurableSpace.comap past inferInstance =
      sequencePrefixFiltration (E := E) start by
        exact (sequencePrefixFiltration_eq_comap_blockCoordinates start).symm]
    exact hprefix
  obtain ⟨pastEvent, hpastEvent, hpastPreimage⟩ :=
    (MeasurableSpace.measurableSet_comap).1 hpast
  have hindep := indepFun_blockCoordinates_blockCoordinates ν 0 start length
  have hfactor := hindep.measure_inter_preimage_eq_mul
    pastEvent event hpastEvent hevent
  have hfuture :
      (iidSequenceLaw ν) (future ⁻¹' event) =
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event) := by
    calc
      _ = ((iidSequenceLaw ν).map future) event :=
        (Measure.map_apply (μ := iidSequenceLaw ν)
          (measurable_blockCoordinates start length) hevent).symm
      _ = ((iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 length)) event := by
        rw [iidSequenceLaw_map_blockCoordinates]
      _ = _ := Measure.map_apply (μ := iidSequenceLaw ν)
        (measurable_blockCoordinates 0 length) hevent
  simpa only [past, future, Nat.zero_add, ← hpastPreimage, hfuture]
    using hfactor

end ProbabilityTheory

end
