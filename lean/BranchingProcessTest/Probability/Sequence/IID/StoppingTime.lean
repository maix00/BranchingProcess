/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Sequence.IID.StoppingTime

open MeasureTheory ProbabilityTheory

example {E : Type*} [MeasurableSpace E] (ν : Measure E) [IsProbabilityMeasure ν]
    (τ : (ℕ → E) → WithTop ℕ)
    (hτ : IsStoppingTime (sequencePrefixFiltration (E := E)) τ)
    (timeBound length : ℕ) (event : Set (Fin length → E))
    (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
        ({sequence | τ sequence ≤ timeBound} ∩ iidBlockEventAfter τ event) =
      (iidSequenceLaw ν) {sequence | τ sequence ≤ timeBound} *
        (iidSequenceLaw ν)
          (Combinatorics.Sequence.blockCoordinates 0 length ⁻¹' event) :=
  iidSequenceLaw_measure_boundedStoppingTime_iidBlockEventAfter_eq_mul
    ν τ hτ timeBound length event hevent

#print axioms ProbabilityTheory.iidSequenceLaw_measure_stoppingTimeCell_inter_blockEvent_eq_mul
#print axioms ProbabilityTheory.iidSequenceLaw_measure_boundedStoppingTime_iidBlockEventAfter_eq_mul
#print axioms ProbabilityTheory.iidSequenceLaw_measure_iidBlockEventAfter_le
