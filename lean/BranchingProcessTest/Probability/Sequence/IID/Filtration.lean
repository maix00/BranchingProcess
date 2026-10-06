/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Sequence.IID
import Probability.Sequence.IID.Filtration

open MeasureTheory ProbabilityTheory

example {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (n k : ℕ) (hnk : n ≤ k) :
    Indep (MeasurableSpace.comap
        (fun sequence : ℕ → E => sequence k) inferInstance)
      (sequencePrefixFiltration (E := E) n) (iidSequenceLaw ν) := by
  change Indep (MeasurableSpace.comap
      (fun sequence : ℕ → E => sequence k) inferInstance)
    (⨆ j : Fin n,
      MeasurableSpace.comap (fun sequence : ℕ → E => sequence j) inferInstance)
    (iidSequenceLaw ν)
  exact (iidSequenceLaw_independent ν).indep_coordinatePrefixFiltration_of_le
    (fun j => measurable_pi_apply j) hnk

example {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {μ : Measure Ω} {coordinate : ℕ → Ω → E}
    (hindep : iIndepFun coordinate μ)
    (hmeasurable : ∀ k, Measurable (coordinate k))
    {n k : ℕ} (hnk : n ≤ k) :
    Indep (MeasurableSpace.comap (coordinate k) inferInstance)
      (⨆ j : Fin n, MeasurableSpace.comap (coordinate j) inferInstance) μ :=
  hindep.indep_coordinatePrefixFiltration_of_le hmeasurable hnk

#print axioms ProbabilityTheory.iIndepFun.indep_coordinatePrefixFiltration_of_le
