/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import MeasureTheory.OuterMeasure.Finite.Cover

/-!
# Finite covers by reindexings of identical product measures

The public theorem in this file is:

- `measure_pi_event_le_card_smul_of_reindex_cover`: if a finite family of
  coordinate-reindexed preimages of a measurable set `safe` covers `event`,
  then for the product measure `μ = Measure.pi (fun _ : ι => ν)`,
  `μ(event) ≤ card(κ) · μ(safe)`, where `κ` indexes the reindexings and `ν`
  is a probability measure.

The estimate combines Mathlib's finite-product reindexing theorem with
`MeasureTheory.measure_le_card_smul_of_finite_cover_invariant`. Its use for
cyclically reindexed random-walk increments is in the entrance estimates.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Reindexing a product of copies of one measure preserves the measure of a
measurable set. -/
private theorem measure_pi_preimage_eq_of_reindex
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] {ι : Type*} [Fintype ι]
    (e : ι ≃ ι) (A : Set (ι → E)) (hA : MeasurableSet A) :
    Measure.pi (fun _ : ι => ν)
        ((MeasurableEquiv.piCongrLeft (fun _ : ι => E) e) ⁻¹' A) =
      Measure.pi (fun _ : ι => ν) A := by
  have hmap :
      (Measure.pi (fun _ : ι => ν)).map
          (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e) =
        Measure.pi (fun _ : ι => ν) := by
    simpa using Measure.pi_map_piCongrLeft e (fun _ : ι => ν)
  calc
    Measure.pi (fun _ : ι => ν)
        ((MeasurableEquiv.piCongrLeft (fun _ : ι => E) e) ⁻¹' A) =
      ((Measure.pi (fun _ : ι => ν)).map
        (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e)) A := by
          rw [Measure.map_apply (MeasurableEquiv.piCongrLeft _ e).measurable hA]
    _ = Measure.pi (fun _ : ι => ν) A := by rw [hmap]

/-- A finite family of coordinate reindexings gives a cardinality-loss measure
bound for the product of copies of one probability measure. -/
theorem measure_pi_event_le_card_smul_of_reindex_cover
    {E ι κ : Type*} [MeasurableSpace E] [Fintype ι] [Fintype κ]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (event safe : Set (ι → E)) (rotate : κ → ι ≃ ι)
    (hcover : event ⊆ ⋃ k,
      (MeasurableEquiv.piCongrLeft (fun _ : ι => E) (rotate k).symm) ⁻¹' safe)
    (hsafe : MeasurableSet safe) :
    Measure.pi (fun _ : ι => ν) event ≤
      Fintype.card κ • Measure.pi (fun _ : ι => ν) safe := by
  have hbound := MeasureTheory.measure_le_card_smul_of_finite_cover_invariant
    (μ := Measure.pi (fun _ : ι => ν)) (Finset.univ : Finset κ)
    event safe (fun k =>
      MeasurableEquiv.piCongrLeft (fun _ : ι => E) (rotate k).symm)
    (by simpa using hcover)
    (by
      intro k hk
      exact measure_pi_preimage_eq_of_reindex ν (rotate k).symm safe hsafe)
  simpa using hbound

end ProbabilityTheory

end
