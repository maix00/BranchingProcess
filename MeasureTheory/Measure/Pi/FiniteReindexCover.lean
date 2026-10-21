/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import MeasureTheory.OuterMeasure.Finite.Cover

/-!
# Finite covers by reindexings of finite product measures

The public theorem in this file is:

- `MeasureTheory.measure_pi_event_le_card_smul_of_reindex_cover`: let
  `μ = Measure.pi ν` on `ι → E`, where each `ν i` is sigma-finite. If every
  coordinate equivalence in a finite family preserves the coordinate measures
  and the corresponding preimages of a measurable set `safe` cover `event`,
  then `μ(event) ≤ card(κ) · μ(safe)`.

The estimate combines Mathlib's finite-product reindexing theorem with
`measure_le_card_smul_of_finite_cover_invariant`. The iid case is used for
cyclically reindexed random-walk increments in the entrance estimates.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MeasureTheory

/-- A coordinate equivalence preserving a family of coordinate measures
preserves the measure of a measurable set under their finite product. -/
private theorem measure_pi_preimage_eq_of_reindex
    {E : Type*} [MeasurableSpace E]
    {ι : Type*} [Fintype ι] (ν : ι → Measure E)
    [∀ i, SigmaFinite (ν i)] (e : ι ≃ ι)
    (hν : ∀ i, ν (e i) = ν i) (A : Set (ι → E)) (hA : MeasurableSet A) :
    Measure.pi ν
        ((MeasurableEquiv.piCongrLeft (fun _ : ι => E) e) ⁻¹' A) =
      Measure.pi ν A := by
  have hmap :
      (Measure.pi ν).map
          (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e) =
        Measure.pi ν := by
    simpa only [show (fun i : ι => ν (e i)) = ν from funext hν] using
      Measure.pi_map_piCongrLeft e ν
  calc
    Measure.pi ν
        ((MeasurableEquiv.piCongrLeft (fun _ : ι => E) e) ⁻¹' A) =
      ((Measure.pi ν).map
        (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e)) A := by
          rw [Measure.map_apply (MeasurableEquiv.piCongrLeft _ e).measurable hA]
    _ = Measure.pi ν A := by rw [hmap]

/-- A finite family of coordinate reindexings gives a cardinality-loss measure
bound for a finite product whose coordinate measures are preserved by each
reindexing. -/
theorem measure_pi_event_le_card_smul_of_reindex_cover
    {E ι κ : Type*} [MeasurableSpace E] [Fintype ι] [Fintype κ]
    (ν : ι → Measure E) [∀ i, SigmaFinite (ν i)]
    (event safe : Set (ι → E)) (rotate : κ → ι ≃ ι)
    (hν : ∀ k i, ν (rotate k i) = ν i)
    (hcover : event ⊆ ⋃ k,
      (MeasurableEquiv.piCongrLeft (fun _ : ι => E) (rotate k).symm) ⁻¹' safe)
    (hsafe : MeasurableSet safe) :
    Measure.pi ν event ≤ Fintype.card κ • Measure.pi ν safe := by
  have hbound := measure_le_card_smul_of_finite_cover_invariant
    (μ := Measure.pi ν) (Finset.univ : Finset κ)
    event safe (fun k =>
      MeasurableEquiv.piCongrLeft (fun _ : ι => E) (rotate k).symm)
    (by simpa using hcover)
    (by
      intro k hk
      apply measure_pi_preimage_eq_of_reindex ν (rotate k).symm
      · intro i
        simpa using (hν k ((rotate k).symm i)).symm
      · exact hsafe)
  simpa using hbound

end MeasureTheory

end
