/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import MeasureTheory.Measure.Finite.Cover

/-!
# Finite coordinate reindexing of identical product measures

The public definitions and theorems in this file are:

- `finiteCoordinateReindex`: the coordinate permutation of `Fin n`
  induced by any equivalence of that finite index type.
- `measure_pi_event_le_card_smul_of_reindexCover`: if $n$ reindexed
  copies of a measurable set `safe` cover `event`, then for the product
  measure `μₙ = Measure.pi (fun _ : Fin n => ν)`,
  `μₙ(event) ≤ n · μₙ(safe)`, for a σ-finite measure `ν` repeated across the
  coordinates.

The estimate combines Mathlib's finite-product reindexing theorem with
`MeasureTheory.measure_le_card_smul_of_finite_cover_invariant`. Its use for
cyclically reindexed random-walk increments is in the entrance estimates.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Reindexing a finite vector by `e` as `x ↦ (x (e i))ᵢ`. This is the
homogeneous `Fin n` specialization of
`MeasurableEquiv.piCongrLeft (fun _ => E) e.symm`. -/
noncomputable def finiteCoordinateReindex
    {E : Type*} [MeasurableSpace E] {n : ℕ} (e : Fin n ≃ Fin n) :
    MeasurableEquiv (Fin n → E) (Fin n → E) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => E) e.symm

/-- Reindexing a finite product of copies of the same measure preserves its
measure. This is the product-measure input to the cyclic entrance bound. -/
private theorem measure_pi_preimage_eq_of_reindex
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] {n : ℕ}
    (e : Fin n ≃ Fin n) (A : Set (Fin n → E)) (hA : MeasurableSet A) :
    Measure.pi (fun _ : Fin n => ν)
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => E) e) ⁻¹' A) =
      Measure.pi (fun _ : Fin n => ν) A := by
  have hmap :
      (Measure.pi (fun _ : Fin n => ν)).map
          (MeasurableEquiv.piCongrLeft (fun _ : Fin n => E) e) =
        Measure.pi (fun _ : Fin n => ν) := by
    simpa using Measure.pi_map_piCongrLeft e (fun _ : Fin n => ν)
  calc
    Measure.pi (fun _ : Fin n => ν)
        ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => E) e) ⁻¹' A) =
      ((Measure.pi (fun _ : Fin n => ν)).map
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n => E) e)) A := by
          rw [Measure.map_apply (MeasurableEquiv.piCongrLeft _ e).measurable hA]
    _ = Measure.pi (fun _ : Fin n => ν) A := by rw [hmap]

/-- A finite coordinate-reindexing cover gives a factor-`n` measure bound for
a product of `n` copies of a σ-finite measure. -/
theorem measure_pi_event_le_card_smul_of_reindexCover
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] {n : ℕ}
    (event safe : Set (Fin n → E)) (rotate : Fin n → Fin n ≃ Fin n)
    (hcover : event ⊆ ⋃ k, (finiteCoordinateReindex (rotate k)) ⁻¹' safe)
    (hsafe : MeasurableSet safe) :
    Measure.pi (fun _ : Fin n => ν) event ≤
      n • Measure.pi (fun _ : Fin n => ν) safe := by
  apply MeasureTheory.measure_le_card_smul_of_finite_cover_invariant
    (μ := Measure.pi (fun _ : Fin n => ν)) event safe
    (fun k => finiteCoordinateReindex (rotate k)) hcover
  intro k
  exact measure_pi_preimage_eq_of_reindex ν (rotate k).symm safe hsafe

end ProbabilityTheory

end
