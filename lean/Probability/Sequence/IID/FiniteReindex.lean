/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import MeasureTheory.Measure.FiniteCover

/-!
# Finite coordinate reindexing of an IID product law

The public definitions and theorems in this file are:

- `finiteCoordinateReindex`: the coordinate permutation of `Fin n`
  induced by any equivalence of that finite index type.
- `measure_pi_preimage_eq_of_reindex`: the product measure of identical
  probability laws is invariant under the permutation.
- `measure_pi_event_le_card_smul_of_reindexCover`: if $n$ reindexed
  copies of a measurable event cover another event, its measure is at most
  $n$ times the measure of the original event.

The last statement combines finite-product invariance with
`MeasureTheory.measure_le_card_smul_of_finite_cover_invariant`. Its use for
cyclically reindexed random-walk increments is in the entrance estimates.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Reindexing a finite vector by `e` as `x ↦ (x (e i))ᵢ`. -/
noncomputable def finiteCoordinateReindex
    {E : Type*} [MeasurableSpace E] {n : ℕ} (e : Fin n ≃ Fin n) :
    MeasurableEquiv (Fin n → E) (Fin n → E) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin n => E) e.symm

/-- Reindexing a finite product of copies of the same law preserves its
measure. This is the product-measure input to the cyclic entrance bound. -/
theorem measure_pi_preimage_eq_of_reindex
    {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) [IsProbabilityMeasure ν] {n : ℕ}
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

/-- A finite coordinate-reindexing cover gives the factor-`n` probability
bound for an IID product law. -/
theorem measure_pi_event_le_card_smul_of_reindexCover
    {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) [IsProbabilityMeasure ν] {n : ℕ}
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
