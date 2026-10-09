/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Probability.Process.RandomWalk.SmallDeviation.Entrance.LinearTubeRotation
public import Probability.Sequence.IID

/-!
# Finite exchangeability of an IID prefix

The first `n` coordinates of the canonical IID sequence law have the finite
product law. Coordinate reindexing by any equivalence of `Fin n` preserves
that law. These are the measure-theoretic ingredients for the cyclic-shift
factor in the entrance estimate.
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

/-- The first `n` coordinates of the canonical IID sequence have the finite
product law. -/
theorem iidSequenceLaw_map_finPrefix
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (iidSequenceLaw ν).map (fun x : ℕ → E => fun i : Fin n => x i.val) =
      Measure.pi (fun _ : Fin n => ν) := by
  unfold iidSequenceLaw
  rw [Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => ν) (f := fun i : Fin n => i.val)
    (fun _ _ h => Fin.val_injective h)]
  rw [Measure.infinitePi_eq_pi]

/-- Reindexing a finite product of copies of the same law preserves its
measure. This is the Mathlib product-measure route to the cyclic-rotation
invariance used in the entrance estimate. -/
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

/-- The cyclic-rotation union bound for a finite IID increment vector. The
factor `n` comes from the finite union; invariance under each coordinate
reindexing is discharged by the product-measure theorem above. -/
theorem measure_pi_event_le_card_smul_of_reindexCover
    {E : Type*} [MeasurableSpace E] [Nonempty E]
    (ν : Measure E) [IsProbabilityMeasure ν] {n : ℕ}
    (event safe : Set (Fin n → E)) (rotate : Fin n → Fin n ≃ Fin n)
    (hcover : event ⊆ ⋃ k, (finiteCoordinateReindex (rotate k)) ⁻¹' safe)
    (hsafe : MeasurableSet safe) :
    Measure.pi (fun _ : Fin n => ν) event ≤
      n • Measure.pi (fun _ : Fin n => ν) safe := by
  apply RandomWalk.SmallDeviation.Entrance.measure_le_card_smul_of_finiteRotationCover
    (μ := Measure.pi (fun _ : Fin n => ν)) event safe
    (fun k => finiteCoordinateReindex (rotate k)) hcover
  intro k
  exact measure_pi_preimage_eq_of_reindex ν (rotate k).symm safe hsafe

end ProbabilityTheory

end
