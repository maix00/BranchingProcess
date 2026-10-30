/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.JumpPath.Entrance.Endpoint
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Increments of Poisson entrance paths

For supported sources with integrable marks, the difference between two path
values is the sum of the realized jump integrals over the intervening
half-open time window.

## Public declarations

- `ProbabilityTheory.poissonEntrancePath_eq_fullJumpPath` identifies a
  supported entrance path with the cumulative integrals of its two complete
  Poisson sources at every observation time.
- `ProbabilityTheory.poissonEntrancePath_sub_eq_timeWindow` identifies every
  increment of that path with the sum of the two time-window integrals.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

attribute [local instance] Classical.propDecidable

private theorem integral_jumpPath_sub_eq_timeWindow
    (m : Measure (unitInterval × ℝ))
    (hm : Integrable (fun z : unitInterval × ℝ => z.2) m)
    (s t : unitInterval) (hst : s ≤ t) :
    (∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ) ∂m) -
      (∫ z, (if z.1 ≤ s then z.2 else 0 : ℝ) ∂m) =
    ∫ z, (if s < z.1 ∧ z.1 ≤ t then z.2 else 0 : ℝ) ∂m := by
  have ht : Integrable (fun z : unitInterval × ℝ =>
      if z.1 ≤ t then z.2 else 0) m :=
    hm.indicator (measurableSet_le
      (by fun_prop : Measurable fun z : unitInterval × ℝ => (z.1 : ℝ)) measurable_const)
  have hs : Integrable (fun z : unitInterval × ℝ =>
      if z.1 ≤ s then z.2 else 0) m :=
    hm.indicator (measurableSet_le
      (by fun_prop : Measurable fun z : unitInterval × ℝ => (z.1 : ℝ)) measurable_const)
  rw [← integral_sub ht hs]
  congr 1
  funext z
  by_cases hzs : z.1 ≤ s
  · have hzt : z.1 ≤ t := hzs.trans hst
    simp [hzs, hzt, not_lt.mpr hzs]
  · by_cases hzt : z.1 ≤ t
    · simp [hzs, hzt, lt_of_not_ge hzs]
    · simp [hzs, hzt]

/-- On supported realizations, the selected path equals the cumulative
integral of all realized jumps at every observation time. -/
theorem poissonEntrancePath_eq_fullJumpPath
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    (Ks : ℕ → Ωs → ℕ) (Xs : ℕ → ℕ → Ωs → unitInterval × ℝ)
    (Kb : ℕ → Ωb → ℕ) (Xb : ℕ → ℕ → Ωb → unitInterval × ℝ)
    (A H : Set (unitInterval × ℝ)) (ω : Ωs × Ωb)
    (hs : (poissonRandomMeasure Ks Xs ω.1).restrict A =
      poissonRandomMeasure Ks Xs ω.1)
    (hb : (poissonRandomMeasure Kb Xb ω.2).restrict H =
      poissonRandomMeasure Kb Xb ω.2)
    (t : unitInterval) :
    poissonEntrancePath Ks Xs Kb Xb A H t ω =
      (∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Kb Xb ω.2)) := by
  let B : Set (unitInterval × ℝ) := {z | z.1 ≤ t}
  have hB : MeasurableSet B :=
    measurableSet_Iic.preimage
      (by fun_prop : Measurable fun z : unitInterval × ℝ => (z.1 : ℝ))
  have hsmall : (∫ z in {z | z ∈ A ∧ z.1 ≤ t}, z.2
      ∂(poissonRandomMeasure Ks Xs ω.1)) =
      ∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Ks Xs ω.1) := by
    change (∫ z, z.2 ∂((poissonRandomMeasure Ks Xs ω.1).restrict (A ∩ B))) = _
    rw [Set.inter_comm A B, ← Measure.restrict_restrict hB, hs]
    exact (integral_indicator hB).symm
  have hbig : poissonJumpPath Kb Xb H ω.2 t =
      ∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Kb Xb ω.2) := by
    unfold poissonJumpPath
    rw [hb]
  exact congrArg₂ (· + ·) hsmall hbig

/-- Each increment of a supported jump-sum path is exactly the sum of
Poisson integrals over the corresponding half-open time window. -/
theorem poissonEntrancePath_sub_eq_timeWindow
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    (Ks : ℕ → Ωs → ℕ) (Xs : ℕ → ℕ → Ωs → unitInterval × ℝ)
    (Kb : ℕ → Ωb → ℕ) (Xb : ℕ → ℕ → Ωb → unitInterval × ℝ)
    (A H : Set (unitInterval × ℝ)) (ω : Ωs × Ωb)
    (hs : (poissonRandomMeasure Ks Xs ω.1).restrict A =
      poissonRandomMeasure Ks Xs ω.1)
    (hb : (poissonRandomMeasure Kb Xb ω.2).restrict H =
      poissonRandomMeasure Kb Xb ω.2)
    (hsi : Integrable (fun z : unitInterval × ℝ => z.2)
      (poissonRandomMeasure Ks Xs ω.1))
    (hbi : Integrable (fun z : unitInterval × ℝ => z.2)
      (poissonRandomMeasure Kb Xb ω.2))
    (s t : unitInterval) (hst : s ≤ t) :
    poissonEntrancePath Ks Xs Kb Xb A H t ω -
      poissonEntrancePath Ks Xs Kb Xb A H s ω =
    (∫ z, (if s < z.1 ∧ z.1 ≤ t then z.2 else 0 : ℝ)
      ∂(poissonRandomMeasure Ks Xs ω.1)) +
    (∫ z, (if s < z.1 ∧ z.1 ≤ t then z.2 else 0 : ℝ)
      ∂(poissonRandomMeasure Kb Xb ω.2)) := by
  rw [poissonEntrancePath_eq_fullJumpPath Ks Xs Kb Xb A H ω hs hb t,
    poissonEntrancePath_eq_fullJumpPath Ks Xs Kb Xb A H ω hs hb s]
  calc
    (∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Kb Xb ω.2)) -
      ((∫ z, (if z.1 ≤ s then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Ks Xs ω.1)) +
       (∫ z, (if z.1 ≤ s then z.2 else 0 : ℝ)
        ∂(poissonRandomMeasure Kb Xb ω.2))) =
        ((∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Ks Xs ω.1)) -
         (∫ z, (if z.1 ≤ s then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Ks Xs ω.1))) +
        ((∫ z, (if z.1 ≤ t then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Kb Xb ω.2)) -
         (∫ z, (if z.1 ≤ s then z.2 else 0 : ℝ)
          ∂(poissonRandomMeasure Kb Xb ω.2))) := by ring
    _ = _ := by
      rw [integral_jumpPath_sub_eq_timeWindow _ hsi s t hst,
        integral_jumpPath_sub_eq_timeWindow _ hbi s t hst]

end ProbabilityTheory

end
