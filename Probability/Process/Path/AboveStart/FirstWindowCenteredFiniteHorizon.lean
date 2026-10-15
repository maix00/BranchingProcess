/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.AboveStart.FirstWindowCentered
public import Probability.Process.Path.AboveStart.FirstWindowFiniteHorizon

/-!
# Centered first-window shift on a finite path space

The public definitions and theorems in this file are:

- `ProbabilityTheory.centeredFirstWindowShiftFiniteHorizon`:
  the map $C([0,s],\mathbb R)\to C([0,1],\mathbb R)$ taking a finite
  path to $t\mapsto f(T^s(f)+t)-f(T^s(f))$ at finite $T^s(f)$ and to
  the constant path $-1$ otherwise.
- `ProbabilityTheory.measurable_centeredFirstWindowShiftFiniteHorizon`:
  this finite-path map is Borel measurable.
- `ProbabilityTheory.centeredFirstWindowShiftFiniteHorizon_restrictPathTo`:
  finite-path and whole-path constructions agree after restriction.
- `ProbabilityTheory.continuousAt_centeredFirstWindowShiftFiniteHorizon_of_full`:
  continuity of the whole-path map at $f$ implies continuity of the
  finite-path map at $f|_{[0,s]}$.

The map gives the centered block in Lemma 3.1 and equation (3.2) of
Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The centered first-window map with the actual finite path domain. -/
noncomputable def centeredFirstWindowShiftFiniteHorizon (s : ℝ≥0)
    (f : C(Set.Icc (0 : ℝ≥0) s, ℝ)) :
    C(Set.Icc (0 : ℝ≥0) 1, ℝ) :=
  restrictPathTo 1
    (centeredFirstWindowShiftUpTo
      (extendPathConstantAfter s f) s)

/-- The centered finite-path first-window map is measurable. -/
theorem measurable_centeredFirstWindowShiftFiniteHorizon (s : ℝ≥0) :
    Measurable (centeredFirstWindowShiftFiniteHorizon s) := by
  exact (continuous_restrictPathTo 1).measurable.comp
    ((measurable_centeredFirstWindowShiftUpTo s).comp
      (continuous_extendPathConstantAfter s).measurable)

/-- Restricting a whole path before or after applying the centered
finite-window shift gives the same unit-time path. -/
theorem centeredFirstWindowShiftFiniteHorizon_restrictPathTo
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    centeredFirstWindowShiftFiniteHorizon s (restrictPathTo s f) =
      restrictPathTo 1 (centeredFirstWindowShiftUpTo f s) := by
  rw [centeredFirstWindowShiftFiniteHorizon,
    extendPathConstantAfter_restrictPathTo]
  ext u
  unfold centeredFirstWindowShiftUpTo
  rw [firstNonnegativeWindowStartUpTo_freezeAfter]
  split_ifs with h
  · rfl
  · have hcoe :
        ((firstNonnegativeWindowStartUpTo f s).untopA : WithTop ℝ≥0) =
          firstNonnegativeWindowStartUpTo f s := by
      cases hval : firstNonnegativeWindowStartUpTo f s with
      | top => exact False.elim (h hval)
      | coe a => rfl
    have htime := (firstNonnegativeWindowStartUpTo_eq_coe_iff f s
      (firstNonnegativeWindowStartUpTo f s).untopA).mp hcoe.symm
    have ht := htime.1
    have hstart : (firstNonnegativeWindowStartUpTo f s).untopA ≤ s :=
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ≥0) ≤ 1)).trans ht
    have hu : (firstNonnegativeWindowStartUpTo f s).untopA + u.1 ≤ s :=
      (add_le_add_right u.property.2 _).trans ht
    change f (min ((firstNonnegativeWindowStartUpTo f s).untopA + u.1) s) -
        f (min (firstNonnegativeWindowStartUpTo f s).untopA s) =
      f ((firstNonnegativeWindowStartUpTo f s).untopA + u.1) -
        f (firstNonnegativeWindowStartUpTo f s).untopA
    rw [min_eq_left hu, min_eq_left hstart]

/-- Whole-path continuity transfers to the finite path space by
extending nearby finite paths with the reference path's increments. -/
theorem continuousAt_centeredFirstWindowShiftFiniteHorizon_of_full
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0)
    (hcont : ContinuousAt
      (fun g => centeredFirstWindowShiftUpTo g s) f) :
    ContinuousAt (centeredFirstWindowShiftFiniteHorizon s)
      (restrictPathTo s f) := by
  have hrepresentation (g : C(Set.Icc (0 : ℝ≥0) s, ℝ)) :
      centeredFirstWindowShiftFiniteHorizon s g =
        restrictPathTo 1
          (centeredFirstWindowShiftUpTo
            (extendPathAlong f s g) s) := by
    conv_lhs => rw [← restrictPathTo_extendPathAlong f s g]
    exact centeredFirstWindowShiftFiniteHorizon_restrictPathTo
      (extendPathAlong f s g) s
  have hinner : ContinuousAt
      (fun g : C(Set.Icc (0 : ℝ≥0) s, ℝ) =>
        centeredFirstWindowShiftUpTo
          (extendPathAlong f s g) s)
      (restrictPathTo s f) := by
    have hcont' : ContinuousAt
        (fun g => centeredFirstWindowShiftUpTo g s)
        (extendPathAlong f s (restrictPathTo s f)) := by
      simpa only [extendPathAlong_restrictPathTo] using hcont
    exact hcont'.comp (continuous_extendPathAlong f s).continuousAt
  have houter := (continuous_restrictPathTo 1).continuousAt.comp hinner
  convert houter using 1
  funext g
  exact hrepresentation g

end ProbabilityTheory

end
