/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.FiniteHorizon
public import Probability.Process.Path.AboveStart.FirstWindow.Shift

/-!
# First-window shift on a finite path space

The public definitions and theorems in this file are:

- `ProbabilityTheory.firstWindowShiftFiniteHorizon`:
  $\Phi_s:C([0,s],\mathbb R)\to C([0,1],\mathbb R)$,
  sending $g$ to $u\mapsto g(T^s(g)+u)$ when $T^s(g)<\infty$ and
  to the constant path $-1$ otherwise.
- `ProbabilityTheory.measurable_firstWindowShiftFiniteHorizon`:
  $\Phi_s$ is Borel measurable.
- `ProbabilityTheory.firstNonnegativeWindowStartUpTo_freezeAfter`:
  $T^s(f|_{[0,s]})=T^s(f)$ for a whole-time path $f$.
- `ProbabilityTheory.firstWindowShiftFiniteHorizon_restrictPathTo`:
  $\Phi_s(f|_{[0,s]})$ is the restriction of the whole-time
  finite-window shift to $[0,1]$.
- `ProbabilityTheory.finiteHorizonPathLaw_map_firstWindowShift`:
  $(P^s)\circ\Phi_s^{-1}$ is the law of the restricted finite-window
  shift under the whole-time path law $P$.
- `ProbabilityTheory.continuousAt_firstWindowShiftFiniteHorizon_of_full`:
  continuity of the whole-time finite-window shift at $f$ implies
  continuity of $\Phi_s$ at $f|_{[0,s]}$.

This realizes the domain and codomain of $\Phi_s$ in Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned to
stay positive*, Lemma 2.5 and Section 3, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The displayed finite-horizon first-window shift of Bolthausen,
with domain $C^s$ and codomain $C^1$. -/
noncomputable def firstWindowShiftFiniteHorizon (s : ℝ≥0)
    (f : C(Set.Icc (0 : ℝ≥0) s, ℝ)) :
    C(Set.Icc (0 : ℝ≥0) 1, ℝ) :=
  restrictPathTo 1
    (shiftAtFirstNonnegativeWindowStartUpTo
      (extendPathConstantAfter s f) s)

/-- The finite-horizon shift is measurable on its actual finite path
space. -/
theorem measurable_firstWindowShiftFiniteHorizon (s : ℝ≥0) :
    Measurable (firstWindowShiftFiniteHorizon s) := by
  exact (continuous_restrictPathTo 1).measurable.comp
    ((measurable_shiftAtFirstNonnegativeWindowStartUpTo s).comp
      (continuous_extendPathConstantAfter s).measurable)

/-- A unit window contained in $[0,s]$ has the same eligibility after
freezing the path at time $s$. -/
theorem isNonnegativeWindowStart_freezeAfter_iff
    (f : C(ℝ≥0, ℝ)) (s t : ℝ≥0) (ht : t + 1 ≤ s) :
    IsNonnegativeWindowStart (freezeAfter f s) t ↔
      IsNonnegativeWindowStart f t := by
  have hts : t ≤ s := (le_add_of_nonneg_right (by norm_num : (0 : ℝ≥0) ≤ 1)).trans ht
  constructor <;> intro h u
  · have htu : t + u.1 ≤ s :=
      (add_le_add_right u.property.2 t).trans ht
    simpa [IsNonnegativeWindowStart, freezeAfter,
      min_eq_left hts, min_eq_left htu] using h u
  · have htu : t + u.1 ≤ s :=
      (add_le_add_right u.property.2 t).trans ht
    simpa [IsNonnegativeWindowStart, freezeAfter,
      min_eq_left hts, min_eq_left htu] using h u

/-- The first eligible finite-horizon window depends only on the
restriction to that horizon. -/
theorem firstNonnegativeWindowStartUpTo_freezeAfter
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    firstNonnegativeWindowStartUpTo (freezeAfter f s) s =
      firstNonnegativeWindowStartUpTo f s := by
  classical
  have hpred (t : ℝ≥0) :
      (t + 1 ≤ s ∧ IsNonnegativeWindowStart (freezeAfter f s) t) ↔
        (t + 1 ≤ s ∧ IsNonnegativeWindowStart f t) := by
    exact and_congr_right fun ht =>
      isNonnegativeWindowStart_freezeAfter_iff f s t ht
  have hex : (∃ t : ℝ≥0, t + 1 ≤ s ∧
      IsNonnegativeWindowStart (freezeAfter f s) t) ↔
      (∃ t : ℝ≥0, t + 1 ≤ s ∧ IsNonnegativeWindowStart f t) :=
    exists_congr hpred
  by_cases h : ∃ t : ℝ≥0, t + 1 ≤ s ∧ IsNonnegativeWindowStart f t
  · have hf := hex.mpr h
    simp only [firstNonnegativeWindowStartUpTo, dite_eq_left hf, dite_eq_left h]
    have hset : {t : ℝ≥0 | t + 1 ≤ s ∧
        IsNonnegativeWindowStart (freezeAfter f s) t} =
        {t : ℝ≥0 | t + 1 ≤ s ∧ IsNonnegativeWindowStart f t} := by
      ext t
      exact hpred t
    rw [hset]
  · have hf := mt hex.mp h
    simp [firstNonnegativeWindowStartUpTo, h, hf]

/-- On a whole-time path, applying the finite-space map after
restriction agrees with applying the whole-time finite-window shift
and then restricting the output. -/
theorem firstWindowShiftFiniteHorizon_restrictPathTo
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    firstWindowShiftFiniteHorizon s (restrictPathTo s f) =
      restrictPathTo 1 (shiftAtFirstNonnegativeWindowStartUpTo f s) := by
  rw [firstWindowShiftFiniteHorizon,
    extendPathConstantAfter_restrictPathTo]
  ext u
  unfold shiftAtFirstNonnegativeWindowStartUpTo
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
    have hu : (firstNonnegativeWindowStartUpTo f s).untopA + u.1 ≤ s :=
      (add_le_add_right u.property.2 _).trans ht
    change f (min ((firstNonnegativeWindowStartUpTo f s).untopA + u.1) s) =
      f ((firstNonnegativeWindowStartUpTo f s).untopA + u.1)
    rw [min_eq_left hu]

/-- The finite-horizon projected law $P^s$ and the whole-time path law
$P$ give the same shifted output law when paired with their respective
finite-window maps. -/
theorem finiteHorizonPathLaw_map_firstWindowShift
    (P : Measure C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    (finiteHorizonPathLaw P s).map (firstWindowShiftFiniteHorizon s) =
      P.map (fun f => restrictPathTo 1
        (shiftAtFirstNonnegativeWindowStartUpTo f s)) := by
  rw [finiteHorizonPathLaw, Measure.map_map]
  · congr 1
    funext f
    exact firstWindowShiftFiniteHorizon_restrictPathTo f s
  · exact measurable_firstWindowShiftFiniteHorizon s
  · exact (continuous_restrictPathTo s).measurable

/-- Almost-sure continuity may be transferred from a whole path to
its finite-horizon restriction by extending nearby finite paths with
the fixed reference path's future increments. -/
theorem continuousAt_firstWindowShiftFiniteHorizon_of_full
    (f : C(ℝ≥0, ℝ)) (s : ℝ≥0)
    (hcont : ContinuousAt
      (fun g => shiftAtFirstNonnegativeWindowStartUpTo g s) f) :
    ContinuousAt (firstWindowShiftFiniteHorizon s)
      (restrictPathTo s f) := by
  have hrepresentation (g : C(Set.Icc (0 : ℝ≥0) s, ℝ)) :
      firstWindowShiftFiniteHorizon s g =
        restrictPathTo 1
          (shiftAtFirstNonnegativeWindowStartUpTo
            (extendPathAlong f s g) s) := by
    conv_lhs => rw [← restrictPathTo_extendPathAlong f s g]
    exact firstWindowShiftFiniteHorizon_restrictPathTo
      (extendPathAlong f s g) s
  have hinner : ContinuousAt
      (fun g : C(Set.Icc (0 : ℝ≥0) s, ℝ) =>
        shiftAtFirstNonnegativeWindowStartUpTo
          (extendPathAlong f s g) s)
      (restrictPathTo s f) := by
    have hcont' : ContinuousAt
        (fun g => shiftAtFirstNonnegativeWindowStartUpTo g s)
        (extendPathAlong f s (restrictPathTo s f)) := by
      simpa only [extendPathAlong_restrictPathTo] using hcont
    exact hcont'.comp (continuous_extendPathAlong f s).continuousAt
  have houter := (continuous_restrictPathTo 1).continuousAt.comp hinner
  convert houter using 1
  funext g
  exact hrepresentation g

end ProbabilityTheory

end
