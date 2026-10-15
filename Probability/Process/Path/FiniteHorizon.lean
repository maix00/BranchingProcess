/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Continuous
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Continuous paths on a finite time horizon

The public definitions and theorems in this file are:

- `ProbabilityTheory.restrictPathTo`: the restriction
  $f|_{[0,s]}\in C([0,s],\mathbb R)$ of a continuous path on
  $[0,\infty)$.
- `ProbabilityTheory.continuous_restrictPathTo`: restriction is
  continuous for the compact-open topologies.
- `ProbabilityTheory.extendPathConstantAfter`: the extension of
  $g\in C([0,s],\mathbb R)$ that equals $g(s)$ after time $s$.
- `ProbabilityTheory.continuous_extendPathConstantAfter`: this extension
  is continuous as a map between continuous-path spaces.
- `ProbabilityTheory.restrictPathTo_extendPathConstantAfter`: restricting
  the extension recovers $g$.
- `ProbabilityTheory.extendPathConstantAfter_restrictPathTo`: extending
  a restriction gives the path stopped at $s$.
- `ProbabilityTheory.finiteHorizonPathLaw`: the projected law
  $P^s=P\circ\Pi_s^{-1}$ on $C([0,s],\mathbb R)$.
- `ProbabilityTheory.extendPathAlong`: extend a finite path past $s$
  using the increments of a fixed whole-time reference path.
- `ProbabilityTheory.continuous_extendPathAlong`: this extension is
  continuous in the finite path.
- `ProbabilityTheory.restrictPathTo_extendPathAlong`: the extension
  restricts to the original finite path.
- `ProbabilityTheory.extendPathAlong_restrictPathTo`: using the
  reference path's own restriction recovers the reference path.

These maps realize the projection $\Pi_s:C^\infty\to C^s$ used in
Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Section 3, Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- Restrict a continuous path to the closed interval $[0,s]$. -/
noncomputable def restrictPathTo (s : ℝ≥0) (f : C(ℝ≥0, ℝ)) :
    C(Set.Icc (0 : ℝ≥0) s, ℝ) :=
  ⟨fun t => f t.1, f.continuous.comp continuous_subtype_val⟩

/-- Restriction to a finite time interval is continuous. -/
theorem continuous_restrictPathTo (s : ℝ≥0) :
    Continuous (restrictPathTo s) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_eval.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- Extend a finite-horizon path by holding its endpoint value constant. -/
noncomputable def extendPathConstantAfter (s : ℝ≥0)
    (f : C(Set.Icc (0 : ℝ≥0) s, ℝ)) : C(ℝ≥0, ℝ) := by
  let clamp : ℝ≥0 → Set.Icc (0 : ℝ≥0) s := fun t =>
    ⟨min t s, ⟨bot_le, min_le_right t s⟩⟩
  have hclamp : Continuous clamp := by
    exact Continuous.subtype_mk (continuous_id.min continuous_const) _
  exact ⟨fun t => f (clamp t), f.continuous.comp hclamp⟩

/-- Constant extension is continuous in the finite-horizon path. -/
theorem continuous_extendPathConstantAfter (s : ℝ≥0) :
    Continuous (extendPathConstantAfter s) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  exact continuous_eval.comp
    (continuous_fst.prodMk
      (Continuous.subtype_mk (continuous_snd.min continuous_const) _))

/-- Restricting a constant extension recovers the finite path. -/
@[simp]
theorem restrictPathTo_extendPathConstantAfter (s : ℝ≥0)
    (f : C(Set.Icc (0 : ℝ≥0) s, ℝ)) :
    restrictPathTo s (extendPathConstantAfter s f) = f := by
  ext t
  change f (⟨min t.1 s, ⟨bot_le, min_le_right t.1 s⟩⟩ :
    Set.Icc (0 : ℝ≥0) s) = f t
  simp [min_eq_left t.property.2]

/-- Constant extension after restriction agrees with stopping the path
at the horizon. -/
theorem extendPathConstantAfter_restrictPathTo (s : ℝ≥0)
    (f : C(ℝ≥0, ℝ)) :
    extendPathConstantAfter s (restrictPathTo s f) = freezeAfter f s := by
  ext t
  rfl

/-- The law of a whole-time continuous path observed only through
time `s`; this is the distinction between $P$ and $P^s$. -/
noncomputable def finiteHorizonPathLaw
    (P : Measure C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    Measure C(Set.Icc (0 : ℝ≥0) s, ℝ) :=
  P.map (restrictPathTo s)

/-- Projection preserves total probability mass. -/
instance finiteHorizonPathLaw.isProbabilityMeasure
    (P : Measure C(ℝ≥0, ℝ)) [IsProbabilityMeasure P] (s : ℝ≥0) :
    IsProbabilityMeasure (finiteHorizonPathLaw P s) := by
  unfold finiteHorizonPathLaw
  infer_instance

/-- Continue a finite path after time `s` with the increments of a
fixed reference path. The continuation agrees with the finite path
at the joining time. -/
noncomputable def extendPathAlong (reference : C(ℝ≥0, ℝ)) (s : ℝ≥0)
    (f : C(Set.Icc (0 : ℝ≥0) s, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨fun t => extendPathConstantAfter s f t + reference t -
    freezeAfter reference s t, by fun_prop⟩

/-- The reference-tail extension is continuous in its finite path. -/
theorem continuous_extendPathAlong (reference : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    Continuous (extendPathAlong reference s) := by
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have hfirst : Continuous (fun p : C(Set.Icc (0 : ℝ≥0) s, ℝ) × ℝ≥0 =>
      extendPathConstantAfter s p.1 p.2) :=
    continuous_eval.comp
      (((continuous_extendPathConstantAfter s).comp continuous_fst).prodMk
        continuous_snd)
  have href : Continuous (fun p : C(Set.Icc (0 : ℝ≥0) s, ℝ) × ℝ≥0 =>
      reference p.2) := reference.continuous.comp continuous_snd
  have hstop : Continuous (fun p : C(Set.Icc (0 : ℝ≥0) s, ℝ) × ℝ≥0 =>
      freezeAfter reference s p.2) :=
    (freezeAfter reference s).continuous.comp continuous_snd
  exact (hfirst.add href).sub hstop

/-- The reference-tail extension agrees with the finite path on
the observed time interval. -/
@[simp]
theorem restrictPathTo_extendPathAlong (reference : C(ℝ≥0, ℝ))
    (s : ℝ≥0) (f : C(Set.Icc (0 : ℝ≥0) s, ℝ)) :
    restrictPathTo s (extendPathAlong reference s f) = f := by
  ext t
  change f (⟨min t.1 s, ⟨bot_le, min_le_right t.1 s⟩⟩ :
      Set.Icc (0 : ℝ≥0) s) + reference t.1 - reference (min t.1 s) = f t
  simp only [min_eq_left t.property.2]
  ring

/-- The reference-tail extension of the reference path's restriction
is the reference path itself. -/
@[simp]
theorem extendPathAlong_restrictPathTo (reference : C(ℝ≥0, ℝ))
    (s : ℝ≥0) :
    extendPathAlong reference s (restrictPathTo s reference) = reference := by
  ext t
  change reference (min t s) + reference t - reference (min t s) =
    reference t
  ring

end ProbabilityTheory

end
