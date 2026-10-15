/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Analysis.Real.Sqrt

/-!
# The last zero of a continuous path

The public definition and theorems in this file are:

- `ContinuousMap.lastZero`: $g(f)=\sup\{t\in[0,1]:f(t)=0\}$.
- `ContinuousMap.lastZero_apply_eq_zero`: if $f(0)=0$, then $f(g(f))=0$.
- `ContinuousMap.lastZero_lt_top_of_ne_zero`: if $f(0)=0$ and
  $f(1)\ne0$, then $g(f)<1$.
- `ContinuousMap.ne_zero_of_lastZero_lt`: if $g(f)<t\le1$, then $f(t)\ne0$.
- `ContinuousMap.tailAffineTime`: $(a,t)\mapsto a+(1-a)t$ maps
  $[0,1]^2$ to $[0,1]$.
- `ContinuousMap.lastZeroMeanderTransform`:
  $f\mapsto\left(t\mapsto(1-g(f))^{-1/2}
  |f(g(f)+(1-g(f))t)|\right)$ when $g(f)<1$, with the zero path
  used when $g(f)=1$.
- `ContinuousMap.lastZeroMeanderTransform_zero`: if $f(0)=0$,
  the transformed path starts at zero.
- `ContinuousMap.lastZeroMeanderTransform_nonnegative`: the transformed
  path is nonnegative at every time.

This is the zero-time functional used by Donald L. Iglehart,
*Functional Central Limit Theorems for Random Walks Conditioned to Stay
Positive*, Ann. Probab. 2(4) (1974), 608--619, Section 3, to describe
Brownian meander through the terminal excursion.
-/

@[expose] public section

namespace ContinuousMap

/-- The last zero of a continuous real path on the unit interval. -/
noncomputable def lastZero (f : C(unitInterval, ℝ)) : unitInterval :=
  sSup {t : unitInterval | f t = 0}

/-- Every zero of the path occurs no later than its last zero. -/
theorem le_lastZero_of_apply_eq_zero (f : C(unitInterval, ℝ))
    {t : unitInterval} (ht : f t = 0) : t ≤ lastZero f :=
  le_sSup ht

/-- The last zero is itself a zero when the path starts at zero. -/
theorem lastZero_apply_eq_zero (f : C(unitInterval, ℝ))
    (hf0 : f 0 = 0) : f (lastZero f) = 0 := by
  have hnonempty : Set.Nonempty {t : unitInterval | f t = 0} :=
    ⟨0, hf0⟩
  have hclosed : IsClosed {t : unitInterval | f t = 0} :=
    isClosed_singleton.preimage f.continuous
  exact IsClosed.sSup_mem hnonempty hclosed

/-- A path ending away from zero has its last zero strictly before one. -/
theorem lastZero_lt_top_of_ne_zero (f : C(unitInterval, ℝ))
    (hf0 : f 0 = 0) (hf1 : f ⊤ ≠ 0) : lastZero f < ⊤ := by
  exact lt_top_iff_ne_top.mpr (fun h =>
    hf1 (h ▸ lastZero_apply_eq_zero f hf0))

/-- The path has no zero after its last zero. -/
theorem ne_zero_of_lastZero_lt (f : C(unitInterval, ℝ))
    {t : unitInterval} (ht : lastZero f < t) : f t ≠ 0 := by
  intro hzero
  exact (not_le_of_gt ht) (le_lastZero_of_apply_eq_zero f hzero)

/-- Affine rescaling of the terminal interval `[start, 1]` to the
unit interval. -/
def tailAffineTime (start t : unitInterval) : unitInterval :=
  ⟨(start : ℝ) + (1 - (start : ℝ)) * (t : ℝ), by
    constructor
    · have hs := start.property.1
      have ht := t.property.1
      have hsu := start.property.2
      nlinarith
    · have hs := start.property.1
      have hsu := start.property.2
      have ht := t.property.1
      have htu := t.property.2
      nlinarith⟩

@[simp]
theorem tailAffineTime_zero (start : unitInterval) :
    tailAffineTime start 0 = start := by
  apply Subtype.ext
  simp [tailAffineTime]

@[simp]
theorem tailAffineTime_top (start : unitInterval) :
    tailAffineTime start ⊤ = ⊤ := by
  apply Subtype.ext
  simp [tailAffineTime]

theorem continuous_tailAffineTime (start : unitInterval) :
    Continuous (tailAffineTime start) := by
  have hreal : Continuous
      (fun t : unitInterval => (start : ℝ) + (1 - (start : ℝ)) * (t : ℝ)) := by
    fun_prop
  exact hreal.subtype_mk _

/-- The terminal Brownian-meander path transform from Iglehart,
Section 3, expressed for an arbitrary continuous path. -/
noncomputable def lastZeroMeanderTransform
    (f : C(unitInterval, ℝ)) : C(unitInterval, ℝ) :=
  ⟨(fun t => if lastZero f = ⊤ then 0 else
      |f (tailAffineTime (lastZero f) t)| /
        Real.sqrt (1 - (lastZero f : ℝ))), by
    by_cases h : lastZero f = ⊤
    · simpa only [h, ↓reduceIte] using (continuous_const :
        Continuous (fun _ : unitInterval => (0 : ℝ)))
    · simpa only [h, ↓reduceIte, Function.comp_apply] using
        ((continuous_abs.comp (f.continuous.comp
          (continuous_tailAffineTime (lastZero f)))).div_const
            (Real.sqrt (1 - (lastZero f : ℝ))))⟩

/-- The last-zero transform starts at zero when the original path does. -/
theorem lastZeroMeanderTransform_zero
    (f : C(unitInterval, ℝ)) (hf0 : f 0 = 0) :
    lastZeroMeanderTransform f 0 = 0 := by
  by_cases h : lastZero f = ⊤
  · simp [lastZeroMeanderTransform, h]
  · simp [lastZeroMeanderTransform, h, lastZero_apply_eq_zero f hf0]

/-- The transformed path is nonnegative at every time. -/
theorem lastZeroMeanderTransform_nonnegative
    (f : C(unitInterval, ℝ)) (t : unitInterval) :
    0 ≤ lastZeroMeanderTransform f t := by
  unfold lastZeroMeanderTransform
  dsimp
  split_ifs
  · exact le_refl 0
  · exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

end ContinuousMap

end
