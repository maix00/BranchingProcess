/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Measurability of a fixed-density transformation of measures

For a fixed measurable density $w$, the map sending a measure $\mu$ to
$\mu.withDensity(w)$ is measurable. This is the parameter-dual of Mathlib's
`measurable_withDensity`, which fixes the base measure and varies the density.

## Public declarations

- `MeasureTheory.Measure.measurable_withDensity_fixed`:
  for measurable $w$, the transformation
  $\mu\mapsto\mu.withDensity(w)$ is measurable on the space of measures.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MeasureTheory.Measure

/-- For fixed measurable density `w`, weighting a measure by `w` is a
measurable map on the space of measures. -/
theorem measurable_withDensity_fixed
    {E : Type*} [MeasurableSpace E]
    {w : E → ℝ≥0∞} (hw : Measurable w) :
    Measurable (fun μ : Measure E => μ.withDensity w) := by
  rw [Measure.measurable_measure]
  intro s hs
  simp_rw [withDensity_apply _ hs]
  have h := Measure.measurable_lintegral (hw.indicator hs)
  convert h using 1
  funext μ
  exact (lintegral_indicator hs w).symm

end MeasureTheory.Measure

end
