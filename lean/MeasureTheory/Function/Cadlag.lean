/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Topology.Cadlag.Jump

/-!
# Measurability of càdlàg time sections

On a compact linearly ordered metric time domain, càdlàg paths have only
countably many discontinuities. Mathlib's general countable-discontinuity
criterion then makes each path measurable as a function of time.

This is measurability of a fixed path's time section. It does not assert that
the evaluation map on a path space is measurable.
-/

@[expose] public section

open MeasureTheory

/-- A càdlàg function on a compact ordered metric space is measurable when
the domain's open sets are measurable and the codomain carries its Borel
measurable structure. -/
theorem IsCadlag.measurable
    {T E : Type*} [LinearOrder T] [PseudoMetricSpace T] [OrderBot T]
    [OrderTopology T] [CompactSpace T] [MeasurableSpace T]
    [OpensMeasurableSpace T] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] {f : T → E} (hf : IsCadlag f) :
    Measurable f :=
  measurable_of_countable_not_continuousAt hf.countable_discontinuitySet

end
