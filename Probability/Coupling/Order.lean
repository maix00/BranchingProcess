/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Order.UpperLower.Basic
public import Probability.Coupling.Basic

/-!
# Order comparison under a coupling

An almost-sure order between coupled observables compares the probabilities of
all measurable upper sets. This formulation applies to any measurable ordered
codomain and specializes to upper-tail comparison on `ℝ`.

## Public declarations

* `ProbabilityTheory.Coupling.measure_preimage_le_of_ae_le`: if
  `g(p.2) ≤ f(p.1)` almost surely under a coupling and `s` is a measurable
  upper set, then `ν (g ⁻¹' s) ≤ μ (f ⁻¹' s)`.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Coupling

/-- An almost-sure order under a coupling compares the measures of preimages
of every measurable upper set. -/
theorem measure_preimage_le_of_ae_le
    {X Y α : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace α] [LE α]
    {μ : Measure X} {ν : Measure Y} {s : Set α}
    (hs : IsUpperSet s) (hms : MeasurableSet s)
    (κ : ProbabilityTheory.Coupling μ ν)
    (f : X → α) (g : Y → α)
    (hf : Measurable f) (hg : Measurable g)
    (horder : ∀ᵐ p ∂κ.joint, g p.2 ≤ f p.1) :
    ν (g ⁻¹' s) ≤ μ (f ⁻¹' s) := by
  let targetEvent : Set (X × Y) := {p | g p.2 ∈ s}
  let sourceEvent : Set (X × Y) := {p | f p.1 ∈ s}
  have hsubset : ∀ᵐ p ∂κ.joint, p ∈ targetEvent → p ∈ sourceEvent := by
    filter_upwards [horder] with p hp
    intro htarget
    exact hs hp htarget
  have htargetMap : κ.joint targetEvent = ν (g ⁻¹' s) := by
    have hpreimage : targetEvent = Prod.snd ⁻¹' (g ⁻¹' s) := by
      ext p
      rfl
    rw [hpreimage, ← Measure.map_apply measurable_snd (hms.preimage hg),
      κ.snd_joint]
  have hsourceMap : κ.joint sourceEvent = μ (f ⁻¹' s) := by
    have hpreimage : sourceEvent = Prod.fst ⁻¹' (f ⁻¹' s) := by
      ext p
      rfl
    rw [hpreimage, ← Measure.map_apply measurable_fst (hms.preimage hf),
      κ.fst_joint]
  rw [← htargetMap, ← hsourceMap]
  exact measure_mono_ae hsubset

end ProbabilityTheory.Coupling
