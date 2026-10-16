/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Coupling.Basic

/-!
# Tail comparison through a coupling

An almost-sure order between two real-valued observables transfers upper-tail
probability bounds through the corresponding coupling.
-/

open MeasureTheory

namespace ProbabilityTheory.Coupling

/-- If the second observable is almost surely at most the first, its upper
tail probability is at most the first observable's upper tail probability. -/
theorem measure_ge_le_of_ae_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (κ : ProbabilityTheory.Coupling μ ν)
    (f : X → ℝ) (g : Y → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (horder : ∀ᵐ p ∂κ.joint, g p.2 ≤ f p.1)
    (threshold : ℝ) :
    ν {y | threshold ≤ g y} ≤ μ {x | threshold ≤ f x} := by
  let targetEvent : Set (X × Y) := {p | threshold ≤ g p.2}
  let sourceEvent : Set (X × Y) := {p | threshold ≤ f p.1}
  have hsubset : ∀ᵐ p ∂κ.joint, p ∈ targetEvent → p ∈ sourceEvent := by
    filter_upwards [horder] with p hp
    intro htarget
    exact htarget.trans hp
  have htargetSet : MeasurableSet {y | threshold ≤ g y} :=
    measurableSet_Ici.preimage hg
  have hsourceSet : MeasurableSet {x | threshold ≤ f x} :=
    measurableSet_Ici.preimage hf
  have htargetMap : κ.joint targetEvent = ν {y | threshold ≤ g y} := by
    have hpreimage : targetEvent =
        Prod.snd ⁻¹' {y | threshold ≤ g y} := by
      ext p
      rfl
    rw [hpreimage, ← Measure.map_apply measurable_snd htargetSet,
      κ.snd_joint]
  have hsourceMap : κ.joint sourceEvent = μ {x | threshold ≤ f x} := by
    have hpreimage : sourceEvent =
        Prod.fst ⁻¹' {x | threshold ≤ f x} := by
      ext p
      rfl
    rw [hpreimage, ← Measure.map_apply measurable_fst hsourceSet,
      κ.fst_joint]
  rw [← htargetMap, ← hsourceMap]
  exact measure_mono_ae hsubset

end ProbabilityTheory.Coupling
