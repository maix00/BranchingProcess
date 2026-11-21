/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Changing the input coordinate in a joint kernel law

## Public declarations

* `MeasureTheory.Measure.map_compProd_left` states
  $(f_\#\mu)\otimes\kappa=(f\times\mathrm{id})_\#
  (\mu\otimes(\kappa\circ f))$ for measurable $f$ and s-finite data.
  This is the first-coordinate counterpart of Mathlib's `Measure.compProd_map`.
* `MeasureTheory.Measure.map_compProd_eq_of_ae` transports a joint law through
  observations $(f,g)$ when $g_\#\kappa(x)=\eta(f(x))$ almost everywhere.
-/

@[expose] public section

open ProbabilityTheory

namespace MeasureTheory.Measure

/-- Change the past coordinate of a joint law and pull the conditional kernel back. -/
theorem map_compProd_left {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) [SFinite μ] (f : A → B) (hf : Measurable f)
    (κ : Kernel B C) [IsSFiniteKernel κ] :
    (μ.map f) ⊗ₘ κ = (μ ⊗ₘ κ.comap f hf).map (Prod.map f id) := by
  ext E hE
  rw [compProd_apply hE, map_apply (by fun_prop) hE,
    compProd_apply (hE.preimage (by fun_prop)),
    lintegral_map (Kernel.measurable_kernel_prodMk_left hE) hf]
  rfl


/-- A measurable observation preserves a joint kernel law when its conditional
future law depends on the observed past alone. -/
theorem map_compProd_eq_of_ae {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) [SFinite μ] (f : A → C) (hf : Measurable f)
    (g : B → D) (hg : Measurable g)
    (κ : Kernel A B) [IsSFiniteKernel κ] (η : Kernel C D) [IsSFiniteKernel η]
    (hκ : κ.map g =ᵐ[μ] η.comap f hf) :
    (μ ⊗ₘ κ).map (Prod.map f g) = (μ.map f) ⊗ₘ η := by
  have hcomp : (Prod.map f g) = (Prod.map f id) ∘ (Prod.map id g) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← compProd_map hg, compProd_congr hκ, ← map_compProd_left μ f hf η]

end MeasureTheory.Measure
