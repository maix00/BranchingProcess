/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional integration from an explicit joint kernel law

## Public declarations

* `ProbabilityTheory.Kernel.condExp_of_jointLaw`: if
  $P\circ(X,Y)^{-1}=(P\circ X^{-1})\otimes\kappa$, then for strongly
  measurable $g$ with $g(X,Y)\in L^1(P)$,
  $E[g(X,Y)\mid X]=\int g(X,y)\,\kappa(X,dy)$ almost surely.

The supplied joint-law identity identifies an existing conditional kernel;
no regular-conditional-distribution construction or standard-Borel
hypothesis is needed. The proof uses Mathlib's kernel Fubini theorem and
conditional-expectation uniqueness.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

/-- Integrate a conditional kernel identified by the joint law, on arbitrary
measurable value spaces. -/
theorem condExp_of_jointLaw {Ω A B E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (Y : Ω → B) (hX : Measurable X) (hY : Measurable Y)
    (κ : Kernel A B) [IsMarkovKernel κ]
    (hlaw : P.map (fun ω ↦ (X ω, Y ω)) = (P.map X) ⊗ₘ κ)
    {g : A × B → E} (hg : StronglyMeasurable g)
    (hgi : Integrable (fun ω ↦ g (X ω, Y ω)) P) :
    P[fun ω ↦ g (X ω, Y ω) | MeasurableSpace.comap X inferInstance] =ᵐ[P]
      fun ω ↦ ∫ y, g (X ω, y) ∂κ (X ω) := by
  have hj : Integrable g ((P.map X) ⊗ₘ κ) := by
    rw [← hlaw]
    exact (integrable_map_measure hg.aestronglyMeasurable
      (hX.prodMk hY).aemeasurable).mpr hgi
  let G : A → E := fun x ↦ ∫ y, g (x, y) ∂κ x
  have hG : StronglyMeasurable G := hg.integral_kernel_prod_right'
  have hGi : Integrable G (P.map X) := by
    change Integrable g ((Kernel.const Unit (P.map X) ⊗ₖ
      κ.prodMkLeft Unit) ()) at hj
    simpa only [Kernel.const_apply, Kernel.prodMkLeft_apply] using hj.integral_compProd
  have hcomp : Integrable (fun ω ↦ G (X ω)) P :=
    (integrable_map_measure hG.aestronglyMeasurable hX.aemeasurable).mp hGi
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hgi
    (fun _ _ _ ↦ hcomp.integrableOn) ?_ ?_).symm
  · rintro _ ⟨t, ht, rfl⟩ _
    change ∫ ω in X ⁻¹' t, G (X ω) ∂P = ∫ ω in X ⁻¹' t, g (X ω, Y ω) ∂P
    rw [← setIntegral_map ht hG.aestronglyMeasurable hX.aemeasurable]
    calc
      ∫ x in t, G x ∂P.map X =
          ∫ p in t ×ˢ Set.univ, g p ∂(P.map X) ⊗ₘ κ := by
        symm
        simpa only [setIntegral_univ] using
          Measure.setIntegral_compProd ht MeasurableSet.univ hj.integrableOn
      _ = ∫ p in t ×ˢ Set.univ, g p ∂P.map (fun ω ↦ (X ω, Y ω)) := by rw [hlaw]
      _ = _ := by
        rw [setIntegral_map (ht.prod MeasurableSet.univ) hg.aestronglyMeasurable
          (hX.prodMk hY).aemeasurable]
        simp only [Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ]
  · exact (hG.comp_measurable (Measurable.of_comap_le le_rfl)).aestronglyMeasurable

end ProbabilityTheory.Kernel
