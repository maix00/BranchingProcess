/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Conditional finite products from complete-complement identities

## Public declarations

In `MeasureTheory`:

* `condExp_finsetProd_of_complement`: suppose `F ≤ Gᵢ ≤ F_ambient`,
  `E[fᵢ | Gᵢ] = gᵢ`, each `gᵢ` is `F`-strongly measurable, and every
  `fⱼ` with `j ≠ i` is `Gᵢ`-strongly measurable. Then
  `E[∏_(i ∈ s) fᵢ | F] = ∏_(i ∈ s) gᵢ` for each finite `s`, provided
  the finite products of the `fᵢ` and the products `gᵢ ∏_(j ∈ s) fⱼ`
  are integrable. The measure is finite; no standard-Borel or countability
  hypothesis on the sample or index space is imposed.

The proof iterates native conditional-expectation tower and pull-out identities.
It supplies the finite-product part of conditional independence from one-coordinate
identities, without constructing regular conditional probabilities or another
conditional-expectation object. This is an abstract conditional-integration
result; no tree, optional line or branching law appears in its interface.
-/

@[expose] public section

namespace MeasureTheory

/-- Complete-complement conditional identities imply conditional finite-product
factorization under explicit integrability of the products. -/
theorem condExp_finsetProd_of_complement {Ω I : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm : m ≤ mΩ)
    (G : I → MeasurableSpace Ω) (hG : ∀ i, G i ≤ mΩ) (hmG : ∀ i, m ≤ G i)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : I → Ω → ℝ) (hg : ∀ i, StronglyMeasurable[m] (g i))
    (hcross : ∀ i j, i ≠ j → StronglyMeasurable[G i] (f j))
    (hcond : ∀ i, μ[f i | G i] =ᵐ[μ] g i)
    (hfint : ∀ s : Finset I, Integrable (∏ i ∈ s, f i) μ)
    (hmix : ∀ i (s : Finset I), Integrable (g i * ∏ j ∈ s, f j) μ)
    (s : Finset I) : μ[∏ i ∈ s, f i | m] =ᵐ[μ] ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Filter.Eventually.of_forall (congrFun (condExp_const hm (1 : ℝ)))
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    have hfi : Integrable (f i) μ := by simpa only [Finset.prod_singleton] using hfint {i}
    have hprod : StronglyMeasurable[G i] (∏ j ∈ s, f j) :=
      s.stronglyMeasurable_prod (fun j hj => hcross i j (fun heq => hi (heq ▸ hj)))
    have hinner := condExp_mul_of_stronglyMeasurable_right hprod
      (by simpa only [Finset.prod_insert hi] using hfint (insert i s)) hfi
    have hinner' : μ[f i * ∏ j ∈ s, f j | G i] =ᵐ[μ] g i * ∏ j ∈ s, f j := by
      filter_upwards [hinner, hcond i] with x hx hix
      simpa only [Pi.mul_apply, hix] using hx
    calc
      _ =ᵐ[μ] μ[μ[f i * ∏ j ∈ s, f j | G i] | m] :=
        (condExp_condExp_of_le (hmG i) (hG i)).symm
      _ =ᵐ[μ] μ[g i * ∏ j ∈ s, f j | m] := condExp_congr_ae hinner'
      _ =ᵐ[μ] g i * μ[∏ j ∈ s, f j | m] :=
        condExp_mul_of_stronglyMeasurable_left (hg i) (hmix i s) (hfint s)
      _ =ᵐ[μ] _ := by
        filter_upwards [ih] with x hx
        simp only [Pi.mul_apply, hx]

end MeasureTheory

end
