/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Null sections of independent random variables

The public theorems in this file are:

- `ProbabilityTheory.IndepFun.measure_preimage_eq_zero_of_null_sections`:
  if $X$ and $Y$ are independent and every section
  $\{b:(a,b)\in E\}$ has zero $Y$-law, then
  $\mathbb P((X,Y)\in E)=0$.

- `ProbabilityTheory.IndepFun.measure_eq_zero_of_null_sections`:
  if $X$ and $Y$ are independent and
  $\mathbb P(F(a,Y)=0)=0$ for every $a$, then
  $\mathbb P(F(X,Y)=0)=0$.

The proof identifies the joint law with a product measure and applies
Fubini's theorem to the zero-mass sections. It is a reusable conditional
atomlessness step for Brownian first-passage times.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- A measurable event with null sections for the second marginal has
zero probability under the joint law of independent variables. -/
theorem IndepFun.measure_preimage_eq_zero_of_null_sections
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → A} {Y : Ω → B} (hXY : X ⟂ᵢ[P] Y)
    (hX : Measurable X) (hY : Measurable Y)
    {E : Set (A × B)} (hE : MeasurableSet E)
    (hnull : ∀ a : A, (P.map Y) {b : B | (a, b) ∈ E} = 0) :
    P {ω | (X ω, Y ω) ∈ E} = 0 := by
  have hprod : (P.map X).prod (P.map Y) E = 0 := by
    apply (Measure.measure_prod_null hE).2
    filter_upwards [] with a
    exact hnull a
  calc
    P {ω | (X ω, Y ω) ∈ E} =
        P.map (fun ω => (X ω, Y ω)) E := by
      rw [Measure.map_apply (hX.prodMk hY) hE]
      rfl
    _ = (P.map X).prod (P.map Y) E := by
      rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
    _ = 0 := hprod

/-- An independent random parameter may be substituted into a family
of null events when the family is jointly measurable. -/
theorem IndepFun.measure_eq_zero_of_null_sections
    {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSpace B] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → A} {Y : Ω → B} (hXY : X ⟂ᵢ[P] Y)
    (hX : Measurable X) (hY : Measurable Y)
    (F : A → B → ℝ)
    (hF : Measurable (fun p : A × B => F p.1 p.2))
    (hnull : ∀ a : A, (P.map Y) {b : B | F a b = 0} = 0) :
    P {ω | F (X ω) (Y ω) = 0} = 0 := by
  let E : Set (A × B) := {p | F p.1 p.2 = 0}
  have hE : MeasurableSet E := hF (measurableSet_singleton 0)
  have hprod : (P.map X).prod (P.map Y) E = 0 := by
    apply (Measure.measure_prod_null hE).2
    filter_upwards [] with a
    exact hnull a
  calc
    P {ω | F (X ω) (Y ω) = 0} =
        P.map (fun ω => (X ω, Y ω)) E := by
      rw [Measure.map_apply (hX.prodMk hY) hE]
      rfl
    _ = (P.map X).prod (P.map Y) E := by
      rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
    _ = 0 := hprod

end ProbabilityTheory

end
