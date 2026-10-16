/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Equality of independent variables with an atomless law

The public theorem in this file is:

- `ProbabilityTheory.IndepFun.measure_eq_zero_of_right_atomless`:
  if real-valued $X$ and $Y$ are independent and the law of $Y$
  has no atoms, then $\mathbb P(X=Y)=0$.

The proof identifies the joint law with the product law and integrates
the zero mass of each singleton section of the diagonal. This is the
probability step for the rational-interval argument in Lemma 2.3 of
Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- Independent real-valued variables coincide with probability zero
when the second marginal assigns zero mass to every singleton. -/
theorem IndepFun.measure_eq_zero_of_right_atomless
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {X Y : Ω → ℝ} (hXY : X ⟂ᵢ[P] Y)
    (hX : Measurable X) (hY : Measurable Y)
    (hnull : ∀ y : ℝ, (P.map Y) {y} = 0) :
    P {ω | X ω = Y ω} = 0 := by
  let diagonal : Set (ℝ × ℝ) := {z | z.1 = z.2}
  have hdiag : MeasurableSet diagonal :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hprod : (P.map X).prod (P.map Y) diagonal = 0 := by
    apply (Measure.measure_prod_null hdiag).2
    filter_upwards [] with x
    have hsection : (Prod.mk x) ⁻¹' diagonal = {x} := by
      ext y
      simp [diagonal, eq_comm]
    rw [hsection]
    exact hnull x
  calc
    P {ω | X ω = Y ω} = P.map (fun ω => (X ω, Y ω)) diagonal := by
      rw [Measure.map_apply (hX.prodMk hY) hdiag]
      rfl
    _ = (P.map X).prod (P.map Y) diagonal := by
      rw [hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
    _ = 0 := hprod

end ProbabilityTheory

end
