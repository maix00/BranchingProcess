/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Product intensities on unit time and a mark space

Lebesgue measure on the unit interval has total mass one. Thus a product
intensity on time and marks has the same full-time mark integrals and masses
as its mark measure. These are the unit-time specializations of product
measure integration used by marked Poisson random measures.

## Public declarations

* `lintegral_unitTime_prod_mark` and `integral_unitTime_prod_mark` identify
  integrals of mark-only functions against unit-time product intensity.
* `unitTime_prod_markWindow`, `unitTime_prod_restrict_markWindow`, and
  `unitTime_prod_restrict_carrier` give full-time mass, restricted-window
  mass, and support statements.

Writing `\lambda_{[0,1]}` for Lebesgue measure on the unit interval, adjoining
the time coordinate preserves mark-only integrals and masses:

\[\begin{aligned}
\int_{[0,1]\times\mathbb R}f(x)\,d(\lambda_{[0,1]}\otimes\nu)(t,x)
&=\int_{\mathbb R}f(x)\,d\nu(x),\\
(\lambda_{[0,1]}\otimes\nu)([0,1]\times A)&=\nu(A),\\
(\lambda_{[0,1]}\otimes(\nu|_J))([0,1]\times A)&=\nu(A)
  \quad(A\subseteq J,\ A,J\text{ measurable}).
\end{aligned}\]

-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- A mark-only nonnegative integral is unchanged by adjoining unit-time
Lebesgue intensity. -/
theorem lintegral_unitTime_prod_mark
    (ν : Measure ℝ) [SigmaFinite ν]
    (f : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ z : unitInterval × ℝ, f z.2
      ∂((volume : Measure unitInterval).prod ν)) =
      ∫⁻ x, f x ∂ν := by
  rw [lintegral_prod (fun z : unitInterval × ℝ => f z.2)
    (hf.comp measurable_snd).aemeasurable]
  simp

/-- A Bochner-integrable mark observable is likewise unchanged by the
unit-time product intensity. -/
theorem integral_unitTime_prod_mark
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ν : Measure ℝ) [SigmaFinite ν]
    (f : ℝ → E) (hf : Integrable f ν) :
    (∫ z : unitInterval × ℝ, f z.2
      ∂((volume : Measure unitInterval).prod ν)) =
      ∫ x, f x ∂ν := by
  rw [integral_prod _ (hf.comp_snd (volume : Measure unitInterval))]
  simp

/-- The product intensity of a full-time mark window equals its Lévy mark
mass, including infinite mass. -/
theorem unitTime_prod_markWindow
    (ν : Measure ℝ) [SigmaFinite ν] (A : Set ℝ) :
    ((volume : Measure unitInterval).prod ν) (Set.univ ×ˢ A) = ν A := by
  rw [Measure.prod_prod]
  simp

/-- Restricting mark intensity to a region does not change the mass of a
measurable window already inside that region. -/
theorem unitTime_prod_restrict_markWindow
    (ν : Measure ℝ) [SigmaFinite ν]
    {A J : Set ℝ} (hJ : MeasurableSet J) (hJA : J ⊆ A) :
    ((volume : Measure unitInterval).prod (ν.restrict A))
      (Set.univ ×ˢ J) = ν J := by
  rw [unitTime_prod_markWindow, Measure.restrict_apply hJ]
  congr 1
  exact Set.inter_eq_left.mpr hJA

/-- A product intensity with restricted marks is carried by the
corresponding full-time mark region. -/
theorem unitTime_prod_restrict_carrier
    (ν : Measure ℝ) [SigmaFinite ν] (A : Set ℝ) (hA : MeasurableSet A) :
    ((volume : Measure unitInterval).prod (ν.restrict A))
      (Set.univ ×ˢ A)ᶜ = 0 := by
  have hcompl : (Set.univ ×ˢ A : Set (unitInterval × ℝ))ᶜ =
      Set.univ ×ˢ Aᶜ := by
    ext z
    simp
  rw [hcompl, Measure.prod_prod]
  simp [Measure.restrict_apply hA.compl]

end ProbabilityTheory
