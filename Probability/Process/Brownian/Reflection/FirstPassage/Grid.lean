/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.FirstPassage.FiniteStoppingTime
public import Mathlib.Probability.Process.HittingTime

/-!
# Reflection at a first grid passage time

The public definition and theorem in this file are:

- `ProbabilityTheory.gridFirstPassage`: the first index $i$ among finitely
  many ordered observation times with $f(r_i)\in S$, taking the final
  index if none is found.
- `ProbabilityTheory.IsBrownianReal.measure_reflectAfter_gridFirstPassage_eq`:
  if $T$ is the first of finitely many ordered observation times at which
  a Brownian path enters a Borel set, reflecting the path after $T$
  preserves its law.

The finite-valued first-passage approximation follows the stopping-time
step in Theorem 2.1 of S. J. Dilworth and Duncan Wright, *A direct proof
of the reflection principle for Brownian motion*, Theory Stoch. Process.
21(37):2 (2016), 1--3, arXiv:1810.01783. The reflection principle supports the Lévy
running-minimum identity cited in Lemma 2.3 of Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- The first observation index at which a continuous path visits `s`,
or the last index if no observation visits `s`. -/
noncomputable def gridFirstPassage (N : ℕ) (r : Fin (N + 1) → ℝ≥0)
    (s : Set ℝ) (f : C(ℝ≥0, ℝ)) : Fin (N + 1) :=
  hittingBtwn (fun i (f : C(ℝ≥0, ℝ)) => f (r i)) s 0 (Fin.last N) f

/-- Reflection at a first visit among finitely many ordered times
preserves the law of a Brownian path. This instantiates the finite-valued
stopping-time step of Theorem 2.1 in S. J. Dilworth and Duncan Wright,
*A direct proof of the reflection principle for Brownian motion*,
arXiv:1810.01783, using `MeasureTheory.Adapted.isStoppingTime_hittingBtwn`. -/
theorem IsBrownianReal.measure_reflectAfter_gridFirstPassage_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    (N : ℕ) (r : Fin (N + 1) → ℝ≥0) (hr : Monotone r)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (P.map (hB.continuousPathMap hBmeasurable)).map
        (fun f => reflectAfter f (r (gridFirstPassage N r s f))) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  let u : Fin (N + 1) → C(ℝ≥0, ℝ) → ℝ := fun i f => f (r i)
  have hum (i : Fin (N + 1)) : StronglyMeasurable (u i) :=
    (ContinuousMap.measurable_eval (r i)).stronglyMeasurable
  let ℱ := Filtration.natural u hum
  have hu : Adapted ℱ u := (Filtration.stronglyAdapted_natural hum).adapted
  have hτ : IsStoppingTime ℱ
      (fun f : C(ℝ≥0, ℝ) =>
        (gridFirstPassage N r s f : WithTop (Fin (N + 1)))) := by
    exact hu.isStoppingTime_hittingBtwn hs
  have hstop (i : Fin (N + 1)) :
      MeasurableSet[MeasurableSpace.comap
        (fun f : C(ℝ≥0, ℝ) => fun v : Set.Iic (r i) => f v) inferInstance]
        {f | gridFirstPassage N r s f = i} := by
    have hi : MeasurableSet[ℱ i] {f : C(ℝ≥0, ℝ) |
        gridFirstPassage N r s f = i} := by
      simpa using hτ.measurableSet_eq i
    rw [Filtration.natural_eq_comap u hum i] at hi
    obtain ⟨E, hE, hEeq⟩ := (MeasurableSpace.measurableSet_comap).mp hi
    let restrict : (Set.Iic (r i) → ℝ) → (Set.Iic i → ℝ) :=
      fun p j => p ⟨r j, hr j.2⟩
    have hrestrict : Measurable restrict := by
      rw [measurable_pi_iff]
      intro j
      exact measurable_pi_apply (⟨r j, hr j.2⟩ : Set.Iic (r i))
    refine (MeasurableSpace.measurableSet_comap).mpr ⟨restrict ⁻¹' E,
      hrestrict hE, ?_⟩
    rw [← hEeq]
    rfl
  exact hB.measure_reflectAfter_finiteStoppingTime_eq hBmeasurable
    (gridFirstPassage N r s) r hstop

end ProbabilityTheory

end
