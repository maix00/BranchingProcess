/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.FiniteStoppingTime
public import Probability.Process.Path.FirstPassage
public import Mathlib.Probability.Process.HittingTime

/-!
# Finite observation times for continuous first passage

The public definition and theorem in this file are:

- `ProbabilityTheory.firstPassageGridCeiling`: the first observation index
  by which the continuous first passage below $a$ has occurred, taking
  the last index when no such observation exists.
- `ProbabilityTheory.IsBrownianReal.measure_reflectAfter_firstPassageGridCeiling_eq`:
  reflection after this finite approximation preserves Brownian path law.

This is the upward finite-valued stopping-time approximation in the proof
of Theorem 2.1 of S. J. Dilworth and Duncan Wright, *A direct proof of the
reflection principle for Brownian motion*, Theory Stoch. Process. 21(37):2
(2016), 1--3, arXiv:1810.01783. The resulting reflection principle is
used for the Lévy running-minimum identity cited in Lemma 2.3 of Erwin
Bolthausen, *On a functional central limit theorem for random walks
conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Classical

namespace ProbabilityTheory

/-- The first grid index by which a continuous path has fallen below
`a`, using the last index if this has not yet happened. -/
noncomputable def firstPassageGridCeiling (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (a : ℝ) (f : C(ℝ≥0, ℝ)) : Fin (N + 1) :=
  hittingBtwn
    (fun i (g : C(ℝ≥0, ℝ)) =>
      if firstPassageBelow g a ≤ r i then true else false)
    {true} 0 (Fin.last N) f

/-- Reflection at the first grid time after continuous first passage
preserves Brownian path law. This is the finite-valued stopping-time
approximation in Theorem 2.1 of S. J. Dilworth and Duncan Wright,
*A direct proof of the reflection principle for Brownian motion*,
arXiv:1810.01783. -/
theorem IsBrownianReal.measure_reflectAfter_firstPassageGridCeiling_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    (N : ℕ) (r : Fin (N + 1) → ℝ≥0) (hr : Monotone r)
    (a : ℝ) :
    (P.map (hB.continuousPathMap hBmeasurable)).map
        (fun f => reflectAfter f (r (firstPassageGridCeiling N r a f))) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  let u : Fin (N + 1) → C(ℝ≥0, ℝ) → Bool :=
    fun i f => if firstPassageBelow f a ≤ r i then true else false
  have hum (i : Fin (N + 1)) : StronglyMeasurable (u i) := by
    have hset : MeasurableSet {f : C(ℝ≥0, ℝ) |
        firstPassageBelow f a ≤ r i} :=
      (measurable_firstPassageBelow a) measurableSet_Iic
    exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable
  let ℱ := Filtration.natural u hum
  have hu : Adapted ℱ u := (Filtration.stronglyAdapted_natural hum).adapted
  have hτ : IsStoppingTime ℱ
      (fun f : C(ℝ≥0, ℝ) =>
        (firstPassageGridCeiling N r a f : WithTop (Fin (N + 1)))) := by
    exact hu.isStoppingTime_hittingBtwn (measurableSet_singleton true)
  have hfiber (i : Fin (N + 1)) :
      MeasurableSet {f : C(ℝ≥0, ℝ) | firstPassageGridCeiling N r a f = i} := by
    have hi : MeasurableSet[ℱ i] {f : C(ℝ≥0, ℝ) |
        firstPassageGridCeiling N r a f = i} := by
      simpa using hτ.measurableSet_eq i
    exact (ℱ.le i) _ hi
  have hT : Measurable (firstPassageGridCeiling N r a) := by
    intro s hs
    have heq : (firstPassageGridCeiling N r a) ⁻¹' s =
        ⋃ i : s, {f : C(ℝ≥0, ℝ) | firstPassageGridCeiling N r a f = i} := by
      ext f
      simp
    rw [heq]
    exact MeasurableSet.iUnion (fun i => hfiber i)
  have hlocal (i : Fin (N + 1)) (f g : C(ℝ≥0, ℝ))
      (hprefix : ∀ v : ℝ≥0, v ≤ r i → f v = g v) :
      firstPassageGridCeiling N r a f = i ↔
        firstPassageGridCeiling N r a g = i := by
    have hi : MeasurableSet[ℱ i] {p : C(ℝ≥0, ℝ) |
        firstPassageGridCeiling N r a p = i} := by
      simpa using hτ.measurableSet_eq i
    rw [Filtration.natural_eq_comap u hum i] at hi
    obtain ⟨E, hE, hEeq⟩ := (MeasurableSpace.measurableSet_comap).mp hi
    have hupast : (fun j : Set.Iic i => u j f) =
        (fun j : Set.Iic i => u j g) := by
      funext j
      have hprefix_j (v : ℝ≥0) (hv : v ≤ r j) : f v = g v :=
        hprefix v (hv.trans (hr j.2))
      have hpassage := firstPassageBelow_le_congr_of_agreeOn
        f g a (r j) hprefix_j
      change (if firstPassageBelow f a ≤ r j then true else false) =
        (if firstPassageBelow g a ≤ r j then true else false)
      exact ite_congr (propext hpassage) (fun _ => rfl) (fun _ => rfl)
    change f ∈ {p : C(ℝ≥0, ℝ) | firstPassageGridCeiling N r a p = i} ↔
      g ∈ {p : C(ℝ≥0, ℝ) | firstPassageGridCeiling N r a p = i}
    rw [← hEeq]
    simpa only [Set.mem_preimage] using (congrArg (· ∈ E) hupast).to_iff
  exact hB.measure_reflectAfter_finitePathwiseStoppingTime_eq
    hBmeasurable (firstPassageGridCeiling N r a) r hT hlocal

end ProbabilityTheory

end
