/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.DescendingHittingTimeLaw
public import Probability.Process.Brownian.Independence.PastFuturePaths
public import Probability.Independence.NullSections

/-!
# Brownian first passage at a past-measurable level

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.measure_randomLevelFirstPassage_eq_zero`:
  for deterministic $q$, let $A$ and $T$ be measurable functions of
  the path stopped at $q$. Then
  $\mathbb P(A>0,\,T>0,\,\tau_A(B_{q+\cdot}-B_q)=T)=0$.

The proof uses independence of the stopped past and future Brownian
path, the atomless fixed-level first-passage law, and Fubini's theorem.
This provides a direct proof of the fixed-excursion-length consequence
of the Lévy decomposition cited by Erwin Bolthausen,
*On a functional central limit theorem for random walks conditioned
to stay positive*, Lemma 2.3, equation (2.2), Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- A future Brownian passage at a positive level and positive time
selected measurably from a deterministic-time stopped past has
probability zero. -/
theorem IsBrownianReal.measure_randomLevelFirstPassage_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (q : ℝ≥0)
    (level target : C(ℝ≥0, ℝ) → ℝ≥0)
    (hlevel : Measurable level) (htarget : Measurable target) :
    let pathB := hB.continuousPathMap hBmeasurable
    let past := fun ω => freezeAfter (pathB ω) q
    let future := fun ω => shiftToZero (pathB ω) q
    P {ω | 0 < level (past ω) ∧ 0 < target (past ω) ∧
      descendingHittingTime (future ω) (level (past ω)) =
        target (past ω)} = 0 := by
  dsimp
  let pathB := hB.continuousPathMap hBmeasurable
  let past : Ω → C(ℝ≥0, ℝ) := fun ω => freezeAfter (pathB ω) q
  let future : Ω → C(ℝ≥0, ℝ) := fun ω => shiftToZero (pathB ω) q
  let E : Set (C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) :=
    {p | 0 < level p.1 ∧ 0 < target p.1 ∧
      descendingHittingTime p.2 (level p.1) = target p.1}
  have hpath : Measurable pathB := hB.measurable_continuousPathMap hBmeasurable
  have hpast : Measurable past := (measurable_freezeAfter q).comp hpath
  have hfuture : Measurable future :=
    measurable_shiftToZero.comp (hpath.prodMk measurable_const)
  have hpassMeas : Measurable (fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      descendingHittingTime p.2 (level p.1)) := by
    exact measurable_firstPassageBelow_pair.comp
      (measurable_snd.prodMk
        ((measurable_subtype_coe.comp (hlevel.comp measurable_fst)).neg))
  have htargetMeas : Measurable
      (fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
        (target p.1 : WithTop ℝ≥0)) := by
    fun_prop
  have hE : MeasurableSet E := by
    exact ((hlevel.comp measurable_fst) measurableSet_Ioi).inter
      (((htarget.comp measurable_fst) measurableSet_Ioi).inter
        (measurableSet_eq_fun hpassMeas htargetMeas))
  haveI : IsProbabilityMeasure P :=
    (hB.toIsPreBrownianReal.hasLaw ∅).isProbabilityMeasure
  have hInd : past ⟂ᵢ[P] future :=
    (hB.indepFun_shiftToZero_freezeAfter hBmeasurable q).symm
  have hfutureLaw : P.map future = P.map pathB :=
    hB.measure_shiftToZero_eq hBmeasurable q
  have hnull (p : C(ℝ≥0, ℝ)) :
      (P.map future) {f : C(ℝ≥0, ℝ) | (p, f) ∈ E} = 0 := by
    by_cases hp : 0 < level p ∧ 0 < target p
    · have hset : {f : C(ℝ≥0, ℝ) | (p, f) ∈ E} =
          {f | descendingHittingTime f (level p) = target p} := by
        ext f
        simp [E, hp.1, hp.2]
      rw [hset, hfutureLaw]
      exact hB.measure_descendingHittingTime_eq_zero
        hBmeasurable hp.2 hp.1
    · have hset : {f : C(ℝ≥0, ℝ) | (p, f) ∈ E} = ∅ := by
        ext f
        change (0 < level p ∧ 0 < target p ∧
          descendingHittingTime f (level p) = target p) ↔ False
        exact iff_false_intro (fun h => hp ⟨h.1, h.2.1⟩)
      simp [hset]
  simpa [E, past, future, pathB] using
    hInd.measure_preimage_eq_zero_of_null_sections hpast hfuture hE hnull

end ProbabilityTheory

end
