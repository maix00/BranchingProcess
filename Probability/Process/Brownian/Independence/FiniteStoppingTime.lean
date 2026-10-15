/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Independence.PastFuturePaths

/-!
# Brownian future path at a finite-valued stopping time

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.measure_shiftToZero_finiteStoppingTime_eq`:
  if a finite-valued pathwise stopping time $T$ has fibers determined by
  the Brownian past, the future increment path
  $u\mapsto B(T+u)-B(T)$ has the original Brownian path law.
- `ProbabilityTheory.IsBrownianReal.measure_shiftToZero_finitePathwiseStoppingTime_eq`:
  the same law when past dependence is expressed by path agreement on
  $[0,T]$.

This is the finite-valued approximation to the strong Markov property
used to identify the descending first-passage process in the Lévy
decomposition cited in Erwin Bolthausen, *On a functional central limit
theorem for random walks conditioned to stay positive*, Lemma 2.3,
equation (2.2), Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098, referring to Kiyosi Itô and Henry P.
McKean, *Diffusion Processes and Their Sample Paths* (1965), §1.7.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- A finite-valued stopping time has a Brownian future increment path
with the original Brownian path law. The stopping-time hypothesis is
measurability of each time fiber with respect to its frozen past path. -/
theorem IsBrownianReal.measure_shiftToZero_finiteStoppingTime_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype ι] [DecidableEq ι]
    (T : C(ℝ≥0, ℝ) → ι) (r : ι → ℝ≥0)
    (hstop : ∀ i,
      MeasurableSet[MeasurableSpace.comap
        (fun f : C(ℝ≥0, ℝ) => freezeAfter f (r i)) inferInstance]
        {f | T f = i}) :
    P.map (fun ω => shiftToZero (hB.continuousPathMap hBmeasurable ω)
      (r (T (hB.continuousPathMap hBmeasurable ω)))) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  classical
  let pathB := hB.continuousPathMap hBmeasurable
  let μ := P.map pathB
  have hpathB : Measurable pathB := hB.measurable_continuousPathMap hBmeasurable
  have hprob : IsProbabilityMeasure P :=
    (hB.toIsPreBrownianReal.hasLaw ∅).isProbabilityMeasure
  letI : IsProbabilityMeasure P := hprob
  have hfiber (i : ι) : MeasurableSet {f : C(ℝ≥0, ℝ) | T f = i} := by
    obtain ⟨s, hs, heq⟩ :=
      (MeasurableSpace.measurableSet_comap).mp (hstop i)
    rw [← heq]
    exact (measurable_freezeAfter (r i)) hs
  have hT : Measurable T := by
    intro s hs
    have heq : T ⁻¹' s = ⋃ i : s, {f : C(ℝ≥0, ℝ) | T f = i} := by
      ext f
      simp
    rw [heq]
    exact MeasurableSet.iUnion (fun i => hfiber i)
  have hF : Measurable (fun ω => shiftToZero (pathB ω) (r (T (pathB ω)))) := by
    exact measurable_shiftToZero.comp
      (hpathB.prodMk ((measurable_of_finite r).comp (hT.comp hpathB)))
  have hfuture (i : ι) :
      P.map (fun ω => shiftToZero (pathB ω) (r i)) = μ :=
    hB.measure_shiftToZero_eq hBmeasurable (r i)
  have hind (i : ι) :
      (fun ω => shiftToZero (pathB ω) (r i)) ⟂ᵢ[P]
        (fun ω => freezeAfter (pathB ω) (r i)) :=
    hB.indepFun_shiftToZero_freezeAfter hBmeasurable (r i)
  have hsplit (s : Set Ω) (hs : MeasurableSet s) :
      P s = ∑ i : ι, P (s ∩ {ω | T (pathB ω) = i}) := by
    have hcover : (⋃ i ∈ Finset.univ, s ∩ {ω | T (pathB ω) = i}) = s := by
      ext ω
      simp
    calc
      P s = P (⋃ i ∈ Finset.univ, s ∩ {ω | T (pathB ω) = i}) := by rw [hcover]
      _ = ∑ i, P (s ∩ {ω | T (pathB ω) = i}) := by
        exact measure_biUnion_finset
          (fun i _ j _ hij =>
            Disjoint.inter_left' _ (Disjoint.inter_right' _
              (Set.disjoint_left.mpr (by
                intro ω hωi hωj
                exact hij (hωi.symm.trans hωj)))))
          (fun i _ => hs.inter ((hT.comp hpathB) (measurableSet_singleton i)))
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hF hA]
  rw [hsplit _ (hF hA)]
  have hterm (i : ι) :
      P ({ω | shiftToZero (pathB ω) (r (T (pathB ω))) ∈ A} ∩
        {ω | T (pathB ω) = i}) =
      μ A * P {ω | T (pathB ω) = i} := by
    obtain ⟨s, hs, heq⟩ :=
      (MeasurableSpace.measurableSet_comap).mp (hstop i)
    have hset : {ω | T (pathB ω) = i} =
        (fun ω => freezeAfter (pathB ω) (r i)) ⁻¹' s := by
      ext ω
      change pathB ω ∈ {f | T f = i} ↔
        freezeAfter (pathB ω) (r i) ∈ s
      rw [← heq]
      rfl
    have hleft :
        P ({ω | shiftToZero (pathB ω) (r (T (pathB ω))) ∈ A} ∩
          {ω | T (pathB ω) = i}) =
        P ((fun ω => shiftToZero (pathB ω) (r i)) ⁻¹' A ∩
          {ω | T (pathB ω) = i}) := by
      congr 1
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · rintro ⟨hAω, hTi⟩
        exact ⟨by simpa [hTi] using hAω, hTi⟩
      · rintro ⟨hAω, hTi⟩
        exact ⟨by simpa [hTi] using hAω, hTi⟩
    rw [hleft, hset]
    have hmul := (hind i).measure_inter_preimage_eq_mul A s hA hs
    rw [hmul]
    have hmap :
        P ((fun ω => shiftToZero (pathB ω) (r i)) ⁻¹' A) = μ A := by
      calc
        P ((fun ω => shiftToZero (pathB ω) (r i)) ⁻¹' A) =
            (P.map (fun ω => shiftToZero (pathB ω) (r i))) A :=
          (Measure.map_apply (measurable_shiftToZero.comp
            (hpathB.prodMk measurable_const)) hA).symm
        _ = μ A := by rw [hfuture i]
    rw [hmap]
  calc
    (∑ i : ι, P ({ω | shiftToZero (pathB ω) (r (T (pathB ω))) ∈ A} ∩
      {ω | T (pathB ω) = i})) =
        ∑ i : ι, μ A * P {ω | T (pathB ω) = i} := by
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = μ A * ∑ i : ι, P {ω | T (pathB ω) = i} := by rw [Finset.mul_sum]
    _ = μ A := by
      have hsum := hsplit Set.univ MeasurableSet.univ
      simp only [Set.univ_inter] at hsum
      rw [measure_univ] at hsum
      rw [← hsum, mul_one]

/-- Finite-valued pathwise stopping times can be specified by a
measurable selector whose fibers are unchanged by alterations after
the selected time. -/
theorem IsBrownianReal.measure_shiftToZero_finitePathwiseStoppingTime_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype ι] [DecidableEq ι]
    (T : C(ℝ≥0, ℝ) → ι) (r : ι → ℝ≥0)
    (hT : Measurable T)
    (hlocal : ∀ i f g, (∀ u, u ≤ r i → f u = g u) →
      (T f = i ↔ T g = i)) :
    P.map (fun ω => shiftToZero (hB.continuousPathMap hBmeasurable ω)
      (r (T (hB.continuousPathMap hBmeasurable ω)))) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  have hstop (i : ι) :
      MeasurableSet[MeasurableSpace.comap
        (fun f : C(ℝ≥0, ℝ) => freezeAfter f (r i)) inferInstance]
        {f | T f = i} := by
    apply (MeasurableSpace.measurableSet_comap).mpr
    refine ⟨{f | T f = i}, hT (measurableSet_singleton i), ?_⟩
    ext f
    change T (freezeAfter f (r i)) = i ↔ T f = i
    apply hlocal i (freezeAfter f (r i)) f
    intro u hu
    change f (min u (r i)) = f u
    rw [min_eq_left hu]
  exact hB.measure_shiftToZero_finiteStoppingTime_eq hBmeasurable T r hstop

end ProbabilityTheory

end
