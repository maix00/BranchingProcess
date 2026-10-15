/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Independence.FiniteStoppingTime

/-!
# Independence of a Brownian stopped past and future

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.indepFun_shiftToZero_freezeAfter_finiteStoppingTime`:
  for a finite-valued stopping time $T$, the path
  $u\mapsto B(T+u)-B(T)$ is independent of
  $u\mapsto B(\min(u,T))$.
- `ProbabilityTheory.IsBrownianReal.indepFun_shiftToZero_freezeAfter_finitePathwiseStoppingTime`:
  the same conclusion when the stop is given by a measurable pathwise
  selector whose fibers depend only on the past.

This is the finite-valued strong-Markov step behind the Lévy
decomposition cited in Erwin Bolthausen, *On a functional central
limit theorem for random walks conditioned to stay positive*,
Lemma 2.3, equation (2.2), Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098, referring to Kiyosi Itô and Henry P.
McKean, *Diffusion Processes and Their Sample Paths* (1965), §1.7.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The future path and stopped past are independent at a finite-valued
stopping time whose fibers depend only on the relevant past. -/
theorem IsBrownianReal.indepFun_shiftToZero_freezeAfter_finiteStoppingTime
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
    (fun ω => shiftToZero (hB.continuousPathMap hBmeasurable ω)
      (r (T (hB.continuousPathMap hBmeasurable ω)))) ⟂ᵢ[P]
    (fun ω => freezeAfter (hB.continuousPathMap hBmeasurable ω)
      (r (T (hB.continuousPathMap hBmeasurable ω)))) := by
  classical
  let pathB := hB.continuousPathMap hBmeasurable
  let μ := P.map pathB
  let F : Ω → C(ℝ≥0, ℝ) := fun ω => shiftToZero (pathB ω) (r (T (pathB ω)))
  let G : Ω → C(ℝ≥0, ℝ) := fun ω => freezeAfter (pathB ω) (r (T (pathB ω)))
  have hpathB : Measurable pathB := hB.measurable_continuousPathMap hBmeasurable
  have hfiber (i : ι) : MeasurableSet {f : C(ℝ≥0, ℝ) | T f = i} := by
    obtain ⟨s, hs, heq⟩ := (MeasurableSpace.measurableSet_comap).mp (hstop i)
    rw [← heq]
    exact (measurable_freezeAfter (r i)) hs
  have hT : Measurable T := by
    intro s hs
    have heq : T ⁻¹' s = ⋃ i : s, {f : C(ℝ≥0, ℝ) | T f = i} := by
      ext f
      simp
    rw [heq]
    exact MeasurableSet.iUnion (fun i => hfiber i)
  have htime : Measurable (fun ω => r (T (pathB ω))) :=
    (measurable_of_finite r).comp (hT.comp hpathB)
  have hF : Measurable F := measurable_shiftToZero.comp (hpathB.prodMk htime)
  have hG : Measurable G := measurable_freezeAfter_pair.comp (hpathB.prodMk htime)
  have hfuture : P.map F = μ :=
    hB.measure_shiftToZero_finiteStoppingTime_eq hBmeasurable T r hstop
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
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A C hA hC
  have hterm (i : ι) :
      P ((F ⁻¹' A ∩ G ⁻¹' C) ∩ {ω | T (pathB ω) = i}) =
        μ A * P (G ⁻¹' C ∩ {ω | T (pathB ω) = i}) := by
    obtain ⟨s, hs, heq⟩ := (MeasurableSpace.measurableSet_comap).mp (hstop i)
    let Fᵢ : Ω → C(ℝ≥0, ℝ) := fun ω => shiftToZero (pathB ω) (r i)
    let Gᵢ : Ω → C(ℝ≥0, ℝ) := fun ω => freezeAfter (pathB ω) (r i)
    have hfiberSet : {ω | T (pathB ω) = i} = Gᵢ ⁻¹' s := by
      ext ω
      change pathB ω ∈ {f | T f = i} ↔ Gᵢ ω ∈ s
      rw [← heq]
      rfl
    have hleft : (F ⁻¹' A ∩ G ⁻¹' C) ∩ {ω | T (pathB ω) = i} =
        Fᵢ ⁻¹' A ∩ Gᵢ ⁻¹' (C ∩ s) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨⟨hFA, hGC⟩, hTi⟩
        change T (pathB ω) = i at hTi
        have hsω : Gᵢ ω ∈ s :=
          (show ω ∈ Gᵢ ⁻¹' s from hfiberSet ▸ hTi)
        exact ⟨by simpa [F, Fᵢ, hTi] using hFA,
          ⟨by simpa [G, Gᵢ, hTi] using hGC, hsω⟩⟩
      · rintro ⟨hFiA, ⟨hGiC, hGiS⟩⟩
        have hTi : T (pathB ω) = i := by
          exact (show ω ∈ {ω | T (pathB ω) = i} from
            hfiberSet.symm ▸ (show ω ∈ Gᵢ ⁻¹' s from hGiS))
        exact ⟨⟨by simpa [F, Fᵢ, hTi] using hFiA,
          by simpa [G, Gᵢ, hTi] using hGiC⟩, hTi⟩
    have hright : G ⁻¹' C ∩ {ω | T (pathB ω) = i} =
        Gᵢ ⁻¹' (C ∩ s) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hGC, hTi⟩
        change T (pathB ω) = i at hTi
        have hsω : Gᵢ ω ∈ s :=
          (show ω ∈ Gᵢ ⁻¹' s from hfiberSet ▸ hTi)
        exact ⟨by simpa [G, Gᵢ, hTi] using hGC, hsω⟩
      · rintro ⟨hGiC, hGiS⟩
        have hTi : T (pathB ω) = i := by
          exact (show ω ∈ {ω | T (pathB ω) = i} from
            hfiberSet.symm ▸ (show ω ∈ Gᵢ ⁻¹' s from hGiS))
        exact ⟨by simpa [G, Gᵢ, hTi] using hGiC, hTi⟩
    rw [hleft, hright]
    have hind := hB.indepFun_shiftToZero_freezeAfter hBmeasurable (r i)
    have hmul := hind.measure_inter_preimage_eq_mul A (C ∩ s) hA (hC.inter hs)
    rw [hmul]
    have hmap : P (Fᵢ ⁻¹' A) = μ A := by
      calc
        P (Fᵢ ⁻¹' A) = (P.map Fᵢ) A :=
          (Measure.map_apply
            (measurable_shiftToZero.comp (hpathB.prodMk measurable_const)) hA).symm
        _ = μ A := by rw [hB.measure_shiftToZero_eq hBmeasurable (r i)]
    rw [hmap]
  have hFprob : P (F ⁻¹' A) = μ A := by
    calc
      P (F ⁻¹' A) = (P.map F) A := (Measure.map_apply hF hA).symm
      _ = μ A := by rw [hfuture]
  rw [hsplit _ ((hF hA).inter (hG hC)), hsplit _ (hG hC), hFprob]
  calc
    (∑ i : ι, P ((F ⁻¹' A ∩ G ⁻¹' C) ∩ {ω | T (pathB ω) = i})) =
        ∑ i : ι, μ A * P (G ⁻¹' C ∩ {ω | T (pathB ω) = i}) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = μ A * ∑ i : ι, P (G ⁻¹' C ∩ {ω | T (pathB ω) = i}) := by
      rw [Finset.mul_sum]

/-- A measurable finite-valued pathwise stopping selector has independent
stopped past and future increment path. -/
theorem IsBrownianReal.indepFun_shiftToZero_freezeAfter_finitePathwiseStoppingTime
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u))
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype ι] [DecidableEq ι]
    (T : C(ℝ≥0, ℝ) → ι) (r : ι → ℝ≥0)
    (hT : Measurable T)
    (hlocal : ∀ i f g, (∀ u, u ≤ r i → f u = g u) →
      (T f = i ↔ T g = i)) :
    (fun ω => shiftToZero (hB.continuousPathMap hBmeasurable ω)
      (r (T (hB.continuousPathMap hBmeasurable ω)))) ⟂ᵢ[P]
    (fun ω => freezeAfter (hB.continuousPathMap hBmeasurable ω)
      (r (T (hB.continuousPathMap hBmeasurable ω)))) := by
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
  exact hB.indepFun_shiftToZero_freezeAfter_finiteStoppingTime
    hBmeasurable T r hstop

end ProbabilityTheory

end
