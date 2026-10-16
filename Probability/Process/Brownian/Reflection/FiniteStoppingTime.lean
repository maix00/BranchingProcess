/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Reflection.Deterministic
public import Mathlib.MeasureTheory.Measure.Basic

/-!
# Reflection at a finite-valued Brownian stopping time

The public theorems in this file are:

- `ProbabilityTheory.IsBrownianReal.measure_reflectAfter_finitePathwiseStoppingTime_eq`:
  a measurable, finite-valued pathwise stopping time preserves Brownian
  path law under reflection.
- `ProbabilityTheory.IsBrownianReal.measure_reflectAfter_finiteStoppingTime_eq`:
  for a finite-valued stopping time $T$ whose fibers are measurable with
  respect to the past path, reflection of a Brownian path after $T$
  preserves its law on $C([0,\infty),\mathbb R)$.

The finite-valued stopping-time step is part of Theorem 2.1 of S. J.
Dilworth and Duncan Wright, *A direct proof of the reflection principle
for Brownian motion*, Theory Stoch. Process. 21(37):2 (2016), 1--3,
arXiv:1810.01783.
That reflection principle supplies the running-minimum identity cited in
Lemma 2.3 of Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976),
480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

private theorem measure_piecewise_reflection_eq
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype ι] [DecidableEq ι]
    (μ : Measure C(ℝ≥0, ℝ))
    (T : C(ℝ≥0, ℝ) → ι) (r : ι → ℝ≥0)
    (hT : Measurable T)
    (hlocal : ∀ i f g, (∀ u, u ≤ r i → f u = g u) → (T f = i ↔ T g = i))
    (hinvariant : ∀ i, μ.map (fun f => reflectAfter f (r i)) = μ) :
    μ.map (fun f => reflectAfter f (r (T f))) = μ := by
  classical
  let R (i : ι) : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) :=
    fun f => reflectAfter f (r i)
  have hR (i : ι) : Measurable (R i) := measurable_reflectAfter _
  have hfiber (i : ι) : MeasurableSet {f : C(ℝ≥0, ℝ) | T f = i} :=
    hT (measurableSet_singleton i)
  have hTreflect (i : ι) (f : C(ℝ≥0, ℝ)) : T (R i f) = i ↔ T f = i := by
    apply (hlocal i (R i f) f _)
    intro u hu
    exact reflectAfter_apply_le f (r i) u hu
  have hF : Measurable (fun f => reflectAfter f (r (T f))) := by
    exact measurable_reflectAfter_pair.comp
      (measurable_id.prodMk ((measurable_of_finite r).comp hT))
  have hsplit (s : Set C(ℝ≥0, ℝ)) (hs : MeasurableSet s) :
      μ s = ∑ i, μ (s ∩ {f | T f = i}) := by
    have hcover : (⋃ i ∈ Finset.univ, s ∩ {f | T f = i}) = s := by
      ext f
      simp
    calc
      μ s = μ (⋃ i ∈ Finset.univ, s ∩ {f | T f = i}) := by rw [hcover]
      _ = ∑ i, μ (s ∩ {f | T f = i}) := by
        exact measure_biUnion_finset
          (fun i _ j _ hij =>
            Disjoint.inter_left' _ (Disjoint.inter_right' _
              (Set.disjoint_left.mpr (by
                intro f hfi hfj
                exact hij (hfi.symm.trans hfj)))))
          (fun i _ => hs.inter (hfiber i))
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply hF hA]
  rw [hsplit _ (hF hA), hsplit A hA]
  apply Finset.sum_congr rfl
  intro i _
  have hset :
      (fun f : C(ℝ≥0, ℝ) => reflectAfter f (r (T f))) ⁻¹' A ∩ {f | T f = i} =
        R i ⁻¹' (A ∩ {f | T f = i}) := by
    ext f
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hfA, hfi⟩
      rw [hfi] at hfA
      exact ⟨hfA, (hTreflect i f).2 hfi⟩
    · rintro ⟨hfA, hfi⟩
      have hfi' := (hTreflect i f).1 hfi
      exact ⟨by simpa [R, hfi'] using hfA, hfi'⟩
  rw [hset, ← Measure.map_apply (hR i) (hA.inter (hfiber i)), hinvariant i]

/-- Reflection after a measurable finite-valued pathwise stopping time
preserves Brownian path law. The fiber $T=i$ is unchanged when the path
is changed after $r_i$. This is the finite-valued stopping-time step of
Theorem 2.1 in S. J. Dilworth and Duncan Wright, *A direct proof of the
reflection principle for Brownian motion*, arXiv:1810.01783. -/
theorem IsBrownianReal.measure_reflectAfter_finitePathwiseStoppingTime_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype ι] [DecidableEq ι]
    (T : C(ℝ≥0, ℝ) → ι) (r : ι → ℝ≥0)
    (hT : Measurable T)
    (hlocal : ∀ i f g, (∀ u, u ≤ r i → f u = g u) → (T f = i ↔ T g = i)) :
    (P.map (hB.continuousPathMap hBmeasurable)).map
        (fun f => reflectAfter f (r (T f))) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  apply measure_piecewise_reflection_eq μ T r hT hlocal
  intro i
  rw [Measure.map_map (measurable_reflectAfter _) (hB.measurable_continuousPathMap _)]
  exact hB.measure_reflectAfter_continuousPathMap_eq hBmeasurable (r i)

/-- Reflection after a finite-valued stopping time preserves Brownian
path law. The stopping-time condition says that the event $T=i$ is
measurable with respect to the path through the associated time $r_i$.
This is the finite-valued stopping-time step of Theorem 2.1 in S. J.
Dilworth and Duncan Wright, *A direct proof of the reflection principle
for Brownian motion*, arXiv:1810.01783. -/
theorem IsBrownianReal.measure_reflectAfter_finiteStoppingTime_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ t, Measurable (B t))
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [Fintype ι] [DecidableEq ι]
    (T : C(ℝ≥0, ℝ) → ι) (r : ι → ℝ≥0)
    (hstop : ∀ i,
      MeasurableSet[MeasurableSpace.comap
        (fun f : C(ℝ≥0, ℝ) => fun u : Set.Iic (r i) => f u) inferInstance]
        {f | T f = i}) :
    (P.map (hB.continuousPathMap hBmeasurable)).map
        (fun f => reflectAfter f (r (T f))) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  have hpast (i : ι) :
      Measurable (fun f : C(ℝ≥0, ℝ) => fun u : Set.Iic (r i) => f u) := by
    rw [measurable_pi_iff]
    intro u
    exact ContinuousMap.measurable_eval (u : ℝ≥0)
  have hfiber (i : ι) : MeasurableSet {f : C(ℝ≥0, ℝ) | T f = i} := by
    obtain ⟨s, hs, heq⟩ := (MeasurableSpace.measurableSet_comap).mp (hstop i)
    rw [← heq]
    exact (hpast i) hs
  have hT : Measurable T := by
    intro s hs
    have heq : T ⁻¹' s = ⋃ i : s, {f : C(ℝ≥0, ℝ) | T f = i} := by
      ext f
      simp
    rw [heq]
    exact MeasurableSet.iUnion (fun i => hfiber i)
  have hlocal (i : ι) (f g : C(ℝ≥0, ℝ))
      (hprefix : ∀ u, u ≤ r i → f u = g u) : T f = i ↔ T g = i := by
    obtain ⟨s, hs, heq⟩ := (MeasurableSpace.measurableSet_comap).mp (hstop i)
    have hp : (fun u : Set.Iic (r i) => f u) =
        (fun u : Set.Iic (r i) => g u) := by
      funext u
      exact hprefix u u.2
    change f ∈ {f : C(ℝ≥0, ℝ) | T f = i} ↔
      g ∈ {f : C(ℝ≥0, ℝ) | T f = i}
    rw [← heq]
    simpa only [Set.mem_preimage] using (congrArg (· ∈ s) hp).to_iff
  exact hB.measure_reflectAfter_finitePathwiseStoppingTime_eq
    hBmeasurable T r hT hlocal

end ProbabilityTheory

end
