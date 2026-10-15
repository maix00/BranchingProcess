/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.Basic

public section

/-!
# Measurable mappings under convergence in distribution

The public theorems in this file are:

- `MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuousAt_ae`:
  $\mu_n\Rightarrow\mu$ and $\mu$-almost-sure continuity of a measurable
  map $f$ imply $f_*\mu_n\Rightarrow f_*\mu$.
- `MeasureTheory.TendstoInDistribution.measurable_comp_of_continuousAt_ae`:
  the corresponding random-variable form,
  $X_n\Rightarrow X\Rightarrow f(X_n)\Rightarrow f(X)$.

The proof uses the open-set form of the Portmanteau theorem. The
random-variable form is used for the first-window path shift in
Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Theorem 3.2, Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098.
-/

open Filter MeasureTheory Set Topology
open scoped Topology

namespace MeasureTheory

/-- Pushforward preserves weak convergence when the measurable map is
continuous almost everywhere for the limiting probability measure. -/
theorem ProbabilityMeasure.tendsto_map_of_tendsto_of_continuousAt_ae
    {Ω Ω' I : Type*}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω]
    [MeasurableSpace Ω'] [TopologicalSpace Ω'] [OpensMeasurableSpace Ω']
    [HasOuterApproxClosed Ω']
    {L : Filter I} [L.IsCountablyGenerated]
    {μ : ProbabilityMeasure Ω} {μs : I → ProbabilityMeasure Ω}
    (hμ : Tendsto μs L (𝓝 μ))
    {f : Ω → Ω'} (hf : Measurable f)
    (hcont : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt f x) :
    Tendsto (fun i => (μs i).map f) L (𝓝 (μ.map f)) := by
  obtain rfl | hL := L.eq_or_neBot
  · simp
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  let V : Set Ω := f ⁻¹' G
  let U : Set Ω := interior V
  have hUopen : IsOpen U := isOpen_interior
  have hUV : V =ᵐ[(μ : Measure Ω)] U := by
    filter_upwards [hcont] with x hx
    apply propext
    constructor
    · intro hxG
      rw [mem_interior_iff_mem_nhds]
      exact hx.preimage_mem_nhds (hG.mem_nhds hxG)
    · intro hxU
      exact interior_subset hxU
  have hmeasure : (μ : Measure Ω) V = (μ : Measure Ω) U :=
    measure_congr hUV
  have hsource :=
    ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hUopen
  calc
    ((μ.map f : ProbabilityMeasure Ω') : Measure Ω') G =
        (μ : Measure Ω) V := by
      exact ProbabilityMeasure.map_apply' μ hf.aemeasurable hG.measurableSet
    _ = (μ : Measure Ω) U := hmeasure
    _ ≤ L.liminf (fun i => ((μs i : ProbabilityMeasure Ω) : Measure Ω) U) :=
      hsource
    _ ≤ L.liminf (fun i =>
        (((μs i).map f : ProbabilityMeasure Ω') : Measure Ω') G) := by
      have hcomp : ∀ᶠ i in L,
          ((μs i : ProbabilityMeasure Ω) : Measure Ω) U ≤
            (((μs i).map f : ProbabilityMeasure Ω') : Measure Ω') G := by
        filter_upwards [] with i
        calc
          ((μs i : ProbabilityMeasure Ω) : Measure Ω) U ≤
              ((μs i : ProbabilityMeasure Ω) : Measure Ω) V :=
            measure_mono interior_subset
          _ = (((μs i).map f : ProbabilityMeasure Ω') : Measure Ω') G := by
            symm
            exact ProbabilityMeasure.map_apply' (μs i) hf.aemeasurable hG.measurableSet
      have hsource_lb : IsBoundedUnder (fun x y : ENNReal => y ≤ x) L
          (fun i => ((μs i : ProbabilityMeasure Ω) : Measure Ω) U) :=
        isBoundedUnder_of ⟨0, fun _ => bot_le⟩
      have htarget_le_one (i : I) :
          (((μs i).map f : ProbabilityMeasure Ω') : Measure Ω') G ≤ 1 := by
        calc
          (((μs i).map f : ProbabilityMeasure Ω') : Measure Ω') G ≤
              (((μs i).map f : ProbabilityMeasure Ω') : Measure Ω') Set.univ :=
            measure_mono (subset_univ _)
          _ = 1 := measure_univ
      have htarget_ub : IsCoboundedUnder (fun x y : ENNReal => y ≤ x) L
          (fun i => (((μs i).map f : ProbabilityMeasure Ω') : Measure Ω') G) := by
        exact (isBoundedUnder_of_eventually_le <|
          Filter.Eventually.of_forall htarget_le_one).isCoboundedUnder_ge
      exact Filter.liminf_le_liminf hcomp hsource_lb htarget_ub

set_option backward.isDefEq.respectTransparency.types false in
/-- The continuous mapping theorem for a measurable map which is
continuous almost surely under the limiting law. -/
theorem TendstoInDistribution.measurable_comp_of_continuousAt_ae
    {I : Type*} {Ω : I → Type*} {Ω' E F : Type*}
    [∀ i, MeasurableSpace (Ω i)] [MeasurableSpace Ω']
    [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [HasOuterApproxClosed E]
    [MeasurableSpace F] [TopologicalSpace F]
    [OpensMeasurableSpace F] [HasOuterApproxClosed F]
    {L : Filter I} [L.IsCountablyGenerated]
    {μ : (i : I) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {X : (i : I) → Ω i → E} {Z : Ω' → E}
    (h : TendstoInDistribution X L Z μ μ')
    {g : E → F} (hg : Measurable g)
    (hcont : ∀ᵐ x ∂(μ'.map Z), ContinuousAt g x) :
    TendstoInDistribution (fun i => g ∘ X i) L (g ∘ Z) μ μ' where
  forall_aemeasurable := fun i =>
    hg.aemeasurable.comp_aemeasurable (h.forall_aemeasurable i)
  aemeasurable_limit :=
    hg.aemeasurable.comp_aemeasurable h.aemeasurable_limit
  tendsto := by
    convert! ProbabilityMeasure.tendsto_map_of_tendsto_of_continuousAt_ae
      h.tendsto hg hcont using 1
    · congr 1
      funext i
      apply Subtype.ext
      exact (AEMeasurable.map_map_of_aemeasurable
        hg.aemeasurable (h.forall_aemeasurable i)).symm
    · congr 1
      apply Subtype.ext
      exact (AEMeasurable.map_map_of_aemeasurable
        hg.aemeasurable h.aemeasurable_limit).symm

end MeasureTheory

end
