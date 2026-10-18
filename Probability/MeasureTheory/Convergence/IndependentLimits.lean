/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.Probability.Independence.Basic

/-!
# Independence in weak limits

The public theorem in this file is:

- `ProbabilityTheory.indepFun_of_tendstoInDistribution_pair`: if each pair
  $(X_i,Y_i)$ has independent coordinates and the pair converges in
  distribution to $(X,Y)$, then $X$ and $Y$ are independent.

The theorem allows the source probability space and its law to vary with the
index. Its proof uses the continuity of products of probability measures and
the characterization of independence by the joint law.
-/

@[expose] public section

open Filter MeasureTheory TopologicalSpace

namespace ProbabilityTheory

/-- Independence of each pair is preserved when the joint laws converge in
distribution. The source probability spaces may depend on the index. -/
theorem indepFun_of_tendstoInDistribution_pair
    {ι : Type*} {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [PseudoMetrizableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] [PseudoMetrizableSpace Y]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {μ : ∀ i, Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {l : Filter ι} [l.NeBot]
    (F : ∀ i, Ω i → X) (G : ∀ i, Ω i → Y)
    (F' : Ω' → X) (G' : Ω' → Y)
    (hlimit : MeasureTheory.TendstoInDistribution
      (fun i ω => (F i ω, G i ω)) l (fun ω => (F' ω, G' ω)) μ μ')
    (hind : ∀ i, F i ⟂ᵢ[μ i] G i) :
    F' ⟂ᵢ[μ'] G' := by
  have hFdist : MeasureTheory.TendstoInDistribution F l F' μ μ' := by
    simpa only [Function.comp_def] using
      hlimit.continuous_comp (g := Prod.fst) continuous_fst
  have hGdist : MeasureTheory.TendstoInDistribution G l G' μ μ' := by
    simpa only [Function.comp_def] using
      hlimit.continuous_comp (g := Prod.snd) continuous_snd
  have hproducts : Tendsto
      (fun i =>
        ProbabilityMeasure.prod
          (⟨(μ i).map (F i), inferInstance⟩ : ProbabilityMeasure X)
          (⟨(μ i).map (G i), inferInstance⟩ : ProbabilityMeasure Y))
      l
      (nhds
        (ProbabilityMeasure.prod
          (⟨μ'.map F', inferInstance⟩ : ProbabilityMeasure X)
          (⟨μ'.map G', inferInstance⟩ : ProbabilityMeasure Y))) := by
    exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
      (hFdist.tendsto.prodMk_nhds hGdist.tendsto)
  have hjoint_eq (i : ι) :
      (⟨(μ i).map (fun ω => (F i ω, G i ω)), inferInstance⟩ :
        ProbabilityMeasure (X × Y)) =
      ProbabilityMeasure.prod
        (⟨(μ i).map (F i), inferInstance⟩ : ProbabilityMeasure X)
        (⟨(μ i).map (G i), inferInstance⟩ : ProbabilityMeasure Y) := by
    apply Subtype.ext
    exact (indepFun_iff_map_prod_eq_prod_map_map
      (measurable_fst.comp_aemeasurable (hlimit.forall_aemeasurable i))
      (measurable_snd.comp_aemeasurable (hlimit.forall_aemeasurable i))).mp (hind i)
  have hjoint_limit :
      (⟨μ'.map (fun ω => (F' ω, G' ω)), inferInstance⟩ :
        ProbabilityMeasure (X × Y)) =
      ProbabilityMeasure.prod
        (⟨μ'.map F', inferInstance⟩ : ProbabilityMeasure X)
        (⟨μ'.map G', inferInstance⟩ : ProbabilityMeasure Y) := by
    apply tendsto_nhds_unique hlimit.tendsto
    simpa only [hjoint_eq] using hproducts
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_fst.comp_aemeasurable hlimit.aemeasurable_limit)
    (measurable_snd.comp_aemeasurable hlimit.aemeasurable_limit)).mpr
  exact congrArg ProbabilityMeasure.toMeasure hjoint_limit

end ProbabilityTheory

end
