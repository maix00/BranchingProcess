/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.DeterministicParameter
public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLimit
public import Topology.Cadlag.Skorokhod.Scaling

/-!
# Functional limits for variable-length blocks

The fixed-horizon path-law limit transfers to variable-length blocks by
combining weak convergence of the base path laws with convergence of the
deterministic normalization ratio. A product with a Dirac law and the
continuous mapping theorem avoid imposing an additive structure on the
Skorokhod `J₁` path space.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

variable {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
  {α : ℝ} {normalization spatialScale : ℕ → ℝ}
  {blockLength : ℕ → ℕ}
  {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]

/-- A fixed-horizon stable path limit transfers to blocks whose length and
spatial normalization vary with the outer parameter. The path-space
implementation uses weak convergence of measures and the continuous product
of probability measures with a Dirac law, so no vector-space structure is
required on the Skorokhod `J₁` path space. -/
theorem tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (htightBase : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))
    (hblock : Tendsto blockLength atTop atTop)
    (hscale : ∀ᶠ n in atTop, 0 < spatialScale n)
    (hnorm : ∀ᶠ n in atTop, 0 < normalization (blockLength n))
    {r : ℝ}
    (hratio : Tendsto
      (fun n => normalization (blockLength n) / spatialScale n)
      atTop (nhds r)) :
    TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc spatialScale blockLength)
      atTop (id : CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ)
      (fun _ => iidSequenceLaw ν)
      (P.map (Skorokhod.scalePath r)) := by
  let factor : ℕ → ℝ := fun n => normalization (blockLength n) / spatialScale n
  let basePath : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ :=
    fun n => RandomWalk.normalizedStepCadlagPathIcc normalization (blockLength n)
  let baseLaw : ℕ → ProbabilityMeasure (CadlagPath unitInterval ℝ) :=
    fun n => ⟨(iidSequenceLaw ν).map (basePath n), inferInstance⟩
  let limitLaw : ProbabilityMeasure (CadlagPath unitInterval ℝ) :=
    ⟨P, inferInstance⟩
  let blockLaw : ℕ → ProbabilityMeasure (CadlagPath unitInterval ℝ) :=
    fun n => ⟨(iidSequenceLaw ν).map
      (RandomWalk.normalizedStepBlockCadlagPathIcc spatialScale blockLength n), inferInstance⟩
  let scalePair : CadlagPath unitInterval ℝ × ℝ → CadlagPath unitInterval ℝ :=
    fun p => Skorokhod.scalePath p.2 p.1

  have hbase : Tendsto baseLaw atTop (nhds limitLaw) := by
    change Tendsto
      (fun n => (⟨RandomWalk.normalizedStepPathLaw ν normalization (blockLength n),
        inferInstance⟩ : ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
        (⟨P, (inferInstance : IsProbabilityMeasure P)⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ)))
    exact (tendsto_normalizedStepPathLaw_of_zeroCenter_stableDomain_of_tight
      hDOA hP htightBase).comp hblock

  have hscalePairContinuous : Continuous scalePair := by
    exact Skorokhod.continuous_scalePath.comp
      (continuous_snd.prodMk continuous_fst)

  have hscaledLaw : Tendsto
      (fun n => ((baseLaw n).prod (MeasureTheory.diracProba (factor n))).map scalePair)
      atTop (nhds ((limitLaw.prod (MeasureTheory.diracProba r)).map scalePair)) :=
    MeasureTheory.ProbabilityMeasure.tendsto_map_prod_dirac_of_tendsto
      baseLaw limitLaw hbase factor r hratio scalePair hscalePairContinuous

  have htarget :
      (limitLaw.prod (MeasureTheory.diracProba r)).map scalePair =
        (⟨P.map (Skorokhod.scalePath r), inferInstance⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ)) := by
    apply Subtype.ext
    change Measure.map scalePair (P.prod (Measure.dirac r)) =
      P.map (Skorokhod.scalePath r)
    calc
      _ = Measure.map scalePair (Measure.map (fun path => (path, r)) P) := by
        rw [Measure.prod_dirac]
      _ = Measure.map (scalePair ∘ fun path => (path, r)) P :=
        Measure.map_map hscalePairContinuous.measurable
          (measurable_id.prodMk measurable_const)
      _ = P.map (Skorokhod.scalePath r) := by
        congr 1

  have hgood : ∀ᶠ n in atTop,
      0 < spatialScale n ∧ 0 < normalization (blockLength n) := hscale.and hnorm
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hgood

  have hpathEq (n : ℕ) (hn : N ≤ n) (ω : ℕ → ℝ) :
      RandomWalk.normalizedStepBlockCadlagPathIcc spatialScale blockLength n ω =
        Skorokhod.scalePath (factor n) (basePath n ω) := by
    apply CadlagPath.ext
    intro t
    simp only [RandomWalk.normalizedStepBlockCadlagPathIcc,
      RandomWalk.normalizedStepCadlagPathIcc_apply, Skorokhod.scalePath_apply,
      basePath, factor, RandomWalk.normalizedStepPath]
    field_simp [ne_of_gt (hN n hn).1, ne_of_gt (hN n hn).2]

  have hbasePathMeasurable (n : ℕ) : Measurable (basePath n) := by
    exact RandomWalk.measurable_normalizedStepCadlagPathIcc normalization (blockLength n)

  have hpairLaw (n : ℕ) :
      (iidSequenceLaw ν).map (fun ω => (basePath n ω, factor n)) =
        ((baseLaw n : ProbabilityMeasure (CadlagPath unitInterval ℝ)) :
          Measure (CadlagPath unitInterval ℝ)).prod (Measure.dirac (factor n)) := by
    calc
      (iidSequenceLaw ν).map (fun ω => (basePath n ω, factor n)) =
          Measure.map (fun path => (path, factor n))
            ((iidSequenceLaw ν).map (basePath n)) := by
        change Measure.map ((fun path : CadlagPath unitInterval ℝ =>
          (path, factor n)) ∘ basePath n) (iidSequenceLaw ν) = _
        exact (Measure.map_map (measurable_id.prodMk measurable_const)
          (hbasePathMeasurable n)).symm
      _ = ((iidSequenceLaw ν).map (basePath n)).prod (Measure.dirac (factor n)) := by
        rw [Measure.prod_dirac]

  have hsource (n : ℕ) (hn : N ≤ n) :
      blockLaw n = ((baseLaw n).prod (MeasureTheory.diracProba (factor n))).map scalePair := by
    apply Subtype.ext
    change (iidSequenceLaw ν).map
        (RandomWalk.normalizedStepBlockCadlagPathIcc spatialScale blockLength n) =
      Measure.map scalePair
        (((iidSequenceLaw ν).map (basePath n)).prod (Measure.dirac (factor n)))
    calc
      _ = (iidSequenceLaw ν).map
          (fun ω => scalePair (basePath n ω, factor n)) := by
        apply Measure.map_congr
        exact ae_of_all _ fun ω => by rw [hpathEq n hn ω]
      _ = Measure.map scalePair
          ((iidSequenceLaw ν).map (fun ω => (basePath n ω, factor n))) := by
        symm
        exact Measure.map_map hscalePairContinuous.measurable
          ((hbasePathMeasurable n).prodMk measurable_const)
      _ = _ := by
        congr 1
        exact hpairLaw n

  have hsourceEventually : ∀ᶠ n in atTop,
      blockLaw n = ((baseLaw n).prod (MeasureTheory.diracProba (factor n))).map scalePair := by
    filter_upwards [Filter.eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    exact hsource n hn

  have hblockLaw : Tendsto blockLaw atTop
      (nhds (⟨P.map (Skorokhod.scalePath r), inferInstance⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ))) := by
    have hsourceEventually' : ∀ᶠ n in atTop,
        ((baseLaw n).prod (MeasureTheory.diracProba (factor n))).map scalePair = blockLaw n :=
      hsourceEventually.mono fun n hn => hn.symm
    simpa only [htarget] using hscaledLaw.congr' hsourceEventually'

  refine ⟨fun n =>
    (RandomWalk.measurable_normalizedStepCadlagPathIcc
      (fun _ => spatialScale n) (blockLength n)).aemeasurable,
    aemeasurable_id, ?_⟩
  simpa [blockLaw, ProbabilityMeasure.map, Measure.map_id] using hblockLaw

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
