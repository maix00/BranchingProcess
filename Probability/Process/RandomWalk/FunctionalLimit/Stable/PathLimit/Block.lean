/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Cadlag.FiniteDimensional.Dense
public import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathFiniteDimensional
public import Probability.Process.Stable.PathLaw
public import Topology.Cadlag.Skorokhod.Separable
public import Probability.Sequence.IID
public import Topology.Cadlag.Skorokhod.Scaling
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Tight

/-!
# Functional limits for variable-length blocks

This file derives the path-law limit for a variable-length block from the
fixed-horizon stable functional limit. Spatial rescaling is handled first on
finite-dimensional Euclidean spaces, where Mathlib's Slutsky theorem applies.
Tightness and the generic dense-grid theorem then reconstruct convergence in
the Skorokhod `J₁` topology.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

variable {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
  {α : ℝ} {normalization spatialScale : ℕ → ℝ}
  {blockLength : ℕ → ℕ}
  {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]

/-- A fixed-horizon stable path limit yields the path-law limit for blocks
whose lengths tend to infinity and whose norming-to-space ratio converges.
The proof applies Slutsky in each finite-dimensional Euclidean space, transfers
tightness through the continuous scalar action on `J₁` path space, and uses
the generic tightness-plus-dense-grid reconstruction theorem. -/
theorem tendstoInDistribution_normalizedStepBlockPathLaw_of_baseTightness
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
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
  let pairPath : ℕ → (ℕ → ℝ) → ℝ × CadlagPath unitInterval ℝ :=
    fun n ω => (factor n, basePath n ω)
  let pairLaw : ℕ → Measure (ℝ × CadlagPath unitInterval ℝ) :=
    fun n => (iidSequenceLaw ν).map (pairPath n)
  let scalePair : ℝ × CadlagPath unitInterval ℝ → CadlagPath unitInterval ℝ :=
    fun p => Skorokhod.scalePath p.1 p.2
  let scaledLaw : ℕ → Measure (CadlagPath unitInterval ℝ) :=
    fun n => (pairLaw n).map scalePair
  let blockLaw : ℕ → Measure (CadlagPath unitInterval ℝ) :=
    fun n => (iidSequenceLaw ν).map
      (RandomWalk.normalizedStepBlockCadlagPathIcc spatialScale blockLength n)
  let limitLaw : ProbabilityMeasure (CadlagPath unitInterval ℝ) :=
    ⟨P.map (Skorokhod.scalePath r), inferInstance⟩

  have hfactorCompact : IsCompact (insert r (Set.range factor)) :=
    hratio.isCompact_insert_range
  have hdiracTight : IsTightMeasureSet
      (Set.range fun n => Measure.dirac (factor n) : Set (Measure ℝ)) := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    refine ⟨insert r (Set.range factor), hfactorCompact, ?_⟩
    intro ρ hρ
    rcases hρ with ⟨n, rfl⟩
    have hn : factor n ∈ insert r (Set.range factor) := Or.inr ⟨n, rfl⟩
    rw [Measure.dirac_apply' _ hfactorCompact.isClosed.measurableSet.compl]
    simp [hn]

  have hpairMeasurable (n : ℕ) : Measurable (pairPath n) := by
    apply Measurable.prodMk
    · exact measurable_const
    · exact RandomWalk.measurable_normalizedStepCadlagPathIcc
        normalization (blockLength n)
  have hfst (n : ℕ) : (pairLaw n).fst = Measure.dirac (factor n) := by
    change ((iidSequenceLaw ν).map (pairPath n)).fst = _
    rw [Measure.fst_map_prodMk measurable_const
      (RandomWalk.measurable_normalizedStepCadlagPathIcc
        normalization (blockLength n))]
    simp [factor, Measure.map_const]
  have hsnd (n : ℕ) : (pairLaw n).snd =
      RandomWalk.normalizedStepPathLaw ν normalization (blockLength n) := by
    change ((iidSequenceLaw ν).map (pairPath n)).snd = _
    rw [Measure.snd_map_prodMk measurable_const
      (RandomWalk.measurable_normalizedStepCadlagPathIcc
        normalization (blockLength n))]
    rfl
  have hfstRange : Measure.fst '' Set.range pairLaw =
      Set.range (fun n => Measure.dirac (factor n)) := by
    ext ρ
    constructor
    · rintro ⟨κ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (hfst n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨pairLaw n, ⟨n, rfl⟩, hfst n⟩
  have hsndRange : Measure.snd '' Set.range pairLaw =
      Set.range (fun n => RandomWalk.normalizedStepPathLaw ν normalization
        (blockLength n)) := by
    ext ρ
    constructor
    · rintro ⟨κ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (hsnd n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨pairLaw n, ⟨n, rfl⟩, hsnd n⟩
  have hsecondTight : IsTightMeasureSet
      (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization
        (blockLength n)) := by
    apply htightBase.subset
    rintro _ ⟨n, rfl⟩
    exact ⟨blockLength n, rfl⟩
  have hpairTight : IsTightMeasureSet (Set.range pairLaw) := by
    apply IsTightMeasureSet.prodMk
    · simpa [hfstRange] using hdiracTight
    · simpa [hsndRange] using hsecondTight
  have hscalePairContinuous : Continuous scalePair :=
    Skorokhod.continuous_scalePath
  have hfixedScaleContinuous : Continuous (Skorokhod.scalePath r) :=
    hscalePairContinuous.comp (continuous_const.prodMk continuous_id)
  have hscaledTight : IsTightMeasureSet (Set.range scaledLaw) := by
    apply (hpairTight.map hscalePairContinuous).subset
    rintro _ ⟨n, rfl⟩
    exact ⟨pairLaw n, ⟨n, rfl⟩, rfl⟩

  have hgood : ∀ᶠ n in atTop,
      0 < spatialScale n ∧ 0 < normalization (blockLength n) :=
    hscale.and hnorm
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hgood
  let shifted : ℕ → ℕ := fun n => max n N
  have hshift : Tendsto shifted atTop atTop := by
    exact Filter.tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall fun n => le_max_left n N)
      tendsto_natCast_atTop_atTop

  have hpathEq (n : ℕ) (hn : N ≤ n) (ω : ℕ → ℝ) :
      RandomWalk.normalizedStepBlockCadlagPathIcc spatialScale blockLength n ω =
        Skorokhod.scalePath (factor n) (basePath n ω) := by
    apply CadlagPath.ext
    intro t
    simp only [RandomWalk.normalizedStepBlockCadlagPathIcc,
      RandomWalk.normalizedStepCadlagPathIcc_apply, Skorokhod.scalePath_apply,
      basePath, factor, RandomWalk.normalizedStepPath]
    field_simp [ne_of_gt (hN n hn).1, ne_of_gt (hN n hn).2]

  have hblockLawEq (n : ℕ) (hn : N ≤ n) : blockLaw n = scaledLaw n := by
    change (iidSequenceLaw ν).map
        (RandomWalk.normalizedStepBlockCadlagPathIcc spatialScale blockLength n) = _
    calc
      _ = (iidSequenceLaw ν).map (scalePair ∘ pairPath n) := by
        apply Measure.map_congr
        exact ae_of_all _ (fun ω => hpathEq n hn ω)
      _ = ((iidSequenceLaw ν).map (pairPath n)).map scalePair := by
        symm
        exact Measure.map_map hscalePairContinuous.measurable (hpairMeasurable n)
      _ = scaledLaw n := rfl

  have hscaledLawTight : IsTightMeasureSet (Set.range scaledLaw) := hscaledTight
  have hmodifiedTight : IsTightMeasureSet
      (Set.range fun n => blockLaw (shifted n)) := by
    apply hscaledLawTight.subset
    rintro ρ ⟨n, rfl⟩
    refine ⟨shifted n, ?_⟩
    exact (hblockLawEq (shifted n) (le_max_right n N)).symm

  have hX : HasStableClockIncrements α μ unitIntervalClock
      cadlagPathProcess P := hP
  have hbaseGrid (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
      (hgrid : StrictMono grid) (hstart : grid 0 = ⊥) :
      TendstoInDistribution
        (fun n (ω : ℕ → ℝ) j =>
          RandomWalk.normalizedStepPath normalization n ω (grid j : ℝ))
        atTop (fun ω j => cadlagPathProcess (grid j) ω)
        (fun _ => iidSequenceLaw ν) P :=
    tendstoInDistribution_normalizedStepPath_finiteGrid_floor_of_zeroCenter
      hDOA hX blocks grid hgrid hstart

  have hbaseBlockGrid (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
      (hgrid : StrictMono grid) (hstart : grid 0 = ⊥) :
      TendstoInDistribution
        (fun n (ω : ℕ → ℝ) j =>
          RandomWalk.normalizedStepPath normalization (blockLength n) ω (grid j : ℝ))
        atTop (fun ω j => cadlagPathProcess (grid j) ω)
        (fun _ => iidSequenceLaw ν) P := by
    have h := hbaseGrid blocks grid hgrid hstart
    refine ⟨fun n => h.forall_aemeasurable (blockLength n),
      h.aemeasurable_limit, ?_⟩
    exact h.tendsto.comp hblock

  have hfactorMeasure : TendstoInMeasure (iidSequenceLaw ν)
      (fun n (_ : ℕ → ℝ) => factor n) atTop (fun _ => r) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      fun_prop
    · filter_upwards with _
      exact hratio

  have hscaledGrid (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
      (hgrid : StrictMono grid) (hstart : grid 0 = ⊥) :
      TendstoInDistribution
        (fun n (ω : ℕ → ℝ) j => factor n *
          RandomWalk.normalizedStepPath normalization (blockLength n) ω (grid j : ℝ))
        atTop (fun ω j => r * cadlagPathProcess (grid j) ω)
        (fun _ => iidSequenceLaw ν) P := by
    have h := hbaseBlockGrid blocks grid hgrid hstart
    exact TendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : (Fin (blocks + 1) → ℝ) × ℝ => fun j => p.2 * p.1 j)
      (by fun_prop) h hfactorMeasure
      (fun n => (measurable_const : Measurable
        (fun _ : ℕ → ℝ => factor n)).aemeasurable)

  let modifiedLaw : ℕ → Measure (CadlagPath unitInterval ℝ) :=
    fun n => blockLaw (shifted n)
  let modifiedPath : ℕ → (ℕ → ℝ) → CadlagPath unitInterval ℝ :=
    fun n => RandomWalk.normalizedStepBlockCadlagPathIcc spatialScale blockLength (shifted n)
  let modifiedProbabilityLaw : ℕ → ProbabilityMeasure (CadlagPath unitInterval ℝ) :=
    fun n => ⟨modifiedLaw n, inferInstance⟩
  have hmodifiedGrid (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
      (hgrid : StrictMono grid) (hstart : grid 0 = ⊥) :
      TendstoInDistribution
        (fun n (ω : ℕ → ℝ) j => modifiedPath n ω (grid j))
        atTop (fun ω j => Skorokhod.scalePath r ω (grid j))
        (fun _ => iidSequenceLaw ν) P := by
    have h := hscaledGrid blocks grid hgrid hstart
    have heq (n : ℕ) :
        (fun ω j => modifiedPath n ω (grid j)) =ᵐ[iidSequenceLaw ν]
          (fun ω j => factor (shifted n) *
            RandomWalk.normalizedStepPath normalization (blockLength (shifted n))
              ω (grid j : ℝ)) := by
      apply ae_of_all
      intro ω
      funext j
      have hpath := hpathEq (shifted n) (le_max_right n N) ω
      simpa [modifiedPath, basePath, Skorokhod.scalePath_apply] using
        congrArg (fun path => path (grid j)) hpath
    have htarget : ∀ᵐ ω ∂P,
        (fun j => Skorokhod.scalePath r ω (grid j)) =
          (fun j => r * cadlagPathProcess (grid j) ω) := by
      filter_upwards with ω
      funext j
      simp [Skorokhod.scalePath_apply]
    have hshifted :=
      (show TendstoInDistribution
        (fun n (ω : ℕ → ℝ) j => factor (shifted n) *
          RandomWalk.normalizedStepPath normalization (blockLength (shifted n))
            ω (grid j : ℝ))
        atTop (fun ω j => r * cadlagPathProcess (grid j) ω)
        (fun _ => iidSequenceLaw ν) P from ?_)
    · exact TendstoInDistribution.congr (fun n => (heq n).symm) htarget hshifted
    · refine ⟨fun n => h.forall_aemeasurable (shifted n),
        h.aemeasurable_limit, ?_⟩
      exact h.tendsto.comp hshift

  have hfinite (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
      (hgrid : StrictMono grid) (hstart : grid 0 = ⊥) :
      Tendsto (fun n => (modifiedProbabilityLaw n).map (Skorokhod.denseEvaluation grid))
        atTop (𝓝 (limitLaw.map (Skorokhod.denseEvaluation grid))) := by
    have hgridLimit := hmodifiedGrid blocks grid hgrid hstart
    have hsource (n : ℕ) :
        (modifiedProbabilityLaw n).map (Skorokhod.denseEvaluation grid) =
          (⟨(iidSequenceLaw ν).map
            (fun ω j => modifiedPath n ω (grid j)), inferInstance⟩ :
            ProbabilityMeasure (Fin (blocks + 1) → ℝ)) := by
      apply Subtype.ext
      change Measure.map (Skorokhod.denseEvaluation grid)
        (Measure.map
          (RandomWalk.normalizedStepCadlagPathIcc
            (fun _ => spatialScale (shifted n)) (blockLength (shifted n)))
          (iidSequenceLaw ν)) = _
      rw [Measure.map_map (Skorokhod.measurable_denseEvaluation grid)
        (measurable_normalizedStepCadlagPathIcc
          (fun _ => spatialScale (shifted n)) (blockLength (shifted n)))]
      rfl
    have htarget : limitLaw.map (Skorokhod.denseEvaluation grid) =
        (⟨P.map (fun ω j => Skorokhod.scalePath r ω (grid j)), inferInstance⟩ :
          ProbabilityMeasure (Fin (blocks + 1) → ℝ)) := by
      apply Subtype.ext
      change Measure.map (Skorokhod.denseEvaluation grid)
        (P.map (Skorokhod.scalePath r)) = _
      rw [Measure.map_map (Skorokhod.measurable_denseEvaluation grid)
        hfixedScaleContinuous.measurable]
      rfl
    simpa only [hsource, htarget] using hgridLimit.tendsto

  have hweakModified :=
    Skorokhod.ProbabilityMeasure.tendsto_of_tight_of_finiteGridEvaluation
      modifiedProbabilityLaw limitLaw hmodifiedTight hfinite
  have hweakActual : Tendsto
      (fun n : ℕ =>
        (⟨blockLaw n, inferInstance⟩ : ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
        limitLaw) := by
    refine hweakModified.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have heq : shifted n = n := max_eq_left hn
    apply Subtype.ext
    simp [modifiedProbabilityLaw, modifiedLaw, heq, blockLaw]

  refine ⟨fun n =>
      (measurable_normalizedStepCadlagPathIcc
        (fun _ => spatialScale n) (blockLength n)).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  change Tendsto
    (fun n : ℕ =>
      (⟨(iidSequenceLaw ν).map
        (RandomWalk.normalizedStepBlockCadlagPathIcc spatialScale blockLength n),
        inferInstance⟩ : ProbabilityMeasure (CadlagPath unitInterval ℝ)))
    atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
      (⟨(P.map (Skorokhod.scalePath r)).map id, inferInstance⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ)))
  simpa [Measure.map_id] using hweakActual

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
