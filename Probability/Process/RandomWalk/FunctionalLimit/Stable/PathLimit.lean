/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Cadlag.FiniteDimensional.Dense
public import Probability.Process.RandomWalk.Path.Skorokhod
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathFiniteDimensional
public import Probability.Process.Stable.PathLaw

/-!
# Stable random-walk path-law convergence

This file connects the stable finite-grid limit to the generic tightness and
finite-dimensional identification theorem for càdlàg path laws. Source-specific
centering estimates are explicit inputs so that the three stable regimes can
discharge them separately.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

variable {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
  {α : ℝ} {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
  {normalization center : ℕ → ℝ}

/-- Tightness and stable finite-grid convergence imply weak convergence of
the normalized random-walk path laws to a stable càdlàg path law. The
block-centering condition is stated on every finite time grid; this separates
the generic functional-limit argument from the source-specific estimates in
the centered stable regimes. -/
theorem tendsto_normalizedStepPathLaw_of_stableDomain_of_tight
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization center)
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hcenter : ∀ (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval),
      StrictMono grid → grid 0 = ⊥ → ∀ j : Fin blocks,
        Tendsto (fun n : ℕ => center
          (⌊(n : ℝ) * (grid j.succ : ℝ)⌋₊ -
            ⌊(n : ℝ) * (grid j.castSucc : ℝ)⌋₊) / normalization n)
          atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (⟨RandomWalk.normalizedStepPathLaw ν normalization n,
        (inferInstance : IsProbabilityMeasure
          (RandomWalk.normalizedStepPathLaw ν normalization n))⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
        (⟨P, (inferInstance : IsProbabilityMeasure P)⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) := by
  let pathLaw : ℕ → ProbabilityMeasure (CadlagPath unitInterval ℝ) :=
    fun n => ⟨RandomWalk.normalizedStepPathLaw ν normalization n, inferInstance⟩
  let limitLaw : ProbabilityMeasure (CadlagPath unitInterval ℝ) := ⟨P, inferInstance⟩
  have htight' : IsTightMeasureSet (Set.range
      (fun n : ℕ => (pathLaw n : Measure (CadlagPath unitInterval ℝ)))) := by
    have heq : Set.range (fun n : ℕ =>
        (pathLaw n : Measure (CadlagPath unitInterval ℝ))) =
        Set.range (fun n => RandomWalk.normalizedStepPathLaw ν normalization n) := by
      congr 1
    rw [heq]
    exact htight
  have hfinite (blocks : ℕ) (grid : Fin (blocks + 1) → unitInterval)
      (hgrid : StrictMono grid) (hstart : grid 0 = ⊥) :
      Tendsto (fun n => (pathLaw n).map (Skorokhod.denseEvaluation grid)) atTop
        (𝓝 (limitLaw.map (Skorokhod.denseEvaluation grid))) := by
    have hincrements : HasStableClockIncrements α μ unitIntervalClock
        cadlagPathProcess P := hP
    have hgridLimit := tendstoInDistribution_normalizedStepPath_finiteGrid_floor_of_stableDomain
      hDOA hincrements blocks grid hgrid hstart (hcenter blocks grid hgrid hstart)
    have hsource (n : ℕ) :
        (pathLaw n).map (Skorokhod.denseEvaluation grid) =
          (⟨(iidSequenceLaw ν).map
            (fun increments j => RandomWalk.normalizedStepPath normalization n
              increments (grid j : ℝ)), inferInstance⟩ :
            ProbabilityMeasure (Fin (blocks + 1) → ℝ)) := by
      apply Subtype.ext
      change ((RandomWalk.normalizedStepPathLaw ν normalization n).map
        (Skorokhod.denseEvaluation grid)) = _
      rw [RandomWalk.normalizedStepPathLaw,
        Measure.map_map (Skorokhod.measurable_denseEvaluation grid)
          (RandomWalk.measurable_normalizedStepCadlagPathIcc normalization n)]
      rfl
    have htarget :
        limitLaw.map (Skorokhod.denseEvaluation grid) =
          (⟨P.map (fun path j => cadlagPathProcess (grid j) path), inferInstance⟩ :
            ProbabilityMeasure (Fin (blocks + 1) → ℝ)) := by
      apply Subtype.ext
      rfl
    simpa only [hsource, htarget] using hgridLimit.tendsto
  change Tendsto pathLaw atTop (𝓝 limitLaw)
  exact Skorokhod.ProbabilityMeasure.tendsto_of_tight_of_finiteGridEvaluation
    pathLaw limitLaw htight' hfinite

/-- Zero-centered stable domain-of-attraction input needs no additional
block-centering estimate. -/
theorem tendsto_normalizedStepPathLaw_of_zeroCenter_stableDomain_of_tight
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitIntervalClock P)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n))) :
    Tendsto (fun n : ℕ =>
      (⟨RandomWalk.normalizedStepPathLaw ν normalization n,
        (inferInstance : IsProbabilityMeasure
          (RandomWalk.normalizedStepPathLaw ν normalization n))⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
        (⟨P, (inferInstance : IsProbabilityMeasure P)⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) := by
  refine tendsto_normalizedStepPathLaw_of_stableDomain_of_tight hDOA hP htight ?_
  intro blocks grid hgrid hstart j
  simp

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
