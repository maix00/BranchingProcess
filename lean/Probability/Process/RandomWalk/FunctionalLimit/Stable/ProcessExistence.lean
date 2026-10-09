/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLawExistence
public import Probability.Process.Stable.PathLaw.Concatenation
public import Probability.Process.Stable.PathLaw.FullProcess
public import Probability.Process.Stable.PathLaw.MonotoneGrid

/-!
# Stable process existence from tight random-walk sources

Tightness and scalar domain-of-attraction convergence produce a subsequential
càdlàg path law. Its strict-grid finite-dimensional laws extend to monotone
grids, which are the input to the generic stable clock-process constructor.
-/

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- Tight source random-walk path laws have a subsequential stable clock law.
The grid-law bridge supplies the zero start and all monotone position laws
needed by the shared clock-process constructor. -/
theorem exists_stableClockProcessLaw_of_tightSource
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hStable : IsStrictlyAlphaStable α μ)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n))) :
    ∃ P : ProbabilityMeasure (CadlagPath unitInterval ℝ),
      IsStableClockProcessLaw α μ UnitInterval.clock (P : Measure _) ∧
      ∃ sub : ℕ → ℕ,
        StrictMono sub ∧
        Tendsto (fun n =>
          (⟨RandomWalk.normalizedStepPathLaw ν normalization (sub n), inferInstance⟩ :
            ProbabilityMeasure (CadlagPath unitInterval ℝ))) atTop
          (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance P) := by
  obtain ⟨sub, P, hsub, hconv, hstrict⟩ :=
    exists_subseq_normalizedStepPathLaw_with_stable_grid_laws
      hDOA hStable htight (by intro blocks grid hgrid hstart j; simp)
  let Pmeasure : Measure (CadlagPath unitInterval ℝ) := P
  letI : IsProbabilityMeasure Pmeasure := inferInstance
  have hStrictPositionLaws : ∀ (n : ℕ) (grid : Fin (n + 1) → unitInterval),
      StrictMono grid → grid 0 = ⊥ →
      Pmeasure.map (MeasureTheory.CadlagPath.denseEvaluation grid) =
        ((stableTimeLawProductProbability (μ := μ) α grid :
          ProbabilityMeasure (Fin n → ℝ)) : Measure (Fin n → ℝ)).map
          (Fin.partialSum : (Fin n → ℝ) → Fin (n + 1) → ℝ) := by
    intro n grid hgrid hstart
    exact congrArg (fun M : ProbabilityMeasure (Fin (n + 1) → ℝ) =>
      (M : Measure (Fin (n + 1) → ℝ))) (hstrict n grid hgrid hstart)
  obtain ⟨hstart, hpositions⟩ :=
    stableGridPositionLaws_of_strictGridPositionLaws hStable hStrictPositionLaws
  have hP : IsStableClockProcessLaw α μ UnitInterval.clock Pmeasure :=
    ProbabilityTheory.isStableClockProcessLaw_of_unitInterval_positionGridLaws
      hStable hstart hpositions
  exact ⟨P, hP, sub, hsub, hconv⟩

/-- Scalar attraction and tightness produce an actual full-time stable Lévy
process without an externally supplied process witness. The path-law cluster
is extracted on the unit interval, then Mathlib's infinite product constructs
independent copies of that unit block and `FullProcess` concatenates them.

The tightness premise is kept explicit here; source-specific tail criteria
should discharge it in the index-regime interfaces. -/
theorem exists_stableLevyProcess_of_tightSource
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization : ℕ → ℝ}
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hStable : IsStrictlyAlphaStable α μ)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n))) :
    ∃ (Q : ProbabilityMeasure (ℕ → CadlagPath unitInterval ℝ))
      (X : NNReal → (ℕ → CadlagPath unitInterval ℝ) → ℝ),
      IsStableLevyProcess α μ X (Q : Measure _) := by
  obtain ⟨P, hP, _sub, _hsub, _hconv⟩ :=
    exists_stableClockProcessLaw_of_tightSource hDOA hStable htight
  let Q : Measure (ℕ → CadlagPath unitInterval ℝ) :=
    ProbabilityTheory.iidUnitPathBlockLaw (P : Measure _)
  have hQ : IsProbabilityMeasure Q :=
    ProbabilityTheory.iidUnitPathBlockLaw_isProbabilityMeasure (P : Measure _)
  let X : NNReal → (ℕ → CadlagPath unitInterval ℝ) → ℝ :=
    fun t ω => ProbabilityTheory.iidUnitPathBlockProcess ω t
  letI : IsProbabilityMeasure Q := hQ
  exact ⟨⟨Q, hQ⟩, X, by
    simpa [Q, X] using
      ProbabilityTheory.iidUnitPathBlockProcess_isStableLevyProcess hP⟩

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
