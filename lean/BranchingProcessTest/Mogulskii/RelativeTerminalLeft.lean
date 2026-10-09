import Probability.Process.Path.PathClass.StepCorridor.Probability.Rate.Relative
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.SourcePathClassRelative
import Topology.Cadlag.TerminalLeft

open MeasureTheory
open ProbabilityTheory
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
open Skorokhod
open Skorokhod.PathClass.StepCorridor
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open scoped NNReal

private noncomputable def unitOpenCorridor : ContinuousAdmissibleStepCorridor := by
  let upper := StepBoundary.constant (1 : EReal)
  let lower := StepBoundary.constant (-1 : EReal)
  refine ⟨⟨upper, lower⟩, ?_⟩
  refine ⟨ContinuousMap.const unitInterval (0 : ℝ), by simp, ?_⟩
  change (Skorokhod.ofContinuousMap (ContinuousMap.const unitInterval (0 : ℝ)) :
      CadlagPath unitInterval ℝ) ∈ corridorSet upper lower
  simp [corridorSet, upper, lower, StepBoundary.eval_constant]

private noncomputable def unitOpenCorridorUnion : FiniteCorridorUnion 2 := by
  refine ⟨1, by decide, fun _ => unitOpenCorridor, ?_⟩
  have hminimum :
      finiteMinimumEnergy 2 1 (by decide : 0 < 1) (fun _ => unitOpenCorridor) =
        unitOpenCorridor.energy 2 := by
    simp [finiteMinimumEnergy]
  rw [hminimum]
  have henergy : unitOpenCorridor.energy 2 = widthCost 2 (1 : EReal) (-1 : EReal) := by
    apply ContinuousAdmissibleStepCorridor.energy_eq_widthCost_of_constant_values
    · intro t
      simp [unitOpenCorridor, StepBoundary.eval_constant]
    · intro t
      simp [unitOpenCorridor, StepBoundary.eval_constant]
  rw [henergy]
  have hnot : ¬ ((1 : EReal) = ⊤ ∨ (-1 : EReal) = ⊥) := by
    rintro (h | h)
    · have h' : ((1 : ℕ) : EReal) = ⊤ := by simpa using h
      exact EReal.natCast_ne_top 1 h'
    · have h' : ((-1 : ℝ) : EReal) = ⊥ := by simpa using h
      exact (EReal.coe_ne_bot (-1)) h'
  have htop : (1 : EReal) ≠ ⊤ := fun h => hnot (Or.inl h)
  change 0 < widthCost 2 (1 : EReal) (-1 : EReal)
  unfold widthCost
  simp [htop]

/-- The source's strict unit corridor, restricted to its terminal-left path
space. -/
private def unitSourceCorridor : Set (CadlagPath unitInterval ℝ) :=
  terminalLeftPathSpace ∩ unitOpenCorridor.toSet

private noncomputable def unitSourceCorridorApproximation :
    RelativeFiniteCorridorUnionApproximation 2 terminalLeftPathSpace unitSourceCorridor := by
  refine ⟨fun _ => unitOpenCorridorUnion, fun _ => unitOpenCorridorUnion, ?_, ?_, ?_⟩
  · intro n path hpath
    simpa [unitSourceCorridor, unitOpenCorridorUnion, FiniteCorridorUnion.toSet] using hpath
  · intro n path hpath
    simpa [unitSourceCorridor, unitOpenCorridorUnion, FiniteCorridorUnion.toSet] using hpath
  · simp

example : HasRelativeVanishingEnergyGapApproximation 2 terminalLeftPathSpace
    unitSourceCorridor := ⟨unitSourceCorridorApproximation⟩

example (path : CadlagPath unitInterval ℝ)
    (hpath : path ∈ terminalLeftPathSpace) :
    terminalLeftPath path = path :=
  terminalLeftPath_eq_self_of_mem_space path hpath

example (path : CadlagPath unitInterval ℝ) :
    terminalLeftPath (terminalLeftPath path) = terminalLeftPath path :=
  terminalLeftPath_idempotent path

example {α C q : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C) (hq : 0 < q) :
    HasStableProcessEscapeRate α (μ.map fun x => q * x)
      (P.map (Skorokhod.scalePath q)) (q ^ α * C) :=
  hEscape.spatialScale hq

section SourceRateApplication

variable {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
variable {C : ℝ} {normalization scale : ℕ → ℝ}
variable (hscale : IsStableMogulskiiScale 2 ν normalization scale)
variable (hslow : Asymptotics.IsSlowlyVaryingAtTop
  (stableSlowVariation 2 ν))
variable {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
variable (hEscape : HasStableProcessEscapeRate 2 μ P C)
variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
variable (hX : IsStableLevyProcess 2 μ X Q)
variable (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
variable (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
variable (htightBase : IsTightMeasureSet
  (Set.range fun n => RandomWalk.normalizedStepPathLaw ν normalization n))

#check
  ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation_of_sourceDiscretestepCorridorRates
    hscale (by norm_num) (by norm_num) hslow hEscape hX hcdf hDOA htightBase
    (G := unitSourceCorridor) ⟨unitSourceCorridorApproximation⟩

end SourceRateApplication

#check ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation_of_sourceDiscretestepCorridorRates

#print axioms Skorokhod.terminalLeftPath_eq_self_of_mem_space
#print axioms Skorokhod.terminalLeftPath_idempotent
#print axioms ProbabilityTheory.IsStableClockProcessLaw.spatialScale
#print axioms ProbabilityTheory.HasStableProcessEscapeRate.spatialScale
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.existsUnique_inner_outer_log_probability_ratio_of_hasRelativeVanishingEnergyGapApproximation_of_sourceDiscretestepCorridorRates
