/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.Portmanteau
public import Probability.Process.Path.UnitInterval
public import Topology.ContinuousMap.Oscillation

/-!
# Probability bounds from finite corridor covers

The deterministic finite cover of zero-starting paths with bounded range
oscillation gives a measure bound by a finite sum of open-corridor masses.
The probabilistic input is expressed through an almost-everywhere
start-at-zero hypothesis; Brownian specializations live in the Brownian layer.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Process.Path

/-- The measurable event that a continuous path has range diameter at most
`width`. -/
def rangeOscillationSet (width : ℝ) : Set C(unitInterval, ℝ) :=
  ⋂ s : unitInterval, ⋂ t : unitInterval,
    {path : C(unitInterval, ℝ) | |path s - path t| ≤ width}

/-- The mass of the range-oscillation event under the continuous-path image of
an arbitrary real-valued process.  The process need not be Brownian here; the
Brownian assumptions enter only in the estimates that use this quantity. -/
noncomputable def rangeOscillationMass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : NNReal → Ω → ℝ}
    (hcontinuous : ∀ ω, Continuous (B · ω)) (width : ℝ) : ENNReal :=
  P.map (continuousunitIntervalPath B hcontinuous)
    (rangeOscillationSet width)

/-- The start-at-zero event in continuous path space. -/
def startsAtZeroSet : Set C(unitInterval, ℝ) := {path | path 0 = 0}

theorem isClosed_rangeOscillationSet (width : ℝ) :
    IsClosed (rangeOscillationSet width) := by
  unfold rangeOscillationSet
  refine isClosed_iInter fun s => isClosed_iInter fun t => ?_
  change IsClosed ((fun path : C(unitInterval, ℝ) =>
    |path s - path t|) ⁻¹' Set.Iic width)
  exact isClosed_Iic.preimage <| continuous_abs.comp
    ((continuous_eval_const s).sub (continuous_eval_const t))

theorem measurableSet_rangeOscillationSet
    [MeasurableSpace C(unitInterval, ℝ)] [BorelSpace C(unitInterval, ℝ)]
    (width : ℝ) : MeasurableSet (rangeOscillationSet width) :=
  (isClosed_rangeOscillationSet width).measurableSet

theorem isClosed_startsAtZeroSet : IsClosed startsAtZeroSet := by
  exact isClosed_singleton.preimage (continuous_eval_const (0 : unitInterval))

theorem measurableSet_startsAtZeroSet
    [MeasurableSpace C(unitInterval, ℝ)] [BorelSpace C(unitInterval, ℝ)] :
    MeasurableSet startsAtZeroSet := isClosed_startsAtZeroSet.measurableSet

/-- A path law supported almost surely on paths starting at zero assigns to
the oscillation event at most the sum of the fixed finite corridor cover. -/
theorem measure_rangeOscillationSet_le_finiteCorridorCover
    (μ : Measure C(unitInterval, ℝ)) [IsProbabilityMeasure μ]
    {width : ℝ} {count : ℕ} (hwidth : 0 < width) (hcount : 0 < count)
    (hstart : ∀ᵐ path ∂μ, path 0 = 0) :
    μ (rangeOscillationSet width) ≤
      ∑ j : Fin count,
        μ (ContinuousMap.rangeInOpenInterval
          (ContinuousMap.oscillationCoverLower width count j)
          (ContinuousMap.oscillationCoverUpper width count j)) := by
  let osc := rangeOscillationSet width
  let start := startsAtZeroSet
  have hae : osc =ᵐ[μ] osc ∩ start := by
    filter_upwards [hstart] with path hpath
    simp [osc, start, startsAtZeroSet, hpath]
  have hmeasure : μ osc = μ (osc ∩ start) := measure_congr hae
  calc
    μ osc = μ (osc ∩ start) := hmeasure
    _ ≤ μ (⋃ j : Fin count,
          ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j)) := by
      apply measure_mono
      intro path hpath
      have hpath' : path 0 = 0 ∧
          ContinuousMap.rangeOscillationLe width path := by
        change path ∈ rangeOscillationSet width ∧ path ∈ startsAtZeroSet at hpath
        have hosc : ∀ s t, |path s - path t| ≤ width := by
          intro s t
          exact Set.mem_iInter.mp (Set.mem_iInter.mp hpath.1 s) t
        exact ⟨hpath.2, hosc⟩
      exact ContinuousMap.rangeOscillationLe_subset_finiteCorridorCover
        width count hwidth hcount hpath'
    _ ≤ ∑ j : Fin count,
          μ (ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j)) :=
      measure_iUnion_fintype_le μ _

/-- Under functional convergence, the range-oscillation mass of the limit is
bounded by the finite sum of `liminf` masses of the fixed open corridors.
This is the Portmanteau bridge used by the corrected Brownian range route. -/
theorem TendstoInDistribution.measure_rangeOscillationSet_le_sum_liminf_finiteCorridorCover
    {Ω : ℕ → Type*} {mΩ : ∀ n, MeasurableSpace (Ω n)}
    {μ : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    [IsProbabilityMeasure μ']
    {X : (n : ℕ) → Ω n → C(unitInterval, ℝ)}
    {Z : Ω' → C(unitInterval, ℝ)}
    (h : TendstoInDistribution X atTop Z μ μ')
    {width : ℝ} {count : ℕ}
    (hwidth : 0 < width) (hcount : 0 < count)
    (hstart : ∀ᵐ path ∂μ'.map Z, path (0 : unitInterval) = 0) :
    μ'.map Z (rangeOscillationSet width) ≤
      ∑ j : Fin count, atTop.liminf (fun n =>
        (μ n).map (X n)
          (ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j))) := by
  calc
    μ'.map Z (rangeOscillationSet width) ≤
        ∑ j : Fin count, μ'.map Z
          (ContinuousMap.rangeInOpenInterval
            (ContinuousMap.oscillationCoverLower width count j)
            (ContinuousMap.oscillationCoverUpper width count j)) :=
      measure_rangeOscillationSet_le_finiteCorridorCover
        (μ'.map Z) hwidth hcount hstart
    _ ≤ ∑ j : Fin count, atTop.liminf (fun n =>
          (μ n).map (X n)
            (ContinuousMap.rangeInOpenInterval
              (ContinuousMap.oscillationCoverLower width count j)
              (ContinuousMap.oscillationCoverUpper width count j))) := by
      apply Finset.sum_le_sum
      intro j _hj
      exact h.measure_map_le_liminf_of_isOpen
        (ContinuousMap.isOpen_rangeInOpenInterval
          (ContinuousMap.oscillationCoverLower_lt_upper
            width count j hwidth hcount))

end ProbabilityTheory.Process.Path

end
