/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.Core
public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.PathSupport
public import Topology.Cadlag.Skorokhod.SmallDeviation.PathSets

/-!
# Path-support entrance specialization

Support criteria for proving positivity of the fixed entrance event.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The exact entrance event in Mogulskii's comparison is a nonempty open
Skorokhod set. Its positivity follows if the straight path to `c-b` belongs
to the support of the unit-time path law. -/
theorem measure_unitEntrance_pos_of_straightPath_mem_support
    (Q : Measure (CadlagPath unitInterval ℝ))
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1) (hc : -1 < c ∧ c < 1)
    (hε : 0 < ε)
    (hsupport : Skorokhod.straightPath (c - b) ∈ Q.support) :
    0 < Q (Skorokhod.rangeInOpenIntervalEndsIn
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  apply measure_skorokhodCorridorEndsIn_pos_of_straightPath_mem_support
    Q (y := c - b)
  · constructor <;> linarith [hc.1, hc.2]
  · constructor <;> linarith [hb.1, hb.2]
  · constructor <;> linarith
  · exact hsupport

/-- The open entrance event used in the proof is contained in the source's
left-open, right-closed `Y` event. Thus path support also gives positivity
for the exact source event, without identifying the two events. -/
theorem measure_unitEntrance_source_pos_of_straightPath_mem_support
    (Q : Measure (CadlagPath unitInterval ℝ))
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1) (hc : -1 < c ∧ c < 1)
    (hε : 0 < ε)
    (hsupport : Skorokhod.straightPath (c - b) ∈ Q.support) :
    0 < Q (Skorokhod.endpointWindow ⊤ (c - b - ε) (c - b + ε)
      (Skorokhod.rangeInOpenInterval (c - 1) (c + 1))) := by
  have hopen := measure_unitEntrance_pos_of_straightPath_mem_support
    Q b c ε hb hc hε hsupport
  exact hopen.trans_le (measure_mono
    (Skorokhod.rangeInOpenIntervalEndsIn_subset_endpointWindow
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)))

/-- The complete comparison chain from path-law support to the negative-log
ratio. The only path-support input is the straight entrance path to `c-b`;
two-sided stable mass gives positivity of every narrow corridor. -/
theorem IsStableLevyProcess.eventually_one_sub_le_logCorridor_ratio_of_path_support
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (F : Ω → CadlagPath unitInterval ℝ) (hF : Measurable F)
    (hpath : ∀ᵐ ω ∂P, ∀ t : unitInterval,
      F ω t = segmentIncrement X 0 1 ω t)
    (b c ε : ℝ) (hb : -1 < b ∧ b < 1) (hc : -1 < c ∧ c < 1)
    (hε : 0 < ε)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hsupportEntrance :
      Skorokhod.straightPath (c - b) ∈ (P.map F).support)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0),
      1 - δ ≤
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (b - 1)) (a * (b + 1)))).toReal) /
        Real.log ((P (fullSegmentCorridorEvent X 0 1
          (a * (c - (1 + ε))) (a * (c + 1 + ε)))).toReal) := by
  have hp : 0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
    apply measure_fullSegmentCorridorReturnEvent_pos_of_path_support
      P X F hF hpath (y := c - b)
    · constructor <;> linarith [hc.1, hc.2]
    · constructor <;> linarith [hb.1, hb.2]
    · constructor <;> linarith
    · exact hsupportEntrance
  obtain ⟨hneg, hpos⟩ :=
    h.increments.strictlyStable.twoSidedMass_of_cdfAtZero hcdf
  exact h.eventually_one_sub_le_logCorridor_ratio_of_entrance_pos
    hpos hneg b c ε hb hε.le hp δ hδ


end ProbabilityTheory

end
