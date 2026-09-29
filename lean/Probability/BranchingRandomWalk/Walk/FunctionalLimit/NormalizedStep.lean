import Mathlib.Topology.UnitInterval
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.FunctionalLimit

/-!
# A normalized-step functional limit input (Skorokhod `J₁`)

The stable route of the small-deviation theorem takes as input that the
càdlàg step paths normalized by a positive norming sequence converge in
distribution to a limit process.  For a jump limit this is the Skorokhod
`J₁` convergence, whereas a continuous limit may use the uniform path
topology.

The consequences the corridor argument consumes are the scale-generic ones: strict finite tubes are bounded
below by the limit law of the open corridor, centred strict tubes by the centred open corridor, and weak finite
tubes are bounded above by the limit law of the closed corridor. They are
obtained here by specializing the càdlàg bridge of
`Mogulskii.FunctionalLimit`, which is stated for an arbitrary positive spatial
scale.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk

open Combinatorics.Branching.Walk

/-- The càdlàg step paths normalized by `normalization` converge in distribution,
in the Skorokhod `J₁` topology, to `limit`. -/
def IsNormalizedStepFunctionalLimit {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (normalization : ℕ → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (limit : Ω → CadlagPath unitInterval ℝ) : Prop :=
  TendstoInDistribution (fun n => normalizedStepCadlagPathIcc normalization n)
    atTop limit (fun _ => independentIncrementLaw ν) P

namespace IsNormalizedStepFunctionalLimit

variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure ℝ} [IsProbabilityMeasure ν] {normalization : ℕ → ℝ}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Strict finite tubes of positive width have the limit law of the open corridor
as a lower bound. -/
theorem measure_skorokhodOpenCorridor_le_liminf_strictTube (h : IsNormalizedStepFunctionalLimit ν normalization P limit)
    (hscale : ∀ᶠ n in atTop, 0 < normalization n) {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    P.map limit (Skorokhod.rangeInOpenInterval (-a) (1 - a)) ≤
      atTop.liminf (fun n : ℕ => independentIncrementLaw ν
        {increment | InOpenHorizontalTube a (normalization n) n increment}) :=
  measure_skorokhodCorridor_le_liminf_strictTube_of_functionalLimit
    P ν normalization hscale limit h ha haOne

/-- Centred strict tubes of positive width, at every normalized width. -/
theorem measure_centeredSkorokhodOpenCorridor_le_liminf_strictTube (h : IsNormalizedStepFunctionalLimit ν normalization P limit)
    (hscale : ∀ᶠ n in atTop, 0 < normalization n) {width : ℝ} (hwidth : 0 < width) :
    P.map limit
        (Skorokhod.rangeInOpenInterval (-(width / 2)) (width / 2)) ≤
      atTop.liminf (fun n : ℕ => independentIncrementLaw ν
        {increment | InOpenHorizontalTube (1 / 2)
          (width * normalization n) n increment}) :=
  measure_centeredSkorokhodCorridor_le_liminf_strictTube_of_functionalLimit
    P ν normalization hscale limit h hwidth

/-- Weak finite tubes have the limit law of the closed corridor as an upper
bound. -/
theorem limsup_weakTube_le_measure_skorokhodClosedCorridor (h : IsNormalizedStepFunctionalLimit ν normalization P limit)
    (hscale : ∀ᶠ n in atTop, 0 < normalization n) {a : ℝ} (ha : 0 ≤ a) (haOne : a ≤ 1) :
    atTop.limsup (fun n : ℕ => independentIncrementLaw ν
        {increment | InHorizontalTube a (normalization n) n increment}) ≤
      P.map limit (Skorokhod.rangeInClosedInterval (-a) (1 - a)) :=
  limsup_weakTube_le_measure_skorokhodCorridor_of_functionalLimit
    P ν normalization hscale limit h ha haOne

end IsNormalizedStepFunctionalLimit

end ProbabilityTheory.RandomWalk
