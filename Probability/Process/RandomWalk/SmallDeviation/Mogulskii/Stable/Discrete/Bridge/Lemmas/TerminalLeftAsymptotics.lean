/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.Path.Skorokhod.Core
import Probability.Process.Stable.Levy
import Probability.Process.Stable.PathLaw.Basic
import Topology.Cadlag.Basic

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Bridge.Events
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Bridge.Lemmas.TerminalLeftGeometry
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Endpoint.StrictStable

import Analysis.Asymptotics.Sequence.NegativeRatio
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Bridge.Lemmas.Comparison
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.TerminalLeft.Bounds.Lower

/-!
# Terminal-left asymptotic lemmas for Mogul'skii equation (34)

This proof-chain module supplies the estimates used by the finite-bridge
comparison and its logarithmic-ratio consequence in equation (34), Theorem 3,
Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726--736,
DOI 10.1137/1119081.

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_sourceBaseCorridorEvent_pos_of_stableDomain`: the source
  base-corridor probability satisfies $\mathbb P_\nu(B_n)>0$ eventually.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_one_sub_le_log_ratio_of_source_equation34`: positive base mass,
  a finite-bridge comparison, and vanishing endpoint mass give
  $1-\delta\leq\log\mathbb P_\nu(B_n)/\log\mathbb P_\nu(E_n)$ eventually.

The endpoint-corridor positivity estimate is private to the logarithmic-ratio
proof. The more general slow-variation version of the endpoint-decay estimate
lives in `EndpointCorridorDecay.lean`.
-/
open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The source lower endpoint-band estimate makes the original open unit
corridor event positive.  The lower estimate controls a closed tube whose
radius is strictly smaller than the unit radius, hence it is contained in the
open source event. -/
lemma eventually_sourceBaseCorridorEvent_pos_of_stableDomain
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ} {horizon : ℕ → ℕ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hnorm : IsStableNorming α ν normalization)
    (hα : 0 < α) (hα₂ : α < 2)
    (hscale : Tendsto scale atTop atTop) :
    ∀ᶠ n in atTop,
      0 < iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) (horizon n)) := by
  obtain ⟨r, lowerBound, hr, hrhalf, hlower, htube⟩ :=
    eventually_horizontalTubeProbability_ge_pow_of_stableDomain
      hDOA hP hX hcdf htight hnorm hα hα₂ hscale
  have hscalePos : ∀ᶠ n in atTop, 0 < scale n :=
    hscale.eventually (eventually_gt_atTop 0)
  have hrSmall : r + 4 * (r / 16) < 1 := by nlinarith
  filter_upwards [htube, hscalePos] with n hbound hscaleN
  let narrowRadius : ℝ := r + 4 * (r / 16)
  have hradPos : 0 < narrowRadius := by
    dsimp [narrowRadius]
    positivity
  have hradLt : narrowRadius < 1 := by
    simpa [narrowRadius] using hrSmall
  have hwidthLt : 2 * narrowRadius * scale n < 2 * scale n :=
    mul_lt_mul_of_pos_right (by nlinarith [hradLt]) (hscaleN)
  have hclosedSubset :
      {increment : ℕ → ℝ |
        InHorizontalTube (1 / 2) (2 * narrowRadius * scale n)
          (horizon n) increment} ⊆
        sourceBaseCorridorEvent (scale n) (horizon n) := by
    intro increment htubeN
    change InOpenHorizontalTube (1 / 2 : ℝ) (2 * scale n)
      (horizon n) increment
    intro k
    have hk := htubeN k
    change -(1 / 2 : ℝ) * (2 * narrowRadius * scale n) ≤
        AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment ≤
        (1 - (1 / 2 : ℝ)) * (2 * narrowRadius * scale n) at hk
    constructor <;> nlinarith [hwidthLt, hk.1, hk.2]
  have hmeasure :
      horizontalTubeProbability (iidSequenceLaw ν) (1 / 2)
          (2 * narrowRadius * scale n) (horizon n) ≤
        iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) (horizon n)) := by
    change iidSequenceLaw ν
        {increment : ℕ → ℝ |
          InHorizontalTube (1 / 2) (2 * narrowRadius * scale n)
            (horizon n) increment} ≤ _
    exact measure_mono hclosedSubset
  have hpow : 0 < lowerBound ^
      (horizon n / stableBlockLength α ν 1 scale n + 1) :=
    ENNReal.pow_pos hlower _
  exact hpow.trans_le (hbound.trans hmeasure)

/-- The finite-cell comparison transfers positivity of the base corridor to
positivity of the terminal-left endpoint corridor. -/
private lemma eventually_sourceEndpointCorridorEvent_pos_of_equation34
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (F : Finset SourceBridgeCenter) (lowerBound : ℝ)
    (hlowerBound : 0 < lowerBound)
    (ε c b : ℝ) (scale : ℕ → ℝ)
    (hcomparison : ∀ᶠ n in atTop,
      ENNReal.ofReal lowerBound * iidSequenceLaw ν
        (sourceBaseCorridorEvent (scale n) n) ≤
      (F.card : ℝ≥0∞) * iidSequenceLaw ν
        (sourceEndpointCorridorEvent (scale n) ε c b n))
    (hbase : ∀ᶠ n in atTop,
      0 < iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n)) :
    ∀ᶠ n in atTop,
      0 < (iidSequenceLaw ν
        (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal := by
  have hbaseToReal : ∀ᶠ n in atTop,
      0 < (iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n)).toReal := by
    filter_upwards [hbase] with n hn
    exact ENNReal.toReal_pos hn.ne' (measure_ne_top _ _)
  filter_upwards [hcomparison, hbase, hbaseToReal] with n hcomp hbaseN hbaseReal
  let μbase := iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n)
  let μtarget := iidSequenceLaw ν
    (sourceEndpointCorridorEvent (scale n) ε c b n)
  have hleft : 0 < ENNReal.ofReal lowerBound * μbase :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hlowerBound).ne' hbaseN.ne'
  have htarget : 0 < μtarget := by
    by_contra hnot
    have hzero : μtarget = 0 := le_antisymm (le_of_not_gt hnot) bot_le
    have hcomp' : ENNReal.ofReal lowerBound * μbase ≤ 0 := by
      simpa [μbase, μtarget, hzero] using hcomp
    exact (not_lt_of_ge hcomp') hleft
  exact ENNReal.toReal_pos htarget.ne' (measure_ne_top _ _)

/-- Once Mogul'skii's equation (34) comparison (Theorem 3, Section 4, p. 764
of the 1974 Russian original cited at the top of this file) is known,
base-corridor
positivity and endpoint-corridor decay give the logarithmic-ratio bound. -/
lemma eventually_one_sub_le_log_ratio_of_source_equation34
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (F : Finset SourceBridgeCenter) (hF : F.Nonempty)
    (lowerBound : ℝ) (hlowerBound : 0 < lowerBound)
    (ε c b : ℝ) (scale : ℕ → ℝ)
    (hcomparison : ∀ᶠ n in atTop,
      ENNReal.ofReal lowerBound * iidSequenceLaw ν
        (sourceBaseCorridorEvent (scale n) n) ≤
      (F.card : ℝ≥0∞) * iidSequenceLaw ν
        (sourceEndpointCorridorEvent (scale n) ε c b n))
    (hbase : ∀ᶠ n in atTop,
      0 < iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n))
    (htargetZero : Tendsto (fun n => (iidSequenceLaw ν
      (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal)
      atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      1 - δ ≤ Real.log ((iidSequenceLaw ν
        (sourceBaseCorridorEvent (scale n) n)).toReal) /
        Real.log ((iidSequenceLaw ν
          (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal) := by
  have htarget := eventually_sourceEndpointCorridorEvent_pos_of_equation34
    F lowerBound hlowerBound ε c b scale hcomparison hbase
  have hbaseReal : ∀ᶠ n in atTop,
      0 < (iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n)).toReal := by
    filter_upwards [hbase] with n hn
    exact ENNReal.toReal_pos hn.ne' (measure_ne_top _ _)
  exact Asymptotics.eventually_one_sub_le_log_ratio_of_mul_bound
    ((F.card : ℝ) / lowerBound)
    (div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hF)) hlowerBound)
    (by
      filter_upwards [hcomparison] with n hn
      have hleftTop : ENNReal.ofReal lowerBound * iidSequenceLaw ν
          (sourceBaseCorridorEvent (scale n) n) ≠ ⊤ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
      have hrightTop : (F.card : ℝ≥0∞) * iidSequenceLaw ν
          (sourceEndpointCorridorEvent (scale n) ε c b n) ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
      have hreal := (ENNReal.toReal_le_toReal hleftTop hrightTop).2 hn
      have hreal' : lowerBound *
          (iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n)).toReal ≤
          (F.card : ℝ) * (iidSequenceLaw ν
            (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal := by
        simpa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
          ENNReal.toReal_ofReal hlowerBound.le] using hreal
      have hdiv : (iidSequenceLaw ν
            (sourceBaseCorridorEvent (scale n) n)).toReal ≤
          ((F.card : ℝ) * (iidSequenceLaw ν
            (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal) /
              lowerBound := by
        apply (le_div_iff₀ hlowerBound).2
        simpa [mul_comm] using hreal'
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv)
    hbaseReal htarget htargetZero δ hδ



end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
