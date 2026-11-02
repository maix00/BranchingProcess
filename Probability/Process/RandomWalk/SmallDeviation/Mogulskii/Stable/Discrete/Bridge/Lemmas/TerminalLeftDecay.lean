/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Bridge.Lemmas.EndpointCorridorDecay
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Bridge.Lemmas.TerminalLeftAsymptotics
import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Entrance.AllIndices
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate
import Probability.Process.Stable.PathLaw.Basic
import Probability.Process.RandomWalk.Path.Skorokhod.Core
import Probability.Process.RandomWalk.FunctionalLimit.NormalizedStep.Block
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Bridge.Events
import all Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.Bridge.Lemmas.TerminalLeftGeometry

/-! # Terminal-left logarithmic comparison lemma

The internal support lemma
`ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_source_equation34_log_ratio_lower_of_stableDomain_slowVariation`
gives Mogul'skii's equation-(34) logarithmic comparison under the stable-domain
hypotheses of A. A. Mogul'skii, “Small deviations in the sample function
space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765;
English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081, Theorem 3, Section 4. It yields the endpoint-corridor
decay from slow variation and the two-scale condition, without imposing
a finite-limit assumption on $L^*$.

## Internal proof declarations

* `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.eventually_source_equation34_log_ratio_lower_of_stableDomain_slowVariation`:
  for every $\delta>0$, the following inequality holds eventually in $n$:
\[
  1-\delta \leq
    \frac{\log\mathbb{P}_\nu(B_n)}{\log\mathbb{P}_\nu(E_n)},
\]
where the events are
$B_n=\texttt{sourceBaseCorridorEvent}(\texttt{scale}(n),n)$ and
$E_n=\texttt{sourceEndpointCorridorEvent}(\texttt{scale}(n),\varepsilon,c,b,n)$;
$\mathbb P_\nu$ is the law `iidSequenceLaw ν`.
-/

section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The equation-(34) logarithmic comparison under the stable-domain
hypotheses of Mogul'skii, *Small Deviations in a Space of Trajectories*,
Theorem 3, Section 4, with no extra finite-limit assumption on `L*`. The proof assembles the finite-bridge comparison, base-corridor positivity,
and endpoint-corridor decay estimates. The all-index stable entrance theorem
supplies bridge positivity under the CDF condition, including $0<\alpha<1$;
slow variation and the two-scale condition supply the endpoint probability
decay. -/
lemma eventually_source_equation34_log_ratio_lower_of_stableDomain_slowVariation
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    {Ω' : Type*} [MeasurableSpace Ω']
    {X : ℝ≥0 → Ω' → ℝ} {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hX : IsStableLevyProcess α μ X Q)
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hnorm : IsStableNorming α ν normalization)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα₂ : α < 2)
    (ε c b : ℝ) (hε : 0 < ε) (hc : -1 < c)
    (hcb : c < b) (hb : b < 1)
    (bridgeLength : ℕ → ℕ)
    (hscaleAll : ∀ n, 0 < scale n)
    (hbridgeLe : ∀ n, bridgeLength n ≤ n)
    (hbridgePos : ∀ᶠ n in atTop, 0 < bridgeLength n)
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale bridgeLength)
      atTop id (fun _ => iidSequenceLaw ν) P)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      1 - δ ≤ Real.log ((iidSequenceLaw ν
        (sourceBaseCorridorEvent (scale n) n)).toReal) /
        Real.log ((iidSequenceLaw ν
        (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal) := by
  have hα : 0 < α := hP.strictlyStable.1
  have hlow : α < 1 → ∀ radius y : ℝ, 0 < radius → -1 < y → y < 1 →
      ∀ x : SourceBridgeCenter,
        0 < Q (fullSegmentCorridorReturnEvent X 0 1
          (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)) := by
    intro _ radius y hradius hylo hyhi x
    convert hX.measure_fullEntrance_pos_of_cdfAtZero_allIndices hcdf
      (-y) (-x.1) radius
      (by constructor <;> linarith [hylo, hyhi])
      (by constructor <;> linarith [x.2.1, x.2.2]) hradius using 1
    ring_nf
  obtain ⟨F, lowerBound, hF, hlowerBound, hcomparison⟩ :=
    exists_source_equation34_finite_bridge_comparison_of_cdf
      hX hP hcdf ε c b hε hc hcb hb scale bridgeLength hscaleAll
      hbridgeLe hbridgePos hlow hlimit
  have hbase : ∀ᶠ n in atTop,
      0 < iidSequenceLaw ν (sourceBaseCorridorEvent (scale n) n) :=
    eventually_sourceBaseCorridorEvent_pos_of_stableDomain
      hDOA hP hX hcdf htight hnorm hα hα₂ hscale.scale_tendsto_atTop
  have htargetZero : Tendsto (fun n => (iidSequenceLaw ν
      (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal)
      atTop (𝓝 0) :=
    tendsto_sourceEndpointCorridor_toReal_zero_of_strictStableDomain_slowVariation
      ν μ hα hP.strictlyStable hα₂ hnorm hDOA hscale ε c b hε
  have hratio := eventually_one_sub_le_log_ratio_of_source_equation34
    F hF lowerBound hlowerBound ε c b scale hcomparison hbase htargetZero δ hδ
  exact hratio

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete
