/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.Bridge.Lemmas.Comparison
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.Bridge.Events
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.TerminalLeft.Bounds.Lower
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.Endpoint.StrictStable
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Partition
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.Bridge.Lemmas.TerminalLeftAsymptotics

/-! # Mogul'skii equation (34) asymptotics

This module proves the logarithmic-ratio consequence of equation (34),
Theorem 3, Section 4,
p. 764 of the 1974 Russian original by A. A. Mogul'skii, “Small deviations in
the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4)
(1974), 755–765; English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975),
726–736, DOI 10.1137/1119081.

The public theorem is `exists_source_equation34_log_ratio_lower_of_stableDomain`.
Writing
$B_n=\mathrm{iidSequenceLaw}(\nu)(\mathrm{sourceBaseCorridorEvent}(s_n,n))$
and
$E_n=\mathrm{iidSequenceLaw}(\nu)(\mathrm{sourceEndpointCorridorEvent}(s_n,\varepsilon,c,b,n))$,
for every $\delta>0$ it produces a finite nonempty center set and $q_0>0$
such that, eventually,

$$
1-\delta\le\frac{\log(B_n.\mathrm{toReal})}{\log(E_n.\mathrm{toReal})}.
$$

Here $s_n$ is the supplied corridor scale. The exact comparison is equation
(34), Theorem 3, Section 4, p. 764 of the cited source.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Mogul'skii's equation (34), Theorem 3, Section 4, p. 764 of the 1974
Russian original cited at the top of this file, followed by the
logarithmic-ratio conclusion.

The bridge limit is supplied in the existing variable-block stable path-law
interface. The finite-prefix cover, the source bridge cells, their IID path
identification, and the finite-cell gluing are proved in the companion
`Bridge/Lemmas` modules. Base-corridor
positivity follows from the existing stable-domain return lower bound; target
decay follows from the strict-stable endpoint upper bound when `L*` has a
positive finite limit. The `α < 1` case is discharged by
`IsStableLevyProcess.measure_fullEntrance_pos_indexLTOne`, whose public
statement hides the Lévy--Khintchine triple used by its finite-variation
Poisson construction in
`Stable/SmallDeviation/Blocks/Lower/Entrance/PoissonModel.lean`. -/
theorem exists_source_equation34_log_ratio_lower_of_stableDomain
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α : ℝ} {normalization scale : ℕ → ℝ}
    {Ω' : Type*} [MeasurableSpace Ω']
    {X : ℝ≥0 → Ω' → ℝ} {Q : Measure Ω'} [IsProbabilityMeasure Q]
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hX : IsStableLevyProcess α μ X Q)
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (htight : IsTightMeasureSet (Set.range
      (fun n => RandomWalk.normalizedStepPathLaw ν normalization n)))
    (hnorm : IsStableNorming α ν normalization)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα₂ : α < 2)
    {ell : ℝ} (hell : 0 < ell)
    (hslowLimit : Tendsto (stableSlowVariation α ν) atTop (𝓝 ell))
    (ε c b : ℝ) (hε : 0 < ε) (hc : -1 < c)
    (hcb : c < b) (hb : b < 1)
    (bridgeLength : ℕ → ℕ)
    (hscaleAll : ∀ n, 0 < scale n)
    (hbridgeLe : ∀ n, bridgeLength n ≤ n)
    (hbridgePos : ∀ᶠ n in atTop, 0 < bridgeLength n)
    (hlow : α < 1 → ∀ radius y : ℝ, 0 < radius → -1 < y → y < 1 →
      ∀ x : SourceBridgeCenter,
        0 < Q (fullSegmentCorridorReturnEvent X 0 1
          (-1 - x.1) (1 - x.1) (y - x.1 - radius) (y - x.1 + radius)))
    (hlimit : TendstoInDistribution
      (RandomWalk.normalizedStepBlockCadlagPathIcc scale bridgeLength)
      atTop id (fun _ => iidSequenceLaw ν) P)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : Finset SourceBridgeCenter, ∃ lowerBound : ℝ,
      F.Nonempty ∧ 0 < lowerBound ∧
      ∀ᶠ n in atTop,
        1 - δ ≤ Real.log ((iidSequenceLaw ν
          (sourceBaseCorridorEvent (scale n) n)).toReal) /
          Real.log ((iidSequenceLaw ν
            (sourceEndpointCorridorEvent (scale n) ε c b n)).toReal) := by
  have hα : 0 < α := hP.strictlyStable.1
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
    tendsto_sourceEndpointCorridor_toReal_zero_of_strictStableDomain
      ν μ hα hP.strictlyStable hα₂ hnorm hDOA hscale
      (ell := ell) hell hslowLimit ε c b hε
  have hratio := eventually_one_sub_le_log_ratio_of_source_equation34
    F hF lowerBound hlowerBound ε c b scale hcomparison hbase htargetZero δ hδ
  exact ⟨F, lowerBound, hF, hlowerBound, hratio⟩



end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
