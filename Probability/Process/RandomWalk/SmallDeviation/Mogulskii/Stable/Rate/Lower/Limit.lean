/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Rate.Lower.Liminf
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Rate.Lower.Positivity
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Rate.Upper

/-!
# Stable horizontal-tube rate limit

Let $(\xi_i)_{i\geq1}$ be i.i.d. with law $\nu$, put
$S_j=\sum_{i=1}^j\xi_i$, and let $\mathbb P_\nu$ denote their product law.
Write $s_n=\mathrm{scale}(n)$,
$L^*(x)=\mathrm{stableSlowVariation}(\alpha,\nu)(x)$,
$a_n=\frac{s_n^\alpha}{nL^*(s_n)}$, and
$T_n=\{|S_j|<s_n/2\text{ for }1\leq j\leq n\}$.
Assume $0<\alpha\leq2$, a stable Mogulskii scale, $a_n\to0$, slow variation
of $L^*$, the stable-process escape-rate hypothesis with constant $C$, and the
stated domain-of-attraction, tightness, and endpoint-sign conditions. The
public declaration is:

- `tendsto_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_of_escapeRate`:
  $a_n\log\mathbb P_\nu(T_n)\to\frac{C}{(1/2)^\alpha}$.

This is the stable horizontal-tube limit in Theorem 3, Section 4 of
A. A. Mogul'skii, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable

/-- The two rate bounds identify the stable centered horizontal-tube limit
of A. A. Mogul'skii, *Small Deviations in a Space of Trajectories*,
Theorem 3, Section 4 (DOI 10.1137/1119081). The only scale assumption on
`L*` is slow variation. -/
theorem tendsto_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_of_escapeRate
    {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    {α C : ℝ} {normalization scale : ℕ → ℝ}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hα : 0 < α) (hα₂ : α ≤ 2)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν))
    (hrate : Tendsto (stableSmallDeviationRate α ν scale)
      atTop (𝓝 0))
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (htightBase : IsTightMeasureSet (Set.range
      fun n => RandomWalk.normalizedStepPathLaw ν normalization n)) :
    Tendsto (fun n => stableSmallDeviationRate α ν scale n *
      Real.log (openHorizontalTubeProbability (iidSequenceLaw ν)
        (1 / 2) (scale n) n).toReal) atTop
      (𝓝 (C / ((1 / 2 : ℝ) ^ α))) := by
  have hside := stableEscapeRate_eventually_positive_and_log_cobounded
    hscale hα hα₂ hslow hrate hEscape hX hcdf hDOA htightBase
  have hlower := stableEscapeRate_liminf_lower
    hscale hα hα₂ hslow hrate hEscape hX hcdf hDOA htightBase
  have hupper :=
    limsup_stableSmallDeviationRate_mul_log_openHorizontalTubeProbability_le
      hscale hα hα₂ hslow hEscape hDOA htightBase
      hside.1 hside.2.1
  exact tendsto_of_le_liminf_of_limsup_le hlower hupper
    hside.2.2.2 hside.2.2.1

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable

end
