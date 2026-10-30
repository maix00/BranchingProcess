/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Attraction.Norming.Asymptotics.Centering
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathLaw.Convergence
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.Tightness.Result

/-!
# Stable random-walk functional limits

These results combine stable finite-grid convergence with the proved stable
tightness criteria below, at, and above index one.
## Public declarations

Let $S_m=\sum_{i=0}^{m-1}X_i$ for IID increments of law $\nu$,
$a_n=\texttt{normalization}(n)$, and
\[
 Q_n=\operatorname{Law}_\nu\!\left(t\mapsto
   \frac{S_{\lfloor nt\rfloor}}{a_n}\right),
 \qquad P=\operatorname{Law}(X),
\]
where $X$ has the specified stable clock-process law. The following results
prove convergence in distribution on the Skorokhod $J_1$ path space:

- `tendsto_normalizedStepPathLaw_of_index_lt_one` proves
  $Q_n\Longrightarrow_{J_1}P$ for $0<\alpha<1$, under zero-centered scalar
  attraction, stable norming, and the two-sided regularly varying tail.
- `tendsto_normalizedStepPathLaw_of_index_one` proves
  $Q_n\Longrightarrow_{J_1}P$ for $\alpha=1$, under zero-centered scalar
  attraction, stable norming, the two-sided tail condition, and Mogulskii's
  sine-centering condition
  $n\int_{\mathbb R}\sin(x/a_n)\,\nu(dx)\to0$.
- `tendsto_normalizedStepPathLaw_of_index_gt_one` proves
  $Q_n\Longrightarrow_{J_1}P$ for $1<\alpha<2$ from zero-centered scalar
  attraction and stable norming; these assumptions yield the tail, integrable
  increments, and zero mean required by the tightness theorem.

-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

variable {ν μ : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
  {α : ℝ} {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
  {normalization : ℕ → ℝ}

/-- The uncentered stable random walk converges in J1 below index one.
The scalar domain-of-attraction hypothesis uses zero centering; the remaining
tail and norming hypotheses supply the already established J1 tightness. -/
theorem tendsto_normalizedStepPathLaw_of_index_lt_one
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-α)) :
    Tendsto (fun n : ℕ =>
      (⟨RandomWalk.normalizedStepPathLaw ν normalization n,
        (inferInstance : IsProbabilityMeasure
          (RandomWalk.normalizedStepPathLaw ν normalization n))⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
        (⟨P, (inferInstance : IsProbabilityMeasure P)⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) := by
  exact tendsto_normalizedStepPathLaw_of_zeroCenter_stableDomain_of_tight
    hDOA hP
    (isTightMeasureSet_range_normalizedStepPathLaw_of_index_lt_one
      hnorm hα₀ hα₁ htail)

/-- The uncentered stable random walk converges in J1 at index one under the
source sine-centering convention. The scalar domain-of-attraction hypothesis
uses zero centering, and the sine-centering condition supplies J1 tightness. -/
theorem tendsto_normalizedStepPathLaw_of_index_one
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw 1 μ unitInterval.clock P)
    (hnorm : IsStableNorming 1 ν normalization)
    (htail : Asymptotics.IsRegularlyVaryingAtTop
      (fun u : ℝ => ν.real {x : ℝ | u < |x|}) (-1))
    (hcenter : IsMogulskiiIndexOneCentered ν normalization) :
    Tendsto (fun n : ℕ =>
      (⟨RandomWalk.normalizedStepPathLaw ν normalization n,
        (inferInstance : IsProbabilityMeasure
          (RandomWalk.normalizedStepPathLaw ν normalization n))⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
        (⟨P, (inferInstance : IsProbabilityMeasure P)⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) := by
  exact tendsto_normalizedStepPathLaw_of_zeroCenter_stableDomain_of_tight
    hDOA hP
    (isTightMeasureSet_range_normalizedStepPathLaw_of_index_one
      hnorm htail hcenter)

/-- The uncentered stable random walk converges in J1 above index one. The
zero-centered scalar domain-of-attraction hypothesis forces zero mean; its
tail regular variation supplies the first moment and the J1 tightness input. -/
theorem tendsto_normalizedStepPathLaw_of_index_gt_one
    (hDOA : IsInDomainOfAttractionAlong ν μ normalization (fun _ => 0))
    (hP : IsStableClockProcessLaw α μ unitInterval.clock P)
    (hnorm : IsStableNorming α ν normalization)
    (hα₀ : 0 < α) (hα₁ : 1 < α) (hα₂ : α < 2) :
    Tendsto (fun n : ℕ =>
      (⟨RandomWalk.normalizedStepPathLaw ν normalization n,
        (inferInstance : IsProbabilityMeasure
          (RandomWalk.normalizedStepPathLaw ν normalization n))⟩ :
        ProbabilityMeasure (CadlagPath unitInterval ℝ)))
      atTop (@nhds (ProbabilityMeasure (CadlagPath unitInterval ℝ)) inferInstance
        (⟨P, (inferInstance : IsProbabilityMeasure P)⟩ :
          ProbabilityMeasure (CadlagPath unitInterval ℝ))) := by
  have hlimit : IsAlphaStable α μ := hP.strictlyStable.isAlphaStable
  have htail := hDOA.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂
  have hint : Integrable (fun x : ℝ => x) ν :=
    integrable_id_of_twoSidedTail_regularlyVarying hα₁ htail
  have hmean := hDOA.integral_eq_zero_of_index_gt_one
    hlimit hnorm hα₁ hα₂
  exact tendsto_normalizedStepPathLaw_of_zeroCenter_stableDomain_of_tight
    hDOA hP
    (isTightMeasureSet_range_normalizedStepPathLaw_of_index_gt_one
      hnorm hα₀ hα₁ hα₂ htail hint hmean)

end ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

end
