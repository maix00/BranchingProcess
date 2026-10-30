/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Probability.Distributions.DomainOfAttraction.Basic
public import Probability.Distributions.Stable.Attraction.Norming.Rescaling.Mogulskii
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Basic
import Probability.Distributions.Stable.Attraction.Normal.Norming

/-!
# Gaussian normalization from raw domain-of-attraction data

For a source normalization $a_n$ with an eventual positivity condition, this
construction changes only its finite initial segment. It produces $a'_n>0$ for
every $n$, with $a'_n=a_n$ eventually, and preserves both the Gaussian
attraction limit and the small-deviation-scale relation.

## Public declarations

- `exists_source_gaussian_mogulskii_inputs`: if the source-normalized sums
  converge to the standard Gaussian along a small-deviation scale, it provides
  a positive stable Mogul'skii normalization $a'_n$ with $a'_n=a_n$ eventually
  and the same Gaussian attraction limit.

This construction supplies normalized inputs for A. A. Mogul'skii,
Theorem 3, Section 4, p. 764, “Small deviations in the sample function space,”
*Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English
translation, “Small Deviations in a Space of Trajectories,” *Theory of
Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081.
The rate formalized from those inputs is Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i).
-/

open Filter MeasureTheory
open scoped NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- The Gaussian-domain counterpart of
`exists_source_reindexed_mogulskii_inputs`.  At index two, the source
normalization is already a stable norming.  We repair only its finite prefix
so positivity holds at every positive index, retaining the same sequence
eventually and therefore the same small-deviation comparison. -/
theorem exists_source_gaussian_mogulskii_inputs
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hsmall : Asymptotics.IsSmallDeviationScale scale normalization)
    (hDOA : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization (fun _ => 0)) :
    ∃ normalization' : ℕ → ℝ,
      IsStableMogulskiiScale 2 ν normalization' scale ∧
      normalization' =ᶠ[atTop] normalization ∧
      IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
        normalization' (fun _ => 0) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hDOA.eventually_scale_pos
  let normalization' : ℕ → ℝ := fun n =>
    if N ≤ n then normalization n else 1
  have hnormalization'pos : ∀ n, 0 < normalization' n := by
    intro n
    by_cases hn : N ≤ n
    · simpa [normalization', hn] using hN n hn
    · simp [normalization', hn]
  have hnormalization'eventually : normalization' =ᶠ[atTop] normalization := by
    filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hn⟩] with n hn
    simp [normalization', hn]
  have hDOA' : IsInDomainOfAttractionAlong ν (gaussianReal 0 1)
      normalization' (fun _ => 0) := by
    refine ⟨Filter.Eventually.of_forall hnormalization'pos, ?_⟩
    have hsumEq : ∀ᶠ n : ℕ in atTop,
        (fun ω => normalizedIidSum normalization (fun _ => 0) n ω) =ᵐ[iidSequenceLaw ν]
          normalizedIidSum normalization' (fun _ => 0) n := by
      filter_upwards [hnormalization'eventually] with n hn
      filter_upwards [] with ω
      simp [normalizedIidSum, hn]
    exact hDOA.tendstoInDistribution.congr_eventually hsumEq
      (fun n => (normalizedIidSum_measurable normalization' (fun _ => 0) n).aemeasurable)
  have hnorm : IsStableNorming 2 ν normalization' :=
    hDOA'.isStableNorming_two_of_gaussian (fun n _ => hnormalization'pos n)
  have hsmall' := hsmall.of_tendsto_normalization_ratio
    hDOA.eventually_scale_pos
    (by
      have heq : (fun n => normalization' n / normalization n) =ᶠ[atTop]
          fun _ => 1 := by
        filter_upwards [hDOA.eventually_scale_pos,
          hnormalization'eventually] with n hpos hn
        rw [hn]
        exact div_self (ne_of_gt hpos)
      exact tendsto_const_nhds.congr' heq.symm)
    one_pos
  exact ⟨normalization', ⟨hnorm, hsmall'⟩, hnormalization'eventually, hDOA'⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
