/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Interpolation.Basic
public import Probability.Process.RandomWalk.Path.Interpolation.Core
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Closed endpoint corridors for polygonal paths

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.normalizedLinearCadlagPathIcc_mem_rangeInClosedIntervalEndsIn_iff_grid`:
  for $a\le0\le b$ and $n>0$, the polygonal interpolation belongs to
  $\{f:f([0,1])\subseteq[a,b],\ f(1)\in[u,v]\}$ exactly when every
  normalized positive grid value belongs to $[a,b]$ and the normalized
  final partial sum belongs to $[u,v]$.

This identifies the finite-grid transition event in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.5, and Appendix A.2, Lemma A.7, with the event of the
polygonal path.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A closed endpoint corridor for the polygonal path is exactly its
finite-grid event together with the normalized endpoint condition. -/
theorem normalizedLinearCadlagPathIcc_mem_rangeInClosedIntervalEndsIn_iff_grid
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lower upper endpointLower endpointUpper : ℝ}
    (hlower : lower ≤ 0) (hupper : 0 ≤ upper)
    (increment : ℕ → ℝ) :
    normalizedLinearCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInClosedIntervalEndsIn
          lower upper endpointLower endpointUpper ↔
      InClosedCorridorOnGrid scale n (fun _ => lower) (fun _ => upper)
        increment ∧
      AdditivePath.displacement n increment / scale n ∈
        Set.Icc endpointLower endpointUpper := by
  rw [Skorokhod.mem_rangeInClosedIntervalEndsIn_iff]
  simp only [Skorokhod.rangeInClosedInterval, Set.mem_ofPred_eq,
    normalizedLinearCadlagPathIcc_apply]
  rw [show (∀ t : unitInterval,
      lower ≤ normalizedLinearPath scale n increment t ∧
        normalizedLinearPath scale n increment t ≤ upper) ↔
      normalizedLinearContinuousPathIcc scale n increment ∈
        ContinuousMap.rangeInClosedInterval lower upper from
      (by simpa only [normalizedLinearContinuousPathIcc_apply] using
        (ContinuousMap.mem_rangeInClosedInterval_iff
          (path := normalizedLinearContinuousPathIcc scale n increment)).symm)]
  have htop : ((⊤ : unitInterval) : ℝ) = 1 := rfl
  rw [htop]
  rw [normalizedLinearContinuousPathIcc_mem_rangeInClosedInterval_iff
    scale hn hlower hupper]
  simp only [normalizedLinearPath_one, inv_mul_eq_div]

end ProbabilityTheory.RandomWalk

end
