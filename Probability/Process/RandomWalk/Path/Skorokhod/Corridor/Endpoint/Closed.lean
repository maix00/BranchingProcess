/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Skorokhod.Corridor.Endpoint.Basic

/-!
# Closed endpoint corridors for step paths

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.normalizedStepCadlagPathIcc_mem_rangeInClosedIntervalEndsIn_iff_grid`:
  for $a\le0\le b$ and $n>0$, the normalized step path lies in
  $[a,b]$ at all times with terminal value in $[u,v]$ exactly when
  its positive grid values lie in $[a,b]$ and its normalized final
  partial sum lies in $[u,v]$.

This is the finite-grid identification used for $D_{N,\Delta}^{\theta}$
in Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with
infinite offspring*, Chapter 3, Lemma 3.5, Appendix A.2.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A closed endpoint corridor for the normalized step path is exactly
its finite-grid event together with the normalized endpoint condition. -/
theorem normalizedStepCadlagPathIcc_mem_rangeInClosedIntervalEndsIn_iff_grid
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lower upper endpointLower endpointUpper : ℝ}
    (hlower : lower ≤ 0) (hupper : 0 ≤ upper)
    (increment : ℕ → ℝ) :
    normalizedStepCadlagPathIcc scale n increment ∈
        Skorokhod.rangeInClosedIntervalEndsIn
          lower upper endpointLower endpointUpper ↔
      InClosedCorridorOnGrid scale n (fun _ => lower) (fun _ => upper)
        increment ∧
      AdditivePath.displacement n increment / scale n ∈
        Set.Icc endpointLower endpointUpper := by
  rw [Skorokhod.mem_rangeInClosedIntervalEndsIn_iff,
    normalizedStepCadlagPathIcc_mem_rangeInClosedInterval_iff_grid
      scale hn hlower hupper]
  change _ ∧ normalizedStepPath scale n increment 1 ∈ _ ↔ _
  rw [normalizedStepPath_one, inv_mul_eq_div]

end ProbabilityTheory.RandomWalk

end
