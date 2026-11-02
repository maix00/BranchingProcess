/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Topology.Cadlag.Skorokhod.EDistance.Logarithmic.Basic

/-!
# Internal threshold selection for the logarithmic conversion modulus

## Internal proof declarations

- `Skorokhod.Separation.Lemmas.exists_small_logarithmicJ1_bound`: for every
  $\varepsilon>0$, there is $b$ with $0<b<\varepsilon$ and
  `logarithmicJ1Modulus b < ε`.

This continuity-based threshold choice is used by the metric-separation proof
and the path-space metric instance. Mathlib's neighborhood and continuity
primitives provide the general argument; the modulus-specific selection is
kept as an internal proof lemma.
-/

open Filter
open scoped ENNReal Topology

namespace Skorokhod

namespace Separation

namespace Lemmas

/-- Choose a positive logarithmic cost threshold below a prescribed tolerance
whose `J₁` conversion modulus is also below that tolerance. -/
lemma exists_small_logarithmicJ1_bound {tolerance : ℝ}
    (htolerance : 0 < tolerance) :
    ∃ bound : ℝ, 0 < bound ∧ bound < tolerance ∧
      logarithmicJ1Modulus bound < tolerance := by
  have hnear :
      {x : ℝ | logarithmicJ1Modulus x ∈ Metric.ball (0 : ℝ) tolerance} ∈
        𝓝 (0 : ℝ) := by
    have hcont : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ),
        logarithmicJ1Modulus x ∈ Metric.ball (0 : ℝ) tolerance := by
      simpa [logarithmicJ1Modulus_zero] using
        continuous_logarithmicJ1Modulus.continuousAt.eventually
          (Metric.ball_mem_nhds (logarithmicJ1Modulus 0) htolerance)
    filter_upwards [hcont] with x hx
    exact hx
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let bound : ℝ := min (radius / 2) (tolerance / 2)
  have hbound : 0 < bound := by
    dsimp [bound]
    exact lt_min (by positivity) (by positivity)
  refine ⟨bound, hbound, ?_, ?_⟩
  · dsimp [bound]
    exact (min_le_right _ _).trans_lt (half_lt_self htolerance)
  · have hbound_radius : bound ∈ Metric.ball (0 : ℝ) radius := by
      rw [Metric.mem_ball, Real.dist_eq]
      simp only [sub_zero, abs_of_pos hbound]
      dsimp [bound]
      exact (min_le_left _ _).trans_lt (half_lt_self hradius)
    have hmod_ball := hball hbound_radius
    change logarithmicJ1Modulus bound ∈ Metric.ball (0 : ℝ) tolerance at hmod_ball
    rw [Metric.mem_ball, Real.dist_eq] at hmod_ball
    exact (le_abs_self _).trans_lt (by simpa [sub_zero] using hmod_ball)

end Lemmas

end Separation

end Skorokhod
