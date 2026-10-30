/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Algebra.Order.Floor.Semifield
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Basic

/-!
# Finite endpoint-window selection

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.exists_nearbyEndpointWindowIndex`:
  if $\varepsilon>0$ and $x\in[-3\varepsilon,3\varepsilon]$, some integer
  $i\in[-3,3]$ satisfies $x+i\varepsilon\in[0,\varepsilon]$. The finite
  index bound is specific to the seven endpoint windows used by the return
  kernel arguments.
-/

open Set

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow

/-- Every point in the return core is within one band width of one of the
seven integer shifts used by the lower block comparison. -/
lemma exists_nearbyEndpointWindowIndex {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Set.Icc (-3 * ε) (3 * ε)) :
    ∃ i ∈ Finset.Icc (-3 : ℤ) 3,
      x + (i : ℝ) * ε ∈ Set.Icc 0 ε := by
  let t : ℝ := x / ε + 3
  let j : ℕ := ⌊t⌋₊
  let i : ℤ := 3 - (j : ℤ)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    have hxdiv : -3 ≤ x / ε := (le_div_iff₀ hε).2 (by nlinarith [hx.1])
    linarith
  have ht6 : t ≤ 6 := by
    dsimp [t]
    have hxdiv : x / ε ≤ 3 := (div_le_iff₀ hε).2 (by nlinarith [hx.2])
    linarith
  have hjle : (j : ℝ) ≤ t := by
    dsimp [j]
    exact Nat.floor_le ht0
  have htlt : t < (j : ℝ) + 1 := by
    dsimp [j]
    exact Nat.lt_floor_add_one t
  have hjle6 : j ≤ 6 := by
    have hcast : (j : ℝ) ≤ 6 := hjle.trans ht6
    exact_mod_cast hcast
  refine ⟨i, ?_, ?_⟩
  · simp only [Finset.mem_Icc]
    constructor <;> dsimp [i] <;> omega
  · have hcast : (i : ℝ) = 3 - (j : ℝ) := by
      simp [i]
    rw [hcast]
    have hidentity : x + (3 - (j : ℝ)) * ε = ε * (t - (j : ℝ)) := by
      dsimp [t]
      field_simp [hε.ne']
      ring
    rw [hidentity]
    have hrem0 : 0 ≤ t - (j : ℝ) := by linarith
    have hrem1 : t - (j : ℝ) ≤ 1 := by linarith
    constructor
    · exact mul_nonneg hε.le hrem0
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left hrem1 hε.le

end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow

end
