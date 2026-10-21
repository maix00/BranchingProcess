/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Topology.Defs.Basic
public import Probability.Process.Brownian.Meander.Corridor
public import Topology.Cadlag.Skorokhod.Corridor.Endpoint

/-!
# Supporting facts for the meander corridor

The declarations in this proof module are specific to the corridor
`BrownianMeander.openCorridor` used in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5 and
Appendix A.2, Lemma A.7:

- `BrownianMeander.isOpen_openCorridor` proves that this event is open in the
  Skorokhod $J_1$ topology.
- `BrownianMeander.straightPath_mem_openCorridor` puts
  $t\mapsto 7t/(16\sigma)$ in this event when $\sigma>0$ and
  $0<\rho<1/48$.
- `BrownianMeander.measure_openCorridor_pos_of_straightPath_mem_support`
  gives positive measure to the event when that path belongs to the measure's
  support.

The last implication applies the definition of measure support to this
particular open set. The Brownian-meander support input comes from Donald L.
Iglehart, *Functional Central Limit Theorems for Random Walks Conditioned to
Stay Positive*, Ann. Probab. 2(4) (1974), 608--619, DOI
10.1214/aop/1176996607, Section 3, theorem (3.4), p. 616.
-/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace BrownianMeander

/-- The meander corridor is open in the Skorokhod path topology. -/
theorem isOpen_openCorridor (sigma rho : ℝ) :
    IsOpen (openCorridor sigma rho) :=
  Skorokhod.isOpen_rangeBelowEndsIn _ _ _

/-- The straight path through $7/(16\sigma)$ lies strictly inside the
meander corridor when $0<\rho<1/48$. -/
theorem straightPath_mem_openCorridor {sigma rho : ℝ}
    (hsigma : 0 < sigma) (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48) :
    Skorokhod.straightPath ((7 / 16) / sigma) ∈
      openCorridor sigma rho := by
  let y : ℝ := (7 / 16) / sigma
  let upper : ℝ := (5 / 6 - rho) / sigma
  have hypos : 0 ≤ y := (div_pos (by norm_num) hsigma).le
  have hyupper : y < upper := by
    dsimp [y, upper]
    exact (div_lt_div_iff_of_pos_right hsigma).2 (by linarith)
  have hleft : (5 / 12 + rho) / sigma < y := by
    dsimp [y]
    exact (div_lt_div_iff_of_pos_right hsigma).2 (by linarith)
  have hright : y < (11 / 24 - rho) / sigma := by
    dsimp [y]
    exact (div_lt_div_iff_of_pos_right hsigma).2 (by linarith)
  change Skorokhod.straightPath y ∈
    Skorokhod.rangeBelowEndsIn upper
      ((5 / 12 + rho) / sigma) ((11 / 24 - rho) / sigma)
  constructor
  · refine ⟨(upper - y) / 2, half_pos (sub_pos.mpr hyupper), fun t => ?_⟩
    have ht : (t : ℝ) ≤ 1 := t.property.2
    have hpath : y * (t : ℝ) ≤ y := by
      nlinarith [mul_nonneg hypos (sub_nonneg.mpr ht)]
    change y * (t : ℝ) ≤ upper - (upper - y) / 2
    linarith
  · simpa [Skorokhod.straightPath] using
      (show y ∈ Set.Ioo ((5 / 12 + rho) / sigma)
        ((11 / 24 - rho) / sigma) from ⟨hleft, hright⟩)

/-- Any path law whose support contains the straight path
$t\mapsto7t/(16\sigma)$ assigns positive mass to the meander corridor. -/
theorem measure_openCorridor_pos_of_straightPath_mem_support
    {mu : Measure (CadlagPath unitInterval ℝ)} {sigma rho : ℝ}
    (hsigma : 0 < sigma) (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈ mu.support) :
    0 < mu (openCorridor sigma rho) := by
  exact (Measure.mem_support_iff_forall _).1 hsupport _
    ((isOpen_openCorridor sigma rho).mem_nhds
      (straightPath_mem_openCorridor hsigma hrho hrhoSmall))

end BrownianMeander

end
