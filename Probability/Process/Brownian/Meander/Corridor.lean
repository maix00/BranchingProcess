/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Corridor.Upper
public import Mathlib.MeasureTheory.Measure.Support

/-!
# The open corridor used for Brownian meander

The public objects and theorems in this file are:

- `BrownianMeander.openCorridor`: the path event
  $\{f:\exists\varepsilon>0,\ \forall t,\
    f(t)\le(5/6-\rho)/\sigma-\varepsilon,\
    f(1)\in((5/12+\rho)/\sigma,(11/24-\rho)/\sigma)\}$.
- `BrownianMeander.isOpen_openCorridor`: this event is open in Skorokhod $J_1$.
- `BrownianMeander.straightPath_mem_openCorridor`: for
  $0<\rho<1/48$ and $\sigma>0$, the path $t\mapsto7t/(16\sigma)$ belongs
  to the corridor.
- `BrownianMeander.measure_openCorridor_pos_of_straightPath_mem_support`:
  if that straight path belongs to the support of a path law $\mathsf m$,
  then $\mathsf m(\mathcal U_{\sigma,\rho})>0$.

This is the open-set and support step in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3,
Lemma 3.5 and Appendix A.2, Lemma A.7. The positive-mass statement for the Brownian
meander law follows from the last-zero representation of Donald L. Iglehart,
*Functional Central Limit Theorems for Random Walks Conditioned to Stay
Positive*, Ann. Probab. 2(4) (1974), 608--619, DOI 10.1214/aop/1176996607, Section 3.
-/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace BrownianMeander

/-- The strict upper and terminal corridor in the meander argument of Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5 and Appendix A.2, Lemma A.7. -/
def openCorridor (sigma rho : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  Skorokhod.rangeBelowEndsIn
    ((5 / 6 - rho) / sigma)
    ((5 / 12 + rho) / sigma)
    ((11 / 24 - rho) / sigma)

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

/-- Any path law with the straight path $t\mapsto7t/(16\sigma)$ in its
support assigns positive mass to the meander corridor. This isolates the
support input used with Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5 and Appendix A.2, Lemma A.7. -/
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
