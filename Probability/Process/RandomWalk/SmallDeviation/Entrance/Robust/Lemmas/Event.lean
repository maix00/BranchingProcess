/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.Robust.Event

/-!
# Interior inclusion for the robust entrance event

Write $S_j=\sum_{i=0}^{j-1}\xi_i$ for the partial sums of the increments,
$h_j=cj/\Delta^2$ for the moving-boundary displacement, and $x$ for the
starting point. The module-visible lemma in this file is:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteInteriorEvent_subset_robustMovingTransitionEvent`:
  if $\Delta>0$, $c\ge0$, $n\le\Delta^2$, and $60c\le\Delta$, then
  $\mathcal I_{n,\Delta,c}(x)\subseteq\mathcal R_{n,\Delta,c}(x)$, where
  $\mathcal I_{n,\Delta,c}(x)=\{\xi:c\le x+S_j\le\Delta\ (1\le j\le n),\
  x+S_n\in[5\Delta/12,7\Delta/12]\}$.

The proofs support Wang Yiyang, *Asymptotic Speed of the N-Branching Random
Walk with Infinite Offspring* (master's thesis, Fudan University, 2026),
Chapter 3, Lemma 3.5, and use the fixed window in Appendix A.2, Lemma A.7.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The Brownian interior-corridor event fits the stronger endpoint window
when the drift over the diffusive entrance is small compared with its width. -/
lemma finiteInteriorEvent_subset_robustMovingTransitionEvent
    {n : ℕ} {width drift start : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hn : (n : ℝ) ≤ width ^ 2)
    (hlarge : 60 * drift ≤ width) :
    FunctionalLimit.Donsker.Entrance.finiteInteriorEvent n width drift start ⊆
      robustMovingTransitionEvent n width drift start := by
  intro increment hinc
  have hmove := finiteInteriorEvent_subset_movingCorridorEvent
    hwidth hdrift hn hinc
  have hsq : 0 < width ^ 2 := sq_pos_of_pos hwidth
  have hshift : drift * (n : ℝ) / width ^ 2 ≤ drift := by
    exact (div_le_iff₀ hsq).2
      (mul_le_mul_of_nonneg_left hn hdrift)
  have hshiftNonneg : 0 ≤ drift * (n : ℝ) / width ^ 2 := by positivity
  refine ⟨hmove, ?_⟩
  exact ⟨by nlinarith [hinc.2.1, hshift, hlarge],
    by nlinarith [hinc.2.2, hshiftNonneg, hwidth]⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
