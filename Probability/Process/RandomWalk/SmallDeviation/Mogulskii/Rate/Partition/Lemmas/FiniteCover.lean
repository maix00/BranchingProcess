/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# Finite reference covers of real intervals

## Internal proof declarations

`exists_finset_Icc_cover_inside` states that, if $m>0$ and
$\ell+m\le u-m$, there is a finite set $F\subseteq[\ell+m,u-m]$ such that
\[
  \forall x\in[\ell,u],\quad \exists y\in F,\quad |x-y|\le m.
\]
The construction is used only by the finite-partition lower-rate proof.
-/

open Metric Set

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- If the interval remains nonempty after removing `margin` at both ends,
then the original interval has a finite `margin`-cover whose reference points
all lie in that smaller interval. -/
lemma exists_finset_Icc_cover_inside
    {lower upper margin : ℝ} (hmargin : 0 < margin)
    (hinside : lower + margin ≤ upper - margin) :
    ∃ references : Finset ℝ,
      (∀ y ∈ references,
        y ∈ Set.Icc (lower + margin) (upper - margin)) ∧
      ∀ x ∈ Set.Icc lower upper,
        ∃ y ∈ references, |x - y| ≤ margin := by
  classical
  let inside := Set.Icc (lower + margin) (upper - margin)
  obtain ⟨net, hnetInside, hnetFinite, hnetCover⟩ :=
    Metric.finite_approx_of_totallyBounded
      (isCompact_Icc.totallyBounded : TotallyBounded inside)
      margin hmargin
  let references : Finset ℝ :=
    hnetFinite.toFinset ∪ {lower + margin, upper - margin}
  refine ⟨references, ?_, ?_⟩
  · intro y hy
    simp only [references, Finset.mem_union, Set.Finite.mem_toFinset,
      Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with hy | hy | hy
    · exact hnetInside hy
    · simpa [hy] using hinside
    · simpa [hy] using hinside
  · intro x hx
    by_cases hxLower : x < lower + margin
    · refine ⟨lower + margin, ?_, ?_⟩
      · simp [references]
      · rw [abs_le]
        constructor <;> linarith [hx.1]
    by_cases hxUpper : upper - margin < x
    · refine ⟨upper - margin, ?_, ?_⟩
      · simp [references]
      · rw [abs_le]
        constructor <;> linarith [hx.2]
    have hxInside : x ∈ inside := ⟨le_of_not_gt hxLower, le_of_not_gt hxUpper⟩
    have hxCovered := hnetCover hxInside
    simp only [Set.mem_iUnion, Metric.mem_ball] at hxCovered
    obtain ⟨y, hyNet, hyDist⟩ := hxCovered
    refine ⟨y, ?_, ?_⟩
    · simp [references, hnetFinite.mem_toFinset.2 hyNet]
    · simpa [Real.dist_eq] using hyDist.le

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
