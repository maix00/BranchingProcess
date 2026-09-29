module

public import Combinatorics.BranchingWalk.Walk.Path.Corridor.Horizontal
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Finite reference covers of real intervals

A closed real interval admits a finite family of reference points in a
smaller concentric corridor such that every point of the original interval is
within the corridor margin of one reference point.
-/

open Metric Set

@[expose] public section

namespace Combinatorics.Branching.Walk

/-- If the interval remains nonempty after removing `margin` at both ends,
then the original interval has a finite `margin`-cover whose reference points
all lie in that smaller interval. -/
theorem exists_finset_Icc_cover_inside
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

end Combinatorics.Branching.Walk
