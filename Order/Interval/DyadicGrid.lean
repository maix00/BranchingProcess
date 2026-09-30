module

public import Order.Interval.UniformGrid

@[expose] public section

/-!
# Dyadic finite grids

The dyadic grids are the nested unit-interval specializations of
`UniformGrid` with `2 ^ k` blocks.  Their finite and countable properties are
kept separate from the topology adapter that proves density in the unit
interval.
-/

open Set

namespace DyadicGrid

/-- The number of dyadic blocks at level `k`. -/
def blocks (k : ℕ) : ℕ := 2 ^ k

/-- The level-`k` dyadic grid on `[0, 1]`. -/
def grid (k : ℕ) : UniformGrid :=
  UniformGrid.unit (blocks k) (by
    dsimp [blocks]
    positivity)

theorem isRefinement_succ (k : ℕ) :
    UniformGrid.IsRefinement (grid k) (grid (k + 1)) := by
  refine ⟨rfl, rfl, ?_⟩
  change blocks k ∣ blocks (k + 1)
  dsimp [blocks]
  rw [pow_succ]
  exact dvd_mul_right _ _

/-- The canonical embedding of level-`k` indices into level `k+1`. -/
def lift (k : ℕ) : (grid k).Index → (grid (k + 1)).Index :=
  UniformGrid.refinementIndex (isRefinement_succ k)

theorem point_lift (k : ℕ) (j : (grid k).Index) :
    (grid (k + 1)).point (lift k j) = (grid k).point j := by
  exact UniformGrid.point_refinement (isRefinement_succ k) j

/-- The countable set of all dyadic grid points in the real line. -/
def points : Set ℝ := ⋃ k, Set.range (grid k).point

theorem countable_points : points.Countable := by
  unfold points
  exact Set.countable_iUnion fun k => Set.countable_range _

theorem zero_mem_points : (0 : ℝ) ∈ points := by
  refine mem_iUnion.mpr ⟨0, mem_range.mpr ⟨0, ?_⟩⟩
  exact UniformGrid.point_zero (grid 0)

theorem one_mem_points : (1 : ℝ) ∈ points := by
  refine mem_iUnion.mpr ⟨0, mem_range.mpr ⟨⟨blocks 0, by
    change blocks 0 < blocks 0 + 1
    exact Nat.lt_succ_self _⟩, ?_⟩⟩
  exact UniformGrid.point_last (grid 0)

end DyadicGrid
