/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Walk.Cloud
public import Combinatorics.BranchingWalk.Cloud.Frontier
public import Order.OrderDual.SetExtrema

/-!
# Frontiers of a deterministic `N`-branching walk

## Public declarations

For generation \(n\), `lowerFrontier` and `upperFrontier` are the infimum and
supremum in a complete lattice. `lowerFrontier_eq_lowerPoint` and
`upperFrontier_eq_upperPoint` identify them with the attained extrema on a
nonempty finite population. The `...FrontierPoints` operations describe the
sets of attaining positions. A scalar potential has an attained minimum on every
nonempty generation, and reversing the position order exchanges the two
frontiers:

\[
\begin{aligned}
\operatorname{Lower}_n
  &=\{x\in P_n:\forall y\in P_n,\ x\le y\},\\
\operatorname{Upper}_n
  &=\{x\in P_n:\forall y\in P_n,\ y\le x\},\\
\min_{x\in P_n}\varphi(x)
  &\le \varphi(y)\quad(y\in P_n,\ P_n\ne\varnothing),\\
\operatorname{Lower}(V^{\mathrm{op}},n)
  &=\operatorname{OrderDual.toDual}''\operatorname{Upper}(V,n).
\end{aligned}
\]

The declarations below are in namespace
`Combinatorics.Branching.Selection.NSelection.Walk`.

- `lowerFrontierPoints`, `upperFrontierPoints`, `mem_lowerFrontierPoints_iff`,
  `lowerFrontierPoints_subset_population`, `mem_upperFrontierPoints_iff`, and
  `upperFrontierPoints_subset_population`: least and greatest positions in a
  generation, characterized by `IsLeast` and `IsGreatest`.
- `lowerPotentialPoint`, `isLeast_lowerPotentialPoint`,
  `lowerPotentialPoint_le`, and `exists_potential_eq_lowerPotentialPoint`:
  for a nonempty generation, the least value of `potential` is attained by a
  particle and is at most every value in that generation.
- `lowerPoint`, `upperPoint`, `isLeast_lowerPoint`, `isGreatest_upperPoint`,
  `lowerPoint_mem_lowerFrontierPoints`, `upperPoint_mem_upperFrontierPoints`,
  `lowerFrontierPoints_nonempty`, and `upperFrontierPoints_nonempty`: extrema of a
  nonempty linearly ordered generation belong to their respective frontiers.
- `mem_lowerFrontierPoints_mapOrderDual_iff`,
  `mem_upperFrontierPoints_mapOrderDual_iff`, `lowerFrontierPoints_mapOrderDual`, and
  `upperFrontierPoints_mapOrderDual`: order reversal exchanges the two frontiers.
- `lowerPoint_mapOrderDual` and `upperPoint_mapOrderDual`: the extrema of the
  reversed walk are the order-duals of the opposite extrema.

The population of a generation is a finite set of positions, so it has a lower
and an upper frontier: the set of its least positions and the set of its
greatest positions. When the population is nonempty and the positions are
linearly ordered, each frontier is a singleton, and its unique element is the
frontier *point* `lowerPoint` or `upperPoint`. A frontier point is what the
asymptotic speed of a selected walk is measured on.

The two frontiers are one object read in two orders: reversing the order on
positions turns the lower frontier of a walk into the upper frontier of the
reversed walk. Consequently the leftmost and rightmost selection rules need
only one theory.

A generation may be empty, because a particle may have no offspring at all; the
frontier points are therefore always taken under an explicit nonemptiness
hypothesis, and non-extinction belongs to the probabilistic layer.

For an arbitrary position space, `lowerPotentialPoint` is the attained lower
frontier of the walk's `CloudSet` after applying a potential
`Position → ℝ`. It does not sort particles or choose an ordered child slot.
-/

open Classical

@[expose] public section

open _root_.Combinatorics.Selection

/-! ### The two frontiers of a generation -/

namespace Combinatorics

namespace Branching

namespace Selection

namespace NSelection namespace Walk

variable {X : Type*} [DecidableEq X] {N : ℕ} {M : FiniteNSelection X N}

/-- The lower frontier of a generation is its infimum. -/
noncomputable def lowerFrontier [CompleteLattice X] (V : Walk N X M) (n : ℕ) : X :=
  V.cloud.lowerFrontier n

/-- The upper frontier of a generation is its supremum. -/
noncomputable def upperFrontier [CompleteLattice X] (V : Walk N X M) (n : ℕ) : X :=
  V.cloud.upperFrontier n

/-- The lower frontier of the walk at generation `n`: the least positions of
the population. -/
noncomputable def lowerFrontierPoints [LE X] (V : Walk N X M) (n : ℕ) : Set X :=
  V.cloud.lowerFrontierPoints n

@[simp] theorem mem_lowerFrontierPoints_iff [LE X] (V : Walk N X M) (n : ℕ) (x : X) :
    x ∈ V.lowerFrontierPoints n ↔ IsLeast {y | y ∈ V.population n} x := by
  rw [lowerFrontierPoints, CloudSet.mem_lowerFrontierPoints_iff]
  rfl

theorem lowerFrontierPoints_subset_population [LE X] (V : Walk N X M) (n : ℕ) :
    V.lowerFrontierPoints n ⊆ {y | y ∈ V.population n} :=
  CloudSet.lowerFrontierPoints_subset_points V.cloud n

/-- The upper frontier of the walk at generation `n`: the greatest positions of
the population. -/
noncomputable def upperFrontierPoints [LE X] (V : Walk N X M) (n : ℕ) : Set X :=
  V.cloud.upperFrontierPoints n

@[simp] theorem mem_upperFrontierPoints_iff [LE X] (V : Walk N X M) (n : ℕ) (x : X) :
    x ∈ V.upperFrontierPoints n ↔ IsGreatest {y | y ∈ V.population n} x := by
  rw [upperFrontierPoints, CloudSet.mem_upperFrontierPoints_iff]
  rfl

theorem upperFrontierPoints_subset_population [LE X] (V : Walk N X M) (n : ℕ) :
    V.upperFrontierPoints n ⊆ {y | y ∈ V.population n} :=
  CloudSet.upperFrontierPoints_subset_points V.cloud n

/-! ### Scalar frontiers through a potential -/

private theorem hasLowerPotentialPoint_of_nonempty (V : Walk N X M)
    (potential : X → ℝ) (n : ℕ) (h : (V.population n).Nonempty) :
    V.cloud.HasLowerPotentialPoint potential n := by
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image
    (V.population n) potential h
  have hxcloud : x ∈ V.cloud.points n := by
    simpa [cloud] using hx
  refine ⟨potential x, ?_⟩
  rw [CloudSet.mem_lowerPotentialFrontierPoints_iff]
  change IsLeast (potential '' V.cloud.points n) (potential x)
  constructor
  · exact ⟨x, hxcloud, rfl⟩
  · intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact hmin z (by simpa [cloud] using hz)

/-- The least scalar potential value in a nonempty generation. -/
noncomputable def lowerPotentialPoint (V : Walk N X M)
    (potential : X → ℝ) (n : ℕ) (h : (V.population n).Nonempty) : ℝ :=
  V.cloud.lowerPotentialPoint potential n (by
    obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image
      (V.population n) potential h
    have hxcloud : x ∈ V.cloud.points n := by
      simpa [cloud] using hx
    refine ⟨potential x, ?_⟩
    rw [CloudSet.mem_lowerPotentialFrontierPoints_iff]
    change IsLeast (potential '' V.cloud.points n) (potential x)
    constructor
    · exact ⟨x, hxcloud, rfl⟩
    · intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      exact hmin z (by simpa [cloud] using hz))

theorem isLeast_lowerPotentialPoint (V : Walk N X M)
    (potential : X → ℝ) (n : ℕ) (h : (V.population n).Nonempty) :
    IsLeast {x | ∃ y ∈ V.population n, potential y = x}
      (V.lowerPotentialPoint potential n h) := by
  have hvalues : V.cloud.potentialValues potential n =
      {x | ∃ y ∈ V.population n, potential y = x} := by
    ext x
    simp [CloudSet.potentialValues, cloud]
  rw [← hvalues]
  exact V.cloud.isLeast_lowerPotentialPoint potential n
    (hasLowerPotentialPoint_of_nonempty V potential n h)

theorem lowerPotentialPoint_le (V : Walk N X M)
    (potential : X → ℝ) (n : ℕ) (h : (V.population n).Nonempty)
    {y : X} (hy : y ∈ V.population n) :
    V.lowerPotentialPoint potential n h ≤ potential y :=
  (V.isLeast_lowerPotentialPoint potential n h).2 ⟨y, hy, rfl⟩

theorem exists_potential_eq_lowerPotentialPoint (V : Walk N X M)
    (potential : X → ℝ) (n : ℕ) (h : (V.population n).Nonempty) :
    ∃ y ∈ V.population n,
      potential y = V.lowerPotentialPoint potential n h :=
  (V.isLeast_lowerPotentialPoint potential n h).1

/-! ### The frontier points -/

/-- The least particle of a nonempty generation. -/
noncomputable def lowerPoint [LinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty) : X :=
  (V.population n).min' h

/-- The greatest particle of a nonempty generation. -/
noncomputable def upperPoint [LinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty) : X :=
  (V.population n).max' h

theorem isLeast_lowerPoint [LinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    IsLeast {x | x ∈ V.population n} (V.lowerPoint n h) :=
  Finset.isLeast_min' (V.population n) h

theorem isGreatest_upperPoint [LinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    IsGreatest {x | x ∈ V.population n} (V.upperPoint n h) :=
  Finset.isGreatest_max' (V.population n) h

theorem lowerPoint_mem_lowerFrontierPoints [LinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    V.lowerPoint n h ∈ V.lowerFrontierPoints n :=
  (mem_lowerFrontierPoints_iff V n _).mpr (isLeast_lowerPoint V n h)

theorem upperPoint_mem_upperFrontierPoints [LinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    V.upperPoint n h ∈ V.upperFrontierPoints n :=
  (mem_upperFrontierPoints_iff V n _).mpr (isGreatest_upperPoint V n h)

/-- On a nonempty finite population, the infimum is attained at its least point. -/
theorem lowerFrontier_eq_lowerPoint [CompleteLinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty) : V.lowerFrontier n = V.lowerPoint n h :=
  CloudSet.lowerFrontier_eq_of_isLeast V.cloud n (V.isLeast_lowerPoint n h)

/-- On a nonempty finite population, the supremum is attained at its greatest point. -/
theorem upperFrontier_eq_upperPoint [CompleteLinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty) : V.upperFrontier n = V.upperPoint n h :=
  CloudSet.upperFrontier_eq_of_isGreatest V.cloud n (V.isGreatest_upperPoint n h)

/-- A nonempty generation has a nonempty lower frontier. -/
theorem lowerFrontierPoints_nonempty [LinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    (V.lowerFrontierPoints n).Nonempty :=
  ⟨V.lowerPoint n h, V.lowerPoint_mem_lowerFrontierPoints n h⟩

/-- A nonempty generation has a nonempty upper frontier. -/
theorem upperFrontierPoints_nonempty [LinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    (V.upperFrontierPoints n).Nonempty :=
  ⟨V.upperPoint n h, V.upperPoint_mem_upperFrontierPoints n h⟩

/-! ### The two orders -/

/-- Reversing the order exchanges the two frontiers of every generation. -/
theorem mem_lowerFrontierPoints_mapOrderDual_iff [LE X] (V : Walk N X M) (n : ℕ)
    (x : X) :
    OrderDual.toDual x ∈ (V.mapOrderDual).lowerFrontierPoints n ↔ x ∈ V.upperFrontierPoints n := by
  show OrderDual.toDual x ∈ (V.mapOrderDual).cloud.lowerFrontierPoints n ↔
    x ∈ V.cloud.upperFrontierPoints n
  rw [mapOrderDual_cloud]
  exact (CloudSet.mem_upperFrontierPoints_iff_orderDual V.cloud n x).symm

theorem mem_upperFrontierPoints_mapOrderDual_iff [LE X] (V : Walk N X M) (n : ℕ)
    (x : X) :
    OrderDual.toDual x ∈ (V.mapOrderDual).upperFrontierPoints n ↔ x ∈ V.lowerFrontierPoints n := by
  show OrderDual.toDual x ∈ (V.mapOrderDual).cloud.upperFrontierPoints n ↔
    x ∈ V.cloud.lowerFrontierPoints n
  rw [mapOrderDual_cloud]
  show IsGreatest (OrderDual.toDual '' V.cloud.points n) (OrderDual.toDual x) ↔
    IsLeast (V.cloud.points n) x
  exact OrderDual.isGreatest_image_toDual_iff

theorem lowerFrontierPoints_mapOrderDual (V : Walk N X M) [LE X] (n : ℕ) :
    (V.mapOrderDual).lowerFrontierPoints n = OrderDual.toDual '' V.upperFrontierPoints n := by
  ext q
  constructor
  · intro hq
    refine ⟨OrderDual.ofDual q, ?_, by simp⟩
    exact (mem_lowerFrontierPoints_mapOrderDual_iff V n (OrderDual.ofDual q)).mp (by simpa using hq)
  · rintro ⟨y, hy, rfl⟩
    exact (mem_lowerFrontierPoints_mapOrderDual_iff V n y).mpr hy

theorem upperFrontierPoints_mapOrderDual (V : Walk N X M) [LE X] (n : ℕ) :
    (V.mapOrderDual).upperFrontierPoints n = OrderDual.toDual '' V.lowerFrontierPoints n := by
  ext q
  constructor
  · intro hq
    refine ⟨OrderDual.ofDual q, ?_, by simp⟩
    exact (mem_upperFrontierPoints_mapOrderDual_iff V n (OrderDual.ofDual q)).mp (by simpa using hq)
  · rintro ⟨y, hy, rfl⟩
    exact (mem_upperFrontierPoints_mapOrderDual_iff V n y).mpr hy

/-- The least particle of the reversed walk is the greatest particle of the
walk. -/
theorem lowerPoint_mapOrderDual [LinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty)
    (h' : (V.mapOrderDual.population n).Nonempty) :
    (V.mapOrderDual).lowerPoint n h' = OrderDual.toDual (V.upperPoint n h) := by
  refine (Finset.min'_eq_iff ((V.mapOrderDual).population n) h'
    (OrderDual.toDual (V.upperPoint n h))).mpr ⟨?_, ?_⟩
  · rw [population_mapOrderDual]
    exact Finset.mem_image_of_mem OrderDual.toDual (Finset.max'_mem (V.population n) h)
  · intro b hb
    rw [population_mapOrderDual] at hb
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact (OrderDual.toDual_le_toDual).mpr (Finset.le_max' (V.population n) y hy)

/-- The greatest particle of the reversed walk is the least particle of the
walk. -/
theorem upperPoint_mapOrderDual [LinearOrder X] (V : Walk N X M) (n : ℕ)
    (h : (V.population n).Nonempty)
    (h' : (V.mapOrderDual.population n).Nonempty) :
    (V.mapOrderDual).upperPoint n h' = OrderDual.toDual (V.lowerPoint n h) := by
  refine (Finset.max'_eq_iff ((V.mapOrderDual).population n) h'
    (OrderDual.toDual (V.lowerPoint n h))).mpr ⟨?_, ?_⟩
  · rw [population_mapOrderDual]
    exact Finset.mem_image_of_mem OrderDual.toDual (Finset.min'_mem (V.population n) h)
  · intro b hb
    rw [population_mapOrderDual] at hb
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    exact (OrderDual.toDual_le_toDual).mpr (Finset.min'_le (V.population n) y hy)

end Walk

end NSelection end Selection

end Branching

end Combinatorics
