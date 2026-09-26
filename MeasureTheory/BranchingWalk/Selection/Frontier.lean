import MeasureTheory.BranchingWalk.Selection.Cloud
import MeasureTheory.BranchingWalk.Cloud.Frontier.Basic

/-!
# Frontiers of a deterministic `N`-branching walk

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
-/

open Classical

namespace MeasureTheory

namespace BranchingWalk

namespace Selection

namespace NBrw

variable {X : Type*} [DecidableEq X] {N : ℕ} {M : Mechanism X N}

/-! ### The two frontiers of a generation -/

/-- The lower frontier of the walk at generation `n`: the least positions of
the population. -/
def lowerFrontier [LE X] (V : NBrw N X M) (n : ℕ) : Set X :=
  V.cloud.lowerFrontier n

@[simp] theorem mem_lowerFrontier_iff [LE X] (V : NBrw N X M) (n : ℕ) (x : X) :
    x ∈ V.lowerFrontier n ↔ IsLeast {y | y ∈ V.population n} x := by
  rw [lowerFrontier, Cloud.mem_lowerFrontier_iff]
  rfl

theorem lowerFrontier_subset_population [LE X] (V : NBrw N X M) (n : ℕ) :
    V.lowerFrontier n ⊆ {y | y ∈ V.population n} :=
  Cloud.lowerFrontier_subset_points V.cloud n

/-- The upper frontier of the walk at generation `n`: the greatest positions of
the population. -/
def upperFrontier [LE X] (V : NBrw N X M) (n : ℕ) : Set X :=
  V.cloud.upperFrontier n

@[simp] theorem mem_upperFrontier_iff [LE X] (V : NBrw N X M) (n : ℕ) (x : X) :
    x ∈ V.upperFrontier n ↔ IsGreatest {y | y ∈ V.population n} x := by
  rw [upperFrontier, Cloud.mem_upperFrontier_iff]
  rfl

theorem upperFrontier_subset_population [LE X] (V : NBrw N X M) (n : ℕ) :
    V.upperFrontier n ⊆ {y | y ∈ V.population n} :=
  Cloud.upperFrontier_subset_points V.cloud n

/-! ### The frontier points -/

/-- The least particle of a nonempty generation. -/
noncomputable def lowerPoint [LinearOrder X] (V : NBrw N X M) (n : ℕ)
    (h : (V.population n).Nonempty) : X :=
  (V.population n).min' h

/-- The greatest particle of a nonempty generation. -/
noncomputable def upperPoint [LinearOrder X] (V : NBrw N X M) (n : ℕ)
    (h : (V.population n).Nonempty) : X :=
  (V.population n).max' h

theorem isLeast_lowerPoint [LinearOrder X] (V : NBrw N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    IsLeast {x | x ∈ V.population n} (V.lowerPoint n h) :=
  Finset.isLeast_min' (V.population n) h

theorem isGreatest_upperPoint [LinearOrder X] (V : NBrw N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    IsGreatest {x | x ∈ V.population n} (V.upperPoint n h) :=
  Finset.isGreatest_max' (V.population n) h

theorem lowerPoint_mem_lowerFrontier [LinearOrder X] (V : NBrw N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    V.lowerPoint n h ∈ V.lowerFrontier n :=
  (mem_lowerFrontier_iff V n _).mpr (isLeast_lowerPoint V n h)

theorem upperPoint_mem_upperFrontier [LinearOrder X] (V : NBrw N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    V.upperPoint n h ∈ V.upperFrontier n :=
  (mem_upperFrontier_iff V n _).mpr (isGreatest_upperPoint V n h)

/-- A nonempty generation has a nonempty lower frontier. -/
theorem lowerFrontier_nonempty [LinearOrder X] (V : NBrw N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    (V.lowerFrontier n).Nonempty :=
  ⟨V.lowerPoint n h, V.lowerPoint_mem_lowerFrontier n h⟩

/-- A nonempty generation has a nonempty upper frontier. -/
theorem upperFrontier_nonempty [LinearOrder X] (V : NBrw N X M) (n : ℕ)
    (h : (V.population n).Nonempty) :
    (V.upperFrontier n).Nonempty :=
  ⟨V.upperPoint n h, V.upperPoint_mem_upperFrontier n h⟩

/-! ### The two orders -/

/-- Reversing the order exchanges the two frontiers of every generation. -/
theorem mem_lowerFrontier_mapOrderDual_iff [LE X] (V : NBrw N X M) (n : ℕ)
    (x : X) :
    OrderDual.toDual x ∈ (V.mapOrderDual).lowerFrontier n ↔ x ∈ V.upperFrontier n := by
  show OrderDual.toDual x ∈ (V.mapOrderDual).cloud.lowerFrontier n ↔
    x ∈ V.cloud.upperFrontier n
  rw [mapOrderDual_cloud]
  exact (Cloud.mem_upperFrontier_iff_orderDual V.cloud n x).symm

theorem mem_upperFrontier_mapOrderDual_iff [LE X] (V : NBrw N X M) (n : ℕ)
    (x : X) :
    OrderDual.toDual x ∈ (V.mapOrderDual).upperFrontier n ↔ x ∈ V.lowerFrontier n := by
  show OrderDual.toDual x ∈ (V.mapOrderDual).cloud.upperFrontier n ↔
    x ∈ V.cloud.lowerFrontier n
  rw [mapOrderDual_cloud]
  show IsGreatest (OrderDual.toDual '' V.cloud.points n) (OrderDual.toDual x) ↔
    IsLeast (V.cloud.points n) x
  exact isGreatest_image_toDual_iff

theorem lowerFrontier_mapOrderDual (V : NBrw N X M) [LE X] (n : ℕ) :
    (V.mapOrderDual).lowerFrontier n = OrderDual.toDual '' V.upperFrontier n := by
  ext q
  constructor
  · intro hq
    refine ⟨OrderDual.ofDual q, ?_, by simp⟩
    exact (mem_lowerFrontier_mapOrderDual_iff V n (OrderDual.ofDual q)).mp (by simpa using hq)
  · rintro ⟨y, hy, rfl⟩
    exact (mem_lowerFrontier_mapOrderDual_iff V n y).mpr hy

theorem upperFrontier_mapOrderDual (V : NBrw N X M) [LE X] (n : ℕ) :
    (V.mapOrderDual).upperFrontier n = OrderDual.toDual '' V.lowerFrontier n := by
  ext q
  constructor
  · intro hq
    refine ⟨OrderDual.ofDual q, ?_, by simp⟩
    exact (mem_upperFrontier_mapOrderDual_iff V n (OrderDual.ofDual q)).mp (by simpa using hq)
  · rintro ⟨y, hy, rfl⟩
    exact (mem_upperFrontier_mapOrderDual_iff V n y).mpr hy

/-- The least particle of the reversed walk is the greatest particle of the
walk. -/
theorem lowerPoint_mapOrderDual [LinearOrder X] (V : NBrw N X M) (n : ℕ)
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
theorem upperPoint_mapOrderDual [LinearOrder X] (V : NBrw N X M) (n : ℕ)
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

end NBrw

end Selection

end BranchingWalk

end MeasureTheory
