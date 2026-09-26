import MeasureTheory.UlamHarris.Tree.Topology
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Basic

/-!
# Borel structure on Ulam--Harris trees

The σ-algebra `instMeasurableSpaceTree` on `Tree α` is the cylinder σ-algebra:
the smallest σ-algebra making every membership evaluation
`T ↦ (u ∈ T.carrier)` measurable. This file compares it with the Borel
σ-algebras of the two topologies of `Tree/Topology.lean`, for a countable label
type `α`.

* `borel_treePointwiseTopology_eq_cylinder`: the Borel σ-algebra of the
  pointwise topology is exactly the cylinder σ-algebra.
* `cylinder_le_borel_truncation`: the cylinder σ-algebra is contained in the
  Borel σ-algebra of the truncation topology, which is finer. Every truncation
  ball is a countable Boolean combination of cylinder sets.
* `borel_treeTruncationTopology_eq_cylinder_of_countable_balls`: the converse
  holds as soon as the truncation balls form a countable family, because then
  every open set is a countable union of balls. For finitely many labels this
  is verified in `Tree/FiniteLabels.lean`, giving equality of the three
  σ-algebras. For an infinite label type the balls need not be countable, so
  this criterion does not apply; the general comparison established here is
  only the inclusion `instMeasurableSpaceTree ≤ borel treeTruncationTopology`.

The two local instances on `Prop` fill small gaps in the current mathlib: the
Sierpinski topology on `Prop` is T0, and `MeasurableSpace Prop` is `⊤`, hence
Borel. They are `local`, so importing this file does not alter the instance
graph seen by other files.
-/

open MeasureTheory
open scoped Topology

set_option linter.style.haveILetI false

namespace MeasureTheory

/-- If a topology has a countable basis whose members are measurable for a
σ-algebra `m`, then its Borel σ-algebra is contained in `m`. -/
theorem borel_le_of_countable_basis {β : Type*} {t : TopologicalSpace β}
    {m : MeasurableSpace β} {B : Set (Set β)}
    (hB : TopologicalSpace.IsTopologicalBasis (t := t) B)
    (hcount : B.Countable) (hmeas : ∀ s ∈ B, MeasurableSet[m] s) :
    @borel β t ≤ m := by
  refine MeasurableSpace.generateFrom_le fun s hs => ?_
  obtain ⟨S, hSB, rfl⟩ := hB.open_eq_sUnion hs
  rw [Set.sUnion_eq_iUnion]
  letI : Countable S := (hcount.mono hSB).to_subtype
  exact MeasurableSet.iUnion fun b : S => hmeas b.1 (hSB b.2)

namespace UlamHarris

local instance instT0SpaceProp : T0Space Prop := by
  rw [t0Space_iff_exists_isOpen_xor_mem]
  intro x y _hxy
  refine ⟨{True}, ?_, ?_⟩
  · exact TopologicalSpace.isOpen_generateFrom_of_mem (by simp)
  · by_cases hx : x <;> by_cases hy : y <;> simp_all [Xor]

local instance instBorelSpaceProp : BorelSpace Prop where
  measurable_eq := by
    rw [borel_eq_top_of_countable]
    rfl

namespace Tree

variable {α : Type*} [LT α]

variable [Countable α]

/-- For the pointwise topology, the Borel σ-algebra on trees is exactly the
cylinder σ-algebra already carried by `Tree α`. -/
theorem borel_treePointwiseTopology_eq_cylinder :
    @borel (Tree α) treePointwiseTopology = instMeasurableSpaceTree := by
  unfold treePointwiseTopology instMeasurableSpaceTree
  rw [borel_comap, ← BorelSpace.measurable_eq (α := List α → Prop)]
  rfl

/-- For a countable label type, the default topology makes `Tree α` a Borel
space with the cylinder σ-algebra. -/
instance instBorelSpaceTree : BorelSpace (Tree α) :=
  ⟨borel_treePointwiseTopology_eq_cylinder.symm⟩

/-- Every topology finer than the pointwise one (below it in mathlib's lattice
order) has a Borel σ-algebra containing the cylinder σ-algebra. -/
theorem cylinder_le_borel_of_le {t : TopologicalSpace (Tree α)}
    (h : t ≤ treePointwiseTopology) :
    instMeasurableSpaceTree ≤ @borel (Tree α) t := by
  rw [← borel_treePointwiseTopology_eq_cylinder]
  exact borel_anti h

/-- The cylinder σ-algebra is contained in the Borel σ-algebra of the
truncation topology. -/
theorem cylinder_le_borel_truncation :
    instMeasurableSpaceTree ≤ @borel (Tree α) treeTruncationTopology :=
  cylinder_le_borel_of_le treeTruncationTopology_le_pointwise

/-- The truncation Borel σ-algebra equals the cylinder σ-algebra as soon as
the truncation topology has a countable basis of cylinder-measurable sets. -/
theorem borel_treeTruncationTopology_eq_cylinder_of_countable_basis
    {B : Set (Set (Tree α))}
    (hB : TopologicalSpace.IsTopologicalBasis (t := treeTruncationTopology) B)
    (hcount : B.Countable) (hmeas : ∀ s ∈ B, MeasurableSet s) :
    @borel (Tree α) treeTruncationTopology = instMeasurableSpaceTree :=
  le_antisymm (borel_le_of_countable_basis hB hcount hmeas) cylinder_le_borel_truncation

/-- A truncation ball is a countable Boolean combination of cylinder sets. -/
theorem truncationBall_measurable (T : Tree α) (n : ℕ) :
    MeasurableSet (Tree.truncationBall T n) := by
  have hset : Tree.truncationBall T n =
      ⋂ u : {u : List α // u.length ≤ n},
        {S : Tree α | u.1 ∈ S.carrier ↔ u.1 ∈ T.carrier} := by
    ext S
    rw [Set.mem_iInter]
    constructor
    · intro h u
      rw [Tree.mem_truncationBall] at h
      have hS : u.1 ∈ S.carrier ↔ u.1 ∈ (S.truncate n).carrier := by
        simp [Tree.mem_truncate, u.2]
      have hT : u.1 ∈ T.carrier ↔ u.1 ∈ (T.truncate n).carrier := by
        simp [Tree.mem_truncate, u.2]
      change u.1 ∈ S.carrier ↔ u.1 ∈ T.carrier
      rw [hS, hT, h]
    · intro h
      rw [Tree.mem_truncationBall]
      ext u
      rw [Tree.mem_truncate, Tree.mem_truncate]
      constructor
      · rintro ⟨hlen, huS⟩
        exact ⟨hlen, (h ⟨u, hlen⟩).1 huS⟩
      · rintro ⟨hlen, huT⟩
        exact ⟨hlen, (h ⟨u, hlen⟩).2 huT⟩
  rw [hset]
  apply MeasurableSet.iInter
  intro u
  by_cases hu : u.1 ∈ T.carrier
  · have hset : {S : Tree α | u.1 ∈ S.carrier ↔ u.1 ∈ T.carrier} =
        {S : Tree α | u.1 ∈ S.carrier} := by
      ext S
      simp [hu]
    rw [hset]
    exact measurableSet_carrier u.1
  · have hset : {S : Tree α | u.1 ∈ S.carrier ↔ u.1 ∈ T.carrier} =
        {S : Tree α | u.1 ∈ S.carrier}ᶜ := by
      ext S
      simp [hu]
    rw [hset]
    exact (measurableSet_carrier u.1).compl

/-- If the truncation balls form a countable family, then every open set of the
truncation topology is a countable union of balls, hence belongs to the
cylinder σ-algebra. This is the only place where the comparison of σ-algebras
needs a countability hypothesis. The criterion is sufficient; no strictness
assertion is made here for infinite label types. -/
theorem borel_treeTruncationTopology_le_cylinder
    (hball : Countable {b : Set (Tree α) // ∃ T n, b = Tree.truncationBall T n}) :
    @borel (Tree α) treeTruncationTopology ≤ instMeasurableSpaceTree := by
  letI : Countable {b : Set (Tree α) // ∃ T n, b = Tree.truncationBall T n} := hball
  refine MeasurableSpace.generateFrom_le fun s hs => ?_
  have hsub : ∀ T ∈ s, ∃ n, Tree.truncationBall T n ⊆ s :=
    (isOpen_truncation_iff_ball s).1 hs
  have hset : s = Set.iUnion (fun b : {b : {b : Set (Tree α) //
      ∃ T n, b = Tree.truncationBall T n} // b.1 ⊆ s} => b.1.1) := by
    ext T
    constructor
    · intro hT
      obtain ⟨n, hn⟩ := hsub T hT
      exact Set.mem_iUnion.2
        ⟨⟨⟨Tree.truncationBall T n, ⟨T, n, rfl⟩⟩, hn⟩, Tree.mem_truncationBall.2 rfl⟩
    · intro hT
      rcases Set.mem_iUnion.1 hT with ⟨b, hb⟩
      exact b.2 hb
  rw [hset]
  refine MeasurableSet.iUnion fun b => ?_
  obtain ⟨T, n, hb⟩ := b.1.2
  rw [hb]
  exact truncationBall_measurable T n

/-- The Borel σ-algebra of the truncation topology is the cylinder σ-algebra as
soon as the truncation balls are countable. -/
theorem borel_treeTruncationTopology_eq_cylinder_of_countable_balls
    (hball : Countable {b : Set (Tree α) // ∃ T n, b = Tree.truncationBall T n}) :
    @borel (Tree α) treeTruncationTopology = instMeasurableSpaceTree :=
  le_antisymm (borel_treeTruncationTopology_le_cylinder hball) cylinder_le_borel_truncation

/-- A sufficient condition for strictness of the cylinder/Borel inclusion: some
truncation ball is not measurable for the cylinder σ-algebra. Such a ball is
open in the truncation topology, hence Borel, so strictness follows. -/
theorem cylinder_lt_borel_truncation_of_not_measurable_ball
    (T : Tree α) (n : ℕ) (hT : ¬ MeasurableSet (Tree.truncationBall T n)) :
    instMeasurableSpaceTree < @borel (Tree α) treeTruncationTopology := by
  refine lt_of_le_of_ne cylinder_le_borel_truncation ?_
  intro heq
  have hball : MeasurableSet[@borel (Tree α) treeTruncationTopology]
      (Tree.truncationBall T n) :=
    MeasurableSpace.measurableSet_generateFrom (isOpen_truncationBall (α := α) T n)
  exact hT (heq.symm ▸ hball)

/-- Existential form of `cylinder_lt_borel_truncation_of_not_measurable_ball`. -/
theorem cylinder_lt_borel_truncation_of_exists_not_measurable_ball
    (h : ∃ (T : Tree α) (n : ℕ), ¬ MeasurableSet (Tree.truncationBall T n)) :
    instMeasurableSpaceTree < @borel (Tree α) treeTruncationTopology := by
  obtain ⟨T, n, hT⟩ := h
  exact cylinder_lt_borel_truncation_of_not_measurable_ball (α := α) T n hT

/-- A necessary condition for strictness of the cylinder/Borel inclusion: the
truncation balls must be uncountable. If they were countable, the two
σ-algebras would coincide by the countable-ball criterion. -/
theorem not_countable_truncationBalls_of_cylinder_lt_borel_truncation
    (h : instMeasurableSpaceTree < @borel (Tree α) treeTruncationTopology) :
    ¬ Countable {b : Set (Tree α) // ∃ T n, b = Tree.truncationBall T n} := by
  intro hball
  exact h.ne' (borel_treeTruncationTopology_eq_cylinder_of_countable_balls hball)

end Tree

end UlamHarris

end MeasureTheory
