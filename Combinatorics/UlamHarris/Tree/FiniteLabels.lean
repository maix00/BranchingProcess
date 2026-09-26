import Combinatorics.UlamHarris.Tree.Borel
import Combinatorics.UlamHarris.Tree.Metric
import Mathlib.Data.Fintype.Powerset

/-!
# Finitely many labels: the three σ-algebras coincide

For a finite label type every truncation has only finitely many nodes, so there
are only finitely many truncations at a fixed height and hence only countably
many truncation balls. The criterion
`borel_treeTruncationTopology_eq_cylinder_of_countable_balls` then applies, and
the cylinder σ-algebra, the Borel σ-algebra of the pointwise topology, and the
Borel σ-algebra of the tree metric all coincide.

For an infinite label type the countable-ball criterion need not hold, so this
file makes no equality assertion beyond the finite case.
-/

open MeasureTheory
open scoped Topology ENNReal

set_option linter.style.haveILetI false

namespace Combinatorics

namespace UlamHarris

namespace Tree

/-- A list of length at most `n` is determined by its first `n` entries, so
there are only finitely many of them over a finite alphabet. -/
private theorem finite_list_length_le {α : Type*} [Finite α] (n : ℕ) :
    Finite {v : List α // v.length ≤ n} := by
  classical
  refine Finite.of_injective
    (fun p : {v : List α // v.length ≤ n} => fun i : Fin n => p.1[(i : ℕ)]?) ?_
  intro p q h
  refine Subtype.ext (List.ext_getElem? fun i => ?_)
  by_cases hi : i < n
  · exact congrFun h ⟨i, hi⟩
  · rw [List.getElem?_eq_none_iff.mpr (by omega : p.1.length ≤ i),
      List.getElem?_eq_none_iff.mpr (by omega : q.1.length ≤ i)]

variable {α : Type*} [LT α]

/-- With finitely many labels, a tree of height at most `n` is determined by
its set of nodes of length at most `n`, so there are only finitely many
truncations at height `n`. -/
theorem finite_truncations [Finite α] (n : ℕ) :
    Finite {τ : Tree α // τ = τ.truncate n} := by
  classical
  haveI := finite_list_length_le (α := α) n
  refine Finite.of_injective
    (fun τ : {τ : Tree α // τ = τ.truncate n} =>
      {u : {v : List α // v.length ≤ n} | u.1 ∈ τ.1.carrier}) ?_
  rintro ⟨τ, hτ⟩ ⟨σ, hσ⟩ h
  refine Subtype.ext (Tree.ext ?_)
  ext u
  by_cases hu : u.length ≤ n
  · have := congrArg (fun S : Set {v : List α // v.length ≤ n} =>
        (⟨u, hu⟩ : {v : List α // v.length ≤ n}) ∈ S) h
    simpa using this
  · have hτ' : u ∉ τ.carrier := by
      intro hmem
      have : u ∈ (τ.truncate n).carrier := hτ ▸ hmem
      exact hu (Tree.mem_truncate.1 this).1
    have hσ' : u ∉ σ.carrier := by
      intro hmem
      have : u ∈ (σ.truncate n).carrier := hσ ▸ hmem
      exact hu (Tree.mem_truncate.1 this).1
    simp [hτ', hσ']

/-- With finitely many labels the truncation balls form a countable family:
each of them is the ball of a truncation at some height. -/
theorem countable_truncationBalls [Finite α] :
    Countable {b : Set (Tree α) // ∃ T n, b = Tree.truncationBall T n} := by
  classical
  haveI : ∀ n : ℕ, Finite {τ : Tree α // τ = τ.truncate n} :=
    fun n => finite_truncations n
  let f : ((n : ℕ) × {τ : Tree α // τ = τ.truncate n}) → Set (Tree α) :=
    fun p => Tree.truncationBall p.2.1 p.1
  have hrange : Set.range f =
      {b : Set (Tree α) | ∃ T n, b = Tree.truncationBall T n} := by
    ext b
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.2.1, p.1, rfl⟩
    · rintro ⟨T, n, rfl⟩
      refine ⟨⟨n, ⟨T.truncate n, by rw [Tree.truncate_truncate, min_self]⟩⟩, ?_⟩
      simp [f, Tree.truncationBall, Tree.truncate_truncate]
  have hcount : (Set.range f).Countable := Set.countable_range f
  rw [hrange] at hcount
  exact hcount

/-- For finitely many labels the Borel σ-algebra of the truncation topology is
the cylinder σ-algebra. -/
theorem borel_treeTruncationTopology_eq_cylinder_of_finite [Finite α] :
    @borel (Tree α) treeTruncationTopology = instMeasurableSpaceTree :=
  borel_treeTruncationTopology_eq_cylinder_of_countable_balls countable_truncationBalls

/-- For finitely many labels the Borel σ-algebra of the tree metric is the
cylinder σ-algebra. -/
theorem borel_treeMetricTopology_eq_cylinder_of_finite [Finite α] :
    @borel (Tree α) (treeMetricTopology α) = instMeasurableSpaceTree := by
  rw [borel_treeMetricTopology_eq_borel_treeTruncationTopology]
  exact borel_treeTruncationTopology_eq_cylinder_of_finite

end Tree

end UlamHarris

end Combinatorics
