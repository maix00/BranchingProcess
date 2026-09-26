import Combinatorics.UlamHarris.Tree.RootIndexed.Topology
import Combinatorics.UlamHarris.Tree.Metric

/-!
# The sup tree metric on root-indexed trees

`RootIndexed.Tree.treeDist T T' = ⨆ r, Tree.treeDist (T r) (T' r)` is the sup
distance: two root-indexed trees are close when *every* initial ancestor agrees
with the other up to a high generation. The uniform balls of
`RootIndexed.Tree/Topology.lean` are exactly the metric balls, which
`mem_uniformBall_iff_treeDist_lt` records, so the topology induced by this
metric is `uniformTopology`.

The metric is exposed as the structure `metricSpace` and *not* as a global
instance, in keeping with the convention of `Tree/Metric.lean`: the default
topology of `RootIndexed.Tree Root α` stays the product topology, and the metric
topology is an additional named structure.

The sup needs a nonempty index type for its elementary properties, so the
metric space is constructed under `[Nonempty Root]`. An empty root type is
degenerate: the family is unique and the space is a point, for which the
product topology is already discrete.
-/

open MeasureTheory
open scoped Topology ENNReal

set_option linter.style.haveILetI false

namespace Combinatorics

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- The tree distance is bounded by one, since its value is the real part of
the inverse of a number at least one. -/
theorem treeDist_le_one (T T' : Tree α) : treeDist T T' ≤ 1 := by
  rw [treeDist, ← ENNReal.toReal_one]
  refine (ENNReal.toReal_le_toReal ?_ ?_).2 ?_
  · rw [ENNReal.inv_ne_top]
    simp
  · simp
  · rw [ENNReal.inv_le_one]
    simp

/-- A strict bound of the tree distance at level `n` upgrades to the bound at
level `n + 1`. The tree distance only takes the values `0` and `(1 + k)⁻¹`, so
the next value below `(1 + n)⁻¹` is `(1 + (n + 1))⁻¹`. -/
theorem treeDist_le_inv_succ_of_lt_inv (S T : Tree α) (n : ℕ)
    (h : treeDist S T < (1 + (n : ℝ))⁻¹) :
    treeDist S T ≤ (1 + ((n + 1 : ℕ) : ℝ))⁻¹ := by
  have hH : ((n + 1 : ℕ) : ℝ≥0∞) ≤ (heightCongr S T : ℝ≥0∞) := by
    have hle := (treeDist_lt_inv_iff S T n).1 h
    simpa using (ENat.toENNReal_le).2 hle
  have hbase : 1 + ((n + 1 : ℕ) : ℝ≥0∞) ≤
      1 + (heightCongr S T : ℝ≥0∞) := by
    simpa [add_comm] using add_le_add_left hH 1
  have hmono : (1 + (heightCongr S T : ℝ≥0∞))⁻¹ ≤
      (1 + ((n + 1 : ℕ) : ℝ≥0∞))⁻¹ :=
    ENNReal.inv_le_inv.2 hbase
  have hrhs : ((1 + ((n + 1 : ℕ) : ℝ≥0∞))⁻¹).toReal =
      (1 + ((n + 1 : ℕ) : ℝ))⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simp),
      ENNReal.toReal_one, ENNReal.toReal_natCast]
  have hreal : ((1 + (heightCongr S T : ℝ≥0∞))⁻¹).toReal ≤
      ((1 + ((n + 1 : ℕ) : ℝ≥0∞))⁻¹).toReal :=
    (ENNReal.toReal_le_toReal (by rw [ENNReal.inv_ne_top]; simp)
      (by rw [ENNReal.inv_ne_top]; simp)).2 hmono
  calc
    treeDist S T = ((1 + (heightCongr S T : ℝ≥0∞))⁻¹).toReal := rfl
    _ ≤ ((1 + ((n + 1 : ℕ) : ℝ≥0∞))⁻¹).toReal := hreal
    _ = (1 + ((n + 1 : ℕ) : ℝ))⁻¹ := hrhs

end Tree

namespace RootIndexed.Tree

variable {Root α : Type*} [LT α]

/-- The sup tree distance on root-indexed trees: the largest single-tree
distance over the initial ancestors. -/
noncomputable def treeDist (T T' : RootIndexed.Tree Root α) : ℝ :=
  ⨆ r, Tree.treeDist (T r) (T' r)

theorem treeDist_bddAbove (T T' : RootIndexed.Tree Root α) :
    BddAbove (Set.range fun r : Root => Tree.treeDist (T r) (T' r)) :=
  ⟨1, by rintro _ ⟨r, rfl⟩; exact Tree.treeDist_le_one _ _⟩

section NonemptyRoot

variable [Nonempty Root]

theorem treeDist_self (T : RootIndexed.Tree Root α) : treeDist T T = 0 := by
  rw [treeDist]
  simp only [Tree.treeDist_self]
  exact ciSup_const

omit [Nonempty Root] in
theorem treeDist_comm (T T' : RootIndexed.Tree Root α) :
    treeDist T T' = treeDist T' T := by
  rw [treeDist, treeDist]
  exact congrArg _ (funext fun r => Tree.treeDist_comm _ _)

omit [Nonempty Root] in
theorem treeDist_nonneg (T T' : RootIndexed.Tree Root α) : 0 ≤ treeDist T T' :=
  Real.iSup_nonneg fun _ => Tree.treeDist_nonneg _ _

theorem treeDist_le_one (T T' : RootIndexed.Tree Root α) : treeDist T T' ≤ 1 :=
  (ciSup_le_iff (treeDist_bddAbove T T')).2 fun _ => Tree.treeDist_le_one _ _

/-- The sup tree distance is ultrametric, because every one of its coordinates
is. -/
theorem treeDist_ultra (T₁ T₂ T₃ : RootIndexed.Tree Root α) :
    treeDist T₁ T₃ ≤ max (treeDist T₁ T₂) (treeDist T₂ T₃) :=
  (ciSup_le_iff (treeDist_bddAbove T₁ T₃)).2 fun r =>
    (Tree.treeDist_ultra _ _ _).trans (max_le_max
      (le_ciSup (treeDist_bddAbove T₁ T₂) r)
      (le_ciSup (treeDist_bddAbove T₂ T₃) r))

omit [Nonempty Root] in
/-- Two root-indexed trees at sup distance zero coincide: every coordinate
distance vanishes. -/
theorem ext_of_zero_treeDist {T T' : RootIndexed.Tree Root α} (h : treeDist T T' = 0) :
    T = T' := by
  funext r
  refine Tree.ext_of_zero_treeDist (le_antisymm ?_ (Tree.treeDist_nonneg _ _))
  rw [← h]
  exact le_ciSup (treeDist_bddAbove T T') r

/-- A uniform ball of level `n + 1` is a metric ball: agreeing with `T` up to
generation `n + 1` at every root is having sup distance less than
`(1 + n)⁻¹`. -/
theorem mem_uniformBall_iff_treeDist_lt (S T : RootIndexed.Tree Root α) (n : ℕ) :
    S ∈ uniformBall T (n + 1) ↔ treeDist S T < (1 + (n : ℝ))⁻¹ := by
  constructor
  · intro hS
    have hsup_le : treeDist S T ≤ (1 + ((n + 1 : ℕ) : ℝ))⁻¹ :=
      (ciSup_le_iff (treeDist_bddAbove S T)).2 fun r =>
        Tree.treeDist_le_inv_succ_of_lt_inv (S r) (T r) n
          ((Tree.mem_truncationBall_iff_treeDist_lt (T r) (S r) n).1 (hS r))
    exact lt_of_le_of_lt hsup_le (by
      rw [inv_lt_inv₀ (a := 1 + ((n + 1 : ℕ) : ℝ)) (b := 1 + (n : ℝ))
        (by positivity) (by positivity)]
      rw [Nat.cast_add, Nat.cast_one]
      linarith)
  · intro h r
    exact (Tree.mem_truncationBall_iff_treeDist_lt (T r) (S r) n).2
      (lt_of_le_of_lt (le_ciSup (treeDist_bddAbove S T) r) h)

/-- The sup tree distance packaged as a metric space on root-indexed trees. It
is a plain structure, not an instance: adding it does not change the default
product topology. The topology it induces is `metricTopology`. -/
@[instance_reducible]
noncomputable def metricSpace : MetricSpace (RootIndexed.Tree Root α) where
  dist := treeDist
  dist_self := treeDist_self
  dist_comm := treeDist_comm
  dist_triangle T₁ T₂ T₃ :=
    (treeDist_ultra T₁ T₂ T₃).trans
      (max_le_add_of_nonneg (treeDist_nonneg _ _) (treeDist_nonneg _ _))
  eq_of_dist_eq_zero := fun h => ext_of_zero_treeDist h

/-- The topology induced by the sup tree metric. It is identified with the
uniform topology in `metricTopology_eq_uniformTopology`. -/
@[instance_reducible]
noncomputable def metricTopology : TopologicalSpace (RootIndexed.Tree Root α) :=
  (metricSpace (Root := Root) (α := α)).toUniformSpace.toTopologicalSpace

section MetricTopology

attribute [local instance] metricSpace

theorem dist_eq_treeDist (T T' : RootIndexed.Tree Root α) :
    dist T T' = treeDist T T' := rfl

theorem metricSpace_isUltrametricDist :
    @IsUltrametricDist (RootIndexed.Tree Root α) (metricSpace (Root := Root) (α := α)).toDist :=
  ⟨treeDist_ultra⟩

/-- The metric balls are the uniform balls, so the metric topology is the
uniform topology. -/
theorem metricTopology_eq_uniformTopology :
    metricTopology (Root := Root) (α := α) =
      uniformTopology (Root := Root) (α := α) := by
  letI : MetricSpace (RootIndexed.Tree Root α) := metricSpace (Root := Root) (α := α)
  letI : TopologicalSpace (RootIndexed.Tree Root α) :=
    metricTopology (Root := Root) (α := α)
  refine le_antisymm ?_ ?_
  · -- the metric topology is finer than the uniform topology
    rw [uniformTopology, TopologicalSpace.le_generateFrom_iff_subset_isOpen]
    rintro s ⟨T, n, rfl⟩
    change IsOpen[(metricSpace (Root := Root) (α := α)).toUniformSpace.toTopologicalSpace]
      (uniformBall T n)
    rw [Metric.isOpen_iff]
    intro S hS
    refine ⟨(1 + (n : ℝ))⁻¹, inv_pos.2 (by positivity), ?_⟩
    intro S' hS'
    have hS'ball : S' ∈ uniformBall S (n + 1) := by
      rw [mem_uniformBall_iff_treeDist_lt]
      simpa [dist_eq_treeDist] using hS'
    exact uniformBall_subset_of_mem hS
      (uniformBall_anti S (Nat.le_succ n) hS'ball)
  · -- every metric-open set is a union of uniform balls
    rw [TopologicalSpace.le_def]
    intro U hU
    have hUmetric : IsOpen[(metricSpace (Root := Root) (α := α)).toUniformSpace.toTopologicalSpace] U :=
      hU
    have hloc : ∀ S : RootIndexed.Tree Root α, S ∈ U →
        ∃ n : ℕ, uniformBall S n ⊆ U := by
      intro S hS
      rcases (Metric.isOpen_iff.1 hUmetric S hS) with ⟨ε, hε, hball⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      have hn' : (1 + (n : ℝ))⁻¹ < ε := by
        rw [one_div] at hn
        rw [add_comm 1 (n : ℝ)]
        exact hn
      refine ⟨n + 1, ?_⟩
      intro S' hS'
      apply hball
      rw [Metric.mem_ball, dist_eq_treeDist]
      exact lt_trans ((mem_uniformBall_iff_treeDist_lt S' S n).1 hS') hn'
    choose n hn using fun p : {S : RootIndexed.Tree Root α // S ∈ U} =>
      hloc p.1 p.2
    have hUnion : U = ⋃ p : {S : RootIndexed.Tree Root α // S ∈ U},
        uniformBall p.1 (n p) := by
      refine Set.Subset.antisymm (fun S hS => Set.mem_iUnion.2 ⟨⟨S, hS⟩, ?_⟩) ?_
      · rw [mem_uniformBall]
        intro r
        exact Tree.mem_truncationBall.2 rfl
      · exact Set.iUnion_subset fun p => hn p
    rw [hUnion]
    exact @isOpen_iUnion (RootIndexed.Tree Root α)
      {S : RootIndexed.Tree Root α // S ∈ U}
      (uniformTopology (Root := Root) (α := α))
      (fun p => uniformBall p.1 (n p))
      (fun p => isOpen_uniformBall p.1 (n p))

end MetricTopology

end NonemptyRoot

end RootIndexed.Tree

end UlamHarris

end Combinatorics
