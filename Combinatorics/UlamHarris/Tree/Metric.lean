module

public import Combinatorics.UlamHarris.Tree.Height
public import Combinatorics.UlamHarris.Tree.Borel
public import Mathlib.Topology.MetricSpace.Ultra.Basic

/-!
# The tree metric and its topology

`treeDist T T' = 1 / (1 + ‖T, T'‖ₕ)` is the distance used for Ulam--Harris
trees: it is zero exactly when the two trees are equal, and it equals
`(1 + n)⁻¹` as soon as the trees agree up to generation `n` and differ at
generation `n + 1`. The truncation balls are therefore the metric balls,
`Tree.truncationBall T (n + 1) = {S | treeDist S T < (1 + n)⁻¹}`, and the metric
is ultrametric because agreement heights satisfy `heightCongr_ultra`.

The metric is exposed as the structure `treeMetricSpace` and *not* as a global
instance: the default topology of `Tree α` is whatever the surrounding
development gives it, and this file adds the metric as an extra structure. The
topology it induces is `treeMetricTopology`, which
`treeMetricTopology_eq_truncationTopology` identifies with the truncation
topology of `Topology.lean`; the Borel σ-algebras of the two therefore coincide
(`borel_treeMetricTopology_eq_borel_treeTruncationTopology`). The comparison
with the cylinder σ-algebra is in `Borel.lean`.

Everything about the metric is stated for the raw function `treeDist`, so no
instance is needed to use it.
-/

@[expose] public section

open MeasureTheory
open scoped Topology ENNReal

set_option linter.style.haveILetI false

namespace Combinatorics

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- The tree metric: `1 / (1 + n)` where `n` is the height up to which the
trees agree, with the value zero when they agree at every height. -/
noncomputable def treeDist (T T' : Tree α) : ℝ :=
  ((1 + (heightCongr T T' : ℝ≥0∞))⁻¹).toReal

theorem treeDist_self (T : Tree α) : treeDist T T = 0 := by
  simp [treeDist, heightCongr_self]

theorem treeDist_comm (T T' : Tree α) : treeDist T T' = treeDist T' T := by
  simp [treeDist, heightCongr_comm]

theorem treeDist_nonneg (T T' : Tree α) : 0 ≤ treeDist T T' :=
  ENNReal.toReal_nonneg

/-- The distance is zero exactly for equal trees. -/
theorem ext_of_zero_treeDist {T T' : Tree α} (h : treeDist T T' = 0) :
    T = T' := by
  rw [treeDist] at h
  rcases (ENNReal.toReal_eq_zero_iff _).1 h with h0 | htop
  · have htop : (heightCongr T T' : ℝ≥0∞) = ⊤ := by
      rcases (ENNReal.add_eq_top.1 (ENNReal.inv_eq_zero.1 h0)) with h | h
      · exact absurd h (by simp)
      · exact h
    exact heightCongr_eq_top_iff.1 (ENat.toENNReal_eq_top.1 htop)
  · exact absurd htop (by simp)

theorem treeDist_eq_zero_iff (T T' : Tree α) :
    treeDist T T' = 0 ↔ T = T' :=
  ⟨ext_of_zero_treeDist, fun h => h ▸ treeDist_self T⟩

private lemma treeDist_eq_aux (T T' : Tree α) :
    (fun x : ℕ∞ => -((1 + (x : ℝ≥0∞))⁻¹).toReal) (heightCongr T T') =
      -treeDist T T' := rfl

private lemma treeDist_mono' :
    StrictMono (fun x : ℕ∞ => -((1 + (x : ℝ≥0∞))⁻¹).toReal) := by
  intro a b hab
  have hlt : (a : ℝ≥0∞) < (b : ℝ≥0∞) := ENat.toENNReal_lt.2 hab
  have hadd : 1 + (a : ℝ≥0∞) < 1 + (b : ℝ≥0∞) :=
    (ENNReal.add_lt_add_iff_left (by simp)).2 hlt
  have hinv : (1 + (b : ℝ≥0∞))⁻¹ < (1 + (a : ℝ≥0∞))⁻¹ :=
    ENNReal.inv_lt_inv.2 hadd
  have hreal := (ENNReal.toReal_lt_toReal (by simp) (by simp)).2 hinv
  simpa [neg_lt_neg_iff] using hreal

private lemma treeDist_mono :
    Monotone (fun x : ℕ∞ => -((1 + (x : ℝ≥0∞))⁻¹).toReal) :=
  treeDist_mono'.monotone

/-- The tree distance is ultrametric. -/
theorem treeDist_ultra (T1 T2 T3 : Tree α) :
    treeDist T1 T3 ≤ max (treeDist T1 T2) (treeDist T2 T3) := by
  rw [le_max_iff]
  by_contra h
  simp only [not_or, not_le] at h
  have hultra := heightCongr_ultra T1 T2 T3
  rw [min_le_iff] at hultra
  rcases hultra with h12 | h23
  · have := treeDist_mono h12
    rw [treeDist_eq_aux, treeDist_eq_aux] at this
    simp only [neg_le_neg_iff] at this
    exact (not_lt_of_ge this) h.1
  · have := treeDist_mono h23
    rw [treeDist_eq_aux, treeDist_eq_aux] at this
    simp only [neg_le_neg_iff] at this
    exact (not_lt_of_ge this) h.2

/-- The distance to a fixed tree, as a function of the agreement height: the
trees at distance `< (1 + n)⁻¹` from `T` are exactly the trees agreeing with
`T` up to generation `n + 1`. -/
theorem treeDist_lt_inv_iff (T T' : Tree α) (n : ℕ) :
    treeDist T T' < (1 + (n : ℝ))⁻¹ ↔
      ((n + 1 : ℕ) : ℕ∞) ≤ heightCongr T T' := by
  have hfun : StrictMono (fun x : ℕ∞ => -((1 + (x : ℝ≥0∞))⁻¹).toReal) :=
    treeDist_mono'
  have h1 : (fun x : ℕ∞ => -((1 + (x : ℝ≥0∞))⁻¹).toReal) (heightCongr T T') =
      -treeDist T T' := treeDist_eq_aux T T'
  have h2 : (fun x : ℕ∞ => -((1 + (x : ℝ≥0∞))⁻¹).toReal) ((n : ℕ) : ℕ∞) =
      -((1 + (n : ℝ))⁻¹) := by
    simp only [ENat.toENNReal_coe]
    rw [ENNReal.toReal_inv, ENNReal.toReal_add (by simp) (by simp), ENNReal.toReal_one,
      ENNReal.toReal_natCast]
  rw [← neg_lt_neg_iff, ← h1, ← h2, hfun.lt_iff_lt]
  exact (ENat.natCast_add_one_le_iff (m := n) (n := heightCongr T T')).symm

/-- Membership in a truncation ball, in terms of the tree distance: agreeing
with `T` up to generation `n + 1` is having distance less than `(1 + n)⁻¹`. -/
theorem mem_truncationBall_iff_treeDist_lt (T S : Tree α) (n : ℕ) :
    S ∈ Tree.truncationBall T (n + 1) ↔
      treeDist S T < (1 + (n : ℝ))⁻¹ := by
  rw [Tree.mem_truncationBall]
  exact (coe_le_heightCongr_iff (T := S) (T' := T) (n := n + 1)).symm.trans
    (treeDist_lt_inv_iff S T n).symm

/-- Truncation balls are metric balls. -/
theorem truncationBall_eq_ball (T : Tree α) (n : ℕ) :
    Tree.truncationBall T (n + 1) =
      {S : Tree α | treeDist S T < (1 + (n : ℝ))⁻¹} :=
  Set.ext fun _ => mem_truncationBall_iff_treeDist_lt T _ n

/-- The tree distance packaged as a metric space on `Tree α`. It is a plain
structure, not an instance: adding it does not change the default topology of
`Tree α`. The topology it induces is `treeMetricTopology`. -/
@[instance_reducible]
noncomputable def treeMetricSpace (α : Type*) [LT α] : MetricSpace (Tree α) where
  dist := treeDist
  dist_self := treeDist_self
  dist_comm := treeDist_comm
  dist_triangle T1 T2 T3 :=
    le_trans (treeDist_ultra T1 T2 T3)
      (max_le_add_of_nonneg (treeDist_nonneg _ _) (treeDist_nonneg _ _))
  eq_of_dist_eq_zero := fun h => ext_of_zero_treeDist h

/-- The topology induced by the tree metric. It is identified with the
truncation topology in `treeMetricTopology_eq_truncationTopology`. -/
@[instance_reducible]
noncomputable def treeMetricTopology (α : Type*) [LT α] : TopologicalSpace (Tree α) :=
  (treeMetricSpace α).toUniformSpace.toTopologicalSpace

section MetricTopology

attribute [local instance] treeMetricSpace

theorem dist_eq_treeDist (T T' : Tree α) :
    dist T T' = treeDist T T' := rfl

theorem treeMetricSpace_isUltrametricDist :
    @IsUltrametricDist (Tree α) (treeMetricSpace α).toDist :=
  ⟨treeDist_ultra⟩

theorem treeMetricTopology_eq_truncationTopology (α : Type*) [LT α] :
    treeMetricTopology α = treeTruncationTopology (α := α) := by
  letI : MetricSpace (Tree α) := treeMetricSpace α
  letI : TopologicalSpace (Tree α) := treeMetricTopology α
  rw [le_antisymm_iff]
  constructor
  · -- every truncation-open set is metric-open
    rw [TopologicalSpace.le_def]
    intro U hU
    rw [Metric.isOpen_iff]
    intro T hT
    obtain ⟨n, hn⟩ := (isOpen_truncation_iff_ball U).1 hU T hT
    refine ⟨(1 + (n : ℝ))⁻¹, inv_pos.2 (by positivity), ?_⟩
    rintro S hS
    have hST : S ∈ Tree.truncationBall T (n + 1) := by
      rw [mem_truncationBall_iff_treeDist_lt]
      simpa [dist_eq_treeDist] using hS
    exact hn (truncationBall_anti T (Nat.le_succ n) hST)
  · -- every metric-open set is truncation-open
    rw [TopologicalSpace.le_def]
    intro U hU
    rw [isOpen_truncation_iff_ball]
    intro T hT
    rcases (Metric.isOpen_iff.1 hU T hT) with ⟨ε, hε, hball⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    refine ⟨n + 1, ?_⟩
    have hn' : (1 + (n : ℝ))⁻¹ < ε := by
      rw [one_div] at hn
      rw [add_comm 1 (n : ℝ)]
      exact hn
    intro S hS
    rw [mem_truncationBall_iff_treeDist_lt] at hS
    have hdist : dist S T < ε := by
      rw [dist_eq_treeDist]
      exact lt_trans hS hn'
    exact hball (Metric.mem_ball.2 hdist)

end MetricTopology

/-- The Borel σ-algebra of the tree metric coincides with that of the
truncation topology. -/
theorem borel_treeMetricTopology_eq_borel_treeTruncationTopology (α : Type*) [LT α] :
    @borel (Tree α) (treeMetricTopology α) = @borel (Tree α) treeTruncationTopology := by
  rw [treeMetricTopology_eq_truncationTopology]

/-- The cylinder σ-algebra is contained in the Borel σ-algebra of the tree
metric. For finitely many labels the two σ-algebras coincide
(`borel_treeMetricTopology_eq_cylinder_of_finite`, in
`Tree/FiniteLabels.lean`). -/
theorem cylinder_le_borel_treeMetricTopology [Countable α] :
    instMeasurableSpaceTree ≤ @borel (Tree α) (treeMetricTopology α) := by
  rw [borel_treeMetricTopology_eq_borel_treeTruncationTopology α]
  exact cylinder_le_borel_truncation

theorem treeDist_le_one (T T' : UlamHarris.Tree α) : treeDist T T' ≤ 1 := by
  rw [treeDist, ← ENNReal.toReal_one]
  refine (ENNReal.toReal_le_toReal ?_ ?_).2 ?_
  · rw [ENNReal.inv_ne_top]
    simp
  · simp
  · rw [ENNReal.inv_le_one]
    simp

theorem treeDist_le_inv_succ_of_lt_inv (S T : UlamHarris.Tree α) (n : ℕ)
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

/-- The sup tree distance on root-indexed trees. -/
noncomputable def treeDist (T T' : RootIndexed.Tree Root α) : ℝ :=
  ⨆ r, UlamHarris.Tree.treeDist (T r) (T' r)

theorem treeDist_bddAbove (T T' : RootIndexed.Tree Root α) :
    BddAbove (Set.range fun r : Root => UlamHarris.Tree.treeDist (T r) (T' r)) :=
  ⟨1, by rintro _ ⟨r, rfl⟩; exact UlamHarris.Tree.treeDist_le_one _ _⟩

section NonemptyRoot

variable [Nonempty Root]

theorem treeDist_self (T : RootIndexed.Tree Root α) : treeDist T T = 0 := by
  rw [treeDist]
  simp only [UlamHarris.Tree.treeDist_self]
  exact ciSup_const

omit [Nonempty Root] in
theorem treeDist_comm (T T' : RootIndexed.Tree Root α) :
    treeDist T T' = treeDist T' T := by
  rw [treeDist, treeDist]
  exact congrArg _ (funext fun r => UlamHarris.Tree.treeDist_comm _ _)

omit [Nonempty Root] in
theorem treeDist_nonneg (T T' : RootIndexed.Tree Root α) : 0 ≤ treeDist T T' :=
  Real.iSup_nonneg fun _ => UlamHarris.Tree.treeDist_nonneg _ _

theorem treeDist_le_one (T T' : RootIndexed.Tree Root α) : treeDist T T' ≤ 1 :=
  (ciSup_le_iff (treeDist_bddAbove T T')).2 fun _ =>
    UlamHarris.Tree.treeDist_le_one _ _

theorem treeDist_ultra (T₁ T₂ T₃ : RootIndexed.Tree Root α) :
    treeDist T₁ T₃ ≤ max (treeDist T₁ T₂) (treeDist T₂ T₃) :=
  (ciSup_le_iff (treeDist_bddAbove T₁ T₃)).2 fun r =>
    (UlamHarris.Tree.treeDist_ultra _ _ _).trans (max_le_max
      (le_ciSup (treeDist_bddAbove T₁ T₂) r)
      (le_ciSup (treeDist_bddAbove T₂ T₃) r))

omit [Nonempty Root] in
theorem ext_of_zero_treeDist {T T' : RootIndexed.Tree Root α} (h : treeDist T T' = 0) :
    T = T' := by
  funext r
  refine UlamHarris.Tree.ext_of_zero_treeDist
    (le_antisymm ?_ (UlamHarris.Tree.treeDist_nonneg _ _))
  rw [← h]
  exact le_ciSup (treeDist_bddAbove T T') r

theorem mem_uniformBall_iff_treeDist_lt (S T : RootIndexed.Tree Root α) (n : ℕ) :
    S ∈ uniformBall T (n + 1) ↔ treeDist S T < (1 + (n : ℝ))⁻¹ := by
  constructor
  · intro hS
    have hsup_le : treeDist S T ≤ (1 + ((n + 1 : ℕ) : ℝ))⁻¹ :=
      (ciSup_le_iff (treeDist_bddAbove S T)).2 fun r =>
        UlamHarris.Tree.treeDist_le_inv_succ_of_lt_inv (S r) (T r) n
          ((UlamHarris.Tree.mem_truncationBall_iff_treeDist_lt (T r) (S r) n).1
            (hS r))
    exact lt_of_le_of_lt hsup_le (by
      rw [inv_lt_inv₀ (a := 1 + ((n + 1 : ℕ) : ℝ)) (b := 1 + (n : ℝ))
        (by positivity) (by positivity)]
      rw [Nat.cast_add, Nat.cast_one]
      linarith)
  · intro h r
    exact (UlamHarris.Tree.mem_truncationBall_iff_treeDist_lt (T r) (S r) n).2
      (lt_of_le_of_lt (le_ciSup (treeDist_bddAbove S T) r) h)

@[instance_reducible]
noncomputable def metricSpace : MetricSpace (RootIndexed.Tree Root α) where
  dist := treeDist
  dist_self := treeDist_self
  dist_comm := treeDist_comm
  dist_triangle T₁ T₂ T₃ :=
    (treeDist_ultra T₁ T₂ T₃).trans
      (max_le_add_of_nonneg (treeDist_nonneg _ _) (treeDist_nonneg _ _))
  eq_of_dist_eq_zero := fun h => ext_of_zero_treeDist h

@[instance_reducible]
noncomputable def metricTopology : TopologicalSpace (RootIndexed.Tree Root α) :=
  (metricSpace (Root := Root) (α := α)).toUniformSpace.toTopologicalSpace

section MetricTopology

attribute [local instance] metricSpace

theorem dist_eq_treeDist (T T' : RootIndexed.Tree Root α) :
    dist T T' = treeDist T T' := rfl

theorem metricSpace_isUltrametricDist :
    @IsUltrametricDist (RootIndexed.Tree Root α)
      (metricSpace (Root := Root) (α := α)).toDist :=
  ⟨treeDist_ultra⟩

theorem metricTopology_eq_uniformTopology :
    metricTopology (Root := Root) (α := α) =
      uniformTopology (Root := Root) (α := α) := by
  letI : MetricSpace (RootIndexed.Tree Root α) :=
    metricSpace (Root := Root) (α := α)
  letI : TopologicalSpace (RootIndexed.Tree Root α) :=
    metricTopology (Root := Root) (α := α)
  refine le_antisymm ?_ ?_
  · rw [uniformTopology, TopologicalSpace.le_generateFrom_iff_subset_isOpen]
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
  · rw [TopologicalSpace.le_def]
    intro U hU
    have hUmetric :
        IsOpen[(metricSpace (Root := Root) (α := α)).toUniformSpace.toTopologicalSpace] U := hU
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
        exact UlamHarris.Tree.mem_truncationBall.2 rfl
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

namespace RootIndexed.Tree

variable {Root α : Type*} [LT α]

/-- The Borel σ-algebras of the uniform and metric topologies coincide. -/
theorem borel_uniformTopology_eq_borel_metricTopology [Nonempty Root] :
    @borel (RootIndexed.Tree Root α)
        (metricTopology (Root := Root) (α := α)) =
      @borel (RootIndexed.Tree Root α)
        (uniformTopology (Root := Root) (α := α)) := by
  rw [metricTopology_eq_uniformTopology]

/-- If the uniform topology has a countable basis of cylinder-measurable sets,
then the Borel σ-algebra of the sup metric is the cylinder σ-algebra. -/
theorem borel_metricTopology_eq_cylinder_of_countable_basis [Nonempty Root]
    [Countable Root] [Countable α]
    {B : Set (Set (RootIndexed.Tree Root α))}
    (hB : TopologicalSpace.IsTopologicalBasis
      (t := uniformTopology (Root := Root) (α := α)) B)
    (hcount : B.Countable) (hmeas : ∀ s ∈ B, MeasurableSet s) :
    @borel (RootIndexed.Tree Root α)
        (metricTopology (Root := Root) (α := α)) =
      (inferInstance : MeasurableSpace (RootIndexed.Tree Root α)) := by
  rw [borel_uniformTopology_eq_borel_metricTopology]
  exact borel_uniformTopology_eq_cylinder_of_countable_basis hB hcount hmeas

end RootIndexed.Tree

end UlamHarris

end Combinatorics

end
