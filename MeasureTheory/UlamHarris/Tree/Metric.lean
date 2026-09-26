import MeasureTheory.UlamHarris.Tree.Height
import MeasureTheory.UlamHarris.Tree.Borel
import Mathlib.Topology.MetricSpace.Ultra.Basic

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

open MeasureTheory
open scoped Topology ENNReal

set_option linter.style.haveILetI false

namespace MeasureTheory

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

end Tree

end UlamHarris

end MeasureTheory
