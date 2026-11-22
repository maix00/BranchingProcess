/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module
public import Combinatorics.UlamHarris.Tree.Topology.Metric.Reciprocal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential depth distance

## Public declarations

In namespace `Combinatorics.UlamHarris.Tree`:

* `expTreeDist` is $\exp(-(h+1))$ at finite agreement height $h$ and zero
  for equal trees. `expTreeDist_of_heightCongr_eq` gives this formula;
  `expTreeDist_of_truncate_eq_of_truncate_ne` identifies the first differing
  generation from two successive truncations.
* `expTreeDist_self`, `expTreeDist_comm`, `expTreeDist_nonneg`,
  `expTreeDist_eq_zero_iff`, and `expTreeDist_ultra` give the ultrametric laws.
* `expTreeDist_lt_iff` and `mem_truncationBall_iff_expTreeDist_lt` identify
  $d(T,T')<\exp(-(n+1))$ with agreement through generation $n+1$.
* `expTreeMetricSpace` and `expTreeMetricTopology` package the metric and
  topology as named structures, preserving the default topology.
* `expTreeMetricTopology_eq_treeMetricTopology` and
  `borel_expTreeMetricTopology_eq_borel_treeMetricTopology` identify the
  topologies and Borel sigma algebras of the exponential and reciprocal metrics.

At the first differing generation $m$, $h=m-1$ and $d(T,T')=\exp(-m)$.
Compare the rooted-tree framework in J. Neveu, "Arbres et processus de
Galton--Watson", Section 2, *Annales de l'I.H.P. Probabilités et statistiques*
22(2) (1986), 199--207, https://www.numdam.org/item/AIHPB_1986__22_2_199_0/.
-/
@[expose] public section
open MeasureTheory
namespace Combinatorics.UlamHarris.Tree
variable {α : Type*} [LT α]

private noncomputable def expHeightWeight : ℕ∞ → ℝ :=
  ENat.recTopCoe 0 (fun n ↦ Real.exp (-((n : ℝ) + 1)))

private lemma expHeightWeight_nonneg (h : ℕ∞) : 0 ≤ expHeightWeight h := by
  cases h using ENat.recTopCoe with
  | top => exact le_rfl
  | coe n => exact (Real.exp_pos _).le

private lemma expHeightWeight_strictAnti : StrictAnti expHeightWeight := by
  intro a b hab
  cases a using ENat.recTopCoe with
  | top => simp at hab
  | coe a =>
    cases b using ENat.recTopCoe with
    | top => exact Real.exp_pos _
    | coe b =>
      change Real.exp (-((b : ℝ) + 1)) < Real.exp (-((a : ℝ) + 1))
      apply Real.exp_lt_exp.mpr
      have h : a < b := by exact_mod_cast hab
      have hc : (a : ℝ) < b := Nat.cast_lt.mpr h
      linarith

/-- Exponential distance at the first differing generation. -/
noncomputable def expTreeDist (T T' : Tree α) : ℝ :=
  ENat.recTopCoe 0 (fun n ↦ Real.exp (-((n : ℝ) + 1))) (heightCongr T T')

@[simp] theorem expTreeDist_self (T : Tree α) : expTreeDist T T = 0 := by
  simp [expTreeDist, heightCongr_self]

theorem expTreeDist_comm (T T' : Tree α) : expTreeDist T T' = expTreeDist T' T := by
  rw [expTreeDist, expTreeDist, heightCongr_comm]

theorem expTreeDist_nonneg (T T' : Tree α) : 0 ≤ expTreeDist T T' :=
  expHeightWeight_nonneg _

theorem expTreeDist_eq_zero_iff (T T' : Tree α) : expTreeDist T T' = 0 ↔ T = T' := by
  constructor
  · intro h
    by_contra hne
    have hh : heightCongr T T' < ⊤ := lt_top_iff_ne_top.mpr
      (fun ht ↦ hne (heightCongr_eq_top_iff.mp ht))
    have hp := expHeightWeight_strictAnti hh
    change 0 < expTreeDist T T' at hp
    exact (ne_of_gt hp) h
  · rintro rfl
    exact expTreeDist_self _

/-- Agreement through $n$ with a difference at $n+1$ gives distance $e^{-(n+1)}$. -/
theorem expTreeDist_of_heightCongr_eq (T T' : Tree α) (n : ℕ)
    (h : heightCongr T T' = n) :
    expTreeDist T T' = Real.exp (-((n : ℝ) + 1)) := by
  rw [expTreeDist, h]
  rfl

/-- Equal truncations through $n$ and different truncations through $n+1$
identify the first differing generation exactly. -/
theorem expTreeDist_of_truncate_eq_of_truncate_ne (T T' : Tree α) (n : ℕ)
    (heq : T.truncate n = T'.truncate n)
    (hne : T.truncate (n + 1) ≠ T'.truncate (n + 1)) :
    expTreeDist T T' = Real.exp (-((n : ℝ) + 1)) := by
  apply expTreeDist_of_heightCongr_eq
  have hlo : (n : ℕ∞) ≤ heightCongr T T' := coe_le_heightCongr_iff.mpr heq
  have hhi : ¬ ((n + 1 : ℕ) : ℕ∞) ≤ heightCongr T T' :=
    fun h ↦ hne (coe_le_heightCongr_iff.mp h)
  apply le_antisymm _ hlo
  exact not_lt.mp (fun h ↦ hhi ((ENat.natCast_add_one_le_iff).mpr h))

theorem expTreeDist_ultra (T₁ T₂ T₃ : Tree α) :
    expTreeDist T₁ T₃ ≤ max (expTreeDist T₁ T₂) (expTreeDist T₂ T₃) := by
  obtain h | h := min_le_iff.mp (heightCongr_ultra T₁ T₂ T₃)
  · exact (expHeightWeight_strictAnti.antitone h).trans (le_max_left _ _)
  · exact (expHeightWeight_strictAnti.antitone h).trans (le_max_right _ _)

theorem expTreeDist_lt_iff (T T' : Tree α) (n : ℕ) :
    expTreeDist T T' < Real.exp (-((n : ℝ) + 1)) ↔
      ((n + 1 : ℕ) : ℕ∞) ≤ heightCongr T T' := by
  change expHeightWeight (heightCongr T T') < expHeightWeight (n : ℕ∞) ↔ _
  rw [expHeightWeight_strictAnti.lt_iff_gt]
  exact (ENat.natCast_add_one_le_iff (m := n) (n := heightCongr T T')).symm

theorem mem_truncationBall_iff_expTreeDist_lt (T S : Tree α) (n : ℕ) :
    S ∈ truncationBall T (n + 1) ↔ expTreeDist S T < Real.exp (-((n : ℝ) + 1)) := by
  rw [mem_truncationBall]
  exact (coe_le_heightCongr_iff (T := S) (T' := T) (n := n + 1)).symm.trans
    (expTreeDist_lt_iff S T n).symm

/-- The exponential metric, as a named structure. -/
@[instance_reducible]
noncomputable def expTreeMetricSpace (α : Type*) [LT α] : MetricSpace (Tree α) where
  dist := expTreeDist
  dist_self := expTreeDist_self
  dist_comm := expTreeDist_comm
  dist_triangle T₁ T₂ T₃ := (expTreeDist_ultra T₁ T₂ T₃).trans
    (max_le_add_of_nonneg (expTreeDist_nonneg _ _) (expTreeDist_nonneg _ _))
  eq_of_dist_eq_zero := fun h ↦ (expTreeDist_eq_zero_iff _ _).mp h

/-- The topology of exponential depth distance. -/
@[instance_reducible]
noncomputable def expTreeMetricTopology (α : Type*) [LT α] : TopologicalSpace (Tree α) :=
  (expTreeMetricSpace α).toUniformSpace.toTopologicalSpace

private theorem expTreeMetricTopology_eq_truncationTopology :
    expTreeMetricTopology α = treeTruncationTopology (α := α) := by
  let : MetricSpace (Tree α) := expTreeMetricSpace α
  let : TopologicalSpace (Tree α) := expTreeMetricTopology α
  rw [le_antisymm_iff]
  constructor
  · rw [TopologicalSpace.le_def]
    intro U hU
    rw [Metric.isOpen_iff]
    intro T hT
    obtain ⟨n, hn⟩ := (isOpen_truncation_iff_ball U).mp hU T hT
    refine ⟨Real.exp (-((n : ℝ) + 1)), Real.exp_pos _, ?_⟩
    intro S hS
    exact hn (truncationBall_anti T (Nat.le_succ n)
      ((mem_truncationBall_iff_expTreeDist_lt T S n).mpr hS))
  · rw [TopologicalSpace.le_def]
    intro U hU
    rw [isOpen_truncation_iff_ball]
    intro T hT
    obtain ⟨ε, hε, hb⟩ := (Metric.isOpen_iff.mp hU) T hT
    obtain ⟨n, hn⟩ := exists_nat_gt (-Real.log ε)
    have he : Real.exp (-((n : ℝ) + 1)) < ε := by
      rw [← Real.exp_log hε]
      apply Real.exp_lt_exp.mpr
      linarith
    refine ⟨n + 1, ?_⟩
    intro S hS
    exact hb (lt_trans ((mem_truncationBall_iff_expTreeDist_lt T S n).mp hS) he)

/-- Exponential and reciprocal depth distances induce the same topology. -/
theorem expTreeMetricTopology_eq_treeMetricTopology (α : Type*) [LT α] :
    expTreeMetricTopology α = treeMetricTopology α := by
  rw [expTreeMetricTopology_eq_truncationTopology, treeMetricTopology_eq_truncationTopology]

/-- Both metrics generate the same Borel sigma algebra. -/
theorem borel_expTreeMetricTopology_eq_borel_treeMetricTopology (α : Type*) [LT α] :
    @borel (Tree α) (expTreeMetricTopology α) = @borel (Tree α) (treeMetricTopology α) := by
  rw [expTreeMetricTopology_eq_treeMetricTopology]

end Combinatorics.UlamHarris.Tree
