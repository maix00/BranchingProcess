/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module
public import Combinatorics.UlamHarris.Tree.Topology.Metric.Exponential
public import Combinatorics.UlamHarris.Tree.Truncation.Limit
public import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Completeness of depth distance on rooted trees

## Public declarations

* `Combinatorics.UlamHarris.Tree.completeSpace_treeMetricSpace` proves
  completeness of the reciprocal depth metric for any child-label type.
  A Cauchy sequence has eventually constant truncations at every height,
  and converges to the tree of its eventually present nodes.
* `Combinatorics.UlamHarris.Tree.completeSpace_expTreeMetricSpace` proves
  completeness for exponential depth distance using the same criterion.

The rooted-tree space is that of J. Neveu, "Arbres et processus de
Galton--Watson", Section 2, *Annales de l'I.H.P. Probabilités et statistiques*
22(2) (1986), 199--207, https://www.numdam.org/item/AIHPB_1986__22_2_199_0/.
-/
@[expose] public section
open Filter
open scoped Topology
namespace Combinatorics.UlamHarris.Tree

private theorem completeSpace_of_truncationBalls {α : Type*} [LT α]
    (m : MetricSpace (Tree α)) (radius : ℕ → ℝ) (hpos : ∀ n, 0 < radius n)
    (hsmall : ∀ ε > 0, ∃ n, radius n < ε)
    (hball : ∀ T S n, S ∈ truncationBall T (n + 1) ↔
      @dist (Tree α) m.toDist S T < radius n) :
    @CompleteSpace (Tree α) m.toUniformSpace := by
  let : MetricSpace (Tree α) := m
  apply Metric.complete_of_cauchySeq_tendsto
  intro s hs
  refine ⟨liminf s, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨n, hn⟩ := hsmall ε hε
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hs _ (hpos n)
  have hstable : ∀ k ≥ N, (s k).truncate (n + 1) = (s N).truncate (n + 1) := by
    intro k hk
    exact (hball (s N) (s k) n).mpr (hN k hk N le_rfl)
  have hlim := truncate_liminf_eq_of_stable s (n + 1) N hstable
  refine ⟨N, fun k hk ↦ ?_⟩
  have hb : s k ∈ truncationBall (liminf s) (n + 1) :=
    (hstable k hk).trans hlim.symm
  exact ((hball (liminf s) (s k) n).mp hb).trans hn

/-- Every depth-Cauchy sequence converges; no local-finiteness assumption is required. -/
theorem completeSpace_treeMetricSpace (α : Type*) [LT α] :
    @CompleteSpace (Tree α) (treeMetricSpace α).toUniformSpace := by
  apply completeSpace_of_truncationBalls (treeMetricSpace α) (fun n ↦ (1 + (n : ℝ))⁻¹)
  · intro n
    exact inv_pos.mpr (by positivity)
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact ⟨n, by simpa [one_div, add_comm] using hn⟩
  · exact mem_truncationBall_iff_treeDist_lt

/-- Exponential depth distance is complete by the same stable-truncation criterion. -/
theorem completeSpace_expTreeMetricSpace (α : Type*) [LT α] :
    @CompleteSpace (Tree α) (expTreeMetricSpace α).toUniformSpace := by
  apply completeSpace_of_truncationBalls (expTreeMetricSpace α)
    (fun n ↦ Real.exp (-((n : ℝ) + 1)))
  · intro n
    exact Real.exp_pos _
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (-Real.log ε)
    refine ⟨n, ?_⟩
    rw [← Real.exp_log hε]
    apply Real.exp_lt_exp.mpr
    linarith
  · exact mem_truncationBall_iff_expTreeDist_lt

end Combinatorics.UlamHarris.Tree
