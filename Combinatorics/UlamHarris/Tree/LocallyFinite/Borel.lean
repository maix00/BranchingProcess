/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module
public import Combinatorics.UlamHarris.Tree.LocallyFinite.Approximation
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Borel sigma algebra of locally finite trees

## Public declarations

* `Combinatorics.UlamHarris.Tree.LocallyFinite.borel_metricTopology_eq_measurableSpace`:
  for countable child labels, the Borel sigma algebra of depth distance on
  locally finite trees equals the trace of the membership-cylinder sigma algebra.
  Finite truncations give a countable basis of measurable depth balls.

The tree sigma algebra follows J. Neveu, "Arbres et processus de
Galton--Watson", Section 2, *Annales de l'I.H.P. Probabilités et statistiques*
22(2) (1986), 199--207, https://www.numdam.org/item/AIHPB_1986__22_2_199_0/.
-/
@[expose] public section
open MeasureTheory TopologicalSpace
namespace Combinatorics.UlamHarris.Tree.LocallyFinite

/-- For countable labels, depth-Borel sets on locally finite trees are exactly cylinders. -/
theorem borel_metricTopology_eq_measurableSpace {α : Type*} [LT α] [Countable α] :
    @borel (LocallyFiniteTree α) (metricTopology α) = measurableSpace α := by
  let : MetricSpace (Tree α) := treeMetricSpace α
  let : TopologicalSpace (Tree α) := treeMetricTopology α
  let : MetricSpace (LocallyFiniteTree α) := metricSpace α
  let : TopologicalSpace (LocallyFiniteTree α) := metricTopology α
  let : Countable (FiniteTree α) := finiteTree_countable
  let ball : FiniteTree α × ℕ → Set (LocallyFiniteTree α) :=
    fun p ↦ Subtype.val ⁻¹' truncationBall p.1.1 p.2
  have hcount : (Set.range ball).Countable := Set.countable_range ball
  have hopen : ∀ U ∈ Set.range ball, IsOpen U := by
    rintro U ⟨p, rfl⟩
    apply isOpen_induced
    have h : @IsOpen (Tree α) treeTruncationTopology (truncationBall p.1.1 p.2) :=
      isOpen_truncationBall _ _
    rwa [← treeMetricTopology_eq_truncationTopology] at h
  have hbasis : IsTopologicalBasis (Set.range ball) := by
    apply isTopologicalBasis_of_isOpen_of_nhds hopen
    intro T U hTU hU
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU T hTU
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    let τ : FiniteTree α := ⟨T.1.truncate (n + 1), T.2.isFinite_truncate _⟩
    refine ⟨ball (τ, n + 1), ⟨(τ, n + 1), rfl⟩, ?_, ?_⟩
    · simp [ball, τ, mem_truncationBall]
    · intro S hS
      have he : S.1.truncate (n + 1) = T.1.truncate (n + 1) := by
        simpa [ball, τ, mem_truncationBall] using hS
      have hd := (mem_truncationBall_iff_treeDist_lt T.1 S.1 n).mp he
      have hr : (1 + (n : ℝ))⁻¹ < ε := by simpa [one_div, add_comm] using hn
      exact hb (hd.trans hr)
  apply le_antisymm
  · let : SecondCountableTopology (LocallyFiniteTree α) :=
      hbasis.secondCountableTopology hcount
    rw [hbasis.borel_eq_generateFrom]
    apply MeasurableSpace.generateFrom_le
    rintro U ⟨p, rfl⟩
    exact (truncationBall_measurable p.1.1 p.2).preimage measurable_subtype_coe
  · exact measurableSpace_le_borel_metricTopology

end Combinatorics.UlamHarris.Tree.LocallyFinite
