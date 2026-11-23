/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module
public import Combinatorics.UlamHarris.Tree.Topology.Metric.Exponential
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Strictness of the depth-Borel sigma algebra

## Public declarations

* `Combinatorics.UlamHarris.Tree.cylinder_lt_borel_treeMetricTopology`
  proves that the membership-cylinder sigma algebra of trees with countably infinite ordered
  child labels having a least element is strictly smaller than their depth-metric Borel sigma algebra.
* `Combinatorics.UlamHarris.Tree.cylinder_lt_borel_expTreeMetricTopology`
  states the same strict inclusion for exponential depth distance.

The full tree space contains a continuum-sized family of depth-two trees
with pairwise disjoint depth-two balls. All unions of these balls are open,
whereas the countably generated cylinder sigma algebra has at most continuum
many sets. Mathlib's cardinal bound for generated sigma algebras and Cantor's
inequality give strictness. The tree framework follows J. Neveu, "Arbres et
processus de Galton--Watson", Section 2, *Annales de l'I.H.P. Probabilités et
statistiques* 22(2) (1986), 199--207,
https://www.numdam.org/item/AIHPB_1986__22_2_199_0/.
-/
@[expose] public section
open MeasureTheory TopologicalSpace Cardinal
namespace Combinatorics.UlamHarris.Tree

variable {α : Type*} [LinearOrder α] [OrderBot α]

private def tips (b : α → Bool) : Tree α where
  carrier := {u | u.length ≤ 1 ∨ ∃ i, u = [i, ⊥] ∧ b i = true}
  root_mem := Or.inl (by simp)
  parent_closed := by
    intro u v h
    by_cases hu : u.length ≤ 1
    · exact Or.inl hu
    · have hv : v = [] := by
        have hl : (u ++ v).length ≤ 2 := by
          rcases h with h | ⟨i, hi, _⟩
          · omega
          · simp [hi]
        have : v.length = 0 := by simp only [List.length_append] at hl; omega
        exact List.length_eq_zero_iff.mp this
      simpa [hv] using h
  sibling_closed := by
    intro u i j h hij
    rcases h with h | ⟨k, hk, hb⟩
    · exact Or.inl (by simpa only [List.length_append, List.length_singleton] using h)
    · have hj : j = ⊥ := by
        have hh := congrArg List.getLast? hk
        simpa using hh
      simp [hj] at hij

private lemma tips_injective : Function.Injective (tips (α := α)) := by
  intro b c h
  funext i
  have hm := congrArg (fun T : Tree α ↦ [i, ⊥] ∈ T.carrier) h
  have he : b i = true ↔ c i = true := by simpa [tips] using Iff.of_eq hm
  cases hb : b i <;> cases hc : c i <;> simp_all

private lemma tips_truncate (b : α → Bool) : (tips b).truncate 2 = tips b := by
  ext u
  simp only [mem_truncate]
  constructor
  · exact And.right
  · intro hu
    refine ⟨?_, hu⟩
    rcases hu with h | ⟨i, rfl, _⟩
    · omega
    · simp

private lemma tips_mem_ball_iff (b c : α → Bool) :
    tips b ∈ truncationBall (tips c) 2 ↔ b = c := by
  rw [mem_truncationBall, tips_truncate, tips_truncate]
  exact tips_injective.eq_iff

/-- On the full countably infinite-label tree space, depth-Borel measurability strictly exceeds cylinders. -/
theorem cylinder_lt_borel_treeMetricTopology [Countable α] [Infinite α] :
    instMeasurableSpaceTree (α := α) < @borel (Tree α) (treeMetricTopology α) := by
  apply lt_of_le_of_ne cylinder_le_borel_treeMetricTopology
  intro heq
  let U : Set (α → Bool) → Set (Tree α) :=
    fun A ↦ ⋃ b ∈ A, truncationBall (tips b) 2
  have hm (A : Set (α → Bool)) : MeasurableSet (U A) := by
    rw [heq]
    change MeasurableSpace.GenerateMeasurable {s | @IsOpen (Tree α) (treeMetricTopology α) s} (U A)
    apply MeasurableSpace.GenerateMeasurable.basic
    rw [treeMetricTopology_eq_truncationTopology]
    let : TopologicalSpace (Tree α) := treeTruncationTopology
    exact isOpen_iUnion (fun b ↦ isOpen_iUnion (fun _ ↦ isOpen_truncationBall _ _))
  have hU (A : Set (α → Bool)) (b : α → Bool) : tips b ∈ U A ↔ b ∈ A := by
    simp only [U, Set.mem_iUnion, tips_mem_ball_iff]
    simp
  have hi : Function.Injective (fun A : Set (α → Bool) ↦
      (⟨U A, hm A⟩ : {s : Set (Tree α) // MeasurableSet s})) := by
    intro A B h
    ext b
    have hh := congrArg (fun C : {s : Set (Tree α) // MeasurableSet s} ↦ tips b ∈ C.1) h
    simpa only [hU] using Iff.of_eq hh
  have hcount := MeasurableSpace.countable_countableGeneratingSet (α := Tree α)
  let : Countable (MeasurableSpace.countableGeneratingSet (Tree α)) := hcount.to_subtype
  have hgen := MeasurableSpace.generateFrom_countableGeneratingSet (α := Tree α)
  have hcard : #{s : Set (Tree α) // MeasurableSet s} ≤ 𝔠 := by
    rw [← hgen]
    exact MeasurableSpace.cardinal_measurableSet_le_continuum
      (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
  have hbig := (Cardinal.mk_le_of_injective hi).trans hcard
  have hc : #(α → Bool) = 𝔠 := by
    simp [Cardinal.mk_eq_aleph0, Cardinal.two_power_aleph0]
  rw [Cardinal.mk_set, hc] at hbig
  exact (not_le_of_gt (Cardinal.cantor 𝔠)) hbig

/-- The same strict inclusion holds for the exponential depth metric. -/
theorem cylinder_lt_borel_expTreeMetricTopology [Countable α] [Infinite α] :
    instMeasurableSpaceTree (α := α) < @borel (Tree α) (expTreeMetricTopology α) := by
  rw [borel_expTreeMetricTopology_eq_borel_treeMetricTopology]
  exact cylinder_lt_borel_treeMetricTopology

end Combinatorics.UlamHarris.Tree
