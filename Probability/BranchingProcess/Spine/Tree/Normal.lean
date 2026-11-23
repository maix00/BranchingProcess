/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Spine.Tree.Construction
public import Probability.BranchingProcess.State.Map
public import Probability.BranchingProcess.State.BranchingProperty

/-!
# Complete descendant-tree laws of normal particles

## Public declarations

In `ProbabilityTheory.BranchingProcess.Spine`:

* `treeKernel_normal` proves that the entire tree from a normal root is
  the original `Q`-tree with all present states embedded by `Sum.inl`.
* `treeKernel_normal_map` erases that role and recovers the original law:
  `Law(erase(T) | normal root s) = State.treeKernel Q s`.

* `traj_normalDescendantTrees` proves the conditional product law at distinct
  current normal nodes: `Law((erase(Tⱼ))ⱼ | history) = ⊗ⱼ P^Q_(sⱼ)`.
  The family of roots and current states is arbitrary.

These give the original-law assertion for nonspinal descendant trees used
in Zhan Shi, *Branching Random Walks* (2015), §4.5, proof of Theorem 4.3
immediately before (4.12),
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
They are derived from the general state-kernel factor theorem and the normal
reproduction identity, rather than a separate normal-tree construction.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.Spine

open MeasureTheory Combinatorics.Branching
open scoped ENNReal

variable {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι]
  [Countable ι] [MeasurableSingletonClass ι]

/-- From a normal root, the complete role-valued tree is an embedded original tree. -/
theorem treeKernel_normal (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s) (s : Option S) :
    treeKernel Q hh harmonic (s.map Sum.inl) =
      (State.treeKernel Q s).map (fun t u => (t u).map Sum.inl) := by
  let : IsMarkovKernel (reproductionKernel Q h) :=
    reproductionKernel_isMarkovKernel Q hh harmonic
  exact (State.treeKernel_map Q (reproductionKernel Q h) Sum.inl measurable_inl
    (fun a => (reproductionKernel_normal Q h a).symm) s).symm

/-- Forgetting normal roles gives exactly the original complete subtree law. -/
theorem treeKernel_normal_map (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s) (s : Option S) :
    (treeKernel Q hh harmonic (s.map Sum.inl)).map
      (fun t u => (t u).map (Sum.elim id Subtype.val)) = State.treeKernel Q s := by
  rw [treeKernel_normal Q hh harmonic s]
  have hmap : Measurable (fun t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      fun u => (t u).map (Sum.elim id Subtype.val)) :=
    Step.map_measurable (measurable_id.sumElim measurable_subtype_coe)
  have hinl : Measurable (fun t : List ι → Option S =>
      fun u => (t u).map (Sum.inl : S → S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞})) :=
    Step.map_measurable measurable_inl
  rw [Measure.map_map hmap hinl]
  have he : ((fun t : List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      fun u => (t u).map (Sum.elim id Subtype.val)) ∘
      (fun t : List ι → Option S => fun u => (t u).map Sum.inl)) = id := by
    funext t u
    change ((t u).map Sum.inl).map (Sum.elim id Subtype.val) = t u
    cases t u <;> rfl
  rw [he, Measure.map_id]

/-- Normal descendant trees are conditionally independent original trees at their current states. -/
theorem traj_normalDescendantTrees {Root J : Type*}
    (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ s, h s ≠ 0 → h s ≠ ∞ →
      (∫⁻ ξ, ∑' i, (ξ i).elim 0 h ∂Q s) = h s)
    (a : ℕ)
    (history : Π k : Finset.Iic a,
      (Root × (Fin k.1 → ι)) → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}))
    (roots : J → Root × (Fin a → ι)) (hinj : Function.Injective roots)
    (states : J → Option S)
    (hstates : ∀ j, history ⟨a, by simp⟩ (roots j) = (states j).map Sum.inl) :
    letI := reproductionKernel_isMarkovKernel Q hh harmonic
    ((Kernel.traj
      (X := fun n : ℕ => (Root × (Fin n → ι)) →
        Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}))
      (State.generationHistoryKernel (reproductionKernel Q h)) a history).map
      (fun x j (u : List ι) =>
        (x (a + u.length) ((roots j).1, Fin.append (roots j).2 u.get)).map
          (Sum.elim id Subtype.val))) =
      Measure.infinitePi (fun j => State.treeKernel Q (states j)) := by
  let := reproductionKernel_isMarkovKernel Q hh harmonic
  have hforget : Measurable
      (Sum.elim id (Subtype.val : {s // h s ≠ 0 ∧ h s ≠ ∞} → S)) :=
    measurable_id.sumElim measurable_subtype_coe
  have hmap : Measurable
      (fun trees : J → List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
        fun j u => (trees j u).map (Sum.elim id Subtype.val)) := by
    have hopt := measurable_option_map hforget
    fun_prop
  have ht := congrArg (fun μ => μ.map
    (fun trees : J → List ι → Option (S ⊕ {s // h s ≠ 0 ∧ h s ≠ ∞}) =>
      fun j u => (trees j u).map (Sum.elim id Subtype.val)))
    (State.traj_descendantTrees (reproductionKernel Q h) a history roots hinj)
  rw [Measure.map_map hmap (by fun_prop)] at ht
  calc
    _ = (Measure.infinitePi (fun j =>
        State.treeKernel (reproductionKernel Q h) (history ⟨a, by simp⟩ (roots j)))).map
        (fun trees j u => (trees j u).map (Sum.elim id Subtype.val)) := ht
    _ = Measure.infinitePi (fun j =>
        (State.treeKernel (reproductionKernel Q h) (history ⟨a, by simp⟩ (roots j))).map
          (fun t u => (t u).map (Sum.elim id Subtype.val))) :=
      Measure.infinitePi_map_pi _ (fun _ => Step.map_measurable hforget)
    _ = _ := by
      congr 1
      funext j
      rw [hstates j]
      exact treeKernel_normal_map Q hh harmonic (states j)

end ProbabilityTheory.BranchingProcess.Spine

end
