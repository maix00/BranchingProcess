/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.BranchingProperty
public import Probability.BranchingProcess.State.Observation.Complement

/-!
# A descendant tree given the complete other trees

## Public declarations

In `ProbabilityTheory.BranchingProcess.State`:

* `condExp_descendantTree` proves `E[g(T_u) | F_{ {u} }] = ∫ g dP_(X_u)`
  at every deterministic node `u`, where the singleton line past contains
  complete reproduction observations outside `u`'s descendant subtree.
  The proof represents this information by history through `|u|` and all
  complementary generation subtrees.

The offspring kernel is state-dependent, the initial root states may have any
joint law, and the state and node-index spaces are arbitrary measurable types.
No standard-Borel, moment or countability hypothesis is imposed. The extra
observations include the whole future on all other depth-`a` branches, rather
than just their states at time `a`.

This is the one-node ordinary branching identity, with outside information
represented by the history and complementary generation subtrees. Compare
P. Jagers and A. N. Lagerås, *General branching processes conditioned on
extinction are still branching processes* (2008), §2.3, p. 543,
DOI 10.1214/ECP.v13-1419. The proof invokes the existing full descendant-tree
joint law and the general conditional-coordinate theorem for independent
kernels. It does not construct a parallel state or descendant law.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.State

open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris Finset Preorder

/-- Observing all other depth-`a` descendant trees leaves the selected tree's
conditional law determined just by its inherited state. -/
private lemma condExp_descendantTree_given_other_trees {Root α S E : Type*}
    [MeasurableSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    (a : ℕ) (u : Root × (Fin a → α))
    (g : (List α → Option S) → E) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S =>
      g (fun v : List α => x (a + v.length) (u.1, Fin.append u.2 v.get)))
      (generationPathLaw K initial)) :
    (generationPathLaw K initial)[fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S =>
      g (fun v : List α => x (a + v.length) (u.1, Fin.append u.2 v.get)) |
      MeasurableSpace.comap
        (fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S =>
          (frestrictLe a x, fun q : {q : Root × (Fin a → α) // q ≠ u} =>
            fun v : List α => x (a + v.length) (q.1.1, Fin.append q.1.2 v.get)))
        inferInstance] =ᵐ[generationPathLaw K initial]
      fun x => ∫ tree, g tree ∂treeKernel K (x a u) := by
  exact Kernel.condExp_coordinate_of_jointLaw
    (Ω := Π n : ℕ, (Root × (Fin n → α)) → Option S)
    (A := Π k : Iic a, (Root × (Fin k.1 → α)) → Option S)
    (I := Root × (Fin a → α)) (B := fun _ => List α → Option S)
    (generationPathLaw K initial)
    (frestrictLe a)
    (fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S =>
      fun q (v : List α) => x (a + v.length) (q.1, Fin.append q.2 v.get))
    (measurable_frestrictLe a) (by fun_prop)
    (fun q => (treeKernel K).comap
      (fun history : Π k : Iic a, (Root × (Fin k.1 → α)) → Option S =>
        history ⟨a, by simp⟩ q) (by fun_prop))
    (descendantTrees_jointLaw K initial a id Function.injective_id) u g hg hgi

/-- Ordinary branching at a deterministic node, with its full outside-descendant
information and arbitrary jointly distributed initial root states.

The deterministic-line identity is stated by P. Jagers and A. N. Lagerås,
*General branching processes conditioned on extinction are still branching processes*
(2008), §2.3, p. 543, DOI 10.1214/ECP.v13-1419. -/
theorem condExp_descendantTree {Root α S E : Type*}
    [MeasurableSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (K : Kernel S (Step α S)) [IsMarkovKernel K]
    (initial : Measure (Root → Option S)) [IsProbabilityMeasure initial]
    (u : RootIndexed.TreeNode Root α)
    (g : (List α → Option S) → E) (hg : StronglyMeasurable g)
    (hgi : Integrable (fun x => g (descendantTree u x)) (generationPathLaw K initial)) :
    (generationPathLaw K initial)[fun x => g (descendantTree u x) |
      Tree.linePast (MeasurableSpace.comap
        (rootStates (Root := Root) (α := α) (S := S)) inferInstance)
        (fun v => MeasurableSpace.comap (offspringStates (S := S) v) inferInstance) {u}]
      =ᵐ[generationPathLaw K initial] fun x => ∫ tree, g tree ∂treeKernel K (stateAt u x) := by
  rcases u with ⟨r, v⟩
  have hread (x : Π n : ℕ, (Root × (Fin n → α)) → Option S) :
      descendantTree (r, v) x = fun w : List α =>
        x (v.length + w.length) (r, Fin.append v.get w.get) := by
    funext w
    simpa only [List.ofFn_get] using descendantTree_ofFn x v.length (r, v.get) w
  have hi := linePast_singleton_eq_comap_complementObservation (S := S) v.length (r, v.get)
  simp only [List.ofFn_get] at hi
  rw [hi]
  have hc := condExp_descendantTree_given_other_trees K initial v.length (r, v.get) g hg
    (by simpa only [hread] using hgi)
  have ho : complementObservation (S := S) v.length (r, v.get) =
      (fun x : Π n : ℕ, (Root × (Fin n → α)) → Option S =>
        (frestrictLe v.length x, fun q : {q : Root × (Fin v.length → α) // q ≠ (r, v.get)} =>
          fun w : List α => x (v.length + w.length) (q.1.1, Fin.append q.1.2 w.get))) := by
    funext x
    apply Prod.ext
    · rfl
    · funext q w
      exact descendantTree_ofFn x v.length q.1 w
  rw [ho]
  simpa only [hread, stateAt] using hc

end ProbabilityTheory.BranchingProcess.State

end
