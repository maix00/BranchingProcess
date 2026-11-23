/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.BranchingProperty

/-!
# Offspring families and complete child subtrees

## Public declarations

In `ProbabilityTheory.BranchingProcess.State`:

* `treeKernel_children_subtrees` identifies the joint law of the root's
  offspring family and all its complete child subtrees:
  `Law(ξ,(Tⱼ)ⱼ) = K_⊥(s,dξ) ⊗ (⊗ⱼ P_(ξⱼ))`.
  This includes absent children, whose tree law is started at `none`.

The state and slot spaces are arbitrary; no moment or standard-Borel
hypothesis is imposed. This is a joint-measure form of the branching
Markov property, derived from the existing canonical state process and its
history/descendant disintegration. It supplies the first recursive split
used in Zhan Shi, *Branching Random Walks* (2015), §4.5, proof of Theorem 4.3
between (4.12) and (4.13),
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching Finset Preorder

namespace ProbabilityTheory.BranchingProcess.State

/-- Given the original offspring family, child trees are independent canonical continuations. -/
theorem treeKernel_children_subtrees {α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (s : Option S) :
    (treeKernel K s).map (fun t : List α → Option S =>
      ((fun j => t [j]), fun j (u : List α) => t (j :: u))) =
      (Kernel.optionElim (Measure.dirac (fun _ : α => (none : Option S))) K) s ⊗ₘ
        Kernel.infinitePi (fun j => (treeKernel K).comap
          (fun ξ : Step α S => ξ j) (measurable_pi_apply j)) := by
  let P := pathKernel K s
  let C (history : Π k : Iic 1, (Unit × (Fin k.1 → α)) → Option S) : Step α S :=
    fun j => history ⟨1, by simp⟩ ((), fun _ => j)
  let D (x : Π n : ℕ, (Unit × (Fin n → α)) → Option S) j (u : List α) :=
    x (1 + u.length) ((), Fin.append (fun _ : Fin 1 => j) u.get)
  let R := Kernel.infinitePi (fun j => (treeKernel K).comap
    (fun history : Π k : Iic 1, (Unit × (Fin k.1 → α)) → Option S =>
      history ⟨1, by simp⟩ ((), fun _ => j)) (by fun_prop))
  let F := Kernel.infinitePi (fun j => (treeKernel K).comap
    (fun ξ : Step α S => ξ j) (measurable_pi_apply j))
  let read (x : Π n : ℕ, (Unit × (Fin n → α)) → Option S) (u : List α) :=
    x u.length ((), u.get)
  have hC : Measurable C := by fun_prop
  have hD : Measurable D := by fun_prop
  have hread : Measurable read := by fun_prop
  have htuple (x : Π n : ℕ, (Unit × (Fin n → α)) → Option S)
      (n : ℕ) (f : Fin n → α) : read x (List.ofFn f) = x n ((), f) :=
    congrArg (fun q : Sigma (fun n => Fin n → α) => x q.1 ((), q.2))
      (List.equivSigmaTuple.apply_symm_apply ⟨n, f⟩)
  have hchild (x : Π n : ℕ, (Unit × (Fin n → α)) → Option S) (j : α) :
      read x [j] = C (frestrictLe 1 x) j := by
    change read x [j] = x 1 ((), fun _ => j)
    have hj := htuple x 1 (fun _ => j)
    simpa only [List.ofFn_const, List.replicate_one] using hj
  have hsub (x : Π n : ℕ, (Unit × (Fin n → α)) → Option S) (j : α) (u : List α) :
      read x (j :: u) = D x j u := by
    have hu := htuple x (1 + u.length) (Fin.append (fun _ : Fin 1 => j) u.get)
    simpa only [List.ofFn_fin_append, List.ofFn_const, List.replicate_one,
      List.ofFn_get, List.singleton_append] using hu
  have hfirst : (P.map (frestrictLe 1)).map C =
      (Kernel.optionElim (Measure.dirac (fun _ : α => (none : Option S))) K) s := by
    rw [Measure.map_map hC (by fun_prop)]
    have hc : (C ∘ frestrictLe 1) =
        (fun t : List α → Option S => fun j => t [j]) ∘ read := by
      funext x j
      exact (hchild x j).symm
    rw [hc, ← Measure.map_map (by fun_prop) hread]
    have ht := treeKernel_children K s
    rw [treeKernel, Kernel.map_apply _ hread] at ht
    exact ht
  have hinj : Function.Injective (fun j : α => ((), fun _ : Fin 1 => j)) := by
    intro i j hij
    exact congrArg (fun p : Unit × (Fin 1 → α) => p.2 0) hij
  have hj := descendantTrees_jointLaw K (Measure.dirac (fun _ : Unit => s)) 1
    (fun j : α => ((), fun _ : Fin 1 => j)) hinj
  rw [← pathKernel_eq_generationPathLaw] at hj
  change P.map (fun x => (frestrictLe 1 x, D x)) = (P.map (frestrictLe 1)) ⊗ₘ R at hj
  have hm := Measure.map_compProd_eq_of_ae (P.map (frestrictLe 1)) C hC id measurable_id R F
    (Filter.Eventually.of_forall fun history => by rw [Kernel.map_id]; rfl)
  rw [← hj, Measure.map_map (by fun_prop) (by fun_prop), hfirst] at hm
  have hproj : (fun x => (C (frestrictLe 1 x), D x)) =
      (fun t : List α → Option S => ((fun j => t [j]), fun j (u : List α) => t (j :: u))) ∘
        read := by
    funext x
    apply Prod.ext
    · funext j
      exact (hchild x j).symm
    · funext j u
      exact (hsub x j u).symm
  have htree : treeKernel K s = P.map read := Kernel.map_apply (pathKernel K) hread s
  rw [htree, Measure.map_map (by fun_prop) hread]
  change P.map
    ((fun t : List α → Option S => ((fun j => t [j]), fun j (u : List α) => t (j :: u))) ∘
      read) = _
  rw [← hproj]
  exact hm

end ProbabilityTheory.BranchingProcess.State

end
