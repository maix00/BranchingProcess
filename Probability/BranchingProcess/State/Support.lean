/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Kernel
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Local reproduction constraints on the realized state tree

## Public declarations

In `ProbabilityTheory.BranchingProcess.State`:

* `ae_pathKernel_reproduction` states that a jointly measurable relation `R`
  between an optional parent state and its child family, holding almost surely
  under every optional offspring law, holds simultaneously at all generations
  and parent addresses of the canonical path process.
* `ae_treeKernel_reproduction` gives the realized-tree form:
  `∀ u, R (t u) (j ↦ t (u ++ [j]))` almost surely.

The slot type is countable; state spaces are arbitrary measurable spaces.
These support statements use the existing one-step joint law and product
marginals, without introducing another path or tree measure. They implement
the passage from the normal/special reproduction rules to the whole system in
Zhan Shi, *Branching Random Walks* (2015), Chapter 4, §4.4 after (4.8),
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf),
for any measurable reproduction constraint, rather than only the spinal rule.
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching Finset Preorder

namespace ProbabilityTheory.BranchingProcess.State

/-- A local offspring constraint holds simultaneously along the canonical process. -/
theorem ae_pathKernel_reproduction {α S : Type*} [Countable α] [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (s : Option S)
    (R : Option S → Step α S → Prop)
    (hR : MeasurableSet {p : Option S × Step α S | R p.1 p.2})
    (hstep : ∀ s, ∀ᵐ ξ ∂(Kernel.optionElim
      (Measure.dirac (fun _ : α => (none : Option S))) K) s, R s ξ) :
    ∀ᵐ x ∂pathKernel K s, ∀ n (p : Unit × (Fin n → α)),
      R (x n p) (fun j => x (n + 1) (p.1, Fin.snoc p.2 j)) := by
  simp only [ae_all_iff]
  intro n p
  let A := {y : (Π k : Iic n, (Unit × (Fin k.1 → α)) → Option S) ×
      ((Unit × (Fin (n + 1) → α)) → Option S) |
      R (y.1 ⟨n, by simp⟩ p) (fun j => y.2 (p.1, Fin.snoc p.2 j))}
  have hA : MeasurableSet A := hR.preimage
    (show Measurable (fun y : (Π k : Iic n, (Unit × (Fin k.1 → α)) → Option S) ×
      ((Unit × (Fin (n + 1) → α)) → Option S) =>
      (y.1 ⟨n, by simp⟩ p, fun j => y.2 (p.1, Fin.snoc p.2 j))) from by fun_prop)
  have hlocal : ∀ history : Π k : Iic n, (Unit × (Fin k.1 → α)) → Option S,
      ∀ᵐ next ∂generationHistoryKernel K n history, (history, next) ∈ A := by
    intro history
    have hm := generationKernel_childFamily K n (history ⟨n, by simp⟩) p
    have hh := hstep (history ⟨n, by simp⟩ p)
    rw [← hm] at hh
    change ∀ᵐ next ∂generationKernel K n (history ⟨n, by simp⟩),
      R (history ⟨n, by simp⟩ p) (fun j => next (p.1, Fin.snoc p.2 j))
    exact ae_of_ae_map
      (show Measurable (fun next : (Unit × (Fin (n + 1) → α)) → Option S =>
        fun j => next (p.1, Fin.snoc p.2 j)) from by fun_prop).aemeasurable hh
  have hprod : ∀ᵐ y ∂(pathKernel K s).map (frestrictLe n) ⊗ₘ
      generationHistoryKernel K n, y ∈ A :=
    Measure.ae_compProd_of_ae_ae hA (Filter.Eventually.of_forall hlocal)
  rw [pathKernel_oneStep] at hprod
  exact ae_of_ae_map (by fun_prop) hprod

/-- Every node of the canonical realized tree satisfies the local offspring constraint. -/
theorem ae_treeKernel_reproduction {α S : Type*} [Countable α] [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (s : Option S)
    (R : Option S → Step α S → Prop)
    (hR : MeasurableSet {p : Option S × Step α S | R p.1 p.2})
    (hstep : ∀ s, ∀ᵐ ξ ∂(Kernel.optionElim
      (Measure.dirac (fun _ : α => (none : Option S))) K) s, R s ξ) :
    ∀ᵐ t ∂treeKernel K s, ∀ u, R (t u) (fun j => t (u ++ [j])) := by
  rw [treeKernel, Kernel.map_apply _ (by fun_prop)]
  have hset : MeasurableSet {t : List α → Option S |
      ∀ u, R (t u) (fun j => t (u ++ [j]))} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun u => hR.preimage
      (show Measurable (fun t : List α → Option S =>
        (t u, fun j => t (u ++ [j]))) from by fun_prop)
  apply (ae_map_iff
    (show Measurable (fun x : Π n : ℕ, (Unit × (Fin n → α)) → Option S =>
      fun u : List α => x u.length ((), u.get)) from by fun_prop).aemeasurable hset).mpr
  filter_upwards [ae_pathKernel_reproduction K s R hR hstep] with x hx u
  have hu := hx u.length ((), u.get)
  have hread : ∀ (n : ℕ) (f : Fin n → α),
      x (List.ofFn f).length ((), (List.ofFn f).get) = x n ((), f) := by
    intro n f
    have heq : (⟨(List.ofFn f).length, (List.ofFn f).get⟩ : Sigma (fun n => Fin n → α)) =
        ⟨n, f⟩ := by
      apply Sigma.ext (List.length_ofFn (f := f))
      apply (Fin.heq_fun_iff (List.length_ofFn (f := f))).mpr
      intro i
      exact List.get_ofFn f i
    exact congrArg (fun v : Sigma (fun n => Fin n → α) => x v.1 ((), v.2)) heq
  have he : ∀ j, u ++ [j] = List.ofFn (Fin.snoc u.get j) := by
    intro j
    symm
    simpa only [List.concat_eq_append, Fin.snoc_castSucc, Fin.snoc_last,
      List.ofFn_get] using List.ofFn_succ' (Fin.snoc u.get j)
  convert hu using 1
  funext j
  rw [he, hread]

end ProbabilityTheory.BranchingProcess.State

end
