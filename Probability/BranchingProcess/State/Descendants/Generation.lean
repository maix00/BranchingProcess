/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Generation
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Restricting state-dependent generation laws to descendant families

## Public declarations

* `ProbabilityTheory.BranchingProcess.State.generationKernel_descendants`:
  choose distinct root-address pairs $(r_i,u_i)$ at depth $a$. Restricting a
  next-generation population to the descendants of these roots gives the
  independent product of their one-generation laws:
  $K_{a+h}(s)\circ\mathrm{rebase}^{-1}
   =\bigotimes_i K_h(s(r_i,u_i\mathbin{++}\cdot))$.
  Absent roots are allowed; their descendant population stays empty.

The proof groups the independent parent kernels by the disjoint descendant
address sets. This is the one-generation step in the finite-depth proof of
branching for state-dependent reproduction. It uses no order, addition,
standard-Borel, or offspring-moment assumption.
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching

namespace ProbabilityTheory.BranchingProcess.State

private lemma appendRoots_injective {Root ι α : Type*} {a h : ℕ}
    (roots : ι → Root × (Fin a → α)) (hinj : Function.Injective roots) :
    Function.Injective (fun q : ι × (Unit × (Fin h → α)) ↦
      ((roots q.1).1, Fin.append (roots q.1).2 q.2.2)) := by
  rintro ⟨i, ⟨x, u⟩⟩ ⟨j, ⟨y, v⟩⟩ he
  cases x
  cases y
  have hroot : roots i = roots j := by
    apply Prod.ext
    · exact congrArg (fun p : Root × (Fin (a + h) → α) ↦ p.1) he
    · funext k
      simpa only [Fin.append_left] using
        congrArg (fun p : Root × (Fin (a + h) → α) ↦ p.2 (Fin.castAdd h k)) he
  have hij := hinj hroot
  subst j
  have huv : u = v := by
    funext k
    simpa only [Fin.append_right] using
      congrArg (fun p : Root × (Fin (a + h) → α) ↦ p.2 (Fin.natAdd a k)) he
  subst v
  rfl

/-- Distinct descendant populations have the product of their corresponding
state-dependent one-generation continuation laws. -/
theorem generationKernel_descendants {Root ι α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (a h : ℕ)
    (roots : ι → Root × (Fin a → α)) (hinj : Function.Injective roots)
    (s : (Root × (Fin (a + h) → α)) → Option S) :
    (generationKernel K (a + h) s).map
        (fun next i (p : Unit × (Fin (h + 1) → α)) ↦
          next ((roots i).1, Fin.append (m := a) (n := h + 1) (roots i).2 p.2)) =
      Measure.infinitePi (fun i ↦ generationKernel K h
        (fun p : Unit × (Fin h → α) ↦ s ((roots i).1, Fin.append (roots i).2 p.2))) := by
  let μ (p : Root × (Fin (a + h) → α)) :=
    (Kernel.optionElim (Measure.dirac (fun _ : α ↦ (none : Option S))) K) (s p)
  let index (q : ι × (Unit × (Fin h → α))) :=
    ((roots q.1).1, Fin.append (roots q.1).2 q.2.2)
  have hindex : Function.Injective index := appendRoots_injective roots hinj
  have hraw := Measure.map_infinitePi_infinitePi_of_inj (P := μ) (f := index) hindex
  have hcur : (Measure.infinitePi μ).map (fun broods i p ↦ broods (index (i, p))) =
      Measure.infinitePi (fun i ↦ Measure.infinitePi (fun p ↦ μ (index (i, p)))) := by
    rw [← Measure.infinitePi_map_curry, ← hraw,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [generationKernel_apply]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simp_rw [generationKernel_apply]
  rw [← Measure.infinitePi_map_pi _ (fun _ ↦ by fun_prop)]
  change Measure.map _ (Measure.infinitePi μ) =
    Measure.map _ (Measure.infinitePi (fun i ↦ Measure.infinitePi (fun p ↦ μ (index (i, p)))))
  rw [← hcur, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext broods i p
  have hx := congrArg (Fin.append (m := a) (n := h + 1) (roots i).2) (Fin.snoc_init_self p.2)
  rw [Fin.append_snoc] at hx
  have hinit := congrArg Fin.init hx
  have hlast := congrArg (fun w : Fin (a + (h + 1)) → α ↦ w (Fin.last (a + h))) hx
  simp only [Fin.init_snoc] at hinit
  change broods ((roots i).1, Fin.init (Fin.append (m := a) (n := h + 1) (roots i).2 p.2))
    (Fin.append (m := a) (n := h + 1) (roots i).2 p.2 (Fin.last (a + h))) = _
  rw [← hinit, ← hlast]
  change broods ((roots i).1, Fin.append (roots i).2 (Fin.init p.2))
    ((Fin.snoc (Fin.append (roots i).2 (Fin.init p.2)) (p.2 (Fin.last h)) :
      Fin ((a + h) + 1) → α) (Fin.last (a + h))) = _
  simp only [Fin.snoc_last, Function.comp_apply, index]

end ProbabilityTheory.BranchingProcess.State
