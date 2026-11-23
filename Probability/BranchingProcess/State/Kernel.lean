/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.State.Generation
public import Probability.Kernel.IonescuTulcea.Uniqueness
public import Mathlib.Data.List.OfFn

/-!
# Single-root process and state-tree kernels

## Public declarations

In namespace `ProbabilityTheory.BranchingProcess.State`:

* `pathKernel K s` is the complete generation-path law started at optional
  root state $s$, with arbitrary state-dependent offspring law $K(x)$.
* `pathKernel.isMarkovKernel` proves these are probability laws.
* `pathKernel_initial` gives its deterministic initial generation.
* `pathKernel_oneStep` gives its past/next conditional generation law.
* `pathKernel_eq_generationPathLaw` identifies this law with the process
  generated from a Dirac initial root-state distribution.
* `treeKernel` records the state at each node $u$ by reading generation
  $|u|$ at the address $u$. Absent nodes have value `none`.
* `treeKernel.isMarkovKernel` proves it is a probability kernel.
* `treeKernel_root` gives root-state marginal $\delta_s$.
* `treeKernel_children` gives the complete root-family marginal
  `Law((t([j]))_j) = K_⊥(s)`.

The underlying construction is Mathlib's Ionescu--Tulcea kernel; its
existence is not assumed. Inputting `offspringStateKernel F hF Q` gives the
process driven by the original mark-valued branching kernel $Q$ and update $F$.
-/

@[expose] public section

open MeasureTheory Combinatorics.Branching Finset Preorder

namespace ProbabilityTheory.BranchingProcess.State

/-- Full single-root generation law, including the possibility of an absent root. -/
noncomputable def pathKernel {α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] :
    Kernel (Option S) (Π n : ℕ, (Unit × (Fin n → α)) → Option S) :=
  (Kernel.traj (X := fun n : ℕ ↦ (Unit × (Fin n → α)) → Option S)
    (generationHistoryKernel (Root := Unit) K) 0).comap
    (fun s (_k : Iic 0) _p ↦ s) (by fun_prop)

instance pathKernel.isMarkovKernel {α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] : IsMarkovKernel (pathKernel K) := by
  unfold pathKernel
  infer_instance

/-- The initial generation contains just the supplied optional root state. -/
theorem pathKernel_initial {α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (s : Option S) :
    (pathKernel K s).map (fun x ↦ x 0) =
      Measure.dirac (fun _ : Unit × (Fin 0 → α) ↦ s) := by
  have he : (fun x : Π n : ℕ, (Unit × (Fin n → α)) → Option S ↦ x 0) =
      (fun h : Π k : Iic 0, (Unit × (Fin k.1 → α)) → Option S ↦ h ⟨0, by simp⟩) ∘
        frestrictLe 0 := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop)]
  change ((Kernel.traj (X := fun n : ℕ ↦ (Unit × (Fin n → α)) → Option S)
    (generationHistoryKernel (Root := Unit) K) 0
    (fun (_k : Iic 0) (_p : Unit × (Fin _k.1 → α)) ↦ s)).map (frestrictLe 0)).map _ = _
  rw [Kernel.traj_map_frestrictLe_apply, Kernel.partialTraj_self, Kernel.id_apply,
    Measure.map_dirac' (by fun_prop)]

/-- Every next generation has precisely the stated state-dependent joint law. -/
theorem pathKernel_oneStep {α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (s : Option S) (n : ℕ) :
    (pathKernel K s).map (frestrictLe n) ⊗ₘ generationHistoryKernel K n =
      (pathKernel K s).map (fun x ↦ (frestrictLe n x, x (n + 1))) := by
  change (Kernel.traj (X := fun n : ℕ ↦ (Unit × (Fin n → α)) → Option S)
    (generationHistoryKernel (Root := Unit) K) 0
    (fun (_k : Iic 0) (_p : Unit × (Fin _k.1 → α)) ↦ s)).map _ ⊗ₘ _ = _
  rw [Kernel.traj_map_frestrictLe_apply]
  exact Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le n)

/-- The root-state kernel and the joint-initial-law construction agree. -/
theorem pathKernel_eq_generationPathLaw {α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (s : Option S) :
    pathKernel K s = generationPathLaw K (Measure.dirac (fun _ : Unit ↦ s)) := by
  rw [generationPathLaw, Measure.map_dirac' (by fun_prop)]
  apply Kernel.eq_trajMeasure
  · exact pathKernel_initial K s
  · exact pathKernel_oneStep K s

/-- The complete realized state tree of a single-root state-dependent process. -/
noncomputable def treeKernel {α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] :
    Kernel (Option S) (List α → Option S) :=
  (pathKernel K).map (fun x u ↦ x u.length ((), u.get))

instance treeKernel.isMarkovKernel {α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] : IsMarkovKernel (treeKernel K) := by
  unfold treeKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The root of the realized tree has exactly the prescribed initial state. -/
theorem treeKernel_root {α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (s : Option S) :
    (treeKernel K s).map (fun t ↦ t []) = Measure.dirac s := by
  rw [treeKernel, Kernel.map_apply _ (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : Π n : ℕ, (Unit × (Fin n → α)) → Option S ↦ x 0 ((), [].get)) =
      (fun y : (Unit × (Fin 0 → α)) → Option S ↦ y ((), [].get)) ∘ (fun x ↦ x 0) := rfl
  change (pathKernel K s).map (fun x ↦ x 0 ((), [].get)) = _
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), pathKernel_initial,
    Measure.map_dirac' (by fun_prop)]

/-- The root's complete child family has the original optional offspring law. -/
theorem treeKernel_children {α S : Type*} [MeasurableSpace S]
    (K : Kernel S (Step α S)) [IsMarkovKernel K] (s : Option S) :
    (treeKernel K s).map (fun t j => t [j]) =
      (Kernel.optionElim (Measure.dirac (fun _ : α => (none : Option S))) K) s := by
  have hfirst : (pathKernel K s).map (fun x => x 1) =
      generationKernel (Root := Unit) K 0 (fun _ => s) := by
    have hm := congrArg (fun L => L (fun (_k : Iic 0)
      (_p : Unit × (Fin _k.1 → α)) => s))
      (Kernel.map_traj_succ_self
        (X := fun n : ℕ => (Unit × (Fin n → α)) → Option S)
        (κ := generationHistoryKernel (Root := Unit) K) (a := 0))
    rw [Kernel.map_apply _ (by fun_prop)] at hm
    exact hm
  rw [treeKernel, Kernel.map_apply _ (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun x : Π n : ℕ, (Unit × (Fin n → α)) → Option S =>
      fun j => x [j].length ((), [j].get)) =
      (fun x => fun j => x 1 ((), Fin.snoc (fun i : Fin 0 => i.elim0) j)) := by
    funext x j
    congr 2
    funext i
    simp only [List.get_eq_getElem, List.getElem_singleton]
    have hi : i = Fin.last 0 := by
      apply Fin.ext
      have hb := i.isLt
      simp only [List.length_singleton] at hb
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hb)
    rw [hi, Fin.snoc_last]
  change (pathKernel K s).map (fun x => fun j => x [j].length ((), [j].get)) = _
  rw [he]
  change (pathKernel K s).map
    ((fun next : (Unit × (Fin 1 → α)) → Option S =>
      fun j => next ((), Fin.snoc (fun i : Fin 0 => i.elim0) j)) ∘ (fun x => x 1)) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), hfirst]
  exact generationKernel_childFamily K 0 (fun _ => s) ((), fun i : Fin 0 => i.elim0)

end ProbabilityTheory.BranchingProcess.State
