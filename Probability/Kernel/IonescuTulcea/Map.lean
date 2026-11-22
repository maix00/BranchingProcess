/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.IonescuTulcea.Uniqueness
public import Probability.Kernel.Composition.Map

/-!
# Observations of Ionescu--Tulcea trajectories

## Public declarations

* `ProbabilityTheory.Kernel.map_traj_eq_trajMeasure`: let $P$ be the trajectory
  law after an observed history through time $a$. If measurable observations
  $f_n(X_{a+n})$ send each conditional next-step law to a kernel depending
  only on their observed history, then their complete path law is the
  Ionescu--Tulcea law of those kernels. The initial observation is deterministic.

This complements Mathlib's finite-history projection identities: it identifies
an entire observed process from its one-step kernel identities. It uses native
Ionescu--Tulcea construction and projective-limit uniqueness, with arbitrary
measurable coordinate spaces.
-/

@[expose] public section

open MeasureTheory Finset Preorder

namespace ProbabilityTheory.Kernel

/-- A measurable observation with closed conditional transition laws has the
corresponding complete trajectory law, starting at any deterministic time. -/
theorem map_traj_eq_trajMeasure
    {X Y : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    (κ : (n : ℕ) → Kernel (Π k : Iic n, X k) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)]
    (η : (n : ℕ) → Kernel (Π k : Iic n, Y k) (Y (n + 1)))
    [∀ n, IsMarkovKernel (η n)]
    (a : ℕ) (x₀ : Π k : Iic a, X k)
    (f : (n : ℕ) → X (a + n) → Y n) (hf : ∀ n, Measurable (f n))
    (hstep : ∀ n (h : Π k : Iic (a + n), X k),
      (κ (a + n) h).map (f (n + 1)) =
        η n (fun k ↦ f k.1 (h ⟨a + k.1,
          mem_Iic.mpr (Nat.add_le_add_left (mem_Iic.mp k.2) a)⟩))) :
    (traj κ a x₀).map (fun x n ↦ f n (x (a + n))) =
      trajMeasure (Measure.dirac (f 0 (x₀ ⟨a, by simp⟩))) η := by
  let P := traj κ a x₀
  let obs (x : Π n, X n) (n : ℕ) := f n (x (a + n))
  have hobs : Measurable obs := measurable_pi_iff.mpr fun n ↦
    (hf n).comp (measurable_pi_apply (a + n))
  apply eq_trajMeasure
  · rw [Measure.map_map (measurable_pi_apply 0) hobs]
    have he : (fun x : Π n, X n ↦ f 0 (x (a + 0))) =
        (fun h : Π k : Iic a, X k ↦ f 0 (h ⟨a, by simp⟩)) ∘ frestrictLe a := rfl
    change (traj κ a x₀).map (fun x ↦ f 0 (x (a + 0))) = _
    rw [he, ← Measure.map_map (by fun_prop) (measurable_frestrictLe a)]
    rw [traj_map_frestrictLe_apply, partialTraj_self, id_apply,
      Measure.map_dirac' (by fun_prop)]
  · intro n
    let past (h : Π k : Iic (a + n), X k) (k : Iic n) :=
      f k.1 (h ⟨a + k.1, by exact mem_Iic.mpr (Nat.add_le_add_left (mem_Iic.mp k.2) a)⟩)
    have hpast : Measurable past := measurable_pi_iff.mpr fun k ↦
      (hf k.1).comp (measurable_pi_apply _)
    have hjoint := Measure.map_compProd_eq_of_ae
      (P.map (frestrictLe (a + n))) past hpast (f (n + 1)) (hf (n + 1))
      (κ (a + n)) (η n) (Filter.Eventually.of_forall fun h ↦ by
        rw [map_apply _ (hf (n + 1))]
        simpa only [comap_apply, past] using hstep n h)
    have hone : P.map (frestrictLe (a + n)) ⊗ₘ κ (a + n) =
        P.map (fun x ↦ (frestrictLe (a + n) x, x (a + n + 1))) := by
      dsimp only [P]
      rw [traj_map_frestrictLe_apply]
      exact partialTraj_compProd_eq_map_traj (Nat.le_add_right a n)
    rw [hone] at hjoint
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map hpast (measurable_frestrictLe (a + n))] at hjoint
    rw [Measure.map_map (measurable_frestrictLe n) hobs,
      Measure.map_map (by fun_prop) hobs]
    exact hjoint.symm

end ProbabilityTheory.Kernel
