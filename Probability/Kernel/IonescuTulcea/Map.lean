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

* `ProbabilityTheory.Kernel.map_eq_trajMeasure` transports any probability
  law whose successive joint laws at nondecreasing times `tₙ` are prescribed by `κ`:
  `P.map (x ↦ (fₙ(xₜₙ))ₙ) = Law_η((P.map evₜ₀).map f₀)` whenever the
  measurable observations intertwine the next-step kernels almost everywhere
  under the actual past law.
* `ProbabilityTheory.Kernel.map_trajMeasure` specializes this to the native
  process with an arbitrary initial law `μ`, giving `Law_η(μ.map f₀)`.
* `ProbabilityTheory.Kernel.map_traj_eq_trajMeasure`: let $P$ be the trajectory
  law after an observed history through time $a$. If measurable observations
  $f_n(X_{a+n})$ send each conditional next-step law to a kernel depending
  only on their observed history, then their complete path law is the
  Ionescu--Tulcea law of those kernels. The initial observation is deterministic.

This complements Mathlib's finite-history projection identities: it identifies
an entire observed process from its one-step kernel identities. It uses native
Ionescu--Tulcea construction and projective-limit uniqueness, with arbitrary
measurable coordinate spaces. The uniqueness statement is the native
Ionescu--Tulcea uniqueness theorem, as in O. Kallenberg, *Foundations of
Modern Probability*, Theorem 8.24, third edition (2021),
DOI 10.1007/978-3-030-61871-1.
-/

@[expose] public section

open MeasureTheory Finset Preorder

namespace ProbabilityTheory.Kernel

/-- An observed process is determined by its observed initial law and closed transition laws. -/
theorem map_eq_trajMeasure
    {X Y : ℕ → Type*} [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    (t : ℕ → ℕ) (ht : Monotone t)
    (κ : (n : ℕ) → Kernel (Π k : Iic (t n), X k) (X (t (n + 1))))
    [∀ n, IsSFiniteKernel (κ n)]
    (η : (n : ℕ) → Kernel (Π k : Iic n, Y k) (Y (n + 1)))
    [∀ n, IsMarkovKernel (η n)]
    (P : Measure (Π n, X n)) [IsProbabilityMeasure P]
    (f : (n : ℕ) → X (t n) → Y n) (hf : ∀ n, Measurable (f n))
    (hstep : ∀ n, ∀ᵐ h ∂P.map (frestrictLe (t n)),
      (κ n h).map (f (n + 1)) =
        η n (fun k ↦ f k.1 (h ⟨t k.1, mem_Iic.mpr (ht (mem_Iic.mp k.2))⟩)))
    (hone : ∀ n, P.map (frestrictLe (t n)) ⊗ₘ κ n =
      P.map (fun x ↦ (frestrictLe (t n) x, x (t (n + 1))))) :
    P.map (fun x n ↦ f n (x (t n))) =
      trajMeasure ((P.map (fun x => x (t 0))).map (f 0)) η := by
  let obs (x : Π n, X n) (n : ℕ) := f n (x (t n))
  have hobs : Measurable obs := measurable_pi_iff.mpr fun n ↦
    (hf n).comp (measurable_pi_apply (t n))
  apply eq_trajMeasure
  · rw [Measure.map_map (measurable_pi_apply 0) hobs,
      Measure.map_map (hf 0) (measurable_pi_apply (t 0))]
    rfl
  · intro n
    let past (h : Π k : Iic (t n), X k) (k : Iic n) :=
      f k.1 (h ⟨t k.1, mem_Iic.mpr (ht (mem_Iic.mp k.2))⟩)
    have hpast : Measurable past := measurable_pi_iff.mpr fun k ↦
      (hf k.1).comp (measurable_pi_apply _)
    have hjoint := Measure.map_compProd_eq_of_ae
      (P.map (frestrictLe (t n))) past hpast (f (n + 1)) (hf (n + 1))
      (κ n) (η n) (by
        filter_upwards [hstep n] with h hh
        rw [map_apply _ (hf (n + 1))]
        simpa only [comap_apply, past] using hh)
    rw [hone n] at hjoint
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map hpast (measurable_frestrictLe (t n))] at hjoint
    rw [Measure.map_map (measurable_frestrictLe n) hobs,
      Measure.map_map (by fun_prop) hobs]
    exact hjoint.symm

/-- State factors transport the native path law with a joint random initial distribution. -/
theorem map_trajMeasure {X Y : ℕ → Type*}
    [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
    (κ : (n : ℕ) → Kernel (Π k : Iic n, X k.1) (X (n + 1)))
    (η : (n : ℕ) → Kernel (Π k : Iic n, Y k.1) (Y (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] [∀ n, IsMarkovKernel (η n)]
    (f : (n : ℕ) → X n → Y n) (hf : ∀ n, Measurable (f n))
    (hstep : ∀ n history, (κ n history).map (f (n + 1)) =
      η n (fun k => f k.1 (history k)))
    (μ : Measure (X 0)) [IsProbabilityMeasure μ] :
    (trajMeasure μ κ).map (fun x n => f n (x n)) = trajMeasure (μ.map (f 0)) η := by
  have hg := map_eq_trajMeasure id monotone_id κ η (trajMeasure μ κ) f hf
    (fun n => Filter.Eventually.of_forall (hstep n))
    (fun _ => map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure)
  change (trajMeasure μ κ).map (fun x n => f n (x n)) =
    trajMeasure (((trajMeasure μ κ).map (fun x => x 0)).map (f 0)) η at hg
  rwa [trajMeasure_initial] at hg

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
  rw [map_eq_trajMeasure (fun n => a + n) (fun _ _ h => Nat.add_le_add_left h a)
    (fun n => κ (a + n)) η (traj κ a x₀) f hf
    (fun n => Filter.Eventually.of_forall (hstep n)) (fun n => by
    rw [traj_map_frestrictLe_apply]
    exact partialTraj_compProd_eq_map_traj (Nat.le_add_right a n))]
  have hinit : (traj κ a x₀).map (fun x => x a) = Measure.dirac (x₀ ⟨a, by simp⟩) := by
    have he : (fun x : Π n, X n => x a) =
        (fun h : Π k : Iic a, X k => h ⟨a, by simp⟩) ∘ frestrictLe a := rfl
    rw [he, ← Measure.map_map (by fun_prop) (measurable_frestrictLe a),
      traj_map_frestrictLe_apply, partialTraj_self, id_apply,
      Measure.map_dirac' (by fun_prop)]
  change trajMeasure (((traj κ a x₀).map (fun x => x a)).map (f 0)) η = _
  rw [hinit, Measure.map_dirac' (hf 0)]

end ProbabilityTheory.Kernel
