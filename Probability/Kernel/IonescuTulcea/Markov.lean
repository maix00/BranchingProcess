/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Probability.Kernel.Composition.Pow

/-!
# Homogeneous kernels in the Ionescu--Tulcea construction

## Public declarations

* `ProbabilityTheory.Kernel.historyKernel K n` sends a history through `n`
  to `K(xₙ, ·)`; it uses the native input comap.
* `ProbabilityTheory.Kernel.historyKernel_isSFiniteKernel` and
  `ProbabilityTheory.Kernel.historyKernel_isMarkovKernel` inherit the
  corresponding property of `K`.
* `ProbabilityTheory.Kernel.lintegral_partialTraj_historyKernel`:
  for `a ≤ b`, the endpoint integral of the native finite-history kernel is
  `∫ f(x_b) dP(x₀,…,x_b | x₀,…,x_a) = K^(b-a) f(x_a)`.
* `ProbabilityTheory.Kernel.traj_historyKernel_map_eval`: for a Markov `K`,
  the endpoint marginal of the native continuation is `K^(b-a)(x_a, ·)`.

This specializes the native Ionescu--Tulcea construction, rather than
constructing a second path law; see O. Kallenberg, *Foundations of Modern
Probability*, third edition (2021), Theorem 8.24,
DOI 10.1007/978-3-030-61871-1.
-/

@[expose] public section

open MeasureTheory Finset Preorder
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]

/-- A homogeneous transition reads only the last state of the history. -/
noncomputable def historyKernel (K : Kernel S S) (n : ℕ) : Kernel (Iic n → S) S :=
  K.comap (fun x => x ⟨n, by simp⟩) (measurable_pi_apply _)

instance historyKernel_isSFiniteKernel (K : Kernel S S) [IsSFiniteKernel K] (n : ℕ) :
    IsSFiniteKernel (historyKernel K n) := by unfold historyKernel; infer_instance

instance historyKernel_isMarkovKernel (K : Kernel S S) [IsMarkovKernel K] (n : ℕ) :
    IsMarkovKernel (historyKernel K n) := by unfold historyKernel; infer_instance

/-- Finite-history endpoint integration agrees with native kernel powers. -/
theorem lintegral_partialTraj_historyKernel (K : Kernel S S) [IsSFiniteKernel K]
    {a b : ℕ} (hab : a ≤ b) (x : Iic a → S) {f : S → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f (y ⟨b, by simp⟩) ∂partialTraj (X := fun _ => S) (historyKernel K) a b x) =
      ∫⁻ z, f z ∂(K ^ (b - a)) (x ⟨a, by simp⟩) := by
  induction b, hab using Nat.le_induction generalizing f with
  | base =>
    rw [partialTraj_self, Kernel.id_apply,
      lintegral_dirac' (f := fun y : Iic a → S => f (y ⟨a, by simp⟩)) _ (by fun_prop)]
    rw [Nat.sub_self, pow_zero]
    change f (x ⟨a, by simp⟩) = ∫⁻ z, f z ∂Kernel.id (x ⟨a, by simp⟩)
    rw [Kernel.id_apply, lintegral_dirac' _ hf]
  | succ b hab ih =>
    have hf' : Measurable (fun y : Iic (b + 1) → S => f (y ⟨b + 1, by simp⟩)) :=
      hf.comp (measurable_pi_apply _)
    rw [partialTraj_succ_of_le hab,
      Kernel.lintegral_map _ (measurable_IicProdIoc (X := fun _ => S)) _
        hf']
    rw [lintegral_comp _ _ _
      (g := fun p => f (IicProdIoc (X := fun _ => S) b (b + 1) p ⟨b + 1, by simp⟩))
      (hf'.comp measurable_IicProdIoc)]
    conv_lhs =>
      arg 2
      ext y
      rw [lintegral_id_prod
        (f := fun p => f (IicProdIoc (X := fun _ => S) b (b + 1) p ⟨b + 1, by simp⟩))
        (hf'.comp measurable_IicProdIoc)]
      rw [Kernel.lintegral_map _ (MeasurableEquiv.piSingleton (X := fun _ => S) b).measurable _
        (g' := fun z => f (IicProdIoc (X := fun _ => S) b (b + 1) (y, z)
          ⟨b + 1, by simp⟩))
        (hf'.comp
          (measurable_IicProdIoc.comp (measurable_const.prodMk measurable_id)))]
    have he : ∀ (y : Iic b → S) (z : S),
        f (IicProdIoc (X := fun _ => S) b (b + 1)
          (y, MeasurableEquiv.piSingleton (X := fun _ => S) b z) ⟨b + 1, by simp⟩) = f z := by
      intro y z
      simp [IicProdIoc_def, MeasurableEquiv.piSingleton]
    simp_rw [he]
    change (∫⁻ y, (∫⁻ z, f z ∂K (y ⟨b, by simp⟩))
      ∂partialTraj (X := fun _ => S) (historyKernel K) a b x) = _
    rw [ih (hf := hf.lintegral_kernel)]
    rw [Nat.succ_sub hab, pow_succ']
    exact (lintegral_comp K (K ^ (b - a)) _ hf).symm

/-- The continuation endpoint has the iterated homogeneous transition law. -/
theorem traj_historyKernel_map_eval (K : Kernel S S) [IsMarkovKernel K]
    {a b : ℕ} (hab : a ≤ b) (x : Iic a → S) :
    (traj (X := fun _ => S) (historyKernel K) a x).map (fun y => y b) =
      (K ^ (b - a)) (x ⟨a, by simp⟩) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [MeasureTheory.lintegral_map hf (by fun_prop)]
  have hm := traj_map_frestrictLe_apply (X := fun _ => S) (κ := historyKernel K) a b x
  have hi := congrArg (fun μ => ∫⁻ y, f (y ⟨b, by simp⟩) ∂μ) hm
  rw [MeasureTheory.lintegral_map (f := fun y : Iic b → S => f (y ⟨b, by simp⟩))
    (by fun_prop) (by fun_prop)] at hi
  exact hi.trans (lintegral_partialTraj_historyKernel K hab x hf)

end ProbabilityTheory.Kernel

end
