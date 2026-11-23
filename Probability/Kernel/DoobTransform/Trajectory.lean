/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.DoobTransform.Basic
public import Probability.Kernel.IonescuTulcea.Markov

/-!
# Finite-history density of a Doob transform

## Public declarations

* `ProbabilityTheory.Kernel.lintegral_partialTraj_doobTransform`: for an
  s-finite `K`, finite positive measurable `h`, and `a ≤ b`,
  `Eʰ[F(X₀,…,X_b) | x₀,…,x_a] = E[h(X_b) F(X₀,…,X_b) | x₀,…,x_a]/h(x_a)`.
* `ProbabilityTheory.Kernel.partialTraj_doobTransform`: the native finite
  history law has density `h(x_b)/h(x_a)` with respect to its original law.

Both kernels use Mathlib's `partialTraj`. Multiplication of the successive
ratios `h(xⱼ₊₁)/h(xⱼ)` telescopes. This is the path form of Zhan Shi,
*Branching Random Walks*, LNM 2151 (2015), Chapter 4, §4.2, (4.4),
DOI 10.1007/978-3-319-25372-5. Harmonicity is only needed when the transformed
laws are to be probability measures.
-/

@[expose] public section

open MeasureTheory Finset Preorder
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]

/-- Endpoint weighting gives expectations of arbitrary finite-history payoffs. -/
theorem lintegral_partialTraj_doobTransform (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (hzero : ∀ x, h x ≠ 0) (htop : ∀ x, h x ≠ ∞)
    {a b : ℕ} (hab : a ≤ b) (x : Iic a → S)
    {f : (Iic b → S) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ y, f y ∂partialTraj (X := fun _ => S) (historyKernel (doobTransform K h)) a b x) =
      (∫⁻ y, h (y ⟨b, by simp⟩) * f y
        ∂partialTraj (X := fun _ => S) (historyKernel K) a b x) / h (x ⟨a, by simp⟩) := by
  let : IsSFiniteKernel (doobTransform K h) :=
    IsSFiniteKernel.withDensity K (fun x y => ENNReal.div_ne_top (htop y) (hzero x))
  induction b, hab using Nat.le_induction with
  | base =>
    simp only [partialTraj_self, Kernel.id_apply]
    rw [lintegral_dirac' _ hf,
      lintegral_dirac' (f := fun y : Iic a → S => h (y ⟨a, by simp⟩) * f y) _
        (by fun_prop)]
    rw [div_eq_mul_inv, mul_comm (h _), mul_assoc,
      ENNReal.mul_inv_cancel (hzero _) (htop _), mul_one]
  | succ b hab ih =>
    rw [partialTraj_succ_of_le hab,
      Kernel.lintegral_map _ (measurable_IicProdIoc (X := fun _ => S)) _ hf]
    rw [lintegral_comp _ _ _
      (g := fun p => f (IicProdIoc (X := fun _ => S) b (b + 1) p))
      (hf.comp measurable_IicProdIoc)]
    conv_lhs =>
      arg 2
      ext y
      rw [lintegral_id_prod
        (f := fun p => f (IicProdIoc (X := fun _ => S) b (b + 1) p))
        (hf.comp measurable_IicProdIoc)]
      rw [Kernel.lintegral_map _ (MeasurableEquiv.piSingleton (X := fun _ => S) b).measurable _
        (g' := fun z => f (IicProdIoc (X := fun _ => S) b (b + 1) (y, z)))
        (hf.comp (measurable_IicProdIoc.comp (measurable_const.prodMk measurable_id)))]
    change (∫⁻ y, (∫⁻ z, f (IicProdIoc (X := fun _ => S) b (b + 1)
      (y, MeasurableEquiv.piSingleton (X := fun _ => S) b z))
      ∂doobTransform K h (y ⟨b, by simp⟩))
      ∂partialTraj (X := fun _ => S) (historyKernel (doobTransform K h)) a b x) = _
    have happend : Measurable (fun p : (Iic b → S) × S =>
        f (IicProdIoc (X := fun _ => S) b (b + 1)
          (p.1, MeasurableEquiv.piSingleton (X := fun _ => S) b p.2))) :=
      hf.comp (measurable_IicProdIoc.comp (measurable_fst.prodMk
        ((MeasurableEquiv.piSingleton (X := fun _ => S) b).measurable.comp measurable_snd)))
    have hi : ∀ y : Iic b → S,
        (∫⁻ z, f (IicProdIoc (X := fun _ => S) b (b + 1)
          (y, MeasurableEquiv.piSingleton (X := fun _ => S) b z))
          ∂doobTransform K h (y ⟨b, by simp⟩)) =
        (∫⁻ z, h z * f (IicProdIoc (X := fun _ => S) b (b + 1)
          (y, MeasurableEquiv.piSingleton (X := fun _ => S) b z))
          ∂K (y ⟨b, by simp⟩)) / h (y ⟨b, by simp⟩) := fun y =>
      lintegral_doobTransform K hh (happend.comp (measurable_const.prodMk measurable_id)) _
    simp_rw [hi]
    have hm : Measurable (fun y : Iic b → S =>
        (∫⁻ z, h z * f (IicProdIoc (X := fun _ => S) b (b + 1)
          (y, MeasurableEquiv.piSingleton (X := fun _ => S) b z))
          ∂K (y ⟨b, by simp⟩)) / h (y ⟨b, by simp⟩)) :=
      (((hh.comp measurable_snd).mul happend).lintegral_kernel_prod_right'
        (κ := historyKernel K b)).div (hh.comp (measurable_pi_apply _))
    rw [ih hm]
    have hc : ∀ y : Iic b → S,
        h (y ⟨b, by simp⟩) *
          ((∫⁻ z, h z * f (IicProdIoc (X := fun _ => S) b (b + 1)
            (y, MeasurableEquiv.piSingleton (X := fun _ => S) b z))
            ∂K (y ⟨b, by simp⟩)) / h (y ⟨b, by simp⟩)) =
          ∫⁻ z, h z * f (IicProdIoc (X := fun _ => S) b (b + 1)
            (y, MeasurableEquiv.piSingleton (X := fun _ => S) b z))
            ∂K (y ⟨b, by simp⟩) := by
      intro y
      rw [div_eq_mul_inv, mul_left_comm, ENNReal.mul_inv_cancel (hzero _) (htop _), mul_one]
    simp_rw [hc]
    congr 1
    have hw : Measurable (fun y : Iic (b + 1) → S => h (y ⟨b + 1, by simp⟩) * f y) :=
      (hh.comp (measurable_pi_apply _)).mul hf
    rw [partialTraj_succ_of_le hab,
      Kernel.lintegral_map _ (measurable_IicProdIoc (X := fun _ => S)) _
        hw]
    rw [lintegral_comp _ _ _
      (g := fun p => h (IicProdIoc (X := fun _ => S) b (b + 1) p ⟨b + 1, by simp⟩) *
        f (IicProdIoc (X := fun _ => S) b (b + 1) p))
      (hw.comp measurable_IicProdIoc)]
    conv_rhs =>
      arg 2
      ext y
      rw [lintegral_id_prod
        (f := fun p => h (IicProdIoc (X := fun _ => S) b (b + 1) p ⟨b + 1, by simp⟩) *
          f (IicProdIoc (X := fun _ => S) b (b + 1) p))
        (hw.comp measurable_IicProdIoc)]
      rw [Kernel.lintegral_map _ (MeasurableEquiv.piSingleton (X := fun _ => S) b).measurable _
        (g' := fun z => h (IicProdIoc (X := fun _ => S) b (b + 1) (y, z)
          ⟨b + 1, by simp⟩) * f (IicProdIoc (X := fun _ => S) b (b + 1) (y, z)))
        (hw.comp
          (measurable_IicProdIoc.comp (measurable_const.prodMk measurable_id)))]
    apply lintegral_congr
    intro y
    apply lintegral_congr
    intro z
    simp [IicProdIoc_def, MeasurableEquiv.piSingleton]

/-- The finite-history Radon--Nikodym formula uses only the endpoint ratio. -/
theorem partialTraj_doobTransform (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (hzero : ∀ x, h x ≠ 0) (htop : ∀ x, h x ≠ ∞)
    {a b : ℕ} (hab : a ≤ b) (x : Iic a → S) :
    partialTraj (X := fun _ => S) (historyKernel (doobTransform K h)) a b x =
      (partialTraj (X := fun _ => S) (historyKernel K) a b x).withDensity
        (fun y => h (y ⟨b, by simp⟩) / h (x ⟨a, by simp⟩)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_partialTraj_doobTransform K hh hzero htop hab x hf,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf]
  simp only [div_eq_mul_inv]
  rw [← lintegral_mul_const _ (by fun_prop)]
  apply lintegral_congr
  intro y
  change (h (y ⟨b, by simp⟩) * f y) * (h (x ⟨a, by simp⟩))⁻¹ =
    (h (y ⟨b, by simp⟩) * (h (x ⟨a, by simp⟩))⁻¹) * f y
  ac_rfl

end ProbabilityTheory.Kernel

end
