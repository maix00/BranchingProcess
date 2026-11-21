/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Kernel.Basic
public import Mathlib.Probability.Kernel.Composition.CompProd
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Products of probability kernels

## Public declarations

* `ProbabilityTheory.Kernel.infinitePi` constructs the joint kernel
  $K(a)=\bigotimes_i\kappa_i(a)$ of conditionally independent coordinates.
  The input and coordinate spaces are arbitrary measurable spaces.
* `ProbabilityTheory.Kernel.infinitePi_apply` identifies that product law.
* `ProbabilityTheory.Kernel.infinitePi.isMarkovKernel` states that the
  product of probability kernels is a probability kernel.
* `ProbabilityTheory.Kernel.infinitePi_pi` evaluates a finite rectangular
  cylinder: $K(a)(\prod_{i\in J}A_i)=\prod_{i\in J}\kappa_i(a,A_i)$.
* `ProbabilityTheory.Kernel.infinitePi_compProd` proves that independent
  coordinatewise two-stage sampling gives $\bigotimes_i(\kappa_i\otimes\eta_i)$.
* `MeasureTheory.Measure.infinitePi_compProd` gives the corresponding
  identity for independent probability measures followed by coordinate kernels.
* `ProbabilityTheory.Kernel.infinitePi_map_eval` recovers the coordinate
  marginal $K(a)\circ\operatorname{ev}_i^{-1}=\kappa_i(a)$.

Measurability is proved first on finite boxes, then on arbitrary finite
cylinders, using Mathlib's Giry measurable structure and monotone class API.
No standard-Borel or countability assumption is needed.
-/

@[expose] public section

open MeasureTheory Set

namespace ProbabilityTheory.Kernel

private lemma measurable_measure_pi {A ι : Type*} {X : ι → Type*}
    [MeasurableSpace A] [∀ i, MeasurableSpace (X i)] [Fintype ι]
    (κ : (i : ι) → Kernel A (X i)) [∀ i, IsMarkovKernel (κ i)] :
    Measurable (fun a ↦ Measure.pi (fun i ↦ κ i a)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_pi.symm isPiSystem_pi
  rintro B ⟨t, ht, rfl⟩
  simp_rw [Measure.pi_pi]
  exact Finset.measurable_prod _ (fun i _ ↦ (κ i).measurable_coe (ht i (mem_univ i)))

/-- The independent product of probability kernels with a common input. -/
noncomputable def infinitePi {A ι : Type*} {X : ι → Type*}
    [MeasurableSpace A] [∀ i, MeasurableSpace (X i)]
    (κ : (i : ι) → Kernel A (X i)) [∀ i, IsMarkovKernel (κ i)] :
    Kernel A (Π i, X i) where
  toFun a := Measure.infinitePi (fun i ↦ κ i a)
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders
    intro B hB
    obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders B).mp hB
    simp_rw [Measure.infinitePi_cylinder _ hS]
    exact (Measure.measurable_coe hS).comp (measurable_measure_pi (fun i : s ↦ κ i))

@[simp] theorem infinitePi_apply {A ι : Type*} {X : ι → Type*}
    [MeasurableSpace A] [∀ i, MeasurableSpace (X i)]
    (κ : (i : ι) → Kernel A (X i)) [∀ i, IsMarkovKernel (κ i)] (a : A) :
    infinitePi κ a = Measure.infinitePi (fun i ↦ κ i a) := rfl

instance infinitePi.isMarkovKernel {A ι : Type*} {X : ι → Type*}
    [MeasurableSpace A] [∀ i, MeasurableSpace (X i)]
    (κ : (i : ι) → Kernel A (X i)) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (infinitePi κ) where
  isProbabilityMeasure a := by rw [infinitePi_apply]; infer_instance

/-- Finite rectangular cylinders have the product of their marginal masses. -/
theorem infinitePi_pi {A ι : Type*} {X : ι → Type*}
    [MeasurableSpace A] [∀ i, MeasurableSpace (X i)]
    (κ : (i : ι) → Kernel A (X i)) [∀ i, IsMarkovKernel (κ i)]
    (a : A) (s : Finset ι) (t : (i : ι) → Set (X i))
    (ht : ∀ i ∈ s, MeasurableSet (t i)) :
    infinitePi κ a (Set.pi s t) = ∏ i ∈ s, κ i a (t i) :=
  Measure.infinitePi_pi _ ht

/-- Each coordinate of the product kernel has its specified marginal law. -/
theorem infinitePi_map_eval {A ι : Type*} {X : ι → Type*}
    [MeasurableSpace A] [∀ i, MeasurableSpace (X i)]
    (κ : (i : ι) → Kernel A (X i)) [∀ i, IsMarkovKernel (κ i)]
    (a : A) (i : ι) : (infinitePi κ a).map (fun x ↦ x i) = κ i a :=
  Measure.infinitePi_map_eval _ i


/-- Forming independent coordinate pairs commutes with successive conditional
sampling. Each second coordinate may depend on its own first coordinate. -/
theorem infinitePi_compProd {A ι : Type*} {B C : ι → Type*}
    [MeasurableSpace A] [∀ i, MeasurableSpace (B i)] [∀ i, MeasurableSpace (C i)]
    (κ : (i : ι) → Kernel A (B i)) [∀ i, IsMarkovKernel (κ i)]
    (η : (i : ι) → Kernel (A × B i) (C i)) [∀ i, IsMarkovKernel (η i)] (a : A) :
    (((infinitePi κ) ⊗ₖ infinitePi (fun i ↦
        (η i).comap (fun p : A × (Π i, B i) ↦ (p.1, p.2 i)) (by fun_prop))) a).map
        (fun p i ↦ (p.1 i, p.2 i)) =
      Measure.infinitePi (fun i ↦ (κ i ⊗ₖ η i) a) := by
  classical
  apply Measure.eq_infinitePi
  intro s t ht
  have hpair : Measurable (fun p : (Π i, B i) × (Π i, C i) ↦ fun i ↦ (p.1 i, p.2 i)) := by
    fun_prop
  have hbox : MeasurableSet (Set.pi (s : Set ι) t) := MeasurableSet.pi s.countable_toSet (fun i _ ↦ ht i)
  rw [Measure.map_apply hpair hbox, compProd_apply (hpair hbox)]
  have hsection (b : Π i, B i) :
      (fun c : Π i, C i ↦ fun i ↦ (b i, c i)) ⁻¹' Set.pi (s : Set ι) t =
        Set.pi (s : Set ι) (fun i ↦ Prod.mk (b i) ⁻¹' t i) := by
    ext c
    simp
  simp only [infinitePi_apply, comap_apply]
  simp_rw [show ∀ b : Π i, B i,
      (Prod.mk b ⁻¹' ((fun p : (Π i, B i) × (Π i, C i) ↦ fun i ↦ (p.1 i, p.2 i)) ⁻¹'
        Set.pi (s : Set ι) t)) =
        Set.pi (s : Set ι) (fun i ↦ Prod.mk (b i) ⁻¹' t i) from hsection]
  have hinner (b : Π i, B i) :
      Measure.infinitePi (fun i ↦ η i (a, b i))
          (Set.pi (s : Set ι) (fun i ↦ Prod.mk (b i) ⁻¹' t i)) =
        ∏ i ∈ s, η i (a, b i) (Prod.mk (b i) ⁻¹' t i) :=
    Measure.infinitePi_pi _ (fun i _ ↦ (ht i).preimage
      ((measurable_const (a := b i)).prodMk measurable_id))
  simp_rw [hinner]
  let f (i : ι) (b : B i) := if hi : i ∈ s then η i (a, b) (Prod.mk b ⁻¹' t i) else 1
  have hf (i : ι) : Measurable (f i) := by
    dsimp [f]
    split_ifs with hi
    · exact measurable_kernel_prodMk_left' (ht i) a
    · exact measurable_const
  have heq (b : Π i, B i) :
      (∏ i ∈ s, η i (a, b i) (Prod.mk (b i) ⁻¹' t i)) = ∏ i ∈ s, f i (b i) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [f, hi]
  simp_rw [heq]
  have hint : (∫⁻ b : Π i, B i, ∏ i ∈ s, f i (b i)
      ∂Measure.infinitePi (fun i ↦ κ i a)) =
      ∏ i ∈ s, ∫⁻ b : Π i, B i, f i (b i) ∂Measure.infinitePi (fun i ↦ κ i a) :=
    lintegral_prod_eq_prod_lintegral_of_indepFun s (fun i (b : Π i, B i) ↦ f i (b i))
      (iIndepFun_infinitePi hf) (fun i ↦ (hf i).comp (measurable_pi_apply i))
  rw [hint]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← MeasureTheory.lintegral_map (hf i) (measurable_pi_apply i), Measure.infinitePi_map_eval]
  simp only [f, hi, dite_true]
  exact (compProd_apply (ht i) (κ i) (η i) a).symm

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

open ProbabilityTheory

/-- Independent products commute with conditioning each coordinate on its own past. -/
theorem infinitePi_compProd {ι : Type*} {B C : ι → Type*}
    [∀ i, MeasurableSpace (B i)] [∀ i, MeasurableSpace (C i)]
    (μ : (i : ι) → Measure (B i)) [∀ i, IsProbabilityMeasure (μ i)]
    (η : (i : ι) → Kernel (B i) (C i)) [∀ i, IsMarkovKernel (η i)] :
    ((Measure.infinitePi μ) ⊗ₘ Kernel.infinitePi (fun i ↦
        (η i).comap (fun b : Π i, B i ↦ b i) (measurable_pi_apply i))).map
        (fun p i ↦ (p.1 i, p.2 i)) =
      Measure.infinitePi (fun i ↦ μ i ⊗ₘ η i) := by
  have h := Kernel.infinitePi_compProd (fun i ↦ Kernel.const Unit (μ i))
    (fun i ↦ Kernel.prodMkLeft Unit (η i)) ()
  have hκ : Kernel.infinitePi (fun i ↦ Kernel.const Unit (μ i)) =
      Kernel.const Unit (Measure.infinitePi μ) := by ext a; rfl
  have hη : Kernel.infinitePi (fun i ↦ (Kernel.prodMkLeft Unit (η i)).comap
        (fun p : Unit × (Π i, B i) ↦ (p.1, p.2 i)) (by fun_prop)) =
      Kernel.prodMkLeft Unit (Kernel.infinitePi (fun i ↦
        (η i).comap (fun b : Π i, B i ↦ b i) (measurable_pi_apply i))) := by
    ext p
    rfl
  rw [hκ, hη] at h
  exact h

end MeasureTheory.Measure
