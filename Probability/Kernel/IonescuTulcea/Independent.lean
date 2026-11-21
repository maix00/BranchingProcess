/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.IonescuTulcea.Uniqueness
public import Probability.Kernel.Composition.InfinitePi
public import Probability.Kernel.Composition.Map

/-!
# Independent families of history-dependent processes

## Public declarations

* `ProbabilityTheory.Kernel.independentHistoryKernel` forms the next-step
  kernel $\bigotimes_i\kappa_{i,n}(x_{i,0:n})$ of independent component processes.
* `ProbabilityTheory.Kernel.independentHistoryKernel.isMarkovKernel` proves
  that it is a probability kernel.
* `ProbabilityTheory.Kernel.independentPathLaw_oneStep` proves the prescribed
  past/next joint-law identity for a product of component path laws, whenever
  it holds for each component.
* `ProbabilityTheory.Kernel.trajMeasure_infinitePi` identifies the resulting
  path law with the product of the component Ionescu--Tulcea laws:
  $\mathcal L((X_{i,n})_{n,i})=\bigotimes_i\mathcal L((X_{i,n})_n)$.

The proof uses finite-history uniqueness and the independent product
composition identity. The coordinate spaces are arbitrary measurable spaces.
-/

@[expose] public section

open MeasureTheory Finset Preorder

namespace ProbabilityTheory.Kernel

variable {ι : Type*} {X : ι → ℕ → Type*} [∀ i n, MeasurableSpace (X i n)]

/-- Evolve each component from its own history, conditionally independently. -/
noncomputable def independentHistoryKernel
    (κ : (i : ι) → (n : ℕ) → Kernel (Π k : Iic n, X i k) (X i (n + 1)))
    [∀ i n, IsMarkovKernel (κ i n)] (n : ℕ) :
    Kernel (Π k : Iic n, Π i, X i k) (Π i, X i (n + 1)) :=
  infinitePi (fun i ↦ (κ i n).comap (fun h k ↦ h k i) (by fun_prop))

instance independentHistoryKernel.isMarkovKernel
    (κ : (i : ι) → (n : ℕ) → Kernel (Π k : Iic n, X i k) (X i (n + 1)))
    [∀ i n, IsMarkovKernel (κ i n)] (n : ℕ) :
    IsMarkovKernel (independentHistoryKernel κ n) := by
  unfold independentHistoryKernel
  infer_instance

/-- Taking independent products preserves the specified conditional next-step laws. -/
theorem independentPathLaw_oneStep
    (κ : (i : ι) → (n : ℕ) → Kernel (Π k : Iic n, X i k) (X i (n + 1)))
    [∀ i n, IsMarkovKernel (κ i n)]
    (P : (i : ι) → Measure (Π n, X i n)) [∀ i, IsProbabilityMeasure (P i)]
    (hstep : ∀ i n, (P i).map (frestrictLe n) ⊗ₘ κ i n =
      (P i).map (fun x ↦ (frestrictLe n x, x (n + 1)))) (n : ℕ) :
    let Q := (Measure.infinitePi P).map (fun x n i ↦ x i n)
    Q.map (frestrictLe n) ⊗ₘ independentHistoryKernel κ n =
      Q.map (fun x ↦ (frestrictLe n x, x (n + 1))) := by
  let Q := (Measure.infinitePi P).map (fun x n i ↦ x i n)
  let μ := fun i ↦ (P i).map (frestrictLe n)
  let flip : (Π i, Π k : Iic n, X i k) → (Π k : Iic n, Π i, X i k) := fun h k i ↦ h i k
  have hflip : Measurable flip := by fun_prop
  have hpref : Q.map (frestrictLe n) = (Measure.infinitePi μ).map flip := by
    dsimp only [Q]
    rw [Measure.map_map (by fun_prop) (by fun_prop),
      ← Measure.infinitePi_map_pi P (fun _ ↦ measurable_frestrictLe n),
      Measure.map_map hflip (by fun_prop)]
    rfl
  change Q.map (frestrictLe n) ⊗ₘ independentHistoryKernel κ n =
    Q.map (fun x ↦ (frestrictLe n x, x (n + 1)))
  rw [hpref, Measure.map_compProd_left _ flip hflip]
  have hκ : (independentHistoryKernel κ n).comap flip hflip =
      infinitePi (fun i ↦ (κ i n).comap (fun h : Π i, Π k : Iic n, X i k ↦ h i)
        (measurable_pi_apply i)) := by
    ext h
    rfl
  rw [hκ]
  let unpack : (Π i, (Π k : Iic n, X i k) × X i (n + 1)) →
      (Π k : Iic n, Π i, X i k) × (Π i, X i (n + 1)) :=
    fun q ↦ (fun k i ↦ (q i).1 k, fun i ↦ (q i).2)
  have hunpack : Measurable unpack := by fun_prop
  have hproduct := Measure.infinitePi_compProd μ (fun i ↦ κ i n)
  have hmap := congrArg (fun m ↦ m.map unpack) hproduct
  rw [Measure.map_map hunpack (by fun_prop)] at hmap
  change (Measure.map (Prod.map flip id) _) = _
  rw [show (Prod.map flip id) =
      unpack ∘ (fun p : (Π i, Π k : Iic n, X i k) × (Π i, X i (n + 1)) ↦
        fun i ↦ (p.1 i, p.2 i)) from rfl, hmap]
  simp_rw [μ, hstep]
  rw [← Measure.infinitePi_map_pi P (fun i ↦
    (measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))),
    Measure.map_map hunpack (by fun_prop)]
  dsimp only [Q]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Independent component trajectory laws form the trajectory law of the
independent product of their history-dependent kernels. -/
theorem trajMeasure_infinitePi
    (κ : (i : ι) → (n : ℕ) → Kernel (Π k : Iic n, X i k) (X i (n + 1)))
    [∀ i n, IsMarkovKernel (κ i n)]
    (μ₀ : (i : ι) → Measure (X i 0)) [∀ i, IsProbabilityMeasure (μ₀ i)] :
    (Measure.infinitePi (fun i ↦ trajMeasure (μ₀ i) (κ i))).map (fun x n i ↦ x i n) =
      trajMeasure (Measure.infinitePi μ₀) (independentHistoryKernel κ) := by
  apply eq_trajMeasure
  · rw [Measure.map_map (by fun_prop) (by fun_prop)]
    change (Measure.infinitePi (fun i ↦ trajMeasure (μ₀ i) (κ i))).map
      (fun x i ↦ x i 0) = _
    rw [Measure.infinitePi_map_pi _ (fun _ ↦ measurable_pi_apply 0)]
    simp_rw [trajMeasure_initial]
  · exact independentPathLaw_oneStep κ _
      (fun i n ↦ map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure)

end ProbabilityTheory.Kernel
