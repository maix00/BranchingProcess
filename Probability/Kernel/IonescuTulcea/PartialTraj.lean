/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# One-step integration of finite histories

## Public declarations

* `ProbabilityTheory.Kernel.lintegral_partialTraj_succ`: for arbitrary
  measurable coordinate spaces and s-finite history kernels,
  `∫ F(x₀,…,x_b,x_b₊₁) dP_{a:b+1} = ∫∫ F(y,z) dκ_b(y)(z) dP_{a:b}(y)`.

This exposes the integral form of Mathlib's `partialTraj_succ_of_le`,
using the same native history concatenation and kernels.
-/

@[expose] public section

open MeasureTheory Finset Preorder
open scoped ENNReal

namespace ProbabilityTheory.Kernel

/-- Append the final coordinate by one iterated kernel integral. -/
theorem lintegral_partialTraj_succ {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ n, IsSFiniteKernel (κ n)] {a b : ℕ} (hab : a ≤ b)
    (x : Π i : Iic a, X i) {f : (Π i : Iic (b + 1), X i) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ y, f y ∂partialTraj κ a (b + 1) x) =
      ∫⁻ y, ∫⁻ z, f (IicProdIoc b (b + 1) (y, MeasurableEquiv.piSingleton b z))
        ∂κ b y ∂partialTraj κ a b x := by
  rw [partialTraj_succ_of_le hab,
    Kernel.lintegral_map _ (measurable_IicProdIoc (X := X)) _ hf]
  rw [lintegral_comp _ _ _ (g := fun p => f (IicProdIoc (X := X) b (b + 1) p))
    (hf.comp measurable_IicProdIoc)]
  simp_rw [lintegral_id_prod (f := fun p => f (IicProdIoc (X := X) b (b + 1) p))
    (hf.comp measurable_IicProdIoc)]
  congr 1
  funext y
  exact Kernel.lintegral_map _ (MeasurableEquiv.piSingleton (X := X) b).measurable _
    (g' := fun z => f (IicProdIoc (X := X) b (b + 1) (y, z)))
    (hf.comp (measurable_IicProdIoc.comp (measurable_const.prodMk measurable_id)))

end ProbabilityTheory.Kernel

end
