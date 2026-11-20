/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.ConditionalExpectation
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Conditioning complete trajectories with random initial values

## Public declarations

* `ProbabilityTheory.Kernel.trajMeasure_compProd_traj` identifies the joint
  law of the prefix and the complete path:
  $P_{0:a}\otimes\operatorname{traj}_a=P\circ(X_{0:a},X)^{-1}$.
* `ProbabilityTheory.Kernel.condExp_trajMeasure` gives
  $E_P[f(X)\mid X_{0:a}]=\int f\,d\operatorname{traj}_a(X_{0:a})$
  for a strongly measurable integrable payoff and any probability initial law.

Mathlib's `partialTraj_compProd_traj` and `condExp_traj` treat a fixed
initial history. These statements integrate the same identities against an
arbitrary initial distribution, retaining arbitrary measurable coordinate spaces.
-/

@[expose] public section

open MeasureTheory Finset Preorder

namespace ProbabilityTheory.Kernel

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))) [∀ n, IsMarkovKernel (κ n)]
  (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]

/-- Random-initial trajectory disintegration at a deterministic time, for the
whole path rather than only the next coordinate. -/
theorem trajMeasure_compProd_traj (a : ℕ) :
    (trajMeasure μ₀ κ).map (frestrictLe a) ⊗ₘ traj κ a =
      (trajMeasure μ₀ κ).map (fun x ↦ (frestrictLe a x, x)) := by
  rw [Measure.compProd_eq_comp_prod, trajMeasure, Measure.map_comp _ _ (by fun_prop),
    traj_map_frestrictLe, Measure.comp_assoc, Measure.map_comp _ _ (by fun_prop)]
  congr with x₀ : 1
  rw [comp_apply, ← Measure.compProd_eq_comp_prod, map_apply _ (by fun_prop),
    partialTraj_compProd_traj (Nat.zero_le a)]

/-- The native continuation kernel is also the conditional path law when the
initial state has an arbitrary probability distribution. -/
theorem condExp_trajMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (a : ℕ)
    {f : (Π n, X n) → E} (hf : StronglyMeasurable f)
    (hfi : Integrable f (trajMeasure μ₀ κ)) :
    (trajMeasure μ₀ κ)[f | Filtration.piLE a] =ᵐ[trajMeasure μ₀ κ]
      fun x ↦ ∫ y, f y ∂traj κ a (frestrictLe a x) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact condExp_of_jointLaw (trajMeasure μ₀ κ) (frestrictLe a) id
    (measurable_frestrictLe a) measurable_id (traj κ a)
    (trajMeasure_compProd_traj κ μ₀ a).symm
    (hf.comp_measurable measurable_snd) hfi

end ProbabilityTheory.Kernel
