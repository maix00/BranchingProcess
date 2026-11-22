/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.IonescuTulcea.Conditional
public import Mathlib.Probability.Process.Stopping

/-!
# Conditional integration at trajectory stopping times on the finite-time event

## Public declarations

* `ProbabilityTheory.Kernel.condExp_trajMeasure_stopping`: for a possibly infinite
  stopping time $\tau$ and jointly strongly measurable payoffs $g_n(h,y)$,
  $E[g_\tau(X_{0:\tau},X)\mid\mathcal F_\tau]
    =\int g_\tau(X_{0:\tau},y)\,d\operatorname{traj}_\tau(X_{0:\tau})$.
  The identity holds almost surely on $\{\tau<\infty\}$. Both the stopped
  payoff and each deterministic-time payoff are integrable.

This assembles the deterministic-time conditional law using Mathlib's
`condExp_stopping_time_ae_eq_restrict_eq_of_countable` on the cells
$\{\tau=n\}$. No new stopping-time or conditional-distribution object is defined.
-/

@[expose] public section

open MeasureTheory Finset Preorder

namespace ProbabilityTheory.Kernel

/-- Condition a history-dependent payoff on the finite-time event of a
possibly infinite stopping time under the actual random-initial path law. -/
theorem condExp_trajMeasure_stopping
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (τ : (Π n, X n) → WithTop ℕ)
    (hτ : IsStoppingTime Filtration.piLE τ)
    (g : (n : ℕ) → ((Π i : Iic n, X i) × (Π n, X n)) → ℝ)
    (hg : ∀ n, StronglyMeasurable (g n))
    (hgi : ∀ n, Integrable (fun x ↦ g n (frestrictLe n x, x)) (trajMeasure μ₀ κ))
    (hstop : Integrable (fun x ↦ g ((τ x).untopD 0)
      (frestrictLe ((τ x).untopD 0) x, x)) (trajMeasure μ₀ κ)) :
    (trajMeasure μ₀ κ)[fun x ↦ g ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x, x) |
      hτ.measurableSpace] =ᵐ[(trajMeasure μ₀ κ).restrict {x | τ x ≠ ⊤}]
      fun x ↦ ∫ y, g ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x, y)
        ∂traj κ ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x) := by
  let P := trajMeasure μ₀ κ
  let f := fun x ↦ g ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x, x)
  have hall : P[f | hτ.measurableSpace] =ᵐ[
      P.restrict (⋃ n : ℕ, {x | τ x = n})]
      fun x ↦ ∫ y, g ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x, y)
        ∂traj κ ((τ x).untopD 0) (frestrictLe ((τ x).untopD 0) x) := by
    rw [ae_eq_restrict_iUnion_iff]
    intro n
    let A := {x | τ x = n}
    have hA : MeasurableSet[Filtration.piLE n] A := by
      exact hτ.measurableSet_eq n
    have hAfull : MeasurableSet A := Filtration.piLE.le n _ hA
    have hdiff : (fun x ↦ f x - g n (frestrictLe n x, x)) =ᵐ[P.restrict A] 0 := by
      filter_upwards [ae_restrict_mem hAfull] with x hx
      change τ x = (n : WithTop ℕ) at hx
      have hi : (τ x).untopD 0 = n := by rw [hx]; rfl
      dsimp only [f]
      rw [hi]
      exact sub_self _
    have hzero := condExp_ae_eq_restrict_zero hA hdiff
    have hsub := condExp_sub hstop (hgi n) (Filtration.piLE n)
    have hdet := condExp_of_jointLaw P (frestrictLe n) id
      (measurable_frestrictLe n) measurable_id (traj κ n)
      (trajMeasure_compProd_traj κ μ₀ n).symm (hg n) (hgi n)
    have hs := condExp_stopping_time_ae_eq_restrict_eq_of_countable (μ := P) hτ n (f := f)
    have hs' : P[f | hτ.measurableSpace] =ᵐ[P.restrict A] P[f | Filtration.piLE n] := by
      exact hs
    rw [Filtration.piLE_eq_comap_frestrictLe] at hzero hsub
    filter_upwards [hs', hzero, hsub.restrict, hdet.restrict,
      ae_restrict_mem hAfull] with x hsx hzx hsubx hdetx hx
    change τ x = (n : WithTop ℕ) at hx
    have hi : (τ x).untopD 0 = n := by rw [hx]; rfl
    rw [hsx]
    have heq : P[f | MeasurableSpace.comap (frestrictLe n) inferInstance] x =
        P[fun x ↦ g n (frestrictLe n x, x) |
          MeasurableSpace.comap (frestrictLe n) inferInstance] x := by
      exact sub_eq_zero.mp (hsubx.symm.trans hzx)
    rw [Filtration.piLE_eq_comap_frestrictLe, hi]
    exact heq.trans hdetx
  have hunion : (⋃ n : ℕ, {x | τ x = n}) = {x | τ x ≠ ⊤} := by
    ext x
    cases hval : τ x using WithTop.recTopCoe <;> simp [hval]
  simpa only [hunion] using hall

end ProbabilityTheory.Kernel
