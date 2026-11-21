/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Identifying a process from its initial and one-step joint laws

## Public declarations

* `ProbabilityTheory.Kernel.trajMeasure_initial` recovers the initial
  marginal $P\circ X_0^{-1}=\mu_0$ of the Ionescu--Tulcea law.
* `ProbabilityTheory.Kernel.eq_trajMeasure` states that a probability law
  $P$ on paths is determined by that initial marginal and
  $P_{0:n}\otimes\kappa_n=P\circ(X_{0:n},X_{n+1})^{-1}$ for every $n$.

The proof identifies finite prefixes by induction and then uses uniqueness
of the projective limit. This is the uniqueness part of the Ionescu--Tulcea
construction; compare O. Kallenberg, *Foundations of Modern Probability*,
Theorem 8.24, third edition (2021), DOI 10.1007/978-3-030-61871-1.
No regular conditional distribution or standard-Borel hypothesis is used.
-/

@[expose] public section

open MeasureTheory Finset Preorder

namespace ProbabilityTheory.Kernel

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))) [∀ n, IsMarkovKernel (κ n)]

/-- The initial coordinate of the trajectory has the prescribed initial law. -/
theorem trajMeasure_initial (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀] :
    (trajMeasure μ₀ κ).map (fun x ↦ x 0) = μ₀ := by
  have ht : (traj κ 0).map (fun x ↦ x 0) =
      deterministic (fun h : Π i : Iic 0, X i ↦ h ⟨0, by simp⟩) (by fun_prop) := by
    have he : (fun x : Π n, X n ↦ x 0) =
        (fun h : Π i : Iic 0, X i ↦ h ⟨0, by simp⟩) ∘ frestrictLe 0 := rfl
    rw [he, map_comp_right _ (by fun_prop) (by fun_prop), traj_map_frestrictLe, partialTraj_self]
    ext h A hA
    rw [map_apply _ (by fun_prop), Kernel.id_apply, Measure.map_dirac' (by fun_prop),
      deterministic_apply (by fun_prop)]
  rw [trajMeasure, Measure.map_comp _ _ (by fun_prop), ht,
    Measure.deterministic_comp_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  have heq : ((fun h : Π i : Iic 0, X i ↦ h ⟨0, by simp⟩) ∘
      (MeasurableEquiv.piUnique (fun i : Iic 0 ↦ X i)).symm) = id := by
    funext x
    exact (MeasurableEquiv.piUnique (fun i : Iic 0 ↦ X i)).apply_symm_apply x
  rw [heq, Measure.map_id]

/-- Matching the initial and successive past/next laws identifies the full path law. -/
theorem eq_trajMeasure (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (P : Measure (Π n, X n)) [IsProbabilityMeasure P]
    (hinit : P.map (fun x ↦ x 0) = μ₀)
    (hstep : ∀ n, P.map (frestrictLe n) ⊗ₘ κ n =
      P.map (fun x ↦ (frestrictLe n x, x (n + 1)))) : P = trajMeasure μ₀ κ := by
  let Q := trajMeasure μ₀ κ
  have hpref : ∀ n, P.map (frestrictLe n) = Q.map (frestrictLe n) := by
    intro n
    induction n with
    | zero =>
      let e : (Π i : Iic 0, X i) ≃ᵐ X 0 := MeasurableEquiv.piUnique _
      apply e.map_measurableEquiv_injective
      rw [Measure.map_map e.measurable (by fun_prop),
        Measure.map_map e.measurable (by fun_prop)]
      change P.map (fun x ↦ x 0) = Q.map (fun x ↦ x 0)
      rw [hinit, trajMeasure_initial]
    | succ n ih =>
      let e : (Π i : Iic (n + 1), X i) ≃ᵐ ((Π i : Iic n, X i) × X (n + 1)) :=
        (MeasurableEquiv.IicProdIoc (Nat.le_succ n)).symm.trans
          (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piSingleton n).symm)
      apply e.map_measurableEquiv_injective
      rw [Measure.map_map e.measurable (by fun_prop),
        Measure.map_map e.measurable (by fun_prop)]
      have he : e ∘ frestrictLe (n + 1) =
          (fun x : Π n, X n ↦ (frestrictLe n x, x (n + 1))) := by
        ext x i <;> rfl
      rw [he, ← hstep n, ← map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure, ih]
  let family (I : Finset ℕ) := Q.map I.restrict
  have hfam : IsProjectiveMeasureFamily family := by
    intro I J hJI
    dsimp [family]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hP : IsProjectiveLimit P family :=
    (isProjectiveLimit_nat_iff hfam P).mpr hpref
  exact hP.unique (fun _ ↦ rfl)


end ProbabilityTheory.Kernel
