/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.DomainFlow.SubtreeVector

/-!
# Independence of subtree-vector events from the past

In namespace `ProbabilityTheory.BranchingRandomWalk`, the public declarations
are:

- `multiRootSubtreeStepFieldVector_future_measurable roots hlen`: if each
  root address has length `n`, then the subtree vector is measurable with
  respect to the future-coordinate sigma-algebra
  $\sigma(\omega(r,u): |u|\ge n)$.
- `fixed_multiRootSubtreeStepFieldVector_independent μ roots hlen`:
  $\operatorname{Indep}(\mathcal F_n,\sigma(V),\nu_m)$, where
  $\mathcal F_n$ is the multi-root past,
  `V` is the subtree vector, and `ν_m` is the finite-root product law.
- `fixed_multiRootSubtreeStepFieldVector_event_factorization μ roots hlen hinj A B hA hB`:
  for pairwise distinct roots at level `n`,
  $\nu_m(A\cap V^{-1}(B))=\nu_m(A)\,(\bigotimes_{j:Fin\,k}
  \operatorname{stepFieldLaw}(\mu))(B)$ when `A`
  is measurable in `𝓕_n` and `B` is measurable in the subtree-vector space.

The subtree vector is measurable for the future space at the roots' common
generation. Its law is the independent product of `k` single-root fields, so
past events factor against measurable subtree-vector events.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


theorem multiRootSubtreeStepFieldVector_future_measurable
    {m k n : ℕ} {X : Type*} [MeasurableSpace X]
    (roots : Fin k → Fin m × 𝕍)
    (hlen : ∀ j, (roots j).2.length = n) :
    Measurable[multiRootStepFutureSpace n]
      (multiRootSubtreeStepFieldVector (X := X) roots) := by
  apply (@measurable_pi_iff (FiniteRootStepField m ℕ X) (Fin k)
    (fun _ => 𝕍 → Step ℕ X) (multiRootStepFutureSpace n)
    (fun _ => inferInstance) (multiRootSubtreeStepFieldVector roots)).2
  intro j
  apply (@measurable_pi_iff (FiniteRootStepField m ℕ X) 𝕍
    (fun _ => Step ℕ X) (multiRootStepFutureSpace n)
    (fun _ => inferInstance)
    (fun ω v => multiRootSubtreeStepFieldVector roots ω j v)).2
  intro v
  let p : Fin m × 𝕍 := ((roots j).1, (roots j).2 ++ v)
  have hp : n ≤ p.2.length := by simp [p, hlen j]
  have hle : multiRootStepCoordinateSpace (X := X) p ≤
      multiRootStepFutureSpace n :=
    le_iSup_of_le p (le_iSup_of_le hp le_rfl)
  have hcoord : Measurable[multiRootStepCoordinateSpace (X := X) p]
      (fun ω : FiniteRootStepField m ℕ X => ω p.1 p.2) :=
    Measurable.of_comap_le le_rfl
  exact hcoord.mono hle le_rfl

theorem fixed_multiRootSubtreeStepFieldVector_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → Fin m × 𝕍)
    (hlen : ∀ j, (roots j).2.length = n) :
    Indep (multiRootStepFiltration (m := m) (X := X) n)
      (MeasurableSpace.comap
        (multiRootSubtreeStepFieldVector roots) inferInstance)
      (finiteRootStepFieldLaw μ m) :=
  indep_of_indep_of_le_right (multiRootStep_past_future_independent μ n)
    (multiRootSubtreeStepFieldVector_future_measurable roots hlen).comap_le

theorem fixed_multiRootSubtreeStepFieldVector_event_factorization
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → Fin m × 𝕍)
    (hlen : ∀ j, (roots j).2.length = n)
    (hinj : Function.Injective roots)
    (A : Set (FiniteRootStepField m ℕ X))
    (B : Set (Fin k → 𝕍 → Step ℕ X))
    (hA : MeasurableSet[multiRootStepFiltration (m := m) (X := X) n] A)
    (hB : MeasurableSet B) :
    finiteRootStepFieldLaw μ m
        (A ∩ multiRootSubtreeStepFieldVector roots ⁻¹' B) =
      finiteRootStepFieldLaw μ m A *
        (Measure.infinitePi (fun _ : Fin k => stepFieldLaw μ)) B := by
  have hB' : MeasurableSet[MeasurableSpace.comap
      (multiRootSubtreeStepFieldVector roots) inferInstance]
      (multiRootSubtreeStepFieldVector roots ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((fixed_multiRootSubtreeStepFieldVector_independent μ roots hlen
    ).indepSet_of_measurableSet hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply
      (multiRootSubtreeStepFieldVector_measurable roots) hB,
    fixed_multiRootSubtreeStepFieldVector_law μ roots hlen hinj] at h
  exact h

end ProbabilityTheory.BranchingRandomWalk
