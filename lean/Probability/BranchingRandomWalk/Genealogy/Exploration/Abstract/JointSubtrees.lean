/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.DomainFlow

/-!
# Joint law of an arbitrary family of abstract branching subtrees

Distinct roots at one generation use disjoint coordinates.  Their descendant
step fields therefore have the joint law of independent copies of the full
pre-sampled branching-step field. Neither the family index nor the child-slot
type is restricted to a finite or countable type in this product-law theorem.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



def subtreeStepFieldVector {κ α X : Type*}
    (roots : κ → TreeNode α)
    (ω : TreeNode α → Step α X) :
    κ → TreeNode α → Step α X :=
  fun i => subtreeStepField (roots i) ω

theorem subtreeStepFieldVector_measurable
    {κ α X : Type*} [MeasurableSpace X]
    (roots : κ → TreeNode α) :
    Measurable (subtreeStepFieldVector (X := X) roots) := by
  apply measurable_pi_iff.mpr
  intro i
  exact subtreeStepField_measurable (roots i)

theorem rootedBranchingAddresses_injective {κ : Type*} {n : ℕ}
    (roots : κ → TreeNode α)
    (hlen : ∀ i, (roots i).length = n)
    (hinj : Function.Injective roots) :
    Function.Injective (fun p : κ × TreeNode α => roots p.1 ++ p.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hp := congrArg (List.take n) h
  have hroot : roots i = roots j := by
    simpa [hlen i, hlen j] using hp
  have hij : i = j := hinj hroot
  subst j
  exact Prod.ext rfl (List.append_cancel_left h)

theorem fixed_subtreeStepFieldVector_law
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {κ : Type*} {n : ℕ} (roots : κ → TreeNode α)
    (hlen : ∀ i, (roots i).length = n)
    (hinj : Function.Injective roots) :
    (stepFieldLaw μ).map (subtreeStepFieldVector roots) =
      Measure.infinitePi (fun _ : κ => stepFieldLaw μ) := by
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : TreeNode α => μ)
    (f := fun p : κ × TreeNode α => roots p.1 ++ p.2)
    (rootedBranchingAddresses_injective roots hlen hinj)
  have hcurry := Measure.infinitePi_map_curry
    (μ := fun (_ : κ) (_ : TreeNode α) => μ)
  change (Measure.infinitePi (fun _ : TreeNode α => μ)).map
    (fun ω i v => ω (roots i ++ v)) =
      Measure.infinitePi
        (fun _ : κ => Measure.infinitePi (fun _ : TreeNode α => μ))
  rw [← hcurry, ← hflat]
  rw [Measure.map_map]
  · rfl
  · exact (MeasurableEquiv.curry (κ) (TreeNode α)
      (Step α X)).measurable
  · apply measurable_pi_iff.mpr
    intro p
    exact measurable_pi_apply (roots p.1 ++ p.2)

theorem stepDescendantSpace_le_future
    {α X : Type*} [MeasurableSpace X]
    (n : ℕ) (u : TreeNode α) (hu : n ≤ u.length) :
    stepDescendantSpace (X := X) u ≤
      stepFutureSpace n := by
  apply iSup_le
  intro v
  have hdepth : n ≤ (u ++ v).length := by simp; omega
  exact le_iSup_of_le (u ++ v) (le_iSup_of_le hdepth le_rfl)

theorem subtreeStepFieldVector_future_measurable
    {α X : Type*} [MeasurableSpace X] {κ : Type*} {n : ℕ}
    (roots : κ → TreeNode α) (hlen : ∀ i, (roots i).length = n) :
    Measurable[stepFutureSpace n]
      (subtreeStepFieldVector (X := X) roots) := by
  apply (@measurable_pi_iff
    (TreeNode α → Step α X) (κ)
    (fun _ => TreeNode α → Step α X)
    (stepFutureSpace n) (fun _ => inferInstance)
    (subtreeStepFieldVector roots)).2
  intro i
  exact (subtreeStepField_descendant_measurable (X := X) (roots i)).mono
    (stepDescendantSpace_le_future n (roots i) (by rw [hlen i]))
    le_rfl

theorem fixed_subtreeStepFieldVector_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {κ : Type*} {n : ℕ} (roots : κ → TreeNode α)
    (hlen : ∀ i, (roots i).length = n) :
    Indep (generationFiltration (M := Step α X) n)
      (MeasurableSpace.comap (subtreeStepFieldVector roots) inferInstance)
      (stepFieldLaw μ) :=
  indep_of_indep_of_le_right
    (generation_stepFuture_independent μ n)
    (subtreeStepFieldVector_future_measurable roots hlen).comap_le

theorem fixed_subtreeStepFieldVector_event_factorization
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {κ : Type*} {n : ℕ} (roots : κ → TreeNode α)
    (hlen : ∀ i, (roots i).length = n)
    (hinj : Function.Injective roots)
    (A : Set (TreeNode α → Step α X))
    (B : Set (κ → TreeNode α → Step α X))
    (hA : MeasurableSet[
      generationFiltration (M := Step α X) n] A)
    (hB : MeasurableSet B) :
    stepFieldLaw μ (A ∩ subtreeStepFieldVector roots ⁻¹' B) =
      stepFieldLaw μ A *
        (Measure.infinitePi (fun _ : κ => stepFieldLaw μ)) B := by
  have hB' : MeasurableSet[
      MeasurableSpace.comap (subtreeStepFieldVector roots) inferInstance]
      (subtreeStepFieldVector roots ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((fixed_subtreeStepFieldVector_independent μ roots hlen
    ).indepSet_of_measurableSet hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply (subtreeStepFieldVector_measurable roots) hB,
    fixed_subtreeStepFieldVector_law μ roots hlen hinj] at h
  exact h

end ProbabilityTheory.BranchingRandomWalk
