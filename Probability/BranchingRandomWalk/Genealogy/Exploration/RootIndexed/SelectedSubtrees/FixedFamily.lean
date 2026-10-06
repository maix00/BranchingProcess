/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Filtration
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.DomainFlow.Space
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law
public import Mathlib.Probability.Independence.Basic

/-!
# Subtree families in an arbitrary root-indexed field

This is the primary multi-root interface.  The initial-root type `Root`, the
selected-family index `κ`, and the child-slot type `α` are arbitrary.  Product
measures and fixed-coordinate measurability do not require any of them to be
finite or countable.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

def RootIndexed.subtreeStepFieldVector {Root κ α X : Type*}
    (roots : κ → Root × TreeNode α)
    (step : RootIndexed.StepField Root α X) :
    RootIndexed.StepField κ α X :=
  fun i v => step (roots i).1 ((roots i).2 ++ v)

theorem RootIndexed.branchingAddresses_injective
    {Root κ α : Type*} {n : ℕ}
    (roots : κ → Root × TreeNode α)
    (hlen : ∀ i, (roots i).2.length = n)
    (hinj : Function.Injective roots) :
    Function.Injective (fun p : κ × TreeNode α =>
      ((roots p.1).1, (roots p.1).2 ++ p.2)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hr : (roots i).1 = (roots j).1 := (Prod.mk.inj h).1
  have hp : (roots i).2 ++ a = (roots j).2 ++ b := (Prod.mk.inj h).2
  have hpref := congrArg (List.take n) hp
  have hpath : (roots i).2 = (roots j).2 := by
    simpa [hlen i, hlen j] using hpref
  have hij : i = j := hinj (Prod.ext hr hpath)
  subst j
  exact Prod.ext rfl (List.append_cancel_left hp)

theorem RootIndexed.subtreeStepFieldVector_measurable
    {Root κ α X : Type*} [MeasurableSpace X]
    (roots : κ → Root × TreeNode α) :
    Measurable (RootIndexed.subtreeStepFieldVector (X := X) roots) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro v
  exact (measurable_pi_apply ((roots i).2 ++ v)).comp
    (measurable_pi_apply (roots i).1)

theorem RootIndexed.subtreeStepFieldVector_law
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ} (roots : κ → Root × TreeNode α)
    (hlen : ∀ i, (roots i).2.length = n)
    (hinj : Function.Injective roots) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (RootIndexed.subtreeStepFieldVector roots) =
      RootIndexed.stepFieldLaw (Root := κ) μ := by
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Root × TreeNode α => μ)
    (f := fun p : κ × TreeNode α =>
      ((roots p.1).1, (roots p.1).2 ++ p.2))
    (RootIndexed.branchingAddresses_injective roots hlen hinj)
  have hcurrySource := Measure.infinitePi_map_curry
    (μ := fun (_ : Root) (_ : TreeNode α) => μ)
  have hcurryTarget := Measure.infinitePi_map_curry
    (μ := fun (_ : κ) (_ : TreeNode α) => μ)
  change (Measure.infinitePi
    (fun _ : Root => Measure.infinitePi (fun _ : TreeNode α => μ))).map
      (fun ω i v => ω (roots i).1 ((roots i).2 ++ v)) =
    RootIndexed.stepFieldLaw (Root := κ) μ
  unfold RootIndexed.stepFieldLaw
    _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
    _root_.ProbabilityTheory.BranchingProcess.offspringFieldLaw
  rw [← hcurrySource, ← hcurryTarget, ← hflat]
  rw [Measure.map_map, Measure.map_map]
  · rfl
  · exact (MeasurableEquiv.curry κ (TreeNode α) (Step α X)).measurable
  · apply measurable_pi_iff.mpr
    intro p
    exact measurable_pi_apply ((roots p.1).1, (roots p.1).2 ++ p.2)
  · exact RootIndexed.subtreeStepFieldVector_measurable roots
  · exact (MeasurableEquiv.curry Root (TreeNode α) (Step α X)).measurable

theorem RootIndexed.subtreeStepFieldVector_future_measurable
    {Root κ α X : Type*} [MeasurableSpace X] {n : ℕ}
    (roots : κ → Root × TreeNode α)
    (hlen : ∀ i, (roots i).2.length = n) :
    Measurable[RootIndexed.stepFutureSpace
      (Root := Root) (α := α) (X := X) n]
      (RootIndexed.subtreeStepFieldVector (X := X) roots) := by
  apply (@measurable_pi_iff
    (RootIndexed.StepField Root α X) κ
    (fun _ => TreeNode α → Step α X)
    (RootIndexed.stepFutureSpace n) (fun _ => inferInstance)
    (RootIndexed.subtreeStepFieldVector roots)).2
  intro i
  apply (@measurable_pi_iff
    (RootIndexed.StepField Root α X) (TreeNode α)
    (fun _ => Step α X)
    (RootIndexed.stepFutureSpace n) (fun _ => inferInstance)
    (fun ω v => RootIndexed.subtreeStepFieldVector roots ω i v)).2
  intro v
  let p : Root × TreeNode α := ((roots i).1, (roots i).2 ++ v)
  have hp : n ≤ p.2.length := by simp [p, hlen i]
  have hle : RootIndexed.stepCoordinateSpace (X := X) p ≤
      RootIndexed.stepFutureSpace n :=
    le_iSup_of_le p (le_iSup_of_le hp le_rfl)
  have hm : Measurable[RootIndexed.stepCoordinateSpace (X := X) p]
      (fun ω : RootIndexed.StepField Root α X => ω p.1 p.2) :=
    Measurable.of_comap_le le_rfl
  exact hm.mono hle le_rfl

theorem RootIndexed.subtreeStepFieldVector_independent
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ} (roots : κ → Root × TreeNode α)
    (hlen : ∀ i, (roots i).2.length = n) :
    Indep (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n)
      (MeasurableSpace.comap
        (RootIndexed.subtreeStepFieldVector roots) inferInstance)
      (RootIndexed.stepFieldLaw (Root := Root) μ) :=
  indep_of_indep_of_le_right
    (RootIndexed.step_past_future_independent μ n)
    (RootIndexed.subtreeStepFieldVector_future_measurable roots hlen).comap_le

theorem RootIndexed.subtreeStepFieldVector_event_factorization
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ} (roots : κ → Root × TreeNode α)
    (hlen : ∀ i, (roots i).2.length = n)
    (hinj : Function.Injective roots)
    (A : Set (RootIndexed.StepField Root α X))
    (B : Set (κ → TreeNode α → Step α X))
    (hA : MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] A)
    (hB : MeasurableSet B) :
    RootIndexed.stepFieldLaw (Root := Root) μ
        (A ∩ RootIndexed.subtreeStepFieldVector roots ⁻¹' B) =
      RootIndexed.stepFieldLaw (Root := Root) μ A *
        RootIndexed.stepFieldLaw (Root := κ) μ B := by
  have hB' : MeasurableSet[MeasurableSpace.comap
      (RootIndexed.subtreeStepFieldVector roots) inferInstance]
      (RootIndexed.subtreeStepFieldVector roots ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((RootIndexed.subtreeStepFieldVector_independent μ roots hlen
    ).indepSet_of_measurableSet hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply
      (RootIndexed.subtreeStepFieldVector_measurable roots) hB,
    RootIndexed.subtreeStepFieldVector_law μ roots hlen hinj] at h
  exact h

end ProbabilityTheory.BranchingRandomWalk
