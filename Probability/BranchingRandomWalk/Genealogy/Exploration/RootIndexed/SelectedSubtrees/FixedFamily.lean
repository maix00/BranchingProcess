/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Field.Filtration
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.AddressFiltration.PastFuture
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Combinatorics.UlamHarris.Generation
public import Mathlib.Probability.Independence.Basic

/-!
# Subtree families in an arbitrary root-indexed field

The initial-root type `Root`, the selected-family index `κ`, and the child-slot type `α` are
arbitrary. Product measures and fixed-coordinate measurability do not require any of them to be
finite or countable.

## Public declarations

* `RootIndexed.subtreeStepFieldVector` rebases a fixed family of root-address
  pairs.
* `subtreeStepFieldVector_measurable` proves measurability for fixed roots,
  while `subtreeStepFieldVector_measurable_of_measurable_roots` handles a
  random family with countable range and measurable fibers.
* `subtreeStepFieldVector_law` gives the rebased field the full product law.
  `subtreeStepFieldVector_future_measurable` places it in the future of the
  generation-`n` filtration, and `subtreeStepFieldVector_independent` proves
  independence from that flow.
* `subtreeStepFieldVector_event_factorization` gives the corresponding
  product formula for a generation-`n` event and a measurable event of the
  rebased future field.
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

/-- Measurability of a step-field vector rebased at a measurable,
countable-range random family of roots. The proof partitions the domain by
the countable set of root families and uses measurability for each fixed
family. -/
theorem RootIndexed.subtreeStepFieldVector_measurable_of_measurable_roots
    {Root κ α X : Type*} [MeasurableSpace X]
    [MeasurableSpace Root] [MeasurableSpace (RootIndexed.TreeNode Root α)]
    [Countable κ] [MeasurableSingletonClass Root]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root α)]
    (roots : RootIndexed.StepField Root α X → κ → RootIndexed.TreeNode Root α)
    (hroots : Measurable roots)
    (hcount : (Set.range roots).Countable) :
    Measurable (fun ω =>
      RootIndexed.subtreeStepFieldVector (roots ω) ω) := by
  classical
  let S : Set (κ → RootIndexed.TreeNode Root α) := Set.range roots
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  intro B hB
  have hpre :
      (fun ω => RootIndexed.subtreeStepFieldVector (roots ω) ω) ⁻¹' B =
        ⋃ q : S, {ω | roots ω = q.1} ∩
          RootIndexed.subtreeStepFieldVector q.1 ⁻¹' B := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨⟨roots ω, Set.mem_range_self ω⟩, rfl, h⟩
    · rintro ⟨q, hq, h⟩
      simpa [hq] using h
  rw [hpre]
  exact MeasurableSet.iUnion fun q =>
    (hroots (measurableSet_singleton q.1)).inter
      ((RootIndexed.subtreeStepFieldVector_measurable q.1) hB)

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
    (Combinatorics.UlamHarris.RootIndexed.appendAddresses_injective
      roots hlen hinj)
  have hcurrySource := Measure.infinitePi_map_curry
    (μ := fun (_ : Root) (_ : TreeNode α) => μ)
  have hcurryTarget := Measure.infinitePi_map_curry
    (μ := fun (_ : κ) (_ : TreeNode α) => μ)
  change (Measure.infinitePi
    (fun _ : Root => Measure.infinitePi (fun _ : TreeNode α => μ))).map
      (fun ω i v => ω (roots i).1 ((roots i).2 ++ v)) =
    RootIndexed.stepFieldLaw (Root := κ) μ
  unfold RootIndexed.stepFieldLaw
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
