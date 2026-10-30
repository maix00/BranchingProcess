/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily
public import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedCoordinates

/-!
# Generation-measurably selected subtree families

A same-generation injective family selected from the revealed generation
produces a fresh root-indexed step field.  The selected field is measurable,
has the full product law, and is independent of the information used to
choose its roots.
## Public declarations

* `RootIndexed.selectedSubtreeStepFieldVector` rebases a random field at a
  field-measurable family of roots.
* `selectedSubtreeStepFieldVector_measurable` proves measurability when the
  chosen family has countable range and measurable fibers.
* `selectedSubtreeStepFieldVector_event_factorization` proves that for an
  event `A` observable by generation `n` and a measurable future event `B`,
  the probability of `A` together with `B` for the selected fresh field is
  `P(A) * P_field(B)`.
* `selectedSubtreeStepFieldVector_law` gives the selected field the full
  product law; `selectedSubtreeStepFieldVector_law_comp` transports this law
  through a measurable realization of the input field.
  `selectedSubtreeStepFieldVector_independent` states its independence from
  the generation-`n` filtration.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

private def RootIndexed.subtreeCoordinateMapOfRoots
    {Root κ α : Type*} (roots : κ → Root × TreeNode α) :
    κ × TreeNode α → Root × TreeNode α :=
  fun p => ((roots p.1).1, (roots p.1).2 ++ p.2)

private def RootIndexed.selectedSubtreeCoordinateMap
    {Root κ α X : Type*}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α) :
    RootIndexed.StepField Root α X → κ × TreeNode α → Root × TreeNode α :=
  fun field => RootIndexed.subtreeCoordinateMapOfRoots (chosen field)

private theorem RootIndexed.selectedSubtreeCoordinateMap_range_countable
    {Root κ α X : Type*}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable) :
    (Set.range (RootIndexed.selectedSubtreeCoordinateMap chosen)).Countable := by
  have hrange : Set.range (RootIndexed.selectedSubtreeCoordinateMap chosen) =
      (RootIndexed.subtreeCoordinateMapOfRoots (α := α)) '' Set.range chosen := by
    ext f
    simp [RootIndexed.selectedSubtreeCoordinateMap]
  rw [hrange]
  exact hcount.image (RootIndexed.subtreeCoordinateMapOfRoots (α := α))

private theorem RootIndexed.selectedSubtreeCoordinateMap_fiber_measurable
    {Root κ α X : Type*} [MeasurableSpace X] {n : ℕ}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | chosen ω = roots})
    (f : κ × TreeNode α → Root × TreeNode α) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      {ω | RootIndexed.selectedSubtreeCoordinateMap chosen ω = f} := by
  let S : Set (κ → Root × TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  let T : Set S := {roots | RootIndexed.subtreeCoordinateMapOfRoots roots.1 = f}
  have hset : {ω | RootIndexed.selectedSubtreeCoordinateMap chosen ω = f} =
      ⋃ roots : T, {ω | chosen ω = roots.1.1} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · intro h
      refine ⟨⟨⟨chosen ω, Set.mem_range_self ω⟩, ?_⟩, rfl⟩
      change RootIndexed.subtreeCoordinateMapOfRoots (chosen ω) = f
      simpa [RootIndexed.selectedSubtreeCoordinateMap] using h
    · rintro ⟨roots, hroots⟩
      have hmap :
          RootIndexed.subtreeCoordinateMapOfRoots roots.1.1 = f := roots.2
      change RootIndexed.subtreeCoordinateMapOfRoots (chosen ω) = f
      rw [hroots]
      exact hmap
  rw [hset]
  exact MeasurableSet.iUnion fun roots => hfiber roots.1.1

def RootIndexed.selectedSubtreeStepFieldVector
    {Root κ α X : Type*}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (ω : RootIndexed.StepField Root α X) :
    RootIndexed.StepField κ α X :=
  RootIndexed.subtreeStepFieldVector (chosen ω) ω

/-- Measurability of a selected subtree family is proved by partitioning over
the countable range of the selected labelled family.  Neither the ambient root
type, the family index, nor the offspring-slot type is assumed countable. -/
theorem RootIndexed.selectedSubtreeStepFieldVector_measurable
    {Root κ α X : Type*} [MeasurableSpace X] {n : ℕ}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | chosen ω = roots}) :
    Measurable (RootIndexed.selectedSubtreeStepFieldVector chosen) := by
  change Measurable
    (RootIndexed.selectedCoordinateField
      (RootIndexed.selectedSubtreeCoordinateMap chosen))
  exact RootIndexed.selectedCoordinateField_measurable
    (RootIndexed.selectedSubtreeCoordinateMap chosen)
    (RootIndexed.selectedSubtreeCoordinateMap_range_countable chosen hcount)
    (RootIndexed.selectedSubtreeCoordinateMap_fiber_measurable
      chosen hcount hfiber)

theorem RootIndexed.selectedSubtreeStepFieldVector_event_factorization
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).2.length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω))
    (A : Set (RootIndexed.StepField Root α X))
    (B : Set (κ → TreeNode α → Step α X))
    (hA : MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] A)
    (hB : MeasurableSet B) :
    RootIndexed.stepFieldLaw (Root := Root) μ
        (A ∩ RootIndexed.selectedSubtreeStepFieldVector chosen ⁻¹' B) =
      RootIndexed.stepFieldLaw (Root := Root) μ A *
        RootIndexed.stepFieldLaw (Root := κ) μ B := by
  have hfuture : ∀ field p,
      n ≤ (RootIndexed.selectedSubtreeCoordinateMap chosen field p).2.length := by
    intro field p
    simp [RootIndexed.selectedSubtreeCoordinateMap,
      RootIndexed.subtreeCoordinateMapOfRoots, hdepth field p.1]
  have hmapInjective : ∀ field,
      Function.Injective (RootIndexed.selectedSubtreeCoordinateMap chosen field) := by
    intro field
    exact Combinatorics.UlamHarris.RootIndexed.appendAddresses_injective
      (chosen field) (hdepth field) (hinj field)
  have hfield : RootIndexed.selectedSubtreeStepFieldVector chosen =
      RootIndexed.selectedCoordinateField
        (RootIndexed.selectedSubtreeCoordinateMap chosen) := by
    funext field
    rfl
  rw [hfield]
  exact RootIndexed.selectedCoordinateField_event_factorization μ
    (RootIndexed.selectedSubtreeCoordinateMap chosen)
    (RootIndexed.selectedSubtreeCoordinateMap_range_countable chosen hcount)
    (RootIndexed.selectedSubtreeCoordinateMap_fiber_measurable
      chosen hcount hfiber)
    hfuture hmapInjective A B hA hB

/-- A generation-measurably selected injective family of same-generation
roots is itself a complete root-indexed i.i.d. step field.  This is the
adaptive counterpart of `RootIndexed.stepFieldLaw_reindexCoordinates`: the
chosen coordinate blocks may depend on the already exposed generation. -/
theorem RootIndexed.selectedSubtreeStepFieldVector_law
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).2.length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω)) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (RootIndexed.selectedSubtreeStepFieldVector chosen) =
      RootIndexed.stepFieldLaw (Root := κ) μ := by
  ext B hB
  rw [Measure.map_apply
    (RootIndexed.selectedSubtreeStepFieldVector_measurable
      chosen hcount hfiber) hB]
  have h := RootIndexed.selectedSubtreeStepFieldVector_event_factorization
    μ chosen hcount hfiber hdepth hinj Set.univ B (by simp) hB
  simpa using h

/-- The adaptive fresh-field law composes with any measurable realization of
the input product field.  This is the induction interface for successive
restart stages: a stage only needs the preceding field's law, rather than its
particular underlying sample space. -/
theorem RootIndexed.selectedSubtreeStepFieldVector_law_comp
    {Ω Root κ α X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ}
    (field : Ω → RootIndexed.StepField Root α X)
    (hfield : Measurable field)
    (hfieldLaw : P.map field = RootIndexed.stepFieldLaw (Root := Root) μ)
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).2.length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω)) :
    P.map (RootIndexed.selectedSubtreeStepFieldVector chosen ∘ field) =
      RootIndexed.stepFieldLaw (Root := κ) μ := by
  have hselected := RootIndexed.selectedSubtreeStepFieldVector_measurable
    chosen hcount hfiber
  rw [← Measure.map_map hselected hfield, hfieldLaw,
    RootIndexed.selectedSubtreeStepFieldVector_law
      μ chosen hcount hfiber hdepth hinj]

theorem RootIndexed.selectedSubtreeStepFieldVector_independent
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {ω | chosen ω = roots})
    (hdepth : ∀ ω i, (chosen ω i).2.length = n)
    (hinj : ∀ ω, Function.Injective (chosen ω)) :
    Indep (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n)
      (MeasurableSpace.comap
        (RootIndexed.selectedSubtreeStepFieldVector chosen) inferInstance)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  have hselected := RootIndexed.selectedSubtreeStepFieldVector_measurable
    chosen hcount hfiber
  apply (indep_iff_forall_indepSet
    (RootIndexed.stepFieldLaw (Root := Root) μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    ((RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) |>.le n) _ hA)
    (hselected hB) (RootIndexed.stepFieldLaw (Root := Root) μ)).2
  have hlaw : RootIndexed.stepFieldLaw (Root := Root) μ
      (RootIndexed.selectedSubtreeStepFieldVector chosen ⁻¹' B) =
      RootIndexed.stepFieldLaw (Root := κ) μ B := by
    rw [← Measure.map_apply
      (RootIndexed.selectedSubtreeStepFieldVector_measurable
        chosen hcount hfiber) hB,
      RootIndexed.selectedSubtreeStepFieldVector_law
        μ chosen hcount hfiber hdepth hinj]
  rw [hlaw]
  exact RootIndexed.selectedSubtreeStepFieldVector_event_factorization μ
    chosen hcount hfiber hdepth hinj A B hA hB

end ProbabilityTheory.BranchingRandomWalk

end
