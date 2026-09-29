import Probability.BranchingRandomWalk.Genealogy.RootIndexed.GenerationDecomposition
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.SelectedFamily
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedCoordinates

/-!
# Predictable pasting of descendant fields

At generation `n`, choose an injective family of depth-`n` roots using only
the coordinates strictly before `n`.  Glue their descendant fields onto the
past of the right copy of a two-copy product field.  The result has the
original root-indexed product law.

Countability is required only for the actual range of the random family of
chosen roots, which is the condition used to form measurable unions over its
fibres.  Roots, family indices, and offspring slots remain arbitrary.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- The past of the right copy in a two-copy field. -/
def RootIndexed.StepField.rightPast
    {Root α X : Type*} (n : ℕ)
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.Past Root α X n :=
  (field.reindex Sum.inr).past n

/-- The right-copy past is measurable in the joint generation domain flow. -/
theorem RootIndexed.StepField.rightPast_measurable
    {Root α X : Type*} [MeasurableSpace X] (n : ℕ) :
    @Measurable
      (RootIndexed.StepField (Root ⊕ Root) α X)
      (RootIndexed.Past Root α X n)
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) n) inferInstance
      (RootIndexed.StepField.rightPast
        (Root := Root) (α := α) (X := X) n) := by
  apply (@measurable_pi_iff
    (RootIndexed.StepField (Root ⊕ Root) α X)
    {q : RootIndexed.TreeNode Root α // q.2.length < n}
    (fun _ => Step α X)
    (RootIndexed.stepFiltration n) (fun _ => inferInstance)
    (RootIndexed.StepField.rightPast n)).2
  intro q
  exact RootIndexed.step_measurable (Sum.inr q.1.1) q.1.2 q.2

/-- Glue a predictably selected family of fresh descendant fields onto the
past of the fallback (right) copy. -/
def RootIndexed.StepField.splice
    {Root α X : Type*} (n : ℕ)
    (chosen : RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.Generation Root α n → (Root ⊕ Root) × TreeNode α)
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.StepField Root α X :=
  RootIndexed.StepField.glue n (field.rightPast n)
    (RootIndexed.selectedSubtreeStepFieldVector chosen field)

/-- The deterministic right-copy generation family. -/
def RootIndexed.rightGenerationRoots
    {Root α : Type*} (n : ℕ) :
    RootIndexed.Generation Root α n → (Root ⊕ Root) × TreeNode α :=
  fun q => (Sum.inr q.1.1, q.1.2)

theorem RootIndexed.rightGenerationRoots_injective
    {Root α : Type*} (n : ℕ) :
    Function.Injective
      (RootIndexed.rightGenerationRoots (Root := Root) (α := α) n) := by
  intro p q h
  apply Subtype.ext
  exact Prod.ext (Sum.inr.inj (Prod.mk.inj h).1) (Prod.mk.inj h).2

@[simp] theorem RootIndexed.rightGenerationRoots_depth
    {Root α : Type*} (n : ℕ) (q : RootIndexed.Generation Root α n) :
    (RootIndexed.rightGenerationRoots n q).2.length = n :=
  q.2

/-- Gluing the canonical right-copy generation family recovers the complete
right field. -/
theorem RootIndexed.StepField.splice_right
    {Root α X : Type*} (n : ℕ)
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.StepField.glue n (field.rightPast n)
        (RootIndexed.subtreeStepFieldVector
          (RootIndexed.rightGenerationRoots n) field) =
      field.reindex Sum.inr := by
  change RootIndexed.StepField.glue n
      ((field.reindex Sum.inr).past n)
      (RootIndexed.subtreeStepFieldVector
        (RootIndexed.generationRoots n) (field.reindex Sum.inr)) =
    field.reindex Sum.inr
  exact RootIndexed.StepField.glue_past_subtrees n
    (field.reindex Sum.inr)

/-- Glue fresh selected descendant fields onto an arbitrary transformed past.
The past transformation may depend on all information before `n`; its only
distributional requirement is to have the same marginal as the fallback
past.  This is the induction interface for recursive couplings. -/
theorem RootIndexed.stepFieldLaw_glueSelected
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ)
    (past : RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.Past Root α X n)
    (hpast : Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n] past)
    (hpastLaw : (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map past =
      (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.StepField.rightPast n))
    (chosen : RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.Generation Root α n → (Root ⊕ Root) × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
        {field | chosen field = roots})
    (hdepth : ∀ field i, (chosen field i).2.length = n)
    (hinj : ∀ field, Function.Injective (chosen field)) :
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (fun field => RootIndexed.StepField.glue n (past field)
          (RootIndexed.selectedSubtreeStepFieldVector chosen field)) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let A := past
  let A₀ := RootIndexed.StepField.rightPast
    (Root := Root) (α := α) (X := X) n
  let B := RootIndexed.selectedSubtreeStepFieldVector chosen
  let B₀ : RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField (RootIndexed.Generation Root α n) α X :=
    RootIndexed.subtreeStepFieldVector
      (RootIndexed.rightGenerationRoots (Root := Root) (α := α) n)
  let glue := Function.uncurry
    (RootIndexed.StepField.glue (Root := Root) (α := α) (X := X) n)
  have hA : Measurable A := hpast.mono
    (RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) le_rfl
  have hA₀ : Measurable A₀ :=
    (RootIndexed.StepField.rightPast_measurable n).mono
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) le_rfl
  have hB : Measurable B :=
    RootIndexed.selectedSubtreeStepFieldVector_measurable chosen hcount hfiber
  have hB₀ : Measurable B₀ :=
    RootIndexed.subtreeStepFieldVector_measurable
      (RootIndexed.rightGenerationRoots n)
  have hBlaw : P.map B = RootIndexed.stepFieldLaw
      (Root := RootIndexed.Generation Root α n) μ :=
    RootIndexed.selectedSubtreeStepFieldVector_law μ chosen hcount hfiber
      hdepth hinj
  have hB₀law : P.map B₀ = RootIndexed.stepFieldLaw
      (Root := RootIndexed.Generation Root α n) μ :=
    RootIndexed.subtreeStepFieldVector_law μ
      (RootIndexed.rightGenerationRoots n)
      (RootIndexed.rightGenerationRoots_depth n)
      (RootIndexed.rightGenerationRoots_injective n)
  have hiB : A ⟂ᵢ[P] B := by
    show Indep (MeasurableSpace.comap A inferInstance)
      (MeasurableSpace.comap B inferInstance) P
    exact indep_of_indep_of_le_left
      (RootIndexed.selectedSubtreeStepFieldVector_independent μ chosen
        hcount hfiber hdepth hinj)
      hpast.comap_le
  have hiB₀ : A₀ ⟂ᵢ[P] B₀ := by
    show Indep (MeasurableSpace.comap A₀ inferInstance)
      (MeasurableSpace.comap B₀ inferInstance) P
    exact indep_of_indep_of_le_left
      (RootIndexed.subtreeStepFieldVector_independent μ
        (RootIndexed.rightGenerationRoots n)
        (RootIndexed.rightGenerationRoots_depth n))
      (RootIndexed.StepField.rightPast_measurable n).comap_le
  have hpairs : P.map (fun field => (A field, B field)) =
      P.map (fun field => (A₀ field, B₀ field)) := by
    rw [hiB.map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable,
      hiB₀.map_prod_eq_prod_map_map hA₀.aemeasurable hB₀.aemeasurable,
      hBlaw, hB₀law, hpastLaw]
  calc
    P.map (fun field => RootIndexed.StepField.glue n (past field)
        (RootIndexed.selectedSubtreeStepFieldVector chosen field)) =
        (P.map fun field => (A field, B field)).map glue := by
      rw [Measure.map_map]
      · rfl
      · exact RootIndexed.StepField.glue_measurable n
      · exact hA.prodMk hB
    _ = (P.map fun field => (A₀ field, B₀ field)).map glue := by rw [hpairs]
    _ = P.map (RootIndexed.StepField.reindex Sum.inr) := by
      rw [Measure.map_map]
      · congr 1
        funext field
        exact RootIndexed.StepField.splice_right n field
      · exact RootIndexed.StepField.glue_measurable n
      · exact hA₀.prodMk hB₀
    _ = RootIndexed.stepFieldLaw (Root := Root) μ := by
      exact RootIndexed.stepFieldLaw_reindex μ Sum.inr Sum.inr_injective

/-- Coordinate-level version of `stepFieldLaw_glueSelected`.  Each output
descendant field may mix arbitrary fresh source coordinates, provided the
complete random coordinate map is injective and chosen from the past. -/
theorem RootIndexed.stepFieldLaw_glueCoordinates
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ)
    (past : RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.Past Root α X n)
    (hpast : Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n] past)
    (hpastLaw : (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map past =
      (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.StepField.rightPast n))
    (chosen : RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.Generation Root α n × TreeNode α →
        (Root ⊕ Root) × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ f, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
        {field | chosen field = f})
    (hfuture : ∀ field p, n ≤ (chosen field p).2.length)
    (hinj : ∀ field, Function.Injective (chosen field)) :
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (fun field => RootIndexed.StepField.glue n (past field)
          (RootIndexed.selectedCoordinateField chosen field)) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let A := past
  let A₀ := RootIndexed.StepField.rightPast
    (Root := Root) (α := α) (X := X) n
  let B := RootIndexed.selectedCoordinateField chosen
  let B₀ : RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField (RootIndexed.Generation Root α n) α X :=
    RootIndexed.subtreeStepFieldVector
      (RootIndexed.rightGenerationRoots (Root := Root) (α := α) n)
  let glue := Function.uncurry
    (RootIndexed.StepField.glue (Root := Root) (α := α) (X := X) n)
  have hA : Measurable A := hpast.mono
    (RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) le_rfl
  have hA₀ : Measurable A₀ :=
    (RootIndexed.StepField.rightPast_measurable n).mono
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) le_rfl
  have hB : Measurable B :=
    RootIndexed.selectedCoordinateField_measurable chosen hcount hfiber
  have hB₀ : Measurable B₀ :=
    RootIndexed.subtreeStepFieldVector_measurable
      (RootIndexed.rightGenerationRoots n)
  have hBlaw : P.map B = RootIndexed.stepFieldLaw
      (Root := RootIndexed.Generation Root α n) μ :=
    RootIndexed.selectedCoordinateField_law μ chosen hcount hfiber
      hfuture hinj
  have hB₀law : P.map B₀ = RootIndexed.stepFieldLaw
      (Root := RootIndexed.Generation Root α n) μ :=
    RootIndexed.subtreeStepFieldVector_law μ
      (RootIndexed.rightGenerationRoots n)
      (RootIndexed.rightGenerationRoots_depth n)
      (RootIndexed.rightGenerationRoots_injective n)
  have hiB : A ⟂ᵢ[P] B := by
    show Indep (MeasurableSpace.comap A inferInstance)
      (MeasurableSpace.comap B inferInstance) P
    exact indep_of_indep_of_le_left
      (RootIndexed.selectedCoordinateField_independent μ chosen
        hcount hfiber hfuture hinj) hpast.comap_le
  have hiB₀ : A₀ ⟂ᵢ[P] B₀ := by
    show Indep (MeasurableSpace.comap A₀ inferInstance)
      (MeasurableSpace.comap B₀ inferInstance) P
    exact indep_of_indep_of_le_left
      (RootIndexed.subtreeStepFieldVector_independent μ
        (RootIndexed.rightGenerationRoots n)
        (RootIndexed.rightGenerationRoots_depth n))
      (RootIndexed.StepField.rightPast_measurable n).comap_le
  have hpairs : P.map (fun field => (A field, B field)) =
      P.map (fun field => (A₀ field, B₀ field)) := by
    rw [hiB.map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable,
      hiB₀.map_prod_eq_prod_map_map hA₀.aemeasurable hB₀.aemeasurable,
      hBlaw, hB₀law, hpastLaw]
  calc
    P.map (fun field => RootIndexed.StepField.glue n (past field)
        (RootIndexed.selectedCoordinateField chosen field)) =
        (P.map fun field => (A field, B field)).map glue := by
      rw [Measure.map_map]
      · rfl
      · exact RootIndexed.StepField.glue_measurable n
      · exact hA.prodMk hB
    _ = (P.map fun field => (A₀ field, B₀ field)).map glue := by rw [hpairs]
    _ = P.map (RootIndexed.StepField.reindex Sum.inr) := by
      rw [Measure.map_map]
      · congr 1
        funext field
        exact RootIndexed.StepField.splice_right n field
      · exact RootIndexed.StepField.glue_measurable n
      · exact hA₀.prodMk hB₀
    _ = RootIndexed.stepFieldLaw (Root := Root) μ := by
      exact RootIndexed.stepFieldLaw_reindex μ Sum.inr Sum.inr_injective

/-- A generation-predictable injective selection of fresh descendant fields
can be spliced onto the fallback past without changing the complete product
law. -/
theorem RootIndexed.stepFieldLaw_splice
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (n : ℕ)
    (chosen : RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.Generation Root α n → (Root ⊕ Root) × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
        {field | chosen field = roots})
    (hdepth : ∀ field i, (chosen field i).2.length = n)
    (hinj : ∀ field, Function.Injective (chosen field)) :
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.StepField.splice n chosen) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  exact RootIndexed.stepFieldLaw_glueSelected μ n
    (RootIndexed.StepField.rightPast n)
    (RootIndexed.StepField.rightPast_measurable n) rfl
    chosen hcount hfiber hdepth hinj

end ProbabilityTheory.BranchingRandomWalk
