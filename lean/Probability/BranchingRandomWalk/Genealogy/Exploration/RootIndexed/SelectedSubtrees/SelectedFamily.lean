import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily

/-!
# Generation-measurably selected subtree families

A same-generation injective family selected from the revealed generation
produces a fresh root-indexed step field.  The selected field is measurable,
has the full product law, and is independent of the information used to
choose its roots.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

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
  let S : Set (κ → Root × TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  intro B hB
  have hpre :
      RootIndexed.selectedSubtreeStepFieldVector chosen ⁻¹' B =
        ⋃ roots : S,
          {ω | chosen ω = roots.1} ∩
            RootIndexed.subtreeStepFieldVector roots.1 ⁻¹' B := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq, RootIndexed.selectedSubtreeStepFieldVector]
    constructor
    · intro h
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩, rfl, h⟩
    · rintro ⟨roots, hr, h⟩
      simpa [hr] using h
  rw [hpre]
  apply MeasurableSet.iUnion
  intro roots
  exact ((RootIndexed.stepFiltration
    (Root := Root) (α := α) (X := X) |>.le n) _ (hfiber roots.1)).inter
      ((RootIndexed.subtreeStepFieldVector_measurable roots.1) hB)

def RootIndexed.vectorSelectionCell {Root κ α X : Type*}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (A : Set (RootIndexed.StepField Root α X))
    (roots : κ → Root × TreeNode α) :
    Set (RootIndexed.StepField Root α X) :=
  A ∩ {ω | chosen ω = roots}

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
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := κ) μ
  let S : Set (κ → Root × TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  let C := fun roots : S =>
    RootIndexed.vectorSelectionCell chosen A roots.1
  let D := fun roots : S => C roots ∩
    RootIndexed.subtreeStepFieldVector roots.1 ⁻¹' B
  have hCmeas (roots : S) : MeasurableSet (C roots) :=
    (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) |>.le n) _
      (hA.inter (hfiber roots.1))
  have hDmeas (roots : S) : MeasurableSet (D roots) :=
    (hCmeas roots).inter
      ((RootIndexed.subtreeStepFieldVector_measurable roots.1) hB)
  have hCpair : Pairwise (fun r s => Disjoint (C r) (C s)) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    intro ω hcr hcs
    exact hrs (Subtype.ext (hcr.2.symm.trans hcs.2))
  have hDpair : Pairwise (fun r s => Disjoint (D r) (D s)) := by
    intro r s hrs
    exact (hCpair hrs).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ roots, C roots) = A := by
    ext ω
    simp only [Set.mem_iUnion, C, RootIndexed.vectorSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, hAω, _⟩; exact hAω
    · intro hAω
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩, hAω, rfl⟩
  have hDunion : (⋃ roots, D roots) =
      A ∩ RootIndexed.selectedSubtreeStepFieldVector chosen ⁻¹' B := by
    ext ω
    simp only [Set.mem_iUnion, D, C, RootIndexed.vectorSelectionCell,
      Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
      RootIndexed.selectedSubtreeStepFieldVector]
    constructor
    · rintro ⟨roots, ⟨⟨hAω, hr⟩, hBω⟩⟩
      exact ⟨hAω, by simpa [hr] using hBω⟩
    · rintro ⟨hAω, hBω⟩
      exact ⟨⟨chosen ω, Set.mem_range_self ω⟩,
        ⟨⟨hAω, rfl⟩, hBω⟩⟩
  have hCsum : (∑' roots, P (C roots)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  have hcell (roots : S) : P (D roots) = P (C roots) * Q B := by
    obtain ⟨ω, hω⟩ := roots.2
    have hlen : ∀ i, (roots.1 i).2.length = n := by
      intro i
      simpa [← hω] using hdepth ω i
    have hrootsinj : Function.Injective roots.1 := by
      simpa [← hω] using hinj ω
    exact fixed_RootIndexed.subtreeStepFieldVector_event_factorization μ
      roots.1 hlen hrootsinj (C roots) B
      (hA.inter (hfiber roots.1)) hB
  calc
    P (A ∩ RootIndexed.selectedSubtreeStepFieldVector chosen ⁻¹' B) =
        P (⋃ roots, D roots) := by rw [hDunion]
    _ = ∑' roots, P (D roots) := measure_iUnion hDpair hDmeas
    _ = ∑' roots, P (C roots) * Q B := tsum_congr hcell
    _ = (∑' roots, P (C roots)) * Q B := ENNReal.tsum_mul_right
    _ = P A * Q B := by rw [hCsum]

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
