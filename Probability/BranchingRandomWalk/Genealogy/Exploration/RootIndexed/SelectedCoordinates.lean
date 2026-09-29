import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily

/-!
# Predictably selected coordinate fields

An injective coordinate relabelling whose values lie in the future of a
generation may be chosen measurably from the past.  The resulting complete
field has the product law and is independent of that past.  This extends the
selected-subtree theorem to coordinate maps which may mix several fresh
subtrees inside one output field.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Pull a field back through a sample-dependent complete coordinate map. -/
def RootIndexed.selectedCoordinateField
    {Root NewRoot α X : Type*}
    (chosen : RootIndexed.StepField Root α X →
      NewRoot × TreeNode α → Root × TreeNode α)
    (field : RootIndexed.StepField Root α X) :
    RootIndexed.StepField NewRoot α X :=
  field.reindexCoordinates (chosen field)

/-- A fixed coordinate relabelling into the future is measurable from the
future coordinate space. -/
theorem RootIndexed.StepField.reindexCoordinates_future_measurable
    {Root NewRoot α X : Type*} [MeasurableSpace X] {n : ℕ}
    (f : NewRoot × TreeNode α → Root × TreeNode α)
    (hfuture : ∀ p, n ≤ (f p).2.length) :
    Measurable[RootIndexed.stepFutureSpace
      (Root := Root) (α := α) (X := X) n]
      (RootIndexed.StepField.reindexCoordinates (X := X) f) := by
  apply (@measurable_pi_iff
    (RootIndexed.StepField Root α X) NewRoot
    (fun _ => TreeNode α → Step α X)
    (RootIndexed.stepFutureSpace n) (fun _ => inferInstance)
    (RootIndexed.StepField.reindexCoordinates f)).2
  intro r
  apply (@measurable_pi_iff
    (RootIndexed.StepField Root α X) (TreeNode α)
    (fun _ => Step α X)
    (RootIndexed.stepFutureSpace n) (fun _ => inferInstance)
    (fun field u =>
      RootIndexed.StepField.reindexCoordinates f field r u)).2
  intro u
  let p := f (r, u)
  have hle : RootIndexed.stepCoordinateSpace (X := X) p ≤
      RootIndexed.stepFutureSpace n :=
    le_iSup_of_le p (le_iSup_of_le (hfuture (r, u)) le_rfl)
  exact (Measurable.of_comap_le hle : Measurable[
    RootIndexed.stepFutureSpace n]
      (fun field : RootIndexed.StepField Root α X => field p.1 p.2))

/-- A fixed injective future-coordinate field is independent of the past. -/
theorem RootIndexed.StepField.reindexCoordinates_independent
    {Root NewRoot α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] {n : ℕ}
    (f : NewRoot × TreeNode α → Root × TreeNode α)
    (hfuture : ∀ p, n ≤ (f p).2.length) :
    Indep (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n)
      (MeasurableSpace.comap
        (RootIndexed.StepField.reindexCoordinates f) inferInstance)
      (RootIndexed.stepFieldLaw (Root := Root) μ) :=
  indep_of_indep_of_le_right
    (RootIndexed.step_past_future_independent μ n)
    (RootIndexed.StepField.reindexCoordinates_future_measurable
      f hfuture).comap_le

/-- The sample-dependent coordinate field is measurable when the random map
has countable actual range and past-measurable fibres. -/
theorem RootIndexed.selectedCoordinateField_measurable
    {Root NewRoot α X : Type*} [MeasurableSpace X] {n : ℕ}
    (chosen : RootIndexed.StepField Root α X →
      NewRoot × TreeNode α → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ f, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {field | chosen field = f}) :
    Measurable (RootIndexed.selectedCoordinateField chosen) := by
  let S := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  intro B hB
  have hpre : RootIndexed.selectedCoordinateField chosen ⁻¹' B =
      ⋃ f : S, {field | chosen field = f.1} ∩
        RootIndexed.StepField.reindexCoordinates f.1 ⁻¹' B := by
    ext field
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq, RootIndexed.selectedCoordinateField]
    constructor
    · intro h
      exact ⟨⟨chosen field, Set.mem_range_self field⟩, rfl, h⟩
    · rintro ⟨f, hf, h⟩
      simpa [hf] using h
  rw [hpre]
  apply MeasurableSet.iUnion
  intro f
  exact ((RootIndexed.stepFiltration
    (Root := Root) (α := α) (X := X) |>.le n) _ (hfiber f.1)).inter
      (RootIndexed.StepField.measurable_reindexCoordinates f.1 hB)

/-- One coordinate selected by a predictable, countably ranged coordinate
map is measurable in any later domain flow that already contains the selected
coordinate.  No countability assumption is imposed on either index type. -/
theorem RootIndexed.selectedCoordinate_measurable
    {Root NewRoot α X : Type*} [MeasurableSpace X] {n k : ℕ}
    (chosen : RootIndexed.StepField Root α X →
      NewRoot × TreeNode α → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ f, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {field | chosen field = f})
    (hnk : n ≤ k) (p : NewRoot × TreeNode α)
    (hdepth : ∀ field, (chosen field p).2.length < k) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) k]
      (fun field : RootIndexed.StepField Root α X =>
        field (chosen field p).1 (chosen field p).2) := by
  let S : Set (NewRoot × TreeNode α → Root × TreeNode α) := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  let selected := fun field : RootIndexed.StepField Root α X => chosen field p
  have hselectedCount : (Set.range selected).Countable := by
    apply (hcount.image fun f => f p).mono
    rintro q ⟨field, rfl⟩
    exact ⟨chosen field, Set.mem_range_self field, rfl⟩
  have hselectedFiber : ∀ q, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) k] {field | selected field = q} := by
    intro q
    have hset : {field | selected field = q} =
        ⋃ f : {f : S // f.1 p = q}, {field | chosen field = f.1.1} := by
      ext field
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        exact ⟨⟨⟨chosen field, Set.mem_range_self field⟩, h⟩, rfl⟩
      · rintro ⟨f, hf⟩
        simpa [selected, hf] using f.2
    rw [hset]
    apply MeasurableSet.iUnion
    intro f
    exact (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) |>.mono hnk) _ (hfiber f.1.1)
  exact RootIndexed.selectedStep_measurable selected hselectedFiber hdepth
    hselectedCount

/-- Event factorization for a predictably selected injective coordinate
field. -/
theorem RootIndexed.selectedCoordinateField_event_factorization
    {Root NewRoot α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] {n : ℕ}
    (chosen : RootIndexed.StepField Root α X →
      NewRoot × TreeNode α → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ f, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {field | chosen field = f})
    (hfuture : ∀ field p, n ≤ (chosen field p).2.length)
    (hinj : ∀ field, Function.Injective (chosen field))
    (A : Set (RootIndexed.StepField Root α X))
    (B : Set (RootIndexed.StepField NewRoot α X))
    (hA : MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] A)
    (hB : MeasurableSet B) :
    RootIndexed.stepFieldLaw (Root := Root) μ
        (A ∩ RootIndexed.selectedCoordinateField chosen ⁻¹' B) =
      RootIndexed.stepFieldLaw (Root := Root) μ A *
        RootIndexed.stepFieldLaw (Root := NewRoot) μ B := by
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let Q := RootIndexed.stepFieldLaw (Root := NewRoot) μ
  let S := Set.range chosen
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  let C := fun f : S => A ∩ {field | chosen field = f.1}
  let D := fun f : S => C f ∩
    RootIndexed.StepField.reindexCoordinates f.1 ⁻¹' B
  have hCmeas (f : S) : MeasurableSet (C f) :=
    (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) |>.le n) _
      (hA.inter (hfiber f.1))
  have hDmeas (f : S) : MeasurableSet (D f) :=
    (hCmeas f).inter
      (RootIndexed.StepField.measurable_reindexCoordinates f.1 hB)
  have hCpair : Pairwise (fun f g => Disjoint (C f) (C g)) := by
    intro f g hfg
    apply Set.disjoint_left.mpr
    intro field hf hg
    exact hfg (Subtype.ext (hf.2.symm.trans hg.2))
  have hDpair : Pairwise (fun f g => Disjoint (D f) (D g)) := by
    intro f g hfg
    exact (hCpair hfg).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ f, C f) = A := by
    ext field
    simp only [Set.mem_iUnion, C, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, h, _⟩; exact h
    · intro h
      exact ⟨⟨chosen field, Set.mem_range_self field⟩, h, rfl⟩
  have hDunion : (⋃ f, D f) =
      A ∩ RootIndexed.selectedCoordinateField chosen ⁻¹' B := by
    ext field
    simp only [Set.mem_iUnion, D, C, Set.mem_inter_iff,
      Set.mem_ofPred_eq, Set.mem_preimage,
      RootIndexed.selectedCoordinateField]
    constructor
    · rintro ⟨f, ⟨⟨hAfield, hf⟩, hBfield⟩⟩
      exact ⟨hAfield, by simpa [hf] using hBfield⟩
    · rintro ⟨hAfield, hBfield⟩
      exact ⟨⟨chosen field, Set.mem_range_self field⟩,
        ⟨⟨hAfield, rfl⟩, hBfield⟩⟩
  have hCsum : (∑' f, P (C f)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  have hcell (f : S) : P (D f) = P (C f) * Q B := by
    obtain ⟨field, hfield⟩ := f.2
    have hfuture' : ∀ p, n ≤ (f.1 p).2.length := by
      intro p
      simpa [← hfield] using hfuture field p
    have hinj' : Function.Injective f.1 := by simpa [← hfield] using hinj field
    have hind := RootIndexed.StepField.reindexCoordinates_independent μ f.1 hfuture'
    have hpre : MeasurableSet[MeasurableSpace.comap
        (RootIndexed.StepField.reindexCoordinates f.1) inferInstance]
        (RootIndexed.StepField.reindexCoordinates f.1 ⁻¹' B) :=
      ⟨B, hB, rfl⟩
    have h := (hind.indepSet_of_measurableSet
      (hA.inter (hfiber f.1)) hpre).measure_inter_eq_mul
    rw [← Measure.map_apply
        (RootIndexed.StepField.measurable_reindexCoordinates f.1) hB,
      RootIndexed.stepFieldLaw_reindexCoordinates μ f.1 hinj'] at h
    exact h
  calc
    P (A ∩ RootIndexed.selectedCoordinateField chosen ⁻¹' B) =
        P (⋃ f, D f) := by rw [hDunion]
    _ = ∑' f, P (D f) := measure_iUnion hDpair hDmeas
    _ = ∑' f, P (C f) * Q B := tsum_congr hcell
    _ = (∑' f, P (C f)) * Q B := ENNReal.tsum_mul_right
    _ = P A * Q B := by rw [hCsum]

/-- The predictably selected coordinate field has the complete product law. -/
theorem RootIndexed.selectedCoordinateField_law
    {Root NewRoot α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] {n : ℕ}
    (chosen : RootIndexed.StepField Root α X →
      NewRoot × TreeNode α → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ f, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {field | chosen field = f})
    (hfuture : ∀ field p, n ≤ (chosen field p).2.length)
    (hinj : ∀ field, Function.Injective (chosen field)) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (RootIndexed.selectedCoordinateField chosen) =
      RootIndexed.stepFieldLaw (Root := NewRoot) μ := by
  ext B hB
  rw [Measure.map_apply
    (RootIndexed.selectedCoordinateField_measurable chosen hcount hfiber) hB]
  simpa using RootIndexed.selectedCoordinateField_event_factorization μ
    chosen hcount hfiber hfuture hinj Set.univ B (by simp) hB

/-- The selected coordinate field is independent of the past used to choose
its coordinate map. -/
theorem RootIndexed.selectedCoordinateField_independent
    {Root NewRoot α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] {n : ℕ}
    (chosen : RootIndexed.StepField Root α X →
      NewRoot × TreeNode α → Root × TreeNode α)
    (hcount : (Set.range chosen).Countable)
    (hfiber : ∀ f, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n] {field | chosen field = f})
    (hfuture : ∀ field p, n ≤ (chosen field p).2.length)
    (hinj : ∀ field, Function.Injective (chosen field)) :
    Indep (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n)
      (MeasurableSpace.comap
        (RootIndexed.selectedCoordinateField chosen) inferInstance)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  have hselected := RootIndexed.selectedCoordinateField_measurable
    chosen hcount hfiber
  apply (indep_iff_forall_indepSet
    (RootIndexed.stepFieldLaw (Root := Root) μ)).2
  intro A T hA hT
  obtain ⟨B, hB, rfl⟩ := hT
  apply (indepSet_iff_measure_inter_eq_mul
    ((RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) |>.le n) _ hA)
    (hselected hB) (RootIndexed.stepFieldLaw (Root := Root) μ)).2
  rw [← Measure.map_apply hselected hB,
    RootIndexed.selectedCoordinateField_law μ chosen hcount hfiber
      hfuture hinj]
  exact RootIndexed.selectedCoordinateField_event_factorization μ chosen
    hcount hfiber hfuture hinj A B hA hB

end ProbabilityTheory.BranchingRandomWalk
