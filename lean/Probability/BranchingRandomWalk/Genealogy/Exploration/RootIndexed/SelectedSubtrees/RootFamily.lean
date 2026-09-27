import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Filtration
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law
import Mathlib.Probability.Independence.Basic

/-!
# Subtree families in an arbitrary root-indexed field

This is the primary multi-root interface.  The initial-root type `Root`, the
selected-family index `κ`, and the child-slot type `α` are arbitrary.  Product
measures and fixed-coordinate measurability do not require any of them to be
finite or countable.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

def RootIndexed.subtreeStepFieldVector {Root κ α X : Type*}
    (roots : κ → Root × TreeNode α)
    (step : RootIndexed.StepField Root α X) :
    κ → TreeNode α → Step α X :=
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

theorem fixed_RootIndexed.subtreeStepFieldVector_law
    {Root κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {n : ℕ} (roots : κ → Root × TreeNode α)
    (hlen : ∀ i, (roots i).2.length = n)
    (hinj : Function.Injective roots) :
    (RootIndexed.stepFieldLaw (Root := Root) μ).map
        (RootIndexed.subtreeStepFieldVector roots) =
      Measure.infinitePi (fun _ : κ => _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ) := by
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
    Measure.infinitePi
      (fun _ : κ => Measure.infinitePi (fun _ : TreeNode α => μ))
  rw [← hcurrySource, ← hcurryTarget, ← hflat]
  rw [Measure.map_map, Measure.map_map]
  · rfl
  · exact (MeasurableEquiv.curry κ (TreeNode α) (Step α X)).measurable
  · apply measurable_pi_iff.mpr
    intro p
    exact measurable_pi_apply ((roots p.1).1, (roots p.1).2 ++ p.2)
  · exact RootIndexed.subtreeStepFieldVector_measurable roots
  · exact (MeasurableEquiv.curry Root (TreeNode α) (Step α X)).measurable

@[instance_reducible] def RootIndexed.stepCoordinateSpace
    {Root α X : Type*} [MeasurableSpace X]
    (p : Root × TreeNode α) :
    MeasurableSpace (RootIndexed.StepField Root α X) :=
  MeasurableSpace.comap (fun ω => ω p.1 p.2) inferInstance

@[instance_reducible] def RootIndexed.stepFutureSpace
    {Root α X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (RootIndexed.StepField Root α X) :=
  ⨆ p ∈ {p : Root × TreeNode α | n ≤ p.2.length},
    RootIndexed.stepCoordinateSpace p

theorem RootIndexed.step_past_future_independent
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ] (n : ℕ) :
    Indep (RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n)
      (RootIndexed.stepFutureSpace (Root := Root) (α := α) (X := X) n)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
  have hcoord : iIndep (fun p : Root × TreeNode α =>
      RootIndexed.stepCoordinateSpace (X := X) p)
      (RootIndexed.stepFieldLaw (Root := Root) μ) := by
    have h : iIndepFun
        (fun (p : Root × TreeNode α)
          (ω : RootIndexed.StepField Root α X) => ω p.1 p.2)
        (RootIndexed.stepFieldLaw (Root := Root) μ) := by
      unfold RootIndexed.stepFieldLaw _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw
      simpa using (iIndepFun_uncurry_infinitePi'
        (μ := fun (_ : Root) (_ : TreeNode α) => μ)
        (X := fun (_ : Root) (_ : TreeNode α) => id)
        (fun _ _ => measurable_id))
    exact h.iIndep
  have hle : ∀ p : Root × TreeNode α,
      RootIndexed.stepCoordinateSpace (X := X) p ≤
      (inferInstance : MeasurableSpace (RootIndexed.StepField Root α X)) := by
    intro p
    have hm : Measurable
        (fun ω : RootIndexed.StepField Root α X => ω p.1 p.2) :=
      (measurable_pi_apply p.2 : Measurable
        (fun field : TreeNode α → Step α X => field p.2)).comp
        (measurable_pi_apply p.1 : Measurable
          (fun ω : RootIndexed.StepField Root α X => ω p.1))
    exact hm.comap_le
  have hdisj : Disjoint
      {p : Root × TreeNode α | p.2.length < n}
      {p : Root × TreeNode α | n ≤ p.2.length} := by
    apply Set.disjoint_left.mpr
    intro p hp hf
    change p.2.length < n at hp
    change n ≤ p.2.length at hf
    exact (not_lt_of_ge hf) hp
  have hpast : RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n =
      ⨆ p ∈ {p : Root × TreeNode α | p.2.length < n},
        RootIndexed.stepCoordinateSpace (X := X) p := by
    apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      rintro s ⟨r, u, hu, t, ht, rfl⟩
      have hle : RootIndexed.stepCoordinateSpace (X := X) (r, u) ≤
          ⨆ p ∈ {p : Root × TreeNode α | p.2.length < n},
            RootIndexed.stepCoordinateSpace (X := X) p :=
        le_iSup_of_le (r, u) (le_iSup_of_le hu le_rfl)
      apply hle
      exact ⟨t, ht, rfl⟩
    · apply iSup_le
      intro p
      apply iSup_le
      intro hp
      exact (RootIndexed.step_measurable (X := X) p.1 p.2 hp).comap_le
  rw [hpast]
  exact indep_iSup_of_disjoint hle hcoord hdisj

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

theorem fixed_RootIndexed.subtreeStepFieldVector_independent
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

theorem fixed_RootIndexed.subtreeStepFieldVector_event_factorization
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
        (Measure.infinitePi (fun _ : κ => _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ)) B := by
  have hB' : MeasurableSet[MeasurableSpace.comap
      (RootIndexed.subtreeStepFieldVector roots) inferInstance]
      (RootIndexed.subtreeStepFieldVector roots ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((fixed_RootIndexed.subtreeStepFieldVector_independent μ roots hlen
    ).indepSet_of_measurableSet hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply
      (RootIndexed.subtreeStepFieldVector_measurable roots) hB,
    fixed_RootIndexed.subtreeStepFieldVector_law μ roots hlen hinj] at h
  exact h

def RootIndexed.selectedSubtreeStepFieldVector
    {Root κ α X : Type*}
    (chosen : RootIndexed.StepField Root α X → κ → Root × TreeNode α)
    (ω : RootIndexed.StepField Root α X) :
    κ → TreeNode α → Step α X :=
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
        (Measure.infinitePi (fun _ : κ => _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ)) B := by
  let P := RootIndexed.stepFieldLaw (Root := Root) μ
  let Q := Measure.infinitePi (fun _ : κ => _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ)
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
      (Measure.infinitePi (fun _ : κ => _root_.ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ)) B := by
    have h := RootIndexed.selectedSubtreeStepFieldVector_event_factorization
      μ chosen hcount hfiber hdepth hinj Set.univ B (by simp) hB
    simpa using h
  rw [hlaw]
  exact RootIndexed.selectedSubtreeStepFieldVector_event_factorization μ
    chosen hcount hfiber hdepth hinj A B hA hB

end ProbabilityTheory.BranchingRandomWalk
