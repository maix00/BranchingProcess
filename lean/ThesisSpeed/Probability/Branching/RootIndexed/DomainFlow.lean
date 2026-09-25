import ThesisSpeed.Probability.Genealogy.RootIndexed.Law
import ThesisSpeed.Probability.Branching.AbstractJointSubtrees
import ThesisSpeed.Probability.Genealogy.RootIndexed.Filtration

/-!
# Domain flow and branching property for several initial roots

The coordinate space is `Fin m × TreeNode`.  Thus selected descendants may
belong to different initial roots while still sharing one pre-sampled product
probability space.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

@[instance_reducible] def multiRootStepCoordinateSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (p : Fin m × TreeNode) : MeasurableSpace (FiniteRootBranchingStepField m X) :=
  MeasurableSpace.comap (fun ω => ω p.1 p.2) inferInstance

@[instance_reducible] def multiRootStepPastSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (FiniteRootBranchingStepField m X) :=
  ⨆ p ∈ {p : Fin m × TreeNode | p.2.length < n},
    multiRootStepCoordinateSpace p

@[instance_reducible] def multiRootStepFutureSpace
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    MeasurableSpace (FiniteRootBranchingStepField m X) :=
  ⨆ p ∈ {p : Fin m × TreeNode | n ≤ p.2.length},
    multiRootStepCoordinateSpace p

theorem multiRootStepGenerationSpace_eq_past
    {m : ℕ} {X : Type*} [MeasurableSpace X] (n : ℕ) :
    multiRootStepGenerationSpace (m := m) (X := X) n =
      multiRootStepPastSpace n := by
  apply le_antisymm
  · unfold multiRootStepGenerationSpace
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨i, u, hu, t, ht, rfl⟩
    have hle : multiRootStepCoordinateSpace (X := X) (i, u) ≤
        multiRootStepPastSpace n :=
      le_iSup_of_le (i, u) (le_iSup_of_le hu le_rfl)
    apply hle
    exact ⟨t, ht, rfl⟩
  · apply iSup_le
    intro p
    apply iSup_le
    intro hp
    exact (multiRootStep_measurable (X := X) p.1 p.2 hp).comap_le

theorem multiRootStep_coordinates_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ] :
    iIndep (multiRootStepCoordinateSpace (m := m) (X := X))
      (finiteRootBranchingStepFieldLaw μ m) := by
  have h : iIndepFun
      (fun (p : Fin m × TreeNode) (ω : FiniteRootBranchingStepField m X) =>
        ω p.1 p.2) (finiteRootBranchingStepFieldLaw μ m) := by
    unfold finiteRootBranchingStepFieldLaw
      rootIndexedBranchingStepFieldLaw branchingStepFieldLaw
    simpa using (iIndepFun_uncurry_infinitePi'
      (μ := fun (_ : Fin m) (_ : TreeNode) => μ)
      (X := fun (_ : Fin m) (_ : TreeNode) => id)
      (fun _ _ => measurable_id))
  exact h.iIndep

theorem multiRootStep_past_future_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) :
    Indep (multiRootStepFiltration (m := m) (X := X) n)
      (multiRootStepFutureSpace n) (finiteRootBranchingStepFieldLaw μ m) := by
  have hle : ∀ p : Fin m × TreeNode,
      multiRootStepCoordinateSpace (X := X) p ≤
        (inferInstance : MeasurableSpace (FiniteRootBranchingStepField m X)) := by
    intro p
    have hmeas : Measurable
        (fun ω : FiniteRootBranchingStepField m X => ω p.1 p.2) :=
      (measurable_pi_apply p.2 : Measurable
        (fun field : TreeNode → BranchingStep ℕ X => field p.2)).comp
        (measurable_pi_apply p.1 : Measurable
          (fun ω : FiniteRootBranchingStepField m X => ω p.1))
    exact hmeas.comap_le
  have hdisj : Disjoint
      {p : Fin m × TreeNode | p.2.length < n}
      {p : Fin m × TreeNode | n ≤ p.2.length} := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    change p.2.length < n at hp
    change n ≤ p.2.length at hq
    exact (not_lt_of_ge hq) hp
  rw [show multiRootStepFiltration (m := m) (X := X) n =
      multiRootStepGenerationSpace (m := m) (X := X) n from rfl,
    multiRootStepGenerationSpace_eq_past]
  exact indep_iSup_of_disjoint hle
    (multiRootStep_coordinates_independent μ) hdisj

def multiRootSubtreeStepFieldVector
    {m k : ℕ} {X : Type*}
    (roots : Fin k → Fin m × TreeNode) (step : FiniteRootBranchingStepField m X) :
    Fin k → TreeNode → BranchingStep ℕ X :=
  fun j v => step (roots j).1 ((roots j).2 ++ v)

theorem multiRootBranchingAddresses_injective {m k n : ℕ}
    (roots : Fin k → Fin m × TreeNode)
    (hlen : ∀ j, (roots j).2.length = n)
    (hinj : Function.Injective roots) :
    Function.Injective (fun p : Fin k × TreeNode =>
      ((roots p.1).1, (roots p.1).2 ++ p.2)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hrootIndex : (roots i).1 = (roots j).1 := (Prod.mk.inj h).1
  have hpath : (roots i).2 ++ a = (roots j).2 ++ b := (Prod.mk.inj h).2
  have hp := congrArg (List.take n) hpath
  have hrootPath : (roots i).2 = (roots j).2 := by
    simpa [hlen i, hlen j] using hp
  have hij : i = j := hinj (Prod.ext hrootIndex hrootPath)
  subst j
  exact Prod.ext rfl (List.append_cancel_left hpath)

theorem fixed_multiRootSubtreeStepFieldVector_law
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → Fin m × TreeNode)
    (hlen : ∀ j, (roots j).2.length = n)
    (hinj : Function.Injective roots) :
    (finiteRootBranchingStepFieldLaw μ m).map
        (multiRootSubtreeStepFieldVector roots) =
      Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ) := by
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin m × TreeNode => μ)
    (f := fun p : Fin k × TreeNode =>
      ((roots p.1).1, (roots p.1).2 ++ p.2))
    (multiRootBranchingAddresses_injective roots hlen hinj)
  have hcurrySource := Measure.infinitePi_map_curry
    (μ := fun (_ : Fin m) (_ : TreeNode) => μ)
  have hcurryTarget := Measure.infinitePi_map_curry
    (μ := fun (_ : Fin k) (_ : TreeNode) => μ)
  change (Measure.infinitePi
    (fun _ : Fin m => Measure.infinitePi (fun _ : TreeNode => μ))).map
    (fun ω j v => ω (roots j).1 ((roots j).2 ++ v)) =
      Measure.infinitePi
        (fun _ : Fin k => Measure.infinitePi (fun _ : TreeNode => μ))
  rw [← hcurrySource, ← hcurryTarget, ← hflat]
  rw [Measure.map_map, Measure.map_map]
  · rfl
  · exact (MeasurableEquiv.curry (Fin k) TreeNode
      (BranchingStep ℕ X)).measurable
  · apply measurable_pi_iff.mpr
    intro p
    exact measurable_pi_apply ((roots p.1).1, (roots p.1).2 ++ p.2)
  · apply measurable_pi_iff.mpr
    intro j
    apply measurable_pi_iff.mpr
    intro v
    exact (measurable_pi_apply ((roots j).2 ++ v)).comp
      (measurable_pi_apply (roots j).1)
  · exact (MeasurableEquiv.curry (Fin m) TreeNode
      (BranchingStep ℕ X)).measurable

theorem multiRootSubtreeStepFieldVector_measurable
    {m k : ℕ} {X : Type*} [MeasurableSpace X]
    (roots : Fin k → Fin m × TreeNode) :
    Measurable (multiRootSubtreeStepFieldVector (X := X) roots) := by
  apply measurable_pi_iff.mpr
  intro j
  apply measurable_pi_iff.mpr
  intro v
  exact (measurable_pi_apply ((roots j).2 ++ v)).comp
    (measurable_pi_apply (roots j).1)

theorem multiRootSubtreeStepFieldVector_future_measurable
    {m k n : ℕ} {X : Type*} [MeasurableSpace X]
    (roots : Fin k → Fin m × TreeNode)
    (hlen : ∀ j, (roots j).2.length = n) :
    Measurable[multiRootStepFutureSpace n]
      (multiRootSubtreeStepFieldVector (X := X) roots) := by
  apply (@measurable_pi_iff (FiniteRootBranchingStepField m X) (Fin k)
    (fun _ => TreeNode → BranchingStep ℕ X) (multiRootStepFutureSpace n)
    (fun _ => inferInstance) (multiRootSubtreeStepFieldVector roots)).2
  intro j
  apply (@measurable_pi_iff (FiniteRootBranchingStepField m X) TreeNode
    (fun _ => BranchingStep ℕ X) (multiRootStepFutureSpace n)
    (fun _ => inferInstance)
    (fun ω v => multiRootSubtreeStepFieldVector roots ω j v)).2
  intro v
  let p : Fin m × TreeNode := ((roots j).1, (roots j).2 ++ v)
  have hp : n ≤ p.2.length := by simp [p, hlen j]
  have hle : multiRootStepCoordinateSpace (X := X) p ≤
      multiRootStepFutureSpace n :=
    le_iSup_of_le p (le_iSup_of_le hp le_rfl)
  have hcoord : Measurable[multiRootStepCoordinateSpace (X := X) p]
      (fun ω : FiniteRootBranchingStepField m X => ω p.1 p.2) :=
    Measurable.of_comap_le le_rfl
  exact hcoord.mono hle le_rfl

theorem fixed_multiRootSubtreeStepFieldVector_independent
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → Fin m × TreeNode)
    (hlen : ∀ j, (roots j).2.length = n) :
    Indep (multiRootStepFiltration (m := m) (X := X) n)
      (MeasurableSpace.comap
        (multiRootSubtreeStepFieldVector roots) inferInstance)
      (finiteRootBranchingStepFieldLaw μ m) :=
  indep_of_indep_of_le_right (multiRootStep_past_future_independent μ n)
    (multiRootSubtreeStepFieldVector_future_measurable roots hlen).comap_le

theorem fixed_multiRootSubtreeStepFieldVector_event_factorization
    {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → Fin m × TreeNode)
    (hlen : ∀ j, (roots j).2.length = n)
    (hinj : Function.Injective roots)
    (A : Set (FiniteRootBranchingStepField m X))
    (B : Set (Fin k → TreeNode → BranchingStep ℕ X))
    (hA : MeasurableSet[multiRootStepFiltration (m := m) (X := X) n] A)
    (hB : MeasurableSet B) :
    finiteRootBranchingStepFieldLaw μ m
        (A ∩ multiRootSubtreeStepFieldVector roots ⁻¹' B) =
      finiteRootBranchingStepFieldLaw μ m A *
        (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
  have hB' : MeasurableSet[MeasurableSpace.comap
      (multiRootSubtreeStepFieldVector roots) inferInstance]
      (multiRootSubtreeStepFieldVector roots ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((fixed_multiRootSubtreeStepFieldVector_independent μ roots hlen
    ).indepSet_of_measurableSet hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply
      (multiRootSubtreeStepFieldVector_measurable roots) hB,
    fixed_multiRootSubtreeStepFieldVector_law μ roots hlen hinj] at h
  exact h

end ThesisSpeed
