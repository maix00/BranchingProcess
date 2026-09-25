import ThesisSpeed.Probability.Branching.AbstractDomainFlow

/-!
# Joint law of finitely many abstract branching subtrees

Distinct roots at one generation use disjoint coordinates.  Their descendant
step fields therefore have the joint law of independent copies of the full
pre-sampled branching-step field.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def subtreeStepFieldVector {X : Type*} {k : ℕ}
    (roots : Fin k → TreeNode)
    (ω : TreeNode → BranchingStep ℕ X) :
    Fin k → TreeNode → BranchingStep ℕ X :=
  fun i => subtreeStepField (roots i) ω

theorem subtreeStepFieldVector_measurable
    {X : Type*} [MeasurableSpace X] {k : ℕ}
    (roots : Fin k → TreeNode) :
    Measurable (subtreeStepFieldVector (X := X) roots) := by
  apply measurable_pi_iff.mpr
  intro i
  exact subtreeStepField_measurable (roots i)

theorem rootedBranchingAddresses_injective {k n : ℕ}
    (roots : Fin k → TreeNode)
    (hlen : ∀ i, (roots i).length = n)
    (hinj : Function.Injective roots) :
    Function.Injective (fun p : Fin k × TreeNode => roots p.1 ++ p.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hp := congrArg (List.take n) h
  have hroot : roots i = roots j := by
    simpa [hlen i, hlen j] using hp
  have hij : i = j := hinj hroot
  subst j
  exact Prod.ext rfl (List.append_cancel_left h)

theorem fixed_subtreeStepFieldVector_law
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → TreeNode)
    (hlen : ∀ i, (roots i).length = n)
    (hinj : Function.Injective roots) :
    (branchingStepFieldLaw μ).map (subtreeStepFieldVector roots) =
      Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ) := by
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : TreeNode => μ)
    (f := fun p : Fin k × TreeNode => roots p.1 ++ p.2)
    (rootedBranchingAddresses_injective roots hlen hinj)
  have hcurry := Measure.infinitePi_map_curry
    (μ := fun (_ : Fin k) (_ : TreeNode) => μ)
  change (Measure.infinitePi (fun _ : TreeNode => μ)).map
    (fun ω i v => ω (roots i ++ v)) =
      Measure.infinitePi
        (fun _ : Fin k => Measure.infinitePi (fun _ : TreeNode => μ))
  rw [← hcurry, ← hflat]
  rw [Measure.map_map]
  · rfl
  · exact (MeasurableEquiv.curry (Fin k) TreeNode
      (BranchingStep ℕ X)).measurable
  · apply measurable_pi_iff.mpr
    intro p
    exact measurable_pi_apply (roots p.1 ++ p.2)

theorem branchingStepDescendantSpace_le_future
    {X : Type*} [MeasurableSpace X]
    (n : ℕ) (u : TreeNode) (hu : n ≤ u.length) :
    branchingStepDescendantSpace (X := X) u ≤
      branchingStepFutureSpace n := by
  apply iSup_le
  intro v
  have hdepth : n ≤ (u ++ v).length := by simp; omega
  exact le_iSup_of_le (u ++ v) (le_iSup_of_le hdepth le_rfl)

theorem subtreeStepFieldVector_future_measurable
    {X : Type*} [MeasurableSpace X] {k n : ℕ}
    (roots : Fin k → TreeNode) (hlen : ∀ i, (roots i).length = n) :
    Measurable[branchingStepFutureSpace n]
      (subtreeStepFieldVector (X := X) roots) := by
  apply (@measurable_pi_iff
    (TreeNode → BranchingStep ℕ X) (Fin k)
    (fun _ => TreeNode → BranchingStep ℕ X)
    (branchingStepFutureSpace n) (fun _ => inferInstance)
    (subtreeStepFieldVector roots)).2
  intro i
  exact (subtreeStepField_descendant_measurable (X := X) (roots i)).mono
    (branchingStepDescendantSpace_le_future n (roots i) (by rw [hlen i]))
    le_rfl

theorem fixed_subtreeStepFieldVector_independent
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → TreeNode)
    (hlen : ∀ i, (roots i).length = n) :
    Indep (generationFiltration (Mark := BranchingStep ℕ X) n)
      (MeasurableSpace.comap (subtreeStepFieldVector roots) inferInstance)
      (branchingStepFieldLaw μ) :=
  indep_of_indep_of_le_right
    (generation_branchingStepFuture_independent μ n)
    (subtreeStepFieldVector_future_measurable roots hlen).comap_le

theorem fixed_subtreeStepFieldVector_event_factorization
    {X : Type*} [MeasurableSpace X]
    (μ : Measure (BranchingStep ℕ X)) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → TreeNode)
    (hlen : ∀ i, (roots i).length = n)
    (hinj : Function.Injective roots)
    (A : Set (TreeNode → BranchingStep ℕ X))
    (B : Set (Fin k → TreeNode → BranchingStep ℕ X))
    (hA : MeasurableSet[
      generationFiltration (Mark := BranchingStep ℕ X) n] A)
    (hB : MeasurableSet B) :
    branchingStepFieldLaw μ (A ∩ subtreeStepFieldVector roots ⁻¹' B) =
      branchingStepFieldLaw μ A *
        (Measure.infinitePi (fun _ : Fin k => branchingStepFieldLaw μ)) B := by
  have hB' : MeasurableSet[
      MeasurableSpace.comap (subtreeStepFieldVector roots) inferInstance]
      (subtreeStepFieldVector roots ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((fixed_subtreeStepFieldVector_independent μ roots hlen
    ).indepSet_of_measurableSet hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply (subtreeStepFieldVector_measurable roots) hB,
    fixed_subtreeStepFieldVector_law μ roots hlen hinj] at h
  exact h

end ThesisSpeed
