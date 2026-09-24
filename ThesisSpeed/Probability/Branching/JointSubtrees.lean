import ThesisSpeed.Probability.Branching.RandomSubtree

/-!
# Joint law of finitely many deterministic subtrees

Distinct roots at the same generation have disjoint Ulam--Harris address
sets. The corresponding finite vector of subtrees is therefore an infinite
product of independent copies of the original marked tree.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

def subtreeVector {k : ℕ} (roots : Fin k → TreeNode)
    (ω : MarkedTree OffspringMark) : Fin k → MarkedTree OffspringMark :=
  fun i => subtreeMarks (roots i) ω

theorem subtreeVector_measurable {k : ℕ}
    (roots : Fin k → TreeNode) :
    Measurable (subtreeVector roots) := by
  apply measurable_pi_iff.mpr
  intro i
  exact subtreeMarks_measurable (roots i)

theorem rooted_addresses_injective {k n : ℕ}
    (roots : Fin k → TreeNode)
    (hlen : ∀ i, (roots i).length = n)
    (hinj : Function.Injective roots) :
    Function.Injective
      (fun p : Fin k × TreeNode => roots p.1 ++ p.2) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hp := congrArg (List.take n) h
  have hroot : roots i = roots j := by
    simpa [hlen i, hlen j] using hp
  have hij : i = j := hinj hroot
  subst j
  have hab : a = b := List.append_cancel_left h
  exact Prod.ext rfl hab

theorem fixed_subtreeVector_law
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → TreeNode)
    (hlen : ∀ i, (roots i).length = n)
    (hinj : Function.Injective roots) :
    (iidMarkedTreeLaw μ).map (subtreeVector roots) =
      Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ) := by
  have hflat := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : TreeNode => μ)
    (f := fun p : Fin k × TreeNode => roots p.1 ++ p.2)
    (rooted_addresses_injective roots hlen hinj)
  have hcurry := Measure.infinitePi_map_curry
    (μ := fun (_ : Fin k) (_ : TreeNode) => μ)
  change (Measure.infinitePi (fun _ : TreeNode => μ)).map
    (fun ω i v => ω (roots i ++ v)) =
      Measure.infinitePi
        (fun _ : Fin k => Measure.infinitePi (fun _ : TreeNode => μ))
  rw [← hcurry, ← hflat]
  rw [Measure.map_map]
  · rfl
  · exact (MeasurableEquiv.curry (Fin k) TreeNode OffspringMark).measurable
  · apply measurable_pi_iff.mpr
    intro p
    exact measurable_pi_apply (roots p.1 ++ p.2)

/-- All marks used by a rooted subtree of depth at least `n` belong to the
future mark field from generation `n`. -/
theorem descendantMarkSpace_le_future (n : ℕ) (u : TreeNode)
    (hu : n ≤ u.length) :
    descendantMarkSpace u ≤ futureMarkSpace n := by
  unfold descendantMarkSpace futureMarkSpace
  apply iSup_le
  intro v
  have hdepth : n ≤ (u ++ v).length := by simp; omega
  exact le_iSup_of_le (u ++ v)
    (le_iSup_of_le
      (show u ++ v ∈ {w : TreeNode | n ≤ w.length} from hdepth) le_rfl)

theorem subtreeVector_future_measurable {k n : ℕ}
    (roots : Fin k → TreeNode) (hlen : ∀ i, (roots i).length = n) :
    Measurable[futureMarkSpace n] (subtreeVector roots) := by
  apply (@measurable_pi_iff (MarkedTree OffspringMark) (Fin k)
    (fun _ => MarkedTree OffspringMark) (futureMarkSpace n)
    (fun _ => inferInstance) (subtreeVector roots)).2
  intro i
  exact (subtreeMarks_descendant_measurable (roots i)).mono
    (descendantMarkSpace_le_future n (roots i) (by rw [hlen i])) le_rfl

theorem fixed_subtreeVector_independent
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → TreeNode)
    (hlen : ∀ i, (roots i).length = n) :
    Indep (generationFiltration (Mark := OffspringMark) n)
      (MeasurableSpace.comap (subtreeVector roots) inferInstance)
      (iidMarkedTreeLaw μ) :=
  indep_of_indep_of_le_right (generation_future_mark_independent μ n)
    (subtreeVector_future_measurable roots hlen).comap_le

/-- The joint deterministic-time branching event formula. -/
theorem fixed_subtreeVector_event_factorization
    (μ : Measure OffspringMark) [IsProbabilityMeasure μ]
    {k n : ℕ} (roots : Fin k → TreeNode)
    (hlen : ∀ i, (roots i).length = n)
    (hinj : Function.Injective roots)
    (A : Set (MarkedTree OffspringMark))
    (B : Set (Fin k → MarkedTree OffspringMark))
    (hA : MeasurableSet[generationFiltration (Mark := OffspringMark) n] A)
    (hB : MeasurableSet B) :
    iidMarkedTreeLaw μ (A ∩ subtreeVector roots ⁻¹' B) =
      iidMarkedTreeLaw μ A *
        (Measure.infinitePi (fun _ : Fin k => iidMarkedTreeLaw μ)) B := by
  have hB' : MeasurableSet[MeasurableSpace.comap (subtreeVector roots) inferInstance]
      (subtreeVector roots ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((fixed_subtreeVector_independent μ roots hlen).indepSet_of_measurableSet
    hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply (subtreeVector_measurable roots) hB,
    fixed_subtreeVector_law μ roots hlen hinj] at h
  exact h

end ThesisSpeed
