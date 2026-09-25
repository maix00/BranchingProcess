import ThesisSpeed.Probability.PointProcess.Law.IID
import Mathlib.Probability.Independence.Basic

/-!
# Independent past and future mark fields

At a deterministic generation boundary, the addresses already exposed have
depth below `n`; all other addresses still carry independent marks. This is
the σ-algebra form of the first step of the branching property. The selected
BRW subtree statement needs additional address and position definitions.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

/-- The information in one offspring mark. -/
@[instance_reducible] def coordinateMarkSpace (u : TreeNode) :
    MeasurableSpace (MarkedTree OffspringMark) :=
  MeasurableSpace.comap (fun ω => ω u) inferInstance

/-- Information carried by marks of parents before generation `n`. -/
@[instance_reducible] def pastMarkSpace (n : ℕ) :
    MeasurableSpace (MarkedTree OffspringMark) :=
  ⨆ u ∈ {u : TreeNode | u.length < n}, coordinateMarkSpace u

/-- Information carried by marks at generation `n` and beyond. -/
@[instance_reducible] def futureMarkSpace (n : ℕ) :
    MeasurableSpace (MarkedTree OffspringMark) :=
  ⨆ u ∈ {u : TreeNode | n ≤ u.length}, coordinateMarkSpace u

/-- All pre-sampled marks in the descendant subtree rooted at `u`, including
the mark at `u` itself. -/
@[instance_reducible] def descendantMarkSpace (u : TreeNode) :
    MeasurableSpace (MarkedTree OffspringMark) :=
  ⨆ v : TreeNode, coordinateMarkSpace (u ++ v)

/-- Address set of the subtree rooted at `u`. -/
def descendantAddresses (u : TreeNode) : Set TreeNode :=
  {w | ∃ tail : TreeNode, w = u ++ tail}

/-- The pre-sampled subtree viewed again as a full marked tree. -/
def subtreeMarks (u : TreeNode) (ω : MarkedTree OffspringMark) :
    MarkedTree OffspringMark :=
  fun v => ω (u ++ v)

/-- Every fixed rooted subtree has the same law as the original marked tree. -/
theorem subtreeMarks_law (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (u : TreeNode) :
    (iidMarkedTreeLaw μ).map (subtreeMarks u) = iidMarkedTreeLaw μ := by
  change (Measure.infinitePi (fun _ : TreeNode => μ)).map
    (fun ω v => ω (u ++ v)) = Measure.infinitePi (fun _ : TreeNode => μ)
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : TreeNode => μ)
    (f := fun v : TreeNode => u ++ v)
    (fun _ _ h => List.append_cancel_left h)

/-- Extracting a fixed rooted subtree reads only descendant marks. -/
theorem subtreeMarks_descendant_measurable (u : TreeNode) :
    Measurable[descendantMarkSpace u] (subtreeMarks u) := by
  apply (@measurable_pi_iff (MarkedTree OffspringMark) TreeNode
    (fun _ => OffspringMark) (descendantMarkSpace u)
    (fun _ => inferInstance) (subtreeMarks u)).2
  intro v
  have hle : coordinateMarkSpace (u ++ v) ≤ descendantMarkSpace u := by
    unfold descendantMarkSpace
    exact le_iSup (fun v : TreeNode => coordinateMarkSpace (u ++ v)) v
  have hcoord : Measurable[coordinateMarkSpace (u ++ v)]
      (fun ω : MarkedTree OffspringMark => ω (u ++ v)) :=
    Measurable.of_comap_le le_rfl
  exact hcoord.mono hle le_rfl

theorem subtreeMarks_measurable (u : TreeNode) :
    Measurable (subtreeMarks u) := by
  apply measurable_pi_iff.mpr
  intro v
  exact measurable_pi_apply (u ++ v)

theorem descendantMarkSpace_eq_iSup (u : TreeNode) :
    descendantMarkSpace u =
      ⨆ w ∈ descendantAddresses u, coordinateMarkSpace w := by
  apply le_antisymm
  · unfold descendantMarkSpace
    apply iSup_le
    intro tail
    exact le_iSup_of_le (u ++ tail)
      (le_iSup_of_le (show u ++ tail ∈ descendantAddresses u from
        ⟨tail, rfl⟩) le_rfl)
  · apply iSup_le
    intro w
    apply iSup_le
    intro hw
    obtain ⟨tail, rfl⟩ := hw
    unfold descendantMarkSpace
    exact le_iSup (fun tail : TreeNode => coordinateMarkSpace (u ++ tail)) tail

/-- The cylinder definition of the generation filtration agrees with the
join of the individually revealed coordinate σ-algebras. -/
theorem generationSpace_eq_pastMarkSpace (n : ℕ) :
    generationSpace (Mark := OffspringMark) n = pastMarkSpace n := by
  apply le_antisymm
  · unfold generationSpace
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨u, hu, t, ht, rfl⟩
    have hle : coordinateMarkSpace u ≤ pastMarkSpace n := by
      unfold pastMarkSpace
      exact le_iSup_of_le u
        (le_iSup_of_le (show u ∈ {v : TreeNode | v.length < n} from hu) le_rfl)
    apply hle
    change ∃ t' : Set OffspringMark, MeasurableSet t' ∧
      (fun ω : MarkedTree OffspringMark => ω u) ⁻¹' t' =
        {ω : MarkedTree OffspringMark | ω u ∈ t}
    exact ⟨t, ht, rfl⟩
  · unfold pastMarkSpace
    apply iSup_le
    intro u
    apply iSup_le
    intro hu
    change u.length < n at hu
    exact (mark_measurable_of_depth_lt u n hu).comap_le

theorem iid_coordinateMarkSpaces (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] :
    iIndep coordinateMarkSpace (iidMarkedTreeLaw μ) := by
  exact (iidMarkedTree_independent μ).iIndep

/-- Everything revealed before generation `n` is independent of all marks
of generation `n` and later, under the pre-sampled i.i.d. tree law. -/
theorem past_future_mark_independent (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (n : ℕ) :
    Indep (pastMarkSpace n) (futureMarkSpace n)
      (iidMarkedTreeLaw μ) := by
  have hle : ∀ u : TreeNode, coordinateMarkSpace u ≤
      (inferInstance : MeasurableSpace (MarkedTree OffspringMark)) :=
    fun u => (measurable_pi_apply u).comap_le
  have hdisj : Disjoint
      {u : TreeNode | u.length < n}
      {u : TreeNode | n ≤ u.length} := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    change u.length < n at hu
    change n ≤ u.length at hv
    exact (not_lt_of_ge hv) hu
  exact indep_iSup_of_disjoint hle (iid_coordinateMarkSpaces μ) hdisj

/-- The actual generation-`n` information is independent of all marks at
depth at least `n`. -/
theorem generation_future_mark_independent (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (n : ℕ) :
    Indep (generationFiltration (Mark := OffspringMark) n)
      (futureMarkSpace n) (iidMarkedTreeLaw μ) := by
  rw [show generationFiltration (Mark := OffspringMark) n =
      generationSpace (Mark := OffspringMark) n from rfl,
    generationSpace_eq_pastMarkSpace]
  exact past_future_mark_independent μ n

/-- The unexposed mark at one fixed parent is independent of all previously
revealed generations. -/
theorem generation_coordinate_independent (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (n : ℕ) (u : TreeNode)
    (hu : n ≤ u.length) :
    Indep (generationFiltration (Mark := OffspringMark) n)
      (coordinateMarkSpace u) (iidMarkedTreeLaw μ) := by
  apply indep_of_indep_of_le_right (generation_future_mark_independent μ n)
  unfold futureMarkSpace
  exact le_iSup_of_le u
    (le_iSup_of_le (show u ∈ {v : TreeNode | n ≤ v.length} from hu) le_rfl)

/-- The whole fixed descendant subtree is independent of the information
available just before its root reproduces. -/
theorem generation_descendant_independent (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (u : TreeNode) :
    Indep (generationFiltration (Mark := OffspringMark) u.length)
      (descendantMarkSpace u) (iidMarkedTreeLaw μ) := by
  apply indep_of_indep_of_le_right
    (generation_future_mark_independent μ u.length)
  unfold descendantMarkSpace
  apply iSup_le
  intro v
  unfold futureMarkSpace
  have hdepth : u.length ≤ (u ++ v).length := by simp
  exact le_iSup_of_le (u ++ v)
    (le_iSup_of_le
      (show u ++ v ∈ {w : TreeNode | u.length ≤ w.length} from hdepth) le_rfl)

/-- The fixed subtree random variable is independent of the domain flow at
the root's generation. -/
theorem generation_subtree_independent (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (u : TreeNode) :
    Indep (generationFiltration (Mark := OffspringMark) u.length)
      (MeasurableSpace.comap (subtreeMarks u) inferInstance)
      (iidMarkedTreeLaw μ) :=
  indep_of_indep_of_le_right (generation_descendant_independent μ u)
    (subtreeMarks_descendant_measurable u).comap_le

/-- The concrete product form of deterministic-time branching for one fixed
root. It applies to every past event and measurable subtree event. -/
theorem fixed_subtree_event_factorization (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (u : TreeNode)
    (A B : Set (MarkedTree OffspringMark))
    (hA : MeasurableSet[generationFiltration (Mark := OffspringMark) u.length] A)
    (hB : MeasurableSet B) :
    iidMarkedTreeLaw μ (A ∩ subtreeMarks u ⁻¹' B) =
      iidMarkedTreeLaw μ A * iidMarkedTreeLaw μ B := by
  have hB' : MeasurableSet[MeasurableSpace.comap (subtreeMarks u) inferInstance]
      (subtreeMarks u ⁻¹' B) := ⟨B, hB, rfl⟩
  have h := ((generation_subtree_independent μ u).indepSet_of_measurableSet
    hA hB').measure_inter_eq_mul
  rw [← Measure.map_apply (subtreeMarks_measurable u) hB,
    subtreeMarks_law] at h
  exact h

/-- Distinct roots at the same depth have disjoint pre-sampled subtrees. -/
theorem descendantAddresses_disjoint (u v : TreeNode)
    (hlen : u.length = v.length) (hne : u ≠ v) :
    Disjoint (descendantAddresses u) (descendantAddresses v) := by
  apply Set.disjoint_left.mpr
  intro w hw₁ hw₂
  obtain ⟨a, ha⟩ := hw₁
  obtain ⟨b, hb⟩ := hw₂
  have heq : u ++ a = v ++ b := ha.symm.trans hb
  have hp := congrArg (List.take u.length) heq
  have huv : u = v := by
    simpa [hlen] using hp
  exact hne huv

/-- All descendant marks of two different generation-`n` roots are
independent. This is the pairwise deterministic-time branching statement at
the level of raw offspring randomness. -/
theorem distinct_descendant_marks_independent (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (u v : TreeNode)
    (hlen : u.length = v.length) (hne : u ≠ v) :
    Indep (descendantMarkSpace u) (descendantMarkSpace v)
      (iidMarkedTreeLaw μ) := by
  rw [descendantMarkSpace_eq_iSup, descendantMarkSpace_eq_iSup]
  have hle : ∀ w : TreeNode, coordinateMarkSpace w ≤
      (inferInstance : MeasurableSpace (MarkedTree OffspringMark)) :=
    fun w => (measurable_pi_apply w).comap_le
  exact indep_iSup_of_disjoint hle (iid_coordinateMarkSpaces μ)
    (descendantAddresses_disjoint u v hlen hne)

end ThesisSpeed
