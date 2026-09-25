import ThesisSpeed.Probability.PointProcess.Law.OrderedSupport
import ThesisSpeed.Probability.Genealogy.Positions

/-!
# A branching random walk with several initial ancestors

`Fin m` labels the `m` initial particles. Each label owns a complete,
independent pre-sampled Ulam--Harris marked tree. A later selection rule must
compare descendants across all labels and keep the globally leftmost `N`.
The present file establishes the probability space, domain filtration, and
positions; it does not define that selection rule.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

abbrev MultiRootTree (m : ℕ) := Fin m → MarkedTree OffspringMark

/-- Independent marked trees attached to all initial particle labels. -/
noncomputable def iidMultiRootLaw (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (m : ℕ) : Measure (MultiRootTree m) :=
  Measure.infinitePi (fun _ : Fin m => iidMarkedTreeLaw μ)

instance (μ : Measure OffspringMark) [IsProbabilityMeasure μ] (m : ℕ) :
    IsProbabilityMeasure (iidMultiRootLaw μ m) := by
  unfold iidMultiRootLaw
  infer_instance

theorem iidMultiRoot_marginal (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] {m : ℕ} (i : Fin m) :
    (iidMultiRootLaw μ m).map (fun ω : MultiRootTree m => ω i) =
      iidMarkedTreeLaw μ := by
  simpa [iidMultiRootLaw] using
    (Measure.infinitePi_map_eval
      (fun _ : Fin m => iidMarkedTreeLaw μ) i)

theorem iidMultiRoot_independent (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (m : ℕ) :
    iIndepFun (fun i (ω : MultiRootTree m) => ω i)
      (iidMultiRootLaw μ m) := by
  unfold iidMultiRootLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : Fin m => iidMarkedTreeLaw μ)
    (X := fun _ : Fin m => id)
    (fun _ => measurable_id))

theorem iidMultiRoot_mark_marginal (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] {m : ℕ}
    (i : Fin m) (u : TreeNode) :
    (iidMultiRootLaw μ m).map
      (fun ω : MultiRootTree m => ω i u) = μ := by
  have hi := iidMultiRoot_marginal μ i
  have hu := iidMarkedTree_marginal μ u
  calc
    (iidMultiRootLaw μ m).map (fun ω : MultiRootTree m => ω i u) =
        ((iidMultiRootLaw μ m).map
          (fun ω : MultiRootTree m => ω i)).map
            (fun tree : MarkedTree OffspringMark => tree u) := by
      rw [Measure.map_map]
      · rfl
      · exact measurable_pi_apply u
      · exact measurable_pi_apply i
    _ = μ := by rw [hi, hu]

theorem iidMultiRoot_all_ordered (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (hμ : μ orderedOffspring = 1)
    (m : ℕ) :
    ∀ᵐ ω ∂iidMultiRootLaw μ m, ∀ i : Fin m,
      ∀ u : TreeNode, ω i u ∈ orderedOffspring := by
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro u
  have hpre : iidMultiRootLaw μ m
      {ω : MultiRootTree m | ω i u ∈ orderedOffspring} =
      μ orderedOffspring := by
    calc
      iidMultiRootLaw μ m {ω : MultiRootTree m |
          ω i u ∈ orderedOffspring} =
          ((iidMultiRootLaw μ m).map
            (fun ω : MultiRootTree m => ω i u)) orderedOffspring := by
          have hmeas : Measurable
              (fun ω : MultiRootTree m => ω i u) :=
            (measurable_pi_apply u).comp (measurable_pi_apply i)
          rw [Measure.map_apply hmeas orderedOffspring_measurable]
          rfl
      _ = μ orderedOffspring := by rw [iidMultiRoot_mark_marginal]
  apply (ae_mem_iff_measure_eq
    (((measurable_pi_apply u).comp (measurable_pi_apply i))
      orderedOffspring_measurable).nullMeasurableSet).2
  change iidMultiRootLaw μ m
    {ω : MultiRootTree m | ω i u ∈ orderedOffspring} =
      (iidMultiRootLaw μ m) Set.univ
  rw [hpre, hμ]
  simp

theorem iidMultiRoot_all_nonempty (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ] (hμ : μ offspringNonempty = 1)
    (m : ℕ) :
    ∀ᵐ ω ∂iidMultiRootLaw μ m, ∀ i : Fin m,
      ∀ u : TreeNode, ω i u ∈ offspringNonempty := by
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro u
  have hmeas : Measurable (fun ω : MultiRootTree m => ω i u) :=
    (measurable_pi_apply u).comp (measurable_pi_apply i)
  have hpre : iidMultiRootLaw μ m
      {ω : MultiRootTree m | ω i u ∈ offspringNonempty} =
      μ offspringNonempty := by
    calc
      iidMultiRootLaw μ m
          {ω : MultiRootTree m | ω i u ∈ offspringNonempty} =
          ((iidMultiRootLaw μ m).map
            (fun ω : MultiRootTree m => ω i u)) offspringNonempty := by
              rw [Measure.map_apply hmeas offspringNonempty_measurable]
              rfl
      _ = μ offspringNonempty := by rw [iidMultiRoot_mark_marginal]
  apply (ae_mem_iff_measure_eq
    (hmeas offspringNonempty_measurable).nullMeasurableSet).2
  change iidMultiRootLaw μ m
    {ω : MultiRootTree m | ω i u ∈ offspringNonempty} =
      (iidMultiRootLaw μ m) Set.univ
  rw [hpre, hμ]
  simp

/-- For several initial ancestors, ordered support and the thesis's
at-least-one-child assumption imply that slot zero exists at every address
simultaneously almost surely. -/
theorem iidMultiRoot_all_first_child (μ : Measure OffspringMark)
    [IsProbabilityMeasure μ]
    (hordered : μ orderedOffspring = 1)
    (hnonempty : μ offspringNonempty = 1)
    (m : ℕ) :
    ∀ᵐ ω ∂iidMultiRootLaw μ m, ∀ i : Fin m,
      ∀ u : TreeNode, ω i u ∈ childRealized 0 := by
  filter_upwards [iidMultiRoot_all_ordered μ hordered m,
    iidMultiRoot_all_nonempty μ hnonempty m] with ω hord hne
  intro i u
  obtain ⟨j, hj⟩ := hne i u
  exact orderedOffspring_first_present (ω i u) (hord i u) j hj

/-- Information from all initial ancestors through generation `n`. -/
@[instance_reducible] def multiRootGenerationSpace (m n : ℕ) :
    MeasurableSpace (MultiRootTree m) :=
  MeasurableSpace.generateFrom
    {s | ∃ i : Fin m, ∃ u : TreeNode, u.length < n ∧
      ∃ t : Set OffspringMark, MeasurableSet t ∧
        s = {ω : MultiRootTree m | ω i u ∈ t}}

def multiRootFiltration (m : ℕ) :
    Filtration ℕ (inferInstance : MeasurableSpace (MultiRootTree m)) where
  seq := multiRootGenerationSpace m
  mono' := by
    intro n k hnk
    apply MeasurableSpace.generateFrom_mono
    rintro s ⟨i, u, hu, t, ht, rfl⟩
    exact ⟨i, u, lt_of_lt_of_le hu hnk, t, ht, rfl⟩
  le' := by
    intro n
    apply MeasurableSpace.generateFrom_le
    rintro s ⟨i, u, hu, t, ht, rfl⟩
    exact ((measurable_pi_apply u).comp (measurable_pi_apply i)) ht

theorem multiRootGenerationSpace_zero (m : ℕ) :
    multiRootGenerationSpace m 0 = ⊥ := by
  unfold multiRootGenerationSpace
  have hgen :
      {s : Set (MultiRootTree m) |
        ∃ i : Fin m, ∃ u : TreeNode, u.length < 0 ∧
          ∃ t : Set OffspringMark, MeasurableSet t ∧
            s = {ω : MultiRootTree m | ω i u ∈ t}} = ∅ := by
    ext s
    simp
  rw [hgen, MeasurableSpace.generateFrom_empty]

theorem multiRootMark_measurable (m n : ℕ) (i : Fin m)
    (u : TreeNode) (hu : u.length < n) :
    Measurable[multiRootFiltration m n]
      (fun ω : MultiRootTree m => ω i u) := by
  intro t ht
  exact MeasurableSpace.measurableSet_generateFrom
    ⟨i, u, hu, t, ht, rfl⟩

/-- A generation-measurably selected address within a fixed labelled root
has an observable mark whenever its depth has already been revealed. -/
theorem multiRootSelectedMark_measurable {m n : ℕ} (i : Fin m)
    (chosen : MultiRootTree m → TreeNode)
    (hchosen : Measurable[multiRootFiltration m n] chosen)
    (hdepth : ∀ ω, (chosen ω).length < n) :
    Measurable[multiRootFiltration m n]
      (fun ω : MultiRootTree m => ω i (chosen ω)) := by
  intro t ht
  have hset :
      {ω : MultiRootTree m | ω i (chosen ω) ∈ t} =
        ⋃ u : TreeNode,
          {ω : MultiRootTree m | chosen ω = u} ∩
            {ω : MultiRootTree m | ω i u ∈ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨chosen ω, rfl, h⟩
    · rintro ⟨u, hu, hmark⟩
      simpa [hu] using hmark
  change MeasurableSet[multiRootFiltration m n]
    {ω : MultiRootTree m | ω i (chosen ω) ∈ t}
  rw [hset]
  apply MeasurableSet.iUnion
  intro u
  by_cases hu : u.length < n
  · exact (hchosen (measurableSet_singleton u)).inter
      ((multiRootMark_measurable m n i u hu) ht)
  · have hempty : {ω : MultiRootTree m | chosen ω = u} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact hu (heq ▸ hdepth ω)
    simp [hempty]

/-- Realization of a labelled descendant checks only its own ancestral marks. -/
def multiRootRealized {m : ℕ} (i : Fin m) (u : TreeNode) :
    Set (MultiRootTree m) :=
  {ω | ω i ∈ realizedNode u}

theorem multiRootRealized_measurable {m : ℕ} (i : Fin m)
    (u : TreeNode) :
    MeasurableSet[multiRootFiltration m u.length]
      (multiRootRealized i u) := by
  have hset : multiRootRealized i u =
      ⋂ j ∈ Finset.range u.length,
        {ω : MultiRootTree m |
          ω i (u.take j) ∈ childRealized (u[j]!)} := by
    ext ω
    simp [multiRootRealized, realizedNode]
  rw [hset]
  apply Finset.measurableSet_biInter
  intro j hj
  have hj' : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj'), hj']
  exact (multiRootMark_measurable m u.length i (u.take j) hprefix)
    (childRealized_measurable (u[j]!))

/-- The position of a descendant, including its initial ancestor's offset. -/
def multiRootPosition {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootTree m) (i : Fin m) (u : TreeNode) : ℝ :=
  x i + vertexPosition (ω i) u

theorem multiRootPosition_at_root {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootTree m) (i : Fin m) :
    multiRootPosition x ω i [] = x i := by
  simp [multiRootPosition, vertexPosition]

theorem multiRootPosition_child {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootTree m) (i : Fin m) (u : TreeNode) (j : ℕ) :
    multiRootPosition x ω i (u ++ [j]) =
      multiRootPosition x ω i u + childDisplacement (ω i u) j := by
  simp [multiRootPosition, vertexPosition_append_singleton, add_assoc]

theorem multiRootPosition_measurable {m : ℕ} (x : Fin m → ℝ)
    (i : Fin m) (u : TreeNode) :
    Measurable[multiRootFiltration m u.length]
      (fun ω : MultiRootTree m => multiRootPosition x ω i u) := by
  unfold multiRootPosition vertexPosition
  apply measurable_const.add
  apply Finset.measurable_fun_sum
  intro j hj
  have hj' : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj'), hj']
  exact (childDisplacement_measurable (u[j]!)).comp
    (multiRootMark_measurable m u.length i (u.take j) hprefix)

end ThesisSpeed
