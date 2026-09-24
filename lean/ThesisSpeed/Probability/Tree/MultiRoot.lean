import ThesisSpeed.Probability.Tree.OrderedLaw
import ThesisSpeed.Probability.Tree.Positions

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
