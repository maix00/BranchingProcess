import ThesisSpeed.Probability.PointProcess.Law.OrderedSupport
import ThesisSpeed.Probability.PointProcess.Legacy.PositionsWeighted

/-!
# A branching random walk with several initial ancestors

`Fin m` labels the `m` initial particles. Each label owns a complete,
independent pre-sampled field of branching steps over all Ulam--Harris
addresses. This file constructs the product law and transfers ordered
support, nonemptiness, and the thesis's at-least-one-child assumption to it
almost surely. The domain filtration is in `MultiRoot/Filtration.lean` and
the positions are in `MultiRoot/Realized.lean`; a selection rule comparing
descendants across labels is not defined here.
-/

open MeasureTheory ProbabilityTheory

namespace ThesisSpeed

abbrev MultiRootMark (m : ℕ) := Fin m → Mark ℕ WeightedBranchingStep

/-- Independent pre-sampled step fields attached to all initial labels. -/
noncomputable def iidMultiRootLaw (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ] (m : ℕ) : Measure (MultiRootMark m) :=
  Measure.infinitePi (fun _ : Fin m => iidMarkLaw μ)

instance (μ : Measure WeightedBranchingStep) [IsProbabilityMeasure μ] (m : ℕ) :
    IsProbabilityMeasure (iidMultiRootLaw μ m) := by
  unfold iidMultiRootLaw
  infer_instance

theorem iidMultiRoot_marginal (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ] {m : ℕ} (i : Fin m) :
    (iidMultiRootLaw μ m).map (fun ω : MultiRootMark m => ω i) =
      iidMarkLaw μ := by
  simpa [iidMultiRootLaw] using
    (Measure.infinitePi_map_eval
      (fun _ : Fin m => iidMarkLaw μ) i)

theorem iidMultiRoot_independent (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ] (m : ℕ) :
    iIndepFun (fun i (ω : MultiRootMark m) => ω i)
      (iidMultiRootLaw μ m) := by
  unfold iidMultiRootLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : Fin m => iidMarkLaw μ)
    (X := fun _ : Fin m => id)
    (fun _ => measurable_id))

theorem iidMultiRoot_mark_marginal (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ] {m : ℕ}
    (i : Fin m) (u : 𝕍) :
    (iidMultiRootLaw μ m).map
      (fun ω : MultiRootMark m => ω i u) = μ := by
  have hi := iidMultiRoot_marginal μ i
  have hu := iidMark_marginal μ u
  calc
    (iidMultiRootLaw μ m).map (fun ω : MultiRootMark m => ω i u) =
        ((iidMultiRootLaw μ m).map
          (fun ω : MultiRootMark m => ω i)).map
            (fun tree : Mark ℕ WeightedBranchingStep => tree u) := by
      rw [Measure.map_map]
      · rfl
      · exact measurable_pi_apply u
      · exact measurable_pi_apply i
    _ = μ := by rw [hi, hu]

theorem iidMultiRoot_all_ordered (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ] (hμ : μ orderedOffspring = 1)
    (m : ℕ) :
    ∀ᵐ ω ∂iidMultiRootLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, ω i u ∈ orderedOffspring := by
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro u
  have hpre : iidMultiRootLaw μ m
      {ω : MultiRootMark m | ω i u ∈ orderedOffspring} =
      μ orderedOffspring := by
    calc
      iidMultiRootLaw μ m {ω : MultiRootMark m |
          ω i u ∈ orderedOffspring} =
          ((iidMultiRootLaw μ m).map
            (fun ω : MultiRootMark m => ω i u)) orderedOffspring := by
          have hmeas : Measurable
              (fun ω : MultiRootMark m => ω i u) :=
            (measurable_pi_apply u).comp (measurable_pi_apply i)
          rw [Measure.map_apply hmeas orderedOffspring_measurable]
          rfl
      _ = μ orderedOffspring := by rw [iidMultiRoot_mark_marginal]
  change ∀ᵐ ω ∂iidMultiRootLaw μ m,
    ω ∈ (fun ω : MultiRootMark m => ω i u) ⁻¹' orderedOffspring
  apply (ae_mem_iff_measure_eq
    (((measurable_pi_apply u).comp (measurable_pi_apply i))
      orderedOffspring_measurable).nullMeasurableSet).2
  change iidMultiRootLaw μ m
    {ω : MultiRootMark m | ω i u ∈ orderedOffspring} =
      (iidMultiRootLaw μ m) Set.univ
  rw [hpre, hμ]
  simp

theorem iidMultiRoot_all_nonempty (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ] (hμ : μ offspringNonempty = 1)
    (m : ℕ) :
    ∀ᵐ ω ∂iidMultiRootLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, ω i u ∈ offspringNonempty := by
  apply ae_all_iff.2
  intro i
  apply ae_all_iff.2
  intro u
  have hmeas : Measurable (fun ω : MultiRootMark m => ω i u) :=
    (measurable_pi_apply u).comp (measurable_pi_apply i)
  have hpre : iidMultiRootLaw μ m
      {ω : MultiRootMark m | ω i u ∈ offspringNonempty} =
      μ offspringNonempty := by
    calc
      iidMultiRootLaw μ m
          {ω : MultiRootMark m | ω i u ∈ offspringNonempty} =
          ((iidMultiRootLaw μ m).map
            (fun ω : MultiRootMark m => ω i u)) offspringNonempty := by
              rw [Measure.map_apply hmeas offspringNonempty_measurable]
              rfl
      _ = μ offspringNonempty := by rw [iidMultiRoot_mark_marginal]
  apply (ae_mem_iff_measure_eq
    (hmeas offspringNonempty_measurable).nullMeasurableSet).2
  change iidMultiRootLaw μ m
    {ω : MultiRootMark m | ω i u ∈ offspringNonempty} =
      (iidMultiRootLaw μ m) Set.univ
  rw [hpre, hμ]
  simp

/-- For several initial ancestors, ordered support and the thesis's
at-least-one-child assumption imply that slot zero exists at every address
simultaneously almost surely. -/
theorem iidMultiRoot_all_first_child (μ : Measure WeightedBranchingStep)
    [IsProbabilityMeasure μ]
    (hordered : μ orderedOffspring = 1)
    (hnonempty : μ offspringNonempty = 1)
    (m : ℕ) :
    ∀ᵐ ω ∂iidMultiRootLaw μ m, ∀ i : Fin m,
      ∀ u : 𝕍, ω i u ∈ childRealized 0 := by
  filter_upwards [iidMultiRoot_all_ordered μ hordered m,
    iidMultiRoot_all_nonempty μ hnonempty m] with ω hord hne
  intro i u
  obtain ⟨j, hj⟩ := hne i u
  exact orderedOffspring_first_present (ω i u) (hord i u) j hj

end ThesisSpeed
