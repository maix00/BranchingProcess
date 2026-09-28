import Probability.BranchingRandomWalk.Population.Processes.Causal.Capacity
import Probability.BranchingRandomWalk.Population.Processes.Causal.PathWindow
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.FiniteExpectations
import Probability.BranchingRandomWalk.Spine.Path.ManyToOne

/-!
# First moments of causal killed populations

The pathwise estimate in this file turns the size of a killed generation into
an unweighted ancestral-path observable.  Integrating it and applying the
path-functional many-to-one identity leaves only a one-dimensional spine
expectation.  This is the first-moment route used by capacity estimates.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed.CausalFinitePopulation

open Combinatorics.UlamHarris Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk.Spine

attribute [local instance] Classical.propDecidable Classical.decEq

/-- For one initial root, every particle retained by the restarted killed
population contributes one to the corresponding unrestricted path sum. -/
theorem size_le_pathGeneration_restartedWindow
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (r : Root) (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d) (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (hzero : 0 ∈ window 0)
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    (n : ℕ) (field : RootIndexed.StepField Root α Mark) :
    let P := ofRestartedRealPositionSets initialPosition d hd
      ({(r, ([] : TreeNode α))} : Finset (RootIndexed.TreeNode Root α))
      (by simp) cutoff window hwindow upper hupper
    P.size n field ≤
      pathGeneration (⟨d, hd⟩ : Potential Mark) n
        (restartedWindowTest cutoff window) (initialPosition r) (field r) := by
  classical
  dsimp only
  let P := ofRestartedRealPositionSets initialPosition d hd
    ({(r, ([] : TreeNode α))} : Finset (RootIndexed.TreeNode Root α))
    (by simp) cutoff window hwindow upper hupper
  let addresses : Finset (TreeNode α) := (P n field).image Prod.snd
  have hroot {q : RootIndexed.TreeNode Root α} (hq : q ∈ P n field) :
      q.1 = r := by
    have hinitial := P.initial_mem_of_mem hq
    change (q.1, ([] : TreeNode α)) ∈
      ({(r, ([] : TreeNode α))} :
        Finset (RootIndexed.TreeNode Root α)) at hinitial
    simpa using hinitial
  have hinj : Set.InjOn Prod.snd (↑(P n field) :
      Set (RootIndexed.TreeNode Root α)) := by
    intro q hq q' hq' heq
    apply Prod.ext
    · exact (hroot hq).trans (hroot hq').symm
    · exact heq
  have hcard : addresses.card = (P n field).card :=
    Finset.card_image_iff.mpr hinj
  rw [size, ← hcard]
  calc
    (addresses.card : ENNReal) = ∑ u ∈ addresses, (1 : ENNReal) := by simp
    _ ≤ ∑ u ∈ addresses,
        pathGenerationTerm (⟨d, hd⟩ : Potential Mark) n
          (restartedWindowTest cutoff window) (initialPosition r) u
          (field r) := by
      apply Finset.sum_le_sum
      intro u hu
      obtain ⟨q, hq, hqu⟩ := Finset.mem_image.mp hu
      have hqroot : q.1 = r := hroot hq
      have hqdepth : q.2.length = n := P.depth n field q hq
      have hqsurvive : surviveAlong (field r) [] u := by
        have := P.surviveAlong_of_mem hq
        simpa [hqroot, ← hqu] using this
      have hqwindow := mem_ofRestartedRealPositionSets_inRestartedWindows
        initialPosition d hd {(r, [])} (by simp) cutoff window hwindow hzero
        upper hupper hq
      have huwindow : InRestartedWindows cutoff window
          (pathHistory (⟨d, hd⟩ : Potential Mark) n
            (initialPosition r) (field r) u) := by
        simpa [hqroot, ← hqu] using hqwindow
      have htest : restartedWindowTest cutoff window
          (pathHistory (⟨d, hd⟩ : Potential Mark) n
            (initialPosition r) (field r) u) = 1 :=
        (restartedWindowTest_eq_one_iff cutoff window _).2 huwindow
      rw [pathGenerationTerm, Set.indicator_of_mem]
      · exact le_of_eq htest.symm
      · exact ⟨by simpa [← hqu] using hqdepth, hqsurvive⟩
    _ ≤ ∑' u : TreeNode α,
        pathGenerationTerm (⟨d, hd⟩ : Potential Mark) n
          (restartedWindowTest cutoff window) (initialPosition r) u
          (field r) := ENNReal.sum_le_tsum addresses
    _ = pathGeneration (⟨d, hd⟩ : Potential Mark) n
        (restartedWindowTest cutoff window) (initialPosition r) (field r) := rfl

/-- The first moment of a one-root restarted killed generation is bounded by
the corresponding spine path expectation.  This theorem contains no second
moment or pair estimate. -/
theorem lintegral_size_le_spine_restartedWindow
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (r : Root) (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d)
    (μ : Measure (Combinatorics.Branching.Step α Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (⟨d, hd⟩ : Potential Mark) μ)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (hzero : 0 ∈ window 0)
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    (n : ℕ) :
    let P := ofRestartedRealPositionSets initialPosition d hd
      ({(r, ([] : TreeNode α))} : Finset (RootIndexed.TreeNode Root α))
      (by simp) cutoff window hwindow upper hupper
    (∫⁻ field, P.size n field
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp (tiltedPosition n increment)) *
          restartedWindowTest cutoff window
            (spineHistory n (initialPosition r) increment)
        ∂tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ := by
  dsimp only
  let test : (Fin (n + 1) → ℝ) → ENNReal :=
    restartedWindowTest cutoff window
  have htest : Measurable test :=
    restartedWindowTest_measurable cutoff window hwindow
  calc
    (∫⁻ field,
        (ofRestartedRealPositionSets initialPosition d hd
          ({(r, ([] : TreeNode α))} :
            Finset (RootIndexed.TreeNode Root α))
          (by simp) cutoff window hwindow upper hupper).size n field
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) ≤
        ∫⁻ field,
          pathGeneration (⟨d, hd⟩ : Potential Mark) n test
            (initialPosition r) (field r)
          ∂RootIndexed.stepFieldLaw (Root := Root) μ :=
      lintegral_mono fun field =>
        size_le_pathGeneration_restartedWindow r initialPosition d hd cutoff
          window hwindow hzero upper hupper n field
    _ = ∫⁻ tree : Combinatorics.Branching.StepField α Mark,
          pathGeneration (⟨d, hd⟩ : Potential Mark) n test
            (initialPosition r) tree
          ∂ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ := by
      exact RootIndexed.lintegral_root_observable μ r _
        (pathGeneration_measurable (⟨d, hd⟩ : Potential Mark) n htest
          (initialPosition r))
    _ = ∫⁻ increment,
        ENNReal.ofReal (Real.exp (tiltedPosition n increment)) *
          test (spineHistory n (initialPosition r) increment)
        ∂tiltedIncrementFieldLaw (⟨d, hd⟩ : Potential Mark) μ :=
      pathManyToOneCore (⟨d, hd⟩ : Potential Mark) μ hboundary n htest
        (initialPosition r)

end RootIndexed.CausalFinitePopulation
end ProbabilityTheory.BranchingRandomWalk
