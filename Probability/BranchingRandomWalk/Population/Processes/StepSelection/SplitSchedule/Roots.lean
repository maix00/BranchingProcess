import Probability.BranchingRandomWalk.Population.Processes.StepSelection.SplitSchedule.Geometric
import Mathlib.Data.Finset.Sort

/-!
# Fresh roots supplied by a successful split trial

The first successful fixed-age population supplies a finite family of new
subtree roots.  An abstract linear order on addresses gives a canonical
enumeration; no child slot is distinguished.  A caller-provided family is
used off the success event, so the selector remains total.
-/

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed
namespace StepSelection
namespace SplitSchedule

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- Canonically enumerate `N` nodes from a finite population when enough are
available.  This deterministic operation contains no probabilistic or
measurability assumptions. -/
noncomputable def rootFamily
    {Root α : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (root : Root) (fallback : Fin N → Root × TreeNode α)
    (population : Finset (TreeNode α)) : Fin N → Root × TreeNode α :=
  if h : N ≤ population.card then
    fun i => (root, population.orderEmbOfCardLe h i)
  else fallback

/-- The first `N` nodes of the first successful fixed-age population.  When
there is no successful population, `fallback` supplies an arbitrary total
value.  Its validity is requested only by the corresponding structural
theorems. -/
noncomputable def roots
    {Root α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (root : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (ω : RootIndexed.StepField Root α X) :
    Fin N → Root × TreeNode α :=
  (firstSuccess R root duration target ω).recTopCoe fallback fun k =>
    rootFamily N (root k) fallback
      (RootIndexed.StepSelection.population R duration ω (root k))

theorem roots_of_firstSuccess_eq
    {Root α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (root : ℕ → Root) (duration target k : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (ω : RootIndexed.StepField Root α X)
    (hk : firstSuccess R root duration target ω = k)
    (hN : N ≤ (RootIndexed.StepSelection.population
      R duration ω (root k)).card) :
    roots N R root duration target fallback ω =
      fun i => (root k,
        (RootIndexed.StepSelection.population R duration ω (root k)
          ).orderEmbOfCardLe hN i) := by
  rw [roots, hk]
  change rootFamily N (root k) fallback
    (RootIndexed.StepSelection.population R duration ω (root k)) = _
  rw [rootFamily]
  rw [dite_eq_left hN]

theorem roots_injective
    {Root α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (root : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (hfallback : Function.Injective fallback)
    (ω : RootIndexed.StepField Root α X) :
    Function.Injective (roots N R root duration target fallback ω) := by
  induction hfirst : firstSuccess R root duration target ω using WithTop.recTopCoe with
  | top => simpa [roots, hfirst] using hfallback
  | coe k =>
      rw [roots, hfirst, WithTop.recTopCoe_coe]
      rw [rootFamily]
      split_ifs with h
      · intro i j hij
        exact (Finset.orderEmbOfCardLe _ h).injective
          (congrArg Prod.snd hij)
      · exact hfallback

theorem roots_depth
    {Root α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (root : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (hfallback : ∀ i, (fallback i).2.length = duration)
    (ω : RootIndexed.StepField Root α X) (i : Fin N) :
    ((roots N R root duration target fallback ω) i).2.length = duration := by
  induction hfirst : firstSuccess R root duration target ω using WithTop.recTopCoe with
  | top => simpa [roots, hfirst] using hfallback i
  | coe k =>
      rw [roots, hfirst, WithTop.recTopCoe_coe]
      rw [rootFamily]
      split_ifs with h
      · exact RootIndexed.StepSelection.population_depth R ω
          (Finset.orderEmbOfCardLe_mem _ h i)
      · exact hfallback i

/-- Every fiber of the successful-root selector is observable from the
generation `duration` domain flow.  The candidate root type is arbitrary.
Countability is needed only for finite address sets, which form the discrete
input of the deterministic enumeration performed after a trial is chosen. -/
theorem roots_fiber_adapted
    {Root α X : Type*} [Countable α] [MeasurableSpace X]
    [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X) (hR : Measurable R.select)
    (root : ℕ → Root) (duration target : ℕ)
    (fallback selected : Fin N → Root × TreeNode α) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) duration]
      {ω | roots N R root duration target fallback ω = selected} := by
  have hpopulation : ∀ k, Measurable[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) duration]
      (fun ω : RootIndexed.StepField Root α X =>
        RootIndexed.StepSelection.population R duration ω (root k)) := fun k =>
    (measurable_pi_apply (root k)).comp
      (RootIndexed.StepSelection.population_adapted R hR duration)
  have hchoose : ∀ k, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) duration]
      {ω : RootIndexed.StepField Root α X |
        rootFamily N (root k) fallback
          (RootIndexed.StepSelection.population R duration ω (root k)) =
            selected} := by
    intro k
    exact hpopulation k
      (DiscreteMeasurableSpace.forall_measurableSet
        {population : Finset (TreeNode α) |
          rootFamily N (root k) fallback population = selected})
  have hfiber : ∀ j : WithTop ℕ,
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) duration]
        {ω : RootIndexed.StepField Root α X |
          j.recTopCoe fallback (fun k => rootFamily N (root k) fallback
            (RootIndexed.StepSelection.population R duration ω (root k))) =
              selected} := by
    intro j
    induction j using WithTop.recTopCoe with
    | top => by_cases h : fallback = selected <;> simp [h]
    | coe k =>
        change MeasurableSet[RootIndexed.stepFiltration
          (Root := Root) (α := α) (X := X) duration]
          {ω : RootIndexed.StepField Root α X |
            rootFamily N (root k) fallback
              (RootIndexed.StepSelection.population R duration ω (root k)) =
                selected}
        exact hchoose k
  have hset :
      {ω : RootIndexed.StepField Root α X |
        roots N R root duration target fallback ω = selected} =
      ⋃ j : WithTop ℕ,
        {ω | firstSuccess R root duration target ω = j} ∩
          {ω | j.recTopCoe fallback (fun k => rootFamily N (root k) fallback
            (RootIndexed.StepSelection.population R duration ω (root k))) =
              selected} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      refine ⟨firstSuccess R root duration target ω, rfl, ?_⟩
      simpa [roots] using h
    · rintro ⟨j, hj, hselected⟩
      rw [roots, hj]
      exact hselected
  rw [hset]
  apply MeasurableSet.iUnion
  intro j
  induction j using WithTop.recTopCoe with
  | top =>
      exact (measurableSet_firstSuccess_eq_top_adapted
        R hR root duration target).inter (hfiber ⊤)
  | coe k =>
      exact (measurableSet_firstSuccess_eq_adapted
        R hR root duration target k).inter (hfiber k)

/-- The selector has countable range even when `Root` itself is uncountable:
each finite-success branch is the image of the countable type of finite
address sets, and the no-success branch contributes one extra value. -/
theorem roots_range_countable
    {Root α X : Type*} [Countable α] [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (root : ℕ → Root) (duration target : ℕ)
    (fallback : Fin N → Root × TreeNode α) :
    (Set.range (roots N R root duration target fallback)).Countable := by
  let candidates : Set (Fin N → Root × TreeNode α) :=
    {fallback} ∪ ⋃ k : ℕ,
      Set.range (fun population : Finset (TreeNode α) =>
        rootFamily N (root k) fallback population)
  have hcandidates : candidates.Countable :=
    (Set.countable_singleton fallback).union <|
      Set.countable_iUnion fun k => Set.countable_range
        (fun population : Finset (TreeNode α) =>
          rootFamily N (root k) fallback population)
  apply hcandidates.mono
  rintro selected ⟨ω, rfl⟩
  induction hfirst : firstSuccess R root duration target ω using WithTop.recTopCoe with
  | top =>
      left
      simp [roots, hfirst]
  | coe k =>
      right
      refine Set.mem_iUnion.2 ⟨k, ?_⟩
      refine ⟨RootIndexed.StepSelection.population R duration ω (root k), ?_⟩
      rw [roots, hfirst]
      rfl

theorem roots_mem_population_of_firstSuccess_eq
    {Root α X : Type*} [LinearOrder (TreeNode α)]
    (N : ℕ) (R : Step.FiniteSelection α X)
    (root : ℕ → Root) (duration target k : ℕ)
    (fallback : Fin N → Root × TreeNode α)
    (ω : RootIndexed.StepField Root α X)
    (hk : firstSuccess R root duration target ω = k)
    (hNtarget : N ≤ target) (i : Fin N) :
    (roots N R root duration target fallback ω i).1 = root k ∧
      (roots N R root duration target fallback ω i).2 ∈
        RootIndexed.StepSelection.population R duration ω (root k) := by
  have hsuccess := (firstSuccess_eq_iff R root duration target k ω).mp hk |>.1
  have hN : N ≤ (RootIndexed.StepSelection.population
      R duration ω (root k)).card := hNtarget.trans hsuccess
  rw [roots_of_firstSuccess_eq N R root duration target k fallback ω hk hN]
  exact ⟨rfl, Finset.orderEmbOfCardLe_mem _ hN i⟩

end SplitSchedule
end StepSelection
end RootIndexed
end ProbabilityTheory.BranchingRandomWalk
