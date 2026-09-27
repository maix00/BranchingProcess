import Combinatorics.UlamHarris.Split
import Probability.BranchingRandomWalk.Timing.DeclaredSplit
import Probability.BranchingRandomWalk.Timing.Measurability

/-!
# Pre-sampled reserve lineages

All potential reserve lineages are defined on one marked tree before any trial
outcome is inspected.  Trial labels, child slots, and marks are independent
type parameters.  Countability is requested only by the measurable random
coordinate and countable-union arguments that use it.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris MeasureTheory

/-- A family of causal full-depth lineages on one pre-sampled marked tree. -/
structure ReserveLineages (Trial α M : Type*) [MeasurableSpace M] where
  path : Trial → ℕ → Mark α M → TreeNode α
  step : Trial → TreeNode α × M → TreeNode α
  measurable_step : ∀ i, Measurable (step i)
  measurable_root : ∀ i,
    Measurable[generationFiltration (M := M) 0] (path i 0)
  depth : ∀ i n ω, (path i n ω).length = n
  recursion : ∀ i n ω,
    path i (n + 1) ω = step i (path i n ω, ω (path i n ω))

theorem ReserveLineages.path_adapted
    {Trial α M : Type*} [Countable α] [MeasurableSpace M]
    (r : ReserveLineages Trial α M) (i : Trial) :
    ∀ n, Measurable[generationFiltration (M := M) n] (r.path i n) :=
  causal_lineage_adapted (r.path i) (r.step i) (r.measurable_step i)
    (r.measurable_root i) (r.depth i) (r.recursion i)

/-- The first generation at which the mark on a reserve lineage belongs to a
measurable declaration set.  It is defined for every trial independently of
whether an earlier trial succeeds. -/
noncomputable def ReserveLineages.sigma
    {Trial α M : Type*} [MeasurableSpace M]
    (r : ReserveLineages Trial α M) (splitMark : Set M) (i : Trial) :
    Mark α M → WithTop ℕ :=
  firstDeclaredSuccess (splitDeclaration (r.path i) splitMark)

theorem ReserveLineages.sigma_isStoppingTime
    {Trial α M : Type*} [Countable α] [MeasurableSpace M]
    (r : ReserveLineages Trial α M) (splitMark : Set M)
    (hsplit : MeasurableSet splitMark) (i : Trial) :
    IsStoppingTime (generationFiltration (M := M)) (r.sigma splitMark i) :=
  first_split_generation_isStoppingTime (r.path i) (r.path_adapted i)
    (r.depth i) splitMark hsplit

theorem ReserveLineages.all_sigma_isStoppingTime
    {Trial α M : Type*} [Countable α] [MeasurableSpace M]
    (r : ReserveLineages Trial α M) (splitMark : Set M)
    (hsplit : MeasurableSet splitMark) :
    ∀ i, IsStoppingTime (generationFiltration (M := M))
      (r.sigma splitMark i) :=
  r.sigma_isStoppingTime splitMark hsplit

/-- Observable at-completion tests make the first successful declaration a
stopping time for any countable trial family. -/
theorem ReserveLineages.first_success_isStoppingTime
    {Trial α M : Type*} [Countable Trial] [Countable α] [MeasurableSpace M]
    (r : ReserveLineages Trial α M) (splitMark : Set M)
    (hsplit : MeasurableSet splitMark)
    (test : Trial → ℕ → Set (Mark α M))
    (htest : ∀ i n,
      MeasurableSet[generationFiltration (M := M) n] (test i n)) :
    IsStoppingTime (generationFiltration (M := M))
      (firstDeclaredSuccess fun n =>
        {ω | ∃ i, r.sigma splitMark i ω = n ∧
          ω ∈ successAtCompletion (r.sigma splitMark i) (test i)}) :=
  first_successful_candidate_isStoppingTime
    (generationFiltration (M := M)) (r.sigma splitMark) test
    (r.all_sigma_isStoppingTime splitMark hsplit) htest

/-- Success by generation `T` inside an arbitrary subset of a countable trial
family is measurable at generation `T`. -/
theorem ReserveLineages.successfulWithin_measurable
    {Trial α M : Type*} [Countable Trial] [Countable α] [MeasurableSpace M]
    (r : ReserveLineages Trial α M) (splitMark : Set M)
    (hsplit : MeasurableSet splitMark)
    (test : Trial → ℕ → Set (Mark α M))
    (htest : ∀ i n,
      MeasurableSet[generationFiltration (M := M) n] (test i n))
    (trials : Set Trial) (T : ℕ) :
    MeasurableSet[generationFiltration (M := M) T]
      (successfulCandidateWithin (r.sigma splitMark)
        (fun i => successAtCompletion (r.sigma splitMark i) (test i))
        trials T) :=
  successfulCandidateWithin_measurable
    (generationFiltration (M := M)) (r.sigma splitMark)
      (fun i => successAtCompletion (r.sigma splitMark i) (test i))
      (successAtCompletion_observable
        (generationFiltration (M := M)) (r.sigma splitMark) test
        (r.all_sigma_isStoppingTime splitMark hsplit) htest) trials T

theorem ReserveLineages.failureWithin_measurable
    {Trial α M : Type*} [Countable Trial] [Countable α] [MeasurableSpace M]
    (r : ReserveLineages Trial α M) (splitMark : Set M)
    (hsplit : MeasurableSet splitMark)
    (test : Trial → ℕ → Set (Mark α M))
    (htest : ∀ i n,
      MeasurableSet[generationFiltration (M := M) n] (test i n))
    (trials : Set Trial) (T : ℕ) :
    MeasurableSet[generationFiltration (M := M) T]
      (successfulCandidateWithin (r.sigma splitMark)
        (fun i => successAtCompletion (r.sigma splitMark i) (test i))
        trials T)ᶜ :=
  (r.successfulWithin_measurable splitMark hsplit test htest trials T).compl

end ProbabilityTheory.BranchingRandomWalk
