import Combinatorics.UlamHarris.Split
import Combinatorics.BranchingWalk.Step.Measurability
import Probability.BranchingRandomWalk.Timing.FirstSplit
import Probability.BranchingRandomWalk.Timing.Measurability

/-!
# Pre-sampled reserve lineages

Every reserve lineage is defined on the same marked Ulam--Harris tree before
any trial outcome is inspected. The family is indexed independently of
success or failure of earlier trials, so its visible split time is a
generation stopping time, and the first successful tested completion is one
too. The multi-root version is in `Lineage/MultiRoot.lean`.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



/-! Generic reserve lineages.  The concrete `Step ℕ ℝ` construction below
    is retained as an application layer; the measurability argument itself is
    independent of point-process coordinates. -/
structure AbstractReserveLineages (M : Type*) [MeasurableSpace M] where
  path : ℕ → ℕ → Mark ℕ M → 𝕍
  step : ℕ → 𝕍 × M → 𝕍
  measurable_step : ∀ i, Measurable (step i)
  measurable_root : ∀ i,
    Measurable[generationFiltration (M := M) 0] (path i 0)
  depth : ∀ i n ω, (path i n ω).length = n
  recursion : ∀ i n ω,
    path i (n + 1) ω = step i (path i n ω, ω (path i n ω))

theorem AbstractReserveLineages.path_adapted
    {M : Type*} [MeasurableSpace M]
    (r : AbstractReserveLineages M) (i : ℕ) :
    ∀ n, Measurable[generationFiltration (M := M) n]
      (r.path i n) :=
  causal_lineage_adapted (r.path i) (r.step i) (r.measurable_step i)
    (r.measurable_root i) (r.depth i) (r.recursion i)

/-- A countable family of causal full-depth lineages on one pre-sampled tree.
The index labels potential reserve trials; all indices exist on every sample. -/
structure ReserveLineages where
  path : ℕ → ℕ → Mark ℕ (Step ℕ ℝ) → 𝕍
  step : ℕ → 𝕍 × Step ℕ ℝ → 𝕍
  measurable_step : ∀ i, Measurable (step i)
  measurable_root : ∀ i,
    Measurable[generationFiltration (M := Step ℕ ℝ) 0] (path i 0)
  depth : ∀ i n ω, (path i n ω).length = n
  recursion : ∀ i n ω,
    path i (n + 1) ω = step i (path i n ω, ω (path i n ω))

theorem ReserveLineages.path_adapted (r : ReserveLineages) (i : ℕ) :
    ∀ n, Measurable[generationFiltration (M := Step ℕ ℝ) n]
      (r.path i n) :=
  causal_lineage_adapted (r.path i) (r.step i) (r.measurable_step i)
    (r.measurable_root i) (r.depth i) (r.recursion i)

/-- `σᵢ` is the generation at which the first split of reserve lineage `i`
is observable. It is defined even when an earlier reserve succeeds. -/
noncomputable def ReserveLineages.sigma (r : ReserveLineages) (i : ℕ) :
    Mark ℕ (Step ℕ ℝ) → WithTop ℕ :=
  firstDeclaredSuccess (splitDeclaration (r.path i) nontrivialSupport)

theorem ReserveLineages.sigma_isStoppingTime
    (r : ReserveLineages) (i : ℕ) :
    IsStoppingTime (generationFiltration (M := Step ℕ ℝ))
      (r.sigma i) :=
  first_bifurcation_isStoppingTime (r.path i) (r.path_adapted i)
    (r.depth i)

/-- Every candidate split time is available to the generic observable-trial
interface simultaneously. -/
theorem ReserveLineages.all_sigma_isStoppingTime (r : ReserveLineages) :
    ∀ i, IsStoppingTime (generationFiltration (M := Step ℕ ℝ))
      (r.sigma i) :=
  r.sigma_isStoppingTime

/-- If the success test for reserve `i` at generation `n` is measurable at
that generation, then the first successful reserve completion is a stopping
time. The unsuccessful and unused reserves remain pre-defined. -/
theorem ReserveLineages.first_success_isStoppingTime
    (r : ReserveLineages)
    (test : ℕ → ℕ → Set (Mark ℕ (Step ℕ ℝ)))
    (htest : ∀ i n,
      MeasurableSet[generationFiltration (M := Step ℕ ℝ) n]
        (test i n)) :
    IsStoppingTime (generationFiltration (M := Step ℕ ℝ))
      (firstDeclaredSuccess fun n =>
        {ω | ∃ i, r.sigma i ω = n ∧
          ω ∈ successAtCompletion (r.sigma i) (test i)}) :=
  first_successful_candidate_isStoppingTime
    (generationFiltration (M := Step ℕ ℝ)) r.sigma test
    r.all_sigma_isStoppingTime htest

/-- The restart event that one of the first candidate reserves succeeds by a
fixed generation belongs to that generation's domain.  Thus the event used in
the exceptional-event estimate is derived from the causal tests rather than
postulated measurable. -/
theorem ReserveLineages.successfulBy_measurable
    (r : ReserveLineages)
    (test : ℕ → ℕ → Set (Mark ℕ (Step ℕ ℝ)))
    (htest : ∀ i n,
      MeasurableSet[generationFiltration (M := Step ℕ ℝ) n]
        (test i n)) (K T : ℕ) :
    MeasurableSet[generationFiltration (M := Step ℕ ℝ) T]
      (successfulCandidateBy r.sigma
        (fun i => successAtCompletion (r.sigma i) (test i)) K T) :=
  successfulCandidateBy_measurable
    (generationFiltration (M := Step ℕ ℝ)) r.sigma
      (fun i => successAtCompletion (r.sigma i) (test i))
      (successAtCompletion_observable
        (generationFiltration (M := Step ℕ ℝ)) r.sigma test
        r.all_sigma_isStoppingTime htest) K T

theorem ReserveLineages.failureBy_measurable
    (r : ReserveLineages)
    (test : ℕ → ℕ → Set (Mark ℕ (Step ℕ ℝ)))
    (htest : ∀ i n,
      MeasurableSet[generationFiltration (M := Step ℕ ℝ) n]
        (test i n)) (K T : ℕ) :
    MeasurableSet[generationFiltration (M := Step ℕ ℝ) T]
      (successfulCandidateBy r.sigma
        (fun i => successAtCompletion (r.sigma i) (test i)) K T)ᶜ :=
  (r.successfulBy_measurable test htest K T).compl

end ProbabilityTheory.BranchingRandomWalk
