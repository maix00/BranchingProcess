import ThesisSpeed.Probability.Genealogy.Tree.Split
import ThesisSpeed.Probability.PointProcess.Legacy.FirstSplitWeighted
import ThesisSpeed.Probability.Timing.Measurability

/-!
# Pre-sampled reserve lineages

Every reserve lineage is defined on the same marked Ulam--Harris tree before
any trial outcome is inspected. The family is indexed independently of
success or failure of earlier trials, so its visible split time is a
generation stopping time, and the first successful tested completion is one
too. The multi-root version is in `Reserve/MultiRoot.lean`.
-/

open MeasureTheory

namespace ThesisSpeed

/-! Generic reserve lineages.  The concrete `WeightedBranchingStep` construction below
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
  path : ℕ → ℕ → Mark ℕ WeightedBranchingStep → 𝕍
  step : ℕ → 𝕍 × WeightedBranchingStep → 𝕍
  measurable_step : ∀ i, Measurable (step i)
  measurable_root : ∀ i,
    Measurable[generationFiltration (M := WeightedBranchingStep) 0] (path i 0)
  depth : ∀ i n ω, (path i n ω).length = n
  recursion : ∀ i n ω,
    path i (n + 1) ω = step i (path i n ω, ω (path i n ω))

theorem ReserveLineages.path_adapted (r : ReserveLineages) (i : ℕ) :
    ∀ n, Measurable[generationFiltration (M := WeightedBranchingStep) n]
      (r.path i n) :=
  causal_lineage_adapted (r.path i) (r.step i) (r.measurable_step i)
    (r.measurable_root i) (r.depth i) (r.recursion i)

/-- `σᵢ` is the generation at which the first split of reserve lineage `i`
is observable. It is defined even when an earlier reserve succeeds. -/
noncomputable def ReserveLineages.sigma (r : ReserveLineages) (i : ℕ) :
    Mark ℕ WeightedBranchingStep → WithTop ℕ :=
  firstDeclaredSuccess (splitDeclaration (r.path i) twoChildren)

theorem ReserveLineages.sigma_isStoppingTime
    (r : ReserveLineages) (i : ℕ) :
    IsStoppingTime (generationFiltration (M := WeightedBranchingStep))
      (r.sigma i) :=
  first_bifurcation_isStoppingTime (r.path i) (r.path_adapted i)
    (r.depth i)

/-- Every candidate split time is available to the generic observable-trial
interface simultaneously. -/
theorem ReserveLineages.all_sigma_isStoppingTime (r : ReserveLineages) :
    ∀ i, IsStoppingTime (generationFiltration (M := WeightedBranchingStep))
      (r.sigma i) :=
  r.sigma_isStoppingTime

/-- If the success test for reserve `i` at generation `n` is measurable at
that generation, then the first successful reserve completion is a stopping
time. The unsuccessful and unused reserves remain pre-defined. -/
theorem ReserveLineages.first_success_isStoppingTime
    (r : ReserveLineages)
    (test : ℕ → ℕ → Set (Mark ℕ WeightedBranchingStep))
    (htest : ∀ i n,
      MeasurableSet[generationFiltration (M := WeightedBranchingStep) n]
        (test i n)) :
    IsStoppingTime (generationFiltration (M := WeightedBranchingStep))
      (firstDeclaredSuccess fun n =>
        {ω | ∃ i, r.sigma i ω = n ∧
          ω ∈ successAtCompletion (r.sigma i) (test i)}) :=
  first_successful_candidate_isStoppingTime
    (generationFiltration (M := WeightedBranchingStep)) r.sigma test
    r.all_sigma_isStoppingTime htest

end ThesisSpeed
