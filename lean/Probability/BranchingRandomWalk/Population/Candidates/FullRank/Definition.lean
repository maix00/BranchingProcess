import Probability.BranchingRandomWalk.Population.Processes.Selected
import Combinatorics.BranchingWalk.Step.Monotone
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law

/-!
# Rank among all countably many children

The full one-step child set is countable and may be infinite. A child at slot
`j ≥ N` cannot be among the first `N` children globally: its own parent
supplies `N` distinct realized earlier siblings, all strictly ahead under the
position-consistent tie key.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


/-- All realized children of a finite labelled parent set, without a slot
cutoff. -/
def allMultiRootChildren {m : ℕ}
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ ℝ) :
    Set (RootAddress m ℕ) :=
  {q | ∃ p ∈ s, ∃ j : ℕ,
    survive (ω p.1 p.2) j ∧ q = childAddress p j}

theorem multiRootCandidates_subset_all {m : ℕ}
    (N : ℕ) (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ ℝ) :
    ↑(multiRootCandidates N s ω) ⊆ allMultiRootChildren s ω := by
  intro q hq
  unfold multiRootCandidates at hq
  obtain ⟨p, hp, hq'⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨j, _, hqj⟩ := Finset.mem_biUnion.mp hq'
  obtain ⟨hj, rfl⟩ :=
    (mem_oneChildCandidate_iff ω p q j).1 hqj
  exact ⟨p, hp, j, hj, rfl⟩

/-- A particle is among the first `N` of a possibly infinite set when there
is no finite set of `N` distinct candidates strictly ahead of it. -/
def fullRankBelow {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (ω : FiniteRootStepField m ℕ ℝ) (s : Set (RootAddress m ℕ))
    (q : RootAddress m ℕ) : Prop :=
  ¬∃ t : Finset (RootAddress m ℕ), t.card = N ∧
    ∀ r ∈ t, r ∈ s ∧ candidateEarlier x ω r q

theorem childAddress_injective {m : ℕ} (p : RootAddress m ℕ) :
    Function.Injective (childAddress p) := by
  intro i j hij
  have hpath : p.2 ++ [i] = p.2 ++ [j] :=
    (Prod.mk.inj hij).2
  have hsingle : [i] = [j] := List.append_cancel_left hpath
  simpa using hsingle

/-- Every realized slot beyond the finite cutoff has `N` strictly earlier
realized siblings in the full child set. -/
theorem lateChild_not_fullRankBelow {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ ℝ)
    (p : RootAddress m ℕ) (hp : p ∈ s)
    (horder : Step.IsOrdered (ω p.1 p.2))
    (j : ℕ) (hNj : N ≤ j)
    (hj : survive (ω p.1 p.2) j) :
    ¬fullRankBelow N x ω (allMultiRootChildren s ω)
      (childAddress p j) := by
  intro hbelow
  apply hbelow
  let t : Finset (RootAddress m ℕ) :=
    (Finset.range N).image (childAddress p)
  refine ⟨t, ?_, ?_⟩
  · dsimp [t]
    rw [Finset.card_image_of_injective _ (childAddress_injective p)]
    simp
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    have hij : i < j := lt_of_lt_of_le (Finset.mem_range.mp hi) hNj
    have hreal : survive (ω p.1 p.2) i :=
      Step.IsSiblingClosed.survive_of_lt horder.1 hij hj
    constructor
    · exact ⟨p, hp, i, hreal, rfl⟩
    · exact candidateEarlier_ordered_siblings x ω p horder hij hj

end ProbabilityTheory.BranchingRandomWalk
