module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Measurability
public import Probability.BranchingRandomWalk.Population.Candidates.Prefix

/-!
# Finite child candidates from several initial ancestors

At a selection step with capacity `N`, only the first `N` child slots of
each retained parent are inspected. Under the ordered-child-set support
condition, later slots cannot enter the global leftmost `N`; that reduction
still needs a proof. The survive file establishes the finite candidate set
and its causal measurability. The mark type is a parameter: candidate
generation only reads slot presence.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



variable {X : Type*}

/-- All candidate children of a finite parent population. Every parent
contributes at most the first `N` slots. -/
noncomputable def multiRootCandidates {m : ℕ} (N : ℕ)
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ X) :
    Finset (RootAddress m ℕ) := by
  classical
  exact s.biUnion (fun p =>
    (Finset.range N).biUnion (oneChildCandidate ω p))

theorem oneChildCandidate_measurable {m n : ℕ} [MeasurableSpace X]
    (p : RootAddress m ℕ) (hp : p.2.length = n) (j : ℕ) :
    Measurable[multiRootStepFiltration (m := m) (X := X) (n + 1)]
      (fun ω : FiniteRootStepField m ℕ X => oneChildCandidate ω p j) := by
  classical
  have htest : MeasurableSet[multiRootStepFiltration (m := m) (X := X) (n + 1)]
      {ω : FiniteRootStepField m ℕ X | survive (ω p.1 p.2) j} :=
    (multiRootStep_measurable (X := X) p.1 p.2
      (by rw [hp]; exact Nat.lt_succ_self n))
      (survive_measurableSet (X := X) j)
  unfold oneChildCandidate
  exact measurable_const.ite htest measurable_const

theorem multiRootCandidates_fixed_measurable {m n : ℕ} [MeasurableSpace X] (N : ℕ)
    (s : Finset (RootAddress m ℕ))
    (hs : ∀ p ∈ s, p.2.length = n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) (n + 1)]
      (fun ω : FiniteRootStepField m ℕ X => multiRootCandidates N s ω) := by
  classical
  have hunion : Measurable
      (fun p : Finset (RootAddress m ℕ) × Finset (RootAddress m ℕ) =>
        p.1 ∪ p.2) := measurable_of_countable _
  have hparent (p : RootAddress m ℕ) (hp : p.2.length = n) :
      Measurable[multiRootStepFiltration (m := m) (X := X) (n + 1)]
        (fun ω : FiniteRootStepField m ℕ X =>
          (Finset.range N).biUnion (oneChildCandidate ω p)) := by
    induction Finset.range N using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih =>
        have h := hunion.comp
          ((oneChildCandidate_measurable p hp j).prodMk ih)
        simpa only [Finset.biUnion_insert, Function.comp_def] using h
  induction s using Finset.induction_on with
  | empty => simp [multiRootCandidates]
  | @insert p t hpt ih =>
      have hp : p.2.length = n := hs p (Finset.mem_insert_self p t)
      have ht : ∀ q ∈ t, q.2.length = n := by
        intro q hq
        exact hs q (Finset.mem_insert_of_mem hq)
      have h := hunion.comp ((hparent p hp).prodMk (ih ht))
      simpa only [multiRootCandidates, Finset.biUnion_insert,
        Function.comp_def] using h

/-- Filter out addresses of the wrong generation before exposing marks.
For a genuine selected population this filter is the identity; it makes
the update measurable for every possible finite-set input. -/
noncomputable def multiRootCandidatesAtGeneration {m : ℕ}
    (N n : ℕ) (s : Finset (RootAddress m ℕ))
    (ω : FiniteRootStepField m ℕ X) : Finset (RootAddress m ℕ) := by
  classical
  exact multiRootCandidates N (s.filter (fun p => p.2.length = n)) ω

theorem multiRootCandidatesAtGeneration_fixed_measurable {m : ℕ} [MeasurableSpace X]
    (N n : ℕ) (s : Finset (RootAddress m ℕ)) :
    Measurable[multiRootStepFiltration (m := m) (X := X) (n + 1)]
      (multiRootCandidatesAtGeneration N n s) := by
  classical
  unfold multiRootCandidatesAtGeneration
  exact multiRootCandidates_fixed_measurable N _
    (by intro p hp; exact (Finset.mem_filter.mp hp).2)

theorem oneChildCandidate_first_mem {m : ℕ}
    (ω : FiniteRootStepField m ℕ X) (p : RootAddress m ℕ) :
    childAddress p 0 ∈ oneChildCandidate ω p 0 ↔
      survive (ω p.1 p.2) 0 := by
  classical
  by_cases h : survive (ω p.1 p.2) 0 <;>
    simp [oneChildCandidate, h]

theorem multiRootCandidates_first_mem {m N : ℕ}
    (hN : 0 < N) (s : Finset (RootAddress m ℕ))
    (ω : FiniteRootStepField m ℕ X) (p : RootAddress m ℕ) (hp : p ∈ s)
    (hfirst : survive (ω p.1 p.2) 0) :
    childAddress p 0 ∈ multiRootCandidates N s ω := by
  classical
  unfold multiRootCandidates
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hp, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨0, Finset.mem_range.mpr hN,
    (oneChildCandidate_first_mem ω p).2 hfirst⟩

theorem multiRootCandidates_depth {m n : ℕ} (N : ℕ)
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ X)
    (hs : ∀ p ∈ s, p.2.length = n)
    (q : RootAddress m ℕ) (hq : q ∈ multiRootCandidates N s ω) :
    q.2.length = n + 1 := by
  classical
  unfold multiRootCandidates at hq
  obtain ⟨p, hp, j, hj, hqj⟩ := by
    simpa only [Finset.mem_biUnion] using hq
  exact oneChildCandidate_depth ω p q j (hs p hp) hqj

theorem multiRootCandidatesAtGeneration_depth {m : ℕ} (N n : ℕ)
    (s : Finset (RootAddress m ℕ)) (ω : FiniteRootStepField m ℕ X)
    (q : RootAddress m ℕ)
    (hq : q ∈ multiRootCandidatesAtGeneration N n s ω) :
    q.2.length = n + 1 := by
  classical
  unfold multiRootCandidatesAtGeneration at hq
  exact multiRootCandidates_depth N _ ω
    (by intro p hp; exact (Finset.mem_filter.mp hp).2) q hq

end ProbabilityTheory.BranchingRandomWalk
