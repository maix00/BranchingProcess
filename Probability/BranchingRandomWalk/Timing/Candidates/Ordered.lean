/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.HittingTime.ObservableCandidates
public import Probability.Process.Adapted.Recursion

/-!
# Ordered pre-sampled candidate declarations

All candidates and their completion times are defined independently of which
earlier candidate succeeds.  At generation `n`, an ordered declaration keeps
a successful completion only when no preceding candidate has already
declared success by `n`.  This is the causal version of the usual
"first successful trial" formula.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

/-- Candidate `i` has declared success by generation `n`. -/
def candidateSucceededBy
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (i : ι) (n : ℕ) : Set Ω :=
  {ω | ∃ k ≤ n, completion i ω = k ∧ ω ∈ success i}

theorem candidateSucceededBy_measurable
    (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success) (i : ι) (n : ℕ) :
    MeasurableSet[F n] (candidateSucceededBy completion success i n) := by
  have hset : candidateSucceededBy completion success i n =
      ⋃ k : ℕ, ⋃ (_ : k ≤ n),
        {ω | completion i ω = (k : WithTop ℕ) ∧ ω ∈ success i} := by
    ext ω
    simp only [candidateSucceededBy, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk, hc, hs⟩
      exact ⟨k, hk, hc, hs⟩
    · rintro ⟨k, hk, hc, hs⟩
      exact ⟨k, hk, hc, hs⟩
  rw [hset]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun hk =>
    F.mono hk _ (h i k)

/-- A preceding candidate in `candidates` has declared success by generation
`n`.  The relation `before` need not be a global order. -/
def earlierCandidateSucceededBy
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (candidates : Set ι) (before : ι → ι → Prop)
    (i : ι) (n : ℕ) : Set Ω :=
  {ω | ∃ j ∈ candidates, before j i ∧
    ω ∈ candidateSucceededBy completion success j n}

theorem earlierCandidateSucceededBy_measurable
    (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success)
    (candidates : Set ι) (hcandidates : candidates.Countable)
    (before : ι → ι → Prop) (i : ι) (n : ℕ) :
    MeasurableSet[F n]
      (earlierCandidateSucceededBy completion success candidates before i n) := by
  let _ : Countable candidates := Set.countable_coe_iff.mpr hcandidates
  have hset :
      earlierCandidateSucceededBy completion success candidates before i n =
        ⋃ j : candidates, ⋃ (_ : before j.1 i),
          candidateSucceededBy completion success j.1 n := by
    ext ω
    simp only [earlierCandidateSucceededBy, Set.mem_ofPred_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj, hji, hs⟩
      exact ⟨⟨j, hj⟩, hji, hs⟩
    · rintro ⟨j, hji, hs⟩
      exact ⟨j.1, j.2, hji, hs⟩
  rw [hset]
  exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ =>
    candidateSucceededBy_measurable F completion success h j.1 n

/-- Successful completions at generation `n` whose preceding candidates have
not declared success by that generation. -/
def orderedCandidateDeclarationWithin
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (candidates : Set ι) (before : ι → ι → Prop)
    (n : ℕ) : Set Ω :=
  {ω | ∃ i ∈ candidates,
    completion i ω = n ∧ ω ∈ success i ∧
      ω ∉ earlierCandidateSucceededBy
        completion success candidates before i n}

theorem orderedCandidateDeclarationWithin_measurable
    (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success)
    (candidates : Set ι) (hcandidates : candidates.Countable)
    (before : ι → ι → Prop) (n : ℕ) :
    MeasurableSet[F n]
      (orderedCandidateDeclarationWithin
        completion success candidates before n) := by
  let _ : Countable candidates := Set.countable_coe_iff.mpr hcandidates
  have hset :
      orderedCandidateDeclarationWithin
          completion success candidates before n =
        ⋃ i : candidates,
          {ω | completion i.1 ω = (n : WithTop ℕ) ∧ ω ∈ success i.1} \
            earlierCandidateSucceededBy
              completion success candidates before i.1 n := by
    ext ω
    simp only [orderedCandidateDeclarationWithin, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_sdiff]
    constructor
    · rintro ⟨i, hi, hc, hs, hearlier⟩
      exact ⟨⟨i, hi⟩, ⟨hc, hs⟩, hearlier⟩
    · rintro ⟨i, ⟨hc, hs⟩, hearlier⟩
      exact ⟨i.1, i.2, hc, hs, hearlier⟩
  rw [hset]
  exact MeasurableSet.iUnion fun i =>
    (h i.1 n).diff
      (earlierCandidateSucceededBy_measurable F completion success h
        candidates hcandidates before i.1 n)

/-- The first ordered successful declaration of a countable pre-sampled
candidate family is a stopping time. -/
theorem firstOrderedCandidateCompletionWithin_isStoppingTime
    (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success)
    (candidates : Set ι) (hcandidates : candidates.Countable)
    (before : ι → ι → Prop) :
    IsStoppingTime F
      (firstDeclaredSuccess
        (orderedCandidateDeclarationWithin
          completion success candidates before)) :=
  firstDeclaredSuccess_isStoppingTime F _ fun n =>
    orderedCandidateDeclarationWithin_measurable F completion success h
      candidates hcandidates before n

/-- If preceding candidates finish no later than the current candidate, the
observable "no earlier success by completion" condition is exactly the usual
condition that every preceding candidate failed. -/
theorem mem_orderedCandidateDeclarationWithin_iff
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (candidates : Set ι) (before : ι → ι → Prop)
    (hmono : ∀ ω i j, i ∈ candidates → j ∈ candidates → before j i →
      completion j ω ≤ completion i ω)
    (n : ℕ) (ω : Ω) :
    ω ∈ orderedCandidateDeclarationWithin
        completion success candidates before n ↔
      ∃ i ∈ candidates,
        completion i ω = n ∧ ω ∈ success i ∧
          ∀ j ∈ candidates, before j i → ω ∉ success j := by
  constructor
  · rintro ⟨i, hi, hcompletion, hsuccess, hearlier⟩
    refine ⟨i, hi, hcompletion, hsuccess, ?_⟩
    intro j hj hji hsuccessj
    apply hearlier
    have hle : completion j ω ≤ (n : WithTop ℕ) := by
      simpa [hcompletion] using hmono ω i j hi hj hji
    have hne : completion j ω ≠ ⊤ := by
      intro htop
      simp [htop] at hle
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hne
    have hkn : k ≤ n := by
      apply WithTop.coe_le_coe.mp
      simpa [hk] using hle
    exact ⟨j, hj, hji, k, hkn, hk.symm, hsuccessj⟩
  · rintro ⟨i, hi, hcompletion, hsuccess, hfailed⟩
    refine ⟨i, hi, hcompletion, hsuccess, ?_⟩
    rintro ⟨j, hj, hji, k, hk, hcompletionj, hsuccessj⟩
    exact hfailed j hj hji hsuccessj

end ProbabilityTheory.BranchingRandomWalk
