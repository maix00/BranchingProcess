module

public import Mathlib.Probability.Process.HittingTime
public import Probability.Process.HittingTime.Declarations

/-!
# Observable candidate declarations

These lemmas express when a candidate's completion and success are visible at
the generation where they occur. Countability is imposed only on the family
whose success events are joined.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A candidate is observable when success at each finite completion time is
measurable at that time. -/
def CandidateObservable {ι : Type*} (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω) : Prop :=
  ∀ i n, MeasurableSet[F n] {ω | completion i ω = n ∧ ω ∈ success i}

/-- A candidate succeeds when its test holds at its actual finite completion
time. The test remains defined even if another candidate succeeds earlier. -/
def successAtCompletion (completion : Ω → WithTop ℕ)
    (test : ℕ → Set Ω) : Set Ω :=
  {ω | ∃ n : ℕ, completion ω = (n : WithTop ℕ) ∧ ω ∈ test n}

/-- A stopping completion and an adapted generation test imply the required
joint-event measurability. -/
theorem successAtCompletion_observable {ι : Type*} (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ)
    (test : ι → ℕ → Set Ω)
    (hcompletion : ∀ i, IsStoppingTime F (completion i))
    (htest : ∀ i n, MeasurableSet[F n] (test i n)) :
    CandidateObservable F completion
      (fun i => successAtCompletion (completion i) (test i)) := by
  intro i n
  have heq :
      {ω | completion i ω = n ∧
        ω ∈ successAtCompletion (completion i) (test i)} =
      {ω | completion i ω = n} ∩ test i n := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, successAtCompletion]
    constructor
    · rintro ⟨hn, k, hk, htestk⟩
      have : k = n := by
        apply WithTop.coe_injective
        calc
          (k : WithTop ℕ) = completion i ω := hk.symm
          _ = (n : WithTop ℕ) := hn
      exact ⟨hn, this ▸ htestk⟩
    · rintro ⟨hn, htestn⟩
      exact ⟨hn, n, hn, htestn⟩
  rw [heq]
  exact (hcompletion i).measurableSet_eq n |>.inter (htest i n)

/-- The declarations of countably many candidates form a measurable event at
each generation. -/
theorem candidate_declaration_measurable {ι : Type*} [Countable ι]
    (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success) (n : ℕ) :
    MeasurableSet[F n]
      {ω | ∃ i, completion i ω = n ∧ ω ∈ success i} := by
  have hset :
      {ω | ∃ i, completion i ω = n ∧ ω ∈ success i} =
        ⋃ i : ι, {ω | completion i ω = n ∧ ω ∈ success i} := by
    ext ω
    simp
  rw [hset]
  exact MeasurableSet.iUnion fun i => h i n

/-- The event that one of the first `K + 1` pre-sampled candidates succeeds
by generation `T`. -/
def successfulCandidateBy
    (completion : ℕ → Ω → WithTop ℕ) (success : ℕ → Set Ω)
    (K T : ℕ) : Set Ω :=
  {ω | ∃ i ≤ K, ∃ n ≤ T,
    completion i ω = (n : WithTop ℕ) ∧ ω ∈ success i}

theorem successfulCandidateBy_measurable (F : Filtration ℕ m)
    (completion : ℕ → Ω → WithTop ℕ) (success : ℕ → Set Ω)
    (h : CandidateObservable F completion success) (K T : ℕ) :
    MeasurableSet[F T] (successfulCandidateBy completion success K T) := by
  have hset : successfulCandidateBy completion success K T =
      ⋃ i : ℕ, ⋃ (_ : i ≤ K), ⋃ n : ℕ, ⋃ (_ : n ≤ T),
        {ω | completion i ω = (n : WithTop ℕ) ∧ ω ∈ success i} := by
    ext ω
    simp only [successfulCandidateBy, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, n, hn, hc, hs⟩
      exact ⟨i, hi, n, hn, hc, hs⟩
    · rintro ⟨i, hi, n, hn, hc, hs⟩
      exact ⟨i, hi, n, hn, hc, hs⟩
  rw [hset]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro hi
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro hn
  exact F.mono hn _ (h i n)

theorem successfulCandidateBy_compl_measurable (F : Filtration ℕ m)
    (completion : ℕ → Ω → WithTop ℕ) (success : ℕ → Set Ω)
    (h : CandidateObservable F completion success) (K T : ℕ) :
    MeasurableSet[F T] (successfulCandidateBy completion success K T)ᶜ :=
  (successfulCandidateBy_measurable F completion success h K T).compl

/-- Success by time `T` inside a specified candidate set. The ambient type
may be uncountable; only the candidate subset needs to be countable. -/
def successfulCandidateWithin {ι : Type*}
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (candidates : Set ι) (T : ℕ) : Set Ω :=
  {ω | ∃ i ∈ candidates, ∃ n ≤ T,
    completion i ω = (n : WithTop ℕ) ∧ ω ∈ success i}

theorem successfulCandidateWithin_measurable
    {ι : Type*} (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success)
    (candidates : Set ι) (hcandidates : candidates.Countable) (T : ℕ) :
    MeasurableSet[F T]
      (successfulCandidateWithin completion success candidates T) := by
  let _ : Countable candidates := Set.countable_coe_iff.mpr hcandidates
  have hset : successfulCandidateWithin completion success candidates T =
      ⋃ i : candidates, ⋃ n : ℕ, ⋃ (_ : n ≤ T),
        {ω | completion i.1 ω = (n : WithTop ℕ) ∧ ω ∈ success i.1} := by
    ext ω
    simp only [successfulCandidateWithin, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, n, hn, hc, hs⟩
      exact ⟨⟨i, hi⟩, n, hn, hc, hs⟩
    · rintro ⟨i, n, hn, hc, hs⟩
      exact ⟨i.1, i.2, n, hn, hc, hs⟩
  rw [hset]
  exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun n =>
    MeasurableSet.iUnion fun hn => F.mono hn _ (h i.1 n)

/-- The declarations made at generation `n` by a specified candidate set. -/
def candidateDeclarationWithin {ι : Type*}
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (candidates : Set ι) (n : ℕ) : Set Ω :=
  {ω | ∃ i ∈ candidates, completion i ω = n ∧ ω ∈ success i}

/-- A countable set of observable candidates has a measurable declaration
event. -/
theorem candidateDeclarationWithin_measurable
    {ι : Type*} (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success)
    (candidates : Set ι) (hcandidates : candidates.Countable) (n : ℕ) :
    MeasurableSet[F n]
      (candidateDeclarationWithin completion success candidates n) := by
  let _ : Countable candidates := Set.countable_coe_iff.mpr hcandidates
  have hset : candidateDeclarationWithin completion success candidates n =
      ⋃ i : candidates,
        {ω | completion i.1 ω = n ∧ ω ∈ success i.1} := by
    ext ω
    simp only [candidateDeclarationWithin, Set.mem_ofPred_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hc, hs⟩
      exact ⟨⟨i, hi⟩, hc, hs⟩
    · rintro ⟨i, hc, hs⟩
      exact ⟨i.1, i.2, hc, hs⟩
  rw [hset]
  exact MeasurableSet.iUnion fun i => h i.1 n

/-- The first successful declaration in a specified countable candidate set
is a stopping time. -/
theorem first_candidate_completion_within_isStoppingTime
    {ι : Type*} (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success)
    (candidates : Set ι) (hcandidates : candidates.Countable) :
    IsStoppingTime F
      (firstDeclaredSuccess
        (candidateDeclarationWithin completion success candidates)) :=
  firstDeclaredSuccess_isStoppingTime F _ fun n =>
    candidateDeclarationWithin_measurable F completion success h
      candidates hcandidates n

/-- Adapted tests at observable completion times give a stopping time for
the first success among a countable candidate subset. -/
theorem first_successful_candidate_within_isStoppingTime
    {ι : Type*} (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ)
    (test : ι → ℕ → Set Ω)
    (hcompletion : ∀ i, IsStoppingTime F (completion i))
    (htest : ∀ i n, MeasurableSet[F n] (test i n))
    (candidates : Set ι) (hcandidates : candidates.Countable) :
    IsStoppingTime F
      (firstDeclaredSuccess
        (candidateDeclarationWithin completion
          (fun i => successAtCompletion (completion i) (test i))
          candidates)) :=
  first_candidate_completion_within_isStoppingTime F completion
    (fun i => successAtCompletion (completion i) (test i))
    (successAtCompletion_observable F completion test hcompletion htest)
    candidates hcandidates

/-- The first declared completion is a stopping time for a countable
candidate family. -/
theorem first_candidate_completion_isStoppingTime {ι : Type*} [Countable ι]
    (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success) :
    IsStoppingTime F
      (firstDeclaredSuccess fun n =>
        {ω | ∃ i, completion i ω = n ∧ ω ∈ success i}) :=
  firstDeclaredSuccess_isStoppingTime F _
    (candidate_declaration_measurable F completion success h)

/-- The first success among countably many candidates is a stopping time
when completion and at-completion tests are observable. -/
theorem first_successful_candidate_isStoppingTime
    {ι : Type*} [Countable ι] (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ)
    (test : ι → ℕ → Set Ω)
    (hcompletion : ∀ i, IsStoppingTime F (completion i))
    (htest : ∀ i n, MeasurableSet[F n] (test i n)) :
    IsStoppingTime F
      (firstDeclaredSuccess fun n =>
        {ω | ∃ i, completion i ω = n ∧
          ω ∈ successAtCompletion (completion i) (test i)}) :=
  first_candidate_completion_isStoppingTime F completion
    (fun i => successAtCompletion (completion i) (test i))
    (successAtCompletion_observable F completion test hcompletion htest)

end ProbabilityTheory

end
