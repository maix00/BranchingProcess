import Probability.BranchingRandomWalk.Timing.Stopping

/-!
# Measurability interfaces for restart candidates and causal couplings

The restart proof has two distinct obligations. A successful candidate must be
declared using information available at its completion generation. A coupled
generation process must be computed causally from its previous generation and
newly observed marks. These theorems verify the measure-theoretic closure
steps; a concrete marked-tree model must supply their hypotheses.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open MeasureTheory

open MeasureTheory


variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- At generation `n`, a successful candidate is visible if the joint event
that its completion time equals `n` and it succeeds is `F n`-measurable. -/
def CandidateObservable {ι : Type*} (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω) : Prop :=
  ∀ i n, MeasurableSet[F n] {ω | completion i ω = n ∧ ω ∈ success i}

/-- A trial succeeds when its generation-dependent test holds at the
candidate's actual completion generation. The test is evaluated at a
pre-defined candidate even if an earlier trial succeeds. -/
def successAtCompletion (completion : Ω → WithTop ℕ)
    (test : ℕ → Set Ω) : Set Ω :=
  {ω | ∃ n : ℕ, completion ω = (n : WithTop ℕ) ∧ ω ∈ test n}

/-- Stopping of the candidate and adaptation of its per-generation success
test imply the required joint-event measurability. -/
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

/-- All candidates are pre-defined, including those that will never be used.
Their union of success declarations is measurable at the declaration time. -/
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
by generation `T`.  The candidate family remains countably infinite; `K` and
`T` occur only in this bounded event used by the restart estimate. -/
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
    · rintro ⟨i, hi, n, hc, hn, hs⟩
      exact ⟨i, hi, n, hc, hn, hs⟩
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

/-- A success by time `T` inside a countable set of candidates.  The ambient
candidate type can be uncountable: countability is required only of the set
whose declarations are joined. -/
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

/-- The declarations made at generation `n` by a specified candidate set.
The definition itself is cardinality-free. -/
def candidateDeclarationWithin {ι : Type*}
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (candidates : Set ι) (n : ℕ) : Set Ω :=
  {ω | ∃ i ∈ candidates, completion i ω = n ∧ ω ∈ success i}

/-- A countable set of observable candidates has a measurable declaration
event.  No countability assumption is imposed on the ambient candidate
type. -/
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

/-- The first successful declaration among a specified countable set of
candidates is a stopping time. -/
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

/-- Observable completion tests give a stopping time for the first success
inside a specified countable set of candidates. -/
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

/-- The first declared completion is a stopping time. This applies to
unconditionally pre-sampled reserve candidates; it does not assert that a
retrospectively constructed generation process is adapted. -/
theorem first_candidate_completion_isStoppingTime {ι : Type*} [Countable ι]
    (F : Filtration ℕ m)
    (completion : ι → Ω → WithTop ℕ) (success : ι → Set Ω)
    (h : CandidateObservable F completion success) :
    IsStoppingTime F
      (firstDeclaredSuccess fun n =>
        {ω | ∃ i, completion i ω = n ∧ ω ∈ success i}) :=
  firstDeclaredSuccess_isStoppingTime F _ (candidate_declaration_measurable F completion success h)

/-- The completed trial's first success is a stopping time as soon as all
candidate completion times and all at-completion tests are observable. -/
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

/-- A state recursion driven only by marks visible in the new generation is
adapted. This is the reusable criterion for a causal coupling. -/
theorem causal_recursion_adapted {State M : Type*}
    [MeasurableSpace State] [MeasurableSpace M]
    (F : Filtration ℕ m) (state : ℕ → Ω → State)
    (marks : ℕ → Ω → M) (step : State × M → State)
    (hstep : Measurable step)
    (hzero : Measurable[F 0] (state 0))
    (hmarks : ∀ n, Measurable[F (n + 1)] (marks n))
    (hrec : ∀ n ω, state (n + 1) ω = step (state n ω, marks n ω)) :
    ∀ n, Measurable[F n] (state n) := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      have hold : Measurable[F (n + 1)] (state n) :=
        ih.mono (F.mono (Nat.le_succ n)) le_rfl
      have hpair : Measurable[F (n + 1)] (fun ω => (state n ω, marks n ω)) :=
        hold.prodMk (hmarks n)
      convert hstep.comp hpair using 1
      funext ω
      exact hrec n ω

end ProbabilityTheory.BranchingRandomWalk
