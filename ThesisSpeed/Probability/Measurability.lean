import ThesisSpeed.Probability.Stopping

/-!
# Measurability interfaces for restart candidates and causal couplings

The restart proof has two distinct obligations. A successful candidate must be
declared using information available at its completion generation. A coupled
generation process must be computed causally from its previous generation and
newly observed marks. These theorems verify the measure-theoretic closure
steps; a concrete marked-tree model must supply their hypotheses.
-/

open MeasureTheory

namespace ThesisSpeed

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- At generation `n`, a successful candidate is visible if the joint event
that its completion time equals `n` and it succeeds is `F n`-measurable. -/
def CandidateObservable (F : Filtration ℕ m)
    (completion : ℕ → Ω → WithTop ℕ) (success : ℕ → Set Ω) : Prop :=
  ∀ i n, MeasurableSet[F n] {ω | completion i ω = n ∧ ω ∈ success i}

/-- A trial succeeds when its generation-dependent test holds at the
candidate's actual completion generation. The test is evaluated at a
pre-defined candidate even if an earlier trial succeeds. -/
def successAtCompletion (completion : Ω → WithTop ℕ)
    (test : ℕ → Set Ω) : Set Ω :=
  {ω | ∃ n : ℕ, completion ω = (n : WithTop ℕ) ∧ ω ∈ test n}

/-- Stopping of the candidate and adaptation of its per-generation success
test imply the required joint-event measurability. -/
theorem successAtCompletion_observable (F : Filtration ℕ m)
    (completion : ℕ → Ω → WithTop ℕ)
    (test : ℕ → ℕ → Set Ω)
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
theorem candidate_declaration_measurable (F : Filtration ℕ m)
    (completion : ℕ → Ω → WithTop ℕ) (success : ℕ → Set Ω)
    (h : CandidateObservable F completion success) (n : ℕ) :
    MeasurableSet[F n]
      {ω | ∃ i, completion i ω = n ∧ ω ∈ success i} := by
  have hset :
      {ω | ∃ i, completion i ω = n ∧ ω ∈ success i} =
        ⋃ i : ℕ, {ω | completion i ω = n ∧ ω ∈ success i} := by
    ext ω
    simp
  rw [hset]
  exact MeasurableSet.iUnion fun i => h i n

/-- The first declared completion is a stopping time. This applies to
unconditionally pre-sampled reserve candidates; it does not assert that a
retrospectively constructed generation process is adapted. -/
theorem first_candidate_completion_isStoppingTime (F : Filtration ℕ m)
    (completion : ℕ → Ω → WithTop ℕ) (success : ℕ → Set Ω)
    (h : CandidateObservable F completion success) :
    IsStoppingTime F
      (firstDeclaredSuccess fun n =>
        {ω | ∃ i, completion i ω = n ∧ ω ∈ success i}) :=
  firstDeclaredSuccess_isStoppingTime F _ (candidate_declaration_measurable F completion success h)

/-- The completed trial's first success is a stopping time as soon as all
candidate completion times and all at-completion tests are observable. -/
theorem first_successful_candidate_isStoppingTime (F : Filtration ℕ m)
    (completion : ℕ → Ω → WithTop ℕ)
    (test : ℕ → ℕ → Set Ω)
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
theorem causal_recursion_adapted {State Mark : Type*}
    [MeasurableSpace State] [MeasurableSpace Mark]
    (F : Filtration ℕ m) (state : ℕ → Ω → State)
    (marks : ℕ → Ω → Mark) (step : State × Mark → State)
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

end ThesisSpeed
