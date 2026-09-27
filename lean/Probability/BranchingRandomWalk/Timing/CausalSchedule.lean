import Probability.BranchingRandomWalk.Timing.Stopping

/-!
# Causal schedules of pre-sampled trials

Every trial is defined whether or not an earlier trial succeeds.  Trial
`i + 1` starts at the first generation after trial `i`'s start at which its
pre-defined readiness event is observed.  This provides the stopping-time
schedule needed by concurrent reserve constructions without conditioning the
definition of later trial times on earlier failures.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk
namespace CausalSchedule

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Recursive observable trial times. `ready i n` is the generation-`n`
event that announces the next start after trial `i`. -/
noncomputable def time
    (initial : Ω → WithTop ℕ) (ready : ℕ → ℕ → Set Ω) :
    ℕ → Ω → WithTop ℕ
  | 0 => initial
  | i + 1 => firstDeclaredSuccess fun n =>
      {ω | time initial ready i ω ≤ n ∧ ω ∈ ready i n}

@[simp] theorem time_zero
    (initial : Ω → WithTop ℕ) (ready : ℕ → ℕ → Set Ω) :
    time initial ready 0 = initial :=
  rfl

@[simp] theorem time_succ
    (initial : Ω → WithTop ℕ) (ready : ℕ → ℕ → Set Ω)
    (i : ℕ) :
    time initial ready (i + 1) = firstDeclaredSuccess fun n =>
      {ω | time initial ready i ω ≤ n ∧ ω ∈ ready i n} :=
  rfl

/-- Adapted readiness declarations recursively produce stopping times. -/
theorem time_isStoppingTime
    (F : Filtration ℕ m)
    (initial : Ω → WithTop ℕ) (hinitial : IsStoppingTime F initial)
    (ready : ℕ → ℕ → Set Ω)
    (hready : ∀ i n, MeasurableSet[F n] (ready i n)) :
    ∀ i, IsStoppingTime F (time initial ready i) := by
  intro i
  induction i with
  | zero => simpa using hinitial
  | succ i ih =>
      rw [time_succ]
      apply firstDeclaredSuccess_isStoppingTime F
      intro n
      exact (ih n).inter (hready i n)

/-- Every next trial starts weakly after the preceding trial. -/
theorem time_le_succ
    (initial : Ω → WithTop ℕ) (ready : ℕ → ℕ → Set Ω)
    (i : ℕ) (ω : Ω) :
    time initial ready i ω ≤ time initial ready (i + 1) ω := by
  rw [time_succ]
  by_cases htop : firstDeclaredSuccess
      (fun n => {ω | time initial ready i ω ≤ n ∧ ω ∈ ready i n}) ω = ⊤
  · simp [htop]
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    have hdeclared := (firstDeclaredSuccess_le_iff
      (fun n => {ω | time initial ready i ω ≤ n ∧ ω ∈ ready i n})
      ω n).mp (by simp [← hn])
    obtain ⟨j, hjn, hj, _⟩ := hdeclared
    calc
      time initial ready i ω ≤ (j : WithTop ℕ) := hj
      _ ≤ (n : WithTop ℕ) := WithTop.coe_le_coe.mpr hjn
      _ = firstDeclaredSuccess
          (fun n => {ω | time initial ready i ω ≤ n ∧ ω ∈ ready i n}) ω := hn

/-- Trial times are monotone in their trial index. -/
theorem time_mono
    (initial : Ω → WithTop ℕ) (ready : ℕ → ℕ → Set Ω)
    {ω : Ω} : Monotone fun i => time initial ready i ω := by
  apply monotone_nat_of_le_succ
  exact fun i => time_le_succ initial ready i ω

end CausalSchedule
end ProbabilityTheory.BranchingRandomWalk
