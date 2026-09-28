import Probability.BranchingRandomWalk.Walk.Basic

/-!
# Paths of random walks

Finite histories and partial sums depend only on an increment path. They are
kept outside the spine layer so that invariance principles and small-deviation
theorems can be stated for arbitrary random walks.
-/

open MeasureTheory
open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

variable {E : Type*} [AddCommMonoid E]

/-- Sum of the first `n` increments. -/
def partialSum (n : ℕ) (increment : ℕ → E) : E :=
  ∑ k ∈ Finset.range n, increment k

@[simp] theorem partialSum_zero (increment : ℕ → E) :
    partialSum 0 increment = 0 := by
  simp [partialSum]

theorem partialSum_succ (n : ℕ) (increment : ℕ → E) :
    partialSum (n + 1) increment = partialSum n increment + increment n := by
  simp [partialSum, Finset.sum_range_succ]

theorem partialSum_measurable [MeasurableSpace E] [MeasurableAdd₂ E]
    (n : ℕ) : Measurable (partialSum (E := E) n) := by
  unfold partialSum
  exact Finset.measurable_sum (Finset.range n)
    (fun k _ => measurable_pi_apply k)

/-- Positions at times `0, ..., n`, starting from `initial`. -/
def history (n : ℕ) (initial : E) (increment : ℕ → E) :
    Fin (n + 1) → E :=
  fun k => initial + partialSum k increment

@[simp] theorem history_zero (n : ℕ) (initial : E)
    (increment : ℕ → E) :
    history n initial increment ⟨0, Nat.zero_lt_succ n⟩ = initial := by
  simp [history]

theorem history_last (n : ℕ) (initial : E) (increment : ℕ → E) :
    history n initial increment ⟨n, Nat.lt_succ_self n⟩ =
      initial + partialSum n increment := rfl

theorem history_measurable [MeasurableSpace E] [MeasurableAdd₂ E]
    (n : ℕ) (initial : E) : Measurable (history n initial) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_const.add (partialSum_measurable k)

theorem history_joint_measurable [MeasurableSpace E] [MeasurableAdd₂ E]
    (n : ℕ) :
    Measurable (fun p : E × (ℕ → E) => history n p.1 p.2) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_fst.add ((partialSum_measurable k).comp measurable_snd)

/-- Add a time-zero position in front of a nonempty finite history. -/
def prependHistory {n : ℕ} (initial : E) (tail : Fin (n + 1) → E) :
    Fin (n + 2) → E :=
  Fin.cases initial tail

/-- Remove the first coordinate of an increment path. -/
def incrementTail (increment : ℕ → E) : ℕ → E :=
  fun k => increment (k + 1)

omit [AddCommMonoid E] in
@[simp] theorem prependHistory_zero {n : ℕ} (initial : E)
    (tail : Fin (n + 1) → E) :
    prependHistory initial tail 0 = initial := rfl

omit [AddCommMonoid E] in
@[simp] theorem prependHistory_succ {n : ℕ} (initial : E)
    (tail : Fin (n + 1) → E) (k : Fin (n + 1)) :
    prependHistory initial tail k.succ = tail k := rfl

omit [AddCommMonoid E] in
theorem prependHistory_joint_measurable [MeasurableSpace E] (n : ℕ) :
    Measurable (fun p : E × (Fin (n + 1) → E) =>
      prependHistory p.1 p.2) := by
  rw [measurable_pi_iff]
  intro k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact measurable_fst
  · exact measurable_pi_apply j |>.comp measurable_snd

omit [AddCommMonoid E] in
theorem incrementTail_measurable [MeasurableSpace E] :
    Measurable (incrementTail (E := E)) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_pi_apply (k + 1)

/-- Partial sums split into the first increment and the partial sums of the
remaining path. -/
theorem partialSum_succ_eq_head_add_tail (n : ℕ)
    (increment : ℕ → E) :
    partialSum (n + 1) increment =
      increment 0 + partialSum n (incrementTail increment) := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      rw [partialSum_succ, ih, partialSum_succ]
      simp only [incrementTail]
      ac_rfl

/-- A finite history has the expected first-step decomposition. -/
theorem history_succ (n : ℕ) (initial : E) (increment : ℕ → E) :
    history (n + 1) initial increment =
      prependHistory initial
        (history n (initial + increment 0) (incrementTail increment)) := by
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [history]
  · simp only [history, prependHistory_succ]
    change initial + partialSum (j.val + 1) increment =
      initial + increment 0 + partialSum j.val (incrementTail increment)
    rw [partialSum_succ_eq_head_add_tail]
    ac_rfl

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
