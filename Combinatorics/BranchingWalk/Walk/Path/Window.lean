import Combinatorics.BranchingWalk.Walk.Path.Basic

/-!
# Windows for deterministic walk paths

Finite path-window and survival predicates depend only on an initial state
and an increment path.  Measurability and probability laws are developed in
the corresponding probability layer.
-/

namespace Combinatorics.Branching.Walk

/-- A finite path remains in the prescribed window at every coordinate. -/
def InWindows {E : Type*} {n : ℕ} (window : Fin (n + 1) → Set E)
    (path : Fin (n + 1) → E) : Prop :=
  ∀ k, path k ∈ window k

/-- A real increment path, including its time-zero position, remains in a
fixed closed interval through time `n`. -/
def InClosedInterval (lower upper : ℝ) (n : ℕ) (initial : ℝ)
    (increment : ℕ → ℝ) : Prop :=
  InWindows (fun _ : Fin (n + 1) => Set.Icc lower upper)
    (history n initial increment)

/-- All strictly positive-time positions through time `n` belong to
`allowed`. -/
def StaysIn {E : Type*} [AddCommMonoid E] (allowed : Set E) (n : ℕ)
    (initial : E) (increment : ℕ → E) : Prop :=
  ∀ k : Fin n, initial + partialSum (k + 1) increment ∈ allowed

/-- For an initial position already in the interval, `StaysIn` is the closed
interval path event that also records time zero. -/
theorem staysIn_Icc_iff_inClosedInterval
    (lower upper : ℝ) (n : ℕ) (initial : ℝ)
    (hinitial : initial ∈ Set.Icc lower upper) (increment : ℕ → ℝ) :
    StaysIn (Set.Icc lower upper) n initial increment ↔
      InClosedInterval lower upper n initial increment := by
  constructor
  · intro h k
    refine Fin.cases ?_ (fun j => ?_) k
    · simpa [history] using hinitial
    · simpa [history, Fin.val_succ] using h j
  · intro h k
    simpa [InClosedInterval, InWindows, history, Fin.val_succ] using h k.succ

/-- Staying inside for one more step decomposes into acceptance of the first
position and the same event for the shifted increment path. -/
theorem staysIn_succ_iff {E : Type*} [AddCommMonoid E]
    (allowed : Set E) (n : ℕ) (initial : E) (increment : ℕ → E) :
    StaysIn allowed (n + 1) initial increment ↔
      initial + increment 0 ∈ allowed ∧
        StaysIn allowed n (initial + increment 0)
          (fun k => increment (k + 1)) := by
  constructor
  · intro h
    constructor
    · simpa [StaysIn, partialSum_succ] using h (0 : Fin (n + 1))
    · intro k
      have hk := h k.succ
      rw [Fin.val_succ] at hk
      have hposition :
          initial + partialSum ((k : ℕ) + 1 + 1) increment =
            (initial + increment 0) +
              partialSum (k + 1) (fun j => increment (j + 1)) := by
        rw [show (k : ℕ) + 1 + 1 = 1 + (k + 1) by omega,
          partialSum_add]
        simp [partialSum]
        ac_rfl
      rwa [hposition] at hk
  · rintro ⟨hfirst, htail⟩ k
    refine Fin.cases ?_ (fun j => ?_) k
    · simpa [partialSum_succ] using hfirst
    · have hj := htail j
      rw [Fin.val_succ]
      have hposition :
          initial + partialSum ((j : ℕ) + 1 + 1) increment =
            (initial + increment 0) +
              partialSum (j + 1) (fun k => increment (k + 1)) := by
        rw [show (j : ℕ) + 1 + 1 = 1 + (j + 1) by omega,
          partialSum_add]
        simp [partialSum]
        ac_rfl
      rwa [hposition]

/-- Staying in a fixed interval through `m + n` is equivalent to staying in
it before the cut and, after restarting from the position at the cut, along
the shifted increment sequence. -/
theorem inClosedInterval_add_iff
    (lower upper : ℝ) (m n : ℕ) (initial : ℝ)
    (increment : ℕ → ℝ) :
    InClosedInterval lower upper (m + n) initial increment ↔
      InClosedInterval lower upper m initial increment ∧
        InClosedInterval lower upper n
          (initial + partialSum m increment)
          (fun k => increment (m + k)) := by
  constructor
  · intro h
    constructor
    · intro k
      exact h ⟨k, by omega⟩
    · intro k
      rw [history_restart]
      exact h ⟨m + k, by omega⟩
  · rintro ⟨hfirst, hsecond⟩ k
    by_cases hk : (k : ℕ) ≤ m
    · exact hfirst ⟨k, by omega⟩
    · let j : Fin (n + 1) := ⟨(k : ℕ) - m, by omega⟩
      have hj := hsecond j
      rw [history_restart] at hj
      have hmk : m ≤ (k : ℕ) := by omega
      simpa [j, Nat.add_sub_of_le hmk] using hj

end Combinatorics.Branching.Walk
