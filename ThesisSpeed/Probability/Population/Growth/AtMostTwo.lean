import ThesisSpeed.Probability.PointProcess.Encoding

/-!
# Deterministic size bounds for an immortal one-or-two-child process

Every parent keeps a first child; a second child may or may not be present.
The process is not assumed to bifurcate at every generation.
-/

namespace ThesisSpeed

/-- The number of additional children in generation `n` cannot exceed the
number of parents. -/
theorem one_or_two_size_bounds (population extras : ℕ → ℕ)
    (hzero : population 0 = 1)
    (hextras : ∀ n, extras n ≤ population n)
    (hrec : ∀ n, population (n + 1) = population n + extras n) :
    ∀ n, 1 ≤ population n ∧ population n ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      constructor
      · rw [hrec n]
        omega
      · rw [hrec n, pow_succ]
        have he := hextras n
        omega

/-- The immortal first-child line makes the population nondecreasing. -/
theorem one_or_two_size_monotone (population extras : ℕ → ℕ)
    (hrec : ∀ n, population (n + 1) = population n + extras n) :
    Monotone population := by
  apply monotone_nat_of_le_succ
  intro n
  rw [hrec n]
  omega

end ThesisSpeed
