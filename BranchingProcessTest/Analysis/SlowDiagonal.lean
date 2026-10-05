import Analysis.Asymptotics.SlowDiagonal

open Filter

example : ∃ d : ℕ → ℕ, Tendsto d atTop atTop ∧ ∀ᶠ n : ℕ in atTop, d n ≤ n := by
  apply Asymptotics.exists_tendsto_slowDiagonal
  intro k
  exact Filter.eventually_atTop.2 ⟨k, fun n hn => hn⟩

#print axioms Asymptotics.exists_tendsto_slowDiagonal
