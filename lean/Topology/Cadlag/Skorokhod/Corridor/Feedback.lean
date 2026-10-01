module

public import Topology.Cadlag.Skorokhod.Corridor

/-!
# Feedback control of endpoint errors

Alternating between positive and negative endpoint corrections keeps every
partial endpoint error in a fixed interval. The result concerns only real
sequences; independence and positive block probabilities belong to the
probability layer.
-/

@[expose] public section

namespace ProbabilityTheory

/-- If each increment corrects the sign of the current error by an amount
between `r` and `R`, endpoint errors never exceed `R`. -/
theorem feedback_endpoint_error_bound
    (e : ℕ → ℝ) (n : ℕ) (r R : ℝ)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (he0 : e 0 = 0)
    (hstep : ∀ k < n,
      (0 ≤ e k → -R ≤ e (k + 1) - e k ∧ e (k + 1) - e k ≤ -r) ∧
      (e k < 0 → r ≤ e (k + 1) - e k ∧ e (k + 1) - e k ≤ R)) :
    ∀ k ≤ n, |e k| ≤ R := by
  intro k hk
  induction k with
  | zero => simp [he0, hR]
  | succ k ih =>
    have hk' : k < n := by omega
    have hprev : |e k| ≤ R := ih (by omega)
    have hbound : -R ≤ e k ∧ e k ≤ R := abs_le.mp hprev
    rcases hstep k hk' with ⟨hpositive, hnegative⟩
    apply abs_le.mpr
    by_cases hsign : 0 ≤ e k
    · rcases hpositive hsign with ⟨hlo, hhi⟩
      constructor <;> linarith
    · have hneg : e k < 0 := lt_of_not_ge hsign
      rcases hnegative hneg with ⟨hlo, hhi⟩
      constructor <;> linarith

/-- A block's endpoint error, within-block increment and deterministic
drift bound give a uniform bound throughout that block. -/
theorem feedback_within_block_bound
    (startValue value driftAtStart driftIncrement R w d : ℝ)
    (hstart : |startValue - driftAtStart| ≤ R)
    (hblock : |value - startValue| ≤ w)
    (hdrift : |driftIncrement| ≤ |d|) :
    |value - (driftAtStart + driftIncrement)| ≤ R + w + |d| := by
  have htriangle := abs_add_le (startValue - driftAtStart)
    ((value - startValue) - driftIncrement)
  have hmiddle := abs_sub_le (value - startValue) 0 driftIncrement
  simp only [sub_zero, zero_sub, abs_neg] at hmiddle
  have hidentity : value - (driftAtStart + driftIncrement) =
      (startValue - driftAtStart) +
        ((value - startValue) - driftIncrement) := by ring
  rw [hidentity]
  linarith

/-- A finite family of block paths satisfying the feedback rule remains in
one fixed tube around the prescribed linear motion. This is the pathwise
part of the finite-block support argument. -/
theorem feedback_blockPaths_bound
    (e : ℕ → ℝ) (block : ℕ → unitInterval → ℝ)
    (n : ℕ) (r R w d : ℝ)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (he0 : e 0 = 0)
    (hstep : ∀ k < n,
      (0 ≤ e k → -R ≤ e (k + 1) - e k ∧ e (k + 1) - e k ≤ -r) ∧
      (e k < 0 → r ≤ e (k + 1) - e k ∧ e (k + 1) - e k ≤ R))
    (hblock : ∀ k < n, ∀ t : unitInterval, |block k t| ≤ w) :
    ∀ k < n, ∀ t : unitInterval,
      |e k + block k t - d * (t : ℝ)| ≤ R + w + |d| := by
  intro k hk t
  have he := feedback_endpoint_error_bound e n r R hR hr he0 hstep k hk.le
  have ht : |(t : ℝ)| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [t.property.1], t.property.2⟩
  have hd : |d * (t : ℝ)| ≤ |d| := by
    rw [abs_mul]
    nlinarith [abs_nonneg d]
  have h := feedback_within_block_bound (e k)
    (e k + block k t) 0 (d * (t : ℝ)) R w d
    (by simpa using he) (by simpa using hblock k hk t) hd
  simpa only [sub_zero, zero_add] using h

end ProbabilityTheory

end
