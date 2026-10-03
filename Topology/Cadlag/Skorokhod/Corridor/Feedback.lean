module

public import Mathlib.Topology.UnitInterval
public import Order.Bounds.Feedback
public import Topology.Cadlag.Skorokhod.Corridor

/-!
# Compatibility names for deterministic feedback bounds

The estimates are owned by `Real` in `Order.Bounds.Feedback`. This module
retains the previous `ProbabilityTheory` names used by Skorokhod applications.
-/

@[expose] public section

namespace ProbabilityTheory

/-- Compatibility name for `Real.feedback_endpoint_error_bound`. -/
@[deprecated Real.feedback_endpoint_error_bound (since := "2026-10-03")]
theorem feedback_endpoint_error_bound
    (e : ℕ → ℝ) (n : ℕ) (r R : ℝ)
    (hR : 0 ≤ R) (hr : 0 ≤ r) (he0 : e 0 = 0)
    (hstep : ∀ k < n,
      (0 ≤ e k → -R ≤ e (k + 1) - e k ∧ e (k + 1) - e k ≤ -r) ∧
      (e k < 0 → r ≤ e (k + 1) - e k ∧ e (k + 1) - e k ≤ R)) :
    ∀ k ≤ n, |e k| ≤ R :=
  Real.feedback_endpoint_error_bound e n r R hR hr he0 hstep

/-- Compatibility name for `Real.feedback_within_block_bound`. -/
@[deprecated Real.feedback_within_block_bound (since := "2026-10-03")]
theorem feedback_within_block_bound
    (startValue value driftAtStart driftIncrement R w d : ℝ)
    (hstart : |startValue - driftAtStart| ≤ R)
    (hblock : |value - startValue| ≤ w)
    (hdrift : |driftIncrement| ≤ |d|) :
    |value - (driftAtStart + driftIncrement)| ≤ R + w + |d| :=
  Real.feedback_within_block_bound startValue value driftAtStart
    driftIncrement R w d hstart hblock hdrift

/-- Compatibility name for `Real.feedback_blockPaths_bound` on
`unitInterval`. -/
@[deprecated Real.feedback_blockPaths_bound +typeChanged (since := "2026-10-03")]
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
  apply Real.feedback_blockPaths_bound (fun t : unitInterval => (t : ℝ))
    e block n r R w d hR hr he0 hstep hblock
  intro t
  rw [abs_le]
  exact ⟨by linarith [t.property.1], t.property.2⟩

/-- Compatibility name for `Real.feedback_positive_scaledWindow`. -/
@[deprecated Real.feedback_positive_scaledWindow (since := "2026-10-03")]
theorem feedback_positive_scaledWindow
    (a r R z d : ℝ) (ha : 0 < a)
    (hz : z / a ∈ Set.Ioo r R) (hd : |d| / a < r / 2) :
    r * a / 2 < z - d ∧ z - d < (R + r / 2) * a :=
  Real.feedback_positive_scaledWindow a r R z d ha hz hd

/-- Compatibility name for `Real.feedback_negative_scaledWindow`. -/
@[deprecated Real.feedback_negative_scaledWindow (since := "2026-10-03")]
theorem feedback_negative_scaledWindow
    (a r R z d : ℝ) (ha : 0 < a)
    (hz : z / a ∈ Set.Ioo (-R) (-r)) (hd : |d| / a < r / 2) :
    -(R + r / 2) * a < z - d ∧ z - d < -(r * a / 2) :=
  Real.feedback_negative_scaledWindow a r R z d ha hz hd

end ProbabilityTheory

end
