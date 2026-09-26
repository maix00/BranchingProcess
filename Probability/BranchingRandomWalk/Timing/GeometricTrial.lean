import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Joint-transform geometric trial calculation

For a waiting step, `a` contributes `E[exp (λ Ξ₁) 1_{no split}]`, not
`P(no split) * E[exp (λ Ξ₁)]`. The probabilistic identification of each term
with `p * a ^ g` remains a separate independence proof obligation.
-/

namespace ProbabilityTheory.BranchingRandomWalk


/-- The geometric-series step of the correct one-trial transform. -/
theorem geometric_trial_transform (p a : ℝ) (ha₀ : 0 ≤ a) (ha₁ : a < 1) :
    (∑' g : ℕ, p * a ^ g) = p / (1 - a) := by
  rw [tsum_mul_left, tsum_geometric_of_lt_one ha₀ ha₁]
  simp [div_eq_mul_inv]

end ProbabilityTheory.BranchingRandomWalk
