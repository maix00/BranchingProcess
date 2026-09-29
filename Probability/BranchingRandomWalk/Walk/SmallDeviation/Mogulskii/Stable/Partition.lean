import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Corridor

/-!
# Finite partitions of the unit interval along the stable block length

The partition step of Mogulskii's stable proof splits `[0, 1]` into finitely many intervals and compares the
two-sided corridor probability with the product of the per-block corridor probabilities. The comparison itself
is scale-free and lives in `Walk/Path/Block/Partition.lean`; this module only supplies the stable block-length
bookkeeping that turns the block length into the block count those statements take as a parameter.

The count is the largest number of complete blocks of length `stableBlockLength α constant b n` that fit in `n`
steps. Its asymptotic form, which is what the rate statement consumes, additionally needs the small-deviation
rate to vanish and is not proved here.
-/

open Filter

namespace ProbabilityTheory.RandomWalk

/-! ## The number of complete blocks -/

/-- The largest number of complete blocks of the stable block length that fit in
`n` steps. -/
noncomputable def stableBlockCount (α constant : ℝ) (normalization : ℕ → ℝ) (n : ℕ) : ℕ :=
  n / stableBlockLength α constant normalization n

/-- The complete blocks fit in `n` steps. -/
theorem stableBlockCount_mul_stableBlockLength_le
    (α constant : ℝ) (normalization : ℕ → ℝ) (n : ℕ) :
    stableBlockCount α constant normalization n *
        stableBlockLength α constant normalization n ≤ n :=
  Nat.div_mul_le_self n _

/-- A block length that fits in `n` gives at least one complete block. -/
theorem stableBlockCount_pos_of_stableBlockLength_le
    {α constant : ℝ} {normalization : ℕ → ℝ} {n : ℕ}
    (hpos : 0 < stableBlockLength α constant normalization n)
    (hle : stableBlockLength α constant normalization n ≤ n) :
    0 < stableBlockCount α constant normalization n :=
  Nat.div_pos hle hpos

end ProbabilityTheory.RandomWalk
