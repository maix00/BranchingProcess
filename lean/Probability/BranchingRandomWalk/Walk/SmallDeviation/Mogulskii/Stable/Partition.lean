import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Corridor

/-!
# Finite partitions of the unit interval along the stable block length

The partition step of Mogulskii's stable proof splits `[0, 1]` into finitely many intervals and compares the
two-sided corridor probability with the product of the per-block corridor probabilities. The comparison itself
is scale-free and lives in `Walk/Path/Block/Partition.lean`; this module only supplies the stable block-length
bookkeeping that turns the block length into the block count those statements take as a parameter.

The count is the largest number of complete blocks of length `stableBlockLength α μ constant b n` that fit in
`n` steps. Its asymptotic form, which is what the rate statement consumes, additionally needs the
small-deviation scale to vanish relative to `n` and is not proved here.
-/

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-! ## The number of complete blocks -/

/-- The largest number of complete blocks of the stable block length that fit in
`n` steps. -/
noncomputable def stableBlockCount (α : ℝ) (μ : Measure ℝ) (constant : ℝ)
    (normalization : ℕ → ℝ) (n : ℕ) : ℕ :=
  n / stableBlockLength α μ constant normalization n

/-- The complete blocks fit in `n` steps. -/
theorem stableBlockCount_mul_stableBlockLength_le
    (α : ℝ) (μ : Measure ℝ) (constant : ℝ) (normalization : ℕ → ℝ) (n : ℕ) :
    stableBlockCount α μ constant normalization n *
        stableBlockLength α μ constant normalization n ≤ n :=
  Nat.div_mul_le_self n _

/-- A block length that fits in `n` gives at least one complete block. -/
theorem stableBlockCount_pos_of_stableBlockLength_le
    {α : ℝ} {μ : Measure ℝ} {constant : ℝ} {normalization : ℕ → ℝ} {n : ℕ}
    (hpos : 0 < stableBlockLength α μ constant normalization n)
    (hle : stableBlockLength α μ constant normalization n ≤ n) :
    0 < stableBlockCount α μ constant normalization n :=
  Nat.div_pos hle hpos

/-- The block count brackets `n`: the complete blocks fit in the available `n`
steps, and one further block would not. This is the deterministic bracket that the
block asymptotics and the partition argument both rest on. -/
theorem stableBlockCount_mul_stableBlockLength_le_lt_succ
    (α : ℝ) (μ : Measure ℝ) (constant : ℝ) (normalization : ℕ → ℝ) (n : ℕ)
    (hpos : 0 < stableBlockLength α μ constant normalization n) :
    stableBlockCount α μ constant normalization n *
          stableBlockLength α μ constant normalization n ≤ n ∧
      n < (stableBlockCount α μ constant normalization n + 1) *
          stableBlockLength α μ constant normalization n := by
  refine ⟨stableBlockCount_mul_stableBlockLength_le α μ constant normalization n, ?_⟩
  have hdecomp : stableBlockLength α μ constant normalization n *
      stableBlockCount α μ constant normalization n +
        n % stableBlockLength α μ constant normalization n = n := by
    rw [stableBlockCount]
    exact Nat.div_add_mod n _
  have hr := Nat.mod_lt n hpos
  nlinarith [hdecomp, hr]

/-- The complete blocks cover all of the `n` steps except at most one block length: the total covered by
the block count is above `n` minus one block length. Together with
`stableBlockCount_mul_stableBlockLength_le` this brackets the covered steps inside the last block, which
is the form in which the partition argument uses the count. -/
theorem sub_stableBlockLength_lt_stableBlockCount_mul_stableBlockLength
    (α : ℝ) (μ : Measure ℝ) (constant : ℝ) (normalization : ℕ → ℝ) (n : ℕ)
    (hpos : 0 < stableBlockLength α μ constant normalization n) :
    (n : ℝ) - stableBlockLength α μ constant normalization n <
      (stableBlockCount α μ constant normalization n : ℝ) *
        stableBlockLength α μ constant normalization n := by
  have h := (stableBlockCount_mul_stableBlockLength_le_lt_succ α μ constant normalization n hpos).2
  have hcast : (n : ℝ) <
      ((stableBlockCount α μ constant normalization n : ℝ) + 1) *
        stableBlockLength α μ constant normalization n := by
    exact_mod_cast h
  nlinarith [hcast]

end ProbabilityTheory.RandomWalk
