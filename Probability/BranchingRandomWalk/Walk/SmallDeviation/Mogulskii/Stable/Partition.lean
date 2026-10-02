module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Corridor

@[expose] public section

/-!
# Block counts at the stable small-deviation scale

The partition step of Mogulskii's stable proof splits `[0, 1]` into finitely many intervals and compares the
two-sided corridor probability with the product of the per-block corridor probabilities. The comparison itself
is scale-free and lives in `Walk/Path/Block/Partition/Basic.lean` and
`Walk/Path/Block/Partition/Normalized.lean`; this module only supplies the stable block-length
bookkeeping that turns the block length into the block count those statements take as a parameter.

The count is the largest number of complete blocks of length `stableBlockLength α μ constant scale n` that fit in
`n` steps. Its asymptotic form, which is what the rate statement consumes, additionally needs the
stable block length to vanish relative to `n`, and
`tendsto_stableBlockCount_mul_stableBlockLength_div_nat` derives it from that single hypothesis.
-/

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk

/-! ## The number of complete blocks -/

/-- The largest number of complete blocks of the stable block length that fit in
`n` steps. -/
noncomputable def stableBlockCount (α : ℝ) (μ : Measure ℝ) (constant : ℝ)
    (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  n / stableBlockLength α μ constant scale n

/-- The complete blocks fit in `n` steps. -/
theorem stableBlockCount_mul_stableBlockLength_le
    (α : ℝ) (μ : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableBlockCount α μ constant scale n *
        stableBlockLength α μ constant scale n ≤ n :=
  Nat.div_mul_le_self n _

/-- A block length that fits in `n` gives at least one complete block. -/
theorem stableBlockCount_pos_of_stableBlockLength_le
    {α : ℝ} {μ : Measure ℝ} {constant : ℝ} {scale : ℕ → ℝ} {n : ℕ}
    (hpos : 0 < stableBlockLength α μ constant scale n)
    (hle : stableBlockLength α μ constant scale n ≤ n) :
    0 < stableBlockCount α μ constant scale n :=
  Nat.div_pos hle hpos

/-- The block count brackets `n`: the complete blocks fit in the available `n`
steps, and one further block would not. This is the deterministic bracket that the
block asymptotics and the partition argument both rest on. -/
theorem stableBlockCount_mul_stableBlockLength_le_lt_succ
    (α : ℝ) (μ : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ)
    (hpos : 0 < stableBlockLength α μ constant scale n) :
    stableBlockCount α μ constant scale n *
          stableBlockLength α μ constant scale n ≤ n ∧
      n < (stableBlockCount α μ constant scale n + 1) *
          stableBlockLength α μ constant scale n := by
  refine ⟨stableBlockCount_mul_stableBlockLength_le α μ constant scale n, ?_⟩
  have hdecomp : stableBlockLength α μ constant scale n *
      stableBlockCount α μ constant scale n +
        n % stableBlockLength α μ constant scale n = n := by
    rw [stableBlockCount]
    exact Nat.div_add_mod n _
  have hr := Nat.mod_lt n hpos
  nlinarith [hdecomp, hr]

/-- The complete blocks cover all of the `n` steps except at most one block length: the total covered by
the block count is above `n` minus one block length. Together with
`stableBlockCount_mul_stableBlockLength_le` this brackets the covered steps inside the last block, which
is the form in which the partition argument uses the count. -/
theorem sub_stableBlockLength_lt_stableBlockCount_mul_stableBlockLength
    (α : ℝ) (μ : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ)
    (hpos : 0 < stableBlockLength α μ constant scale n) :
    (n : ℝ) - stableBlockLength α μ constant scale n <
      (stableBlockCount α μ constant scale n : ℝ) *
        stableBlockLength α μ constant scale n := by
  have h := (stableBlockCount_mul_stableBlockLength_le_lt_succ α μ constant scale n hpos).2
  have hcast : (n : ℝ) <
      ((stableBlockCount α μ constant scale n : ℝ) + 1) *
        stableBlockLength α μ constant scale n := by
    exact_mod_cast h
  nlinarith [hcast]


/-- The block count and the block length bracket `n` in relative terms: for a positive
block length `L`, `|count * L / n - 1| ≤ L / n`. This is the cast form of
`stableBlockCount_mul_stableBlockLength_le_lt_succ`, so it is the form in which the block
count is asymptotic to `n / L`: it converges to `1` as soon as `L / n` converges to `0`. -/
theorem stableBlockCount_mul_stableBlockLength_div_sub_one_abs_le
    (α : ℝ) (μ : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ)
    (hpos : 0 < stableBlockLength α μ constant scale n) (hn : 0 < n) :
    |((stableBlockCount α μ constant scale n *
        stableBlockLength α μ constant scale n : ℕ) : ℝ) / n - 1| ≤
      (stableBlockLength α μ constant scale n : ℝ) / n := by
  set c : ℕ := stableBlockCount α μ constant scale n with hc
  set l : ℕ := stableBlockLength α μ constant scale n with hl
  have hbr := stableBlockCount_mul_stableBlockLength_le_lt_succ α μ constant scale n hpos
  have hle : ((c * l : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbr.1
  have hlt : (n : ℝ) < (((c + 1) * l : ℕ) : ℝ) := by exact_mod_cast hbr.2
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlen : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hpos
  have hcast : (((c + 1) * l : ℕ) : ℝ) = ((c * l : ℕ) : ℝ) + (l : ℝ) := by
    have : (c + 1) * l = c * l + l := by ring
    rw [this]
    push_cast
    ring
  have hkey : (n : ℝ) - (l : ℝ) < ((c * l : ℕ) : ℝ) := by linarith [hlt, hcast]
  have h1 : ((c * l : ℕ) : ℝ) - (n : ℝ) ≤ 0 := by linarith
  have h2 : -(((c * l : ℕ) : ℝ) - (n : ℝ)) ≤ (l : ℝ) := by linarith
  have habs : |((c * l : ℕ) : ℝ) - (n : ℝ)| ≤ (l : ℝ) := by
    rw [abs_of_nonpos h1]
    exact h2
  rw [div_sub_one (ne_of_gt hnpos), abs_div, abs_of_pos hnpos]
  exact (div_le_div_iff_of_pos_right hnpos).mpr habs

/-- The block count is asymptotic to `n` divided by the block length: once the block length is
`o(n)`, the complete blocks fill the `n` steps up to a vanishing fraction. This is the form of the
block asymptotics that the rate statement of the theorem consumes. -/
theorem tendsto_stableBlockCount_mul_stableBlockLength_div_nat
    {α : ℝ} {μ : Measure ℝ} {constant : ℝ} {scale : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < stableBlockLength α μ constant scale n)
    (hscale : Tendsto (fun n => (stableBlockLength α μ constant scale n : ℝ) / n)
      atTop (nhds 0)) :
    Tendsto (fun n => ((stableBlockCount α μ constant scale n *
        stableBlockLength α μ constant scale n : ℕ) : ℝ) / n) atTop (nhds 1) := by
  rw [Metric.tendsto_atTop] at hscale ⊢
  intro ε hε
  rcases hscale ε hε with ⟨N₁, hN₁⟩
  rcases eventually_atTop.1 hpos with ⟨N₂, hN₂⟩
  refine ⟨max N₁ (max N₂ 1), fun n hn => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left N₁ (max N₂ 1)) hn
  have hN₂le : N₂ ≤ n :=
    le_trans (le_trans (le_max_left N₂ 1) (le_max_right N₁ (max N₂ 1))) hn
  have h1le : 1 ≤ n :=
    le_trans (le_trans (le_max_right N₂ 1) (le_max_right N₁ (max N₂ 1))) hn
  have hp : 0 < stableBlockLength α μ constant scale n := hN₂ n hN₂le
  have hn0 : 0 < n := h1le
  have hεn := hN₁ n hn1
  have hb :=
    stableBlockCount_mul_stableBlockLength_div_sub_one_abs_le α μ constant scale n hp hn0
  have hb' : |((stableBlockCount α μ constant scale n *
      stableBlockLength α μ constant scale n : ℕ) : ℝ) / n - 1| ≤
      |(stableBlockLength α μ constant scale n : ℝ) / n| :=
    le_trans hb (le_abs_self _)
  rw [Real.dist_eq, sub_zero] at hεn
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hb' hεn

/-- If the stable time scale is negligible relative to the full horizon, the
number of full blocks satisfies the source's fourth block relation:
`B*(aₙ) / n * ⌊n / mₙ⌋ → 1 / constant`, where
`mₙ = ⌊constant · B*(aₙ)⌋₊`.  This is pure scale and floor arithmetic; it does
not assume the missing regular-variation relation `B(mₙ) / aₙ →
constant^(1/α)`. -/
theorem tendsto_stableScaleTime_div_nat_mul_stableBlockCount
    {α : ℝ} {μ : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α μ (scale n) ∧ stableSlowVariation α μ (scale n) ≤ K)
    (hrate : Tendsto (stableSmallDeviationRate α μ scale) atTop (nhds 0)) :
    Tendsto (fun n => stableScaleTime α μ (scale n) / (n : ℝ) *
      (stableBlockCount α μ constant scale n : ℝ)) atTop (nhds constant⁻¹) := by
  have hlengthPos := eventually_stableBlockLength_pos
    hα hconstant hK hscale hvariation
  have hlengthRate := tendsto_stableBlockLength_div_nat_zero
    hα hconstant hK hscale hvariation hrate
  have hcountProduct := tendsto_stableBlockCount_mul_stableBlockLength_div_nat
    hlengthPos hlengthRate
  have hlengthScale := tendsto_stableBlockLength_div_stableScaleTime
    hα hconstant hK hscale hvariation
  have hscaleTimePos : ∀ᶠ n in atTop,
      0 < stableScaleTime α μ (scale n) := by
    filter_upwards [hscale.eventually (eventually_gt_atTop 0), hvariation]
      with n hscalePos hvar
    exact div_pos (Real.rpow_pos_of_pos hscalePos α) hvar.1
  have hinverse := hlengthScale.inv₀ hconstant.ne'
  have hscaleOverLength : Tendsto
      (fun n => stableScaleTime α μ (scale n) /
        (stableBlockLength α μ constant scale n : ℝ))
      atTop (nhds constant⁻¹) := by
    apply hinverse.congr'
    filter_upwards [hscaleTimePos, hlengthPos] with n htime hlength
    have htimeNe : stableScaleTime α μ (scale n) ≠ 0 := htime.ne'
    have hlengthNe : (stableBlockLength α μ constant scale n : ℝ) ≠ 0 := by
      exact_mod_cast hlength.ne'
    field_simp [htimeNe, hlengthNe]
  have hproduct := hscaleOverLength.mul hcountProduct
  have heq : (fun n => stableScaleTime α μ (scale n) / (n : ℝ) *
      (stableBlockCount α μ constant scale n : ℝ)) =ᶠ[atTop]
      fun n => stableScaleTime α μ (scale n) /
        (stableBlockLength α μ constant scale n : ℝ) *
          (((stableBlockCount α μ constant scale n *
            stableBlockLength α μ constant scale n : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hlengthPos] with n hn hlength
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hlengthNe : (stableBlockLength α μ constant scale n : ℝ) ≠ 0 := by
      exact_mod_cast hlength.ne'
    change stableScaleTime α μ (scale n) / (n : ℝ) *
        (stableBlockCount α μ constant scale n : ℝ) =
      stableScaleTime α μ (scale n) /
        (stableBlockLength α μ constant scale n : ℝ) *
          (((stableBlockCount α μ constant scale n *
            stableBlockLength α μ constant scale n : ℕ) : ℝ) / (n : ℝ))
    push_cast
    field_simp [hnNe, hlengthNe]
  have hres := hproduct.congr' heq.symm
  simpa using hres

end ProbabilityTheory.RandomWalk
