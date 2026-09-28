import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Assumptions

/-!
# Diffusive block lengths

Mogulskii blocking uses integer time blocks whose length is asymptotic to a
positive constant times the square of the spatial scale.  This file isolates
the rounding facts from the probabilistic argument.
-/

open Filter Topology

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

/-- The integer block length obtained by rounding down a constant multiple of
the squared spatial scale. -/
noncomputable def diffusiveBlockLength
    (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊constant * scale n ^ 2⌋₊

/-- The real quantity rounded in `diffusiveBlockLength` diverges for every
positive block constant. -/
theorem IsMogulskiiScale.tendsto_const_mul_sq_atTop
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n => constant * scale n ^ 2) atTop atTop := by
  have hsquare : Tendsto (fun n => scale n * scale n) atTop atTop :=
    hscale.1.atTop_mul_atTop₀ hscale.1
  simpa [pow_two] using hsquare.const_mul_atTop hconstant

/-- Diffusive block lengths themselves tend to infinity. -/
theorem IsMogulskiiScale.tendsto_diffusiveBlockLength_atTop
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (diffusiveBlockLength constant scale) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (hscale.tendsto_const_mul_sq_atTop hconstant)

/-- In particular, a diffusive block has positive integer length eventually. -/
theorem IsMogulskiiScale.eventually_diffusiveBlockLength_pos
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    ∀ᶠ n in atTop, 0 < diffusiveBlockLength constant scale n :=
  (hscale.tendsto_diffusiveBlockLength_atTop hconstant).eventually
    (eventually_gt_atTop 0)

/-- Rounding the diffusive block length has no effect after normalization by
the squared spatial scale. -/
theorem IsMogulskiiScale.tendsto_diffusiveBlockLength_div_sq
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n =>
        (diffusiveBlockLength constant scale n : ℝ) / scale n ^ 2)
      atTop (nhds constant) := by
  have hratio := (tendsto_nat_floor_div_atTop (R := ℝ)).comp
    (hscale.tendsto_const_mul_sq_atTop hconstant)
  have hmul := hratio.mul_const constant
  convert hmul.congr' ?_ using 1 <;> simp
  filter_upwards [hscale.eventually_pos] with n hn
  dsimp [diffusiveBlockLength]
  field_simp [hconstant.ne', hn.ne']

/-- The number of complete diffusive blocks available before time `n`
diverges. -/
theorem IsMogulskiiScale.tendsto_nat_div_diffusiveBlockLength_atTop
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n => n / diffusiveBlockLength constant scale n)
      atTop atTop := by
  rw [tendsto_atTop]
  intro blockCount
  have hratio : ∀ᶠ n : ℕ in atTop,
      (blockCount : ℝ) * constant ≤ (n : ℝ) / scale n ^ 2 :=
    hscale.tendsto_natCast_div_sq_atTop.eventually
      (eventually_ge_atTop ((blockCount : ℝ) * constant))
  filter_upwards [hratio, hscale.eventually_pos,
    hscale.eventually_diffusiveBlockLength_pos hconstant]
      with n hnRatio hnScale hnBlock
  apply (Nat.le_div_iff_mul_le hnBlock).2
  have hfloor :
      (diffusiveBlockLength constant scale n : ℝ) ≤
        constant * scale n ^ 2 := by
    exact Nat.floor_le (mul_nonneg hconstant.le (sq_nonneg _))
  have htime :
      ((blockCount * diffusiveBlockLength constant scale n : ℕ) : ℝ) ≤
        (n : ℝ) := by
    calc
      ((blockCount * diffusiveBlockLength constant scale n : ℕ) : ℝ) =
          (blockCount : ℝ) *
            (diffusiveBlockLength constant scale n : ℝ) := by norm_num
      _ ≤ (blockCount : ℝ) * (constant * scale n ^ 2) :=
        mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg blockCount)
      _ ≤ (n : ℝ) := by
        have hsquare : 0 < scale n ^ 2 := sq_pos_of_pos hnScale
        simpa [mul_assoc] using (le_div_iff₀ hsquare).mp hnRatio
  exact_mod_cast htime

/-- The complete-block exponent has the expected Mogulskii normalization.
The proof uses the Euclidean-division bounds, so the integer rounding errors
are handled here rather than in the probabilistic blocking argument. -/
theorem IsMogulskiiScale.tendsto_completeBlockCount_mul_sq_div
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n =>
        ((n / diffusiveBlockLength constant scale n : ℕ) : ℝ) *
          scale n ^ 2 / (n : ℝ))
      atTop (nhds (1 / constant)) := by
  have hblockRatio :=
    hscale.tendsto_diffusiveBlockLength_div_sq hconstant
  have hinverse : Tendsto (fun n =>
      scale n ^ 2 /
        (diffusiveBlockLength constant scale n : ℝ))
      atTop (nhds (1 / constant)) := by
    have hinv := hblockRatio.inv₀ hconstant.ne'
    convert hinv.congr' ?_ using 1 <;> simp [one_div]
  have hlower := hinverse.sub hscale.tendsto_sq_div_natCast_zero
  have hlower' : Tendsto (fun n =>
      scale n ^ 2 /
          (diffusiveBlockLength constant scale n : ℝ) -
        scale n ^ 2 / (n : ℝ))
      atTop (nhds (1 / constant)) := by
    simpa using hlower
  apply hlower'.squeeze' hinverse
  · filter_upwards [hscale.eventually_pos,
      hscale.eventually_diffusiveBlockLength_pos hconstant,
      eventually_gt_atTop 0] with n hnScale hnBlock hn
    have hdivision :
        n < (n / diffusiveBlockLength constant scale n + 1) *
          diffusiveBlockLength constant scale n := by
      simpa [mul_comm] using Nat.lt_mul_div_succ n hnBlock
    have hdivisionReal :
        (n : ℝ) <
          ((n / diffusiveBlockLength constant scale n + 1 : ℕ) : ℝ) *
            diffusiveBlockLength constant scale n := by
      exact_mod_cast hdivision
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
    have hbReal : (0 : ℝ) < diffusiveBlockLength constant scale n := by
      exact_mod_cast hnBlock
    have hsquare : 0 ≤ scale n ^ 2 := sq_nonneg _
    push_cast at hdivisionReal
    have hquotient :
        (n : ℝ) / diffusiveBlockLength constant scale n ≤
          ((n / diffusiveBlockLength constant scale n : ℕ) : ℝ) + 1 :=
      (div_le_iff₀ hbReal).2 hdivisionReal.le
    have hmul := mul_le_mul_of_nonneg_right hquotient hsquare
    have hdiv := div_le_div_of_nonneg_right hmul hnReal.le
    rw [sub_le_iff_le_add]
    convert hdiv using 1
    all_goals field_simp [hnReal.ne', hbReal.ne']
  · filter_upwards [hscale.eventually_diffusiveBlockLength_pos hconstant,
      eventually_gt_atTop 0] with n hnBlock hn
    have hdivision := Nat.div_mul_le_self n
      (diffusiveBlockLength constant scale n)
    have hdivisionReal :
        ((n / diffusiveBlockLength constant scale n : ℕ) : ℝ) *
            diffusiveBlockLength constant scale n ≤ (n : ℝ) := by
      exact_mod_cast hdivision
    have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
    have hbReal : (0 : ℝ) < diffusiveBlockLength constant scale n := by
      exact_mod_cast hnBlock
    have hsquare : 0 ≤ scale n ^ 2 := sq_nonneg _
    have hquotient :
        ((n / diffusiveBlockLength constant scale n : ℕ) : ℝ) ≤
          (n : ℝ) / diffusiveBlockLength constant scale n :=
      (le_div_iff₀ hbReal).2 hdivisionReal
    have hmul := mul_le_mul_of_nonneg_right hquotient hsquare
    have hdiv := div_le_div_of_nonneg_right hmul hnReal.le
    convert hdiv using 1
    all_goals field_simp [hnReal.ne', hbReal.ne']

/-- Counting one extra block for the incomplete tail has the same normalized
limit as counting only complete blocks. -/
theorem IsMogulskiiScale.tendsto_succ_completeBlockCount_mul_sq_div
    {scale : ℕ → ℝ} (hscale : IsMogulskiiScale scale)
    {constant : ℝ} (hconstant : 0 < constant) :
    Tendsto (fun n =>
        ((n / diffusiveBlockLength constant scale n + 1 : ℕ) : ℝ) *
          scale n ^ 2 / (n : ℝ))
      atTop (nhds (1 / constant)) := by
  have hsum :=
    (hscale.tendsto_completeBlockCount_mul_sq_div hconstant).add
      hscale.tendsto_sq_div_natCast_zero
  have hsum' : Tendsto (fun n =>
      ((n / diffusiveBlockLength constant scale n : ℕ) : ℝ) *
          scale n ^ 2 / (n : ℝ) + scale n ^ 2 / (n : ℝ))
      atTop (nhds (1 / constant)) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [] with n
  push_cast
  ring

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
