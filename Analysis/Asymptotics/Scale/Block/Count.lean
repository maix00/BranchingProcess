/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.Nat

/-!
# Complete block counts

## Public declarations

`blockCount blockLength n = n / blockLength n` is the number of complete
blocks of the given length that fit in a horizon of `n` steps. The module
records the quotient/remainder bounds and the resulting asymptotic fraction
of the horizon covered by complete blocks. In particular, if
`blockLength n / n → 0` and the block length is eventually positive, the
complete blocks occupy an asymptotic fraction one of the horizon.

Public declarations: `blockCount`, `blockCount_mul_blockLength_le`,
`blockCount_mul_blockLength_le_lt_succ`,
`sub_blockLength_lt_blockCount_mul_blockLength`,
`blockCount_mul_blockLength_div_sub_one_abs_le`,
`tendsto_blockCount_mul_blockLength_div_nat`,
`tendsto_quotientBlockCount_mul_blockLength_div_nat`, and
`tendsto_div_nat_mul_quotientBlockCount`.

For block length `\ell_n>0`, the count `c_n=\lfloor n/\ell_n\rfloor` obeys
\[
  c_n\ell_n\le n<(c_n+1)\ell_n.
\]
If `\ell_n/n → 0`, then `c_n\ell_n/n → 1`; more generally, for
`H_n/n → τ`, `\ell_n/n → 0`, and eventually positive `\ell_n`,
\[
  \frac{\lfloor H_n/\ell_n\rfloor\ell_n}{n}\longrightarrow\tau.
\]
-/

public section

open Filter Topology

namespace Asymptotics

/-- The largest number of complete blocks of the given length that fit in a
horizon of `n` steps. -/
@[expose] noncomputable def blockCount (blockLength : ℕ → ℕ) (n : ℕ) : ℕ :=
  n / blockLength n

/-- Complete blocks fit in the available horizon. -/
theorem blockCount_mul_blockLength_le (blockLength : ℕ → ℕ) (n : ℕ) :
    blockCount blockLength n * blockLength n ≤ n :=
  Nat.div_mul_le_self n _

/-- When a block has positive length, the number of complete blocks brackets
the horizon: one more block would be too long. -/
theorem blockCount_mul_blockLength_le_lt_succ (blockLength : ℕ → ℕ) (n : ℕ)
    (hpos : 0 < blockLength n) :
    blockCount blockLength n * blockLength n ≤ n ∧
      n < (blockCount blockLength n + 1) * blockLength n := by
  refine ⟨blockCount_mul_blockLength_le blockLength n, ?_⟩
  have hdecomp : blockLength n * blockCount blockLength n +
      n % blockLength n = n := by
    rw [blockCount]
    exact Nat.div_add_mod n _
  have hr := Nat.mod_lt n hpos
  nlinarith [hdecomp, hr]

/-- The complete blocks cover all but less than one block length. -/
theorem sub_blockLength_lt_blockCount_mul_blockLength
    (blockLength : ℕ → ℕ) (n : ℕ) (hpos : 0 < blockLength n) :
    (n : ℝ) - blockLength n <
      (blockCount blockLength n : ℝ) * blockLength n := by
  have h := (blockCount_mul_blockLength_le_lt_succ blockLength n hpos).2
  have hcast : (n : ℝ) <
      ((blockCount blockLength n : ℝ) + 1) * blockLength n := by
    exact_mod_cast h
  nlinarith [hcast]

/-- The relative error in the number of covered steps is at most one block
length divided by the horizon. -/
theorem blockCount_mul_blockLength_div_sub_one_abs_le
    (blockLength : ℕ → ℕ) (n : ℕ)
    (hpos : 0 < blockLength n) (hn : 0 < n) :
    |((blockCount blockLength n * blockLength n : ℕ) : ℝ) / n - 1| ≤
      (blockLength n : ℝ) / n := by
  set c : ℕ := blockCount blockLength n with hc
  set l : ℕ := blockLength n with hl
  have hbr := blockCount_mul_blockLength_le_lt_succ blockLength n hpos
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

/-- If the block length is `o(n)`, the number of covered steps is
asymptotic to the horizon. -/
theorem tendsto_blockCount_mul_blockLength_div_nat
    {blockLength : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < blockLength n)
    (hscale : Tendsto (fun n => (blockLength n : ℝ) / n)
      atTop (nhds 0)) :
    Tendsto (fun n => ((blockCount blockLength n * blockLength n : ℕ) : ℝ) / n)
      atTop (nhds 1) := by
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
  have hp : 0 < blockLength n := hN₂ n hN₂le
  have hn0 : 0 < n := h1le
  have hεn := hN₁ n hn1
  have hb := blockCount_mul_blockLength_div_sub_one_abs_le blockLength n hp hn0
  have hb' : |((blockCount blockLength n * blockLength n : ℕ) : ℝ) / n - 1|
      ≤ |(blockLength n : ℝ) / n| := le_trans hb (le_abs_self _)
  rw [Real.dist_eq, sub_zero] at hεn
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hb' hεn

/-- Complete equal-length blocks occupy the same asymptotic fraction as an
arbitrary horizon sequence. This version is used for subintervals of a finite
partition, where the horizon is `⌊nt₁⌋ - ⌊nt₀⌋` rather than `n` itself. -/
theorem tendsto_quotientBlockCount_mul_blockLength_div_nat
    {horizon blockLength : ℕ → ℕ} {τ : ℝ}
    (hhorizon : Tendsto (fun n => (horizon n : ℝ) / n) atTop (nhds τ))
    (hblock : Tendsto (fun n => (blockLength n : ℝ) / n)
      atTop (nhds 0))
    (hpositive : ∀ᶠ n in atTop, 0 < blockLength n) :
    Tendsto (fun n =>
      ((horizon n / blockLength n * blockLength n : ℕ) : ℝ) / n)
      atTop (nhds τ) := by
  let covered : ℕ → ℝ := fun n =>
    ((horizon n / blockLength n * blockLength n : ℕ) : ℝ)
  have hlower : Tendsto (fun n => (horizon n : ℝ) / n -
      (blockLength n : ℝ) / n) atTop (nhds τ) := by
    simpa using hhorizon.sub hblock
  have hcovered : Tendsto (fun n => covered n / n) atTop (nhds τ) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hhorizon
    · filter_upwards [hpositive, eventually_gt_atTop (0 : ℕ)] with n hlen hnNat
      have hdecomp : horizon n / blockLength n * blockLength n +
          horizon n % blockLength n = horizon n := by
        simpa [Nat.mul_comm] using Nat.div_add_mod (horizon n) (blockLength n)
      have hrem : horizon n % blockLength n < blockLength n :=
        Nat.mod_lt _ hlen
      have hgap :
          (horizon n : ℝ) - covered n < (blockLength n : ℝ) := by
        have hcast :
            covered n + (horizon n % blockLength n : ℝ) = horizon n := by
          dsimp [covered]
          exact_mod_cast hdecomp
        have hrem' : (horizon n % blockLength n : ℝ) < blockLength n :=
          by exact_mod_cast hrem
        rw [← hcast]
        linarith
      have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
      have hdiv := (div_lt_div_iff_of_pos_right hn).2 hgap
      rw [sub_div] at hdiv
      have hbound : (horizon n : ℝ) / n - (blockLength n : ℝ) / n <
          covered n / n := by
        linarith
      exact le_of_lt hbound
    · filter_upwards [hpositive, eventually_gt_atTop (0 : ℕ)] with n hlen hnNat
      have hle : horizon n / blockLength n * blockLength n ≤ horizon n :=
        Nat.div_mul_le_self _ _
      have hcast :
          ((horizon n / blockLength n * blockLength n : ℕ) : ℝ) ≤
            (horizon n : ℝ) := by
        exact_mod_cast hle
      have hn : 0 < (n : ℝ) := by exact_mod_cast hnNat
      exact (div_le_div_iff_of_pos_right hn).2 (by simpa [covered] using hcast)
  simpa [covered] using hcovered

/-- A macroscopic horizon made of complete blocks has the expected scaled
count. If `horizon / n → τ`, `blockLength / n → 0`, and
`scale / blockLength → L`, then `scale / n * (horizon / blockLength) → L * τ`.
This combines the quotient estimate with ordinary multiplication of limits. -/
theorem tendsto_div_nat_mul_quotientBlockCount
    {horizon blockLength : ℕ → ℕ} {scale : ℕ → ℝ} {limit τ : ℝ}
    (hhorizon : Tendsto (fun n => (horizon n : ℝ) / n)
      atTop (nhds τ))
    (hpositive : ∀ᶠ n in atTop, 0 < blockLength n)
    (hblockLength : Tendsto (fun n => (blockLength n : ℝ) / n)
      atTop (nhds 0))
    (hscale : Tendsto (fun n => scale n / (blockLength n : ℝ))
      atTop (nhds limit)) :
    Tendsto (fun n => scale n / (n : ℝ) *
      ((horizon n / blockLength n : ℕ) : ℝ)) atTop (nhds (limit * τ)) := by
  have hcovered := tendsto_quotientBlockCount_mul_blockLength_div_nat
    hhorizon hblockLength hpositive
  have hproduct := hscale.mul hcovered
  have heq : (fun n => scale n / (n : ℝ) *
      ((horizon n / blockLength n : ℕ) : ℝ)) =ᶠ[atTop]
      fun n => scale n / (blockLength n : ℝ) *
        (((horizon n / blockLength n * blockLength n : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hpositive] with n hn hlen
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hlenNe : (blockLength n : ℝ) ≠ 0 := by
      exact_mod_cast hlen.ne'
    change scale n / (n : ℝ) *
        ((horizon n / blockLength n : ℕ) : ℝ) =
      scale n / (blockLength n : ℝ) *
        (((horizon n / blockLength n * blockLength n : ℕ) : ℝ) / (n : ℝ))
    push_cast
    field_simp [hnNe, hlenNe]
  simpa using hproduct.congr' heq.symm
end Asymptotics
