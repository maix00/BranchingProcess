module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.Nat

public section

/-!
# Integer block scales

This file contains the rounding and quotient facts shared by the diffusive
and stable small-deviation constructions.  The probabilistic scale
parameters remain in their respective modules; only the common floor
operation and its asymptotic interface live here.
-/

open Filter Topology

namespace ProbabilityTheory.Asymptotics

/-- The integer length obtained by rounding a real-valued block argument
down at each time. -/
@[expose] noncomputable def floorBlockLength (argument : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌊argument n⌋₊

/-- A divergent nonnegative block argument has a divergent rounded length. -/
theorem tendsto_floorBlockLength_atTop {argument : ℕ → ℝ}
    (hargument : Tendsto argument atTop atTop) :
    Tendsto (floorBlockLength argument) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp hargument

/-- A divergent rounded block length is eventually positive. -/
theorem eventually_floorBlockLength_pos {argument : ℕ → ℝ}
    (hargument : Tendsto argument atTop atTop) :
    ∀ᶠ n in atTop, 0 < floorBlockLength argument n :=
  (tendsto_floorBlockLength_atTop hargument).eventually
    (eventually_gt_atTop 0)

/-- Rounding a positive divergent argument does not change its normalized
length. -/
theorem tendsto_floorBlockLength_div_argument {argument : ℕ → ℝ}
    (hargument : Tendsto argument atTop atTop) :
    Tendsto (fun n => (floorBlockLength argument n : ℝ) / argument n)
      atTop (nhds 1) :=
  (tendsto_nat_floor_div_atTop (R := ℝ)).comp hargument

/-- The rounded length is bounded above by its argument whenever the latter
is nonnegative. -/
theorem floorBlockLength_le {argument : ℕ → ℝ} {n : ℕ}
    (hargument : 0 ≤ argument n) :
    (floorBlockLength argument n : ℝ) ≤ argument n :=
  Nat.floor_le hargument

/-! ## Counts of complete blocks -/

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

end ProbabilityTheory.Asymptotics
