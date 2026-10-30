/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Lower bounds for floor-power products

## Public declarations

The public theorem `Asymptotics.eventually_floor_rpow_mul_ge` states that,
for real sequences $x_n\to\infty$ and $y_n$, exponents $a>0$ and
$\delta<a+r$, and any $C\in\mathbb R$, an eventual lower bound
$x_n^r\le y_n$ implies
\[
  Cx_n^\delta\le\lfloor x_n^a\rfloor y_n
\]
eventually. The proof combines Mathlib's `tendsto_nat_floor_div_atTop` from
`Mathlib.Analysis.SpecificLimits.Basic` with `tendsto_rpow_atTop` from
`Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Asymptotics

private lemma eventually_floorRpow_mul_rpow_ge
    {a r δ C : ℝ} (ha : 0 < a) (hgap : δ < a + r) :
    ∀ᶠ x : ℝ in atTop,
      C * x ^ δ ≤ ((Nat.floor (x ^ a) : ℕ) : ℝ) * x ^ r := by
  let gap : ℝ := a + r - δ
  have hgapPos : 0 < gap := by dsimp [gap]; linarith
  have hfloor : Tendsto
      (fun x : ℝ => (Nat.floor (x ^ a) : ℝ) / x ^ a) atTop (𝓝 1) := by
    exact tendsto_nat_floor_div_atTop.comp (_root_.tendsto_rpow_atTop ha)
  have hpower : Tendsto (fun x : ℝ => x ^ gap) atTop atTop :=
    (_root_.tendsto_rpow_atTop hgapPos)
  filter_upwards [
    hfloor.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
    hpower.eventually_gt_atTop (2 * C),
    eventually_ge_atTop (1 : ℝ)] with x hfloor hpower hx
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hargPos : 0 < x ^ a := Real.rpow_pos_of_pos hxpos _
  have hratio : (1 / 2 : ℝ) <
      (Nat.floor (x ^ a) : ℝ) / x ^ a := hfloor
  have hratioPos : 0 < (Nat.floor (x ^ a) : ℝ) / x ^ a := by linarith
  have hpowPos : 0 < x ^ gap := Real.rpow_pos_of_pos hxpos _
  have hmul : C <
      ((Nat.floor (x ^ a) : ℝ) / x ^ a) * x ^ gap := by
    calc
      C < (1 / 2 : ℝ) * x ^ gap := by nlinarith
      _ < ((Nat.floor (x ^ a) : ℝ) / x ^ a) * x ^ gap :=
        mul_lt_mul_of_pos_right hratio hpowPos
  have hscale :
      (((Nat.floor (x ^ a) : ℝ) * x ^ r) / x ^ δ) =
        ((Nat.floor (x ^ a) : ℝ) / x ^ a) * x ^ gap := by
    have hquot : x ^ r / x ^ δ = x ^ (r - δ) :=
      (Real.rpow_sub hxpos r δ).symm
    have hgapquot : x ^ gap / x ^ a = x ^ (gap - a) :=
      (Real.rpow_sub hxpos gap a).symm
    have hexp : r - δ = gap - a := by dsimp [gap]; ring
    calc
      ((Nat.floor (x ^ a) : ℝ) * x ^ r) / x ^ δ =
          (Nat.floor (x ^ a) : ℝ) * (x ^ r / x ^ δ) := by ring
      _ = (Nat.floor (x ^ a) : ℝ) * x ^ (r - δ) := by rw [hquot]
      _ = (Nat.floor (x ^ a) : ℝ) * x ^ (gap - a) := by rw [hexp]
      _ = (Nat.floor (x ^ a) : ℝ) * (x ^ gap / x ^ a) := by
        rw [hgapquot]
      _ = ((Nat.floor (x ^ a) : ℝ) / x ^ a) * x ^ gap := by ring
  have hratioGreat : C <
      (((Nat.floor (x ^ a) : ℝ) * x ^ r) / x ^ δ) := by
    rw [hscale]
    exact hmul
  have hdeltaPos : 0 < x ^ δ := Real.rpow_pos_of_pos hxpos _
  exact le_of_lt ((lt_div_iff₀ hdeltaPos).mp hratioGreat)

/-- An eventual lower power bound for a real sequence, multiplied by the
integer part of another diverging power, dominates every power below the sum
of the two exponents. -/
theorem eventually_floor_rpow_mul_ge
    {x y : ℕ → ℝ} (hx : Tendsto x atTop atTop)
    {a r δ C : ℝ} (ha : 0 < a) (hbudget : δ < a + r)
    (hy : ∀ᶠ n : ℕ in atTop, x n ^ r ≤ y n) :
    ∀ᶠ n : ℕ in atTop,
      C * x n ^ δ ≤ ((Nat.floor (x n ^ a) : ℕ) : ℝ) * y n := by
  have hbase := eventually_floorRpow_mul_rpow_ge (C := C) ha hbudget
  filter_upwards [hx.eventually hbase, hy] with n hbase hy
  have hfloorNonneg : 0 ≤ ((Nat.floor (x n ^ a) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hmonotone := mul_le_mul_of_nonneg_left hy hfloorNonneg
  exact le_trans hbase hmonotone

end Asymptotics
