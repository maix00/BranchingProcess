/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Exponential bounds for finite sums

## Public declarations

- `Asymptotics.eventually_sum_exp_le_exp_mul_of_uniform_gap`: if $g\to+\infty$ and each of finitely many exponents satisfies $e_i/g<c-\delta$ eventually for a common $\delta>0$, then
  $\sum_{i\in F}\exp(e_i)\leq\exp(cg)$ eventually.

The fixed finite number of summands contributes only the factor $|F|$; the
diverging margin $\delta g$ absorbs that factor. This result applies to any
filter and does not depend on probability or on a particular scale sequence.
-/

@[expose] public section

open Filter
open scoped BigOperators Topology

namespace Asymptotics

/-- A uniform strict gap between finitely many normalized exponents and `c`
absorbs the finite sum into the exponential with rate `c`. -/
theorem eventually_sum_exp_le_exp_mul_of_uniform_gap
    {ι X : Type*} [DecidableEq ι] {l : Filter X}
    (F : Finset ι) (g : X → ℝ) (e : X → ι → ℝ)
    (c δ : ℝ) (hδ : 0 < δ) (hg : Tendsto g l atTop)
    (hgap : ∀ i ∈ F, ∀ᶠ x in l, e x i / g x < c - δ) :
    ∀ᶠ x in l, (∑ i ∈ F, Real.exp (e x i)) ≤ Real.exp (c * g x) := by
  have hgapAll : ∀ᶠ x in l, ∀ i ∈ F, e x i / g x < c - δ :=
    F.eventually_all.2 hgap
  have hgpos : ∀ᶠ x in l, 0 < g x := hg.eventually_gt_atTop 0
  have hmargin : Tendsto (fun x => δ * g x) l atTop := hg.const_mul_atTop hδ
  have hcard : ∀ᶠ x in l, Real.log ((F.card : ℝ) + 1) < δ * g x :=
    hmargin.eventually_gt_atTop (Real.log ((F.card : ℝ) + 1))
  filter_upwards [hgapAll, hgpos, hcard] with x hgapx hgx hcardx
  have hcardExp : (F.card : ℝ) ≤ Real.exp (δ * g x) := by
    have hlt := Real.exp_lt_exp.mpr hcardx
    have hlog : Real.exp (Real.log ((F.card : ℝ) + 1)) =
        (F.card : ℝ) + 1 := Real.exp_log (by positivity)
    calc
      (F.card : ℝ) ≤ (F.card : ℝ) + 1 := by norm_num
      _ = Real.exp (Real.log ((F.card : ℝ) + 1)) := hlog.symm
      _ ≤ Real.exp (δ * g x) := hlt.le
  have hterm (i : ι) (hi : i ∈ F) :
      Real.exp (e x i) ≤ Real.exp ((c - δ) * g x) := by
    apply Real.exp_le_exp.mpr
    exact (div_lt_iff₀ hgx).mp (hgapx i hi) |>.le
  calc
    (∑ i ∈ F, Real.exp (e x i)) ≤
        ∑ i ∈ F, Real.exp ((c - δ) * g x) :=
      Finset.sum_le_sum fun i hi => hterm i hi
    _ = (F.card : ℝ) * Real.exp ((c - δ) * g x) := by simp
    _ ≤ Real.exp (δ * g x) * Real.exp ((c - δ) * g x) :=
      mul_le_mul_of_nonneg_right hcardExp (Real.exp_nonneg _)
    _ = Real.exp (c * g x) := by
      rw [← Real.exp_add]
      congr 1
      ring

end Asymptotics

end
