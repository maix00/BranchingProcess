/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Truncated second moments

For a measure `μ` on `ℝ`, `truncatedSecondMoment μ u` is the second moment
restricted to `[-u,u]`. The definition is meaningful for every real cutoff;
monotonicity and convergence below use nonnegative cutoffs.

## Public declarations

- `truncatedSecondMoment μ u = ∫_{-u}^u x² μ(dx)`.
- If `μ` is locally finite and `0 ≤ u ≤ v`, then
  `truncatedSecondMoment μ u ≤ truncatedSecondMoment μ v`.
- If `x ↦ x²` is `μ`-integrable, then
  `truncatedSecondMoment μ u → ∫ x² μ(dx)` as `u → ∞`; the same limit holds
  along integer cutoffs.

Writing `V_\mu(u)` for the truncated second moment, its definition and
monotone convergence properties are

\[\begin{aligned}
V_\mu(u)&=\int_{[-u,u]}x^2\,d\mu(x),\\
0\le u\le v&\Longrightarrow V_\mu(u)\le V_\mu(v),\\
x\mapsto x^2\in L^1(\mu)
&\Longrightarrow\lim_{u\to\infty}V_\mu(u)
  =\int_{\mathbb R}x^2\,d\mu(x).
\end{aligned}\]
-/

open Filter MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory

/-- The second moment truncated to the symmetric interval of radius `u`. -/
noncomputable def truncatedSecondMoment (μ : Measure ℝ) (u : ℝ) : ℝ :=
  ∫ x in Set.Icc (-u) u, x ^ 2 ∂μ

/-- The truncated second moment is nondecreasing in its nonnegative cutoff.
This uses only local finiteness of the measure: the integrand is bounded on every
bounded truncation interval, so no global second moment is required. -/
theorem truncatedSecondMoment_mono (μ : Measure ℝ) [IsLocallyFiniteMeasure μ]
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    truncatedSecondMoment μ u ≤ truncatedSecondMoment μ v := by
  let s : Set ℝ := Set.Icc (-u) u
  let t : Set ℝ := Set.Icc (-v) v
  have hsub : s ⊆ t := by
    intro x hx
    constructor
    · exact (neg_le_neg huv).trans hx.1
    · exact hx.2.trans huv
  have hbound : ∀ x ∈ t, ‖x ^ 2‖ ≤ v ^ 2 := by
    intro x hx
    have hxabs : |x| ≤ v := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    have hsq : x ^ 2 ≤ v ^ 2 := by
      rw [← sq_abs x]
      exact (sq_le_sq₀ (abs_nonneg x) (le_trans hu huv)).2 hxabs
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
    exact hsq
  have htfinite : μ t ≠ ⊤ := by
    dsimp [t]
    exact (measure_Icc_lt_top (a := -v) (b := v)).ne
  have hint : IntegrableOn (fun x : ℝ => x ^ 2) t μ :=
    Measure.integrableOn_of_bounded htfinite
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 2) μ)
      (ae_restrict_of_forall_mem measurableSet_Icc (fun x hx => hbound x hx))
  change (∫ x in s, x ^ 2 ∂μ) ≤ ∫ x in t, x ^ 2 ∂μ
  exact setIntegral_mono_set hint
    (ae_of_all _ fun x => sq_nonneg x)
    (LE.le.eventuallyLE hsub)

/-- Truncated second moments over expanding symmetric intervals converge to
the full second moment whenever it is finite. -/
theorem tendsto_truncatedSecondMoment
    (μ : Measure ℝ) (hμ : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (truncatedSecondMoment μ) atTop
      (nhds (∫ x, x ^ 2 ∂μ)) := by
  change Tendsto (fun u : ℝ => truncatedSecondMoment μ u) atTop
    (nhds (∫ x, x ^ 2 ∂μ))
  let s : ℝ → Set ℝ := fun u => Set.Icc (-u) u
  have hsMeasurable : ∀ u, MeasurableSet (s u) := fun _ => measurableSet_Icc
  have hsMono : Monotone s := by
    intro u v huv x hx
    dsimp [s] at hx ⊢
    constructor
    · exact (neg_le_neg huv).trans hx.1
    · exact hx.2.trans huv
  have hsUnion : (⋃ u, s u) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    simp only [Set.mem_iUnion, s, Set.mem_Icc]
    refine ⟨|x| + 1, ?_⟩
    constructor <;> linarith [le_abs_self x, neg_abs_le x]
  have h := tendsto_setIntegral_of_monotone hsMeasurable hsMono
    (hμ.integrableOn : IntegrableOn (fun x : ℝ => x ^ 2) (⋃ u, s u) μ)
  simpa only [truncatedSecondMoment, s, hsUnion, Measure.restrict_univ] using h

/-- Integer radii are a cofinal specialization of the real-radius limit. -/
theorem tendsto_truncatedSecondMoment_nat
    (μ : Measure ℝ) (hμ : Integrable (fun x : ℝ => x ^ 2) μ) :
    Tendsto (fun n : ℕ => truncatedSecondMoment μ n) atTop
      (nhds (∫ x, x ^ 2 ∂μ)) := by
  exact (tendsto_truncatedSecondMoment μ hμ).comp
    tendsto_natCast_atTop_atTop

end ProbabilityTheory

end
