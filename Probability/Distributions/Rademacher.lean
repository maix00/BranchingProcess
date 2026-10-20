/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Topology.UnitInterval
public import Probability.Distributions.Moments.Truncated.Basic

/-!
# The Rademacher distribution

The Rademacher law is the equal mixture of the point masses at `-1` and `1`.
It is defined as a specialization of mathlib's `bernoulliMeasure`.

The public declarations are:

- `rademacherMeasure` and `rademacherMeasure.instIsProbabilityMeasure`:
  the probability law with mass $1/2$ at each of $-1$ and $1$.
- `rademacherOfBool`, `measurable_rademacherOfBool`, `fairBoolMeasure`,
  `fairBoolMeasure.instIsProbabilityMeasure`, and
  `map_fairBernoulli_rademacherOfBool`: the measurable Boolean encoding of
  this law and its fair-Bernoulli pushforward representation.
- `fairBoolMeasure_singleton`: each Boolean atom has mass $1/2$.
- `integral_rademacherMeasure`: for every $f : \mathbb R\to\mathbb R$,
  $\int f\,d\mu=(f(-1)+f(1))/2$.
- `truncatedSecondMoment_rademacher_eq_one_of_one_le`: for $u\ge1$,
  $\int_{[-u,u]}x^2\,\mu(dx)=1$.
-/

open MeasureTheory unitInterval

@[expose] public section

namespace ProbabilityTheory

/-- The probability measure assigning mass `1 / 2` to each of `-1` and `1`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  Ber((-1 : ℝ), 1, ⟨1 / 2, by constructor <;> norm_num⟩)

noncomputable instance rademacherMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure rademacherMeasure := by
  unfold rademacherMeasure
  infer_instance

/-- Encode the two Rademacher increments by a Boolean branch. -/
def rademacherOfBool (step : Bool) : ℝ :=
  if step then 1 else -1

theorem measurable_rademacherOfBool : Measurable rademacherOfBool :=
  measurable_of_countable _

/-- The fair Bernoulli law on the two Boolean branches. -/
noncomputable def fairBoolMeasure : Measure Bool :=
  Ber(false, true, ⟨1 / 2, by constructor <;> norm_num⟩)

noncomputable instance fairBoolMeasure.instIsProbabilityMeasure :
    IsProbabilityMeasure fairBoolMeasure := by
  unfold fairBoolMeasure
  infer_instance

@[simp] theorem fairBoolMeasure_singleton (step : Bool) :
    fairBoolMeasure {step} = ENNReal.ofReal (1 / 2 : ℝ) := by
  cases step <;> simp [fairBoolMeasure]
  all_goals
    rw [ENNReal.coe_nnreal_eq]
    simp only [unitInterval.coe_toNNReal, unitInterval.coe_symm_eq]
    norm_num
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num

/-- The fair Boolean Bernoulli law pushes forward to the Rademacher law. -/
theorem map_fairBernoulli_rademacherOfBool :
    fairBoolMeasure.map rademacherOfBool = rademacherMeasure := by
  unfold fairBoolMeasure
  rw [map_bernoulliMeasure]
  rfl

/-- Integration against the Rademacher law is symmetric averaging. -/
theorem integral_rademacherMeasure (f : ℝ → ℝ) :
    ∫ x, f x ∂rademacherMeasure = (f (-1) + f 1) / 2 := by
  rw [rademacherMeasure, integral_bernoulliMeasure]
  norm_num [smul_eq_mul]
  ring

/-- Once the truncation interval contains the support, its second moment is
the full unit second moment of the Rademacher law. -/
theorem truncatedSecondMoment_rademacher_eq_one_of_one_le {u : ℝ}
    (hu : 1 ≤ u) :
    truncatedSecondMoment rademacherMeasure u = 1 := by
  rw [truncatedSecondMoment]
  have hset : MeasurableSet (Set.Icc (-u) u) := measurableSet_Icc
  have hmass : rademacherMeasure (Set.Icc (-u) u) = 1 := by
    simpa [rademacherMeasure] using
      (bernoulliMeasure_apply_of_mem_of_mem
        (x := (-1 : ℝ)) (y := (1 : ℝ))
        (p := (⟨1 / 2, by norm_num⟩ : unitInterval))
        (s := Set.Icc (-u) u) hset
        (by constructor <;> linarith)
        (by constructor <;> linarith))
  have hae : ∀ᵐ x ∂rademacherMeasure, x ∈ Set.Icc (-u) u :=
    (mem_ae_iff_prob_eq_one hset).2 hmass
  have hzero : ∀ᵐ x ∂rademacherMeasure,
      x ∉ Set.Icc (-u) u → x ^ 2 = 0 := by
    filter_upwards [hae] with x hx hnot
    exact (hnot hx).elim
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero hzero,
    integral_rademacherMeasure]
  norm_num

end ProbabilityTheory

end
