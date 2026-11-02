/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Levy.FiniteDimensional
public import Probability.Distributions.InfinitelyDivisible.Basic
public import Probability.Sequence.IID.Law
public import Mathlib.Probability.Independence.CharacteristicFunction
public import MeasureTheory.Measure.CharacteristicFunction.Convolution

/-!
# Marginal laws of Lévy processes

## Public declarations

- `ProbabilityTheory.IsLevyProcess.isInfinitelyDivisible_timeMarginal`:
  every fixed-time law of a real-valued Lévy process is infinitely divisible:
  for every $t\ge0$ and $n\ge1$, there is a probability measure $\nu_{t,n}$
  such that $\operatorname{Law}(X_t)=\nu_{t,n}^{*n}$. The proof takes the
  common law of the $n$ stationary increments on an equal time partition.
- `ProbabilityTheory.IsLevyProcess.map_eval_eq_convPower_div` proves
  $\operatorname{Law}(X_t)=\operatorname{Law}(X_{t/n})^{*n}$ for every
  $t\ge0$ and positive integer $n$.
- `ProbabilityTheory.IsLevyProcess.map_eval_nat_eq_iidSum` identifies the
  marginal at integer time $n$ with the law of the sum of the first $n$
  coordinates under the canonical i.i.d. sequence with law
  $\operatorname{Law}(X_1)$.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

@[expose] public section

namespace ProbabilityTheory.IsLevyProcess

variable {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℝ≥0 → Ω → ℝ}

/-- The marginal at time `t` is the `n`-fold convolution power of the common
law of the stationary increments on the equal partition of `[0,t]`. -/
theorem map_eval_eq_convPower_div
    (h : IsLevyProcess X P) (t : ℝ≥0) (n : ℕ) (hn : 0 < n) :
    P.map (fun ω => X t ω) =
      (P.map (fun ω => X (t / (n : ℝ≥0)) ω)).convPower n := by
  let duration : ℝ≥0 := t / (n : ℝ≥0)
  let grid : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * duration
  let increment : ℕ → Ω → ℝ := fun k ω =>
    X (grid (k + 1)) ω - X (grid k) ω
  let ν : Measure ℝ := P.map fun ω => X duration ω

  have hnR : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
  have hnRne : (n : ℝ≥0) ≠ 0 := hnR.ne'
  have hgrid_mono : Monotone grid := by
    intro j k hjk
    dsimp [grid]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) (by positivity)
  have hgrid_step (k : ℕ) : grid k + duration = grid (k + 1) := by
    simp only [grid, Nat.cast_add, Nat.cast_one]
    rw [add_mul, one_mul]
  have hgrid_zero : grid 0 = 0 := by simp [grid]
  have hgrid_last : grid n = t := by
    dsimp [grid, duration]
    field_simp [hnRne]

  have hincrement_indep : iIndepFun increment P := by
    simpa [increment] using h.indepIncrements.nat hgrid_mono
  have hincrement_meas (k : ℕ) : AEMeasurable (increment k) P := by
    exact (h.aemeasurable_eval (grid (k + 1))).sub
      (h.aemeasurable_eval (grid k))
  have hincrement_law (k : ℕ) :
      IdentDistrib (increment k) (fun ω => X duration ω) P P := by
    simpa [increment, hgrid_step k] using
      h.stationaryIncrements.identDistrib_increment_of_ae_start
        h.ae_start_eq_zero (grid k) duration

  have hν_probability : IsProbabilityMeasure ν := by
    apply (Measure.isProbabilityMeasure_map_iff (h.aemeasurable_eval duration)).2
    infer_instance

  have hsum_ae : (fun ω => ∑ k ∈ Finset.range n, increment k ω) =ᵐ[P]
      fun ω => X t ω := by
    filter_upwards [h.ae_start_eq_zero] with ω hω
    change (∑ k ∈ Finset.range n,
        (X (grid (k + 1)) ω - X (grid k) ω)) = X t ω
    calc
      _ = X (grid n) ω - X (grid 0) ω := by
        simpa only using (Finset.sum_range_sub (fun k => X (grid k) ω) n)
      _ = X t ω := by rw [hgrid_last, hgrid_zero, hω]; simp

  apply Measure.ext_of_charFun
  ext ξ
  rw [Measure.charFun_convPower]
  have hchar_sum : charFun (P.map fun ω => X t ω) ξ =
      ∏ k ∈ Finset.range n, charFun ν ξ := by
    calc
      charFun (P.map fun ω => X t ω) ξ =
          charFun (P.map (fun ω => ∑ k ∈ Finset.range n, increment k ω)) ξ := by
        rw [← Measure.map_congr hsum_ae]
      _ = ∏ k ∈ Finset.range n, charFun (P.map fun ω => increment k ω) ξ :=
        by
          have hrestricted :
              iIndepFun ((Finset.range n).restrict increment) P :=
            hincrement_indep.restrict (Finset.range n)
          have h := ProbabilityTheory.iIndepFun.charFun_map_fun_finsetSum_eq_prod
            (P := P) (X := increment) (s := Finset.range n)
            (fun k _ => hincrement_meas k) hrestricted
          simpa using congrFun h ξ
      _ = ∏ k ∈ Finset.range n, charFun ν ξ := by
        apply Finset.prod_congr rfl
        intro k hk
        exact congrArg (fun μ : Measure ℝ => charFun μ ξ)
          (hincrement_law k).map_eq
  simpa using hchar_sum

/-- The marginal at integer time `n` is the law of the sum of the first `n`
coordinates under the canonical i.i.d. sequence whose common law is the
time-one marginal. -/
theorem map_eval_nat_eq_iidSum
    (h : IsLevyProcess X P) (n : ℕ) (hn : 0 < n) :
    P.map (fun ω => X (n : ℝ≥0) ω) =
      (iidSequenceLaw (P.map fun ω => X 1 ω)).map
        (fun sequence : ℕ → ℝ => ∑ k ∈ Finset.range n, sequence k) := by
  have hν_probability : IsProbabilityMeasure (P.map fun ω => X 1 ω) := by
    apply (Measure.isProbabilityMeasure_map_iff (h.aemeasurable_eval 1)).2
    infer_instance
  have hnR : (n : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  calc
    P.map (fun ω => X (n : ℝ≥0) ω) =
        (P.map (fun ω => X ((n : ℝ≥0) / (n : ℝ≥0)) ω)).convPower n :=
      h.map_eval_eq_convPower_div (n : ℝ≥0) n hn
    _ = (P.map (fun ω => X 1 ω)).convPower n := by
      rw [div_self hnR]
    _ = (iidSequenceLaw (P.map fun ω => X 1 ω)).map
        (fun sequence : ℕ → ℝ => ∑ k ∈ Finset.range n, sequence k) := by
      exact (@iidSequenceLaw_map_sum_range_eq_convPower
        (P.map fun ω => X 1 ω) hν_probability n).symm

/-- Every fixed-time marginal of a real-valued Lévy process is infinitely
divisible. The explicit convolution-root formula gives the required root for
each positive integer. -/
theorem isInfinitelyDivisible_timeMarginal
    (h : IsLevyProcess X P) (t : ℝ≥0) :
    IsInfinitelyDivisible (P.map fun ω => X t ω) := by
  intro n hn
  let ν : Measure ℝ := P.map fun ω => X (t / (n : ℝ≥0)) ω
  have hν_probability : IsProbabilityMeasure ν := by
    apply (Measure.isProbabilityMeasure_map_iff
      (h.aemeasurable_eval (t / (n : ℝ≥0)))).2
    infer_instance
  exact ⟨ν, hν_probability, h.map_eval_eq_convPower_div t n hn⟩

end ProbabilityTheory.IsLevyProcess

end
