module

public import Probability.Distributions.DomainOfAttraction.Basic
public import Probability.Sequence.IID.CharacteristicFunction
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Characteristic functions in a domain of attraction

The characteristic function of a normalized i.i.d. sum is expressed using
the one-step characteristic function, scale, and centering.  This module is
independent of any particular limiting distribution.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- The characteristic function of a normalized centered sum under the
canonical i.i.d. sequence law. -/
theorem charFun_map_normalizedIidSum
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (scale center : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    charFun ((iidSequenceLaw ν).map (normalizedIidSum scale center n)) t =
      (charFun ν ((scale n)⁻¹ * t)) ^ n *
        Complex.exp ((inner ℝ (-((scale n)⁻¹ * center n)) t) * Complex.I) := by
  let S : (ℕ → ℝ) → ℝ := fun sequence =>
    ∑ k ∈ Finset.range n, sequence k
  let r : ℝ := (scale n)⁻¹
  let q : ℝ := -(r * center n)
  have hnorm : normalizedIidSum scale center n = fun sequence => r * S sequence + q := by
    funext sequence
    simp [normalizedIidSum, S, r, q]
    ring
  have hsumMeas : AEMeasurable S (iidSequenceLaw ν) := by
    exact (Finset.measurable_sum (Finset.range n)
      (fun k _ => measurable_pi_apply k)).aemeasurable
  have hsumChar := iidSequenceLaw_charFun_sum (ν := ν) n
  rw [hnorm]
  have hmap : (iidSequenceLaw ν).map (fun sequence => r * S sequence + q) =
      ((iidSequenceLaw ν).map (fun sequence => r * S sequence)).map (fun x => x + q) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmap, charFun_map_add_const]
  rw [charFun_map_mul_comp hsumMeas r t, hsumChar]

/-- Convergence in distribution in a stable domain of attraction forces the
corresponding explicit characteristic-function expression to converge. -/
theorem IsInDomainOfAttractionAlong.tendsto_charFun_normalizedIidSum
    {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center) (t : ℝ) :
    Tendsto
      (fun n => (charFun ν ((scale n)⁻¹ * t)) ^ n *
        Complex.exp ((inner ℝ (-((scale n)⁻¹ * center n)) t) * Complex.I))
      atTop (nhds (charFun limit t)) := by
  have hchar := h.tendstoInDistribution.tendsto_charFun t
  have heq : (fun n =>
      charFun ((iidSequenceLaw ν).map (normalizedIidSum scale center n)) t) =ᶠ[atTop]
      (fun n => (charFun ν ((scale n)⁻¹ * t)) ^ n *
        Complex.exp ((inner ℝ (-((scale n)⁻¹ * center n)) t) * Complex.I)) := by
    filter_upwards [] with n
    exact charFun_map_normalizedIidSum (ν := ν) scale center n t
  simpa using hchar.congr' heq

/-- Taking absolute values removes the deterministic centering phase from the
domain-of-attraction characteristic-function limit. -/
theorem IsInDomainOfAttractionAlong.tendsto_norm_charFun_oneStep_pow
    {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center) (t : ℝ) :
    Tendsto (fun n => ‖charFun ν ((scale n)⁻¹ * t)‖ ^ n)
      atTop (nhds ‖charFun limit t‖) := by
  have hcomplex := h.tendsto_charFun_normalizedIidSum t
  have hnorm := hcomplex.norm
  have hphase (n : ℕ) :
      ‖Complex.exp (inner ℝ (-((scale n)⁻¹ * center n)) t * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have heq : (fun n =>
      ‖(charFun ν ((scale n)⁻¹ * t)) ^ n *
        Complex.exp (inner ℝ (-((scale n)⁻¹ * center n)) t * Complex.I)‖) =
      fun n => ‖charFun ν ((scale n)⁻¹ * t)‖ ^ n := by
    funext n
    rw [norm_mul, norm_pow, hphase]
    simp
  rw [heq] at hnorm
  exact hnorm

end ProbabilityTheory

end
