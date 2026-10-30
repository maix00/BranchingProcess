/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.DomainOfAttraction.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Changing a domain-of-attraction normalization

## Public declarations

* `ProbabilityTheory.IsInDomainOfAttractionAlong.changeNormalization` states that if
  $a_n/a'_n\to r$ and both normalizations are eventually positive, attraction
  along $a_n$ to $\mu$ implies attraction along $a'_n$ to the pushforward of
  $\mu$ by $x\mapsto rx$.
* `ProbabilityTheory.IsInDomainOfAttractionAlong.rescale` is the positive constant case: from
  attraction along $a_n$, it gives attraction along $a_n/r$ to the law of
  $rX$, for $r>0$. It is derived from `changeNormalization`.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- A convergent deterministic sequence, regarded as constant random
variables, converges in measure to its limit. -/
private lemma tendstoInMeasure_const_of_tendsto_real
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : ℕ → ℝ} {c : ℝ} (hf : Tendsto f atTop (nhds c)) :
    TendstoInMeasure μ (fun n _ => f n) atTop (fun _ => c) := by
  apply tendstoInMeasure_of_tendsto_ae
    (fun _ => aestronglyMeasurable_const)
  filter_upwards [] with ω
  simpa using hf

set_option linter.style.haveILetI false in
/-- If two eventually positive normalization sequences have an asymptotic
ratio, replacing the denominator in a domain-of-attraction limit changes the
limiting law by the corresponding constant multiplier. This is the
continuous-mapping theorem applied to the deterministic ratio. -/
theorem IsInDomainOfAttractionAlong.changeNormalization
    {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center scale' : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center)
    (hscale' : ∀ᶠ n : ℕ in atTop, 0 < scale' n)
    {r : ℝ}
    (hratio : Tendsto (fun n => scale n / scale' n) atTop (nhds r)) :
    IsInDomainOfAttractionAlong ν (limit.map fun x => r * x) scale' center := by
  let q : ℕ → ℝ := fun n => scale n / scale' n
  let target : Measure ℝ := limit.map fun x => r * x
  letI : IsProbabilityMeasure target := by
    dsimp [target]
    infer_instance
  have hq : TendstoInMeasure (iidSequenceLaw ν)
      (fun n _ => q n) atTop (fun _ => r) := by
    exact tendstoInMeasure_const_of_tendsto_real hratio
  have hjoint := h.tendstoInDistribution.continuous_comp_prodMk_of_tendstoInMeasure_const
    (X := normalizedIidSum scale center)
    (Y := fun n _ => q n) (Z := id) (c := r)
    (g := fun p : ℝ × ℝ => p.1 * p.2) (by fun_prop) hq
    (fun _ => measurable_const.aemeasurable)
  have hreplace : ∀ᶠ n : ℕ in atTop,
      (fun ω => normalizedIidSum scale center n ω * q n) =ᵐ[iidSequenceLaw ν]
        normalizedIidSum scale' center n := by
    filter_upwards [h.eventually_scale_pos, hscale'] with n hn hn'
    filter_upwards [] with ω
    simp only [normalizedIidSum, q]
    field_simp [ne_of_gt hn, ne_of_gt hn']
  have hchanged := hjoint.congr_eventually hreplace
    (fun n => (normalizedIidSum_measurable scale' center n).aemeasurable)
  have hmap : limit.map (fun x => x * r) = target.map id := by
    dsimp [target]
    rw [Measure.map_id]
    congr 1
    funext x
    ring
  have hchanged' := hchanged.congr_limit aemeasurable_id hmap
  exact ⟨hscale', hchanged'⟩

/-- Rescaling the normalization by `r⁻¹` rescales the limiting law by `r`.
This is the constant-ratio case of `changeNormalization`. -/
theorem IsInDomainOfAttractionAlong.rescale
    {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center)
    (r : ℝ) (hr : 0 < r) :
    IsInDomainOfAttractionAlong ν (limit.map fun x => r * x)
      (fun n => r⁻¹ * scale n) center := by
  have hscale' : ∀ᶠ n : ℕ in atTop, 0 < r⁻¹ * scale n := by
    filter_upwards [h.eventually_scale_pos] with n hn
    exact mul_pos (inv_pos.mpr hr) hn
  have hratio : Tendsto (fun n => scale n / (r⁻¹ * scale n))
      atTop (nhds r) := by
    have heq : (fun n => scale n / (r⁻¹ * scale n)) =ᶠ[atTop]
        fun _ => r := by
      filter_upwards [h.eventually_scale_pos] with n hn
      field_simp [hr.ne', hn.ne']
    exact tendsto_const_nhds.congr' heq.symm
  exact h.changeNormalization hscale' hratio

end ProbabilityTheory

end
