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

The public theorem is
`ProbabilityTheory.IsInDomainOfAttractionAlong.changeNormalization`: if
`scale n / scale' n → r` and both scales are eventually positive, attraction
along `scale` to `limit` implies attraction along `scale'` to the pushforward
of `limit` under `x ↦ r x`.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- A convergent deterministic sequence, regarded as constant random
variables, converges in measure to its limit. -/
private lemma tendstoInMeasure_const_of_tendsto_real
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    {f : ι → ℝ} {c : ℝ} (hf : Tendsto f l (nhds c)) :
    TendstoInMeasure μ (fun i _ => f i) l (fun _ => c) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hzero : (fun i => μ {ω | ε ≤ dist (f i) c}) =ᶠ[l] fun _ => 0 := by
    filter_upwards [hf.eventually (Metric.ball_mem_nhds c hε)] with i hi
    have hdist : dist (f i) c < ε := by
      simpa [Metric.mem_ball, dist_comm] using hi
    have hset : {ω : Ω | ε ≤ dist (f i) c} = ∅ := by
      ext ω
      simp [not_le_of_gt hdist]
    simp [hset]
  exact tendsto_const_nhds.congr' hzero.symm

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

end ProbabilityTheory

end
