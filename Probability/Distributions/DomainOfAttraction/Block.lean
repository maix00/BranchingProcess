/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.DomainOfAttraction.Basic
public import Probability.ConvergenceInDistribution.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Block endpoints in a domain of attraction

This module transfers convergence of normalized i.i.d. sums to a varying
block length and spatial scale.  The centering sequence remains explicit:
applications to uncentered small-deviation events must separately establish
that its contribution vanishes at the spatial scale being used.

## Public declarations

- `ProbabilityTheory.IsInDomainOfAttractionAlong.tendstoInDistribution_partialSum_div`:
  if $m_n\to\infty$, $a_{m_n}/s_n\to r$, $b_{m_n}/s_n\to c$, and $s_n\ne0$
  eventually, then for i.i.d. $X_k\sim\nu$ and $Z\sim\mu$,
  \[
    \frac{1}{s_n}\sum_{k<m_n}X_k\ \Rightarrow\ rZ+c,
  \]
  assuming $\nu$ is in the domain of attraction of $\mu$ with norming $a_n$
  and centering $b_n$.
-/

open Filter MeasureTheory
open scoped Topology BigOperators

@[expose] public section

namespace ProbabilityTheory

/-- A block endpoint converges to the domain-of-attraction limit at any
spatial scale whose ratio to the norming sequence converges.  The centering term is retained in
the limit, so this result applies to centered and uncentered domains of
attraction without silently discarding a drift.

The block lengths must tend to infinity.  The scale and centering ratios are
stated directly; applications derive them from the appropriate norming and
regular-variation hypotheses.

## Public declarations

* `ProbabilityTheory.IsInDomainOfAttractionAlong.tendstoInDistribution_partialSum_div` states
  that if $m_n\to\infty$, $a_{m_n}/s_n\to r$, $b_{m_n}/s_n\to c$, and
  $s_n\ne0$ eventually, then
  $s_n^{-1}\sum_{k<m_n}X_k$ converges in distribution to $rZ+c$, where
  $Z\sim\mu$ is the specified limit. The theorem keeps the centering ratio
  explicit and imposes no normalization beyond the attraction data.
-/
theorem IsInDomainOfAttractionAlong.tendstoInDistribution_partialSum_div
    {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {normalization center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit normalization center)
    (blockLength : ℕ → ℕ) (spatialScale : ℕ → ℝ)
    {r c : ℝ}
    (hblock : Tendsto blockLength atTop atTop)
    (hspatial : ∀ᶠ n in atTop, spatialScale n ≠ 0)
    (hratio : Tendsto
      (fun n => normalization (blockLength n) / spatialScale n)
      atTop (nhds r))
    (hcenter : Tendsto
      (fun n => center (blockLength n) / spatialScale n)
      atTop (nhds c)) :
    TendstoInDistribution
      (fun n (increments : ℕ → ℝ) =>
        (∑ k ∈ Finset.range (blockLength n), increments k) / spatialScale n)
      atTop (fun x => r * x + c)
      (fun _ => iidSequenceLaw ν) limit := by
  let walkLaw : Measure (ℕ → ℝ) := iidSequenceLaw ν
  have hnormalized := h.tendstoInDistribution.comp_tendsto hblock
  have hratioInMeasure : TendstoInMeasure walkLaw
      (fun n (_ : ℕ → ℝ) =>
        normalization (blockLength n) / spatialScale n)
      atTop (fun _ => r) := by
    apply tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    filter_upwards [] with increments
    simpa using hratio
  have hscaled := hnormalized.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop)
      hratioInMeasure (fun _ => aemeasurable_const)
  have hcenterInMeasure : TendstoInMeasure walkLaw
      (fun n (_ : ℕ → ℝ) =>
        center (blockLength n) / spatialScale n)
      atTop (fun _ => c) := by
    apply tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
    filter_upwards [] with increments
    simpa using hcenter
  have hsum := hscaled.add_of_tendstoInMeasure_const
      (Y := fun n (_ : ℕ → ℝ) =>
        center (blockLength n) / spatialScale n)
      hcenterInMeasure (fun _ => aemeasurable_const)
  apply hsum.congr_eventually
  · filter_upwards [hblock.eventually h.eventually_scale_pos, hspatial]
      with n hblockNorm hspatial
    filter_upwards [] with increments
    change normalization (blockLength n) / spatialScale n *
        normalizedIidSum normalization center (blockLength n) increments +
          center (blockLength n) / spatialScale n =
      (∑ k ∈ Finset.range (blockLength n), increments k) / spatialScale n
    unfold normalizedIidSum
    field_simp [hblockNorm.ne', hspatial]
    simp
  · intro n
    exact (Finset.measurable_sum (Finset.range (blockLength n))
      (fun k _ => measurable_pi_apply k)).div_const (spatialScale n) |>.aemeasurable

end ProbabilityTheory

end
