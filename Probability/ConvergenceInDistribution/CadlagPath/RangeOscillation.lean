/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.Portmanteau
public import Topology.Cadlag.Skorokhod.SmallDeviation.PathSets

/-!
# Range probabilities under Skorokhod convergence

## Public declarations

- `MeasureTheory.TendstoInDistribution.limsup_measure_rangeOscillationLe_le_of_scalePath`:
  if $X_i$ converges in distribution to the law of $cZ$, where $c>0$ and
  $Z(0)=0$ almost surely, then for $w\in\mathbb R$ and $\delta>0$,
  \[
  \limsup_i\mathbb P(\operatorname{osc}(X_i)\le w)
  \le \mathbb P\!\left(Z(0)=0,\ \operatorname{osc}(Z)<\frac{w+\delta}{c}\right).
  \]
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace MeasureTheory.TendstoInDistribution

/-- Under convergence in distribution to a positively scaled path law, the
probability of a closed range-oscillation constraint is bounded by the
limiting law's slightly wider open range tube. The limiting law is assumed to
start at zero almost surely. -/
theorem limsup_measure_rangeOscillationLe_le_of_scalePath
    {I : Type*} {Ω : I → Type*} {mΩ : ∀ i, MeasurableSpace (Ω i)}
    {μ : (i : I) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    {X : ∀ i, Ω i → CadlagPath unitInterval ℝ} {l : Filter I}
    {c width margin : ℝ}
    (hlimit : TendstoInDistribution X l id μ
      (P.map (Skorokhod.scalePath c)))
    (hstart : ∀ᵐ path ∂P, path ⊥ = 0)
    (hc : 0 < c) (hmargin : 0 < margin) :
    l.limsup (fun i => (μ i).map (X i) (Skorokhod.rangeOscillationLe width)) ≤
      P (Skorokhod.rangeTubeStartingAtZero ((width + margin) / (2 * c))) := by
  have hport : l.limsup (fun i =>
      (μ i).map (X i) (Skorokhod.rangeOscillationLe width)) ≤
      (P.map (Skorokhod.scalePath c)) (Skorokhod.rangeOscillationLe width) := by
    simpa [Measure.map_id] using
      hlimit.limsup_measure_map_le_of_isClosed
        (Skorokhod.isClosed_rangeOscillationLe width)
  have hscaledBound :
      (P.map (Skorokhod.scalePath c)) (Skorokhod.rangeOscillationLe width) ≤
        P (Skorokhod.rangeTubeStartingAtZero ((width + margin) / (2 * c))) := by
    have hscaleMeas : Measurable (fun path : CadlagPath unitInterval ℝ =>
        Skorokhod.scalePath c path) := by
      exact (Skorokhod.continuous_scalePath.comp
        (continuous_const.prodMk continuous_id)).measurable
    rw [Measure.map_apply hscaleMeas
      (Skorokhod.isClosed_rangeOscillationLe width).measurableSet]
    apply measure_mono_ae
    filter_upwards [hstart] with path hstartPath
    intro hpath
    change Skorokhod.scalePath c path ∈ Skorokhod.rangeOscillationLe width at hpath
    have hosc : path ∈ Skorokhod.rangeOscillationLe (width / c) := by
      intro s t
      have hmul : c * |path s - path t| ≤ width := by
        have hscaled := hpath s t
        have heq : |c * path s - c * path t| =
            c * |path s - path t| := by
          rw [← mul_sub, abs_mul, abs_of_pos hc]
        calc
          c * |path s - path t| = |c * path s - c * path t| := heq.symm
          _ = dist (c * path s) (c * path t) := by rw [Real.dist_eq]
          _ ≤ width := by simpa [Skorokhod.scalePath_apply] using hscaled
      have hmul' : c * dist (path s) (path t) ≤ width := by
        simpa [Real.dist_eq] using hmul
      exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hmul')
    have hopen := Skorokhod.rangeOscillationLe_subset_oscillationInOpenTube
      (width / c) (margin / c) (div_pos hmargin hc) hosc
    have hwidthEq : width / c + margin / c =
        2 * ((width + margin) / (2 * c)) := by
      field_simp [hc.ne']
    change path ∈ {f | f ⊥ = 0} ∩
      Skorokhod.oscillationInOpenTube (2 * ((width + margin) / (2 * c)))
    exact ⟨hstartPath, by rw [← hwidthEq]; exact hopen⟩
  exact hport.trans hscaledBound

end MeasureTheory.TendstoInDistribution

end
