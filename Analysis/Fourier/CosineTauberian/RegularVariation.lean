/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Analysis.Asymptotics.RegularVariation.AtZero.Potter
public import Analysis.Fourier.CosineTauberian.Kernel
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Regular variation under the cosine Tauberian kernel

This module combines the nonmonotone Potter envelope with Mathlib's dominated
convergence theorem. It isolates the analytic integral limit from probability
and tail-identification arguments.
-/

open Filter MeasureTheory Set
open scoped Topology

@[expose] public section

namespace Analysis.Fourier.CosineTauberian

/-- If `f` is regularly varying at zero and has compact-uniform ratio control
on `[1, 2]`, then its ratio integral against the cosine Tauberian kernel
converges to the corresponding Mellin integral. The global domination uses a
nonmonotone Potter bound; the eventual bound on `f` controls multipliers that
move beyond the local Potter range. -/
theorem tendsto_integral_ratio_mul_cosineTauberianKernel
    {f : ℝ → ℝ} {ρ δ M : ℝ}
    (hcont : Continuous f)
    (hreg : Asymptotics.IsRegularlyVaryingAtZero f ρ)
    (huniform : TendstoUniformlyOn
      (fun u r => f (r * u) / f u) (fun r => r ^ ρ)
      (𝓝[>] (0 : ℝ)) (Set.Icc 1 2))
    (hρ₀ : 0 < ρ)
    (hδ₀ : 0 < δ) (hδρ : δ < ρ) (hρδ₂ : ρ + δ < 2)
    (hM₀ : 0 ≤ M)
    (hnonneg : ∀ x, 0 ≤ f x)
    (hbounded : ∀ x, f x ≤ M) :
    Tendsto (fun u : ℝ =>
      ∫ s in Ioi (0 : ℝ), f (s * u) / f u * cosineTauberianKernel s)
      (𝓝[>] (0 : ℝ))
      (nhds <| ∫ s in Ioi (0 : ℝ), s ^ ρ * cosineTauberianKernel s) := by
  let p : ℝ := ρ - δ
  let q : ℝ := ρ + δ
  have hp : 0 < p := by dsimp [p]; linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hq₂ : q < 2 := by dsimp [q]; linarith
  obtain ⟨U, C, hU, hC, hposU, hpotter⟩ :=
    Asymptotics.IsRegularlyVaryingAtZero.exists_global_potter_envelope_of_uniform_ratio
      hreg.eventually_pos huniform hρ₀ hδ₀ hδρ hM₀
      (fun _ _ => hnonneg _) (fun _ _ => hbounded _)
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℝ := fun u s => f (s * u) / f u * cosineTauberianKernel s
  let major : ℝ → ℝ := fun s => C * (s ^ p + s ^ q) *
    |cosineTauberianKernel s|
  have hp₂ : p < 2 := by dsimp [p]; linarith
  have hpKernel := integrableOn_rpow_mul_abs_cosineTauberianKernel hp hp₂
  have hqKernel := integrableOn_rpow_mul_abs_cosineTauberianKernel hq hq₂
  have hpScaled : IntegrableOn
      (fun s : ℝ => C * (s ^ p * |cosineTauberianKernel s|)) (Ioi 0) :=
    hpKernel.const_mul C
  have hqScaled : IntegrableOn
      (fun s : ℝ => C * (s ^ q * |cosineTauberianKernel s|)) (Ioi 0) :=
    hqKernel.const_mul C
  have hmajor : Integrable major μ := by
    have hsum : IntegrableOn
        (fun s : ℝ => C * (s ^ p * |cosineTauberianKernel s|) +
          C * (s ^ q * |cosineTauberianKernel s|)) (Ioi 0) :=
      hpScaled.add hqScaled
    have hEq : (fun s : ℝ => C * (s ^ p * |cosineTauberianKernel s|) +
        C * (s ^ q * |cosineTauberianKernel s|)) =ᵐ[μ] major := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      dsimp [major]
      ring
    have hsum' : Integrable (fun s : ℝ => C * (s ^ p *
        |cosineTauberianKernel s|) + C * (s ^ q *
        |cosineTauberianKernel s|)) μ := by
      simpa [μ] using hsum.integrable
    exact hsum'.congr hEq
  have hmeas : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (F u) μ := by
    filter_upwards [] with u
    have hK : Measurable cosineTauberianKernel :=
      continuous_cosineTauberianKernel.measurable
    have hF : Measurable (F u) := by
      dsimp [F]
      exact ((hcont.comp (continuous_id.mul continuous_const)).measurable
        |>.div_const (f u)).mul hK
    exact hF.aestronglyMeasurable
  have hsmall : Set.Iio U ∈ 𝓝[>] (0 : ℝ) :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hU)
  have hbound : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      ∀ᵐ s ∂μ, ‖F u s‖ ≤ major s := by
    filter_upwards [self_mem_nhdsWithin, hsmall, hreg.eventually_pos]
      with u hu huU hfu
    have hfu' : 0 < f u := hfu
    have hu' : 0 < u := hu
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs : 0 < s := hs
    have hratio : f (s * u) / f u ≤ C * (s ^ p + s ^ q) :=
      hpotter hu' huU hs
    have hratioNonneg : 0 ≤ f (s * u) / f u :=
      div_nonneg (hnonneg _) hfu'.le
    dsimp [F, major]
    rw [abs_mul, abs_of_nonneg hratioNonneg]
    exact mul_le_mul_of_nonneg_right hratio (abs_nonneg _)
  have hlim : ∀ᵐ s ∂μ,
      Tendsto (fun u : ℝ => F u s) (𝓝[>] (0 : ℝ))
        (nhds (s ^ ρ * cosineTauberianKernel s)) := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [] with s hs
    have hspos : 0 < s := hs
    have hratio : Tendsto (fun u : ℝ => f (s * u) / f u)
        (𝓝[>] (0 : ℝ)) (nhds (s ^ ρ)) := hreg.ratio_tendsto (c := s) hspos
    simpa [F] using hratio.mul_const (cosineTauberianKernel s)
  have hmajorInt : Integrable major μ := hmajor
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝[>] (0 : ℝ)) (F := F)
    (f := fun s : ℝ => s ^ ρ * cosineTauberianKernel s)
    major hmeas hbound hmajorInt hlim
  simpa [μ, F] using hDCT

end Analysis.Fourier.CosineTauberian

end
