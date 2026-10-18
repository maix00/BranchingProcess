/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Independence.FirstPassageGrid
public import Probability.Process.Path.FirstPassage.GridApproximation
public import Probability.Process.Brownian.Reflection.Path.UnboundedBelow
import Probability.Process.TimeGrid.Expanding
import MeasureTheory.Measure.Convergence.MapInvariance
public import Probability.MeasureTheory.Convergence.IndependentLimits

/-!
# Brownian future path at first passage

The public theorem in this file is:

- `ProbabilityTheory.IsBrownianReal.measure_shiftToZero_firstPassageBelow_eq`:
  for each real level $a$, the path
  $u\mapsto B(\tau_a+u)-B(\tau_a)$ at
  $\tau_a=\inf\{t:B_t\le a\}$ has the original Brownian path law.
- `ProbabilityTheory.IsBrownianReal.indepFun_shiftToZero_freezeAfter_firstPassageBelow`:
  the same future path is independent of the path stopped at $\tau_a$.

The proof takes expanding finite observation grids, uses the
finite-valued stopping-time law, and passes to their almost-sure path
limit. This is the marginal strong-Markov step behind the Lévy
decomposition cited in Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*,
Lemma 2.3, equation (2.2), Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098, referring to Kiyosi Itô and Henry P.
McKean, *Diffusion Processes and Their Sample Paths* (1965), §1.7.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- Every finite first-passage time is approached from above by the
expanding first-passage observation grids. -/
private lemma tendsto_expandingGridCeiling_of_finite
    (a : ℝ) (f : C(ℝ≥0, ℝ)) (τ : ℝ≥0)
    (hτ : firstPassageBelow f a = τ) :
    Filter.Tendsto
      (fun n => expandingGridTime n
        (firstPassageGridCeiling (expandingGridCount n)
          (expandingGridTime n) a f))
      Filter.atTop (nhds τ) := by
  exact tendsto_firstPassageGridCeiling_time_of_finite
    expandingGridCount expandingGridTime expandingGridTime_mono
    a f τ hτ (expandingGridTime_eventually_cover τ)
    (fun b hb => expandingGridTime_dense τ b hb)

/-- Brownian motion restarted at its first passage below any fixed
level has the original Brownian path law. -/
theorem IsBrownianReal.measure_shiftToZero_firstPassageBelow_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (a : ℝ) :
    (P.map (hB.continuousPathMap hBmeasurable)).map
        (fun f => shiftToZero f (firstPassageBelow f a).untopA) =
      P.map (hB.continuousPathMap hBmeasurable) := by
  let μ := P.map (hB.continuousPathMap hBmeasurable)
  haveI : IsProbabilityMeasure P := (hB.hasLaw ∅).isProbabilityMeasure
  haveI : IsFiniteMeasure μ := inferInstance
  let F : C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun f =>
    shiftToZero f (firstPassageBelow f a).untopA
  let Fₙ : ℕ → C(ℝ≥0, ℝ) → C(ℝ≥0, ℝ) := fun n f =>
    shiftToZero f (expandingGridTime n
      (firstPassageGridCeiling (expandingGridCount n)
        (expandingGridTime n) a f))
  have hF : Measurable F :=
    measurable_shiftToZero.comp
      (measurable_id.prodMk (measurable_firstPassageBelow a).untopA)
  have hFₙ (n : ℕ) : Measurable (Fₙ n) := by
    have hT : Measurable (fun f : C(ℝ≥0, ℝ) =>
        expandingGridTime n
          (firstPassageGridCeiling (expandingGridCount n)
            (expandingGridTime n) a f)) :=
      (measurable_of_finite (expandingGridTime n)).comp
        (measurable_firstPassageGridCeiling
          (expandingGridCount n) (expandingGridTime n) a)
    exact measurable_shiftToZero.comp (measurable_id.prodMk hT)
  have hfinite : ∀ᵐ f ∂μ, firstPassageBelow f a ≠ ⊤ := by
    filter_upwards [hB.ae_continuousPath_unboundedBelow hBmeasurable]
      with f hdesc
    intro htop
    obtain ⟨u, hu⟩ := hdesc a
    have hnever := (firstPassageBelow_eq_top_iff f a).mp htop u
    exact (not_lt_of_ge hu.le) hnever
  have hlim : ∀ᵐ f ∂μ,
      Filter.Tendsto (fun n => Fₙ n f) Filter.atTop (nhds (F f)) := by
    filter_upwards [hfinite] with f hf
    obtain ⟨τ, hτ⟩ := WithTop.ne_top_iff_exists.mp hf
    have htime := tendsto_expandingGridCeiling_of_finite a f τ hτ.symm
    have htarget : F f = shiftToZero f τ := by
      change shiftToZero f (firstPassageBelow f a).untopA = shiftToZero f τ
      rw [← hτ]
      rfl
    rw [htarget]
    exact continuous_shiftToZero.continuousAt.tendsto.comp
      (tendsto_const_nhds.prodMk_nhds htime)
  have hinv (n : ℕ) : μ.map (Fₙ n) = μ := by
    rw [Measure.map_map (hFₙ n)
      (hB.measurable_continuousPathMap hBmeasurable)]
    exact hB.measure_shiftToZero_firstPassageGridCeiling_eq hBmeasurable
      (expandingGridCount n) (expandingGridTime n)
      (expandingGridTime_mono n) a
  exact Measure.map_eq_of_ae_pointwise_limit μ F Fₙ hF hFₙ hlim hinv

/-- At a Brownian first-passage time, the future increment path is
independent of the stopped past path. -/
theorem IsBrownianReal.indepFun_shiftToZero_freezeAfter_firstPassageBelow
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBmeasurable : ∀ u, Measurable (B u)) (a : ℝ) :
    (fun ω => shiftToZero (hB.continuousPathMap hBmeasurable ω)
      (firstPassageBelow (hB.continuousPathMap hBmeasurable ω) a).untopA) ⟂ᵢ[P]
    (fun ω => freezeAfter (hB.continuousPathMap hBmeasurable ω)
      (firstPassageBelow (hB.continuousPathMap hBmeasurable ω) a).untopA) := by
  let pathB := hB.continuousPathMap hBmeasurable
  let μ := P.map pathB
  letI : IsProbabilityMeasure P := (hB.hasLaw ∅).isProbabilityMeasure
  let t : Ω → ℝ≥0 := fun ω => (firstPassageBelow (pathB ω) a).untopA
  let tₙ : ℕ → Ω → ℝ≥0 := fun n ω =>
    expandingGridTime n
      (firstPassageGridCeiling (expandingGridCount n)
        (expandingGridTime n) a (pathB ω))
  let F : Ω → C(ℝ≥0, ℝ) := fun ω => shiftToZero (pathB ω) (t ω)
  let G : Ω → C(ℝ≥0, ℝ) := fun ω => freezeAfter (pathB ω) (t ω)
  let Fₙ : ℕ → Ω → C(ℝ≥0, ℝ) := fun n ω => shiftToZero (pathB ω) (tₙ n ω)
  let Gₙ : ℕ → Ω → C(ℝ≥0, ℝ) := fun n ω => freezeAfter (pathB ω) (tₙ n ω)
  have hpathB : Measurable pathB := hB.measurable_continuousPathMap hBmeasurable
  have ht : Measurable t := ((measurable_firstPassageBelow a).comp hpathB).untopA
  have htₙ (n : ℕ) : Measurable (tₙ n) :=
    (measurable_of_finite (expandingGridTime n)).comp
      ((measurable_firstPassageGridCeiling
        (expandingGridCount n) (expandingGridTime n) a).comp hpathB)
  have hF : Measurable F := measurable_shiftToZero.comp (hpathB.prodMk ht)
  have hG : Measurable G := measurable_freezeAfter_pair.comp (hpathB.prodMk ht)
  have hFₙ (n : ℕ) : Measurable (Fₙ n) :=
    measurable_shiftToZero.comp (hpathB.prodMk (htₙ n))
  have hGₙ (n : ℕ) : Measurable (Gₙ n) :=
    measurable_freezeAfter_pair.comp (hpathB.prodMk (htₙ n))
  have hfinite : ∀ᵐ f ∂μ, firstPassageBelow f a ≠ ⊤ := by
    filter_upwards [hB.ae_continuousPath_unboundedBelow hBmeasurable]
      with f hdesc
    intro htop
    obtain ⟨u, hu⟩ := hdesc a
    have hnever := (firstPassageBelow_eq_top_iff f a).mp htop u
    exact (not_lt_of_ge hu.le) hnever
  have hfiniteΩ : ∀ᵐ ω ∂P, firstPassageBelow (pathB ω) a ≠ ⊤ :=
    ae_of_ae_map hpathB.aemeasurable hfinite
  have htime : ∀ᵐ ω ∂P,
      Filter.Tendsto (fun n => tₙ n ω) Filter.atTop (nhds (t ω)) := by
    filter_upwards [hfiniteΩ] with ω hω
    obtain ⟨τ, hτ⟩ := WithTop.ne_top_iff_exists.mp hω
    have htarget : t ω = τ := by
      change (firstPassageBelow (pathB ω) a).untopA = τ
      rw [← hτ]
      rfl
    rw [htarget]
    exact tendsto_expandingGridCeiling_of_finite a (pathB ω) τ hτ.symm
  have hFlim : ∀ᵐ ω ∂P,
      Filter.Tendsto (fun n => Fₙ n ω) Filter.atTop (nhds (F ω)) :=
    htime.mono (fun ω hω =>
      continuous_shiftToZero.continuousAt.tendsto.comp
        (tendsto_const_nhds.prodMk_nhds hω))
  have hGlim : ∀ᵐ ω ∂P,
      Filter.Tendsto (fun n => Gₙ n ω) Filter.atTop (nhds (G ω)) :=
    htime.mono (fun ω hω =>
      continuous_freezeAfter.continuousAt.tendsto.comp
        (tendsto_const_nhds.prodMk_nhds hω))
  have hPairlim : ∀ᵐ ω ∂P,
      Filter.Tendsto (fun n => (Fₙ n ω, Gₙ n ω)) Filter.atTop
        (nhds (F ω, G ω)) :=
    (hFlim.and hGlim).mono fun _ hω => hω.1.prodMk_nhds hω.2
  have hPairdist : MeasureTheory.TendstoInDistribution
      (fun n ω => (Fₙ n ω, Gₙ n ω)) Filter.atTop
      (fun ω => (F ω, G ω)) (fun _ => P) P := by
    exact MeasureTheory.tendstoInDistribution_of_ae_tendsto
      (fun n => ((hFₙ n).prodMk (hGₙ n)).aemeasurable)
      (hF.prodMk hG).aemeasurable hPairlim
  have hind (n : ℕ) : Fₙ n ⟂ᵢ[P] Gₙ n :=
    hB.indepFun_shiftToZero_freezeAfter_firstPassageGridCeiling
      hBmeasurable (expandingGridCount n) (expandingGridTime n)
      (expandingGridTime_mono n) a
  exact indepFun_of_tendstoInDistribution_pair
    (F := Fₙ) (G := Gₙ) (F' := F) (G' := G)
    (μ := fun _ => P) (μ' := P) hPairdist hind

end ProbabilityTheory

end
