/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic

/-!
# Second-moment convergence with varying laws

The public theorems in this file are:

- `ProbabilityTheory.tendsto_integral_abs_sq_of_tendsto_tail_and_fourth_moment`:
  fixed-threshold tail probabilities tending to zero and a uniform fourth
  moment bound imply convergence of centered second moments to zero.
- `ProbabilityTheory.tendsto_integral_abs_sq_of_polynomial_tails_and_fourth_moment`:
  polynomial one-sided tail bounds and a uniform fourth moment bound imply the
  same second-moment convergence.
-/

@[expose] public section

open Filter MeasureTheory Topology

namespace ProbabilityTheory

/-- For a family of probability spaces that may vary with the index, convergence
of every fixed-threshold tail probability to zero together with a uniform
fourth-moment bound implies convergence of the second moments to zero. This
is the analytic last step from the two polynomial tail estimates and the
fourth-moment estimate in the trajectory-limit proof. -/
theorem tendsto_integral_abs_sq_of_tendsto_tail_and_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (X : ℕ → Ω → ℝ) (c : ℝ)
    (hX : ∀ n, Measurable (X n))
    (hfourth : ∃ C : ℝ, ∀ n,
      Integrable (fun ω => |X n ω - c| ^ 4) (μ n) ∧
        (∫ ω, |X n ω - c| ^ 4 ∂μ n) ≤ C)
    (htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ n).real {ω | ε ≤ |X n ω - c|})
        atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, |X n ω - c| ^ 2 ∂μ n)
      atTop (𝓝 0) := by
  obtain ⟨C, hfourth⟩ := hfourth
  have hC : 0 ≤ C := by
    letI : IsProbabilityMeasure (μ 0) := hμ 0
    have hnonneg : 0 ≤ ∫ ω, |X 0 ω - c| ^ 4 ∂μ 0 := by
      apply integral_nonneg
      intro ω
      positivity
    have hbound := (hfourth 0).2
    linarith
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hnonneg (n : ℕ) : 0 ≤ ∫ ω, |X n ω - c| ^ 2 ∂μ n :=
      by
        letI : IsProbabilityMeasure (μ n) := hμ n
        apply integral_nonneg
        intro ω
        positivity
    filter_upwards [] with n
    exact lt_of_lt_of_le hb (hnonneg n)
  · intro ε hε
    let δ : ℝ := Real.sqrt (ε / 3)
    let K : ℝ := Real.sqrt (3 * (C + 1) / ε)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact Real.sqrt_pos.2 (by positivity)
    have hK : 0 < K := by
      dsimp [K]
      exact Real.sqrt_pos.2 (by positivity)
    have htailδ := htail δ hδ
    have hthreshold : 0 < ε / 3 / K ^ 2 := by positivity
    have hsmallTail : ∀ᶠ n : ℕ in atTop,
        (μ n).real {ω | δ ≤ |X n ω - c|} < ε / 3 / K ^ 2 :=
      htailδ.eventually (Iio_mem_nhds hthreshold)
    have hδsq : δ ^ 2 = ε / 3 := by
      dsimp [δ]
      exact Real.sq_sqrt (by positivity)
    have hKsq : K ^ 2 = 3 * (C + 1) / ε := by
      dsimp [K]
      exact Real.sq_sqrt (by positivity)
    have hmomentSmall : C / K ^ 2 ≤ ε / 3 := by
      rw [hKsq]
      have heq : C / (3 * (C + 1) / ε) = ε * C / (3 * (C + 1)) := by
        field_simp [ne_of_gt hε]
      rw [heq]
      have hden : 0 < 3 * (C + 1) := by positivity
      rw [div_le_iff₀ hden]
      nlinarith [hC]
    filter_upwards [hsmallTail] with n hn
    letI : IsProbabilityMeasure (μ n) := hμ n
    let A : Set Ω := {ω | δ ≤ |X n ω - c|}
    let bad : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
    let y : Ω → ℝ := fun ω => |X n ω - c|
    have hA : MeasurableSet A := by
      exact measurableSet_Ici.preimage
        (Measurable.abs ((hX n).sub measurable_const))
    have hbad : Integrable bad (μ n) :=
      (integrable_const (1 : ℝ)).indicator hA
    have hfourInt : Integrable (fun ω => y ω ^ 4) (μ n) := by
      simpa [y] using (hfourth n).1
    have htailInt : Integrable (fun ω => (K ^ 2)⁻¹ * y ω ^ 4) (μ n) :=
      hfourInt.const_mul ((K ^ 2)⁻¹)
    have hboundInt : Integrable
        (fun ω => δ ^ 2 + K ^ 2 * bad ω + (K ^ 2)⁻¹ * y ω ^ 4)
        (μ n) := by
      exact ((integrable_const _).add (hbad.const_mul (K ^ 2))).add htailInt
    have hsecondInt : Integrable (fun ω => y ω ^ 2) (μ n) := by
      have hmajor : Integrable (fun ω => y ω ^ 4 + 1) (μ n) :=
        hfourInt.add (integrable_const 1)
      have hymeas : Measurable (fun ω => y ω ^ 2) := by
        exact (Measurable.abs ((hX n).sub measurable_const)).pow_const 2
      apply hmajor.mono' hymeas.aestronglyMeasurable
      filter_upwards [] with ω
      change ‖y ω ^ 2‖ ≤ y ω ^ 4 + 1
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (y ω))]
      have hy : 0 ≤ y ω ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg (y ω ^ 2 - 1)]
    have hpoint : ∀ ω,
        y ω ^ 2 ≤ δ ^ 2 + K ^ 2 * bad ω + (K ^ 2)⁻¹ * y ω ^ 4 := by
      intro ω
      have htailNonneg : 0 ≤ (K ^ 2)⁻¹ * y ω ^ 4 :=
        mul_nonneg (inv_nonneg.mpr (sq_nonneg K)) (by positivity)
      by_cases hAω : ω ∈ A
      · simp [A, bad, hAω]
        by_cases hKω : K ≤ y ω
        · have hKsq_le : K ^ 2 ≤ y ω ^ 2 := by
            have hleft : 0 ≤ y ω - K := sub_nonneg.mpr hKω
            have hright : 0 ≤ y ω + K := by positivity
            nlinarith [mul_nonneg hleft hright]
          have hfour : K ^ 2 * y ω ^ 2 ≤ y ω ^ 4 := by
            have hleft : 0 ≤ y ω ^ 2 - K ^ 2 := sub_nonneg.mpr hKsq_le
            have hright : 0 ≤ y ω ^ 2 := sq_nonneg _
            nlinarith [mul_nonneg hleft hright]
          have hquot : y ω ^ 2 ≤ (K ^ 2)⁻¹ * y ω ^ 4 := by
            calc
              y ω ^ 2 = (K ^ 2)⁻¹ * (K ^ 2 * y ω ^ 2) := by
                field_simp [ne_of_gt (sq_pos_of_pos hK)]
              _ ≤ (K ^ 2)⁻¹ * y ω ^ 4 :=
                mul_le_mul_of_nonneg_left hfour
                  (inv_nonneg.mpr (sq_nonneg K))
          calc
            y ω ^ 2 ≤ (K ^ 2)⁻¹ * y ω ^ 4 := hquot
            _ ≤ δ ^ 2 + K ^ 2 + (K ^ 2)⁻¹ * y ω ^ 4 := by
              nlinarith [sq_nonneg δ, sq_nonneg K]
        · have hyK : y ω ≤ K := le_of_not_ge hKω
          have hysq : y ω ^ 2 ≤ K ^ 2 := by
            have hleft : 0 ≤ K - y ω := sub_nonneg.mpr hyK
            have hright : 0 ≤ K + y ω := by positivity
            nlinarith [mul_nonneg hleft hright]
          calc
            y ω ^ 2 ≤ K ^ 2 := hysq
            _ ≤ δ ^ 2 + K ^ 2 + (K ^ 2)⁻¹ * y ω ^ 4 := by
              nlinarith [sq_nonneg δ, htailNonneg]
      · have hyδ : y ω < δ := lt_of_not_ge (by simpa [A, y] using hAω)
        simp [bad, hAω]
        have hysq : y ω ^ 2 ≤ δ ^ 2 := by
          have hleft : 0 ≤ δ - y ω := sub_nonneg.mpr hyδ.le
          have hright : 0 ≤ δ + y ω := by positivity
          nlinarith [mul_nonneg hleft hright]
        calc
          y ω ^ 2 ≤ δ ^ 2 := hysq
          _ ≤ δ ^ 2 + (K ^ 2)⁻¹ * y ω ^ 4 := by
            linarith
    have hmono := integral_mono_ae hsecondInt hboundInt
      (ae_of_all (μ n) hpoint)
    have hbadIntegral : (∫ ω, bad ω ∂μ n) = (μ n).real A := by
      simpa [bad] using integral_indicator_const (1 : ℝ) hA
    have hboundIntegral :
        (∫ ω, δ ^ 2 + K ^ 2 * bad ω + (K ^ 2)⁻¹ * y ω ^ 4 ∂μ n) =
          δ ^ 2 + K ^ 2 * (μ n).real A +
            (K ^ 2)⁻¹ * ∫ ω, y ω ^ 4 ∂μ n := by
      calc
        (∫ ω, δ ^ 2 + K ^ 2 * bad ω + (K ^ 2)⁻¹ * y ω ^ 4 ∂μ n) =
            ∫ ω, (δ ^ 2 + K ^ 2 * bad ω) + (K ^ 2)⁻¹ * y ω ^ 4 ∂μ n := by
              congr 1
        _ = (∫ ω, δ ^ 2 + K ^ 2 * bad ω ∂μ n) +
            (∫ ω, (K ^ 2)⁻¹ * y ω ^ 4 ∂μ n) :=
              integral_add ((integrable_const _).add (hbad.const_mul (K ^ 2))) htailInt
        _ = ((∫ ω, δ ^ 2 ∂μ n) + (∫ ω, K ^ 2 * bad ω ∂μ n)) +
            (∫ ω, (K ^ 2)⁻¹ * y ω ^ 4 ∂μ n) := by
              rw [integral_add (integrable_const _) (hbad.const_mul (K ^ 2))]
        _ = δ ^ 2 + K ^ 2 * (μ n).real A +
            (K ^ 2)⁻¹ * ∫ ω, y ω ^ 4 ∂μ n := by
              rw [integral_const_mul, integral_const_mul, hbadIntegral]
              simp [add_assoc]
    have hfourBound : (∫ ω, y ω ^ 4 ∂μ n) ≤ C := by
      simpa [y] using (hfourth n).2
    have hupper : (∫ ω, y ω ^ 2 ∂μ n) ≤
        δ ^ 2 + K ^ 2 * (μ n).real A + (K ^ 2)⁻¹ * C := by
      rw [hboundIntegral] at hmono
      have htailBound := mul_le_mul_of_nonneg_left hfourBound
        (inv_nonneg.mpr (sq_nonneg K))
      exact hmono.trans (by
        simpa [add_assoc] using add_le_add_left htailBound
          (δ ^ 2 + K ^ 2 * (μ n).real A))
    rw [hδsq] at hupper
    have htailTerm : K ^ 2 * (μ n).real A < ε / 3 := by
      have hmul := mul_lt_mul_of_pos_left hn (sq_pos_of_pos hK)
      calc
        K ^ 2 * (μ n).real A =
            K ^ 2 * (μ n).real {ω | δ ≤ |X n ω - c|} := by rfl
        _ < K ^ 2 * (ε / 3 / K ^ 2) := hmul
        _ = ε / 3 := by field_simp [ne_of_gt (sq_pos_of_pos hK)]
    have hmomentTerm : (K ^ 2)⁻¹ * C ≤ ε / 3 := by
      calc
        (K ^ 2)⁻¹ * C = C / K ^ 2 := by rw [div_eq_mul_inv]; ring
        _ ≤ ε / 3 := hmomentSmall
    have : (∫ ω, y ω ^ 2 ∂μ n) < ε := by
      calc
        (∫ ω, y ω ^ 2 ∂μ n) ≤ ε / 3 + K ^ 2 * (μ n).real A +
            (K ^ 2)⁻¹ * C := hupper
        _ < ε / 3 + ε / 3 + ε / 3 := by linarith
        _ = ε := by ring
    simpa [y] using this

/-- The two one-sided polynomial tail bounds used in the trajectory-limit
argument imply the fixed-threshold tail convergence required by
`tendsto_integral_abs_sq_of_tendsto_tail_and_fourth_moment`. The exponents may
depend on the threshold. -/
theorem tendsto_integral_abs_sq_of_polynomial_tails_and_fourth_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : ℕ → Measure Ω) (hμ : ∀ n, IsProbabilityMeasure (μ n))
    (X : ℕ → Ω → ℝ) (c : ℝ)
    (hX : ∀ n, Measurable (X n))
    (hfourth : ∃ C : ℝ, ∀ n,
      Integrable (fun ω => |X n ω - c| ^ 4) (μ n) ∧
        (∫ ω, |X n ω - c| ^ 4 ∂μ n) ≤ C)
    (hleft : ∀ z : ℝ, z < c → ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      (μ n).real {ω | X n ω ≤ z} ≤ 1 / ((n : ℝ) ^ α))
    (hright : ∀ z : ℝ, c < z → ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      (μ n).real {ω | z ≤ X n ω} ≤ 1 / ((n : ℝ) ^ α)) :
    Tendsto (fun n => ∫ ω, |X n ω - c| ^ 2 ∂μ n)
      atTop (𝓝 0) := by
  have hpolyZero (tail : ℕ → ℝ)
      (hbound : ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
        tail n ≤ 1 / ((n : ℝ) ^ α))
      (hnonneg : ∀ n, 0 ≤ tail n) : Tendsto tail atTop (𝓝 0) := by
    obtain ⟨α, hα, hbound⟩ := hbound
    let p : ℕ → ℝ := fun n => 1 / ((n : ℝ) ^ α)
    have hp : Tendsto p atTop (𝓝 0) := by
      have hpower : Tendsto (fun n : ℕ => (n : ℝ) ^ α) atTop atTop :=
        (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
      convert hpower.inv_tendsto_atTop using 1
      ext n
      simp [p, one_div]
    apply tendsto_order.mpr
    constructor
    · intro b hb
      filter_upwards [] with n
      exact lt_of_lt_of_le hb (hnonneg n)
    · intro ε hε
      filter_upwards [hbound, hp.eventually (Iio_mem_nhds hε)] with n h₁ h₂
      exact lt_of_le_of_lt h₁ h₂
  have htail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (μ n).real {ω | ε ≤ |X n ω - c|})
        atTop (𝓝 0) := by
    intro ε hε
    let left : ℕ → ℝ := fun n =>
      (μ n).real {ω | X n ω ≤ c - ε}
    let right : ℕ → ℝ := fun n =>
      (μ n).real {ω | c + ε ≤ X n ω}
    have hleftZero : Tendsto left atTop (𝓝 0) := by
      apply hpolyZero left ?_ (fun n => by dsimp [left]; exact measureReal_nonneg)
      obtain ⟨α, hα, hbound⟩ := hleft (c - ε) (by linarith)
      exact ⟨α, hα, hbound⟩
    have hrightZero : Tendsto right atTop (𝓝 0) := by
      apply hpolyZero right ?_ (fun n => by dsimp [right]; exact measureReal_nonneg)
      obtain ⟨α, hα, hbound⟩ := hright (c + ε) (by linarith)
      exact ⟨α, hα, hbound⟩
    have hsumZero : Tendsto (fun n => left n + right n) atTop (𝓝 0) := by
      simpa using hleftZero.add hrightZero
    let tail : ℕ → ℝ := fun n =>
      (μ n).real {ω | ε ≤ |X n ω - c|}
    have hbound : ∀ᶠ n : ℕ in atTop, tail n ≤ left n + right n := by
      filter_upwards [] with n
      letI : IsProbabilityMeasure (μ n) := hμ n
      have hsubset : {ω | ε ≤ |X n ω - c|} ⊆
          {ω | X n ω ≤ c - ε} ∪ {ω | c + ε ≤ X n ω} := by
        intro ω hω
        change ε ≤ |X n ω - c| at hω
        by_cases hx : 0 ≤ X n ω - c
        · right
          rw [abs_of_nonneg hx] at hω
          change c + ε ≤ X n ω
          linarith
        · left
          have hx' : X n ω - c ≤ 0 := le_of_not_ge hx
          rw [abs_of_nonpos hx'] at hω
          change X n ω ≤ c - ε
          linarith
      calc
        tail n ≤ (μ n).real
            ({ω | X n ω ≤ c - ε} ∪ {ω | c + ε ≤ X n ω}) :=
          measureReal_mono hsubset
        _ ≤ (μ n).real {ω | X n ω ≤ c - ε} +
            (μ n).real {ω | c + ε ≤ X n ω} := measureReal_union_le _ _
        _ = left n + right n := by rfl
    apply tendsto_order.mpr
    constructor
    · intro b hb
      filter_upwards [] with n
      exact lt_of_lt_of_le hb
        (measureReal_nonneg : 0 ≤ (μ n).real {ω | ε ≤ |X n ω - c|})
    · intro η hη
      filter_upwards [hbound, hsumZero.eventually (Iio_mem_nhds hη)]
        with n hn hs
      exact lt_of_le_of_lt hn hs
  exact tendsto_integral_abs_sq_of_tendsto_tail_and_fourth_moment
    μ hμ X c hX hfourth htail


end ProbabilityTheory

end
