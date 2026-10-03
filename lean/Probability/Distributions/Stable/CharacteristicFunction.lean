module

public import Probability.Distributions.Stable.Basic
public import Probability.Measure.CharacteristicFunction.Nondegenerate
public import Analysis.FunctionalEquation.ContinuousAdditivePositive
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Characteristic functions of stable laws

The modulus of the characteristic function is determined directly from the
weighted-sum definition of stability.  The argument does not choose a
Lévy–Khintchine representation or a phase parametrization.
-/

open MeasureTheory MeasureTheory.Measure
open Filter Topology
open scoped MeasureTheory NNReal

@[expose] public section

namespace ProbabilityTheory

/-- The characteristic-function modulus identity forced by the stability
relation, with the translation phase removed by taking norms. -/
theorem IsAlphaStable.norm_charFun_weightedSum
    {α : ℝ} {μ : Measure ℝ} (h : IsAlphaStable α μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    ‖charFun μ (a * t)‖ * ‖charFun μ (b * t)‖ =
      ‖charFun μ (alphaStableScale α a b * t)‖ := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  obtain ⟨shift, hstable⟩ := h.2.2.2.2 a b ha hb
  have hprod :
      (μ.map fun x => a * x) ∗ (μ.map fun x => b * x) =
        (μ.prod μ).map (weightedSum a b) := by
    rw [Measure.conv, Measure.map_prod_map μ μ (by fun_prop) (by fun_prop)]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hmapAffine :
      μ.map (affine (alphaStableScale α a b) shift) =
        (μ.map fun x => alphaStableScale α a b * x).map (fun x => x + shift) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hchar := congrArg (fun ν : Measure ℝ => charFun ν t) hstable
  rw [← hprod, charFun_conv, charFun_map_mul, charFun_map_mul,
    hmapAffine, charFun_map_add_const, charFun_map_mul] at hchar
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hchar
  simp only [norm_mul] at hnorm
  have hphase :
      ‖Complex.exp ((inner ℝ shift t) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hphase, mul_one] at hnorm
  exact hnorm

/-- Every nondegenerate alpha-stable law has a characteristic function whose
modulus is `exp (-c * |t|^α)` for a strictly positive constant `c`.  This
holds for the general affine stability definition, including `α = 1`. -/
theorem IsAlphaStable.exists_pos_norm_charFun_eq_exp
    {α : ℝ} {μ : Measure ℝ} (h : IsAlphaStable α μ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ t : ℝ, ‖charFun μ t‖ = Real.exp (-c * |t| ^ α) := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  let r : ℝ → ℝ := fun t => ‖charFun μ t‖
  have hrcont : Continuous r := MeasureTheory.continuous_charFun.norm
  have hr0 : r 0 = 1 := by simp [r]
  have hr_even (t : ℝ) : r (-t) = r t := by
    simp [r, charFun_neg]
  let F : ℝ≥0 → ℝ := fun s => r ((s : ℝ) ^ (1 / α))
  have hpowCont : Continuous (fun s : ℝ≥0 => (s : ℝ) ^ (1 / α)) := by
    exact (Real.continuous_rpow_const (one_div_nonneg.mpr h.alpha_pos.le)).comp
      NNReal.continuous_coe
  have hFcont : Continuous F := hrcont.comp hpowCont
  have hF0 : F 0 = 1 := by
    change r ((0 : ℝ) ^ (1 / α)) = 1
    rw [Real.zero_rpow (one_div_pos.mpr h.alpha_pos).ne', hr0]
  have hFadd (s u : ℝ≥0) : F (s + u) = F s * F u := by
    by_cases hs : s = 0
    · subst s
      simp [hF0]
    by_cases hu : u = 0
    · subst u
      simp [hF0]
    have hspos : 0 < (s : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hs)
    have hupos : 0 < (u : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hu)
    let a : ℝ := (s : ℝ) ^ (1 / α)
    let b : ℝ := (u : ℝ) ^ (1 / α)
    have ha : 0 < a := Real.rpow_pos_of_pos hspos _
    have hb : 0 < b := Real.rpow_pos_of_pos hupos _
    have haPow : a ^ α = (s : ℝ) := by
      dsimp [a]
      rw [← Real.rpow_mul hspos.le, one_div_mul_cancel h.alpha_pos.ne', Real.rpow_one]
    have hbPow : b ^ α = (u : ℝ) := by
      dsimp [b]
      rw [← Real.rpow_mul hupos.le, one_div_mul_cancel h.alpha_pos.ne', Real.rpow_one]
    have hscale : alphaStableScale α a b = ((s + u : ℝ≥0) : ℝ) ^ (1 / α) := by
      simp only [alphaStableScale, a, b, haPow, hbPow, NNReal.coe_add]
    have hrel : r (alphaStableScale α a b) = r a * r b := by
      simpa [r] using (h.norm_charFun_weightedSum ha hb 1).symm
    change r (((s + u : ℝ≥0) : ℝ) ^ (1 / α)) =
      r ((s : ℝ) ^ (1 / α)) * r ((u : ℝ) ^ (1 / α))
    rw [← hscale]
    simpa [a, b] using hrel
  have hFpositive : ∀ s : ℝ≥0, 0 < F s := by
    intro s
    have hnear : ∀ᶠ x : ℝ≥0 in 𝓝 0, 0 < F x := by
      exact (isOpen_Ioi.preimage hFcont).mem_nhds (by simp [hF0])
    have hseq : Tendsto (fun n : ℕ => s / ((n + 1 : ℕ) : ℝ≥0)) atTop (𝓝 0) := by
      exact (tendsto_const_div_atTop_nhds_zero_nat s).comp (tendsto_add_atTop_nat 1)
    obtain ⟨n, hn⟩ := (hseq.eventually hnear).exists
    let y : ℝ≥0 := s / ((n + 1 : ℕ) : ℝ≥0)
    have hy : 0 < F y := hn
    have hiter : ∀ k : ℕ, F ((k : ℝ≥0) * y) = F y ^ k := by
      intro k
      induction k with
      | zero => simp [hF0]
      | succ k ih =>
          simp only [Nat.cast_succ, add_mul, one_mul, hFadd, ih, pow_succ]
    have hmul : ((n + 1 : ℕ) : ℝ≥0) * y = s := by
      rw [mul_comm]
      dsimp [y]
      exact div_mul_cancel₀ s (by positivity : ((n + 1 : ℕ) : ℝ≥0) ≠ 0)
    rw [← hmul, hiter]
    exact pow_pos hy _
  let G : ℝ≥0 → ℝ := fun s => -Real.log (F s)
  have hGcont : Continuous G := by
    apply continuous_iff_continuousAt.mpr
    intro s
    change ContinuousAt (fun x => -Real.log (F x)) s
    exact (ContinuousAt.neg
      ((Real.continuousAt_log (ne_of_gt (hFpositive s))).comp hFcont.continuousAt))
  have hGadd (s u : ℝ≥0) : G (s + u) = G s + G u := by
    simp only [G, hFadd]
    rw [Real.log_mul (ne_of_gt (hFpositive s)) (ne_of_gt (hFpositive u))]
    ring
  have hFone : 0 < F 1 := hFpositive 1
  have hFone_le : F 1 ≤ 1 := by
    simpa [F, r] using norm_charFun_le_one (μ := μ) (1 : ℝ)
  let c : ℝ := -Real.log (F 1)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    have hlog : Real.log (F 1) ≤ 0 := by
      calc
        Real.log (F 1) ≤ Real.log 1 := Real.log_le_log hFone hFone_le
        _ = 0 := by simp
    linarith
  have hGformula (s : ℝ≥0) : G s = (s : ℝ) * c := by
    have h := continuous_additive_nnreal_eq_smul G hGcont hGadd s
    simpa [G, c, smul_eq_mul] using h
  have hFformula (s : ℝ≥0) : F s = Real.exp (-c * (s : ℝ)) := by
    have hlog : Real.log (F s) = -c * (s : ℝ) := by
      have := hGformula s
      dsimp [G] at this
      linarith
    rw [← Real.exp_log (hFpositive s), hlog]
  have hrformula_pos (t : ℝ) (ht : 0 < t) : r t = Real.exp (-c * t ^ α) := by
    let s : ℝ≥0 := ⟨t ^ α, Real.rpow_nonneg ht.le _⟩
    have hs : (s : ℝ) = t ^ α := rfl
    have hαinv : α * (1 / α) = 1 := by field_simp [h.alpha_pos.ne']
    have hroot : (s : ℝ) ^ (1 / α) = t := by
      rw [hs, ← Real.rpow_mul ht.le, hαinv, Real.rpow_one]
    have h := hFformula s
    change r ((s : ℝ) ^ (1 / α)) = Real.exp (-c * (s : ℝ)) at h
    rw [hroot, hs] at h
    simpa [r] using h
  have hrformula (t : ℝ) : r t = Real.exp (-c * |t| ^ α) := by
    by_cases ht : t < 0
    · have hpos : 0 < -t := by linarith
      have h := hrformula_pos (-t) hpos
      simpa [hr_even, abs_of_neg ht] using h
    · by_cases ht0 : t = 0
      · subst t
        simp [r, hr0, h.alpha_pos.ne']
      · have hpos : 0 < t := lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm ht0)
        simpa [abs_of_nonneg hpos.le] using hrformula_pos t hpos
  refine ⟨c, ?_, hrformula⟩
  by_contra hc
  have hc0 : c = 0 := le_antisymm (le_of_not_gt hc) hc_nonneg
  have hunit : ∀ t : ℝ, ‖charFun μ t‖ = 1 := by
    intro t
    change r t = 1
    rw [hrformula t, hc0]
    simp
  obtain ⟨x, hdirac⟩ := MeasureTheory.exists_dirac_of_norm_charFun_eq_one hunit
  exact h.nondegenerate ⟨x, hdirac⟩

end ProbabilityTheory

end
