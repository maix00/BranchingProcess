/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Topology.Cadlag.Skorokhod.TimeChange

/-!
# Logarithmic distortion of Skorokhod time changes

The logarithmic distortion measures the largest multiplicative change in a
secant slope. It is the time-change penalty used by the complete metric
equivalent to the usual Skorokhod `J₁` metric.
-/

@[expose] public section

open scoped ENNReal

namespace Skorokhod

namespace TimeChange

/-- The slope of a time change across a strictly ordered pair of times. -/
noncomputable def secantSlope (τ : TimeChange) (s t : unitInterval) : ℝ :=
  ((τ t : ℝ) - (τ s : ℝ)) / ((t : ℝ) - (s : ℝ))

/-- A pair of strictly ordered times. -/
abbrev SecantPair := {p : unitInterval × unitInterval // p.1 < p.2}

/-- The absolute logarithmic distortion of a secant slope. -/
noncomputable def logSecantDistortion (τ : TimeChange) (s t : unitInterval) : ℝ :=
  |Real.log (τ.secantSlope s t)|

/-- The possibly infinite supremum of the absolute logarithmic secant-slope
distortion of a time change. -/
noncomputable def logDistortion (τ : TimeChange) : ℝ≥0∞ :=
  ⨆ p : SecantPair, ENNReal.ofReal (τ.logSecantDistortion p.1.1 p.1.2)

theorem secantSlope_pos (τ : TimeChange) {s t : unitInterval} (hst : s < t) :
    0 < τ.secantSlope s t := by
  apply div_pos
  · have hτ : τ s < τ t := τ.strictMono_toHomeomorph hst
    exact sub_pos.mpr hτ
  · exact sub_pos.mpr hst

theorem secantSlope_trans_eq (τ σ : TimeChange) {s t : unitInterval}
    (hst : s < t) :
    (τ.trans σ).secantSlope s t =
      σ.secantSlope (τ s) (τ t) * τ.secantSlope s t := by
  have hstR : (s : ℝ) < (t : ℝ) := hst
  have hτst : τ s < τ t := τ.strictMono_toHomeomorph hst
  have hτstR : (τ s : ℝ) < (τ t : ℝ) := hτst
  have hst_ne : (t : ℝ) - (s : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hstR)
  have hτst_ne : (τ t : ℝ) - (τ s : ℝ) ≠ 0 :=
    ne_of_gt (sub_pos.mpr hτstR)
  simp only [secantSlope, TimeChange.trans_apply]
  field_simp [hst_ne, hτst_ne]

theorem logSecantDistortion_trans_le (τ σ : TimeChange) {s t : unitInterval}
    (hst : s < t) :
    (τ.trans σ).logSecantDistortion s t ≤
      τ.logSecantDistortion s t + σ.logSecantDistortion (τ s) (τ t) := by
  have hτ : 0 < τ.secantSlope s t := secantSlope_pos τ hst
  have hστ : 0 < σ.secantSlope (τ s) (τ t) :=
    secantSlope_pos σ (τ.strictMono_toHomeomorph hst)
  rw [logSecantDistortion, secantSlope_trans_eq τ σ hst]
  rw [Real.log_mul (ne_of_gt hστ) (ne_of_gt hτ)]
  calc
    |Real.log (σ.secantSlope (τ s) (τ t)) + Real.log (τ.secantSlope s t)| ≤
        |Real.log (σ.secantSlope (τ s) (τ t))| +
          |Real.log (τ.secantSlope s t)| := abs_add_le _ _
    _ = τ.logSecantDistortion s t +
        σ.logSecantDistortion (τ s) (τ t) := by
          unfold logSecantDistortion
          exact add_comm _ _

theorem logSecantDistortion_nonneg (τ : TimeChange) (s t : unitInterval) :
    0 ≤ τ.logSecantDistortion s t := abs_nonneg _

@[simp]
theorem logSecantDistortion_refl (s t : unitInterval) :
    refl.logSecantDistortion s t = 0 := by
  simp [logSecantDistortion, secantSlope, refl]

@[simp]
theorem logDistortion_refl : refl.logDistortion = 0 := by
  simp [logDistortion, logSecantDistortion_refl]

theorem logDistortion_le_iff (τ : TimeChange) {r : ℝ≥0∞} :
    τ.logDistortion ≤ r ↔ ∀ p : SecantPair,
      ENNReal.ofReal (τ.logSecantDistortion p.1.1 p.1.2) ≤ r :=
  iSup_le_iff

/-- Uniform two-sided control of secant slopes yields a bound on the
logarithmic distortion. -/
theorem logDistortion_le_of_secantSlope_mem_Icc
    (τ : TimeChange) {q : ℝ} (hq_lt : q < 1)
    (hsecant : ∀ p : SecantPair,
      1 - q ≤ τ.secantSlope p.1.1 p.1.2 ∧
        τ.secantSlope p.1.1 p.1.2 ≤ 1 + q) :
    τ.logDistortion ≤ ENNReal.ofReal
      (max (Real.log (1 + q)) (-Real.log (1 - q))) := by
  unfold logDistortion
  refine iSup_le fun p ↦ ?_
  have hslope : 0 < τ.secantSlope p.1.1 p.1.2 :=
    TimeChange.secantSlope_pos τ p.2
  have hlow : 0 < 1 - q := by linarith
  have hloglow : Real.log (1 - q) ≤
      Real.log (τ.secantSlope p.1.1 p.1.2) :=
    Real.log_le_log hlow (hsecant p).1
  have hloghigh : Real.log (τ.secantSlope p.1.1 p.1.2) ≤ Real.log (1 + q) :=
    Real.log_le_log hslope (hsecant p).2
  have hlogabs : |Real.log (τ.secantSlope p.1.1 p.1.2)| ≤
      max (Real.log (1 + q)) (-Real.log (1 - q)) := by
    rw [abs_le]
    constructor
    · have hmax : -Real.log (1 - q) ≤
          max (Real.log (1 + q)) (-Real.log (1 - q)) := le_max_right _ _
      linarith
    · exact hloghigh.trans (le_max_left _ _)
  exact ENNReal.ofReal_le_ofReal hlogabs

theorem logSecantDistortion_symm_pair (τ : TimeChange) (s t : unitInterval)
    (hst : s < t) :
    τ.symm.logSecantDistortion (τ s) (τ t) = τ.logSecantDistortion s t := by
  have hτ : 0 < τ.secantSlope s t := secantSlope_pos τ hst
  have hrecip : τ.symm.secantSlope (τ s) (τ t) = (τ.secantSlope s t)⁻¹ := by
    simp only [secantSlope, TimeChange.symm_apply_apply]
    simp [div_eq_mul_inv, mul_comm]
  change |Real.log (τ.symm.secantSlope (τ s) (τ t))| =
    |Real.log (τ.secantSlope s t)|
  rw [hrecip, Real.log_inv]
  simp

private def mapSecantPair (τ : TimeChange) : SecantPair ≃ SecantPair where
  toFun p := ⟨(τ p.1.1, τ p.1.2), τ.strictMono_toHomeomorph p.2⟩
  invFun p := ⟨(τ.symm p.1.1, τ.symm p.1.2),
    τ.symm.strictMono_toHomeomorph p.2⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv p := by
    apply Subtype.ext
    simp

@[simp]
theorem logDistortion_symm (τ : TimeChange) :
    τ.symm.logDistortion = τ.logDistortion := by
  simp only [logDistortion]
  calc
    (⨆ p : SecantPair,
        ENNReal.ofReal (τ.symm.logSecantDistortion p.1.1 p.1.2)) =
      ⨆ p : SecantPair, ENNReal.ofReal
        (τ.symm.logSecantDistortion ((mapSecantPair τ p).1.1)
          ((mapSecantPair τ p).1.2)) := by
            symm
            exact (mapSecantPair τ).iSup_comp
              (g := fun p : SecantPair => ENNReal.ofReal
                (τ.symm.logSecantDistortion p.1.1 p.1.2))
    _ = ⨆ p : SecantPair,
        ENNReal.ofReal (τ.logSecantDistortion p.1.1 p.1.2) := by
          apply iSup_congr
          intro p
          exact congrArg ENNReal.ofReal <|
            logSecantDistortion_symm_pair τ p.1.1 p.1.2 p.2

theorem logDistortion_trans_le (τ σ : TimeChange) :
    (τ.trans σ).logDistortion ≤ τ.logDistortion + σ.logDistortion := by
  refine iSup_le fun p : SecantPair => ?_
  have hpoint := logSecantDistortion_trans_le τ σ p.2
  have hfirst : ENNReal.ofReal (τ.logSecantDistortion p.1.1 p.1.2) ≤
      τ.logDistortion := le_iSup (fun q : SecantPair => ENNReal.ofReal
        (τ.logSecantDistortion q.1.1 q.1.2)) p
  have hsecond : ENNReal.ofReal
      (σ.logSecantDistortion (τ p.1.1) (τ p.1.2)) ≤ σ.logDistortion := by
    exact le_iSup (fun q : SecantPair => ENNReal.ofReal
      (σ.logSecantDistortion q.1.1 q.1.2))
        ⟨(τ p.1.1, τ p.1.2), τ.strictMono_toHomeomorph p.2⟩
  calc
    ENNReal.ofReal ((τ.trans σ).logSecantDistortion p.1.1 p.1.2) ≤
        ENNReal.ofReal (τ.logSecantDistortion p.1.1 p.1.2 +
          σ.logSecantDistortion (τ p.1.1) (τ p.1.2)) :=
      ENNReal.ofReal_le_ofReal hpoint
    _ = ENNReal.ofReal (τ.logSecantDistortion p.1.1 p.1.2) +
        ENNReal.ofReal (σ.logSecantDistortion (τ p.1.1) (τ p.1.2)) := by
      change ENNReal.ofReal
          (|Real.log (τ.secantSlope p.1.1 p.1.2)| +
            |Real.log (σ.secantSlope (τ p.1.1) (τ p.1.2))|) = _
      exact ENNReal.ofReal_add
        (abs_nonneg (Real.log (τ.secantSlope p.1.1 p.1.2)))
        (abs_nonneg (Real.log (σ.secantSlope (τ p.1.1) (τ p.1.2))))
    _ ≤ τ.logDistortion + σ.logDistortion := add_le_add hfirst hsecond

/-- A uniform bound on the logarithmic secant distortion controls the usual
uniform displacement of a time change. The symmetric exponential bound is
chosen so that it tends to zero with the logarithmic bound. -/
theorem distortion_le_exp_sub_exp_neg_of_logDistortion_le (τ : TimeChange)
    {bound : ℝ} (hbound : 0 ≤ bound)
    (hlog : τ.logDistortion ≤ ENNReal.ofReal bound) :
    τ.distortion ≤ Real.exp bound - Real.exp (-bound) := by
  rw [distortion, ContinuousMap.dist_le_iff_of_nonempty]
  intro t
  change dist (τ t) t ≤ Real.exp bound - Real.exp (-bound)
  have hexp_one : 1 ≤ Real.exp bound := by
    calc
      1 = Real.exp 0 := by simp
      _ ≤ Real.exp bound := Real.exp_le_exp.mpr hbound
  have hexp_neg_one : Real.exp (-bound) ≤ 1 := by
    calc
      Real.exp (-bound) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := by simp
  have hspan_nonneg : 0 ≤ Real.exp bound - Real.exp (-bound) := by linarith
  by_cases ht : t = ⊥
  · subst t
    simpa [TimeChange.apply_bot] using hspan_nonneg
  · have htpos : ⊥ < t := bot_lt_iff_ne_bot.mpr ht
    have htR : 0 < (t : ℝ) := htpos
    have htle : (t : ℝ) ≤ 1 := unitInterval.le_one t
    let p : SecantPair := ⟨(⊥, t), htpos⟩
    have hp_le : ENNReal.ofReal (τ.logSecantDistortion ⊥ t) ≤
        ENNReal.ofReal bound := by
      exact (le_iSup (fun q : SecantPair => ENNReal.ofReal
        (τ.logSecantDistortion q.1.1 q.1.2)) p).trans hlog
    have hlog_real : τ.logSecantDistortion ⊥ t ≤ bound :=
      (ENNReal.ofReal_le_ofReal_iff hbound).mp hp_le
    have hslope : τ.secantSlope ⊥ t = (τ t : ℝ) / (t : ℝ) := by
      simp [secantSlope]
    have hslope_pos : 0 < τ.secantSlope ⊥ t := secantSlope_pos τ htpos
    have habs := abs_le.mp hlog_real
    have hslope_upper : τ.secantSlope ⊥ t ≤ Real.exp bound :=
      (Real.log_le_iff_le_exp hslope_pos).mp habs.2
    have hslope_lower : Real.exp (-bound) ≤ τ.secantSlope ⊥ t := by
      have hExp := Real.exp_le_exp.mpr habs.1
      simpa only [Real.exp_log hslope_pos] using hExp
    have hvalue : (τ t : ℝ) = τ.secantSlope ⊥ t * (t : ℝ) := by
      rw [hslope]
      field_simp
    have hvalue_upper : (τ t : ℝ) ≤ Real.exp bound * (t : ℝ) := by
      calc
        (τ t : ℝ) = τ.secantSlope ⊥ t * (t : ℝ) := hvalue
        _ ≤ Real.exp bound * (t : ℝ) :=
          mul_le_mul_of_nonneg_right hslope_upper htR.le
    have hvalue_lower : Real.exp (-bound) * (t : ℝ) ≤ (τ t : ℝ) := by
      calc
        Real.exp (-bound) * (t : ℝ) ≤ τ.secantSlope ⊥ t * (t : ℝ) :=
          mul_le_mul_of_nonneg_right hslope_lower htR.le
        _ = (τ t : ℝ) := hvalue.symm
    have hupper_factor_nonneg : 0 ≤ Real.exp bound - 1 := by linarith
    have hlower_factor_nonneg : 0 ≤ 1 - Real.exp (-bound) := by linarith
    have hupper : (τ t : ℝ) - t ≤ Real.exp bound - 1 := by
      calc
        (τ t : ℝ) - t ≤ Real.exp bound * t - t := sub_le_sub_right hvalue_upper _
        _ = t * (Real.exp bound - 1) := by ring
        _ ≤ 1 * (Real.exp bound - 1) :=
          mul_le_mul_of_nonneg_right htle hupper_factor_nonneg
        _ = Real.exp bound - 1 := one_mul _
    have hlower : (t : ℝ) - τ t ≤ 1 - Real.exp (-bound) := by
      calc
        (t : ℝ) - τ t ≤ t - Real.exp (-bound) * t :=
          sub_le_sub_left hvalue_lower _
        _ = t * (1 - Real.exp (-bound)) := by ring
        _ ≤ 1 * (1 - Real.exp (-bound)) :=
          mul_le_mul_of_nonneg_right htle hlower_factor_nonneg
        _ = 1 - Real.exp (-bound) := one_mul _
    have hdist_le : |(τ t : ℝ) - t| ≤ Real.exp bound - Real.exp (-bound) := by
      rw [abs_le]
      constructor <;> linarith
    simpa only [Subtype.dist_eq, Real.dist_eq] using hdist_le

end TimeChange

end Skorokhod
