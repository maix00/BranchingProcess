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

end TimeChange

end Skorokhod
