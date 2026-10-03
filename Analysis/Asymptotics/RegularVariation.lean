module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Regular variation at infinity

This file provides the ratio-limit interface for regularly varying real
functions.  It is independent of probability and does not assume monotonicity.
The product and reciprocal rules give the scale algebra used in domain-of-
attraction arguments.  Potter bounds and asymptotic inverses are separate
results and are not inferred from these closure lemmas alone.
-/

open Filter

@[expose] public section

namespace Asymptotics

/-- `f` is regularly varying at infinity with index `ρ` if it is eventually
positive and `f (c * x) / f x → c ^ ρ` for every fixed positive multiplier
`c`. -/
def IsRegularlyVaryingAtTop (f : ℝ → ℝ) (ρ : ℝ) : Prop :=
  (∀ᶠ x : ℝ in atTop, 0 < f x) ∧
    ∀ c : ℝ, 0 < c →
      Tendsto (fun x : ℝ => f (c * x) / f x) atTop (nhds (c ^ ρ))

/-- Slow variation is regular variation with index zero. -/
abbrev IsSlowlyVaryingAtTop (f : ℝ → ℝ) : Prop :=
  IsRegularlyVaryingAtTop f 0

namespace IsRegularlyVaryingAtTop

theorem eventually_pos {f : ℝ → ℝ} {ρ : ℝ}
    (h : IsRegularlyVaryingAtTop f ρ) : ∀ᶠ x : ℝ in atTop, 0 < f x := h.1

theorem ratio_tendsto {f : ℝ → ℝ} {ρ c : ℝ}
    (h : IsRegularlyVaryingAtTop f ρ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => f (c * x) / f x) atTop (nhds (c ^ ρ)) := h.2 c hc

/-- Positive powers are regularly varying with their exponent as index. -/
theorem rpow (ρ : ℝ) : IsRegularlyVaryingAtTop (fun x : ℝ => x ^ ρ) ρ := by
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact Real.rpow_pos_of_pos hx ρ
  · intro c hc
    have heq : (fun x : ℝ => (c * x) ^ ρ / x ^ ρ) =ᶠ[atTop] fun _ => c ^ ρ := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have hmul := Real.mul_rpow (x := c) (y := x) (z := ρ) hc.le hx.le
      rw [hmul]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hx ρ)]
    exact tendsto_const_nhds.congr' heq.symm

/-- The product of regularly varying functions has the sum of their indices. -/
theorem mul {f g : ℝ → ℝ} {ρ σ : ℝ}
    (hf : IsRegularlyVaryingAtTop f ρ)
    (hg : IsRegularlyVaryingAtTop g σ) :
    IsRegularlyVaryingAtTop (fun x => f x * g x) (ρ + σ) := by
  refine ⟨hf.1.and hg.1 |>.mono (fun x hx => mul_pos hx.1 hx.2), ?_⟩
  intro c hc
  have hprod := (hf.ratio_tendsto hc).mul (hg.ratio_tendsto hc)
  have hlim : c ^ ρ * c ^ σ = c ^ (ρ + σ) := (Real.rpow_add hc ρ σ).symm
  rw [hlim] at hprod
  have heq : (fun x : ℝ => (f (c * x) * g (c * x)) / (f x * g x)) =ᶠ[atTop]
      fun x => (f (c * x) / f x) * (g (c * x) / g x) := by
    filter_upwards [hf.1, hg.1] with x hfx hgx
    field_simp [ne_of_gt hfx, ne_of_gt hgx]
  exact hprod.congr' heq.symm

/-- Taking reciprocals negates the regular-variation index. -/
theorem inv {f : ℝ → ℝ} {ρ : ℝ}
    (hf : IsRegularlyVaryingAtTop f ρ) :
    IsRegularlyVaryingAtTop (fun x => (f x)⁻¹) (-ρ) := by
  refine ⟨hf.1.mono (fun x hx => inv_pos.mpr hx), ?_⟩
  intro c hc
  have hcTop : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have hfc : ∀ᶠ x : ℝ in atTop, 0 < f (c * x) := hcTop.eventually hf.1
  have hratio := (hf.ratio_tendsto hc).inv₀
    (Real.rpow_pos_of_pos hc ρ).ne'
  have heq : (fun x : ℝ => (f (c * x))⁻¹ / (f x)⁻¹) =ᶠ[atTop]
      fun x => (f (c * x) / f x)⁻¹ := by
    filter_upwards [hf.1, hfc] with x hfx hfcx
    field_simp [ne_of_gt hfx, ne_of_gt hfcx]
  have hpow : (c ^ ρ)⁻¹ = c ^ (-ρ) := by
    rw [Real.rpow_neg hc.le]
  rw [hpow] at hratio
  exact hratio.congr' heq.symm

end IsRegularlyVaryingAtTop

namespace IsSlowlyVaryingAtTop

theorem mul {f g : ℝ → ℝ}
    (hf : IsSlowlyVaryingAtTop f) (hg : IsSlowlyVaryingAtTop g) :
    IsSlowlyVaryingAtTop (fun x => f x * g x) := by
  change IsRegularlyVaryingAtTop (fun x => f x * g x) 0
  simpa using IsRegularlyVaryingAtTop.mul hf hg

theorem inv {f : ℝ → ℝ} (hf : IsSlowlyVaryingAtTop f) :
    IsSlowlyVaryingAtTop (fun x => (f x)⁻¹) := by
  change IsRegularlyVaryingAtTop (fun x => (f x)⁻¹) 0
  simpa using IsRegularlyVaryingAtTop.inv hf

end IsSlowlyVaryingAtTop

/-- If `L` is slowly varying and eventually positive, `x^α / L(x)` is
regularly varying with index `α`. This is the generic scale-time fact used
for a truncated-moment norming; it does not assert that the norming is an
asymptotic inverse, or derive slow variation from domain-of-attraction
hypotheses. -/
theorem isRegularlyVaryingAtTop_rpow_div_of_slowlyVarying
    {L : ℝ → ℝ} {α : ℝ}
    (hL : IsSlowlyVaryingAtTop L) :
    IsRegularlyVaryingAtTop (fun x => x ^ α / L x) α := by
  simpa [IsSlowlyVaryingAtTop, div_eq_mul_inv] using
    (IsRegularlyVaryingAtTop.rpow α).mul
      (IsRegularlyVaryingAtTop.inv hL)

end Asymptotics
