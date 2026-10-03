module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Order.Filter.AtTopBot.Field

/-!
# Regular variation at infinity

This file provides the ratio-limit interface for regularly varying real
functions, together with product, reciprocal, and monotone Potter upper-bound
results.  It is independent of probability.  The Potter theorem states its
eventual monotonicity assumption explicitly; no asymptotic inverse theorem is
claimed here.
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

/-- A function is eventually nondecreasing on a terminal interval. -/
def IsEventuallyMonotoneAtTop (f : ℝ → ℝ) : Prop :=
  ∃ R : ℝ, ∀ ⦃x y : ℝ⦄, R ≤ x → x ≤ y → f x ≤ f y

namespace IsRegularlyVaryingAtTop

theorem eventually_pos {f : ℝ → ℝ} {ρ : ℝ}
    (h : IsRegularlyVaryingAtTop f ρ) : ∀ᶠ x : ℝ in atTop, 0 < f x := h.1

theorem ratio_tendsto {f : ℝ → ℝ} {ρ c : ℝ}
    (h : IsRegularlyVaryingAtTop f ρ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => f (c * x) / f x) atTop (nhds (c ^ ρ)) := h.2 c hc

/-- Regular variation is invariant under eventual equality. -/
theorem congr {f g : ℝ → ℝ} {ρ : ℝ}
    (hf : IsRegularlyVaryingAtTop f ρ) (hfg : f =ᶠ[atTop] g) :
    IsRegularlyVaryingAtTop g ρ := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.eventually_pos, hfg] with x hx heq
    rw [← heq]
    exact hx
  · intro c hc
    have hcTop : Tendsto (fun x : ℝ => c * x) atTop atTop :=
      tendsto_id.const_mul_atTop hc
    have hnum := hcTop.eventually hfg
    have heq : (fun x : ℝ => f (c * x) / f x) =ᶠ[atTop]
        fun x => g (c * x) / g x := by
      filter_upwards [hnum, hfg] with x hnum hden
      rw [hnum, hden]
    exact (hf.ratio_tendsto hc).congr' heq

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

/-- Composing a regularly varying function with a positive real power
multiplies its index by that power. -/
theorem comp_rpow {f : ℝ → ℝ} {ρ p : ℝ}
    (hf : IsRegularlyVaryingAtTop f ρ) (hp : 0 < p) :
    IsRegularlyVaryingAtTop (fun x : ℝ => f (x ^ p)) (p * ρ) := by
  refine ⟨?_, ?_⟩
  · have hpow := (tendsto_rpow_atTop hp).eventually hf.eventually_pos
    filter_upwards [hpow] with x hx
    exact hx
  · intro c hc
    have hcPow : 0 < c ^ p := Real.rpow_pos_of_pos hc p
    have hratio := (hf.ratio_tendsto hcPow).comp (tendsto_rpow_atTop hp)
    have heq : (fun x : ℝ => f (c ^ p * x ^ p) / f (x ^ p)) =ᶠ[atTop]
        fun x => f ((c * x) ^ p) / f (x ^ p) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [Real.mul_rpow hc.le hx.le]
    have hpow : (c ^ p) ^ ρ = c ^ (p * ρ) := by
      rw [← Real.rpow_mul hc.le]
    rw [hpow] at hratio
    exact hratio.congr' heq

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

/-- A function with a finite positive limit is slowly varying. -/
theorem of_tendsto_pos {f : ℝ → ℝ} {C : ℝ}
    (hC : 0 < C) (hlim : Tendsto f atTop (nhds C)) :
    IsSlowlyVaryingAtTop f := by
  refine ⟨hlim.eventually (Ioi_mem_nhds hC), ?_⟩
  intro c hc
  have hcTop : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have hnum : Tendsto (fun x : ℝ => f (c * x)) atTop (nhds C) := hlim.comp hcTop
  have hratio := hnum.div hlim hC.ne'
  have hratio' : Tendsto ((fun x : ℝ => f (c * x)) / f) atTop (nhds 1) := by
    simpa [hC.ne'] using hratio
  have heq : ((fun x : ℝ => f (c * x)) / f) =
      (fun x => f (c * x) / f x) := rfl
  rw [heq] at hratio'
  simpa [Real.rpow_zero] using hratio'

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

/-- Potter's upper bound for an eventually nondecreasing regularly varying
function of nonnegative index. For every positive `ε`, the function grows at
most like the power with index `ρ + ε`, uniformly for `R ≤ x ≤ y`. The
monotonicity hypothesis is explicit; this theorem does not claim that an
arbitrary regularly varying function is monotone. -/
theorem IsRegularlyVaryingAtTop.exists_potter_upper_bound
    {f : ℝ → ℝ} {ρ : ℝ}
    (hreg : IsRegularlyVaryingAtTop f ρ)
    (hmono : IsEventuallyMonotoneAtTop f)
    (hρ : 0 ≤ ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ ⦃x y : ℝ⦄, R ≤ x → x ≤ y →
      f y / f x ≤ 2 ^ (ρ + ε) * (y / x) ^ (ρ + ε) := by
  let p : ℝ := ρ + ε
  let q : ℝ := 2 ^ p
  have hp : 0 < p := add_pos_of_nonneg_of_pos hρ hε
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) p
  have hqgap : 2 ^ ρ < q := by
    dsimp [q, p]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by linarith)
  have hratio := hreg.ratio_tendsto (ρ := ρ) (c := 2) (by norm_num)
  have hevent : ∀ᶠ z : ℝ in atTop, f (2 * z) / f z < q :=
    hratio.eventually (Iio_mem_nhds hqgap)
  obtain ⟨Rratio, hRratio⟩ := eventually_atTop.1 hevent
  obtain ⟨Rpositive, hRpositive⟩ := eventually_atTop.1 hreg.eventually_pos
  obtain ⟨Rmonotone, hRmonotone⟩ := hmono
  let R : ℝ := max 1 (max Rratio (max Rpositive Rmonotone))
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRratioLe : Rratio ≤ R := by
    dsimp [R]
    exact le_max_of_le_right (le_max_left _ _)
  have hRpositiveLe : Rpositive ≤ R := by
    dsimp [R]
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hRmonotoneLe : Rmonotone ≤ R := by
    dsimp [R]
    exact le_max_of_le_right (le_max_of_le_right (le_max_right _ _))
  have hRratio : ∀ ⦃z : ℝ⦄, R ≤ z → f (2 * z) / f z < q := by
    intro z hz
    exact hRratio z (le_trans hRratioLe hz)
  have hRpositive : ∀ ⦃z : ℝ⦄, R ≤ z → 0 < f z := by
    intro z hz
    exact hRpositive z (le_trans hRpositiveLe hz)
  have hRmonotone' : ∀ ⦃x y : ℝ⦄, R ≤ x → x ≤ y → f x ≤ f y := by
    intro x y hx hxy
    exact hRmonotone (le_trans hRmonotoneLe hx) hxy
  have hstep : ∀ ⦃z : ℝ⦄, R ≤ z → f (2 * z) ≤ q * f z := by
    intro z hz
    have hzpos := hRpositive hz
    exact (div_lt_iff₀ hzpos).1 (hRratio hz) |>.le
  have hiterate : ∀ n : ℕ, ∀ ⦃x : ℝ⦄, R ≤ x →
      f ((2 : ℝ) ^ n * x) ≤ q ^ n * f x := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simp
    | succ n ih =>
        intro x hx
        have hpowLower : 1 ≤ (2 : ℝ) ^ n :=
          one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
        have hbase : R ≤ (2 : ℝ) ^ n * x := by
          calc
            R ≤ x := hx
            _ = 1 * x := by rw [one_mul]
            _ ≤ (2 : ℝ) ^ n * x :=
              mul_le_mul_of_nonneg_right hpowLower (le_of_lt (lt_of_lt_of_le hRpos hx))
        calc
          f ((2 : ℝ) ^ (n + 1) * x) = f (2 * ((2 : ℝ) ^ n * x)) := by
            congr 1
            rw [pow_succ]
            ring
          _ ≤ q * f ((2 : ℝ) ^ n * x) := hstep hbase
          _ ≤ q * (q ^ n * f x) := mul_le_mul_of_nonneg_left (ih hx) hq.le
          _ = q ^ (n + 1) * f x := by rw [pow_succ]; ring
  refine ⟨R, hRpos, ?_⟩
  intro x y hx hxy
  have hxpos : 0 < x := lt_of_lt_of_le hRpos hx
  have hr : 1 ≤ y / x := (one_le_div₀ hxpos).2 hxy
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near hr (by norm_num : (1 : ℝ) < 2)
  have hupper : y < (2 : ℝ) ^ (n + 1) * x := (div_lt_iff₀ hxpos).1 hnhi
  have hmonoUpper := hRmonotone' (le_trans hx hxy) hupper.le
  have hbound := hmonoUpper.trans (hiterate (n + 1) hx)
  have hratioBound : f y / f x ≤ q ^ (n + 1) := (div_le_iff₀ (hRpositive hx)).2 hbound
  have hpowEq : q ^ (n + 1) = ((2 : ℝ) ^ (n + 1 : ℕ)) ^ p := by
    dsimp [q]
    rw [← Real.rpow_natCast (2 ^ p) (n + 1)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) p ((n + 1 : ℕ) : ℝ)]
    rw [← Real.rpow_natCast (2 : ℝ) (n + 1)]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) ((n + 1 : ℕ) : ℝ) p]
    congr 1
    ring
  have hpowerBase : (2 : ℝ) ^ (n + 1) ≤ 2 * (y / x) := by
    calc
      (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := by rw [pow_succ]
      _ ≤ (y / x) * 2 := mul_le_mul_of_nonneg_right hnlo (by norm_num)
      _ = 2 * (y / x) := by ring
  have hpower := Real.rpow_le_rpow (by positivity) hpowerBase hp.le
  have hypos : 0 < y := lt_of_lt_of_le hxpos hxy
  have hmul : (2 * (y / x)) ^ p = 2 ^ p * (y / x) ^ p :=
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt (div_pos hypos hxpos))
  calc
    f y / f x ≤ q ^ (n + 1) := hratioBound
    _ = ((2 : ℝ) ^ (n + 1 : ℕ)) ^ p := hpowEq
    _ ≤ (2 * (y / x)) ^ p := hpower
    _ = 2 ^ (ρ + ε) * (y / x) ^ (ρ + ε) := by simpa [q, p] using hmul

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
