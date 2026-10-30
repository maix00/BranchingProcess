/-
Copyright (c) 2026 Marcel Morgenstern. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcel Morgenstern
-/

module

public import Probability.Ergodic.Kingman.Basic
public import Mathlib.Analysis.Subadditive
import MeasureTheory.Integral.MeasurePreserving

/-!
# Fekete's lemma for integrals of subadditive cocycles

## Public declarations

* `ProbabilityTheory.Kingman.integral_subadditive`: if `T` preserves `μ` and every `g n` is
  integrable, then the sequence `n ↦ ∫ x, g n x ∂μ` is subadditive.
* `ProbabilityTheory.Kingman.exists_fekete`: under the same assumptions and a lower bound on
  `n ↦ (∫ g (n+1) dμ)/(n+1)`, that normalized integral sequence converges to a real limit.

These statements use Mathlib's `Subadditive.lim` for the Fekete limit.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace ProbabilityTheory.Kingman

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {T : X → X}

/-- **Integral subadditivity.** The integral sequence `aₙ = ∫ gₙ` is subadditive
in Mathlib's sense (`a (m+n) ≤ a m + a n`), the Fekete input. -/
theorem integral_subadditive (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ) :
    Subadditive (fun n => ∫ x, g n x ∂μ) := by
  intro m n
  simp only
  have hcomp : Integrable (fun x => g n (T^[m] x)) μ :=
    (hT.iterate m).integrable_comp_of_integrable (hint n)
  calc ∫ x, g (m + n) x ∂μ
      ≤ ∫ x, (g m x + g n (T^[m] x)) ∂μ :=
        integral_mono (hint _) ((hint m).add hcomp) (fun x => hsub.apply_add_le m n x)
    _ = (∫ x, g m x ∂μ) + ∫ x, g n (T^[m] x) ∂μ := integral_add (hint m) hcomp
    _ = (∫ x, g m x ∂μ) + ∫ x, g n x ∂μ := by rw [← (hT.iterate m).integral_comp_of_integrable (hint n)]

/-! ### Fekete: the limit `γ` of the normalized integrals -/

/-- **Fekete.** The normalized integral sequence `(∫ g (n+1)) / (n+1)` converges to
the Fekete constant `γ := (integral_subadditive …).lim`. The `n+1`-indexed bounded-below
hypothesis is bridged to the `n`-indexed Fekete input by hand (the `n = 0` term is
`(∫ g 0)/0 = 0`). -/
theorem exists_fekete (hT : MeasurePreserving T μ μ) {g : ℕ → X → ℝ}
    (hsub : IsSubadditiveCocycle T g) (hint : ∀ n, Integrable (g n) μ)
    (hbdd : BddBelow (Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1))) :
    ∃ γ : ℝ, Tendsto (fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1)) atTop (𝓝 γ) := by
  set a : ℕ → ℝ := fun n => ∫ x, g n x ∂μ with hadef
  have hsa : Subadditive a := integral_subadditive hT hsub hint
  -- Bridge the `n+1`-indexed bound to a bound on `{a n / n}` over all `n`.
  have hbdd' : BddBelow (Set.range fun n : ℕ => a n / n) := by
    obtain ⟨lb, hlb⟩ := hbdd
    refine ⟨min lb 0, ?_⟩
    rintro y ⟨n, rfl⟩
    rcases n with _ | m
    · -- `n = 0`: `a 0 / 0 = 0 ≥ min lb 0`.
      simp only [Nat.cast_zero, div_zero]
      exact min_le_right lb 0
    · -- `n = m + 1`: bounded by `lb` from `hbdd`.
      have hmem : a (m + 1) / ((m : ℝ) + 1)
          ∈ Set.range fun n : ℕ => (∫ x, g (n + 1) x ∂μ) / (n + 1) :=
        ⟨m, by simp only [hadef]⟩
      have : (fun n : ℕ => a n / n) (m + 1) = a (m + 1) / ((m : ℝ) + 1) := by push_cast; ring
      rw [this]
      exact le_trans (min_le_left lb 0) (hlb hmem)
  -- Fekete: `a n / n → γ`, and the shifted sequence shares the limit.
  refine ⟨hsa.lim, ?_⟩
  have hlim := hsa.tendsto_lim hbdd'
  rw [← tendsto_add_atTop_iff_nat (f := fun n : ℕ => a n / n) 1] at hlim
  refine hlim.congr (fun n => ?_)
  show a (n + 1) / ((n + 1 : ℕ) : ℝ) = (∫ x, g (n + 1) x ∂μ) / ((n : ℝ) + 1)
  simp only [hadef, Nat.cast_add, Nat.cast_one]

end ProbabilityTheory.Kingman
