/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.Subadditive
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Expected limits of subadditive arrays

## Public declarations

- `ProbabilityTheory.Subadditive.tendsto_expectedNormalized_of_subadditiveArray`:
  if every \(X_{m,n}\) is integrable, the expected increments are stationary,
  \(X_{0,m+n}\le X_{0,m}+X_{m,m+n}\) almost everywhere, and the normalized
  expectations have a linear lower bound, then
  \(\mathbb E[X_{0,n}]/n\to c\) for some \(c\in\mathbb R\).

The proof applies Mathlib's Fekete lemma to the sequence of expectations. The
result requires mean-stationarity of increments; it does not assume a
measure-preserving shift or claim almost-sure convergence of the random array.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.Subadditive

/-- The expected first-row values of an integrable mean-stationary subadditive
array have a normalized limit, by Fekete's lemma. Subadditivity is only
required almost everywhere; `hstationaryMean` identifies expected block
increments with the corresponding first-row expectation. -/
theorem tendsto_expectedNormalized_of_subadditiveArray
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : ℕ → ℕ → Ω → ℝ)
    (hInt : ∀ m n, Integrable (X m n) μ)
    (hzero : (∫ ω, X 0 0 ω ∂μ) = 0)
    (hstationaryMean : ∀ m n,
      (∫ ω, X m (m + n) ω ∂μ) = ∫ ω, X 0 n ω ∂μ)
    (hsubadditive : ∀ m n,
      X 0 (m + n) ≤ᵐ[μ] fun ω => X 0 m ω + X m (m + n) ω)
    (lowerMeanRate : ℝ)
    (hlower : ∀ n : ℕ, lowerMeanRate * (n : ℝ) ≤ ∫ ω, X 0 n ω ∂μ) :
    ∃ c : ℝ, Tendsto
      (fun n : ℕ => (∫ ω, X 0 n ω ∂μ) / (n : ℝ)) atTop (𝓝 c) := by
  let u : ℕ → ℝ := fun n => ∫ ω, X 0 n ω ∂μ
  have hu : Subadditive u := by
    intro m n
    change (∫ ω, X 0 (m + n) ω ∂μ) ≤
      (∫ ω, X 0 m ω ∂μ) + (∫ ω, X 0 n ω ∂μ)
    calc
      (∫ ω, X 0 (m + n) ω ∂μ) ≤
          ∫ ω, X 0 m ω + X m (m + n) ω ∂μ :=
        integral_mono_ae (hInt 0 (m + n)) ((hInt 0 m).add (hInt m (m + n)))
          (hsubadditive m n)
      _ = (∫ ω, X 0 m ω ∂μ) + (∫ ω, X m (m + n) ω ∂μ) :=
        integral_add (hInt 0 m) (hInt m (m + n))
      _ = (∫ ω, X 0 m ω ∂μ) + (∫ ω, X 0 n ω ∂μ) := by
        rw [hstationaryMean m n]
  have hbdd : BddBelow (Set.range fun n : ℕ => u n / (n : ℝ)) := by
    refine ⟨min lowerMeanRate 0, ?_⟩
    rintro x ⟨n, rfl⟩
    by_cases hn : n = 0
    · subst n
      simp [u, hzero]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hratio : lowerMeanRate ≤ u n / (n : ℝ) := by
        change lowerMeanRate ≤ (∫ ω, X 0 n ω ∂μ) / (n : ℝ)
        exact (le_div_iff₀ hnpos).2 (by simpa using hlower n)
      exact (min_le_left _ _).trans hratio
  refine ⟨hu.lim, ?_⟩
  simpa [u] using hu.tendsto_lim hbdd

end ProbabilityTheory.Subadditive
