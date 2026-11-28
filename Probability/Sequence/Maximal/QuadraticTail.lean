/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.Tails.Quadratic
public import Mathlib.Probability.HasLaw

/-!
# Vanishing exceptional marks on a diffusive horizon

## Public declarations

In `ProbabilityTheory`:

* `measureReal_exists_lt_le_of_hasLaw` gives
  `P(∃ j < m, c < Bⱼ) ≤ m ν((c,∞))` for observations with common law `ν`.
* `tendsto_measureReal_exists_lt_of_vanishingQuadraticTail` proves
  `P(∃ j < mₙ, α Lₙ < Bⱼ) → 0` if `Lₙ → ∞`, `mₙ ≤ C Lₙ²`
  eventually, `α > 0` and `x² ν((x,∞)) → 0`.
* `eventually_measureReal_inter_marks_ge` gives, uniformly over all events
  `A` with `P(A) ≥ p > 0`, the bound
  `P(A ∩ {Bⱼ ≤ α Lₙ, j < mₙ}) ≥ p/2` eventually.

The observations need not be independent, and `A` can depend on every mark.
This is the zero-tail-constant block step of B. Mallein, *Necessary and
sufficient conditions for the convergence of the consistent maximal displacement
of the branching random walk*, Theorem 2.3 and proof of Lemma 2.4,
arXiv:1510.00602v2. Only the union bound and the vanishing quadratic tail are
used. It applies to a diffusion block of length `O(L²)`; it does not replace
the concatenation argument on a full horizon of order `L³`.
-/

@[expose] public section
namespace ProbabilityTheory
open MeasureTheory Filter
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℕ → Ω → ℝ} {ν : Measure ℝ}

theorem measureReal_exists_lt_le_of_hasLaw (hB : ∀ j, HasLaw (B j) ν P)
    (m : ℕ) (c : ℝ) :
    P.real {ω | ∃ j < m, c < B j ω} ≤ (m : ℝ) * ν.real (Set.Ioi c) := by
  have heq : {ω | ∃ j < m, c < B j ω} =
      ⋃ j ∈ Finset.range m, {ω | c < B j ω} := by
    ext ω
    simp
  rw [heq]
  refine (measureReal_biUnion_finset_le _ _).trans_eq ?_
  simp_rw [(hB _).measureReal_eq (measurableSet_Ioi : MeasurableSet {x : ℝ | c < x})]
  simp [Set.Ioi]

theorem tendsto_measureReal_exists_lt_of_vanishingQuadraticTail
    (hB : ∀ j, HasLaw (B j) ν P) (htail : HasVanishingQuadraticTail ν id)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {length : ℕ → ℕ} {C α : ℝ} (hα : 0 < α)
    (hlength : ∀ᶠ n in atTop, (length n : ℝ) ≤ C * scale n ^ 2) :
    Tendsto (fun n => P.real {ω | ∃ j < length n, α * scale n < B j ω})
      atTop (𝓝 0) := by
  have ht := ((htail.scale_threshold hα).comp hscale).const_mul C
  simp only [mul_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => measureReal_nonneg) _ ht
  filter_upwards [hlength] with n hn
  exact (measureReal_exists_lt_le_of_hasLaw hB _ _).trans
    (by simpa only [Function.comp_def, id_eq, mul_assoc, Set.Ioi] using
      mul_le_mul_of_nonneg_right hn (show 0 ≤ ν.real (Set.Ioi (α * scale n)) from
        measureReal_nonneg))

variable [IsFiniteMeasure P]

/-- A positive unmarked block probability survives the mark restriction,
uniformly over the event, including events correlated with the marks. -/
theorem eventually_measureReal_inter_marks_ge
    (hB : ∀ j, HasLaw (B j) ν P) (htail : HasVanishingQuadraticTail ν id)
    {scale : ℕ → ℝ} (hscale : Tendsto scale atTop atTop)
    {length : ℕ → ℕ} {C α p : ℝ} (hα : 0 < α) (hp : 0 < p)
    (hlength : ∀ᶠ n in atTop, (length n : ℝ) ≤ C * scale n ^ 2) :
    ∀ᶠ n in atTop, ∀ A : Set Ω, p ≤ P.real A →
      p / 2 ≤ P.real (A ∩ {ω | ∀ j < length n, B j ω ≤ α * scale n}) := by
  have ht := tendsto_measureReal_exists_lt_of_vanishingQuadraticTail hB htail
    hscale hα hlength
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < p / 2))] with n hn
  intro A hA
  have hcover : A ⊆
      (A ∩ {ω | ∀ j < length n, B j ω ≤ α * scale n}) ∪
        {ω | ∃ j < length n, α * scale n < B j ω} := by
    intro ω hω
    by_cases h : ∀ j < length n, B j ω ≤ α * scale n
    · exact Or.inl ⟨hω, h⟩
    · right
      simpa only [Set.mem_ofPred_eq, not_forall, exists_prop, not_le] using h
  have h := (measureReal_mono (μ := P) hcover).trans (measureReal_union_le _ _)
  linarith

end ProbabilityTheory
