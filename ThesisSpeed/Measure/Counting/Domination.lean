import ThesisSpeed.Measure.Counting.FiniteOnFamily
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Almost-everywhere finiteness from a dominating functional

This is the abstract form of the computation that the paper uses to derive
"locally finite on the left". Nothing here mentions `ℝ`, an order, or the
exponential weight: if a random measure is dominated on every member of a
family by a constant times a random functional `W`, and `W` is integrable,
then the measure is a.e. finite on that family.

The paper's instance takes `𝒜` to be the left rays, `W` to be the total
exponential weight `∑ₓ e^{-λx}` and `C (Iic A) = e^{λA}`; the pointwise
inequality `N(A) ≤ e^{λA} W` is exactly the integrand estimate in
`contents/known-results/assumptions.tex`.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace ThesisSpeed

/-- If every member of a family is dominated by `C s * W`, and `W` is
integrable, then the measure is a.e. finite on the family. -/
theorem ae_finiteOnFamily_of_dominated
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω}
    {ν : Ω → Measure E} {𝒜 : Set (Set E)}
    {W : Ω → ℝ≥0∞} {C : Set E → ℝ≥0∞}
    (hWm : AEMeasurable W P)
    (hC : ∀ s ∈ 𝒜, C s ≠ ∞)
    (hdom : ∀ᵐ ω ∂P, ∀ s ∈ 𝒜, ν ω s ≤ C s * W ω)
    (hW : ∫⁻ ω, W ω ∂P < ∞) :
    ∀ s ∈ 𝒜, ∀ᵐ ω ∂P, ν ω s ≠ ∞ := by
  have hWtop : ∀ᵐ ω ∂P, W ω < ∞ := ae_lt_top' hWm hW.ne
  intro s hs
  filter_upwards [hdom, hWtop] with ω hd hlt
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (hC s hs) hlt.ne) (hd s hs)

/-- For a countable family the a.e. statements can be taken simultaneously.
This is the form needed to build one good event on which the whole comparison
holds. -/
theorem ae_all_finiteOnFamily_of_dominated
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω}
    {ν : Ω → Measure E} {𝒜 : Set (Set E)} (h𝒜 : 𝒜.Countable)
    {W : Ω → ℝ≥0∞} {C : Set E → ℝ≥0∞}
    (hWm : AEMeasurable W P)
    (hC : ∀ s ∈ 𝒜, C s ≠ ∞)
    (hdom : ∀ᵐ ω ∂P, ∀ s ∈ 𝒜, ν ω s ≤ C s * W ω)
    (hW : ∫⁻ ω, W ω ∂P < ∞) :
    ∀ᵐ ω ∂P, ∀ s ∈ 𝒜, ν ω s ≠ ∞ := by
  have h𝒜' := h𝒜.to_subtype
  have key : ∀ᵐ ω ∂P, ∀ s : {s : Set E // s ∈ 𝒜}, ν ω s.1 ≠ ∞ :=
    ae_all_iff.mpr fun s =>
      ae_finiteOnFamily_of_dominated hWm hC hdom hW s.1 s.2
  filter_upwards [key] with ω hω
  intro s hs
  exact hω ⟨s, hs⟩

end ThesisSpeed
