module

public import Probability.Process.Stable.SmallDeviation.Blocks.Lower.Global
import Mathlib.Order.CompleteLattice.Lemmas

/-!
# A concrete finite partition for returning corridor blocks

The two bins split the return core at zero. Unlike the abstract binning
theorem, endpoint coverage and all bin bounds are discharged here. A narrow
return core makes both translated block corridors contain the zero starting
point.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

private def returnBin (coreLower coreUpper : ℝ) : Bool → Set ℝ
  | false => Set.Ioo coreLower 0
  | true => Set.Ico 0 coreUpper

private def returnBinLower (coreLower : ℝ) : Bool → ℝ
  | false => coreLower
  | true => 0

private def returnBinUpper (coreUpper : ℝ) : Bool → ℝ
  | false => 0
  | true => coreUpper

private theorem returnBin_measurable (coreLower coreUpper : ℝ) (i : Bool) :
    MeasurableSet (returnBin coreLower coreUpper i) := by
  cases i <;> simp [returnBin, measurableSet_Ioo, measurableSet_Ico]

private theorem returnBin_disjoint (coreLower coreUpper : ℝ) :
    Pairwise (fun i k => Disjoint (returnBin coreLower coreUpper i)
      (returnBin coreLower coreUpper k)) := by
  intro i k hik
  cases i <;> cases k
  · exact (hik rfl).elim
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hy.1) hx.2
  · apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.1) hy.2
  · exact (hik rfl).elim

private theorem returnBin_bounds (coreLower coreUpper : ℝ) (i : Bool)
    (b : ℝ) (hb : b ∈ returnBin coreLower coreUpper i) :
    returnBinLower coreLower i ≤ b ∧ b ≤ returnBinUpper coreUpper i := by
  cases i with
  | false =>
      simp only [returnBin, Set.mem_Ioo, returnBinLower, returnBinUpper] at *
      exact ⟨le_of_lt hb.1, le_of_lt hb.2⟩
  | true =>
      simp only [returnBin, Set.mem_Ico, returnBinLower, returnBinUpper] at *
      exact ⟨hb.1, le_of_lt hb.2⟩

private theorem returnBin_cover (coreLower coreUpper : ℝ) :
    Set.Ioo coreLower coreUpper ⊆ ⋃ i : Bool, returnBin coreLower coreUpper i := by
  intro b hb
  by_cases h : b < 0
  · exact Set.mem_iUnion.mpr ⟨false, by simpa [returnBin] using And.intro hb.1 h⟩
  · exact Set.mem_iUnion.mpr ⟨true, by
      simpa [returnBin] using And.intro (le_of_not_gt h) hb.2⟩

/-- A concrete two-bin version of the stable block lower estimate. The two
block probabilities correspond to endpoints in the negative and nonnegative
halves of the return core. -/
theorem IsStableLevyProcess.min_two_blockProbabilities_pow_le_rationalHorizonTube
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P)
    (blocks : ℕ) (hblocks : 0 < blocks)
    (lower upper extra : ℝ) (hextra : 0 < extra)
    (coreLower coreUpper : ℝ) (hcore : coreLower < 0 ∧ 0 < coreUpper) :
    (P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
        ⟨0, hblocks⟩ q ω) ⁻¹'
        rationalCoordinateCorridorReturn
          (lower - coreLower) upper 0 coreUpper) ⊓
      P ((fun ω q => rationalUniformBlockProcessFromTime X hblocks
        ⟨0, hblocks⟩ q ω) ⁻¹'
        rationalCoordinateCorridorReturn
          lower (upper - coreUpper) coreLower 0)) ^ blocks ≤
      P (rationalHorizonTubeEvent X 1 (upper - lower + extra)) := by
  have hbound := h.iInf_blockProbability_pow_le_rationalHorizonTube_of_coreCover
    blocks hblocks lower upper extra hextra coreLower coreUpper hcore
    (returnBin coreLower coreUpper)
    (returnBinLower coreLower) (returnBinUpper coreUpper)
    (returnBin_measurable coreLower coreUpper)
    (returnBin_disjoint coreLower coreUpper)
    (returnBin_bounds coreLower coreUpper)
    (returnBin_cover coreLower coreUpper)
  simpa [iInf_bool_eq, inf_comm, returnBinLower, returnBinUpper] using hbound

end ProbabilityTheory
