module

public import Probability.Distributions.Stable.Basic
public import Mathlib.Probability.CDF

/-!
# Signs in a stable law

The original small-deviation hypothesis is stated using the cumulative
distribution function at zero. Strict stability alone makes this condition
imply positive mass on each open half-line; no atomlessness hypothesis is
needed.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- The original condition `0 < F(0) < 1` gives positive mass to both
signs. If the negative half-line had zero mass, the atom at zero would have
mass `θ ∈ (0,1)`; strict stability and nonnegativity force `θ = θ²`. -/
theorem IsStrictlyAlphaStable.twoSidedMass_of_cdfAtZero
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    0 < μ (Set.Iio 0) ∧ 0 < μ (Set.Ioi 0) := by
  letI : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hIic : μ (Set.Iic 0) = ENNReal.ofReal (cdf μ 0) :=
    (ofReal_cdf μ 0).symm
  have hθpos : 0 < μ (Set.Iic 0) := by
    rw [hIic]
    exact ENNReal.ofReal_pos.mpr hcdf.1
  have hθlt : μ (Set.Iic 0) < 1 := by
    rw [hIic]
    exact ENNReal.ofReal_lt_one.mpr hcdf.2
  have hpos : 0 < μ (Set.Ioi 0) := by
    rw [← Set.compl_Iic, measure_compl measurableSet_Iic (by finiteness)]
    simpa only [measure_univ] using (tsub_pos_iff_lt.mpr hθlt)
  refine ⟨?_, hpos⟩
  by_contra hneg
  have hneg0 : μ (Set.Iio 0) = 0 := nonpos_iff_eq_zero.mp (le_of_not_gt hneg)
  have hnonneg : μ (Set.Ici 0) = 1 := by
    rw [← Set.compl_Iio, measure_compl measurableSet_Iio (by finiteness), hneg0]
    simp
  let ν := μ.prod μ
  have hnonnegProd : ν (Set.Ici 0 ×ˢ Set.Ici 0) = 1 := by
    change (μ.prod μ) (Set.Ici 0 ×ˢ Set.Ici 0) = 1
    rw [Measure.prod_prod, hnonneg]
    simp
  have haeNonneg : ∀ᵐ p : ℝ × ℝ ∂ν,
      0 ≤ p.1 ∧ 0 ≤ p.2 := by
    have hnull : ν (Set.Ici 0 ×ˢ Set.Ici 0)ᶜ = 0 := by
      rw [measure_compl (measurableSet_Ici.prod measurableSet_Ici)
        (by finiteness), hnonnegProd]
      simp
    filter_upwards [ae_iff.mpr hnull] with p hp
    exact hp
  have hscale : alphaStableScale α 1 1 ≠ 0 := by
    unfold alphaStableScale
    have htwo : (0 : ℝ) < (1 : ℝ) ^ α + 1 ^ α := by positivity
    exact (Real.rpow_pos_of_pos htwo _).ne'
  have hstable := h.2.2.2.2 1 1 (by norm_num) (by norm_num)
  have hmap : (μ.map (fun x => alphaStableScale α 1 1 * x)) {0} = μ {0} := by
    have hm : Measurable (fun x : ℝ => alphaStableScale α 1 1 * x) := by fun_prop
    rw [Measure.map_apply hm (measurableSet_singleton 0)]
    congr 1
    ext x
    simp [hscale]
  have hsum : ν (weightedSum 1 1 ⁻¹' {0}) = ν ({0} ×ˢ {0}) := by
    apply measure_congr
    filter_upwards [haeNonneg] with p hp
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod,
      weightedSum, one_mul]
    apply propext
    constructor
    · intro hzero
      constructor <;> linarith [hp.1, hp.2]
    · rintro ⟨hzero1, hzero2⟩
      rw [hzero1, hzero2]
      ring
  have hθeq : μ {0} = μ {0} * μ {0} := by
    calc
      μ {0} = (μ.map (fun x => alphaStableScale α 1 1 * x)) {0} := hmap.symm
      _ = (ν.map (weightedSum 1 1)) {0} := by simpa [ν] using congrArg (· {0}) hstable.symm
      _ = ν (weightedSum 1 1 ⁻¹' {0}) :=
        Measure.map_apply (measurable_weightedSum 1 1) (measurableSet_singleton 0)
      _ = ν ({0} ×ˢ {0}) := hsum
      _ = μ {0} * μ {0} := Measure.prod_prod _ _
  have hθ : μ {0} = μ (Set.Iic 0) := by
    have hsplit : μ (Set.Iio 0 ∪ {0}) =
        μ (Set.Iio 0) + μ {0} := by
      rw [measure_union]
      · apply Set.disjoint_left.mpr
        intro x hx hx0
        simp only [Set.mem_Iio, Set.mem_singleton_iff] at hx hx0
        linarith
      · exact measurableSet_singleton 0
    have hunion : Set.Iio (0 : ℝ) ∪ {0} = Set.Iic 0 := by
      ext x
      simp only [Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff, Set.mem_Iic]
      constructor
      · rintro (h | h) <;> linarith
      · intro h
        rcases lt_or_eq_of_le h with h | h
        · exact Or.inl h
        · exact Or.inr h
    rw [hunion, hneg0, zero_add] at hsplit
    exact hsplit.symm
  rw [hθ] at hθeq
  have hθfinite : μ (Set.Iic 0) ≠ ⊤ := (measure_lt_top μ _).ne
  have hθrealpos : 0 < (μ (Set.Iic 0)).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hθpos, measure_lt_top μ _⟩
  have hθreallt : (μ (Set.Iic 0)).toReal < 1 := by
    exact (ENNReal.toReal_lt_toReal hθfinite (by simp)).mpr hθlt
  have hθrealeq : (μ (Set.Iic 0)).toReal =
      (μ (Set.Iic 0)).toReal * (μ (Set.Iic 0)).toReal := by
    simpa only [ENNReal.toReal_mul] using congrArg ENNReal.toReal hθeq
  nlinarith [mul_pos hθrealpos (sub_pos.mpr hθreallt)]

end ProbabilityTheory

end
