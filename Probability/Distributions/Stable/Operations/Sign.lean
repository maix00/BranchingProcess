/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

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

private theorem one_sub_lt_one_of_pos {x : ENNReal}
    (hx : 0 < x) (hxle : x ≤ 1) : 1 - x < 1 := by
  have hxfinite : x ≠ ⊤ := ne_top_of_le_ne_top (by simp) hxle
  have hsubfinite : 1 - x ≠ ⊤ := by finiteness
  have hxrealpos : 0 < x.toReal := ENNReal.toReal_pos_iff.mpr
    ⟨hx, lt_top_iff_ne_top.mpr hxfinite⟩
  have hreal : (1 - x).toReal < (1 : ENNReal).toReal := by
    rw [ENNReal.toReal_sub_of_le hxle (by simp)]
    change (1 : ℝ) - x.toReal < 1
    linarith
  exact (ENNReal.toReal_lt_toReal hsubfinite (by simp)).mp hreal

/-- The original condition `0 < F(0) < 1` gives positive mass to both
signs. If the negative half-line had zero mass, the atom at zero would have
mass `θ ∈ (0,1)`; strict stability and nonnegativity force `θ = θ²`. -/
theorem IsStrictlyAlphaStable.twoSidedMass_of_cdfAtZero
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) :
    0 < μ (Set.Iio 0) ∧ 0 < μ (Set.Ioi 0) := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
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

/-- Negating a strictly stable law preserves strict stability. -/
private theorem IsStrictlyAlphaStable.map_neg
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ) :
    IsStrictlyAlphaStable α (μ.map Neg.neg) := by
  let ν : Measure ℝ := μ.map Neg.neg
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hνprob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    change (μ.map Neg.neg) Set.univ = 1
    rw [Measure.map_apply measurable_neg MeasurableSet.univ]
    simp
  have hνback : ν.map Neg.neg = μ := by
    dsimp [ν]
    rw [Measure.map_map measurable_neg measurable_neg]
    simp
  have hνnondeg : ¬ ∃ x : ℝ, ν = Measure.dirac x := by
    rintro ⟨x, hx⟩
    apply h.nondegenerate
    refine ⟨-x, ?_⟩
    calc
      μ = ν.map Neg.neg := hνback.symm
      _ = (Measure.dirac x).map Neg.neg := congrArg (fun m : Measure ℝ => m.map Neg.neg) hx
      _ = Measure.dirac (-x) := by simp
  refine ⟨h.1, h.2.1, hνprob, hνnondeg, ?_⟩
  intro a b ha hb
  let scale := alphaStableScale α a b
  have hprod : ν.prod ν = (μ.prod μ).map (Prod.map Neg.neg Neg.neg) := by
    dsimp [ν]
    rw [← Measure.map_prod_map μ μ measurable_neg measurable_neg]
  have hmap : (ν.prod ν).map (weightedSum a b) =
      ((μ.prod μ).map (weightedSum a b)).map Neg.neg := by
    calc
      (ν.prod ν).map (weightedSum a b) =
      (μ.prod μ).map (fun p => weightedSum a b (Prod.map Neg.neg Neg.neg p)) := by
        rw [hprod, Measure.map_map (measurable_weightedSum a b) (by fun_prop)]
        rfl
      _ = (μ.prod μ).map (fun p => -(weightedSum a b p)) := by
        congr 1
        funext p
        simp [weightedSum, Prod.map]
        ring
      _ = ((μ.prod μ).map (weightedSum a b)).map Neg.neg := by
        rw [Measure.map_map measurable_neg (measurable_weightedSum a b)]
        rfl
  have hscale : ν.map (fun x => scale * x) =
      (μ.map (fun x => scale * x)).map Neg.neg := by
    calc
      ν.map (fun x => scale * x) = μ.map (fun x => scale * (-x)) := by
        dsimp [ν]
        rw [Measure.map_map (by fun_prop) measurable_neg]
        congr 1
      _ = μ.map (fun x => -(scale * x)) := by
        congr 1
        funext x
        ring
      _ = (μ.map (fun x => scale * x)).map Neg.neg := by
        rw [Measure.map_map measurable_neg (by fun_prop)]
        rfl
  calc
    (ν.prod ν).map (weightedSum a b) =
        ((μ.prod μ).map (weightedSum a b)).map Neg.neg := hmap
    _ = (μ.map (fun x => scale * x)).map Neg.neg := by
      rw [h.2.2.2.2 a b ha hb]
    _ = ν.map (fun x => scale * x) := hscale.symm

/-- The source convention `F(0) = μ((-∞, 0))` implies Mathlib's right
continuous CDF condition for a nondegenerate strictly stable law. This
conversion uses strict stability to rule out a one-sided law with an atom at
zero; it does not assume atomlessness. -/
theorem IsStrictlyAlphaStable.cdfAtZero_condition_of_strictLeftMass
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (hleft : 0 < μ (Set.Iio 0) ∧ μ (Set.Iio 0) < 1) :
    0 < cdf μ 0 ∧ cdf μ 0 < 1 := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have hIic : μ (Set.Iic 0) = ENNReal.ofReal (cdf μ 0) :=
    (ofReal_cdf μ 0).symm
  have hIio_le_Iic : μ (Set.Iio 0) ≤ μ (Set.Iic 0) :=
    measure_mono (fun _ hx => hx.le)
  have hIic_pos : 0 < μ (Set.Iic 0) := hleft.1.trans_le hIio_le_Iic
  have hcdf_pos : 0 < cdf μ 0 := by
    apply ENNReal.ofReal_pos.mp
    rw [← hIic]
    exact hIic_pos
  have hIic_compl : μ (Set.Iic 0) = 1 - μ (Set.Ioi 0) := by
    rw [← Set.compl_Ioi, measure_compl measurableSet_Ioi (by finiteness)]
    simp
  have hν := h.map_neg
  let ν : Measure ℝ := μ.map Neg.neg
  have hνIic : ν (Set.Iic 0) = 1 - μ (Set.Iio 0) := by
    change (μ.map Neg.neg) (Set.Iic 0) = _
    rw [Measure.map_apply measurable_neg measurableSet_Iic]
    have hpre : Neg.neg ⁻¹' Set.Iic (0 : ℝ) = Set.Ici 0 := by
      ext x
      simp
    rw [hpre, ← Set.compl_Iio,
      measure_compl measurableSet_Iio (by finiteness)]
    simp
  have hνIic_pos : 0 < ν (Set.Iic 0) := by
    rw [hνIic]
    exact (tsub_pos_iff_lt.mpr hleft.2)
  have hleft_le_one : μ (Set.Iio 0) ≤ 1 := by
    calc
      μ (Set.Iio 0) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hνIic_lt : ν (Set.Iic 0) < 1 := by
    rw [hνIic]
    exact one_sub_lt_one_of_pos hleft.1 hleft_le_one
  have hνcdf : 0 < cdf ν 0 ∧ cdf ν 0 < 1 := by
    have hνeq : ν (Set.Iic 0) = ENNReal.ofReal (cdf ν 0) :=
      (ofReal_cdf ν 0).symm
    constructor
    · apply ENNReal.ofReal_pos.mp
      rw [← hνeq]
      exact hνIic_pos
    · apply ENNReal.ofReal_lt_one.mp
      rw [← hνeq]
      exact hνIic_lt
  have hνnegative : 0 < ν (Set.Iio 0) :=
    (hν.twoSidedMass_of_cdfAtZero hνcdf).1
  have hνIio : ν (Set.Iio 0) = μ (Set.Ioi 0) := by
    change (μ.map Neg.neg) (Set.Iio 0) = _
    rw [Measure.map_apply measurable_neg measurableSet_Iio]
    congr 1
    ext x
    simp
  have hIoi_pos : 0 < μ (Set.Ioi 0) := by
    rw [← hνIio]
    exact hνnegative
  have hIic_lt : μ (Set.Iic 0) < 1 := by
    rw [hIic_compl]
    have hIoi_le_one : μ (Set.Ioi 0) ≤ 1 := by
      calc
        μ (Set.Ioi 0) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact one_sub_lt_one_of_pos hIoi_pos hIoi_le_one
  have hcdf_lt : cdf μ 0 < 1 := by
    apply ENNReal.ofReal_lt_one.mp
    rw [← hIic]
    exact hIic_lt
  exact ⟨hcdf_pos, hcdf_lt⟩

end ProbabilityTheory

end
