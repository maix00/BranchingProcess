import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Topology.UnitInterval
import Topology.Cadlag.Skorokhod.TimeChange

/-!
# Rational grids on the unit interval

The rational points of `[0, 1]` form a countable dense family of times.  A
finite family of such points is contained in one finite uniform grid.  These
facts are independent of probability and path regularity.
-/

open Set

namespace Skorokhod

/-- Rational points in the closed unit interval. -/
abbrev RationalunitInterval := Set.Icc (0 : ℚ) 1

/-- The canonical inclusion of rational unit-interval points into the real
unit interval. -/
def rationalunitIntervalCoe (q : RationalunitInterval) : unitInterval :=
  ⟨(q : ℚ), by
    constructor
    · exact_mod_cast q.property.1
    · exact_mod_cast q.property.2⟩

theorem injective_rationalunitIntervalCoe :
    Function.Injective rationalunitIntervalCoe := by
  intro p q hpq
  apply Subtype.ext
  exact Rat.cast_injective (congrArg Subtype.val hpq)

/-- Rational unit-interval points are dense in the real unit interval. -/
theorem denseRange_rationalunitIntervalCoe :
    DenseRange rationalunitIntervalCoe := by
  rw [Metric.denseRange_iff]
  intro x radius hradius
  by_cases hx0 : (x : ℝ) = 0
  · refine ⟨⟨0, by simp⟩, ?_⟩
    rw [Subtype.dist_eq]
    simp [rationalunitIntervalCoe, hx0, hradius]
  by_cases hx1 : (x : ℝ) = 1
  · refine ⟨⟨1, by simp⟩, ?_⟩
    rw [Subtype.dist_eq]
    simp [rationalunitIntervalCoe, hx1, hradius]
  have hx0lt : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx0)
  have hx1lt : (x : ℝ) < 1 := lt_of_le_of_ne x.property.2 hx1
  let lower : ℝ := max 0 ((x : ℝ) - radius)
  let upper : ℝ := min 1 ((x : ℝ) + radius)
  have hlower : lower < (x : ℝ) := by
    dsimp only [lower]
    exact max_lt hx0lt (sub_lt_self _ hradius)
  have hupper : (x : ℝ) < upper := by
    dsimp only [upper]
    exact lt_min hx1lt (lt_add_of_pos_right _ hradius)
  obtain ⟨q, hlq, hqu⟩ := exists_rat_btwn (hlower.trans hupper)
  have hqmem : q ∈ Set.Icc (0 : ℚ) 1 := by
    constructor
    · exact_mod_cast (le_max_left 0 ((x : ℝ) - radius) |>.trans_lt hlq).le
    · exact_mod_cast (hqu.trans_le (min_le_left 1 ((x : ℝ) + radius))).le
  refine ⟨⟨q, hqmem⟩, ?_⟩
  rw [Subtype.dist_eq, Real.dist_eq]
  apply abs_lt.2
  constructor
  · have := hqu.trans_le (min_le_right 1 ((x : ℝ) + radius))
    dsimp only [rationalunitIntervalCoe]
    linarith
  · have := (le_max_right 0 ((x : ℝ) - radius)).trans_lt hlq
    dsimp only [rationalunitIntervalCoe]
    linarith

/-- Positive denominator of a rational unit-interval point. -/
def rationalDenominator (q : RationalunitInterval) : ℕ :=
  (q : ℚ).den

theorem rationalDenominator_pos (q : RationalunitInterval) :
    0 < rationalDenominator q :=
  Rat.den_pos _

/-- Natural numerator of a nonnegative rational unit-interval point. -/
def rationalNumerator (q : RationalunitInterval) : ℕ :=
  (q : ℚ).num.toNat

theorem rationalNum_nonneg (q : RationalunitInterval) :
    0 ≤ (q : ℚ).num := by
  exact Rat.num_nonneg.mpr q.property.1

theorem cast_rationalunitInterval_eq_numerator_div_denominator
    (q : RationalunitInterval) :
    (q : ℝ) = rationalNumerator q / rationalDenominator q := by
  rw [show (q : ℝ) = ((q : ℚ) : ℝ) by rfl, Rat.cast_def]
  unfold rationalNumerator rationalDenominator
  congr 1
  norm_cast
  exact (Int.toNat_of_nonneg (rationalNum_nonneg q)).symm

theorem rationalNumerator_le_denominator (q : RationalunitInterval) :
    rationalNumerator q ≤ rationalDenominator q := by
  have hcast : (q : ℝ) ≤ 1 := by exact_mod_cast q.property.2
  rw [cast_rationalunitInterval_eq_numerator_div_denominator,
    div_le_one (by exact_mod_cast rationalDenominator_pos q)] at hcast
  exact_mod_cast hcast

/-- A positive common denominator for a finite family of rational times. -/
def rationalGridDenominator (I : Finset RationalunitInterval) : ℕ :=
  ∏ q ∈ I, rationalDenominator q

theorem rationalGridDenominator_pos (I : Finset RationalunitInterval) :
    0 < rationalGridDenominator I := by
  unfold rationalGridDenominator
  exact Finset.prod_pos fun q _ ↦ rationalDenominator_pos q

theorem rationalDenominator_dvd_rationalGridDenominator
    {I : Finset RationalunitInterval} (q : I) :
    rationalDenominator q ∣ rationalGridDenominator I := by
  unfold rationalGridDenominator
  exact Finset.dvd_prod_of_mem (fun q ↦ rationalDenominator q) q.property

/-- Every finite family of rational unit-interval points is contained in one
finite uniform grid. -/
theorem exists_uniformGrid_of_finset (I : Finset RationalunitInterval) :
    ∃ blocks > 0, ∃ index : I → Fin (blocks + 1),
      ∀ i : I, (rationalunitIntervalCoe i : ℝ) =
        (index i : ℕ) / (blocks : ℝ) := by
  let blocks := rationalGridDenominator I
  have hblocks : 0 < blocks := rationalGridDenominator_pos I
  let indexValue : I → ℕ := fun i ↦
    rationalNumerator i * (blocks / rationalDenominator i)
  have hindex_le (i : I) : indexValue i ≤ blocks := by
    have hdvd : rationalDenominator i ∣ blocks :=
      rationalDenominator_dvd_rationalGridDenominator i
    calc
      indexValue i ≤ rationalDenominator i *
          (blocks / rationalDenominator i) := by
        dsimp only [indexValue]
        gcongr
        exact rationalNumerator_le_denominator i
      _ = blocks := Nat.mul_div_cancel' hdvd
  let index : I → Fin (blocks + 1) := fun i ↦
    ⟨indexValue i, Nat.lt_succ_iff.mpr (hindex_le i)⟩
  refine ⟨blocks, hblocks, index, fun (i : I) ↦ ?_⟩
  have hdvd : rationalDenominator i ∣ blocks :=
    rationalDenominator_dvd_rationalGridDenominator i
  have hquotient : 0 < blocks / rationalDenominator i := by
    exact Nat.div_pos (Nat.le_of_dvd hblocks hdvd) (rationalDenominator_pos i)
  rw [show (rationalunitIntervalCoe i : ℝ) = (i : ℝ) by rfl,
    cast_rationalunitInterval_eq_numerator_div_denominator]
  dsimp only [index, indexValue]
  push_cast
  rw [show (blocks : ℝ) =
      (rationalDenominator i : ℝ) *
        (blocks / rationalDenominator i : ℕ) by
    exact_mod_cast (Nat.mul_div_cancel' hdvd).symm]
  field_simp

end Skorokhod
