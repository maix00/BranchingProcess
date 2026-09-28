import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Partition

/-!
# Gaussian products for finite Mogulskii partitions

Positivity, scale monotonicity, and a compatible quantitative parameter choice
for the finite Gaussian products used in the partition lower bound.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- Every nonempty open interval has positive mass under the standard
Gaussian law.  This is derived from mathlib's mutual absolute continuity of a
nondegenerate Gaussian law and Lebesgue measure. -/
theorem gaussianReal_zero_one_Ioo_pos {a b : ℝ} (hab : a < b) :
    0 < gaussianReal 0 1 (Set.Ioo a b) := by
  rw [pos_iff_ne_zero]
  intro hzero
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have hac := gaussianReal_absolutelyContinuous' (0 : ℝ) (v := 1) hv
  have hvolume : (volume : Measure ℝ) (Set.Ioo a b) = 0 := hac hzero
  have hpositive : 0 < (volume : Measure ℝ) (Set.Ioo a b) :=
    (Measure.measure_Ioo_pos (volume : Measure ℝ)).2 hab
  exact hpositive.ne' hvolume

/-- The finite Gaussian product occurring in the partition estimate is
strictly positive whenever the block scale and interval radius are positive. -/
theorem prod_gaussian_Ioo_sub_add_pos
    {constant blockRadius : ℝ} (hconstant : 0 < constant)
    (hblockRadius : 0 < blockRadius) {blocks : ℕ} (target : ℕ → ℝ) :
    0 < ∏ j : Fin blocks,
      gaussianReal 0 1
        (Set.Ioo
          ((target j - blockRadius) / Real.sqrt constant)
          ((target j + blockRadius) / Real.sqrt constant)) := by
  rw [pos_iff_ne_zero]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact (gaussianReal_zero_one_Ioo_pos
    (div_lt_div_of_pos_right (by linarith)
      (Real.sqrt_pos.2 hconstant))).ne'

/-- Shrinking a positive block constant below one only enlarges the symmetric
Gaussian interval used by the zero-target block estimate. -/
theorem prod_gaussian_Ioo_one_le_of_constant_le_one
    {constant blockRadius : ℝ} (hconstant : 0 < constant)
    (hconstantOne : constant ≤ 1) (hblockRadius : 0 < blockRadius)
    (blocks : ℕ) :
    (∏ _j : Fin blocks,
        gaussianReal 0 1 (Set.Ioo (-blockRadius) blockRadius)) ≤
      ∏ _j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo
            (-blockRadius / Real.sqrt constant)
            (blockRadius / Real.sqrt constant)) := by
  apply Finset.prod_le_prod
  intro j hj
  apply measure_mono
  intro x hx
  have hsqrtPos : 0 < Real.sqrt constant := Real.sqrt_pos.2 hconstant
  have hsqrtOne : Real.sqrt constant ≤ 1 := Real.sqrt_le_one.2 hconstantOne
  constructor
  · have hright : blockRadius ≤ blockRadius / Real.sqrt constant := by
      exact (le_div_iff₀ hsqrtPos).2
        (mul_le_of_le_one_right hblockRadius.le hsqrtOne)
    have hleft : -blockRadius / Real.sqrt constant ≤ -blockRadius := by
      simpa only [neg_div] using neg_le_neg hright
    exact hleft.trans_lt hx.1
  · have hright : blockRadius ≤ blockRadius / Real.sqrt constant := by
      exact (le_div_iff₀ hsqrtPos).2
        (mul_le_of_le_one_right hblockRadius.le hsqrtOne)
    exact hx.2.trans_le hright

/-- There are explicit positive block and error parameters for which a
positive numerical lower bound remains after paying the maximal-inequality
error.  The comparison uses the Gaussian product at block constant one; a
smaller constant only enlarges its symmetric intervals. -/
theorem exists_constant_error_lowerBound_lt_gaussianProduct
    {endpointMargin blockRadius : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius)
    {blocks : ℕ} (hblocks : 0 < blocks) :
    ∃ constant > 0, constant ≤ 1 ∧ ∃ error > 0,
      ∃ lowerBound : ENNReal, 0 < lowerBound ∧
        lowerBound + ENNReal.ofReal
            (blocks * (constant / endpointMargin ^ 2 + error)) <
          ∏ _j : Fin blocks,
            gaussianReal 0 1
              (Set.Ioo
                (-blockRadius / Real.sqrt constant)
                (blockRadius / Real.sqrt constant)) := by
  let base : ENNReal := ∏ _j : Fin blocks,
    gaussianReal 0 1 (Set.Ioo (-blockRadius) blockRadius)
  have hbasePos : 0 < base := by
    simpa [base] using
      (prod_gaussian_Ioo_sub_add_pos (constant := (1 : ℝ))
        zero_lt_one hblockRadius (blocks := blocks) (fun _ => 0))
  have hbaseLeOne : base ≤ 1 := by
    dsimp [base]
    apply Finset.prod_le_one
    intro j hj
    simpa using
      (measure_mono (by intro x hx; trivial) :
        gaussianReal 0 1 (Set.Ioo (-blockRadius) blockRadius) ≤
          gaussianReal 0 1 Set.univ)
  have hbaseTop : base ≠ ⊤ :=
    ne_of_lt (hbaseLeOne.trans_lt ENNReal.one_lt_top)
  have hbaseRealPos : 0 < base.toReal :=
    ENNReal.toReal_pos hbasePos.ne' hbaseTop
  have hblocksReal : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have hmarginSq : 0 < endpointMargin ^ 2 := sq_pos_of_pos hendpointMargin
  let constant : ℝ := min (1 / 2)
    (base.toReal * endpointMargin ^ 2 / (16 * (blocks : ℝ)))
  have hconstant : 0 < constant := by
    dsimp [constant]
    rw [lt_min_iff]
    constructor
    · norm_num
    · exact div_pos (mul_pos hbaseRealPos hmarginSq) (by positivity)
  have hconstantOne : constant ≤ 1 :=
    (min_le_left _ _).trans (by norm_num)
  have hconstantBound :
      constant ≤ base.toReal * endpointMargin ^ 2 /
        (16 * (blocks : ℝ)) := min_le_right _ _
  let error := constant / endpointMargin ^ 2
  have herror : 0 < error := div_pos hconstant hmarginSq
  have htotal :
      (blocks : ℝ) * (constant / endpointMargin ^ 2 + error) ≤
        base.toReal / 8 := by
    dsimp [error]
    calc
      (blocks : ℝ) *
          (constant / endpointMargin ^ 2 +
            constant / endpointMargin ^ 2) =
          2 * (blocks : ℝ) * constant / endpointMargin ^ 2 := by ring
      _ ≤ 2 * (blocks : ℝ) *
          (base.toReal * endpointMargin ^ 2 /
            (16 * (blocks : ℝ))) / endpointMargin ^ 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hconstantBound (by positivity))
          hmarginSq.le
      _ = base.toReal / 8 := by
        field_simp [hblocksReal.ne', hmarginSq.ne']
        ring
  let lowerBound := ENNReal.ofReal (base.toReal / 2)
  have hlowerBound : 0 < lowerBound := ENNReal.ofReal_pos.2 (by positivity)
  have herrorBound :
      ENNReal.ofReal
          (blocks * (constant / endpointMargin ^ 2 + error)) ≤
        ENNReal.ofReal (base.toReal / 8) :=
    ENNReal.ofReal_le_ofReal htotal
  have hgapBase : lowerBound + ENNReal.ofReal
        (blocks * (constant / endpointMargin ^ 2 + error)) < base := by
    calc
      lowerBound + ENNReal.ofReal
          (blocks * (constant / endpointMargin ^ 2 + error)) ≤
          ENNReal.ofReal (base.toReal / 2) +
            ENNReal.ofReal (base.toReal / 8) :=
        by simpa [lowerBound, add_comm] using
          add_le_add_left herrorBound (ENNReal.ofReal (base.toReal / 2))
      _ = ENNReal.ofReal (base.toReal / 2 + base.toReal / 8) := by
        rw [ENNReal.ofReal_add] <;> positivity
      _ < ENNReal.ofReal base.toReal := by
        exact (ENNReal.ofReal_lt_ofReal_iff hbaseRealPos).2 (by linarith)
      _ = base := ENNReal.ofReal_toReal hbaseTop
  refine ⟨constant, hconstant, hconstantOne, error, herror,
    lowerBound, hlowerBound, ?_⟩
  exact hgapBase.trans_le
    (prod_gaussian_Ioo_one_le_of_constant_le_one
      hconstant hconstantOne hblockRadius blocks)

/-- If the principal maximal-inequality error is strictly below every member
of a nonempty finite Gaussian-product family, then a positive additional
error tolerance and a positive common survival bound can be chosen while
retaining a strict gap. -/
theorem exists_error_lowerBound_gap_finset_gaussianProduct
    {constant endpointMargin blockRadius : ℝ}
    (hconstant : 0 < constant)
    (hendpointMargin : 0 < endpointMargin)
    {blocks : ℕ} (hblocks : 0 < blocks)
    (references : Finset ℝ) (hreferences : references.Nonempty)
    (target : ℝ → ℕ → ℝ)
    (hprincipal : ∀ y ∈ references,
      ENNReal.ofReal (blocks * (constant / endpointMargin ^ 2)) <
        ∏ j : Fin blocks,
          gaussianReal 0 1
            (Set.Ioo
              ((target y j - blockRadius) / Real.sqrt constant)
              ((target y j + blockRadius) / Real.sqrt constant))) :
    ∃ error > 0, ∃ lowerBound : ENNReal,
      0 < lowerBound ∧ lowerBound ≤ 1 ∧ ∀ y ∈ references,
        lowerBound + ENNReal.ofReal
            (blocks * (constant / endpointMargin ^ 2 + error)) <
          ∏ j : Fin blocks,
            gaussianReal 0 1
              (Set.Ioo
                ((target y j - blockRadius) / Real.sqrt constant)
                ((target y j + blockRadius) / Real.sqrt constant)) := by
  classical
  let product : ℝ → ENNReal := fun y => ∏ j : Fin blocks,
    gaussianReal 0 1
      (Set.Ioo
        ((target y j - blockRadius) / Real.sqrt constant)
        ((target y j + blockRadius) / Real.sqrt constant))
  obtain ⟨y₀, hy₀, hy₀Min⟩ :=
    references.exists_min_image product hreferences
  have hproductLeOne : product y₀ ≤ 1 := by
    dsimp [product]
    apply Finset.prod_le_one
    intro j hj
    simpa using
      (measure_mono (by intro x hx; trivial) :
        gaussianReal 0 1
            (Set.Ioo
              ((target y₀ j - blockRadius) / Real.sqrt constant)
              ((target y₀ j + blockRadius) / Real.sqrt constant)) ≤
          gaussianReal 0 1 Set.univ)
  have hproductTop : product y₀ ≠ ⊤ :=
    ne_of_lt (hproductLeOne.trans_lt ENNReal.one_lt_top)
  have hblocksReal : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have hmarginSq : 0 < endpointMargin ^ 2 :=
    sq_pos_of_pos hendpointMargin
  let principal : ℝ :=
    (blocks : ℝ) * (constant / endpointMargin ^ 2)
  have hprincipalNonneg : 0 ≤ principal := by
    dsimp [principal]
    positivity
  have hstrict : ENNReal.ofReal principal < product y₀ := by
    simpa [principal] using hprincipal y₀ hy₀
  have hstrictReal : principal < (product y₀).toReal := by
    have h :=
      (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hproductTop).2 hstrict
    simpa [ENNReal.toReal_ofReal hprincipalNonneg] using h
  have hproductPos : 0 < product y₀ := lt_of_le_of_lt bot_le hstrict
  have hproductRealPos : 0 < (product y₀).toReal :=
    ENNReal.toReal_pos hproductPos.ne' hproductTop
  let gap : ℝ := (product y₀).toReal - principal
  have hgap : 0 < gap := sub_pos.mpr hstrictReal
  let error : ℝ := gap / (4 * (blocks : ℝ))
  have herror : 0 < error := div_pos hgap (by positivity)
  let lowerBound : ENNReal := ENNReal.ofReal (gap / 4)
  have hlowerBound : 0 < lowerBound :=
    ENNReal.ofReal_pos.2 (div_pos hgap (by norm_num))
  have hlowerBoundOne : lowerBound ≤ 1 := by
    calc
      lowerBound ≤ product y₀ := by
        rw [show lowerBound = ENNReal.ofReal (gap / 4) by rfl,
          ← ENNReal.ofReal_toReal hproductTop]
        exact ENNReal.ofReal_le_ofReal (by
          dsimp [gap]
          nlinarith [hprincipalNonneg, hproductRealPos])
      _ ≤ 1 := hproductLeOne
  refine ⟨error, herror, lowerBound, hlowerBound, hlowerBoundOne, ?_⟩
  intro y hy
  have hmin : product y₀ ≤ product y := hy₀Min y hy
  have hsum : lowerBound + ENNReal.ofReal
      (blocks * (constant / endpointMargin ^ 2 + error)) < product y₀ := by
    rw [show lowerBound = ENNReal.ofReal (gap / 4) by rfl]
    have htotal : (blocks : ℝ) *
        (constant / endpointMargin ^ 2 + error) = principal + gap / 4 := by
      dsimp [error, principal]
      field_simp [hblocksReal.ne']
    rw [htotal]
    have hquarterNonneg : 0 ≤ gap / 4 := by positivity
    have htotalNonneg : 0 ≤ principal + gap / 4 :=
      add_nonneg hprincipalNonneg hquarterNonneg
    calc
      ENNReal.ofReal (gap / 4) + ENNReal.ofReal (principal + gap / 4) =
          ENNReal.ofReal (gap / 4 + (principal + gap / 4)) :=
        (ENNReal.ofReal_add hquarterNonneg htotalNonneg).symm
      _ < ENNReal.ofReal (product y₀).toReal :=
        (ENNReal.ofReal_lt_ofReal_iff hproductRealPos).2 (by
          dsimp [gap]
          nlinarith)
      _ = product y₀ := ENNReal.ofReal_toReal hproductTop
  exact hsum.trans_le hmin

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
