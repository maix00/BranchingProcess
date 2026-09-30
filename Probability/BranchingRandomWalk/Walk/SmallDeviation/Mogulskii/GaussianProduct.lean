module

public import Probability.Distributions.Gaussian.Interval

@[expose] public section

/-!
# Gaussian products for finite Mogulskii partitions

Scale monotonicity and a compatible quantitative parameter choice for the finite
Gaussian products used in the partition lower bound.  Gaussian interval
positivity itself lives in the distribution layer.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory.RandomWalk

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
  exact (gaussianReal_Ioo_pos (μ := 0) (v := 1) (by norm_num)
    (div_lt_div_of_pos_right (by linarith)
      (Real.sqrt_pos.2 hconstant))).ne'

/-- A quadratic `ENNReal.ofReal` error can be made smaller than any fixed
positive finite-dimensional probability while retaining an arbitrary
positive upper bound on its scale. -/
theorem exists_pos_lt_ofReal_mul_sq_div_lt
    {coefficient denominator : ℝ} {probability : ENNReal}
    (hprobability : 0 < probability) {upper : ℝ} (hupper : 0 < upper) :
    ∃ radius : ℝ, 0 < radius ∧ radius < upper ∧
      ENNReal.ofReal (coefficient * (radius ^ 2 / denominator ^ 2)) <
        probability := by
  have hreal : Tendsto
      (fun radius : ℝ => coefficient * (radius ^ 2 / denominator ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hfull : Tendsto
        (fun radius : ℝ => coefficient * (radius ^ 2 / denominator ^ 2))
        (𝓝 0) (𝓝 0) := by
      simpa using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => coefficient)
          (𝓝 0) (𝓝 coefficient)).mul
          (((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).pow 2).div_const
            (denominator ^ 2))
    exact hfull.mono_left inf_le_left
  have hennreal : Tendsto
      (fun radius : ℝ =>
        ENNReal.ofReal (coefficient * (radius ^ 2 / denominator ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  have hsmall : ∀ᶠ radius in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (coefficient * (radius ^ 2 / denominator ^ 2)) <
        probability :=
    (tendsto_order.1 hennreal).2 _ hprobability
  have hinterval : ∀ᶠ radius in 𝓝[>] (0 : ℝ),
      radius ∈ Ioo 0 upper := Ioo_mem_nhdsGT hupper
  obtain ⟨radius, hradius, herror⟩ := (hinterval.and hsmall).exists
  exact ⟨radius, hradius.1, hradius.2, herror⟩

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

/-- If the center shift is at most half the block radius, every shifted
Gaussian interval contains the fixed interval with half that radius.  This
removes the reference point from the numerical lower bound used by the
finite-cover return argument. -/
theorem prod_gaussian_Ioo_halfRadius_le_linearReturn
    {constant blockRadius y : ℝ} (hconstant : 0 < constant)
    {blocks : ℕ} (hblocks : 0 < blocks)
    (hshift : |y / (blocks : ℝ)| ≤ blockRadius / 2) :
    (∏ _j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo
            (-(blockRadius / 2) / Real.sqrt constant)
            ((blockRadius / 2) / Real.sqrt constant))) ≤
      ∏ _j : Fin blocks,
        gaussianReal 0 1
          (Set.Ioo
            (((-y / (blocks : ℝ)) - blockRadius) /
              Real.sqrt constant)
            (((-y / (blocks : ℝ)) + blockRadius) /
              Real.sqrt constant)) := by
  have hsqrt : 0 < Real.sqrt constant := Real.sqrt_pos.2 hconstant
  have hblocksReal : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have hshift' : |-y / (blocks : ℝ)| ≤ blockRadius / 2 := by
    rw [neg_div, abs_neg]
    exact hshift
  rw [abs_le] at hshift'
  apply Finset.prod_le_prod
  intro j hj
  apply measure_mono
  intro x hx
  constructor
  · apply lt_of_le_of_lt _ hx.1
    apply (div_le_div_iff_of_pos_right hsqrt).2
    linarith [hshift'.1]
  · apply lt_of_lt_of_le hx.2
    apply (div_le_div_iff_of_pos_right hsqrt).2
    linarith [hshift'.2]

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

/-- Uniform parameter choice for all linear-return intervals whose center
shift is at most half the prescribed radius.  The chosen constant, auxiliary
error, and positive lower bound do not depend on the reference point. -/
theorem exists_constant_error_lowerBound_lt_linearReturn
    {endpointMargin blockRadius : ℝ}
    (hendpointMargin : 0 < endpointMargin)
    (hblockRadius : 0 < blockRadius)
    {blocks : ℕ} (hblocks : 0 < blocks) :
    ∃ constant > 0, constant ≤ 1 ∧ ∃ error > 0,
      ∃ lowerBound : ENNReal, 0 < lowerBound ∧
        ∀ y : ℝ, |y / (blocks : ℝ)| ≤ blockRadius / 2 →
          lowerBound + ENNReal.ofReal
              (blocks * (constant / endpointMargin ^ 2 + error)) <
            ∏ _j : Fin blocks,
              gaussianReal 0 1
                (Set.Ioo
                  (((-y / (blocks : ℝ)) - blockRadius) /
                    Real.sqrt constant)
                  (((-y / (blocks : ℝ)) + blockRadius) /
                    Real.sqrt constant)) := by
  obtain ⟨constant, hconstant, hconstantOne, error, herror,
      lowerBound, hlowerBound, hgap⟩ :=
    exists_constant_error_lowerBound_lt_gaussianProduct
      hendpointMargin (half_pos hblockRadius) hblocks
  refine ⟨constant, hconstant, hconstantOne, error, herror,
    lowerBound, hlowerBound, ?_⟩
  intro y hy
  exact hgap.trans_le
    (prod_gaussian_Ioo_halfRadius_le_linearReturn
      hconstant hblocks hy)

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

end ProbabilityTheory.RandomWalk
