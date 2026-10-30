/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Distributions.Gaussian.Interval

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# Proof-specific Gaussian product parameters

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks.exists_error_lowerBound_gap_finset_gaussianProduct`:
  for $c,r>0$, $k>0$, and a nonempty finite reference family, if
  \[
    \operatorname{ofReal}\!\left(\frac{kc}{r^2}\right)
      < \prod_{j<k}\mathbb P\!\left(
        Z\in\left(\frac{x_{y,j}-R}{\sqrt c},
                   \frac{x_{y,j}+R}{\sqrt c}\right)\right)
  \]
  holds for every reference $y$, then one can choose $\delta>0$ and
  $0<\underline p\leq1$ so that
  \[
    \underline p+\operatorname{ofReal}\!\left(
      k\left(\frac{c}{r^2}+\delta\right)\right)
      < \prod_{j<k}\mathbb P\!\left(
        Z\in\left(\frac{x_{y,j}-R}{\sqrt c},
                   \frac{x_{y,j}+R}{\sqrt c}\right)\right)
  \]
  for every reference $y$.

These quantitative choices occur in the finite-partition lower-bound proof of
Theorem 3, Section 4, p. 764 of the 1974 Russian original by A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755–765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(4) (1975), 726–736, DOI 10.1137/1119081.
Gaussian interval positivity itself belongs to the distribution layer.
-/

section

open MeasureTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks

/-- If the principal maximal-inequality error is strictly below every member
of a nonempty finite Gaussian-product family, then a positive additional
error tolerance and a positive common survival bound can be chosen while
retaining a strict gap. -/
lemma exists_error_lowerBound_gap_finset_gaussianProduct
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

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Gaussian.Blocks
