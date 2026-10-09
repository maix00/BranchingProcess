/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.CadlagPath.Tightness
public import Probability.Process.RandomWalk.Path.Skorokhod
public import Probability.Process.RandomWalk.Path.Skorokhod.Oscillation
public import Topology.Cadlag.Skorokhod.Oscillation.DoubleExcursion.Converse

/-!
# Random-walk oscillation partitions

This module turns uniform finite-window double-excursion and endpoint
probability estimates into the multiscale oscillation-partition events used
by the deterministic Skorokhod compactness criterion. Distribution-specific
estimates are supplied by adapters.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk.FunctionalLimit

/-- Integer window length used to cover the sample by overlapping blocks.
The additive one keeps the window nonempty even at the first few horizons. -/
private noncomputable def oscillationWindowWidth (δ : ℝ) (n : ℕ) : ℕ :=
  ⌈2 * δ * (n : ℝ)⌉₊ + 1

/-- The window length has the lower coverage bound and the asymptotic upper
fraction needed by both stable excursion estimates. -/
private theorem eventually_oscillationWindowGeometry {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 16) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧
        (n : ℝ) * δ ≤ oscillationWindowWidth δ n ∧
        (2 * oscillationWindowWidth δ n : ℝ) / n ≤ 6 * δ ∧
        (oscillationWindowWidth δ n : ℝ) / n ≤ 6 * δ ∧
        ((n / oscillationWindowWidth δ n + 1 : ℕ) : ℝ) ≤ 1 / δ := by
  have hrecip : ∀ᶠ n : ℕ in atTop, 2 / (n : ℝ) ≤ δ := by
    have hlim : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) := by
      simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hhalf : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n < δ / 2 :=
      hlim.eventually (Iio_mem_nhds (half_pos hδ))
    filter_upwards [hhalf, eventually_gt_atTop (0 : ℕ)] with n hhalf hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hdiv : 2 / (n : ℝ) < δ := by
      have h := hhalf
      field_simp [ne_of_gt hnR] at h ⊢
      nlinarith
    exact hdiv.le
  filter_upwards [hrecip, eventually_gt_atTop (0 : ℕ)] with n hrecip hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let c : ℝ := (⌈2 * δ * (n : ℝ)⌉₊ : ℝ)
  have hceilLower : 2 * δ * (n : ℝ) ≤ c := by
    dsimp [c]
    exact Nat.le_ceil _
  have hceilUpper : c < 2 * δ * (n : ℝ) + 1 := by
    dsimp [c]
    exact Nat.ceil_lt_add_one (by positivity)
  have hwidth : (oscillationWindowWidth δ n : ℝ) = c + 1 := by
    simp [oscillationWindowWidth, c]
  have hwidthLower : 2 * δ * (n : ℝ) ≤
      (oscillationWindowWidth δ n : ℝ) := by
    rw [hwidth]
    linarith
  have hwidthUpper : (oscillationWindowWidth δ n : ℝ) <
      2 * δ * (n : ℝ) + 2 := by
    rw [hwidth]
    linarith
  have hcoverage : (n : ℝ) * δ ≤
      (oscillationWindowWidth δ n : ℝ) := by
    nlinarith [hwidthLower]
  have hwidthRatio : (oscillationWindowWidth δ n : ℝ) / n ≤ 3 * δ := by
    apply (div_le_iff₀ hnR).2
    have hrecip' : 2 ≤ δ * (n : ℝ) := by
      have := hrecip
      rw [div_le_iff₀ hnR] at this
      nlinarith
    nlinarith [hwidthUpper]
  have hdoubleRatio :
      (2 * oscillationWindowWidth δ n : ℝ) / n ≤ 6 * δ := by
    calc
      (2 * oscillationWindowWidth δ n : ℝ) / n =
          2 * ((oscillationWindowWidth δ n : ℝ) / n) := by ring
      _ ≤ 2 * (3 * δ) := by nlinarith [hwidthRatio]
      _ = 6 * δ := by ring
  let q : ℝ := ((n / oscillationWindowWidth δ n : ℕ) : ℝ)
  have hquotientProduct :
      ((n / oscillationWindowWidth δ n : ℕ) : ℝ) *
          (oscillationWindowWidth δ n : ℝ) ≤ n := by
    exact_mod_cast Nat.div_mul_le_self n (oscillationWindowWidth δ n)
  have hqProduct : q * (2 * δ * (n : ℝ)) ≤ n := by
    dsimp [q]
    calc
      ((n / oscillationWindowWidth δ n : ℕ) : ℝ) *
          (2 * δ * (n : ℝ)) ≤
        ((n / oscillationWindowWidth δ n : ℕ) : ℝ) *
          (oscillationWindowWidth δ n : ℝ) := by
            gcongr
      _ ≤ n := hquotientProduct
  have hqDen : q * (2 * δ) ≤ 1 := by
    have hmul : (q * (2 * δ)) * (n : ℝ) ≤ 1 * (n : ℝ) := by
      nlinarith [hqProduct]
    exact le_of_mul_le_mul_right hmul hnR
  have hq : q ≤ 1 / (2 * δ) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [hqDen]
  have hrecipOne : 1 ≤ 1 / (2 * δ) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [hδsmall]
  have hcount : ((n / oscillationWindowWidth δ n + 1 : ℕ) : ℝ) ≤ 1 / δ := by
    calc
      ((n / oscillationWindowWidth δ n + 1 : ℕ) : ℝ) = q + 1 := by simp [q]
      _ ≤
        1 / (2 * δ) + 1 := by linarith [hq]
      _ ≤ 1 / δ := by
        have hidentity : 1 / δ = 1 / (2 * δ) + 1 / (2 * δ) := by
          field_simp
          ring
        rw [hidentity]
        linarith [hrecipOne]
  exact ⟨hn, hcoverage, hdoubleRatio, hwidthRatio.trans (by nlinarith [hδsmall]),
    hcount⟩

/-- Uniform finite-window double-excursion and endpoint bounds yield a
multiscale oscillation-partition event. The local probability estimates and
the control of truncation bias are supplied by the distribution-specific
adapter. -/
theorem exists_eventually_oscillationPartitions_bound_of_localEstimates
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization : ℕ → ℝ}
    (hscale : ∀ᶠ n : ℕ in atTop, 0 < normalization n)
    (coefficient : ℝ → ℝ) (hcoefficient : ∀ {ε : ℝ}, 0 < ε → 0 < coefficient ε)
    (biasBound : ℝ) (hbiasBound : 0 ≤ biasBound)
    (hdoubleProvider : ∀ {ε endpointDelta blockFraction : ℝ} {width : ℕ → ℕ},
      0 < ε → 0 < endpointDelta → 0 < blockFraction →
      blockFraction * biasBound < ε / 4 →
      (∀ n, 0 < width n) →
      (∀ᶠ n : ℕ in atTop, (n : ℝ) * endpointDelta ≤ width n) →
      (∀ᶠ n : ℕ in atTop, (2 * width n : ℝ) / n ≤ blockFraction) →
      ∀ᶠ n : ℕ in atTop,
        iidSequenceLaw ν
          {increment | ¬ Skorokhod.HasDoubleExcursionBound
            (RandomWalk.normalizedStepCadlagPathIcc normalization n increment)
            endpointDelta ε} ≤
          ((n / width n + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal (blockFraction * coefficient ε)) ^ 2)
    (hendpointProvider : ∀ {ε endpointDelta blockFraction : ℝ} {width : ℕ → ℕ},
      0 < ε → 0 < endpointDelta → 0 < blockFraction →
      blockFraction * biasBound < ε / 4 →
      (∀ n, 0 < width n) →
      (∀ᶠ n : ℕ in atTop, (n : ℝ) * endpointDelta ≤ width n) →
      (∀ᶠ n : ℕ in atTop, (width n : ℝ) / n ≤ blockFraction) →
      ∀ᶠ n : ℕ in atTop,
        iidSequenceLaw ν
          {increment | ¬ Skorokhod.HasEndpointOscillationBound
            (RandomWalk.normalizedStepCadlagPathIcc normalization n increment)
            endpointDelta ε} ≤
          2 * ENNReal.ofReal (blockFraction * coefficient ε))
    {η : ℝ≥0∞} (hη : 0 < η) (hηone : η < 1) :
    ∃ gap oscillationTolerance : ℕ → ℝ,
      (∀ m, 0 < gap m) ∧ (∀ m, 0 < oscillationTolerance m) ∧
        Tendsto oscillationTolerance atTop (nhds 0) ∧
          ∀ᶠ n : ℕ in atTop,
            (normalizedStepPathLaw ν normalization n)
              (Skorokhod.admitsOscillationPartitionSequence
                (E := ℝ) gap oscillationTolerance)ᶜ ≤ η := by
  have hηTop : η ≠ ∞ := ne_of_lt (lt_of_lt_of_le hηone le_top)
  have hηReal : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hη) hηTop
  let epsilon : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  let budget : ℕ → ℝ≥0∞ := fun m => (η / 2) * (2⁻¹ : ℝ≥0∞) ^ m
  let levelCoefficient : ℕ → ℝ := fun m => coefficient (epsilon m)
  let δ : ℕ → ℝ := fun m => min (1 / 16)
    (min ((budget m).toReal / (96 * (levelCoefficient m + 1) ^ 2))
      (epsilon m / (80 * (biasBound + 1))))
  have hepsilon (m : ℕ) : 0 < epsilon m := by
    dsimp [epsilon]
    positivity
  have hbudgetPos (m : ℕ) : 0 < budget m := by
    dsimp [budget]
    apply (ENNReal.mul_pos_iff).2
    refine ⟨ENNReal.div_pos_iff.mpr ⟨ne_of_gt hη, by norm_num⟩, ?_⟩
    exact ENNReal.pow_pos (ENNReal.inv_pos.mpr (by norm_num)) _
  have hbudgetTop (m : ℕ) : budget m ≠ ∞ := by
    dsimp [budget]
    apply ENNReal.mul_ne_top
    · exact ENNReal.div_ne_top hηTop (by norm_num)
    · exact ENNReal.pow_ne_top (by norm_num)
  have hbudgetReal (m : ℕ) : 0 < (budget m).toReal :=
    ENNReal.toReal_pos (ne_of_gt (hbudgetPos m)) (hbudgetTop m)
  have hlevelCoefficient (m : ℕ) : 0 < levelCoefficient m := by
    dsimp [levelCoefficient]
    exact hcoefficient (hepsilon m)
  have hδpos (m : ℕ) : 0 < δ m := by
    dsimp [δ]
    have hlevelCoefficientPos : 0 < levelCoefficient m + 1 := by
      linarith [hlevelCoefficient m]
    have hfirst : 0 < 96 * (levelCoefficient m + 1) ^ 2 := by
      positivity
    have hsecond : 0 < 80 * (biasBound + 1) := by
      have hbias : 0 < biasBound + 1 := by linarith [hbiasBound]
      positivity
    refine lt_min (by norm_num) (lt_min ?_ ?_)
    · exact div_pos (hbudgetReal m) hfirst
    · exact div_pos (hepsilon m) hsecond
  have hδsmall (m : ℕ) : δ m ≤ 1 / 16 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδbudget (m : ℕ) :
      δ m ≤ (budget m).toReal / (96 * (levelCoefficient m + 1) ^ 2) := by
    dsimp [δ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδbias (m : ℕ) :
      6 * δ m * biasBound < epsilon m / 4 := by
    have hbiasDen : 0 < biasBound + 1 := by linarith
    have hδ' : δ m ≤ epsilon m / (80 * (biasBound + 1)) := by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hmul := mul_le_mul_of_nonneg_right hδ' hbiasBound
    have hbound : 6 * (epsilon m / (80 * (biasBound + 1))) * biasBound ≤
        epsilon m / 8 := by
      have hε := hepsilon m
      field_simp [ne_of_gt hbiasDen]
      nlinarith [hε, hbiasBound]
    nlinarith [hmul, hbound, hepsilon m]
  have hepsilonTendsto : Tendsto epsilon atTop (nhds 0) := by
    change Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (nhds 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hbudgetSum : ∑' m : ℕ, budget m = η := by
    simp only [budget, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
    rw [ENNReal.div_eq_inv_mul]
    calc
      2⁻¹ * η * 2 = η * (2⁻¹ * 2) := by ac_rfl
      _ = η := by
        rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]
  classical
  let width : ℕ → ℕ → ℕ := fun m n => oscillationWindowWidth (δ m) n
  have hlevelLarge : ∀ m : ℕ, ∀ᶠ n : ℕ in atTop,
      (normalizedStepPathLaw ν normalization n)
        (Skorokhod.admitsOscillationPartition (E := ℝ)
          (min (δ m / 32) 1) (6 * epsilon m))ᶜ ≤ budget m := by
    intro m
    let widthAtLevel : ℕ → ℕ := width m
    have hgeom := eventually_oscillationWindowGeometry (hδpos m) (hδsmall m)
    have hwidth : ∀ n, 0 < widthAtLevel n := by
      intro n
      dsimp [widthAtLevel, width, oscillationWindowWidth]
      omega
    have hwidthLower : ∀ᶠ n : ℕ in atTop,
        (n : ℝ) * δ m ≤ widthAtLevel n := by
      filter_upwards [hgeom] with n hn
      exact hn.2.1
    have hdoubleRatio : ∀ᶠ n : ℕ in atTop,
        (2 * widthAtLevel n : ℝ) / n ≤ 6 * δ m := by
      filter_upwards [hgeom] with n hn
      exact hn.2.2.1
    have hdoubleRatio' : ∀ᶠ n : ℕ in atTop,
        ((2 * widthAtLevel n : ℕ) : ℝ) / n ≤ 6 * δ m := by
      filter_upwards [hdoubleRatio] with n hn
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn
    have hendpointRatio : ∀ᶠ n : ℕ in atTop,
        (widthAtLevel n : ℝ) / n ≤ 6 * δ m := by
      filter_upwards [hgeom] with n hn
      exact hn.2.2.2.1.trans (by nlinarith [hδsmall m])
    have hcount : ∀ᶠ n : ℕ in atTop,
        ((n / widthAtLevel n + 1 : ℕ) : ℝ) ≤ 1 / δ m := by
      filter_upwards [hgeom] with n hn
      exact hn.2.2.2.2
    have hsmall : (6 * δ m) * biasBound < epsilon m / 4 := by
      simpa [show (6 : ℝ) * δ m * biasBound = 6 * δ m * biasBound by ring] using
        hδbias m
    have hdouble := hdoubleProvider (ε := epsilon m) (endpointDelta := δ m)
      (blockFraction := 6 * δ m) (width := widthAtLevel)
      (hepsilon m) (hδpos m) (mul_pos (by norm_num) (hδpos m))
      hsmall hwidth hwidthLower hdoubleRatio
    have hendpoint := hendpointProvider (ε := epsilon m) (endpointDelta := δ m)
      (blockFraction := 6 * δ m) (width := widthAtLevel)
      (hepsilon m) (hδpos m) (mul_pos (by norm_num) (hδpos m))
      hsmall hwidth hwidthLower hendpointRatio
    have hlarge : ∀ᶠ n : ℕ in atTop,
        (normalizedStepPathLaw ν normalization n)
          (Skorokhod.admitsOscillationPartition (E := ℝ)
            (min (δ m / 32) 1) (6 * epsilon m))ᶜ ≤ budget m := by
      filter_upwards [hdouble, hendpoint, hgeom, hscale] with n hd he hg hs
      let path := RandomWalk.normalizedStepCadlagPathIcc normalization n
      let pathAdmission := Skorokhod.admitsOscillationPartition
        (E := ℝ) (min (δ m / 32) 1) (6 * epsilon m)
      have hpathSubset : path ⁻¹' pathAdmissionᶜ ⊆
          {increment | ¬ Skorokhod.HasDoubleExcursionBound
              (path increment) (δ m) (epsilon m)} ∪
            {increment | ¬ Skorokhod.HasEndpointOscillationBound
              (path increment) (δ m) (epsilon m)} := by
        intro increment hnot
        by_contra hgood
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hgood
        have hdoublePath : Skorokhod.HasDoubleExcursionBound
            (path increment) (δ m) (epsilon m) := not_not.mp hgood.1
        have hendpointPath : Skorokhod.HasEndpointOscillationBound
            (path increment) (δ m) (epsilon m) := not_not.mp hgood.2
        obtain ⟨partition, hmesh, hosc⟩ :=
          Skorokhod.HasDoubleExcursionBound.exists_oscillation_partition
            hdoublePath hendpointPath
            (hδpos m) (by linarith [hδsmall m]) (hepsilon m)
        have hgap : min (δ m / 32) 1 < δ m / 16 := by
          apply lt_of_le_of_lt (min_le_left _ _)
          linarith [hδpos m]
        have hbound : 5 * epsilon m < 6 * epsilon m := by
          linarith [hepsilon m]
        have hmem : path increment ∈ pathAdmission := by
          change ∃ p : Skorokhod.OscillationPartition,
            min (δ m / 32) 1 < p.mesh ∧
              ∃ oscillation < 6 * epsilon m,
                Skorokhod.OscillationBoundedOnPartition p (path increment) oscillation
          exact ⟨partition, lt_of_lt_of_le hgap hmesh, 5 * epsilon m,
            hbound, hosc⟩
        exact hnot (by simpa [path, pathAdmission] using hmem)
      have hdoubleNum :
          ((n / widthAtLevel n + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal (6 * δ m * levelCoefficient m)) ^ 2 ≤
              ENNReal.ofReal (36 * δ m * (levelCoefficient m) ^ 2) := by
        have hcountN : ((n / widthAtLevel n + 1 : ℕ) : ℝ≥0∞) ≤
            ENNReal.ofReal (1 / δ m) := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hg.2.2.2.2
        calc
          _ ≤ ENNReal.ofReal (1 / δ m) *
              (ENNReal.ofReal (6 * δ m * levelCoefficient m)) ^ 2 :=
                mul_le_mul_of_nonneg_right hcountN (sq_nonneg _)
          _ = ENNReal.ofReal (36 * δ m * (levelCoefficient m) ^ 2) := by
            have hscaledNonneg : 0 ≤ 6 * δ m * levelCoefficient m :=
              mul_nonneg (mul_nonneg (by norm_num) (hδpos m).le)
                (hlevelCoefficient m).le
            have hδinv : 0 ≤ 1 / δ m := div_nonneg (by norm_num) (hδpos m).le
            rw [← ENNReal.ofReal_pow hscaledNonneg]
            rw [← ENNReal.ofReal_mul hδinv]
            congr 1
            field_simp [ne_of_gt (hδpos m)]
            ring
      have hendpointNum :
          2 * ENNReal.ofReal (6 * δ m * levelCoefficient m) ≤
            ENNReal.ofReal (12 * δ m * levelCoefficient m) := by
        apply le_of_eq
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
        congr 1
        ring
      have hbudgetEstimate :
          36 * δ m * (levelCoefficient m) ^ 2 +
            12 * δ m * levelCoefficient m ≤ (budget m).toReal := by
        have hA : 1 ≤ levelCoefficient m + 1 := by linarith [hlevelCoefficient m]
        have hprod : δ m * (96 * (levelCoefficient m + 1) ^ 2) ≤
            (budget m).toReal := by
          exact (le_div_iff₀ (by positivity)).mp (hδbudget m)
        have hmain : 48 * δ m * (levelCoefficient m + 1) ^ 2 ≤
            (budget m).toReal / 2 := by
          nlinarith [hprod]
        have hcoarse : 36 * δ m * (levelCoefficient m) ^ 2 +
            12 * δ m * levelCoefficient m ≤
              48 * δ m * (levelCoefficient m + 1) ^ 2 := by
          have hδnonneg : 0 ≤ δ m := (hδpos m).le
          have hcoeffnonneg : 0 ≤ levelCoefficient m := (hlevelCoefficient m).le
          nlinarith
        nlinarith [hmain, hcoarse, hbudgetReal m]
      have hprob : (iidSequenceLaw ν) (path ⁻¹' pathAdmissionᶜ) ≤ budget m := by
        calc
          _ ≤ (iidSequenceLaw ν)
                ({increment | ¬ Skorokhod.HasDoubleExcursionBound
                    (path increment) (δ m) (epsilon m)} ∪
                  {increment | ¬ Skorokhod.HasEndpointOscillationBound
                    (path increment) (δ m) (epsilon m)}) := measure_mono hpathSubset
          _ ≤ (iidSequenceLaw ν)
                {increment | ¬ Skorokhod.HasDoubleExcursionBound
                  (path increment) (δ m) (epsilon m)} +
              (iidSequenceLaw ν)
                {increment | ¬ Skorokhod.HasEndpointOscillationBound
                  (path increment) (δ m) (epsilon m)} := measure_union_le _ _
          _ ≤ ENNReal.ofReal (36 * δ m * (levelCoefficient m) ^ 2) +
              ENNReal.ofReal (12 * δ m * levelCoefficient m) := by
            apply add_le_add
            · calc
                _ ≤ ((n / widthAtLevel n + 1 : ℕ) : ℝ≥0∞) *
                    (ENNReal.ofReal (6 * δ m * levelCoefficient m)) ^ 2 := by
                      simpa [path] using hd
                _ ≤ ENNReal.ofReal (36 * δ m * (levelCoefficient m) ^ 2) := hdoubleNum
            · calc
                _ ≤ 2 * ENNReal.ofReal (6 * δ m * levelCoefficient m) := by
                      simpa [path] using he
                _ ≤ ENNReal.ofReal (12 * δ m * levelCoefficient m) := hendpointNum
          _ ≤ budget m := by
            have hfirstNonneg : 0 ≤ 36 * δ m * (levelCoefficient m) ^ 2 := by
              exact mul_nonneg (mul_nonneg (by norm_num) (hδpos m).le)
                (sq_nonneg _)
            have hsecondNonneg : 0 ≤ 12 * δ m * levelCoefficient m := by
              exact mul_nonneg (mul_nonneg (by norm_num) (hδpos m).le)
                (hlevelCoefficient m).le
            rw [← ENNReal.ofReal_add hfirstNonneg hsecondNonneg]
            exact (ENNReal.ofReal_le_iff_le_toReal (hbudgetTop m)).2 hbudgetEstimate
      rw [RandomWalk.normalizedStepPathLaw, Measure.map_apply]
      · exact hprob
      · exact RandomWalk.measurable_normalizedStepCadlagPathIcc normalization n
      · exact Skorokhod.measurableSet_admitsOscillationPartition
          (min (δ m / 32) 1) (6 * epsilon m) |>.compl
    exact hlarge
  choose cutoff hcutoff using fun m => Filter.eventually_atTop.mp (hlevelLarge m)
  choose prefixGap hprefixGap hprefix using fun m =>
    RandomWalk.exists_pos_uniform_admitsOscillationPartition_normalizedStepPath_prefix
      normalization (cutoff m)
        (mul_pos (by norm_num : (0 : ℝ) < 6) (hepsilon m))
  let gap : ℕ → ℝ := fun m => min (δ m / 32) (prefixGap m)
  let oscillationTolerance : ℕ → ℝ := fun m => 6 * epsilon m
  have hgap (m : ℕ) : 0 < gap m := by
    dsimp [gap]
    exact lt_min (div_pos (hδpos m) (by norm_num)) (hprefixGap m)
  have htolerance (m : ℕ) : 0 < oscillationTolerance m := by
    dsimp [oscillationTolerance]
    positivity
  have htendsto : Tendsto oscillationTolerance atTop (nhds 0) := by
    simpa [oscillationTolerance] using
      (tendsto_const_nhds (x := (6 : ℝ))).mul hepsilonTendsto
  have hlevel : ∀ m n : ℕ,
      (normalizedStepPathLaw ν normalization n)
        (Skorokhod.admitsOscillationPartition (E := ℝ)
          (gap m) (oscillationTolerance m))ᶜ ≤ budget m := by
    intro m n
    by_cases hn : n < cutoff m
    · have hpreimageEmpty :
          (RandomWalk.normalizedStepCadlagPathIcc normalization n) ⁻¹'
            (Skorokhod.admitsOscillationPartition (E := ℝ)
              (gap m) (oscillationTolerance m))ᶜ = ∅ := by
        ext increment
        simp only [Set.mem_preimage, Set.mem_compl_iff,
          Set.mem_empty_iff_false]
        constructor
        · intro hnot
          obtain ⟨partition, hmesh, bound, hbound, hosc⟩ :=
            hprefix m n hn increment
          apply hnot
          exact ⟨partition, lt_of_le_of_lt (min_le_right _ _) hmesh,
            bound, hbound, hosc⟩
        · intro hfalse
          exact False.elim hfalse
      rw [RandomWalk.normalizedStepPathLaw, Measure.map_apply]
      · simp [hpreimageEmpty]
      · exact RandomWalk.measurable_normalizedStepCadlagPathIcc normalization n
      · exact Skorokhod.measurableSet_admitsOscillationPartition
          (gap m) (oscillationTolerance m) |>.compl
    · have hgapLe : gap m ≤ min (δ m / 32) 1 := by
        apply le_min
        · exact le_trans (min_le_left _ _) le_rfl
        · exact le_trans (min_le_left _ _) (by nlinarith [hδsmall m])
      have hlevelInclusion :
          Skorokhod.admitsOscillationPartition (E := ℝ)
              (min (δ m / 32) 1) (6 * epsilon m) ⊆
            Skorokhod.admitsOscillationPartition (E := ℝ)
              (gap m) (oscillationTolerance m) := by
        intro path hpath
        obtain ⟨partition, hmesh, bound, hbound, hosc⟩ := hpath
        exact ⟨partition, lt_of_le_of_lt hgapLe hmesh,
          bound, hbound, hosc⟩
      have hcomplementInclusion :
          (Skorokhod.admitsOscillationPartition (E := ℝ)
            (gap m) (oscillationTolerance m))ᶜ ⊆
          (Skorokhod.admitsOscillationPartition (E := ℝ)
            (min (δ m / 32) 1) (6 * epsilon m))ᶜ := by
        intro path hnot hgood
        exact hnot (hlevelInclusion hgood)
      exact (measure_mono hcomplementInclusion).trans
        (hcutoff m n (Nat.le_of_not_gt hn))
  have hsequenceBound : ∀ n : ℕ,
      (normalizedStepPathLaw ν normalization n)
        (Skorokhod.admitsOscillationPartitionSequence
          (E := ℝ) gap oscillationTolerance)ᶜ ≤ η := by
    intro n
    calc
      _ ≤ (normalizedStepPathLaw ν normalization n)
          (⋃ m : ℕ, (Skorokhod.admitsOscillationPartition
            (E := ℝ) (gap m) (oscillationTolerance m))ᶜ) := by
        apply measure_mono
        intro path hpath
        simp only [Skorokhod.admitsOscillationPartitionSequence,
          Set.mem_iInter, Set.mem_compl_iff, not_forall] at hpath
        simp only [Set.mem_iUnion, Set.mem_compl_iff]
        exact hpath
      _ ≤ ∑' m : ℕ,
          (normalizedStepPathLaw ν normalization n)
            (Skorokhod.admitsOscillationPartition (E := ℝ)
              (gap m) (oscillationTolerance m))ᶜ := measure_iUnion_le _
      _ ≤ ∑' m : ℕ, budget m := ENNReal.tsum_le_tsum (fun m => hlevel m n)
      _ = η := hbudgetSum
  refine ⟨gap, oscillationTolerance, hgap, htolerance, htendsto,
    Filter.Eventually.of_forall hsequenceBound⟩
end ProbabilityTheory.RandomWalk.FunctionalLimit

end
