/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Brownian.Skorokhod
public import Probability.Process.Brownian.ContinuousModification
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Three-dimensional Bessel paths

The public objects and theorems in this file are:

- `BrownianBessel3.productLaw`: $P\otimes P\otimes P$ for three independent
  samples from one probability space.
- `BrownianBessel3.radius`: $R_t=\sqrt{B_t^{(1)2}+B_t^{(2)2}+B_t^{(3)2}}$.
- `BrownianBessel3.path` and `BrownianBessel3.pathLaw`: the radial path on
  $[0,1]$ and its pushforward law $P^{\otimes3}\circ R^{-1}$.
- `BrownianBessel3.pathLawOfBrownian`: the radial path law formed from the
  measurable continuous modification of a Brownian process.
- `BrownianBessel3.isProbabilityMeasure_pathLawOfBrownian`: this path law
  has total mass one.
- `BrownianBessel3.continuous_radius`, `measurable_radius`,
  `measurable_path`, and `isProbabilityMeasure_pathLaw`: continuity,
  measurability, and unit total mass of this path construction.
- `BrownianBessel3.abs_radius_sub_abs_le`: the radial map is controlled by
  $|R-|a||\le|x-a|+|y|+|z|$ for $R=\sqrt{x^2+y^2+z^2}$.

For a Brownian coordinate process, this is the radial construction of
the BES(3) process appearing in Jean-Pierre Imhof, *Density factorizations
for Brownian motion, meander and the three-dimensional Bessel process, and
applications*, Journal of Applied Probability 21 (1984), Theorem 1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BrownianBessel3

abbrev Triple (Ω : Type*) := Ω × (Ω × Ω)

/-- The product law of three independent copies of a probability law. -/
noncomputable def productLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) : Measure (Triple Ω) := P.prod (P.prod P)

noncomputable instance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (productLaw P) := by
  unfold productLaw
  infer_instance

/-- The radial process formed from three copies of a real process. -/
noncomputable def radius {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Triple Ω) : ℝ :=
  Real.sqrt ((B t ω.1) ^ 2 + (B t ω.2.1) ^ 2 + (B t ω.2.2) ^ 2)

/-- A radial path stays close to the first coordinate's target whenever
each coordinate stays close to its corresponding target. -/
theorem abs_radius_sub_abs_le (x y z a : ℝ) :
    |Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) - (|a|)| ≤
      |x - a| + |y| + |z| := by
  let r := Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)
  have hs : 0 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by positivity
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := Real.sq_sqrt hs
  have hx : |x| ≤ r := by
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg y, sq_nonneg z]
  have hu : r ≤ |x| + |y| + |z| := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [← sq_abs x, ← sq_abs y, ← sq_abs z]
      nlinarith [mul_nonneg (abs_nonneg x) (abs_nonneg y),
        mul_nonneg (abs_nonneg x) (abs_nonneg z),
        mul_nonneg (abs_nonneg y) (abs_nonneg z)]
  have hxa : |x| ≤ |a| + |x - a| := by
    calc |x| = |(x - a) + a| := by congr 1; ring
      _ ≤ |x - a| + |a| := abs_add_le _ _
      _ = |a| + |x - a| := add_comm _ _
  have hax : |a| ≤ |x| + |x - a| := by
    calc |a| = |x - (x - a)| := by congr 1; ring
      _ ≤ |x| + |a - x| := by
        simpa [sub_eq_add_neg] using abs_add_le x (-(x - a))
      _ = |x| + |x - a| := by rw [abs_sub_comm]
  apply abs_le.mpr
  constructor <;> linarith

theorem continuous_radius {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    (hB : ∀ ω, Continuous (B · ω)) (ω : Triple Ω) :
    Continuous (radius B · ω) := by
  unfold radius
  exact Real.continuous_sqrt.comp
    (((hB ω.1).pow 2).add ((hB ω.2.1).pow 2) |>.add ((hB ω.2.2).pow 2))

theorem measurable_radius {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hB : ∀ t, Measurable (B t))
    (t : ℝ≥0) : Measurable (radius B t) := by
  unfold radius
  exact Real.continuous_sqrt.measurable.comp
    ((((hB t).comp measurable_fst).pow_const 2).add
      (((hB t).comp (measurable_fst.comp measurable_snd)).pow_const 2) |>.add
      (((hB t).comp (measurable_snd.comp measurable_snd)).pow_const 2))

/-- The radial process as a unit-interval Skorokhod path. -/
noncomputable def path {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ ω, Continuous (B · ω)) :
    Triple Ω → CadlagPath unitInterval ℝ :=
  cadlagunitIntervalPath (radius B) (continuous_radius hB)

theorem measurable_path {Ω : Type*} [MeasurableSpace Ω]
    {B : ℝ≥0 → Ω → ℝ} (hB : ∀ ω, Continuous (B · ω))
    (hBmeas : ∀ t, Measurable (B t)) :
    Measurable (path B hB) :=
  measurable_cadlagunitIntervalPath (radius B)
    (continuous_radius hB) (measurable_radius hBmeas)

/-- The path law of the radial process from three independent copies. -/
noncomputable def pathLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ ω, Continuous (B · ω)) :
    Measure (CadlagPath unitInterval ℝ) :=
  (productLaw P).map (path B hB)

/-- The radial path law of three independent copies of a Brownian process,
using the measurable continuous version determined by its coordinate laws. -/
noncomputable def pathLawOfBrownian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBmeasurable : ∀ t, Measurable (B t)) :
    Measure (CadlagPath unitInterval ℝ) :=
  pathLaw P (hB.continuousModification hBmeasurable)
    (hB.continuous_continuousModification hBmeasurable)

theorem isProbabilityMeasure_pathLaw {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : ∀ ω, Continuous (B · ω))
    (hBmeas : ∀ t, Measurable (B t)) :
    IsProbabilityMeasure (pathLaw P B hB) := by
  unfold pathLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_path hB hBmeas).aemeasurable).2 inferInstance

/-- The radial path law from the measurable continuous version of a
Brownian process is a probability measure. -/
theorem isProbabilityMeasure_pathLawOfBrownian
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (hBmeasurable : ∀ t, Measurable (B t)) :
    IsProbabilityMeasure (pathLawOfBrownian hB hBmeasurable) := by
  exact isProbabilityMeasure_pathLaw P
    (hB.continuousModification hBmeasurable)
    (hB.continuous_continuousModification hBmeasurable)
    (fun t => hB.measurable_continuousModification hBmeasurable t)

end BrownianBessel3

end
