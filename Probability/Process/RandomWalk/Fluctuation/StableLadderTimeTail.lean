/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.DescendingLocalTime
public import Probability.Distributions.Stable.Attraction.NormingRatios.PositiveTail

/-!
# The first descending ladder-time law and its tail

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.firstDescendingLadderTimeValue`:
  the real value of $T^-_1$, with the exceptional value $\infty$ sent to zero.
- `ProbabilityTheory.RandomWalk.firstDescendingLadderTimeLaw`:
  the law of this real value under a measure on increment paths.
- `ProbabilityTheory.RandomWalk.firstDescendingLadderTimeLaw_isProbabilityMeasure`:
  a probability law on paths gives a probability law for $T^-_1$.
- `ProbabilityTheory.RandomWalk.firstDescendingLadderTimeLaw_Iio_zero`:
  this law assigns zero mass to $(-\infty,0)$.
- `ProbabilityTheory.RandomWalk.firstDescendingLadderTimeTailReal_eq_law_tail`:
  if $T^-_1<\infty$ almost surely, then for $x\ge0$,
  $\mathbb P(T^-_1>\lfloor x\rfloor)=\mathbb P(T^-_1>x)$.
- `ProbabilityTheory.RandomWalk.firstDescendingLadderTimeTailReal_regularVariation_of_stableAttraction`:
  a positive $\alpha$-stable attraction law for $T^-_1$ gives regular
  variation of its tail with index $-\alpha$.

This is the distributional-to-tail step cited in Francesco Caravenna and
Loïc Chaumont, *Invariance principles for random walks conditioned to stay
positive*, Lemma 2.1, equation (2.3), DOI 10.1214/07-AIHP119. The
stable-attraction premise there comes from the ladder-variable results of
Doney--Greenwood, Doney, and Greenwood--Omey--Teugels cited in its proof.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

/-- A real-valued version of the first strict descending ladder time.
The value on paths with infinite first ladder time is fixed to zero; the
tail theorem below assumes those paths have measure zero. -/
noncomputable def firstDescendingLadderTimeValue
    (increment : ℕ → ℝ) : ℝ :=
  (((strictDescendingLadderTime increment 1).untopD 0 : ℕ) : ℝ)

/-- The real-valued first ladder time is measurable. -/
theorem measurable_firstDescendingLadderTimeValue :
    Measurable firstDescendingLadderTimeValue := by
  unfold firstDescendingLadderTimeValue
  exact (MeasurableEmbedding.natCast (α := ℝ)).measurable.comp
    ((strictDescendingLadderTime_measurable 1).untopD 0)

/-- Distribution of the first strict descending ladder time. -/
noncomputable def firstDescendingLadderTimeLaw
    (μ : Measure (ℕ → ℝ)) : Measure ℝ :=
  μ.map firstDescendingLadderTimeValue

/-- The measurable ladder-time map preserves probability mass. -/
instance firstDescendingLadderTimeLaw_isProbabilityMeasure
    (μ : Measure (ℕ → ℝ)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (firstDescendingLadderTimeLaw μ) := by
  unfold firstDescendingLadderTimeLaw
  infer_instance

/-- A ladder time takes nonnegative integer values whenever it is finite. -/
theorem firstDescendingLadderTimeLaw_Iio_zero
    (μ : Measure (ℕ → ℝ)) :
    firstDescendingLadderTimeLaw μ (Set.Iio 0) = 0 := by
  rw [firstDescendingLadderTimeLaw,
    Measure.map_apply measurable_firstDescendingLadderTimeValue measurableSet_Iio]
  have hempty : firstDescendingLadderTimeValue ⁻¹' Set.Iio (0 : ℝ) = ∅ := by
    ext increment
    simp [firstDescendingLadderTimeValue]
  rw [hempty]
  exact measure_empty

/-- On the almost-surely finite part of the ladder time, the real upper
tail agrees with the integer-horizon ladder-time tail. -/
theorem firstDescendingLadderTimeTailReal_eq_law_tail
    (μ : Measure (ℕ → ℝ))
    (hfinite : μ {increment |
      strictDescendingLadderTime increment 1 = ⊤} = 0)
    {x : ℝ} (hx : 0 ≤ x) :
    firstDescendingLadderTimeTailReal μ x =
      (firstDescendingLadderTimeLaw μ).real (Set.Ioi x) := by
  unfold firstDescendingLadderTimeTailReal firstDescendingLadderTimeLaw
  change (μ {increment | (Nat.floor x : WithTop ℕ) <
    strictDescendingLadderTime increment 1}).toReal =
    ((μ.map firstDescendingLadderTimeValue) (Set.Ioi x)).toReal
  rw [Measure.map_apply measurable_firstDescendingLadderTimeValue measurableSet_Ioi]
  apply congrArg ENNReal.toReal
  apply measure_congr
  have hae : ∀ᵐ increment ∂μ,
      strictDescendingLadderTime increment 1 ≠ ⊤ := by
    rw [ae_iff]
    simpa only [not_not] using hfinite
  filter_upwards [hae] with increment htime
  cases ht : strictDescendingLadderTime increment 1 with
  | top => exact False.elim (htime ht)
  | coe n =>
    simp only [Set.mem_preimage, Set.mem_Ioi]
    simp only [firstDescendingLadderTimeValue, ht, WithTop.untopD_coe]
    apply propext
    constructor
    · intro h
      exact (Nat.floor_lt hx).1 (WithTop.coe_lt_coe.mp h)
    · intro h
      exact WithTop.coe_lt_coe.mpr ((Nat.floor_lt hx).2 h)

/-- Stable attraction of the finite, nonnegative first ladder-time law
implies the regular variation of its survival tail. This is the final
tail step of Caravenna--Chaumont, Lemma 2.1. -/
theorem firstDescendingLadderTimeTailReal_regularVariation_of_stableAttraction
    {μ : Measure (ℕ → ℝ)} [IsProbabilityMeasure μ]
    (hfinite : μ {increment |
      strictDescendingLadderTime increment 1 = ⊤} = 0)
    {α : ℝ} {limit : Measure ℝ}
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong
      (firstDescendingLadderTimeLaw μ) limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Asymptotics.IsRegularlyVaryingAtTop
      (firstDescendingLadderTimeTailReal μ) (-α) := by
  have hright := h.isRegularlyVarying_rightTail_of_nonneg
    hlimit hα₀ hα₂ (firstDescendingLadderTimeLaw_Iio_zero μ)
  apply hright.congr
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact (firstDescendingLadderTimeTailReal_eq_law_tail μ hfinite hx).symm

end ProbabilityTheory.RandomWalk

end
