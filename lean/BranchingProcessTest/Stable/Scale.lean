import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.Partition
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Stable.TruncatedMoment

open Filter MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk
open scoped Topology

example {α : ℝ} {ν : Measure ℝ} {τ K : ℝ} {a : ℕ → ℝ}
    (hα : 0 < α) (hτ : 0 < τ) (hK : 0 < K)
    (ha : Tendsto a atTop atTop)
    (hL : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (a n) ∧ stableSlowVariation α ν (a n) ≤ K)
    (hrate : Tendsto (stableSmallDeviationRate α ν a) atTop (nhds 0)) :
    Tendsto
      (fun n => stableScaleTime α ν (a n) / (n : ℝ) *
        (stableBlockCount α ν τ a n : ℝ))
      atTop (nhds τ⁻¹) :=
  tendsto_stableScaleTime_div_nat_mul_stableBlockCount
    hα hτ hK ha hL hrate

#print axioms ProbabilityTheory.RandomWalk.tendsto_stableBlockLength_div_stableScaleTime
#print axioms ProbabilityTheory.RandomWalk.tendsto_stableScaleTime_div_nat_mul_stableBlockCount

example {α : ℝ} {ν : Measure ℝ}
    (hL : Asymptotics.IsSlowlyVaryingAtTop
      (stableSlowVariation α ν)) :
    Asymptotics.IsRegularlyVaryingAtTop (stableScaleTime α ν) α :=
  stableScaleTime_isRegularlyVaryingAtTop hL

#print axioms Asymptotics.IsRegularlyVaryingAtTop.mul
#print axioms Asymptotics.IsRegularlyVaryingAtTop.inv
#print axioms Asymptotics.IsRegularlyVaryingAtTop.exists_potter_upper_bound
#print axioms Asymptotics.isRegularlyVaryingAtTop_rpow_div_of_slowlyVarying
#print axioms ProbabilityTheory.stableScaleTime_isRegularlyVaryingAtTop

example {ρ ε : ℝ} (hρ : 0 ≤ ρ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ ⦃x y : ℝ⦄, R ≤ x → x ≤ y →
      y ^ ρ / x ^ ρ ≤ 2 ^ (ρ + ε) * (y / x) ^ (ρ + ε) := by
  apply Asymptotics.IsRegularlyVaryingAtTop.exists_potter_upper_bound
      (Asymptotics.IsRegularlyVaryingAtTop.rpow ρ)
  · exact ⟨0, fun _ _ hx hxy => Real.rpow_le_rpow hx hxy hρ⟩
  · exact hρ
  · exact hε

example {α : ℝ} {ν : Measure ℝ} {b a : ℕ → ℝ} {τ ell : ℝ}
    (hα : 0 < α) (hτ : 0 < τ) (hell : 0 < ell)
    (ha : Tendsto a atTop atTop)
    (hL : Tendsto (stableSlowVariation α ν) atTop (nhds ell))
    (hb : IsStableNorming α ν b) :
    Tendsto (fun n => b (stableBlockLength α ν τ a n) / a n)
      atTop (nhds (τ ^ (1 / α))) :=
  tendsto_stableBlockNorming_div_scale_of_slowVariation_limit
    hα hτ hell ha hL hb

#print axioms
  ProbabilityTheory.RandomWalk.tendsto_stableBlockNorming_div_scale_of_slowVariation_limit

example {α ell : ℝ} {ν : Measure ℝ} {b a : ℕ → ℝ}
    (hα : 0 < α) (hell : 0 < ell)
    (hscale : IsStableMogulskiiScale α ν b a)
    (hL : Tendsto (stableSlowVariation α ν) atTop (nhds ell)) :
    Tendsto (stableSmallDeviationRate α ν a) atTop (nhds 0) :=
  IsStableMogulskiiScale.tendsto_stableSmallDeviationRate_zero_of_slowVariation_limit
    hα hell hscale hL

example {α ell : ℝ} {ν : Measure ℝ} {b a : ℕ → ℝ} {τ : ℝ}
    (hα : 0 < α) (hτ : 0 < τ) (hell : 0 < ell)
    (hscale : IsStableMogulskiiScale α ν b a)
    (hL : Tendsto (stableSlowVariation α ν) atTop (nhds ell)) :
    Tendsto (fun n => stableScaleTime α ν (a n) / (n : ℝ) *
      (stableBlockCount α ν τ a n : ℝ)) atTop (nhds τ⁻¹) :=
  tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation_limit
    hα hτ hell hscale hL

#print axioms
  ProbabilityTheory.RandomWalk.IsStableMogulskiiScale.tendsto_stableSmallDeviationRate_zero_of_slowVariation_limit
#print axioms
  ProbabilityTheory.RandomWalk.tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation_limit

example (ν : Measure ℝ) [IsProbabilityMeasure ν] {α A B : ℝ}
    (hA : Tendsto
      (fun u : ℝ => u ^ (α - 2) * truncatedSquareTailIntegral ν u)
      atTop (nhds A))
    (hB : Tendsto
      (fun u : ℝ => u ^ α * ν.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (stableSlowVariation α ν) atTop (nhds (A - B)) :=
  tendsto_stableSlowVariation_of_layercake_and_tail ν hA hB

#print axioms ProbabilityTheory.tendsto_stableSlowVariation_of_layercake_and_tail


example (ν : Measure ℝ) [IsProbabilityMeasure ν] {α B : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2) (hB : 0 < B)
    (hTail : Tendsto
      (fun u : ℝ => u ^ α * ν.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (fun u : ℝ => u ^ (α - 2) * truncatedSecondMoment ν u) atTop
      (nhds (α * B / (2 - α))) :=
  tendsto_truncatedSecondMoment_scale_of_twoSidedTail ν hα₀ hα₂ hB hTail

example (ν : Measure ℝ) [IsProbabilityMeasure ν] {α B : ℝ}
    (hα₀ : 0 < α) (hα₂ : α < 2) (hB : 0 < B)
    (hTail : Tendsto
      (fun u : ℝ => u ^ α * ν.real {x : ℝ | u < |x|})
      atTop (nhds B)) :
    Tendsto (stableSlowVariation α ν) atTop (nhds (α * B / (2 - α))) :=
  tendsto_stableSlowVariation_of_twoSidedTail ν hα₀ hα₂ hB hTail

#print axioms ProbabilityTheory.tendsto_truncatedSecondMoment_scale_of_layercake_and_tail
#print axioms ProbabilityTheory.tendsto_truncatedSecondMoment_scale_of_twoSidedTail
#print axioms ProbabilityTheory.tendsto_stableSlowVariation_of_twoSidedTail
#print axioms Asymptotics.tendsto_rpow_mul_intervalIntegral_of_tendsto_rpow_mul

example {blockLength : ℕ → ℕ}
    (hpos : ∀ᶠ n in atTop, 0 < blockLength n)
    (hscale : Tendsto (fun n => (blockLength n : ℝ) / n)
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        ((Asymptotics.blockCount blockLength n * blockLength n : ℕ) : ℝ) / n)
      atTop (nhds 1) :=
  Asymptotics.tendsto_blockCount_mul_blockLength_div_nat hpos hscale

#print axioms Asymptotics.tendsto_blockCount_mul_blockLength_div_nat
