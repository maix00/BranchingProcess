import Probability.BranchingRandomWalk.Walk.Kernel.Killed.Return

/-!
# Comparison of killed return kernels

Translation of both the survival corridor and the terminal return interval
gives a comparison between return-kernel row masses.  Finite reference covers
then turn pointwise estimates in shrunken intervals into uniform estimates.
-/

open Filter MeasureTheory Set

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk

open Combinatorics.Branching.Walk

/-- A return-block row started from a nearby reference point in shrunken
outer and return intervals is bounded by the corresponding row in the
original intervals. -/
theorem returnKernel_Icc_apply_univ_mono_of_abs_sub_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (outerLower outerUpper returnLower returnUpper margin initial reference : ℝ)
    (length : ℕ) (hdistance : |initial - reference| ≤ margin)
    (hinitial : initial ∈ Set.Icc returnLower returnUpper)
    (hreference : reference ∈
      Set.Icc (returnLower + margin) (returnUpper - margin)) :
    returnKernel ν
        (Set.Icc (outerLower + margin) (outerUpper - margin)) measurableSet_Icc
        (Set.Icc (returnLower + margin) (returnUpper - margin)) measurableSet_Icc
        length ⟨reference, hreference⟩ univ ≤
      returnKernel ν
        (Set.Icc outerLower outerUpper) measurableSet_Icc
        (Set.Icc returnLower returnUpper) measurableSet_Icc
        length ⟨initial, hinitial⟩ univ := by
  rw [returnKernel_apply_univ_eq_staysIn_endsIn,
    returnKernel_apply_univ_eq_staysIn_endsIn]
  exact measure_mono fun increment h =>
    StaysIn.and_endpoint_mono_Icc_of_abs_sub_le hdistance h

/-- A finite reference cover transfers a common return-block lower bound
from shrunken outer and return intervals to every state in the original
return interval. -/
theorem le_returnKernel_Icc_apply_univ_of_finset
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (outerLower outerUpper returnLower returnUpper margin : ℝ)
    (length : ℕ) (references : Finset ℝ) (lowerBound : ENNReal)
    (hcover : ∀ x ∈ Set.Icc returnLower returnUpper,
      ∃ y ∈ references, |x - y| ≤ margin)
    (hreference : ∀ y ∈ references,
      y ∈ Set.Icc (returnLower + margin) (returnUpper - margin))
    (href : ∀ (y : ℝ) (hy : y ∈ references),
      lowerBound ≤ returnKernel ν
        (Set.Icc (outerLower + margin) (outerUpper - margin)) measurableSet_Icc
        (Set.Icc (returnLower + margin) (returnUpper - margin)) measurableSet_Icc
        length ⟨y, hreference y hy⟩ univ) :
    ∀ x : Set.Icc returnLower returnUpper,
      lowerBound ≤ returnKernel ν
        (Set.Icc outerLower outerUpper) measurableSet_Icc
        (Set.Icc returnLower returnUpper) measurableSet_Icc
        length x univ := by
  intro x
  obtain ⟨y, hy, hxy⟩ := hcover x x.property
  exact (href y hy).trans
    (returnKernel_Icc_apply_univ_mono_of_abs_sub_le
      ν outerLower outerUpper returnLower returnUpper margin x y length
      hxy x.property (hreference y hy))

/-- Eventual finite-reference return bounds transfer uniformly after a
nonnegative scaling. -/
theorem eventually_forall_le_returnKernel_Icc_apply_univ_of_finset
    {ι : Type*} {l : Filter ι}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (outerLower outerUpper returnLower returnUpper margin : ℝ)
    (references : Finset ℝ) (scale : ι → ℝ) (length : ι → ℕ)
    (lowerBound : ENNReal)
    (hscale : ∀ i, 0 ≤ scale i)
    (hcover : ∀ x ∈ Set.Icc returnLower returnUpper,
      ∃ y ∈ references, |x - y| ≤ margin)
    (hreference : ∀ y ∈ references,
      y ∈ Set.Icc (returnLower + margin) (returnUpper - margin))
    (href : ∀ (y : ℝ) (hy : y ∈ references), ∀ᶠ i in l,
      lowerBound ≤ returnKernel ν
        (Set.Icc (scale i * (outerLower + margin))
          (scale i * (outerUpper - margin))) measurableSet_Icc
        (Set.Icc (scale i * (returnLower + margin))
          (scale i * (returnUpper - margin))) measurableSet_Icc
        (length i)
        ⟨scale i * y, by
          constructor <;> nlinarith [(hreference y hy).1,
            (hreference y hy).2, hscale i]⟩ univ) :
    ∀ᶠ i in l, ∀ x : Set.Icc returnLower returnUpper,
      lowerBound ≤ returnKernel ν
        (Set.Icc (scale i * outerLower) (scale i * outerUpper)) measurableSet_Icc
        (Set.Icc (scale i * returnLower) (scale i * returnUpper)) measurableSet_Icc
        (length i)
        ⟨scale i * x, by
          constructor <;> nlinarith [x.property.1, x.property.2, hscale i]⟩ univ := by
  let P : ℝ → ι → Prop := fun y i => ∀ hy : y ∈ references,
    lowerBound ≤ returnKernel ν
      (Set.Icc (scale i * (outerLower + margin))
        (scale i * (outerUpper - margin))) measurableSet_Icc
      (Set.Icc (scale i * (returnLower + margin))
        (scale i * (returnUpper - margin))) measurableSet_Icc
      (length i)
      ⟨scale i * y, by
        constructor <;> nlinarith [(hreference y hy).1,
          (hreference y hy).2, hscale i]⟩ univ
  have hrefEventually : ∀ᶠ i in l, ∀ y ∈ references, P y i := by
    apply references.eventually_all.2
    intro y hy
    filter_upwards [href y hy] with i hi
    intro hy'
    simpa only [P] using hi
  filter_upwards [hrefEventually] with i hi
  intro x
  obtain ⟨y, hy, hxy⟩ := hcover x x.property
  have hscaledDistance :
      |scale i * x - scale i * y| ≤ scale i * margin := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (hscale i)]
    exact mul_le_mul_of_nonneg_left hxy (hscale i)
  refine (hi y hy hy).trans ?_
  rw [returnKernel_apply_univ_eq_staysIn_endsIn,
    returnKernel_apply_univ_eq_staysIn_endsIn]
  apply measure_mono
  intro increment hpath
  apply StaysIn.and_endpoint_mono_Icc_of_abs_sub_le hscaledDistance
  change StaysIn
      (Set.Icc (scale i * (outerLower + margin))
        (scale i * (outerUpper - margin)))
      (length i) (scale i * y) increment ∧
    scale i * y + partialSum (length i) increment ∈
      Set.Icc (scale i * (returnLower + margin))
        (scale i * (returnUpper - margin)) at hpath
  simpa only [mul_add, mul_sub] using hpath

/-- Finite strict `liminf` gaps for shrunken return blocks yield an eventual
one-block bound uniform over the full return interval. -/
theorem eventually_forall_le_returnKernel_Icc_apply_univ_of_finset_liminf
    {ι : Type*} {l : Filter ι}
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (outerLower outerUpper returnLower returnUpper margin : ℝ)
    (references : Finset ℝ) (scale : ι → ℝ) (length : ι → ℕ)
    (lowerBound error : ENNReal) (referenceBound : ℝ → ENNReal)
    (herror : error ≠ ⊤) (hscale : ∀ i, 0 ≤ scale i)
    (hcover : ∀ x ∈ Set.Icc returnLower returnUpper,
      ∃ y ∈ references, |x - y| ≤ margin)
    (hreference : ∀ y ∈ references,
      y ∈ Set.Icc (returnLower + margin) (returnUpper - margin))
    (hliminf : ∀ (y : ℝ) (hy : y ∈ references),
      referenceBound y ≤ l.liminf (fun i =>
        returnKernel ν
          (Set.Icc (scale i * (outerLower + margin))
            (scale i * (outerUpper - margin))) measurableSet_Icc
          (Set.Icc (scale i * (returnLower + margin))
            (scale i * (returnUpper - margin))) measurableSet_Icc
          (length i)
          ⟨scale i * y, by
            constructor <;> nlinarith [(hreference y hy).1,
              (hreference y hy).2, hscale i]⟩ univ + error))
    (hgap : ∀ y ∈ references,
      lowerBound + error < referenceBound y) :
    ∀ᶠ i in l, ∀ x : Set.Icc returnLower returnUpper,
      lowerBound ≤ returnKernel ν
        (Set.Icc (scale i * outerLower) (scale i * outerUpper)) measurableSet_Icc
        (Set.Icc (scale i * returnLower) (scale i * returnUpper)) measurableSet_Icc
        (length i)
        ⟨scale i * x, by
          constructor <;> nlinarith [x.property.1, x.property.2, hscale i]⟩ univ := by
  have href : ∀ (y : ℝ) (hy : y ∈ references), ∀ᶠ i in l,
      lowerBound ≤ returnKernel ν
        (Set.Icc (scale i * (outerLower + margin))
          (scale i * (outerUpper - margin))) measurableSet_Icc
        (Set.Icc (scale i * (returnLower + margin))
          (scale i * (returnUpper - margin))) measurableSet_Icc
        (length i)
        ⟨scale i * y, by
          constructor <;> nlinarith [(hreference y hy).1,
            (hreference y hy).2, hscale i]⟩ univ := by
    intro y hy
    have hstrict : lowerBound + error < l.liminf (fun i =>
        returnKernel ν
          (Set.Icc (scale i * (outerLower + margin))
            (scale i * (outerUpper - margin))) measurableSet_Icc
          (Set.Icc (scale i * (returnLower + margin))
            (scale i * (returnUpper - margin))) measurableSet_Icc
          (length i)
          ⟨scale i * y, by
            constructor <;> nlinarith [(hreference y hy).1,
              (hreference y hy).2, hscale i]⟩ univ + error) :=
      (hgap y hy).trans_le (hliminf y hy)
    filter_upwards [eventually_lt_of_lt_liminf hstrict] with i hi
    exact ((ENNReal.add_lt_add_iff_right herror).1 hi).le
  exact eventually_forall_le_returnKernel_Icc_apply_univ_of_finset
    ν outerLower outerUpper returnLower returnUpper margin references
    scale length lowerBound hscale hcover hreference href

end ProbabilityTheory.BranchingRandomWalk.RandomWalk
