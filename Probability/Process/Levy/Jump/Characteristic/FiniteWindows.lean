import Probability.Process.Levy.Jump.Characteristic.TimeMark

/-!
# Characteristic functions of finite weighted collections of windows

The characteristic formula for one Poisson integral applies directly to a
finite linear combination of time-window integrals. This is the scalar
characteristic-function input for finite-dimensional jump-process laws.
-/

namespace ProbabilityTheory

open MeasureTheory Complex

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The mark integrand for a finite weighted collection of time windows. -/
def finiteWindowIntegrand {ι : Type*} [Fintype ι]
    (S : ι → Set unitInterval) (u : ι → ℝ) : unitInterval × ℝ → ℝ :=
  fun z => ∑ i, if z.1 ∈ S i then u i * z.2 else 0

/-- The corresponding finite linear combination of window jump integrals. -/
def finiteWindowIntegral {ι : Type*} [Fintype ι]
    (S : ι → Set unitInterval) (u : ι → ℝ)
    (N : Measure (unitInterval × ℝ)) : ℝ :=
  ∑ i, u i * (∫ z, (if z.1 ∈ S i then z.2 else 0 : ℝ) ∂N)

/-- Pairwise disjoint windows make the integrand select at most one
coefficient at each time. -/
theorem finiteWindowIntegrand_eq_single_of_mem
    {ι : Type*} [Fintype ι]
    (S : ι → Set unitInterval) (u : ι → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    {i : ι} {z : unitInterval × ℝ} (hz : z.1 ∈ S i) :
    finiteWindowIntegrand S u z = u i * z.2 := by
  classical
  unfold finiteWindowIntegrand
  rw [Finset.sum_eq_single i]
  · simp [hz]
  · intro j hj hji
    have hnot : z.1 ∉ S j := by
      intro hzj
      exact (Set.disjoint_left.mp (hdisj j i hji) hzj hz).elim
    simp [hnot]
  · simp

/-- If a time belongs to no window, the combined integrand vanishes. -/
theorem finiteWindowIntegrand_eq_zero_of_not_mem
    {ι : Type*} [Fintype ι]
    (S : ι → Set unitInterval) (u : ι → ℝ)
    {z : unitInterval × ℝ} (hz : ∀ i, z.1 ∉ S i) :
    finiteWindowIntegrand S u z = 0 := by
  classical
  unfold finiteWindowIntegrand
  apply Finset.sum_eq_zero
  intro i hi
  simp [hz i]

/-- On pairwise disjoint windows, the exponential jump integrand splits
pointwise into the sum of the individual window exponents. -/
theorem exp_finiteWindowIntegrand_sub_one_eq_sum
    {ι : Type*} [Fintype ι]
    (S : ι → Set unitInterval) (u : ι → ℝ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (ξ : ℝ) (z : unitInterval × ℝ) :
    Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1 =
      ∑ i, if z.1 ∈ S i then levyUncompensatedIntegrand (ξ * u i) z.2 else 0 := by
  classical
  by_cases hmem : ∃ i, z.1 ∈ S i
  · obtain ⟨i, hi⟩ := hmem
    have hf := finiteWindowIntegrand_eq_single_of_mem S u hdisj hi
    have hsum : (∑ j, if z.1 ∈ S j then
        levyUncompensatedIntegrand (ξ * u j) z.2 else 0) =
        levyUncompensatedIntegrand (ξ * u i) z.2 := by
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j hj hji
        have hnot : z.1 ∉ S j := by
          intro hzj
          exact (Set.disjoint_left.mp (hdisj j i hji) hzj hi).elim
        simp [hnot]
      · simp
    rw [hf, hsum]
    simp only [levyUncompensatedIntegrand]
    congr 1
    congr 1
    push_cast
    ring
  · have hnone : ∀ i, z.1 ∉ S i := fun i hi => hmem ⟨i, hi⟩
    rw [finiteWindowIntegrand_eq_zero_of_not_mem S u hnone]
    simp only [levyUncompensatedIntegrand]
    simp [show ∀ i, z.1 ∉ S i from hnone]

/-- Integrating the disjoint-window exponent over product intensity separates
it into the sum of the window lengths times their mark exponents. -/
theorem integral_exp_finiteWindowIntegrand_prod
    {ι : Type*} [Fintype ι]
    (ν : Measure ℝ) [SigmaFinite ν]
    (S : ι → Set unitInterval) (u : ι → ℝ)
    (hS : ∀ i, MeasurableSet (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (ξ : ℝ)
    (hmark : ∀ i, Integrable (levyUncompensatedIntegrand (ξ * u i)) ν) :
    (∫ z : unitInterval × ℝ,
      (Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1)
      ∂((volume : Measure unitInterval).prod ν)) =
      ∑ i, ((volume : Measure unitInterval) (S i)).toReal •
        (∫ x, levyUncompensatedIntegrand (ξ * u i) x ∂ν) := by
  classical
  let g : ι → unitInterval × ℝ → ℂ := fun i z =>
    if z.1 ∈ S i then levyUncompensatedIntegrand (ξ * u i) z.2 else 0
  have hpoint (z : unitInterval × ℝ) :
      Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1 =
        ∑ i ∈ Finset.univ, g i z := by
    rw [exp_finiteWindowIntegrand_sub_one_eq_sum S u hdisj ξ z]
  have hgi (i : ι) : Integrable (g i)
      ((volume : Measure unitInterval).prod ν) := by
    have hg : Integrable (fun z : unitInterval × ℝ =>
        levyUncompensatedIntegrand (ξ * u i) z.2)
        ((volume : Measure unitInterval).prod ν) :=
      (hmark i).comp_snd _
    have hset : MeasurableSet (S i ×ˢ Set.univ : Set (unitInterval × ℝ)) :=
      (hS i).prod MeasurableSet.univ
    have heq : g i = (S i ×ˢ Set.univ).indicator
        (fun z : unitInterval × ℝ => levyUncompensatedIntegrand (ξ * u i) z.2) := by
      funext z
      by_cases hz : z.1 ∈ S i <;> simp [g, hz]
    rw [heq]
    exact hg.indicator hset
  have hsum : Integrable (fun z : unitInterval × ℝ => ∑ i ∈ Finset.univ, g i z)
      ((volume : Measure unitInterval).prod ν) :=
    integrable_finsetSum Finset.univ fun i hi => hgi i
  rw [show (fun z : unitInterval × ℝ =>
      Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1) =
      fun z => ∑ i ∈ Finset.univ, g i z by funext z; exact hpoint z]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [show g i = (S i ×ˢ Set.univ).indicator
        (fun z : unitInterval × ℝ => levyUncompensatedIntegrand (ξ * u i) z.2) by
      funext z
      by_cases hz : z.1 ∈ S i <;> simp [g, hz]]
    rw [integral_indicator ((hS i).prod MeasurableSet.univ)]
    exact integral_timeWindow_prod_mark ν (S i) (hS i)
      (levyUncompensatedIntegrand (ξ * u i)) (hmark i)
  · intro i hi
    exact hgi i

/-- Integrability of the product-intensity exponential follows from the
finite disjoint-window decomposition and integrability of each mark exponent. -/
theorem integrable_exp_finiteWindowIntegrand_prod
    {ι : Type*} [Fintype ι]
    (ν : Measure ℝ) [SigmaFinite ν]
    (S : ι → Set unitInterval) (u : ι → ℝ)
    (hS : ∀ i, MeasurableSet (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (ξ : ℝ)
    (hmark : ∀ i, Integrable (levyUncompensatedIntegrand (ξ * u i)) ν) :
    Integrable
      (fun z : unitInterval × ℝ =>
        Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1)
      ((volume : Measure unitInterval).prod ν) := by
  classical
  let g : ι → unitInterval × ℝ → ℂ := fun i z =>
    if z.1 ∈ S i then levyUncompensatedIntegrand (ξ * u i) z.2 else 0
  have hgi (i : ι) : Integrable (g i)
      ((volume : Measure unitInterval).prod ν) := by
    have hg : Integrable (fun z : unitInterval × ℝ =>
        levyUncompensatedIntegrand (ξ * u i) z.2)
        ((volume : Measure unitInterval).prod ν) := (hmark i).comp_snd _
    have hset : MeasurableSet (S i ×ˢ Set.univ : Set (unitInterval × ℝ)) :=
      (hS i).prod MeasurableSet.univ
    have heq : g i = (S i ×ˢ Set.univ).indicator
        (fun z : unitInterval × ℝ => levyUncompensatedIntegrand (ξ * u i) z.2) := by
      funext z
      by_cases hz : z.1 ∈ S i <;> simp [g, hz]
    rw [heq]
    exact hg.indicator hset
  have heq : (fun z : unitInterval × ℝ =>
      Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1) =
      fun z => ∑ i ∈ Finset.univ, g i z := by
    funext z
    rw [exp_finiteWindowIntegrand_sub_one_eq_sum S u hdisj ξ z]
  rw [heq]
  exact integrable_finsetSum Finset.univ fun i hi => hgi i

/-- For a finite-variation Lévy measure, the cutoff small and large
time-space intensities together give the joint-window exponent of the full
Lévy measure. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integral_exp_finiteWindowIntegrand_cutoff_add
    {ι : Type*} [Fintype ι]
    {ν : Measure ℝ} [SigmaFinite ν] (hν : MeasureTheory.IsLevyMeasure ν)
    (hsmall : Integrable smallJumpDisplacement ν)
    (n : ℕ)
    (S : ι → Set unitInterval) (u : ι → ℝ)
    (hS : ∀ i, MeasurableSet (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (ξ : ℝ) :
    (∫ z : unitInterval × ℝ,
      (Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1)
      ∂((volume : Measure unitInterval).prod
        (ν.restrict (smallJumpBand n)))) +
    (∫ z : unitInterval × ℝ,
      (Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1)
      ∂((volume : Measure unitInterval).prod
        (ν.restrict (largeJumpBand n)))) =
      ∑ i, ((volume : Measure unitInterval) (S i)).toReal •
        (∫ x, levyUncompensatedIntegrand (ξ * u i) x ∂ν) := by
  have hsmallMark (i : ι) : Integrable
      (levyUncompensatedIntegrand (ξ * u i))
      (ν.restrict (smallJumpBand n)) :=
    (hν.integrable_uncompensatedIntegrand hsmall (ξ * u i)).mono_measure
      Measure.restrict_le_self
  have hlargeMark (i : ι) : Integrable
      (levyUncompensatedIntegrand (ξ * u i))
      (ν.restrict (largeJumpBand n)) :=
    (hν.integrable_uncompensatedIntegrand hsmall (ξ * u i)).mono_measure
      Measure.restrict_le_self
  rw [integral_exp_finiteWindowIntegrand_prod (ν.restrict (smallJumpBand n))
      S u hS hdisj ξ hsmallMark,
    integral_exp_finiteWindowIntegrand_prod (ν.restrict (largeJumpBand n))
      S u hS hdisj ξ hlargeMark]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    ((volume : Measure unitInterval) (S i)).toReal •
        (∫ x, levyUncompensatedIntegrand (ξ * u i) x
          ∂(ν.restrict (smallJumpBand n))) +
      ((volume : Measure unitInterval) (S i)).toReal •
        (∫ x, levyUncompensatedIntegrand (ξ * u i) x
          ∂(ν.restrict (largeJumpBand n))) =
        ((volume : Measure unitInterval) (S i)).toReal •
          ((∫ x, levyUncompensatedIntegrand (ξ * u i) x
            ∂(ν.restrict (smallJumpBand n))) +
           (∫ x, levyUncompensatedIntegrand (ξ * u i) x
            ∂(ν.restrict (largeJumpBand n)))) := by rw [smul_add]
    _ = ((volume : Measure unitInterval) (S i)).toReal •
        (∫ x, levyUncompensatedIntegrand (ξ * u i) x ∂ν) := by
      rw [hν.integral_smallJumpBand_add_largeJumpBand n
        (hν.integrable_uncompensatedIntegrand hsmall (ξ * u i))]

/-- The finite-dimensional characteristic function of a cutoff jump-sum
process is the product of its interval exponents, expressed as one finite
sum in the exponent. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integral_exp_finiteWindow_sum_cutoff_poissonRandomMeasures
    {ι : Type*} [Fintype ι]
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ν : Measure ℝ} [SigmaFinite ν] (hν : MeasureTheory.IsLevyMeasure ν)
    (hsmall : Integrable smallJumpDisplacement ν)
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod
        (ν.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod
        (ν.restrict (largeJumpBand n))) Pb)
    (S : ι → Set unitInterval) (u : ι → ℝ)
    (hS : ∀ i, MeasurableSet (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (ξ : ℝ)
    (hsreal : ∀ᵐ ω ∂Ps, Integrable (finiteWindowIntegrand S u)
      (poissonRandomMeasure Ks Xs ω))
    (hbreal : ∀ᵐ ω ∂Pb, Integrable (finiteWindowIntegrand S u)
      (poissonRandomMeasure Kb Xb ω)) :
    (∫ ω : Ωs × Ωb, Complex.exp
      (((ξ * ((∫ z, finiteWindowIntegrand S u z
          ∂(poissonRandomMeasure Ks Xs ω.1)) +
        (∫ z, finiteWindowIntegrand S u z
          ∂(poissonRandomMeasure Kb Xb ω.2))) : ℝ) : ℂ) *
        Complex.I) ∂(Ps.prod Pb)) =
      Complex.exp (∑ i, ((volume : Measure unitInterval) (S i)).toReal •
        (∫ x, levyUncompensatedIntegrand (ξ * u i) x ∂ν)) := by
  let νs : Measure ℝ := ν.restrict (smallJumpBand n)
  let νb : Measure ℝ := ν.restrict (largeJumpBand n)
  have hmarkS (i : ι) : Integrable (levyUncompensatedIntegrand (ξ * u i)) νs :=
    (hν.integrable_uncompensatedIntegrand hsmall (ξ * u i)).mono_measure
      Measure.restrict_le_self
  have hmarkB (i : ι) : Integrable (levyUncompensatedIntegrand (ξ * u i)) νb :=
    (hν.integrable_uncompensatedIntegrand hsmall (ξ * u i)).mono_measure
      Measure.restrict_le_self
  have hmeas : Measurable (finiteWindowIntegrand S u) := by
    classical
    unfold finiteWindowIntegrand
    apply Finset.measurable_sum
    intro i hi
    exact Measurable.ite ((hS i).preimage measurable_fst)
      (measurable_const.mul measurable_snd) measurable_const
  have hsint : Integrable
      (fun z : unitInterval × ℝ =>
        Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1)
      ((volume : Measure unitInterval).prod νs) := by
    exact integrable_exp_finiteWindowIntegrand_prod νs S u hS hdisj ξ hmarkS
  have hbint : Integrable
      (fun z : unitInterval × ℝ =>
        Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1)
      ((volume : Measure unitInterval).prod νb) := by
    exact integrable_exp_finiteWindowIntegrand_prod νb S u hS hdisj ξ hmarkB
  have hformula := integral_exp_sum_independent_poissonRandomMeasures
    hds hdb hmeas hmeas ξ hsreal hbreal hsint hbint
  calc
    _ = Complex.exp
        ((∫ z, (Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) *
            Complex.I) - 1) ∂((volume : Measure unitInterval).prod νs)) +
         (∫ z, (Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) *
            Complex.I) - 1) ∂((volume : Measure unitInterval).prod νb))) := hformula
    _ = Complex.exp (∑ i, ((volume : Measure unitInterval) (S i)).toReal •
          (∫ x, levyUncompensatedIntegrand (ξ * u i) x ∂ν)) := by
      rw [hν.integral_exp_finiteWindowIntegrand_cutoff_add hsmall n S u hS
        hdisj ξ]

/-- Integrating the weighted window integrand is the same as summing the
individual window integrals. -/
theorem integral_finiteWindowIntegrand
    {ι : Type*} [Fintype ι]
    (S : ι → Set unitInterval) (u : ι → ℝ)
    (N : Measure (unitInterval × ℝ))
    (hS : ∀ i, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0) N) :
    (∫ z, finiteWindowIntegrand S u z ∂N) = finiteWindowIntegral S u N := by
  classical
  rw [finiteWindowIntegral]
  rw [show (fun z : unitInterval × ℝ => finiteWindowIntegrand S u z) =
      fun z => ∑ i ∈ Finset.univ, u i •
        (if z.1 ∈ S i then z.2 else 0) by
        funext z
        simp [finiteWindowIntegrand, mul_ite]]
  rw [integral_finsetSum]
  · simp_rw [integral_smul]
    rfl
  · intro i hi
    exact (hS i).const_mul (u i)


/-- The preceding characteristic formula is exactly the joint formula for
the finite collection of window integrals, rather than only for their
combined integrand. -/
theorem _root_.MeasureTheory.IsLevyMeasure.integral_exp_finiteWindowIntegrals_cutoff_poissonRandomMeasures
    {ι : Type*} [Fintype ι]
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ν : Measure ℝ} [SigmaFinite ν] (hν : MeasureTheory.IsLevyMeasure ν)
    (hsmall : Integrable smallJumpDisplacement ν)
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (n : ℕ)
    (hds : IsPoissonPointFamily Ks Xs
      ((volume : Measure unitInterval).prod
        (ν.restrict (smallJumpBand n))) Ps)
    (hdb : IsPoissonPointFamily Kb Xb
      ((volume : Measure unitInterval).prod
        (ν.restrict (largeJumpBand n))) Pb)
    (S : ι → Set unitInterval) (u : ι → ℝ)
    (hS : ∀ i, MeasurableSet (S i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (ξ : ℝ)
    (hsi : ∀ i, ∀ᵐ ω ∂Ps, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
      (poissonRandomMeasure Ks Xs ω))
    (hbi : ∀ i, ∀ᵐ ω ∂Pb, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
      (poissonRandomMeasure Kb Xb ω)) :
    (∫ ω : Ωs × Ωb, Complex.exp
      (((ξ * (finiteWindowIntegral S u (poissonRandomMeasure Ks Xs ω.1) +
        finiteWindowIntegral S u (poissonRandomMeasure Kb Xb ω.2)) : ℝ) : ℂ) *
        Complex.I) ∂(Ps.prod Pb)) =
      Complex.exp (∑ i, ((volume : Measure unitInterval) (S i)).toReal •
        (∫ x, levyUncompensatedIntegrand (ξ * u i) x ∂ν)) := by
  have hsiAll : ∀ᵐ ω ∂Ps, ∀ i, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
      (poissonRandomMeasure Ks Xs ω) := ae_all_iff.2 hsi
  have hbiAll : ∀ᵐ ω ∂Pb, ∀ i, Integrable
      (fun z : unitInterval × ℝ => if z.1 ∈ S i then z.2 else 0)
      (poissonRandomMeasure Kb Xb ω) := ae_all_iff.2 hbi
  have hsreal : ∀ᵐ ω ∂Ps, Integrable (finiteWindowIntegrand S u)
      (poissonRandomMeasure Ks Xs ω) := by
    filter_upwards [hsiAll] with ω hω
    have hterms : ∀ i ∈ Finset.univ, Integrable
        (fun z : unitInterval × ℝ => u i •
          (if z.1 ∈ S i then z.2 else 0))
        (poissonRandomMeasure Ks Xs ω) := by
      intro i hi
      exact (hω i).const_mul (u i)
    have heq : (fun z : unitInterval × ℝ => finiteWindowIntegrand S u z) =
        fun z => ∑ i ∈ Finset.univ, u i •
          (if z.1 ∈ S i then z.2 else 0) := by
      funext z
      simp [finiteWindowIntegrand, mul_ite]
    change Integrable (fun z => finiteWindowIntegrand S u z)
      (poissonRandomMeasure Ks Xs ω)
    rw [heq]
    exact integrable_finsetSum Finset.univ hterms
  have hbreal : ∀ᵐ ω ∂Pb, Integrable (finiteWindowIntegrand S u)
      (poissonRandomMeasure Kb Xb ω) := by
    filter_upwards [hbiAll] with ω hω
    have hterms : ∀ i ∈ Finset.univ, Integrable
        (fun z : unitInterval × ℝ => u i •
          (if z.1 ∈ S i then z.2 else 0))
        (poissonRandomMeasure Kb Xb ω) := by
      intro i hi
      exact (hω i).const_mul (u i)
    have heq : (fun z : unitInterval × ℝ => finiteWindowIntegrand S u z) =
        fun z => ∑ i ∈ Finset.univ, u i •
          (if z.1 ∈ S i then z.2 else 0) := by
      funext z
      simp [finiteWindowIntegrand, mul_ite]
    change Integrable (fun z => finiteWindowIntegrand S u z)
      (poissonRandomMeasure Kb Xb ω)
    rw [heq]
    exact integrable_finsetSum Finset.univ hterms
  have hEqS : ∀ᵐ ω ∂Ps,
      finiteWindowIntegral S u (poissonRandomMeasure Ks Xs ω) =
        ∫ z, finiteWindowIntegrand S u z ∂(poissonRandomMeasure Ks Xs ω) := by
    filter_upwards [hsiAll] with ω hω
    symm
    exact integral_finiteWindowIntegrand S u _ (fun i => hω i)
  have hEqB : ∀ᵐ ω ∂Pb,
      finiteWindowIntegral S u (poissonRandomMeasure Kb Xb ω) =
        ∫ z, finiteWindowIntegrand S u z ∂(poissonRandomMeasure Kb Xb ω) := by
    filter_upwards [hbiAll] with ω hω
    symm
    exact integral_finiteWindowIntegrand S u _ (fun i => hω i)
  have hEqS' : ∀ᵐ ω ∂(Ps.prod Pb),
      finiteWindowIntegral S u (poissonRandomMeasure Ks Xs ω.1) =
        ∫ z, finiteWindowIntegrand S u z ∂(poissonRandomMeasure Ks Xs ω.1) :=
    ae_of_ae_map (μ := Ps.prod Pb) measurable_fst.aemeasurable (by simpa using hEqS)
  have hEqB' : ∀ᵐ ω ∂(Ps.prod Pb),
      finiteWindowIntegral S u (poissonRandomMeasure Kb Xb ω.2) =
        ∫ z, finiteWindowIntegrand S u z ∂(poissonRandomMeasure Kb Xb ω.2) :=
    ae_of_ae_map (μ := Ps.prod Pb) measurable_snd.aemeasurable (by simpa using hEqB)
  calc
    _ = ∫ ω : Ωs × Ωb, Complex.exp
        (((ξ * ((∫ z, finiteWindowIntegrand S u z
            ∂(poissonRandomMeasure Ks Xs ω.1)) +
          (∫ z, finiteWindowIntegrand S u z
            ∂(poissonRandomMeasure Kb Xb ω.2))) : ℝ) : ℂ) *
          Complex.I) ∂(Ps.prod Pb) := by
      apply integral_congr_ae
      filter_upwards [hEqS', hEqB'] with ω hs hb
      rw [hs, hb]
    _ = _ := hν.integral_exp_finiteWindow_sum_cutoff_poissonRandomMeasures
      hsmall n hds hdb S u hS hdisj ξ hsreal hbreal

/-- The finite-window sum for two independent Poisson sources has the
characteristic exponent obtained by applying the general Poisson integral
formula to the combined window integrand. -/
theorem integral_exp_finiteWindow_sum_split_poissonRandomMeasures
    {ι : Type*} [Fintype ι]
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ms mb : Measure (unitInterval × ℝ)} [SigmaFinite ms] [SigmaFinite mb]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hds : IsPoissonPointFamily Ks Xs ms Ps)
    (hdb : IsPoissonPointFamily Kb Xb mb Pb)
    (S : ι → Set unitInterval) (u : ι → ℝ)
    (hfs : Measurable (finiteWindowIntegrand S u))
    (hfb : Measurable (finiteWindowIntegrand S u))
    (ξ : ℝ)
    (hsreal : ∀ᵐ ω ∂Ps, Integrable (finiteWindowIntegrand S u)
      (poissonRandomMeasure Ks Xs ω))
    (hbreal : ∀ᵐ ω ∂Pb, Integrable (finiteWindowIntegrand S u)
      (poissonRandomMeasure Kb Xb ω))
    (hsint : Integrable
      (fun z => Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1) ms)
    (hbint : Integrable
      (fun z => Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) * Complex.I) - 1) mb) :
    (∫ ω : Ωs × Ωb, Complex.exp
      (((ξ * ((∫ z, finiteWindowIntegrand S u z
          ∂(poissonRandomMeasure Ks Xs ω.1)) +
        (∫ z, finiteWindowIntegrand S u z
          ∂(poissonRandomMeasure Kb Xb ω.2))) : ℝ) : ℂ) *
        Complex.I) ∂(Ps.prod Pb)) =
      Complex.exp
        ((∫ z, (Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) *
            Complex.I) - 1) ∂ms) +
         (∫ z, (Complex.exp (((ξ * finiteWindowIntegrand S u z : ℝ) : ℂ) *
            Complex.I) - 1) ∂mb)) := by
  exact integral_exp_sum_independent_poissonRandomMeasures hds hdb hfs hfb ξ
    hsreal hbreal hsint hbint

end
end ProbabilityTheory
