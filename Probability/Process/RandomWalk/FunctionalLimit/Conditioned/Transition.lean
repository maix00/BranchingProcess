/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Meander
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Survival
public import Probability.Process.RandomWalk.Path.Skorokhod.Corridor.Endpoint.Closed
public import Probability.Process.RandomWalk.Path.Skorokhod.Corridor.Endpoint.Interpolation
public import Analysis.Asymptotics.ShiftedFloor

/-!
# The finite transition event in the conditioned meander argument

The public objects and theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_nonnegativeTransitionEvent_eq_cond_mul_survival`:
  $\mathbb P(D_{n,\Delta})=
  \mathbb P(D_{n,\Delta}\mid C_n)\mathbb P(C_n)$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.nonnegativeTransitionEvent`:
  $D_{n,\Delta}=\{0\le S_j\le5\Delta/6\ (1\le j\le n),\
  S_n\in[5\Delta/12,11\Delta/24]\}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.mem_nonnegativeTransitionEvent_iff_normalizedTransitionCorridor`:
  for $n>0$ and $\sigma>0$, membership in $D_{n,\Delta}$ equals
  membership of $S_{\lfloor nt\rfloor}/(\sigma\sqrt n)$ in the
  normalized transition corridor with scale $\Delta/\sqrt n$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.mem_nonnegativeTransitionEvent_iff_normalizedInterpolatedTransitionCorridor`:
  the same grid event is the closed endpoint corridor event of the
  polygonal interpolation, whose values between grid points are affine.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_interpolatedTransitionConditionalProbability_ge`:
  from a conditioned polygonal-path limit with support at
  $t\mapsto7t/(16\sigma)$, some $q>0$ satisfies
  $\mathbb P(D_{n+1,\Delta_n}\mid C_{n+1})\ge q$ eventually.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_transitionConditionalProbability_ge`:
  given the Iglehart--Bolthausen conditioned path limit, Brownian-meander
  support at the specified straight path, and $\Delta_n/\sqrt{n+1}\to1$,
  some $q>0$ satisfies $\mathbb P(D_{n+1,\Delta_n}\mid C_{n+1})\ge q$
  eventually.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_transitionConditionalProbability_ge_of_imhofLaw`:
  the same estimate when the limiting law is identified with the Imhof
  transform of the radial law of three independent Brownian paths; its
  straight-path support input follows from the BES(3) support theorem.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.diffusiveTransitionHorizon`:
  $N_{\Delta_n,m}=\lfloor\Delta_n^2\rfloor-m$ for real widths $\Delta_n$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.conditionedMeanderLimit_diffusive`:
  the standard conditioned invariance limit at times $N$ also holds at
  $N=\lfloor\Delta_n^2\rfloor-m$ whenever $\Delta_n\to\infty$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_diffusiveTransitionConditionalProbability_ge`:
  for $\Delta_n\to\infty$ and fixed $m$, the conditional meander limit
  and support give $\mathbb P(D_{N_{\Delta_n,m},\Delta_n}\mid
  C_{N_{\Delta_n,m}})\ge q>0$ eventually.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.exists_eventually_diffusiveTransitionConditionalProbability_ge_of_imhofLaw`:
  the diffusive-horizon estimate with the support input derived from the
  Imhof representation of the limiting path law.

This is the transition event and normalization in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, Lemma 3.5, Appendix A.2.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The nonnegative finite-width transition event in Wang Yiyang,
Chapter 3, Lemma 3.5, Appendix A.2. -/
def nonnegativeTransitionEvent (n : ℕ) (width : ℝ) : Set (ℕ → ℝ) :=
  {increment |
    (∀ k : Fin n,
      0 ≤ AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment ≤ (5 / 6) * width) ∧
    AdditivePath.displacement n increment ∈
      Set.Icc ((5 / 12) * width) ((11 / 24) * width)}

/-- The precise transition event $D_{n,\Delta}$ is contained in the
survival event $C_n$, so its probability factors into conditional transition
and survival probabilities. This is the multiplication step in Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Appendix A.2, proof of the meander transition lemma, using the conditioning
in Caravenna--Chaumont, equation (3.3) (DOI 10.1214/07-AIHP119). -/
theorem measure_nonnegativeTransitionEvent_eq_cond_mul_survival
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) (width : ℝ) :
    iidSequenceLaw ν (nonnegativeTransitionEvent n width) =
      survivalConditionedLaw ν n (nonnegativeTransitionEvent n width) *
        iidSequenceLaw ν {increment | SurvivesNonnegative n increment} := by
  let C : Set (ℕ → ℝ) := {increment | SurvivesNonnegative n increment}
  let D : Set (ℕ → ℝ) := nonnegativeTransitionEvent n width
  have hsubset : D ⊆ C := by
    intro increment hin k
    exact (hin.1 k).1
  have hinter : C ∩ D = D := Set.inter_eq_right.mpr hsubset
  have hcond := ProbabilityTheory.cond_mul_eq_inter
    (measurableSet_survivesNonnegative n) D (iidSequenceLaw ν)
  simpa only [survivalConditionedLaw, C, D, hinter] using hcond.symm

/-- The finite-grid transition event is exactly its Skorokhod path version
after the normalization used by Caravenna--Chaumont, equation (3.3). -/
theorem mem_nonnegativeTransitionEvent_iff_normalizedTransitionCorridor
    {n : ℕ} (hn : 0 < n) {sigma : ℝ} (hsigma : 0 < sigma)
    {width : ℝ} (hwidth : 0 ≤ width) (increment : ℕ → ℝ) :
    increment ∈ nonnegativeTransitionEvent n width ↔
      normalizedStepCadlagPathIcc
          (fun j => sigma * Real.sqrt j) n increment ∈
        normalizedTransitionCorridor sigma (width / Real.sqrt n) := by
  have hroot : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  have hnorm : 0 < sigma * Real.sqrt n := mul_pos hsigma hroot
  have hupper :
      ((5 / 6 * (width / Real.sqrt n)) / sigma) =
        ((5 / 6) * width) / (sigma * Real.sqrt n) := by
    field_simp
  have hendLower :
      ((5 / 12 * (width / Real.sqrt n)) / sigma) =
        ((5 / 12) * width) / (sigma * Real.sqrt n) := by
    field_simp
  have hendUpper :
      ((11 / 24 * (width / Real.sqrt n)) / sigma) =
        ((11 / 24) * width) / (sigma * Real.sqrt n) := by
    field_simp
  rw [normalizedTransitionCorridor,
    normalizedStepCadlagPathIcc_mem_rangeInClosedIntervalEndsIn_iff_grid
      (fun j => sigma * Real.sqrt j) hn (le_refl 0) (by
        rw [hupper]
        exact div_nonneg (mul_nonneg (by norm_num) hwidth) hnorm.le)]
  rw [hupper, hendLower, hendUpper]
  change
    ((∀ k : Fin n,
      0 ≤ AdditivePath.displacement (k + 1) increment ∧
      AdditivePath.displacement (k + 1) increment ≤ (5 / 6) * width) ∧
      AdditivePath.displacement n increment ∈
        Set.Icc ((5 / 12) * width) ((11 / 24) * width)) ↔ _
  constructor
  · rintro ⟨hgrid, hend⟩
    constructor
    · intro k
      dsimp [InClosedCorridorOnGrid]
      rw [normalizedStepPath_grid _ hn, inv_mul_eq_div]
      exact ⟨div_nonneg (hgrid k).1 hnorm.le,
        (div_le_div_iff_of_pos_right hnorm).2 (hgrid k).2⟩
    · exact ⟨(div_le_div_iff_of_pos_right hnorm).2 hend.1,
        (div_le_div_iff_of_pos_right hnorm).2 hend.2⟩
  · rintro ⟨hgrid, hend⟩
    constructor
    · intro k
      have hk := hgrid k
      dsimp [InClosedCorridorOnGrid] at hk
      rw [normalizedStepPath_grid _ hn, inv_mul_eq_div] at hk
      exact ⟨by simpa using (le_div_iff₀ hnorm).1 hk.1,
        (div_le_div_iff_of_pos_right hnorm).1 hk.2⟩
    · exact ⟨(div_le_div_iff_of_pos_right hnorm).1 hend.1,
        (div_le_div_iff_of_pos_right hnorm).1 hend.2⟩

/-- The finite-grid transition event is equally the event that the
polygonal interpolation stays in the closed transition corridor. -/
theorem mem_nonnegativeTransitionEvent_iff_normalizedInterpolatedTransitionCorridor
    {n : ℕ} (hn : 0 < n) {sigma : ℝ} (hsigma : 0 < sigma)
    {width : ℝ} (hwidth : 0 ≤ width) (increment : ℕ → ℝ) :
    increment ∈ nonnegativeTransitionEvent n width ↔
      normalizedLinearCadlagPathIcc
          (fun j => sigma * Real.sqrt j) n increment ∈
        normalizedTransitionCorridor sigma (width / Real.sqrt n) := by
  have hupper : 0 ≤ (5 / 6 * (width / Real.sqrt n)) / sigma := by
    positivity
  have hpathEq :
      (normalizedLinearCadlagPathIcc
          (fun j => sigma * Real.sqrt j) n increment ∈
        normalizedTransitionCorridor sigma (width / Real.sqrt n)) ↔
      (normalizedStepCadlagPathIcc
          (fun j => sigma * Real.sqrt j) n increment ∈
        normalizedTransitionCorridor sigma (width / Real.sqrt n)) := by
    change
      (normalizedLinearCadlagPathIcc
          (fun j => sigma * Real.sqrt j) n increment ∈
        Skorokhod.rangeInClosedIntervalEndsIn
          0 ((5 / 6 * (width / Real.sqrt n)) / sigma)
          ((5 / 12 * (width / Real.sqrt n)) / sigma)
          ((11 / 24 * (width / Real.sqrt n)) / sigma)) ↔
      (normalizedStepCadlagPathIcc
          (fun j => sigma * Real.sqrt j) n increment ∈
        Skorokhod.rangeInClosedIntervalEndsIn
          0 ((5 / 6 * (width / Real.sqrt n)) / sigma)
          ((5 / 12 * (width / Real.sqrt n)) / sigma)
          ((11 / 24 * (width / Real.sqrt n)) / sigma))
    rw [normalizedLinearCadlagPathIcc_mem_rangeInClosedIntervalEndsIn_iff_grid
      _ hn (le_refl 0) hupper,
      normalizedStepCadlagPathIcc_mem_rangeInClosedIntervalEndsIn_iff_grid
        _ hn (le_refl 0) hupper]
  exact (mem_nonnegativeTransitionEvent_iff_normalizedTransitionCorridor
    hn hsigma hwidth increment).trans hpathEq.symm

/-- The conditional transition bound follows directly from convergence
of the polygonal paths and the support point of the limiting law. -/
theorem exists_eventually_interpolatedTransitionConditionalProbability_ge
    {Ωm : Type*} [MeasurableSpace Ωm]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    [∀ n, IsProbabilityMeasure (survivalConditionedLaw ν (n + 1))]
    {Pm : Measure Ωm} [IsProbabilityMeasure Pm]
    {M : Ωm → CadlagPath unitInterval ℝ}
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hlimit : TendstoInDistribution
      (fun n increment => normalizedLinearCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (n + 1) increment)
      atTop M (fun n => survivalConditionedLaw ν (n + 1)) Pm)
    (hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (Pm.map M).support)
    {width : ℕ → ℝ} (hwidth : ∀ n, 0 ≤ width n)
    (hratio : Tendsto (fun n => width n / Real.sqrt (n + 1))
      atTop (𝓝 1)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ survivalConditionedLaw ν (n + 1)
        (nonnegativeTransitionEvent (n + 1) (width n)) := by
  have hnonnegative (n : ℕ) :
      ∀ᵐ increment ∂survivalConditionedLaw ν (n + 1),
        ∀ t : unitInterval,
          0 ≤ normalizedLinearCadlagPathIcc
            (fun j => sigma * Real.sqrt j) (n + 1) increment t := by
    exact ae_nonnegative_normalizedLinearCadlagPathIcc ν (Nat.succ_pos n)
      (fun j => sigma * Real.sqrt j)
      (mul_pos hsigma
        (Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.succ_pos n))))
  obtain ⟨q, hq, hevent⟩ :=
    exists_eventually_normalizedTransitionCorridorProbability_ge
      hsigma hrho hrhoSmall hlimit hsupport hratio hnonnegative
  refine ⟨q, hq, ?_⟩
  filter_upwards [hevent] with n hn
  have hmeas : MeasurableSet
      (normalizedTransitionCorridor sigma
        (width n / Real.sqrt (n + 1))) :=
    (Skorokhod.isClosed_rangeInClosedIntervalEndsIn _ _ _ _).measurableSet
  rw [Measure.map_apply_of_aemeasurable
    (hlimit.forall_aemeasurable n) hmeas] at hn
  have heventEq :
      {increment : ℕ → ℝ |
        normalizedLinearCadlagPathIcc
          (fun j => sigma * Real.sqrt j) (n + 1) increment ∈
        normalizedTransitionCorridor sigma
          (width n / Real.sqrt (n + 1))} =
      nonnegativeTransitionEvent (n + 1) (width n) := by
    ext increment
    simpa only [Set.mem_ofPred_eq, Nat.succ_eq_add_one, Nat.cast_add,
      Nat.cast_one] using
      (mem_nonnegativeTransitionEvent_iff_normalizedInterpolatedTransitionCorridor
        (Nat.succ_pos n) hsigma (hwidth n) increment).symm
  change q ≤ survivalConditionedLaw ν (n + 1)
    {increment : ℕ → ℝ |
      normalizedLinearCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (n + 1) increment ∈
      normalizedTransitionCorridor sigma
        (width n / Real.sqrt (n + 1))} at hn
  rw [heventEq] at hn
  exact hn

/-- The positive conditional probability of the precise finite transition
event follows from the Iglehart--Bolthausen conditioned invariance principle
and the Brownian-meander support step in Wang Yiyang, Chapter 3,
Lemma 3.5, Appendix A.2. The invariance principle and support remain
explicit assumptions until their laws are constructed. -/
theorem exists_eventually_transitionConditionalProbability_ge
    {Ωm : Type*} [MeasurableSpace Ωm]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    [∀ n, IsProbabilityMeasure (survivalConditionedLaw ν (n + 1))]
    {Pm : Measure Ωm} [IsProbabilityMeasure Pm]
    {M : Ωm → CadlagPath unitInterval ℝ}
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hlimit : TendstoInDistribution
      (fun n increment => normalizedStepCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (n + 1) increment)
      atTop M (fun n => survivalConditionedLaw ν (n + 1)) Pm)
    (hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (Pm.map M).support)
    {width : ℕ → ℝ} (hwidth : ∀ n, 0 ≤ width n)
    (hratio : Tendsto (fun n => width n / Real.sqrt (n + 1))
      atTop (𝓝 1)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ survivalConditionedLaw ν (n + 1)
        (nonnegativeTransitionEvent (n + 1) (width n)) := by
  have hnonnegative (n : ℕ) :
      ∀ᵐ increment ∂survivalConditionedLaw ν (n + 1),
        ∀ t : unitInterval,
          0 ≤ normalizedStepCadlagPathIcc
            (fun j => sigma * Real.sqrt j) (n + 1) increment t := by
    exact ae_nonnegative_normalizedStepCadlagPathIcc ν (n + 1)
      (fun j => sigma * Real.sqrt j)
      (mul_pos hsigma
        (Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.succ_pos n))))
  obtain ⟨q, hq, hevent⟩ :=
    exists_eventually_normalizedTransitionCorridorProbability_ge
      hsigma hrho hrhoSmall hlimit hsupport hratio hnonnegative
  refine ⟨q, hq, ?_⟩
  filter_upwards [hevent] with n hn
  have hmeas : MeasurableSet
      (normalizedTransitionCorridor sigma
        (width n / Real.sqrt (n + 1))) :=
    (Skorokhod.isClosed_rangeInClosedIntervalEndsIn _ _ _ _).measurableSet
  rw [Measure.map_apply_of_aemeasurable
    (hlimit.forall_aemeasurable n) hmeas] at hn
  have heventEq :
      {increment : ℕ → ℝ |
        normalizedStepCadlagPathIcc
          (fun j => sigma * Real.sqrt j) (n + 1) increment ∈
        normalizedTransitionCorridor sigma
          (width n / Real.sqrt (n + 1))} =
      nonnegativeTransitionEvent (n + 1) (width n) := by
    ext increment
    simpa only [Set.mem_ofPred_eq, Nat.succ_eq_add_one, Nat.cast_add,
      Nat.cast_one] using
      (mem_nonnegativeTransitionEvent_iff_normalizedTransitionCorridor
        (Nat.succ_pos n) hsigma (hwidth n) increment).symm
  change q ≤ survivalConditionedLaw ν (n + 1)
    {increment : ℕ → ℝ |
      normalizedStepCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (n + 1) increment ∈
      normalizedTransitionCorridor sigma
        (width n / Real.sqrt (n + 1))} at hn
  rw [heventEq] at hn
  exact hn

/-- The transition estimate with its support point derived from the Imhof
representation of the limiting conditioned path law. The remaining limit
identification is the Iglehart--Bolthausen conditioned invariance principle,
recalled by Caravenna--Chaumont in equation (3.3). -/
theorem exists_eventually_transitionConditionalProbability_ge_of_imhofLaw
    {Ωm ΩB : Type*} [MeasurableSpace Ωm] [MeasurableSpace ΩB]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    [∀ n, IsProbabilityMeasure (survivalConditionedLaw ν (n + 1))]
    {Pm : Measure Ωm} [IsProbabilityMeasure Pm]
    {M : Ωm → CadlagPath unitInterval ℝ}
    {PB : Measure ΩB} [IsProbabilityMeasure PB]
    {W : ℝ≥0 → ΩB → ℝ}
    (hBrownian : IsBrownianReal W PB)
    (hWmeasurable : ∀ t, Measurable (W t))
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hlimit : TendstoInDistribution
      (fun n increment => normalizedStepCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (n + 1) increment)
      atTop M (fun n => survivalConditionedLaw ν (n + 1)) Pm)
    (hImhofLaw : Pm.map M = BrownianMeander.imhofTilt
      (BrownianBessel3.pathLawOfBrownian hBrownian hWmeasurable))
    {width : ℕ → ℝ} (hwidth : ∀ n, 0 ≤ width n)
    (hratio : Tendsto (fun n => width n / Real.sqrt (n + 1))
      atTop (𝓝 1)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ survivalConditionedLaw ν (n + 1)
        (nonnegativeTransitionEvent (n + 1) (width n)) := by
  have hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (Pm.map M).support := by
    rw [hImhofLaw]
    change Skorokhod.linearPath ((7 / 16) / sigma) ∈
      (BrownianMeander.imhofTilt
        (BrownianBessel3.pathLawOfBrownian hBrownian hWmeasurable)).support
    exact BrownianMeander.linearPath_mem_imhofTilt_support
      hBrownian hWmeasurable (div_nonneg (by norm_num) hsigma.le)
  exact exists_eventually_transitionConditionalProbability_ge
    hsigma hrho hrhoSmall hlimit hsupport hwidth hratio

/-- The diffusive transition horizon after a fixed finite entrance segment
in Wang Yiyang, Chapter 3, Lemma 3.5, Appendix A.2. -/
noncomputable def diffusiveTransitionHorizon
    (width : ℕ → ℝ) (offset n : ℕ) : ℕ :=
  Asymptotics.floorBlockLength (fun k => width k ^ 2) n - offset

/-- The conditioned path limit at integer times remains valid along the
diffusive transition horizons in Wang Yiyang, Chapter 3, Lemma 3.5,
Appendix A.2. This is a cofinal reindexing of the Iglehart--Bolthausen
limit recalled by Caravenna--Chaumont in equation (3.3). -/
theorem conditionedMeanderLimit_diffusive
    {Ωm : Type*} [MeasurableSpace Ωm]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    [∀ n, IsProbabilityMeasure (survivalConditionedLaw ν (n + 1))]
    {Pm : Measure Ωm} [IsProbabilityMeasure Pm]
    {M : Ωm → CadlagPath unitInterval ℝ}
    {sigma : ℝ} {width : ℕ → ℝ}
    (hwidth : Tendsto width atTop atTop) (offset : ℕ)
    [∀ n, IsProbabilityMeasure
      (survivalConditionedLaw ν (diffusiveTransitionHorizon width offset n))]
    (hlimit : TendstoInDistribution
      (fun n increment => normalizedStepCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (n + 1) increment)
      atTop M (fun n => survivalConditionedLaw ν (n + 1)) Pm) :
    TendstoInDistribution
      (fun n increment => normalizedStepCadlagPathIcc
        (fun j => sigma * Real.sqrt j)
        (diffusiveTransitionHorizon width offset n) increment)
      atTop M
      (fun n => survivalConditionedLaw ν
        (diffusiveTransitionHorizon width offset n)) Pm := by
  have hargument : Tendsto (fun n => width n ^ 2) atTop atTop := by
    have hmul : Tendsto (fun n => width n * width n) atTop atTop :=
      hwidth.atTop_mul_atTop₀ hwidth
    simpa [pow_two] using hmul
  have hhorizon : Tendsto (diffusiveTransitionHorizon width offset)
      atTop atTop := by
    change Tendsto (fun n =>
      Asymptotics.floorBlockLength (fun k => width k ^ 2) n - offset)
      atTop atTop
    exact (tendsto_sub_atTop_nat offset).comp
      (Asymptotics.tendsto_floorBlockLength_atTop hargument)
  have hindex : Tendsto
      (fun n => diffusiveTransitionHorizon width offset n - 1)
      atTop atTop := by
    simpa only [Function.comp_def] using
      (tendsto_sub_atTop_nat 1).comp hhorizon
  have hcomposition := hlimit.comp_tendsto hindex
  have hpositive : ∀ᶠ n : ℕ in atTop,
      0 < diffusiveTransitionHorizon width offset n :=
    hhorizon.eventually (eventually_gt_atTop 0)
  refine ⟨?_, hlimit.aemeasurable_limit, ?_⟩
  · intro n
    exact (RandomWalk.measurable_normalizedStepCadlagPathIcc _ _).aemeasurable
  apply hcomposition.tendsto.congr'
  filter_upwards [hpositive] with n hn
  have hsucc : diffusiveTransitionHorizon width offset n - 1 + 1 =
      diffusiveTransitionHorizon width offset n :=
    Nat.sub_add_cancel hn
  apply Subtype.ext
  simp only [hsucc]

/-- The conditional transition probability for the exact diffusive horizon
$N_{\Delta,m}=\lfloor\Delta^2\rfloor-m$. The scale relation is proved in
`Analysis.Asymptotics.ShiftedFloor`; the meander limit and support are the
remaining external inputs from the Iglehart--Bolthausen limit recalled in
Caravenna--Chaumont, equation (3.3), and
Wang Yiyang, Chapter 3, Lemma 3.5, Appendix A.2. -/
theorem exists_eventually_diffusiveTransitionConditionalProbability_ge
    {Ωm : Type*} [MeasurableSpace Ωm]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    [∀ n, IsProbabilityMeasure (survivalConditionedLaw ν (n + 1))]
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (offset : ℕ)
    [∀ n, IsProbabilityMeasure
      (survivalConditionedLaw ν (diffusiveTransitionHorizon width offset n))]
    {Pm : Measure Ωm} [IsProbabilityMeasure Pm]
    {M : Ωm → CadlagPath unitInterval ℝ}
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hlimit : TendstoInDistribution
      (fun n increment => normalizedStepCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (n + 1) increment)
      atTop M (fun n => survivalConditionedLaw ν (n + 1)) Pm)
    (hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (Pm.map M).support) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ survivalConditionedLaw ν
        (diffusiveTransitionHorizon width offset n)
        (nonnegativeTransitionEvent
          (diffusiveTransitionHorizon width offset n) (width n)) := by
  have hratio : Tendsto (fun n => width n /
      Real.sqrt (diffusiveTransitionHorizon width offset n))
      atTop (𝓝 1) :=
    Asymptotics.tendsto_width_div_sqrt_floor_sq_sub_nat hwidth offset
  have hnonnegative (n : ℕ) :
      ∀ᵐ increment ∂survivalConditionedLaw ν
          (diffusiveTransitionHorizon width offset n),
        ∀ t : unitInterval,
          0 ≤ normalizedStepCadlagPathIcc
            (fun j => sigma * Real.sqrt j)
            (diffusiveTransitionHorizon width offset n) increment t := by
    by_cases hn : 0 < diffusiveTransitionHorizon width offset n
    · exact ae_nonnegative_normalizedStepCadlagPathIcc ν
        (diffusiveTransitionHorizon width offset n)
        (fun j => sigma * Real.sqrt j)
        (mul_pos hsigma (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)))
    · have hn0 : diffusiveTransitionHorizon width offset n = 0 :=
        Nat.eq_zero_of_not_pos hn
      filter_upwards [] with increment
      intro t
      simp [normalizedStepCadlagPathIcc_apply, normalizedStepPath, hn0]
  have hlimitDiffusive := conditionedMeanderLimit_diffusive hwidth offset hlimit
  obtain ⟨q, hq, hevent⟩ :=
    exists_eventually_normalizedTransitionCorridorProbability_ge
      hsigma hrho hrhoSmall hlimitDiffusive hsupport hratio hnonnegative
  have hwidthPos : ∀ᶠ n : ℕ in atTop, 0 < width n :=
    hwidth.eventually (eventually_gt_atTop 0)
  have hargument : Tendsto (fun n => width n ^ 2) atTop atTop := by
    have hmul : Tendsto (fun n => width n * width n) atTop atTop :=
      hwidth.atTop_mul_atTop₀ hwidth
    simpa [pow_two] using hmul
  have hhorizonPos : ∀ᶠ n : ℕ in atTop,
      0 < diffusiveTransitionHorizon width offset n := by
    have hfloor := Asymptotics.tendsto_floorBlockLength_atTop hargument
    filter_upwards [hfloor.eventually (eventually_gt_atTop offset)] with n hn
    exact Nat.sub_pos_iff_lt.mpr hn
  refine ⟨q, hq, ?_⟩
  filter_upwards [hevent, hwidthPos, hhorizonPos] with n hn hw hN
  have hmeas : MeasurableSet
      (normalizedTransitionCorridor sigma
        (width n / Real.sqrt (diffusiveTransitionHorizon width offset n))) :=
    (Skorokhod.isClosed_rangeInClosedIntervalEndsIn _ _ _ _).measurableSet
  rw [Measure.map_apply_of_aemeasurable
    (hlimitDiffusive.forall_aemeasurable n) hmeas] at hn
  have heventEq :
      {increment : ℕ → ℝ |
        normalizedStepCadlagPathIcc (fun j => sigma * Real.sqrt j)
          (diffusiveTransitionHorizon width offset n) increment ∈
        normalizedTransitionCorridor sigma
          (width n / Real.sqrt (diffusiveTransitionHorizon width offset n))} =
      nonnegativeTransitionEvent
        (diffusiveTransitionHorizon width offset n) (width n) := by
    ext increment
    exact (mem_nonnegativeTransitionEvent_iff_normalizedTransitionCorridor
      hN hsigma hw.le increment).symm
  change q ≤ survivalConditionedLaw ν
    (diffusiveTransitionHorizon width offset n)
    {increment : ℕ → ℝ |
      normalizedStepCadlagPathIcc (fun j => sigma * Real.sqrt j)
        (diffusiveTransitionHorizon width offset n) increment ∈
      normalizedTransitionCorridor sigma
        (width n / Real.sqrt (diffusiveTransitionHorizon width offset n))}
      at hn
  rw [heventEq] at hn
  exact hn

/-- The transition estimate at $N_{\Delta_n,m}=\lfloor\Delta_n^2\rfloor-m$
with the limiting support point derived from the Imhof representation of
the radial Brownian law. The conditioned invariance principle remains the
explicit limit input. -/
theorem exists_eventually_diffusiveTransitionConditionalProbability_ge_of_imhofLaw
    {Ωm ΩB : Type*} [MeasurableSpace Ωm] [MeasurableSpace ΩB]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    [∀ n, IsProbabilityMeasure (survivalConditionedLaw ν (n + 1))]
    {width : ℕ → ℝ} (hwidth : Tendsto width atTop atTop)
    (offset : ℕ)
    [∀ n, IsProbabilityMeasure
      (survivalConditionedLaw ν (diffusiveTransitionHorizon width offset n))]
    {Pm : Measure Ωm} [IsProbabilityMeasure Pm]
    {M : Ωm → CadlagPath unitInterval ℝ}
    {PB : Measure ΩB} [IsProbabilityMeasure PB]
    {W : ℝ≥0 → ΩB → ℝ}
    (hBrownian : IsBrownianReal W PB)
    (hWmeasurable : ∀ t, Measurable (W t))
    {sigma rho : ℝ} (hsigma : 0 < sigma)
    (hrho : 0 < rho) (hrhoSmall : rho < 1 / 48)
    (hlimit : TendstoInDistribution
      (fun n increment => normalizedStepCadlagPathIcc
        (fun j => sigma * Real.sqrt j) (n + 1) increment)
      atTop M (fun n => survivalConditionedLaw ν (n + 1)) Pm)
    (hImhofLaw : Pm.map M = BrownianMeander.imhofTilt
      (BrownianBessel3.pathLawOfBrownian hBrownian hWmeasurable)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      q ≤ survivalConditionedLaw ν
        (diffusiveTransitionHorizon width offset n)
        (nonnegativeTransitionEvent
          (diffusiveTransitionHorizon width offset n) (width n)) := by
  have hsupport : Skorokhod.straightPath ((7 / 16) / sigma) ∈
      (Pm.map M).support := by
    rw [hImhofLaw]
    change Skorokhod.linearPath ((7 / 16) / sigma) ∈
      (BrownianMeander.imhofTilt
        (BrownianBessel3.pathLawOfBrownian hBrownian hWmeasurable)).support
    exact BrownianMeander.linearPath_mem_imhofTilt_support
      hBrownian hWmeasurable (div_nonneg (by norm_num) hsigma.le)
  exact exists_eventually_diffusiveTransitionConditionalProbability_ge
    hwidth offset hsigma hrho hrhoSmall hlimit hsupport

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
