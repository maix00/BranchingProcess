/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Survival.Conditioning
public import Probability.Process.RandomWalk.Path.Skorokhod.Corridor.Endpoint.Closed
public import Probability.Process.RandomWalk.Path.Skorokhod.Corridor.Endpoint.Interpolation
public import Analysis.Asymptotics.Scale.ShiftedFloor

/-!
# The finite transition event in the conditioned meander argument

The public objects and theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.nonnegativeTransitionEvent`:
  $D_{n,\Delta}=\{0\le S_j\le5\Delta/6\ (1\le j\le n),\
  S_n\in[5\Delta/12,11\Delta/24]\}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.normalizedTransitionCorridor`:
  the path event $\{f:\forall t\in[0,1],\ 0\le f(t)\le5s/(6\sigma),\
  f(1)\in[5s/(12\sigma),11s/(24\sigma)]\}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.measure_nonnegativeTransitionEvent_eq_cond_mul_survival`:
  $\mathbb P(D_{n,\Delta})=
  \mathbb P(D_{n,\Delta}\mid C_n)\mathbb P(C_n)$, where
  $C_n=\{S_j\ge0:1\le j\le n\}$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.mem_nonnegativeTransitionEvent_iff_normalizedTransitionCorridor`:
  for $n>0$ and $\sigma>0$, membership in $D_{n,\Delta}$ equals
  membership of $S_{\lfloor nt\rfloor}/(\sigma\sqrt n)$ in the
  normalized transition corridor with scale $\Delta/\sqrt n$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.mem_nonnegativeTransitionEvent_iff_normalizedInterpolatedTransitionCorridor`:
  the same grid event is the closed endpoint corridor event of the
  polygonal interpolation, whose values between grid points are affine.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned.diffusiveTransitionHorizon`:
  $N_{\Delta_n,m}=\lfloor\Delta_n^2\rfloor-m$ for real widths $\Delta_n$.

This is the transition event and normalization in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.5, and Appendix A.2, Lemma A.7.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

/-- The path version of $D_{N,\Delta}$ after normalizing the walk by
$\sigma\sqrt N$ and writing $s=\Delta/\sqrt N$. This is the transition
event in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring*, Chapter 3, Lemma 3.5, and Appendix A.2, Lemma A.7. -/
def normalizedTransitionCorridor (sigma scale : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  Skorokhod.rangeInClosedIntervalEndsIn
    0 ((5 / 6 * scale) / sigma)
      ((5 / 12 * scale) / sigma) ((11 / 24 * scale) / sigma)


/-- The nonnegative finite-width transition event in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3,
Lemma 3.5 and Appendix A.2, Lemma A.7. -/
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
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Appendix A.2, Lemma A.7. The conditioning identity follows Francesco
Caravenna and Loïc Chaumont, *Invariance principles for random walks
conditioned to stay positive*, equation (3.3), DOI 10.1214/07-AIHP119. -/
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
after the normalization in Francesco Caravenna and Loïc Chaumont,
*Invariance principles for random walks conditioned to stay positive*,
equation (3.3), DOI 10.1214/07-AIHP119. -/
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

/-- The diffusive transition horizon after a fixed finite entrance segment
in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.5, and Appendix A.2, Lemma A.7. -/
noncomputable def diffusiveTransitionHorizon
    (width : ℕ → ℝ) (offset n : ℕ) : ℕ :=
  Asymptotics.floorBlockLength (fun k => width k ^ 2) n - offset

end ProbabilityTheory.RandomWalk.FunctionalLimit.Conditioned

end
