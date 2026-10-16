/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Power.SequenceLowerPower
public import Probability.Distributions.Moments.Signs
public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Survival.Recurrence
public import Probability.Process.RandomWalk.Fluctuation.FiniteVarianceSignLimit
public import Probability.Process.RandomWalk.Path.Survival.Probability

/-!
# Finite-variance survival lower bound

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.exists_nonnegativeSurvivalProbability_ge_power_of_centeredSecondMoment`:
  for centered increments of variance $\sigma^2>0$ and
  $0<\gamma<1/2$, there is $C>0$ such that
  $\mathbb P(S_1,\ldots,S_n\ge0)\ge C(n+1)^{\gamma-1}$
  for every $n$.

The proof uses the coefficient recurrence in equation (2.2) of Section 2 of
M. Bauer, C. Godrèche, and J.-M. Luck, *Statistics of persistent events in
the binomial random walk: Will the drunken sailor hit the sober man?*,
*Journal of Statistical Physics* 96 (1999), 963–1019, DOI
10.1023/A:1004636216365, arXiv:cond-mat/9905252. Their Appendix A,
equations (A.7)--(A.8), derives the generating-function identity behind the
recurrence. The proof combines the finite recurrence with the Gaussian
endpoint-sign limit and a prefix-sum induction.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk

private lemma partialSum_prefix_eq_displacement
    (n : ℕ) (increment : ℕ → ℝ) (t : Fin (n + 1)) :
    Fin.partialSum (fun i : Fin n => increment i.val) t =
      AdditivePath.displacement t.val increment := by
  induction t using Fin.induction with
  | zero => simp [AdditivePath.displacement]
  | succ k ih =>
      rw [Fin.partialSum_succ, ih]
      simp [AdditivePath.displacement, Finset.sum_range_succ]

private lemma finitePartialSum_measurable (n : ℕ) (t : Fin (n + 1)) :
    Measurable (fun z : Fin n → ℝ => Fin.partialSum z t) := by
  induction t using Fin.induction with
  | zero => simp
  | succ k ih =>
      rw [show (fun z : Fin n → ℝ => Fin.partialSum z k.succ) =
        (fun z => Fin.partialSum z k.castSucc + z k) by funext z; rw [Fin.partialSum_succ]]
      exact ih.add (measurable_pi_apply k)

private lemma finiteSurvivalEvent_measurable (n : ℕ) :
    MeasurableSet {z : Fin n → ℝ |
      ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t} := by
  rw [show {z : Fin n → ℝ | ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t} =
      ⋂ t : Fin (n + 1), {z | 0 ≤ Fin.partialSum z t} by ext z; simp]
  exact MeasurableSet.iInter fun t =>
    measurableSet_Ici.preimage (finitePartialSum_measurable n t)

private lemma finiteSurvivalEvent_eq_infinite
    (n : ℕ) (increment : ℕ → ℝ) :
    (∀ t : Fin (n + 1), 0 ≤ Fin.partialSum
      (fun i : Fin n => increment i.val) t) ↔
      SurvivesNonnegative n increment := by
  constructor
  · intro h k
    simpa only [partialSum_prefix_eq_displacement, Fin.val_succ] using h k.succ
  · intro h t
    induction t using Fin.induction with
    | zero => simp
    | succ k ih =>
        simpa only [partialSum_prefix_eq_displacement, Fin.val_succ] using h k

private lemma finiteSurvivalProbability_eq_infinite
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => ν)).real
      {z : Fin n → ℝ | ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t} =
      ((iidSequenceLaw ν) {increment | SurvivesNonnegative n increment}).toReal := by
  change ((Measure.pi (fun _ : Fin n => ν))
      {z : Fin n → ℝ | ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t}).toReal = _
  rw [← iidSequenceLaw_map_finPrefix ν n]
  rw [Measure.map_apply (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val)
      (finiteSurvivalEvent_measurable n)]
  apply congrArg ENNReal.toReal
  apply congrArg (iidSequenceLaw ν)
  ext increment
  exact finiteSurvivalEvent_eq_infinite n increment
private lemma finiteEndpointProbability_eq_infinite
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.pi (fun _ : Fin n => ν)).real
      {z : Fin n → ℝ | 0 ≤ Fin.partialSum z (Fin.last n)} =
      ((iidSequenceLaw ν)
        {increment | 0 ≤ AdditivePath.displacement n increment}).toReal := by
  change ((Measure.pi (fun _ : Fin n => ν))
      {z : Fin n → ℝ | 0 ≤ Fin.partialSum z (Fin.last n)}).toReal = _
  rw [← iidSequenceLaw_map_finPrefix ν n]
  have hs : MeasurableSet {z : Fin n → ℝ | 0 ≤ Fin.partialSum z (Fin.last n)} := by
    exact measurableSet_Ici.preimage (finitePartialSum_measurable n (Fin.last n))
  rw [Measure.map_apply (measurable_pi_iff.mpr fun i => measurable_pi_apply i.val) hs]
  apply congrArg ENNReal.toReal
  apply congrArg (iidSequenceLaw ν)
  ext increment
  simp only [Set.mem_preimage, Set.mem_ofPred_eq,
    partialSum_prefix_eq_displacement, Fin.val_last]

private lemma finiteSurvivalProbability_zero
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : Fin 0 => ν)).real
      {z : Fin 0 → ℝ | ∀ t : Fin 1, 0 ≤ Fin.partialSum z t} = 1 := by
  have hevent : {z : Fin 0 → ℝ | ∀ t : Fin 1, 0 ≤ Fin.partialSum z t} = Set.univ := by
    ext z
    simp [Fin.forall_fin_succ]
  rw [hevent]
  simp

private lemma recurrence_to_convolution
    (F P : ℕ → ℝ) (hF0 : F 0 = 1)
    (hrec : ∀ n : ℕ, 0 < n →
      P n = (n : ℝ) * F n -
        ∑ r : Fin (n - 1), F (r.val + 1) * P (n - (r.val + 1)))
    {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * F n = ∑ k : Fin n, F k.val * P (n - k.val) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.sub_zero, hF0, one_mul, Fin.val_succ]
  have h := hrec (m + 1) (by omega)
  simpa [Nat.succ_eq_add_one, add_comm, add_left_comm, add_assoc] using
    (sub_eq_iff_eq_add.mp h.symm)
private lemma prefix_bound_of_convolution
    (F P : ℕ → ℝ) (hFnonneg : ∀ k, 0 ≤ F k)
    (hPnonneg : ∀ j, 0 ≤ P j)
    {β : ℝ} (_hβ : 0 ≤ β) (N : ℕ) (_hN : 1 ≤ N)
    (hPβ : ∀ j, N ≤ j → β ≤ P j)
    (hconv : ∀ n : ℕ, 0 < n →
      (n : ℝ) * F n = ∑ k : Fin n, F k.val * P (n - k.val))
    (n : ℕ) (hn : N ≤ n) :
    β * ∑ k ∈ Finset.range (n - N + 1), F k ≤ (n : ℝ) * F n := by
  have hm : n - N + 1 ≤ n := by omega
  rw [hconv n (by omega : 0 < n)]
  have hfin : (∑ k : Fin n, F k.val * P (n - k.val)) =
      ∑ k ∈ Finset.range n, F k * P (n - k) :=
    Fin.sum_univ_eq_sum_range (fun i : ℕ => F i * P (n - i)) n
  rw [hfin]
  calc
    β * ∑ k ∈ Finset.range (n - N + 1), F k =
        ∑ k ∈ Finset.range (n - N + 1), β * F k := by
      rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (n - N + 1), F k * P (n - k) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k < n - N + 1 := Finset.mem_range.mp hk
      have hnk : N ≤ n - k := by omega
      exact mul_le_mul_of_nonneg_right (hPβ (n - k) hnk) (hFnonneg k) |>.trans_eq (mul_comm _ _)
    _ ≤ ∑ k ∈ Finset.range n, F k * P (n - k) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) hm)
      · intro k _ _
        exact mul_nonneg (hFnonneg k) (hPnonneg (n - k))

/-- A positive centered finite-variance walk has a polynomial lower bound
for survival through each finite horizon. -/
theorem exists_nonnegativeSurvivalProbability_ge_power_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {sigma : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma) {γ : ℝ} (hγ : 0 < γ) (hγhalf : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      C * (((n + 1 : ℕ) : ℝ) ^ (γ - 1)) ≤
        ((iidSequenceLaw ν)
          {increment | SurvivesNonnegative n increment}).toReal := by
  let F : ℕ → ℝ := fun n => (Measure.pi (fun _ : Fin n => ν)).real
    {z : Fin n → ℝ | ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t}
  let P : ℕ → ℝ := fun n => (Measure.pi (fun _ : Fin n => ν)).real
    {z : Fin n → ℝ | 0 ≤ Fin.partialSum z (Fin.last n)}
  let β : ℝ := (γ + 1 / 2) / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hγβ : γ < β := by dsimp [β]; linarith
  have hγ1 : γ ≤ 1 := by linarith
  have hF0 : F 0 = 1 := finiteSurvivalProbability_zero ν
  have hFpos (n : ℕ) : 0 < F n := by
    rw [show F n = ((iidSequenceLaw ν)
      {increment | SurvivesNonnegative n increment}).toReal from
      finiteSurvivalProbability_eq_infinite ν n]
    exact ENNReal.toReal_pos
      (survivalProbability_pos_of_positiveIncrement
        ν (hν.measure_Ioi_zero_pos hsigma) n).ne'
      (measure_ne_top _ _)
  have hPnonneg (n : ℕ) : 0 ≤ P n := ENNReal.toReal_nonneg
  have hPlimit : Tendsto P atTop (nhds (1 / 2 : ℝ)) := by
    have h := tendsto_nonnegativePartialSumProbability_half ν hν hsigma
    have hreal := (ENNReal.tendsto_toReal (by norm_num :
      (1 / 2 : ℝ≥0∞) ≠ ⊤)).comp h
    have hhalf : (1 / 2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
    simpa only [Function.comp_def, hhalf,
      ← finiteEndpointProbability_eq_infinite ν] using hreal
  have hβhalf : β < 1 / 2 := by dsimp [β]; linarith
  have hPβ : ∀ᶠ n : ℕ in atTop, β ≤ P n := by
    exact (hPlimit.eventually (eventually_gt_nhds hβhalf)).mono
      (by intro n hn; exact hn.le)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hPβ
  let N := max 1 N₀
  have hN : 1 ≤ N := le_max_left _ _
  have hPβall : ∀ n, N ≤ n → β ≤ P n := by
    intro n hn
    exact hN₀ n (le_trans (le_max_right _ _) hn)
  have hrec : ∀ n : ℕ, 0 < n →
      P n = (n : ℝ) * F n -
        ∑ r : Fin (n - 1), F (r.val + 1) * P (n - (r.val + 1)) := by
    intro n hn
    exact measureReal_nonnegative_endpoint_recurrence ν hn
  have hconv : ∀ n : ℕ, 0 < n →
      (n : ℝ) * F n = ∑ k : Fin n, F k.val * P (n - k.val) :=
    fun n hn => recurrence_to_convolution F P hF0 hrec hn
  obtain ⟨C, hC, hbound⟩ := Asymptotics.lower_power_of_prefix
    F hFpos hβ hγ hγβ hγ1 N hN
      (fun n hn => prefix_bound_of_convolution F P
        (fun k => (hFpos k).le) hPnonneg hβ.le N hN
        hPβall hconv n hn)
  refine ⟨C, hC, ?_⟩
  intro n
  have h := hbound n
  change C * (((n + 1 : ℕ) : ℝ) ^ (γ - 1)) ≤ F n at h
  rw [show F n = ((iidSequenceLaw ν)
    {increment | SurvivesNonnegative n increment}).toReal from
      finiteSurvivalProbability_eq_infinite ν n] at h
  exact h

end ProbabilityTheory.RandomWalk

end
