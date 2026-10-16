/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingProcess.Offspring.Count
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.KingmanInterface
public import Combinatorics.BranchingWalk.Step.Measurability
public import Mathlib.Probability.BorelCantelli
public import Mathlib.Order.LiminfLimsup
public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

/-!
# Filling an initially smaller selected population

The small-initial-population extension has three dependencies:

1. supercriticality implies a positive chance of at least two children;
2. repeated independent opportunities for this split fill any fixed finite
   capacity in finite time almost surely;
3. the process after the filling time has the law of an exact-`N` process,
   so its asymptotic speed is the one obtained from the Kingman interface.

This file begins with the offspring-count implication. The current speed
environment is indexed by exactly `N` active parents per generation, while
the pre-sampled root-indexed selection process can have a random smaller
population before it fills. The stopping-time identification in item 3 must
be proved against that root-indexed field before the exact-`N` speed theorem
can be applied; no restart hypothesis is introduced here in place of that
proof.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw
open Combinatorics.Branching
open Filter ProbabilityTheory
open scoped Topology

/-- Under supercriticality and almost-surely nonempty offspring, one parent
has positive probability of producing at least two children. -/
theorem positive_measure_childCount_ge_two
    {ι Mark : Type*} [Countable ι] [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (hsupercritical : μ.IsSupercritical)
    (hnonempty : μ.HasAtLeastOneChild) :
    0 < μ.childCountLaw {n | 2 ≤ n} := by
  let ν : Measure ℕ∞ := μ.childCountLaw
  have hnonemptyAE : ∀ᵐ ξ ∂(μ : Measure (Step ι Mark)),
      ξ ∈ nonemptySupport := hasAtLeastOneChild_ae μ hnonempty
  have hcountPos : ∀ᵐ n ∂ν, n ≠ 0 := by
    have hsource : ∀ᵐ ξ ∂(μ : Measure (Step ι Mark)),
        Step.childCount ξ ≠ 0 := by
      filter_upwards [hnonemptyAE] with ξ hξ
      have hsupport : (support ξ).Nonempty := by
        rcases hξ with ⟨i, hi⟩
        exact ⟨i, hi⟩
      change (support ξ).encard ≠ 0
      exact (Set.encard_pos.mpr hsupport).ne'
    have hmap := ae_map_iff (μ := (μ : Measure (Step ι Mark)))
      (Step.childCount_measurable (ι := ι) (X := Mark)).aemeasurable
      (MeasurableSet.singleton (0 : ℕ∞)).compl
    have hsource' : ∀ᵐ ξ ∂(μ : Measure (Step ι Mark)),
        Step.childCount ξ ∈ ({0}ᶜ : Set ℕ∞) := by
      exact hsource.mono fun ξ hξ => by simpa using hξ
    change ∀ᵐ n ∂((μ : Measure (Step ι Mark)).map Step.childCount), n ≠ 0
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq] using
      hmap.mpr hsource'
  by_contra hnotpos
  have hnotpos' : ¬ (0 : ℝ≥0∞) < ν {n | 2 ≤ n} := by
    simpa [ν] using hnotpos
  have hzero : ν {n | 2 ≤ n} = 0 := by
    exact le_antisymm (le_of_not_gt hnotpos') bot_le
  have hsmall : ∀ᵐ n ∂ν, n < 2 := by
    rw [ae_iff]
    simpa only [not_lt] using hzero
  have hone : ∀ᵐ n ∂ν, n = 1 := by
    filter_upwards [hcountPos, hsmall] with n hn hp
    have hle : n ≤ 1 := by simpa using hp
    exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hn)
  have hexpect : μ.expectedChildCount = 1 := by
    change (∫⁻ n : ℕ∞, (n : ℝ≥0∞) ∂ν) = 1
    have hone' : ∀ᵐ n : ℕ∞ ∂ν, (n : ℝ≥0∞) = 1 := by
      exact hone.mono fun n hn => by simp [hn]
    rw [lintegral_congr_ae hone']
    simp
  change 1 < μ.expectedChildCount at hsupercritical
  rw [hexpect] at hsupercritical
  exact (lt_irrefl 1) hsupercritical

private lemma childCount_le_one_of_not_split
    {ι X : Type*} (ξ : Step ι X)
    (hnoSplit : ¬ 2 ≤ Step.childCount ξ) : Step.childCount ξ ≤ 1 := by
  cases hcount : Step.childCount ξ with
  | top => exact (hnoSplit (by simp [hcount])).elim
  | coe n =>
    have hnnot : ¬ 2 ≤ n := by simpa [hcount] using hnoSplit
    have hn : n ≤ 1 := by omega
    simpa [hcount] using hn

/-- Direct raw-law form of the supercritical splitting implication. No
nonemptiness assumption is needed: an expected child count above one forces
positive mass on configurations with at least two children. -/
theorem positive_raw_measure_childCount_ge_two
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) :
    0 < μ {ξ | 2 ≤ Step.childCount ξ} := by
  by_contra hpos
  have hzero : μ {ξ | 2 ≤ Step.childCount ξ} = 0 :=
    nonpos_iff_eq_zero.mp (le_of_not_gt hpos)
  have haeNotSplit : ∀ᵐ ξ ∂μ, ¬ 2 ≤ Step.childCount ξ := by
    simpa only [Set.mem_ofPred_eq] using
      (measure_eq_zero_iff_ae_notMem.mp hzero)
  have haeCountLeOne : ∀ᵐ ξ ∂μ,
      (Step.childCount ξ : ℝ≥0∞) ≤ 1 := by
    filter_upwards [haeNotSplit] with ξ hξ
    exact_mod_cast childCount_le_one_of_not_split ξ hξ
  have hle : (∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) ≤ 1 := by
    calc
      (∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) ≤
          ∫⁻ _ξ, (1 : ℝ≥0∞) ∂μ := lintegral_mono_ae haeCountLeOne
      _ = 1 := by simp
  exact (not_lt_of_ge hle) hsupercritical

private lemma measurable_childCount_ge_two
    {ι X : Type*} [Countable ι] [MeasurableSpace X] :
    MeasurableSet {ξ : Step ι X | 2 ≤ Step.childCount ξ} := by
  have heq : {ξ : Step ι X | 2 ≤ Step.childCount ξ} = nontrivialSupport := by
    ext ξ
    change 2 ≤ (support ξ).encard ↔
      ∃ i j, i ≠ j ∧ survive ξ i ∧ survive ξ j
    constructor
    · intro hcount
      have hcard : 1 < (support ξ).encard :=
        lt_of_lt_of_le (by norm_num : (1 : ℕ∞) < 2) hcount
      obtain ⟨i, j, hi, hj, hij⟩ := Set.one_lt_encard_iff.mp hcard
      exact ⟨i, j, hij, by simpa [support] using hi,
        by simpa [support] using hj⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      have hcard : 1 < (support ξ).encard :=
        Set.one_lt_encard_iff.mpr
          ⟨i, j, by simpa [support] using hi,
            by simpa [support] using hj, hij⟩
      cases hencard : (support ξ).encard with
      | top => simp
      | coe n =>
        have hn : 1 < n := by simpa [hencard] using hcard
        have hn' : 2 ≤ n := by omega
        simpa [hencard] using hn'
  rw [heq]
  exact nontrivialSupport_measurable

/-- A split at the first active rank in generation `n`. The sequence of
these events is independent because it reads disjoint generation coordinates
of the pre-sampled product environment. -/
def firstRankSplitEvent {N : ℕ} (hN : 0 < N) (n : ℕ) :
    Set (GenerationEnvironment N) :=
  {ω | 2 ≤ Step.childCount (ω n (⟨0, hN⟩ : Fin N))}

private def batchFirstRankSplitEvent {N : ℕ} (hN : 0 < N) :
    Set (GenerationBatch N) :=
  {batch | 2 ≤ Step.childCount (batch (⟨0, hN⟩ : Fin N))}

private lemma measurable_batchFirstRankSplitEvent {N : ℕ} (hN : 0 < N) :
    MeasurableSet (batchFirstRankSplitEvent hN) := by
  change MeasurableSet
    {batch : GenerationBatch N |
      2 ≤ Step.childCount (batch (⟨0, hN⟩ : Fin N))}
  exact measurable_childCount_ge_two.preimage
    (measurable_pi_apply (⟨0, hN⟩ : Fin N))

/-- The first-rank split event has the same positive probability in every
generation. -/
theorem firstRankSplitEvent_measure_eq
    {N : ℕ} (hN : 0 < N) (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) :
    generationEnvironmentLaw μ N (firstRankSplitEvent hN n) =
      μ {ξ | 2 ≤ Step.childCount ξ} := by
  let E := batchFirstRankSplitEvent hN
  let evalGen : GenerationEnvironment N → GenerationBatch N := fun ω => ω n
  let evalRank : GenerationBatch N → Step ℕ ℝ :=
    fun batch => batch (⟨0, hN⟩ : Fin N)
  have hE : MeasurableSet E := measurable_batchFirstRankSplitEvent hN
  have hEvalGen : Measurable evalGen := measurable_pi_apply n
  have hEvalRank : Measurable evalRank := measurable_pi_apply (⟨0, hN⟩ : Fin N)
  have hfirst : generationEnvironmentLaw μ N (firstRankSplitEvent hN n) =
      (generationEnvironmentLaw μ N).map evalGen E := by
    rw [Measure.map_apply hEvalGen hE]
    rfl
  have hsecond :
      (generationEnvironmentLaw μ N).map evalGen E =
        generationBatchLaw μ N E := by
    exact congrArg (fun ν : Measure (GenerationBatch N) => ν E)
      (generationEnvironmentLaw_generation_marginal μ N n)
  have hthird :
      generationBatchLaw μ N E =
        μ {ξ | 2 ≤ Step.childCount ξ} := by
    have hrawEvent : MeasurableSet
        {ξ : Step ℕ ℝ | 2 ≤ Step.childCount ξ} := by
      exact measurable_childCount_ge_two
    have heq : E = evalRank ⁻¹' {ξ : Step ℕ ℝ |
        2 ≤ Step.childCount ξ} := by
      ext batch
      rfl
    rw [heq, ← Measure.map_apply hEvalRank hrawEvent,
      generationBatchLaw_parent_marginal μ (⟨0, hN⟩ : Fin N)]
  exact hfirst.trans (hsecond.trans hthird)

/-- Under supercriticality, the pre-sampled first-rank offspring marks split
infinitely often in an `N`-generation environment. This concerns the marks;
linking them to a still-active parent in a smaller population requires the
separate population-growth argument. -/
theorem ae_frequently_firstRankSplitEvent
    {N : ℕ} (hN : 0 < N) (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ]
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) :
    ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      ∃ᶠ n in atTop, ω ∈ firstRankSplitEvent hN n := by
  have hsplitRaw := positive_raw_measure_childCount_ge_two μ hsupercritical
  let ν := generationEnvironmentLaw μ N
  have hν : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  let events : ℕ → Set (GenerationEnvironment N) :=
    fun n => firstRankSplitEvent hN n
  let coordinate : ℕ → MeasurableSpace (GenerationEnvironment N) :=
    generationCoordinateSigma
  have hcoordinateIndep : iIndep coordinate ν := by
    apply (iIndepFun_iff_iIndep
      (fun _ : ℕ => (inferInstance : MeasurableSpace (GenerationBatch N)))
      (fun (n : ℕ) (ω : GenerationEnvironment N) => ω n) ν).mp
    exact generationEnvironmentLaw_generations_independent μ N
  have heventMeasurable : ∀ n, MeasurableSet[coordinate n] (events n) := by
    intro n
    let evalGen : GenerationEnvironment N → GenerationBatch N := fun ω => ω n
    have hE : MeasurableSet (batchFirstRankSplitEvent hN) :=
      measurable_batchFirstRankSplitEvent hN
    have heq : events n = evalGen ⁻¹' batchFirstRankSplitEvent hN := by
      ext ω
      rfl
    rw [heq]
    change MeasurableSet[
      (inferInstance : MeasurableSpace (GenerationBatch N)).comap evalGen]
      (evalGen ⁻¹' batchFirstRankSplitEvent hN)
    exact ⟨batchFirstRankSplitEvent hN, hE, rfl⟩
  have heventsMeasurable : ∀ n, MeasurableSet (events n) := by
    intro n
    change MeasurableSet
      {ω : GenerationEnvironment N |
        2 ≤ Step.childCount (ω n (⟨0, hN⟩ : Fin N))}
    exact measurable_childCount_ge_two.preimage
      ((measurable_pi_apply (⟨0, hN⟩ : Fin N)).comp
        (measurable_pi_apply n))
  have heventsIndep : iIndepSet events ν := by
    rw [iIndepSet_iff_iIndep]
    apply iIndep_of_iIndep_of_le hcoordinateIndep
    intro n
    exact MeasurableSpace.generateFrom_le fun s hs => by
      have hs' : s = events n := by simpa using hs
      rw [hs']
      exact heventMeasurable n
  have hprob : ∀ n, ν (events n) = μ {ξ | 2 ≤ Step.childCount ξ} :=
    firstRankSplitEvent_measure_eq hN μ
  have hsum : (∑' n : ℕ, ν (events n)) = ∞ := by
    simpa only [hprob] using
      (ENNReal.tsum_const_eq_top_of_ne_zero hsplitRaw.ne')
  have hBC := ProbabilityTheory.measure_limsup_eq_one
    heventsMeasurable heventsIndep hsum
  have hlimsupMeasurable : MeasurableSet (Filter.limsup events atTop) := by
    rw [limsup_eq_iInf_iSup_of_nat']
    exact MeasurableSet.iInter (fun n =>
      MeasurableSet.iUnion (fun k => heventsMeasurable (k + n)))
  have hae : ∀ᵐ ω ∂ν, ω ∈ Filter.limsup events atTop :=
    (ae_mem_iff_measure_eq
      hlimsupMeasurable.nullMeasurableSet).2 (by
        simpa using hBC)
  filter_upwards [hae] with ω hω
  simpa [events, Filter.mem_limsup_iff_frequently_mem] using hω

/-- A bounded nondecreasing population count reaches its finite capacity if
each split at a time with fewer than `N` particles strictly increases the
count, and splits occur frequently. This is the deterministic saturation
step needed after identifying the rank-zero split events with those of the
actual selected population. -/
theorem exists_eq_capacity_of_frequently_growing
    {N : ℕ} (populationSize : ℕ → ℕ) (split : ℕ → Prop)
    (hinitial : 0 < populationSize 0)
    (hcapacity : ∀ n, populationSize n ≤ N)
    (hmonotone : ∀ n, populationSize n ≤ populationSize (n + 1))
    (hgrowth : ∀ n, 0 < populationSize n → populationSize n < N →
      split n → populationSize n < populationSize (n + 1))
    (hfrequently : ∃ᶠ n in atTop, split n) :
    ∃ n, populationSize n = N := by
  have hmono : ∀ {m n}, m ≤ n → populationSize m ≤ populationSize n := by
    intro m n hmn
    induction hmn with
    | refl => exact le_rfl
    | @step n hmn ih =>
        exact le_trans ih (hmonotone n)
  have hpositive : ∀ n, 0 < populationSize n := by
    intro n
    exact lt_of_lt_of_le hinitial (hmono (Nat.zero_le n))
  have hreach : ∀ q, q ≤ N → ∃ n, q ≤ populationSize n := by
    intro q
    induction q with
    | zero =>
        intro _
        exact ⟨0, Nat.zero_le _⟩
    | succ q ih =>
        intro hq
        have hqN : q ≤ N := Nat.le_trans (Nat.le_succ q) hq
        obtain ⟨n, hn⟩ := ih hqN
        by_cases htarget : q + 1 ≤ populationSize n
        · exact ⟨n, htarget⟩
        · have hcurrent : populationSize n = q := by omega
          obtain ⟨m, hsplit, hnm⟩ :=
            (hfrequently.and_eventually (eventually_ge_atTop n)).exists
          have hge : q ≤ populationSize m := by
            exact hn.trans (hmono hnm)
          by_cases htargetAtM : q + 1 ≤ populationSize m
          · exact ⟨m, htargetAtM⟩
          · have hcurrentAtM : populationSize m = q := by omega
            have hqLtN : q < N := by omega
            have hnext := hgrowth m (hpositive m) (by omega) hsplit
            refine ⟨m + 1, ?_⟩
            omega
  obtain ⟨n, hn⟩ := hreach N le_rfl
  exact ⟨n, le_antisymm (hcapacity n) hn⟩

/-- For a fixed good `N`-slot environment, the leftmost rank has the same
asymptotic speed from every finite initial position vector as from the
origin. Coordinatewise monotonicity sandwiches the trajectory between two
constant translates of the origin trajectory. -/
theorem infiniteOffspringRun_rankZero_hasAsymptoticSpeed_of_initial
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) (c : ℝ)
    (horigin : Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
      (𝕜 := ℝ)
      (fun n => infiniteOffspringRun offspring hgood (fun _ => 0) n
        (⟨0, hN⟩ : Fin N)) c) :
    Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
      (𝕜 := ℝ)
      (fun n => infiniteOffspringRun offspring hgood initial n
        (⟨0, hN⟩ : Fin N)) c := by
  let origin : Fin N := ⟨0, hN⟩
  let K : ℝ := ∑ i : Fin N, |initial i|
  let zeroRun : ℕ → Fin N → ℝ :=
    infiniteOffspringRun offspring hgood (fun _ => 0)
  let initialRun : ℕ → Fin N → ℝ :=
    infiniteOffspringRun offspring hgood initial
  let scaledZero : ℕ → ℝ := fun n =>
    ((n + 1 : ℕ) : ℝ)⁻¹ * zeroRun (n + 1) origin
  let scaledInitial : ℕ → ℝ := fun n =>
    ((n + 1 : ℕ) : ℝ)⁻¹ * initialRun (n + 1) origin
  let scaledLow : ℕ → ℝ := fun n =>
    ((n + 1 : ℕ) : ℝ)⁻¹ * (zeroRun (n + 1) origin - K)
  let scaledHigh : ℕ → ℝ := fun n =>
    ((n + 1 : ℕ) : ℝ)⁻¹ * (zeroRun (n + 1) origin + K)
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact Finset.sum_nonneg fun i _ => abs_nonneg (initial i)
  have hKbound (i : Fin N) : |initial i| ≤ K := by
    dsimp [K]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (initial j))
      (Finset.mem_univ i)
  have hinitialBounds (i : Fin N) : -K ≤ initial i ∧ initial i ≤ K := by
    exact abs_le.mp (hKbound i)
  have hlowMono := infiniteOffspringRun_mono_initial offspring hgood
    (fun _ => -K) initial (fun i => (hinitialBounds i).1)
  have hhighMono := infiniteOffspringRun_mono_initial offspring hgood
    initial (fun _ => K) (fun i => (hinitialBounds i).2)
  have hlowShift : ∀ n,
      infiniteOffspringRun offspring hgood (fun _ => -K) n =
        fun i => zeroRun n i - K := by
    intro n
    simpa [zeroRun, sub_eq_add_neg] using
      infiniteOffspringRun_shift offspring hgood (fun _ => 0) (-K) n
  have hhighShift : ∀ n,
      infiniteOffspringRun offspring hgood (fun _ => K) n =
        fun i => zeroRun n i + K := by
    intro n
    simpa [zeroRun] using
      infiniteOffspringRun_shift offspring hgood (fun _ => 0) K n
  have hzeroSucc : Tendsto scaledZero atTop (𝓝 c) := by
    exact Combinatorics.Branching.Selection.NSelection.hasAsymptoticSpeed_iff_succ
      _ _ |>.1 horigin
  have hreciprocal : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hscaledK : Tendsto (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ)⁻¹ * K) atTop (𝓝 0) := by
    simpa using hreciprocal.mul_const K
  have hlowLimit : Tendsto scaledLow atTop (𝓝 c) := by
    have h := hzeroSucc.sub hscaledK
    simpa [scaledLow, scaledZero, mul_sub] using h
  have hhighLimit : Tendsto scaledHigh atTop (𝓝 c) := by
    have h := hzeroSucc.add hscaledK
    simpa [scaledHigh, scaledZero, mul_add] using h
  have hlowBound (n : ℕ) : scaledLow n ≤ scaledInitial n := by
    have hpos : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hrun := hlowMono (n + 1) origin
    have hrun' : zeroRun (n + 1) origin - K ≤ initialRun (n + 1) origin := by
      rw [hlowShift (n + 1)] at hrun
      simpa [zeroRun, initialRun] using hrun
    simpa [scaledLow, scaledInitial, zeroRun, initialRun, mul_sub] using
      (mul_le_mul_of_nonneg_left hrun' hpos)
  have hhighBound (n : ℕ) : scaledInitial n ≤ scaledHigh n := by
    have hpos : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hrun := hhighMono (n + 1) origin
    have hrun' : initialRun (n + 1) origin ≤ zeroRun (n + 1) origin + K := by
      rw [hhighShift (n + 1)] at hrun
      simpa [zeroRun, initialRun] using hrun
    simpa [scaledHigh, scaledInitial, zeroRun, initialRun, mul_add] using
      (mul_le_mul_of_nonneg_left hrun' hpos)
  have hscaledInitial : Tendsto scaledInitial atTop (𝓝 c) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlowLimit hhighLimit (Eventually.of_forall hlowBound)
      (Eventually.of_forall hhighBound)
  exact Combinatorics.Branching.Selection.NSelection.hasAsymptoticSpeed_iff_succ
    _ _ |>.2 hscaledInitial

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
