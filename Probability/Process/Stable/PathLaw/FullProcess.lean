/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.PathLaw.Concatenation
public import Mathlib.Probability.Independence.Process.Basic

/-!
# Full-time stable processes from unit-time path laws

This file builds the independent-increment part of the full-time process by
concatenating iid unit-time path blocks. The block product is Mathlib's
`Measure.infinitePi`; blockwise and within-block independence are combined
using Mathlib's process-independence APIs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory

private noncomputable def unitBlockGrid {n : ℕ} (t : Fin (n + 1) → ℝ≥0) (k : ℕ) :
    Fin (n + 1) → unitInterval := fun i => Topology.unitBlockParameter k (t i)

private noncomputable def unitBlockIncrement {n : ℕ} (t : Fin (n + 1) → ℝ≥0)
    (k : ℕ) (i : Fin n) (ω : ℕ → CadlagPath unitInterval ℝ) : ℝ :=
  ω k (unitBlockGrid t k i.succ) - ω k (unitBlockGrid t k i.castSucc)

private theorem measurable_unitBlockIncrement {n : ℕ}
    (t : Fin (n + 1) → ℝ≥0) (k : ℕ) (i : Fin n) :
    Measurable (unitBlockIncrement t k i) := by
  exact ((Skorokhod.measurable_apply (unitBlockGrid t k i.succ)).comp
    (measurable_pi_apply k)).sub
      ((Skorokhod.measurable_apply (unitBlockGrid t k i.castSucc)).comp
        (measurable_pi_apply k))

private theorem measurable_unitBlockIncrementVector {n : ℕ}
    (t : Fin (n + 1) → ℝ≥0) (k : ℕ) :
    Measurable (fun ω : ℕ → CadlagPath unitInterval ℝ =>
      fun i : Fin n => unitBlockIncrement t k i ω) := by
  exact measurable_pi_iff.mpr fun i => measurable_unitBlockIncrement t k i

/-- For any nonnegative finite increasing mesh, increments of the
concatenated process are independent. Each elementary coordinate is indexed
by a block and a mesh interval; Mathlib's `iIndepFun_uncurry` flattens the
two independence levels, and `iIndepFun_process` then regroups by global
interval before taking the finite block sums. -/
theorem iidUnitPathBlockProcess_hasIndepIncrements
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P) :
    HasIndepIncrements
      (fun t ω => iidUnitPathBlockProcess ω t) (iidUnitPathBlockLaw P) := by
  intro n t ht
  let Q := iidUnitPathBlockLaw P
  have hμ : IsProbabilityMeasure μ := hP.strictlyStable.isProbabilityMeasure
  letI : IsProbabilityMeasure μ := hμ
  letI : IsProbabilityMeasure Q := iidUnitPathBlockLaw_isProbabilityMeasure P
  let blockVector : ℕ → (CadlagPath unitInterval ℝ) → (Fin n → ℝ) :=
    fun k f i => f (unitBlockGrid t k i.succ) - f (unitBlockGrid t k i.castSucc)
  have houter : iIndepFun
      (fun k : ℕ => fun ω : ℕ → CadlagPath unitInterval ℝ => blockVector k (ω k)) Q := by
    exact iIndepFun_infinitePi (P := fun _ : ℕ => P)
      (X := blockVector) (fun k => by
        apply measurable_pi_iff.mpr
        intro i
        exact (Skorokhod.measurable_apply (unitBlockGrid t k i.succ)).sub
          (Skorokhod.measurable_apply (unitBlockGrid t k i.castSucc)))
  have hwithin (k : ℕ) : iIndepFun
      (fun i : Fin n => fun ω : ℕ → CadlagPath unitInterval ℝ =>
        unitBlockIncrement t k i ω) Q := by
    have hgrid : Monotone (unitBlockGrid t k) :=
      Topology.monotone_unitBlockParameter k |>.comp ht
    have hlaw := hP.increments_hasLaw_pi n (unitBlockGrid t k) hgrid
    let coordLaw : Fin n → Measure ℝ := fun i =>
      stableTimeLaw α μ
        ((unitBlockGrid t k i.succ : unitInterval) -
          (unitBlockGrid t k i.castSucc : unitInterval))
    have hlaw' : HasLaw (blockVector k) (Measure.pi coordLaw) P := by
      simpa [blockVector, coordLaw, unitBlockIncrement, UnitInterval.clock,
        stableTimeLaw] using hlaw
    have heval : HasLaw (fun ω : ℕ → CadlagPath unitInterval ℝ => ω k) P Q :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => P) k).hasLaw
    have hvectorLaw : HasLaw
        (fun ω : ℕ → CadlagPath unitInterval ℝ => blockVector k (ω k))
        (Measure.pi coordLaw) Q :=
      HasLaw.comp_of_hasLaw_comp (measurable_pi_iff.mpr fun i => by
        exact (Skorokhod.measurable_apply (unitBlockGrid t k i.succ)).sub
          (Skorokhod.measurable_apply (unitBlockGrid t k i.castSucc))).aemeasurable
        HasLaw.id heval hlaw'
    have hcoordProb (i : Fin n) : IsProbabilityMeasure (coordLaw i) := by
      dsimp [coordLaw, stableTimeLaw]
      infer_instance
    letI : ∀ i : Fin n, IsProbabilityMeasure (coordLaw i) := hcoordProb
    have hcoordinate (i : Fin n) : HasLaw
        (fun ω : ℕ → CadlagPath unitInterval ℝ => unitBlockIncrement t k i ω)
        (coordLaw i) Q := by
      have hevalCoord := MeasureTheory.measurePreserving_eval coordLaw i
      have hcoord := hevalCoord.comp_hasLaw hvectorLaw
      have hfun : (fun ω : ℕ → CadlagPath unitInterval ℝ =>
          unitBlockIncrement t k i ω) =ᵐ[Q]
          Function.eval i ∘ (fun ω => blockVector k (ω k)) := by
        exact ae_of_all _ fun ω => by funext; rfl
      exact hcoord.congr hfun
    simpa [Q, unitBlockIncrement, blockVector, coordLaw] using
      (iIndepFun_iff_hasLaw_pi_pi hcoordinate).2 hvectorLaw
  have hflat : iIndepFun
      (fun p : Σ k : ℕ, Fin n => fun ω : ℕ → CadlagPath unitInterval ℝ =>
        unitBlockIncrement t p.1 p.2 ω) Q := by
    exact iIndepFun_uncurry
      (X := fun k i ω => unitBlockIncrement t k i ω)
      (by intro k i; exact measurable_unitBlockIncrement t k i)
      houter hwithin
  have hgroup : iIndepFun
      (fun i : Fin n => fun ω : ℕ → CadlagPath unitInterval ℝ =>
        fun k : ℕ => unitBlockIncrement t k i ω) Q := by
    refine iIndepFun.iIndepFun_process
      (X := fun i k ω => unitBlockIncrement t k i ω)
      (by intro i k; exact measurable_unitBlockIncrement t k i) ?_
    intro I J
    let Pair := (Σ i : I, J i)
    let swap : Pair → (Σ k : ℕ, Fin n) := fun p => ⟨p.2, p.1.1⟩
    have hswap : Function.Injective swap := by
      intro a b hab
      cases a with
      | mk ai ak =>
        cases b with
        | mk bi bk =>
          simp only [swap, Sigma.mk.injEq] at hab
          have hai : ai = bi := Subtype.ext (eq_of_heq hab.2)
          subst bi
          have hak : ak = bk := Subtype.ext hab.1
          subst bk
          rfl
    have hpair : iIndepFun
        (fun p : Pair => fun ω : ℕ → CadlagPath unitInterval ℝ =>
          unitBlockIncrement t p.2 p.1.1 ω) Q := by
      simpa [swap] using hflat.precomp hswap
    let coordLaw : Pair → Measure ℝ := fun p =>
      Q.map (unitBlockIncrement t p.2 p.1.1)
    have hcoordProb (p : Pair) : IsProbabilityMeasure (coordLaw p) := by
      dsimp [coordLaw]
      exact Measure.isProbabilityMeasure_map_iff
        (measurable_unitBlockIncrement t p.2 p.1.1).aemeasurable |>.2 inferInstance
    letI : ∀ p : Pair, IsProbabilityMeasure (coordLaw p) := hcoordProb
    have hpairLaw : HasLaw
        (fun ω : ℕ → CadlagPath unitInterval ℝ =>
          fun p : Pair => unitBlockIncrement t p.2 p.1.1 ω)
        (Measure.pi coordLaw) Q :=
      hpair.hasLaw_pi (fun p => hasLaw_map
        (measurable_unitBlockIncrement t p.2 p.1.1).aemeasurable)
    let E : ((p : Pair) → ℝ) ≃ᵐ ((i : I) → (j : J i) → ℝ) :=
      MeasurableEquiv.piCurry (fun _ _ => ℝ)
    have hgroupMeasure :
        (Measure.pi coordLaw).map E =
          Measure.pi (fun i : I => Measure.pi (fun j : J i => coordLaw ⟨i, j⟩)) := by
      calc
        (Measure.pi coordLaw).map E =
            (Measure.infinitePi coordLaw).map E := by
          rw [← Measure.infinitePi_eq_pi]
        _ = Measure.infinitePi (fun i : I =>
              Measure.infinitePi (fun j : J i => coordLaw ⟨i, j⟩)) := by
          exact Measure.infinitePi_map_piCurry
            (μ := fun i j => coordLaw ⟨i, j⟩) (X := fun _ _ => ℝ)
        _ = Measure.pi (fun i : I => Measure.pi (fun j : J i => coordLaw ⟨i, j⟩)) := by
          simp_rw [Measure.infinitePi_eq_pi]
    have hcurriedLaw : HasLaw
        (fun ω : ℕ → CadlagPath unitInterval ℝ =>
          fun i : I => fun j : J i => unitBlockIncrement t j i.1 ω)
        (Measure.pi (fun i : I => Measure.pi (fun j : J i => coordLaw ⟨i, j⟩))) Q := by
      let hpres : MeasurePreserving E (Measure.pi coordLaw)
          (Measure.pi (fun i : I => Measure.pi (fun j : J i => coordLaw ⟨i, j⟩))) :=
        ⟨E.measurable, hgroupMeasure⟩
      have h := hpres.comp_hasLaw hpairLaw
      have hfun : (fun ω => E (fun p : Pair =>
          unitBlockIncrement t p.2 p.1.1 ω)) =ᵐ[Q]
          (fun ω i j => unitBlockIncrement t j i.1 ω) := by
        exact ae_of_all _ fun ω => by funext i j; rfl
      exact h.congr hfun
    have hgroupCoordinateLaw (i : I) : HasLaw
        (fun ω : ℕ → CadlagPath unitInterval ℝ =>
          fun j : J i => unitBlockIncrement t j i.1 ω)
        (Measure.pi (fun j : J i => coordLaw ⟨i, j⟩)) Q := by
      let includeIndex : J i → Pair := fun j => ⟨i, j⟩
      have hinj : Function.Injective includeIndex := by
        intro a b hab
        cases hab
        rfl
      have hind := hpair.precomp hinj
      have hind' : iIndepFun
          (fun j : J i => fun ω : ℕ → CadlagPath unitInterval ℝ =>
            unitBlockIncrement t j i.1 ω) Q := by
        simpa [includeIndex] using hind
      exact hind'.hasLaw_pi (fun j => hasLaw_map
        (measurable_unitBlockIncrement t j i.1).aemeasurable)
    apply (iIndepFun_iff_hasLaw_pi_pi hgroupCoordinateLaw).2
    simpa using hcurriedLaw
  let sumBlocks : Fin n → (ℕ → ℝ) → ℝ := fun i x =>
    ∑ k ∈ Finset.range (Nat.floor (t i.succ : ℝ) + 1), x k
  have hsumMeas (i : Fin n) : Measurable (sumBlocks i) := by
    exact Finset.measurable_sum
      (Finset.range (Nat.floor (t i.succ : ℝ) + 1)) (by
        intro k hk
        exact measurable_pi_apply k)
  have hglobal : iIndepFun
      (fun i : Fin n => fun ω : ℕ → CadlagPath unitInterval ℝ =>
        sumBlocks i (fun k => unitBlockIncrement t k i ω)) Q :=
    hgroup.comp sumBlocks hsumMeas
  have hstarts := iidUnitPathBlockLaw_ae_blocks_start_eq_zero hP
  have hEq (i : Fin n) :
      (fun ω : ℕ → CadlagPath unitInterval ℝ =>
        iidUnitPathBlockProcess ω (t i.succ) - iidUnitPathBlockProcess ω (t i.castSucc)) =ᵐ[Q]
      (fun ω => sumBlocks i (fun k => unitBlockIncrement t k i ω)) := by
    filter_upwards [hstarts] with ω hω
    change Topology.concatenateUnitPaths ω (t i.succ) -
        Topology.concatenateUnitPaths ω (t i.castSucc) = _
    rw [Topology.concatenateUnitPaths_increment_eq_sum ω hω
      (ht (Fin.castSucc_le_succ i))]
    rfl
  exact (iIndepFun.congr (fun i => (hEq i).symm)) hglobal

private noncomputable def unitBlockTimeDuration (s t : ℝ≥0) (k : ℕ) : ℝ :=
  (Topology.unitBlockParameter k t : ℝ) - (Topology.unitBlockParameter k s : ℝ)

private theorem measurable_unitBlockTimeIncrement
    (s t : ℝ≥0) (k : ℕ) :
    Measurable (fun ω : ℕ → CadlagPath unitInterval ℝ =>
      ω k (Topology.unitBlockParameter k t) - ω k (Topology.unitBlockParameter k s)) := by
  exact ((Skorokhod.measurable_apply (Topology.unitBlockParameter k t)).comp
      (measurable_pi_apply k)).sub
    ((Skorokhod.measurable_apply (Topology.unitBlockParameter k s)).comp
      (measurable_pi_apply k))

/-- The increment of the concatenated process over an arbitrary time interval
has the stable law at the elapsed time. Each unit block contributes an
independent stable increment; the stable convolution semigroup and the exact
sum of clamped block durations combine these contributions. -/
theorem iidUnitPathBlockProcess_increment_hasLaw
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw
      (fun ω : ℕ → CadlagPath unitInterval ℝ =>
        iidUnitPathBlockProcess ω t - iidUnitPathBlockProcess ω s)
      (stableTimeLaw α μ ((t : ℝ) - (s : ℝ)))
      (iidUnitPathBlockLaw P) := by
  let Q := iidUnitPathBlockLaw P
  let delta : ℕ → ℝ := unitBlockTimeDuration s t
  let blockIncrement : ℕ → (ℕ → CadlagPath unitInterval ℝ) → ℝ := fun k ω =>
    ω k (Topology.unitBlockParameter k t) - ω k (Topology.unitBlockParameter k s)
  let blocks := Finset.range (Nat.floor (t : ℝ) + 1)
  have hStable := hP.strictlyStable
  have hμ : IsProbabilityMeasure μ := hStable.isProbabilityMeasure
  letI : IsProbabilityMeasure μ := hμ
  letI : IsProbabilityMeasure Q := iidUnitPathBlockLaw_isProbabilityMeasure P
  have hblockIndep : iIndepFun blockIncrement Q := by
    exact iIndepFun_infinitePi (P := fun _ : ℕ => P)
      (X := fun k f => f (Topology.unitBlockParameter k t) -
        f (Topology.unitBlockParameter k s)) (fun k => by
          exact (Skorokhod.measurable_apply (Topology.unitBlockParameter k t)).sub
            (Skorokhod.measurable_apply (Topology.unitBlockParameter k s)))
  have hblockMeas (k : ℕ) : Measurable (blockIncrement k) := by
    exact measurable_unitBlockTimeIncrement s t k
  have hduration_nonneg (k : ℕ) : 0 ≤ delta k := by
    dsimp [delta, unitBlockTimeDuration]
    apply sub_nonneg.mpr
    exact_mod_cast (Topology.monotone_unitBlockParameter k hst)
  have hblockLaw (k : ℕ) : HasLaw (blockIncrement k)
      (stableTimeLaw α μ (delta k)) Q := by
    have hu : Topology.unitBlockParameter k s ≤ Topology.unitBlockParameter k t :=
      Topology.monotone_unitBlockParameter k hst
    have hsingle := hP.increment_hasLaw
      (Topology.unitBlockParameter k s) (Topology.unitBlockParameter k t) hu
    have heval : MeasurePreserving (Function.eval k) Q P := by
      dsimp [Q, iidUnitPathBlockLaw]
      exact measurePreserving_eval_infinitePi (fun _ : ℕ => P) k
    have hlaw := hsingle.fun_comp heval.hasLaw
    have hfun : blockIncrement k =ᵐ[Q]
        (fun ω => (fun f : CadlagPath unitInterval ℝ =>
          f (Topology.unitBlockParameter k t) - f (Topology.unitBlockParameter k s))
            (ω k)) := by
      exact ae_of_all _ fun _ => rfl
    have hlaw' := hlaw.congr hfun
    convert hlaw' using 1 <;> simp [delta, unitBlockTimeDuration,
      stableTimeLaw, UnitInterval.clock]
  have hsumLaw (m : ℕ) :
      HasLaw (∑ k ∈ Finset.range m, blockIncrement k)
        (stableTimeLaw α μ (∑ k ∈ Finset.range m, delta k)) Q := by
    induction m with
    | zero =>
        have hzero : HasLaw
            (0 : (ℕ → CadlagPath unitInterval ℝ) → ℝ)
            (Measure.dirac 0) Q := by
          exact hasLaw_dirac_of_ae_eq (ae_of_all _ fun _ => by simp)
        simp only [Finset.range_zero, Finset.sum_empty]
        rw [hStable.stableTimeLaw_zero]
        exact hzero
    | succ m ih =>
        letI : IsProbabilityMeasure (stableTimeLaw α μ
            (∑ k ∈ Finset.range m, delta k)) := by
          dsimp [stableTimeLaw]
          infer_instance
        letI : IsProbabilityMeasure (stableTimeLaw α μ (delta m)) := by
          dsimp [stableTimeLaw]
          infer_instance
        have hprefixIndep : IndepFun
            (∑ k ∈ Finset.range m, blockIncrement k)
            (blockIncrement m) Q :=
          hblockIndep.indepFun_finsetSum_of_notMem hblockMeas
            (s := Finset.range m) (i := m) (by simp)
        have hadd := hprefixIndep.hasLaw_add ih (hblockLaw m)
        have htime : (∑ k ∈ Finset.range (m + 1), delta k) =
            (∑ k ∈ Finset.range m, delta k) + delta m := by
          simp [Finset.sum_range_succ]
        have hconv := hStable.stableTimeLaw_conv_nonneg
          (s := ∑ k ∈ Finset.range m, delta k) (t := delta m)
          (Finset.sum_nonneg (s := Finset.range m) (f := delta)
            (fun k hk => hduration_nonneg k))
          (hduration_nonneg m)
        rw [htime, ← hconv]
        have hfun : (∑ k ∈ Finset.range (m + 1), blockIncrement k) =
            (∑ k ∈ Finset.range m, blockIncrement k) + blockIncrement m := by
          ext ω
          simp [Finset.sum_range_succ]
        exact hadd.congr (ae_of_all _ fun ω => congrFun hfun ω)
  have htotalDuration : (∑ k ∈ blocks, delta k) = (t : ℝ) - (s : ℝ) := by
    exact Topology.sum_unitBlockParameter_increment_eq_time_sub hst
  have hsumLaw' := hsumLaw (Nat.floor (t : ℝ) + 1)
  rw [htotalDuration] at hsumLaw'
  have hstarts := iidUnitPathBlockLaw_ae_blocks_start_eq_zero hP
  have hprocessEq :
      (fun ω => iidUnitPathBlockProcess ω t - iidUnitPathBlockProcess ω s) =ᵐ[Q]
        (fun ω => ∑ k ∈ blocks, blockIncrement k ω) := by
    filter_upwards [hstarts] with ω hω
    change Topology.concatenateUnitPaths ω t - Topology.concatenateUnitPaths ω s = _
    rw [Topology.concatenateUnitPaths_increment_eq_sum ω hω hst]
  have hsumLawPointwise :
      HasLaw (fun ω => ∑ k ∈ blocks, blockIncrement k ω)
        (stableTimeLaw α μ ((t : ℝ) - (s : ℝ))) Q := by
    have hfun : (fun ω => ∑ k ∈ blocks, blockIncrement k ω) =
        ∑ k ∈ blocks, blockIncrement k := by
      ext ω
      simp
    exact hsumLaw'.congr (ae_of_all _ fun ω => congrFun hfun ω)
  exact hsumLawPointwise.congr hprocessEq

/-- An iid concatenation of a unit-interval stable path law is an actual
full-time stable Lévy process, without an externally supplied process
witness. -/
theorem iidUnitPathBlockProcess_isStableLevyProcess
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P) :
    IsStableLevyProcess α μ
      (fun t ω => iidUnitPathBlockProcess ω t) (iidUnitPathBlockLaw P) := by
  let Q := iidUnitPathBlockLaw P
  let X : ℝ≥0 → (ℕ → CadlagPath unitInterval ℝ) → ℝ :=
    fun t ω => iidUnitPathBlockProcess ω t
  have hStable := hP.strictlyStable
  have hμ : IsProbabilityMeasure μ := hStable.isProbabilityMeasure
  letI : IsProbabilityMeasure μ := hμ
  letI : IsProbabilityMeasure Q := iidUnitPathBlockLaw_isProbabilityMeasure P
  have hinc : HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ)) X Q := by
    refine ⟨hStable, ?_, ?_, ?_, ?_, ?_⟩
    · intro s t hst
      exact_mod_cast hst
    · rfl
    · exact iidUnitPathBlockProcess_ae_start_eq_zero hP
    · exact iidUnitPathBlockProcess_hasIndepIncrements hP
    · intro s t hst
      exact iidUnitPathBlockProcess_increment_hasLaw hP s t hst
  change IsStableClockProcess α μ (fun t : ℝ≥0 => (t : ℝ)) X Q
  exact ⟨hinc, iidUnitPathBlockProcess_ae_cadlag P⟩

/-- Every finite monotone time mesh of the concatenated process has the
product law of stable increments at the corresponding elapsed times. -/
theorem iidUnitPathBlockProcess_increments_hasLaw_pi
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    HasLaw
      (fun ω (i : Fin n) =>
        iidUnitPathBlockProcess ω (t i.succ) -
          iidUnitPathBlockProcess ω (t i.castSucc))
      (Measure.pi fun i : Fin n =>
        stableTimeLaw α μ ((t i.succ : ℝ) - (t i.castSucc : ℝ)))
      (iidUnitPathBlockLaw P) := by
  have hfull := iidUnitPathBlockProcess_isStableLevyProcess hP
  simpa [stableTimeLaw] using
    hfull.increments.increments_hasLaw_pi n t ht

/-- The full-time concatenation restricts back to its input unit-interval
path law. -/
theorem iidUnitPathBlockProcess_isStableLevyProcess_unitIntervalPathLaw_eq
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P) :
    (iidUnitPathBlockProcess_isStableLevyProcess hP).unitIntervalPathLaw =
      ⟨P, inferInstance⟩ := by
  apply Subtype.ext
  exact ProbabilityTheory.iidUnitPathBlockProcess_unitIntervalPathLaw_eq hP

end ProbabilityTheory

end
