/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Data.Finset.Sort
public import Probability.Process.Stable.PathLaw.UnitInterval
public import Probability.Process.RandomWalk.FunctionalLimit.Stable.PathFiniteDimensionalSource
public import Topology.Cadlag.Concatenation

/-!
# Concatenating independent unit-time stable path blocks

This file constructs the canonical probability space of iid unit-interval
path blocks and the càdlàg process obtained by concatenating them. It also
records the unit-interval consistency interface needed for the converse
direction from a unit-time path law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory

/-- The product probability space carrying iid copies of a unit-interval
path law. The product is Mathlib's `Measure.infinitePi`. -/
noncomputable def iidUnitPathBlockLaw
    (P : Measure (CadlagPath unitInterval ℝ)) :
    Measure (ℕ → CadlagPath unitInterval ℝ) :=
  Measure.infinitePi fun _ : ℕ => P

instance iidUnitPathBlockLaw_isProbabilityMeasure
    (P : Measure (CadlagPath unitInterval ℝ)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (iidUnitPathBlockLaw P) := by
  unfold iidUnitPathBlockLaw
  infer_instance

/-- Concatenate iid unit-time path blocks into a process on nonnegative time.
At integer times the next block supplies the right-hand value. -/
noncomputable def iidUnitPathBlockProcess
    (ω : ℕ → CadlagPath unitInterval ℝ) (t : ℝ≥0) : ℝ :=
  Topology.concatenateUnitPaths ω t

theorem iidUnitPathBlockProcess_ae_cadlag
    (P : Measure (CadlagPath unitInterval ℝ)) [IsProbabilityMeasure P] :
    ∀ᵐ ω ∂iidUnitPathBlockLaw P,
      IsCadlag (fun t : ℝ≥0 => iidUnitPathBlockProcess ω t) := by
  filter_upwards [] with ω
  exact Topology.isCadlag_concatenateUnitPaths ω

theorem measurable_iidUnitPathBlockProcess_eval
    (P : Measure (CadlagPath unitInterval ℝ)) [IsProbabilityMeasure P]
    (t : ℝ≥0) :
    Measurable (fun ω : ℕ → CadlagPath unitInterval ℝ =>
      iidUnitPathBlockProcess ω t) := by
  let n := Nat.floor (t : ℝ)
  let u := Topology.unitBlockParameter n t
  have hblock (i : ℕ) (v : unitInterval) :
      Measurable (fun ω : ℕ → CadlagPath unitInterval ℝ => ω i v) := by
    exact (Skorokhod.measurable_apply v).comp (measurable_pi_apply i)
  change Measurable (fun ω : ℕ → CadlagPath unitInterval ℝ =>
    Topology.concatenateUnitPaths ω t)
  dsimp [Topology.concatenateUnitPaths, Topology.unitBlockEndpointSum, n, u]
  exact (Finset.measurable_sum (Finset.range n) (by
    intro i hi
    exact hblock i ⊤)).add (hblock n u)

theorem iidUnitPathBlockProcess_ae_start_eq_zero
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P) :
    ∀ᵐ ω ∂iidUnitPathBlockLaw P,
      iidUnitPathBlockProcess ω 0 = 0 := by
  have hblocks : ∀ᵐ ω ∂iidUnitPathBlockLaw P, ∀ n : ℕ, ω n ⊥ = 0 := by
    rw [ae_all_iff]
    intro n
    let hEval := measurePreserving_eval_infinitePi (fun _ : ℕ => P) n
    have hEvalQP : Measure.QuasiMeasurePreserving (Function.eval n)
        (iidUnitPathBlockLaw P) P := by
      refine ⟨hEval.measurable, ?_⟩
      unfold iidUnitPathBlockLaw
      rw [hEval.map_eq]
    exact hEvalQP.tendsto_ae hP.ae_start_eq_zero
  filter_upwards [hblocks] with ω hω
  change Topology.concatenateUnitPaths ω 0 = 0
  simp only [Topology.concatenateUnitPaths]
  have hfloor : Nat.floor ((0 : ℝ≥0) : ℝ) = 0 := by norm_num
  rw [hfloor]
  simp only [Topology.unitBlockEndpointSum, Finset.range_zero,
    Finset.sum_empty, zero_add]
  have hu : Topology.unitBlockParameter 0 (0 : ℝ≥0) = ⊥ := by
    apply Subtype.ext
    simp [Topology.unitBlockParameter]
  rw [hu]
  apply hω 0

theorem iidUnitPathBlockLaw_ae_blocks_start_eq_zero
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P) :
    ∀ᵐ ω ∂iidUnitPathBlockLaw P, ∀ n : ℕ, ω n ⊥ = 0 := by
  rw [ae_all_iff]
  intro n
  let hEval := measurePreserving_eval_infinitePi (fun _ : ℕ => P) n
  have hEvalQP : Measure.QuasiMeasurePreserving (Function.eval n)
      (iidUnitPathBlockLaw P) P := by
    refine ⟨hEval.measurable, ?_⟩
    unfold iidUnitPathBlockLaw
    rw [hEval.map_eq]
  exact hEvalQP.tendsto_ae hP.ae_start_eq_zero

theorem iidUnitPathBlockProcess_unitIntervalPathLaw_eq
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P) :
    Process.Path.Cadlag.pathLaw (iidUnitPathBlockLaw P)
      (fun t ω => iidUnitPathBlockProcess ω (UnitInterval.toNNReal t))
      (fun t => (measurable_iidUnitPathBlockProcess_eval P
        (UnitInterval.toNNReal t)).aemeasurable) = P := by
  let Q := iidUnitPathBlockLaw P
  let X : unitInterval → (ℕ → CadlagPath unitInterval ℝ) → ℝ :=
    fun t ω => iidUnitPathBlockProcess ω (UnitInterval.toNNReal t)
  have hXmeas : ∀ t, AEMeasurable (X t) Q := by
    intro t
    exact (measurable_iidUnitPathBlockProcess_eval P
      (UnitInterval.toNNReal t)).aemeasurable
  have hcadlag : ∀ᵐ ω ∂Q, IsCadlag (fun t : unitInterval => X t ω) := by
    filter_upwards [iidUnitPathBlockProcess_ae_cadlag P] with ω hω
    exact hω.comp_monotone_continuous (fun _ _ h => h)
      UnitInterval.continuous_toNNReal
  have hmapEq : Process.Path.Cadlag.pathMap X =ᵐ[Q]
      fun ω => ω 0 := by
    filter_upwards [iidUnitPathBlockLaw_ae_blocks_start_eq_zero hP, hcadlag]
      with ω hstarts hω
    let p : CadlagPath unitInterval ℝ := ⟨fun t => X t ω, hω⟩
    have hcoords : (fun q : RationalCoordinate.UnitInterval =>
        X (RationalCoordinate.toUnitInterval q) ω) =
        MeasureTheory.CadlagPath.denseEvaluation RationalCoordinate.toUnitInterval p := by
      funext q
      rfl
    have hmap : Process.Path.Cadlag.pathMap X ω = p := by
      change Function.extend
        (MeasureTheory.CadlagPath.denseEvaluation RationalCoordinate.toUnitInterval)
        id (fun _ => Skorokhod.ofContinuousMap
          (ContinuousMap.const unitInterval 0))
        (fun q : RationalCoordinate.UnitInterval =>
          X (RationalCoordinate.toUnitInterval q) ω) = p
      rw [hcoords]
      exact Process.Path.Cadlag.rationalEvaluationEmbedding.injective.extend_apply
        _ _ _
    have hpfirst : p = ω 0 := by
      apply CadlagPath.ext
      intro t
      exact Topology.concatenateUnitPaths_eq_first ω (hstarts 1) t
    rw [hmap, hpfirst]
  have hEval : HasLaw (fun ω : ℕ → CadlagPath unitInterval ℝ => ω 0) P Q :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => P) 0).hasLaw
  have hPath : HasLaw (Process.Path.Cadlag.pathMap X) P Q :=
    hEval.congr hmapEq
  have hPathLaw : Process.Path.Cadlag.pathLaw Q X hXmeas = P :=
    hPath.map_eq
  simpa [Q, X] using hPathLaw

private theorem iidUnitPathBlockProcess_nat_eval
    (ω : ℕ → CadlagPath unitInterval ℝ)
    (hstarts : ∀ n, ω n ⊥ = 0) (n : ℕ) :
    iidUnitPathBlockProcess ω n = ∑ i ∈ Finset.range n, ω i ⊤ := by
  change Topology.concatenateUnitPaths ω (n : ℝ≥0) = _
  rw [Topology.concatenateUnitPaths]
  have hfloor : Nat.floor ((n : ℝ≥0) : ℝ) = n := by
    change Nat.floor (n : ℝ) = n
    exact Nat.floor_natCast n
  rw [hfloor]
  have hparam : Topology.unitBlockParameter n (n : ℝ≥0) = ⊥ := by
    apply Subtype.ext
    simp [Topology.unitBlockParameter]
  rw [hparam]
  simp [Topology.unitBlockEndpointSum, hstarts n]

/-- The concatenated process has the expected independent stable increment
vector on every finite integer-time grid. -/
theorem iidUnitPathBlockProcess_integer_increments_hasLaw_pi
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P)
    (n : ℕ) :
    HasLaw
      (fun ω (i : Fin n) =>
        iidUnitPathBlockProcess ω (i.succ.val : ℝ≥0) -
          iidUnitPathBlockProcess ω (i.val : ℝ≥0))
      (Measure.pi fun _ : Fin n => μ) (iidUnitPathBlockLaw P) := by
  let Q := iidUnitPathBlockLaw P
  let endpoint : CadlagPath unitInterval ℝ → ℝ := fun f => f ⊤ - f ⊥
  have hendpointLaw : HasLaw endpoint μ P := by
    have h := hP.increment_hasLaw (⊥ : unitInterval) ⊤ bot_le
    simpa [endpoint, UnitInterval.clock] using h
  have hendpointMeas : Measurable endpoint := by
    exact (Skorokhod.measurable_apply ⊤).sub (Skorokhod.measurable_apply ⊥)
  have hendpointIndep :
      iIndepFun (fun k : ℕ => fun ω : ℕ → CadlagPath unitInterval ℝ =>
        endpoint (ω k)) Q := by
    exact iIndepFun_infinitePi (P := fun _ : ℕ => P)
      (X := fun _ f => endpoint f) (by intro k; exact hendpointMeas)
  have hfinIndep :
      iIndepFun (fun i : Fin n => fun ω : ℕ → CadlagPath unitInterval ℝ =>
        endpoint (ω i.val)) Q :=
    hendpointIndep.precomp Fin.val_injective
  have hcoordinateLaw (i : Fin n) :
      HasLaw (fun ω : ℕ → CadlagPath unitInterval ℝ => endpoint (ω i.val)) μ Q := by
    have heval : HasLaw (fun ω : ℕ → CadlagPath unitInterval ℝ => ω i.val) P Q :=
      (measurePreserving_eval_infinitePi (fun _ : ℕ => P) i.val).hasLaw
    exact HasLaw.comp_of_hasLaw_comp hendpointMeas.aemeasurable HasLaw.id
      heval hendpointLaw
  have hendpointVec :
      HasLaw (fun ω (i : Fin n) => endpoint (ω i.val))
        (Measure.pi fun _ : Fin n => μ) Q :=
    hfinIndep.hasLaw_pi hcoordinateLaw
  have hstarts := iidUnitPathBlockLaw_ae_blocks_start_eq_zero hP
  have hvecEq :
      (fun ω (i : Fin n) =>
        iidUnitPathBlockProcess ω (i.succ.val : ℝ≥0) -
          iidUnitPathBlockProcess ω (i.val : ℝ≥0)) =ᵐ[Q]
      (fun ω i => endpoint (ω i.val)) := by
    filter_upwards [hstarts] with ω hω
    funext i
    change iidUnitPathBlockProcess ω (Nat.succ i.val : ℝ≥0) -
        iidUnitPathBlockProcess ω (i.val : ℝ≥0) = endpoint (ω i.val)
    simp only [endpoint]
    rw [iidUnitPathBlockProcess_nat_eval ω hω (Nat.succ i.val),
      iidUnitPathBlockProcess_nat_eval ω hω i.val]
    have hsum :
        (∑ k ∈ Finset.range (i.val + 1), ω k ⊤) =
          (∑ k ∈ Finset.range i.val, ω k ⊤) + ω i.val ⊤ := by
      rw [Finset.sum_range_succ]
    rw [hsum]
    simp [hω i.val]
  exact hendpointVec.congr hvecEq

end ProbabilityTheory

namespace ProbabilityTheory

open scoped NNReal
open MeasureTheory
open MeasureTheory.CadlagPath
open ProbabilityTheory.RandomWalk.FunctionalLimit.Stable

/-- Compress a finite monotone mesh by deleting repeated points. The sorted
image is a strictly increasing mesh, and the original mesh factors through
the monotone surjection assigning each point its rank in that image. This is
an exact finite construction; in particular, it preserves a repeated final
endpoint without a left-limit argument. -/
private theorem exists_strict_grid_rank_factorization {n : ℕ}
    (grid : Fin (n + 1) → unitInterval) (hgrid : Monotone grid)
    (hstart : grid 0 = ⊥) :
    ∃ (m : ℕ) (strictGrid : Fin (m + 1) → unitInterval)
      (rank : Fin (n + 1) → Fin (m + 1)),
      StrictMono strictGrid ∧ strictGrid 0 = ⊥ ∧ Monotone rank ∧
        Function.Surjective rank ∧ (∀ j, strictGrid (rank j) = grid j) ∧
        (∀ f : CadlagPath unitInterval ℝ,
          denseEvaluation grid f = denseEvaluation strictGrid f ∘ rank) := by
  classical
  let points : Finset unitInterval := Finset.univ.image grid
  have hpointsNonempty : points.Nonempty := by
    refine ⟨⊥, ?_⟩
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hstart⟩
  have hcard : 1 ≤ points.card :=
    Nat.succ_le_of_lt (Finset.card_pos.mpr hpointsNonempty)
  let m := points.card - 1
  have hm : m + 1 = points.card := by
    dsimp [m]
    exact Nat.sub_add_cancel hcard
  let e : Fin (m + 1) ≃o points :=
    (Fin.castOrderIso hm).trans (points.orderIsoOfFin rfl)
  let strictGrid : Fin (m + 1) → unitInterval := fun i => e i
  let rank : Fin (n + 1) → Fin (m + 1) := fun j =>
    e.symm ⟨grid j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
  have hbotMem : (⊥ : unitInterval) ∈ points :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, hstart⟩
  have hstrict : StrictMono strictGrid := by
    intro i j hij
    exact e.strictMono hij
  have hzero : strictGrid 0 = ⊥ := by
    apply le_antisymm
    · have hle : e 0 ≤ (⟨⊥, hbotMem⟩ : points) :=
        calc
          e 0 ≤ e (e.symm ⟨⊥, hbotMem⟩) := e.monotone bot_le
          _ = ⟨⊥, hbotMem⟩ := by simp
      exact hle
    · exact bot_le
  have hrankMono : Monotone rank := by
    intro i j hij
    apply e.symm.monotone
    exact Subtype.coe_le_coe.mpr (hgrid hij)
  have hfactor (j : Fin (n + 1)) : strictGrid (rank j) = grid j := by
    simp [strictGrid, rank]
  have hrankSurj : Function.Surjective rank := by
    intro i
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (e i).property
    refine ⟨j, ?_⟩
    apply e.injective
    apply Subtype.ext
    simpa [rank] using hj
  have hevaluation (f : CadlagPath unitInterval ℝ) :
      denseEvaluation grid f = denseEvaluation strictGrid f ∘ rank := by
    funext j
    simp [denseEvaluation, hfactor]
  exact ⟨m, strictGrid, rank, hstrict, hzero, hrankMono, hrankSurj,
    hfactor, hevaluation⟩

/-- Adjacent indices in the compressed mesh are either the same rank or
successive ranks. Surjectivity is essential: a gap would be an omitted mesh
point that nevertheless occurs in the original grid. -/
private theorem rank_succ_val_le_add_one {n m : ℕ}
    (rank : Fin (n + 1) → Fin (m + 1)) (hrankMono : Monotone rank)
    (hrankSurj : Function.Surjective rank) (i : Fin n) :
    (rank i.succ).val ≤ (rank i.castSucc).val + 1 := by
  have hleft_le : rank i.castSucc ≤ rank i.succ :=
    hrankMono (Fin.castSucc_le_succ i)
  apply Nat.le_of_not_gt
  intro hgap
  have hgap' : (rank i.castSucc).val + 1 < (rank i.succ).val := hgap
  let middle : Fin (m + 1) := ⟨(rank i.castSucc).val + 1, by omega⟩
  have hmidLeft : rank i.castSucc < middle := by
    exact Fin.mk_lt_mk.mpr (by simp)
  have hmidRight : middle < rank i.succ := by
    exact Fin.mk_lt_mk.mpr (by simpa [middle] using hgap')
  obtain ⟨j, hj⟩ := hrankSurj middle
  have hsplit : j ≤ i.castSucc ∨ i.succ ≤ j := by
    by_cases h : j ≤ i.castSucc
    · exact Or.inl h
    · right
      apply Fin.le_iff_val_le_val.mpr
      have hleft : i.castSucc.val < j.val := by
        exact lt_of_not_ge (fun h' => h (Fin.le_iff_val_le_val.mpr h'))
      have hadj : i.succ.val = i.castSucc.val + 1 := by simp
      omega
  rcases hsplit with hleft | hright
  · have hmono := hrankMono hleft
    rw [hj] at hmono
    exact (not_lt_of_ge hmono) hmidLeft
  · have hmono := hrankMono hright
    rw [hj] at hmono
    exact (not_lt_of_ge hmono) hmidRight

private def unitGridDifference {n : ℕ} :
    (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
  fun x i => x i.succ - x i.castSucc

private theorem measurable_unitGridDifference {n : ℕ} :
    Measurable (@unitGridDifference n) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_pi_apply i.succ).sub (measurable_pi_apply i.castSucc)

private theorem unitGridDifference_partialSum {n : ℕ} :
    (unitGridDifference ∘ (Fin.partialSum : (Fin n → ℝ) → Fin (n + 1) → ℝ)) = id := by
  funext x i
  simp [unitGridDifference, Fin.partialSum_succ]

private theorem unitGrid_increments_hasLaw_of_positionLaw
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [hμ : IsProbabilityMeasure μ] [hP : IsProbabilityMeasure P] (n : ℕ)
    (grid : Fin (n + 1) → unitInterval) (hgrid : Monotone grid)
    (hstart : grid 0 = ⊥)
    (hposition : P.map (denseEvaluation grid) =
      ((stableTimeLawProductProbability (μ := μ) α grid :
        ProbabilityMeasure (Fin n → ℝ)) : Measure (Fin n → ℝ)).map
          (Fin.partialSum : (Fin n → ℝ) → Fin (n + 1) → ℝ)) :
    HasLaw (fun f (i : Fin n) => f (grid i.succ) - f (grid i.castSucc))
      (stableTimeLawProductProbability (μ := μ) α grid) P := by
  let L := stableTimeLawProductProbability (μ := μ) α grid
  let partialSum : (Fin n → ℝ) → (Fin (n + 1) → ℝ) := Fin.partialSum
  have hpartial : Measurable partialSum :=
    (Fin.continuous_partialSum n).measurable
  have hpreserving : MeasurePreserving unitGridDifference
      ((L : Measure (Fin n → ℝ)).map partialSum) (L : Measure (Fin n → ℝ)) := by
    refine ⟨measurable_unitGridDifference, ?_⟩
    rw [Measure.map_map measurable_unitGridDifference hpartial]
    rw [unitGridDifference_partialSum, Measure.map_id]
  have hposition' : HasLaw (denseEvaluation grid)
      ((L : Measure (Fin n → ℝ)).map partialSum) P := by
    exact ⟨(measurable_denseEvaluation grid).aemeasurable, by simpa [L] using hposition⟩
  have h := hpreserving.comp_hasLaw hposition'
  have hfun : (fun f (i : Fin n) => f (grid i.succ) - f (grid i.castSucc)) =ᵐ[P]
      unitGridDifference ∘ denseEvaluation grid := by
    exact ae_of_all _ fun f => by
      funext i
      rfl
  exact h.congr hfun

/-- A compatible finite-grid position law on every monotone unit-interval
mesh determines the canonical stable clock-process law on that interval.
The hypothesis is expressed through Mathlib's finite product of the stable
increment laws; taking adjacent differences recovers that product law. -/
theorem isStableClockProcessLaw_of_unitInterval_positionGridLaws
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [hμ : IsProbabilityMeasure μ] [hP : IsProbabilityMeasure P]
    (hStable : IsStrictlyAlphaStable α μ)
    (hstart : ∀ᵐ f ∂P, f ⊥ = 0)
    (hposition : ∀ (n : ℕ) (grid : Fin (n + 1) → unitInterval),
      Monotone grid → grid 0 = ⊥ →
      P.map (denseEvaluation grid) =
        ((stableTimeLawProductProbability (μ := μ) α grid :
          ProbabilityMeasure (Fin n → ℝ)) : Measure (Fin n → ℝ)).map
            (Fin.partialSum : (Fin n → ℝ) → Fin (n + 1) → ℝ)) :
    IsStableClockProcessLaw α μ UnitInterval.clock P := by
  refine ⟨hStable, ?_, ?_, hstart, ?_, ?_⟩
  · intro s t hst
    exact_mod_cast hst
  · rfl
  · intro n t ht
    let grid : Fin (n + 2) → unitInterval := Fin.cons ⊥ t
    have hgrid : Monotone grid := by
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      refine Fin.cases ?_ ?_ i
      · simpa [grid] using (bot_le (t 0))
      · intro i
        simpa [grid] using ht (Fin.castSucc_le_succ i)
    have hgridStart : grid 0 = ⊥ := by simp [grid]
    have hposition' := hposition (n + 1) grid hgrid hgridStart
    have hfull : HasLaw
        (fun f (i : Fin (n + 1)) => f (grid i.succ) - f (grid i.castSucc))
        (stableTimeLawProductProbability (μ := μ) α grid) P :=
      unitGrid_increments_hasLaw_of_positionLaw (n + 1) grid hgrid hgridStart
        hposition'
    have hcoordinateLaw (i : Fin (n + 1)) :
        IsProbabilityMeasure (stableTimeLaw α μ
          ((grid i.succ : unitInterval) - (grid i.castSucc : unitInterval))) := by
      dsimp [stableTimeLaw]
      infer_instance
    letI : ∀ i : Fin (n + 1), IsProbabilityMeasure (stableTimeLaw α μ
        ((grid i.succ : unitInterval) - (grid i.castSucc : unitInterval))) :=
      hcoordinateLaw
    have hcoordinate (i : Fin (n + 1)) :
        HasLaw (fun f : CadlagPath unitInterval ℝ =>
          f (grid i.succ) - f (grid i.castSucc))
          (stableTimeLaw α μ
            ((grid i.succ : unitInterval) - (grid i.castSucc : unitInterval))) P := by
      have heval := MeasureTheory.measurePreserving_eval
        (fun j : Fin (n + 1) => stableTimeLaw α μ
          ((grid j.succ : unitInterval) - (grid j.castSucc : unitInterval))) i
      exact heval.comp_hasLaw hfull
    have hfullIndep : iIndepFun
        (fun i : Fin (n + 1) => fun f : CadlagPath unitInterval ℝ =>
          f (grid i.succ) - f (grid i.castSucc)) P :=
      (iIndepFun_iff_hasLaw_pi_pi hcoordinate).2 hfull
    have hsub := hfullIndep.precomp (g := Fin.succ) (Fin.succ_injective n)
    convert hsub using 1
    · funext i f
      rfl
  · intro s t hst
    let grid : Fin 3 → unitInterval := ![⊥, s, t]
    have hgrid : Monotone grid := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [grid] <;> linarith
    have hposition' := hposition 2 grid hgrid (by simp [grid])
    have hfull := unitGrid_increments_hasLaw_of_positionLaw 2 grid hgrid
      (by simp [grid]) hposition'
    let i : Fin 2 := 1
    have hcoordinateLaw (j : Fin 2) :
        IsProbabilityMeasure (stableTimeLaw α μ
          ((grid j.succ : unitInterval) - (grid j.castSucc : unitInterval))) := by
      dsimp [stableTimeLaw]
      infer_instance
    letI : ∀ j : Fin 2, IsProbabilityMeasure (stableTimeLaw α μ
        ((grid j.succ : unitInterval) - (grid j.castSucc : unitInterval))) :=
      hcoordinateLaw
    have heval := MeasureTheory.measurePreserving_eval
      (fun j : Fin 2 => stableTimeLaw α μ
        ((grid j.succ : unitInterval) - (grid j.castSucc : unitInterval))) i
    have hcoord := heval.comp_hasLaw hfull
    have hfun : (fun ω : CadlagPath unitInterval ℝ => ω t - ω s) =ᵐ[P]
        Function.eval i ∘ (fun f j => f (grid j.succ) - f (grid j.castSucc)) := by
      exact ae_of_all _ fun f => by
        funext
        simp [i, grid]
    exact hcoord.congr hfun

end ProbabilityTheory

end
