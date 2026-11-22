/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.InitialPopulation.Speed.Transport
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.InitialPopulation.Field.Independence
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.Basic
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.InitialPopulation.Trajectory.Lemmas.CapacityHit.Mark

/-!
# Endpoint speed after the first capacity hit

## Public declarations

* `smallInitialPopulation_ae_hasAsymptoticSpeed_and_L1_of_stepLaw`: for
  $0<m\le N$, with any deterministic initial positions $(x_i)_{i<m}$, the actual leftmost position
  satisfies $M_n/n\to v_N$ almost surely and in $L^1$. The offspring law satisfies the
  boundary and leftmost first moment assumptions, has nonempty offspring,
  and has mean offspring count greater than one.

The population continues from the positions at its first capacity hit,
with fresh independent descendants. This implements the stopping argument
of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring* (Fudan University, 2026), Chapter 3, Corollary 3.14.
-/

open Asymptotics Filter MeasureTheory
open scoped ENNReal Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection
open EndpointDeviation
open ProbabilityTheory.BranchingRandomWalk.RootIndexed

attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable local instance (k : ℕ) : LinearOrder (RootIndexed.TreeNode (Fin k) ℕ) :=
  RootIndexed.addressLinearOrder (Fin k) ℕ

private theorem measurable_hitData (m N : ℕ) (initialPosition : Fin m → ℝ) (hm : 0 < m) :
    Measurable (fun field =>
      (smallInitialPopulationHitInitialPosition m N initialPosition hm field,
        smallInitialPopulationHitSubtreeField m N initialPosition hm field)) := by
  have hle : (⨆ t, (RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ)) t) ≤
        (inferInstance : MeasurableSpace (FiniteRootStepField m ℕ ℝ)) :=
    iSup_le fun t => (RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)).le t
  apply Measurable.prodMk
  · intro A hA
    exact hle _ (measurableSet_smallInitialPopulationHitInitialPosition_preimage
      m N initialPosition hm A hA).1
  · let roots := smallInitialPopulationHitRoots m N initialPosition hm
    have hroots : Measurable roots := measurable_to_countable' fun r =>
      hle _ (measurableSet_smallInitialPopulationHitRoots_fiber m N initialPosition hm r).1
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun v => ?_
    have heval : Measurable (fun (p : FiniteRootStepField m ℕ ℝ ×
        RootIndexed.TreeNode (Fin m) ℕ) => p.1 p.2.1 (p.2.2 ++ v)) :=
      measurable_from_prod_countable_left fun r =>
        (measurable_pi_apply (r.2 ++ v)).comp (measurable_pi_apply r.1)
    exact heval.comp (measurable_id.prodMk (hroots.eval (a := i)))

private theorem hitData_law (m N : ℕ) (initialPosition : Fin m → ℝ) (hm : 0 < m) (hmN : m ≤ N)
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ) (hnonempty : μ nonemptySupport = 1)
    (hsplit : (1 : ℝ≥0∞) < ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) :
    let P := finiteRootStepFieldLaw μ m
    P.map (fun field => (smallInitialPopulationHitInitialPosition m N initialPosition hm field,
        smallInitialPopulationHitSubtreeField m N initialPosition hm field)) =
      (P.map (smallInitialPopulationHitInitialPosition m N initialPosition hm)).prod
        (finiteRootStepFieldLaw μ N) := by
  intro P
  let h := measurable_hitData m N initialPosition hm
  let _ : IsProbabilityMeasure
      (P.map (fun field => (smallInitialPopulationHitInitialPosition m N initialPosition hm field,
        smallInitialPopulationHitSubtreeField m N initialPosition hm field))) :=
    (Measure.isProbabilityMeasure_map_iff h.aemeasurable).2 inferInstance
  apply Measure.ext_prod
  intro A B hA hB
  have hinit : Measurable (smallInitialPopulationHitInitialPosition m N initialPosition hm) :=
    measurable_fst.comp h
  rw [Measure.map_apply h (hA.prod hB), Measure.prod_prod, Measure.map_apply hinit hA]
  exact smallInitialPopulationHitInitialPosition_freshField_factorization
    m N initialPosition hm hmN μ hboundary hnonempty hsplit A hA B hB

private theorem endpoint_eq_after_hit (m N n j : ℕ) (initialPosition : Fin m → ℝ) (hm : 0 < m)
    (field : FiniteRootStepField m ℕ ℝ)
    (himage : (smallInitialPopulationHitSubtreePopulation m N initialPosition hm field j).image
        (smallInitialPopulationHitAddress m N initialPosition hm field) =
          smallInitialPopulation m N (n + j) initialPosition field)
    (hpop : (smallInitialPopulation m N (n + j) initialPosition field).Nonempty) :
    selectedPopulationEndpointTrajectoryWithParameter N
        (smallInitialPopulationHitInitialPosition m N initialPosition hm field,
          smallInitialPopulationHitSubtreeField m N initialPosition hm field) j =
      RootIndexed.selectedPopulationEndpointWithParameter m N (n + j) (initialPosition, field) := by
  let localPop := smallInitialPopulationHitSubtreePopulation m N initialPosition hm field j
  let address := smallInitialPopulationHitAddress m N initialPosition hm field
  have himage' : localPop.image address = smallInitialPopulation m N (n + j) initialPosition field := himage
  have hlocal : localPop.Nonempty := Finset.image_nonempty.mp (himage'.symm ▸ hpop)
  let initial := smallInitialPopulationHitInitialPosition m N initialPosition hm field
  let fresh := smallInitialPopulationHitSubtreeField m N initialPosition hm field
  change (if h : localPop.Nonempty then localPop.inf' h
    (RootIndexed.observedPositionAtGeneration initial id id j fresh) else 0) =
    (if h : (smallInitialPopulation m N (n + j) initialPosition field).Nonempty then
      (smallInitialPopulation m N (n + j) initialPosition field).inf' h
        (RootIndexed.observedPositionAtGeneration initialPosition id id (n + j) field)
      else 0)
  rw [dite_eq_left hlocal, dite_eq_left hpop]
  have hpos (q : RootIndexed.TreeNode (Fin N) ℕ) (hq : q ∈ localPop) :
      RootIndexed.observedPositionAtGeneration initial id id j fresh q =
      RootIndexed.observedPositionAtGeneration initialPosition id id (n + j) field
        (address q) := by
    have hmem : address q ∈ smallInitialPopulation m N (n + j) initialPosition field :=
      himage' ▸ Finset.mem_image_of_mem address hq
    have hdepthOriginal := RootIndexed.selectedPopulationTotalized_depth N Finset.univ
      initialPosition id id (n + j) field (address q) hmem
    have hdepth := RootIndexed.selectedPopulationTotalized_depth N Finset.univ
      initial id id j fresh q hq
    simp only [RootIndexed.observedPositionAtGeneration, RootIndexed.positionAtGeneration,
      hdepth, hdepthOriginal, ite_true, id_eq]
    exact smallInitialPopulationHitSubtree_position m N initialPosition hm field q.1 q.2
  apply le_antisymm
  · rw [Finset.le_inf'_iff]
    intro p hp
    rw [← himage', Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [← hpos q hq]
    exact Finset.inf'_le _ hq
  · rw [Finset.le_inf'_iff]
    intro q hq
    rw [hpos q hq]
    apply Finset.inf'_le
    rw [← himage']
    exact Finset.mem_image_of_mem address hq

private theorem endpoint_succ_le_activeDisplacement_ae
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (m N : ℕ) (initial : Fin m → ℝ) (hm : 0 < m) (hN : 0 < N)
    (L : StepLaw ι ℕ X) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1) :
    ∀ᵐ field ∂finiteRootStepFieldLaw L.sortedPotentialImage m, ∀ n,
      RootIndexed.selectedPopulationEndpointWithParameter m N (n + 1) (initial, field) ≤
        RootIndexed.selectedPopulationEndpointWithParameter m N n (initial, field) +
          |value' (smallInitialActiveMark m N n initial hm field) 0| := by
  let μ := L.sortedPotentialImage
  have hb := L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hne : μ nonemptySupport = 1 := by
    dsimp [μ]
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hnonempty]
  have ho : μ (orderedBySteps realPotential) = 1 := by
    dsimp [μ]
    rw [L.sortedPotentialImage_orderedBy]
    simp
  filter_upwards [RootIndexed.selectedPopulationTotalized_succ_spec_ae μ hb N Finset.univ initial,
    RootIndexed.selectedPopulationTotalized_nonempty_ae N Finset.univ
        ⟨(⟨0, hm⟩ : Fin m), Finset.mem_univ _⟩ initial hN μ hb hne,
    finiteRootStepFieldLaw_ae_all_of_measure_one
      (orderedBySteps_measurable (ι := ℕ) realPotential) μ ho m,
    finiteRootStepFieldLaw_ae_all_of_measure_one nonemptySupport_measurable μ hne m]
    with field hspec hpop hordered hchildren n
  let parents := smallInitialPopulation m N n initial field
  let selected := smallInitialPopulation m N (n + 1) initial field
  let value (k : ℕ) := RootIndexed.observedPositionAtGeneration initial id id k field
  let p := smallInitialActiveAddress m N n initial hm field
  obtain ⟨hp, hmin⟩ := smallInitialActiveAddress_mem_and_min m N n initial hm field (hpop n)
  have hdepth := RootIndexed.selectedPopulationTotalized_depth N Finset.univ
    initial id id n field p hp
  obtain ⟨i, hi⟩ := hchildren p.1 p.2
  have hzero : survive (field p.1 p.2) 0 := by
    have horder : (field p.1 p.2).map realPotential ∈ orderedSteps := hordered p.1 p.2
    exact (survive_map_iff realPotential _ _).1
      (orderedSteps_survive_of_le _ horder (Nat.zero_le i)
        ((survive_map_iff realPotential _ _).2 hi))
  let q : RootIndexed.TreeNode (Fin m) ℕ := (p.1, p.2 ++ [0])
  have hq := Combinatorics.Branching.Population.childAddress_mem_childrenAtGeneration
    n parents field p hp hdepth 0 hzero
  have hpop' : selected.Nonempty := hpop (n + 1)
  have hparent : parents.Nonempty := hpop n
  have hminEq : parents.inf' hparent (value n) = value n p := by
    apply le_antisymm (Finset.inf'_le _ hp)
    exact Finset.le_inf' hparent (value n) hmin
  have hnext : selected.inf' hpop' (value (n + 1)) ≤ value (n + 1) q := by
    obtain ⟨r, hr, hrmin⟩ := Finset.exists_mem_eq_inf' hpop' (value (n + 1))
    by_contra! hlt
    have hkey := valueKey_lt_of_value_lt (value (n + 1)) (hlt.trans_eq hrmin)
    have hqSelected := (hspec n).lower r hr q hq hkey
    exact (not_le_of_gt hlt) (Finset.inf'_le _ hqSelected)
  have hqvalue : value (n + 1) q = value n p + value' (field p.1 p.2) 0 := by
    simp only [value, RootIndexed.observedPositionAtGeneration, RootIndexed.positionAtGeneration,
      q, List.length_append, List.length_singleton, hdepth, ite_true, id_eq]
    simp [RootIndexed.position_append_singleton]
  change (if h : selected.Nonempty then selected.inf' h (value (n + 1)) else 0) ≤
    (if h : parents.Nonempty then parents.inf' h (value n) else 0) +
      |value' (smallInitialActiveMark m N n initial hm field) 0|
  rw [dite_eq_left hpop', dite_eq_left hparent, hminEq]
  rw [hqvalue] at hnext
  exact hnext.trans (add_le_add le_rfl (le_abs_self _))

private theorem endpointNormalized_unifIntegrable
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (m N : ℕ) (initialPosition : Fin m → ℝ) (hm : 0 < m) (hN : 0 < N)
    (L : StepLaw ι ℕ X) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1) (hfirst : HasLeftmostFirstMoment L) :
    let P := finiteRootStepFieldLaw L.sortedPotentialImage m
    let normalized := fun (n : ℕ) field =>
      (n : ℝ)⁻¹ * RootIndexed.selectedPopulationEndpointWithParameter m N n (initialPosition, field)
    (∀ n, MemLp (normalized n) 1 P) ∧ UnifIntegrable normalized 1 P := by
  intro P normalized
  let μ := L.sortedPotentialImage
  let M (n : ℕ) (field : FiniteRootStepField m ℕ ℝ) :=
    RootIndexed.selectedPopulationEndpointWithParameter m N n (initialPosition, field)
  let W := ∑ i : Fin m, ENNReal.ofReal (Real.exp (-initialPosition i))
  have hW : W ≠ ⊤ := ENNReal.sum_ne_top.mpr fun _ _ => ENNReal.ofReal_ne_top
  let mark (n : ℕ) := smallInitialActiveMark m N n initialPosition hm
  let D (n : ℕ) (field : FiniteRootStepField m ℕ ℝ) := |value' (mark n field) 0|
  let G (n : ℕ) (field : FiniteRootStepField m ℕ ℝ) :=
    (∑ i ∈ Finset.range n, D i field) / (n : ℝ)
  let B (n : ℕ) (field : FiniteRootStepField m ℕ ℝ) := (n : ℝ)⁻¹ * max (-M n field) 0
  have hM (n : ℕ) : Measurable (M n) :=
    (measurable_selectedPopulationEndpointWithParameter m N n).comp
      (measurable_const.prodMk measurable_id)
  have hmark (n : ℕ) : HasLaw (mark n) μ P := by
    refine ⟨?_, (smallInitialActiveMark_independent_and_law m N n initialPosition hm μ).2⟩
    have h : Measurable (mark n) :=
      (measurable_smallInitialActiveMark_at_succ m N n initialPosition hm).mono
        ((RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)).le (n + 1)) le_rfl
    exact h.aemeasurable
  have hDmeas : Measurable (fun ξ : Step ℕ ℝ => |value' ξ 0|) :=
    (value'_measurable 0).abs
  have hDident (n : ℕ) : IdentDistrib (D n) (D 0) P P := by
    exact (show IdentDistrib (mark n) (mark 0) P P from
      ⟨(hmark n).aemeasurable, (hmark 0).aemeasurable,
        (hmark n).map_eq.trans (hmark 0).map_eq.symm⟩).comp hDmeas
  have hD0 : MemLp (D 0) 1 P := by
    have hμ := L.integrable_sortedPotentialImage_firstSlot_abs hboundary hfirst
    rw [← memLp_one_iff_integrable] at hμ
    exact (show MemLp (fun ξ : Step ℕ ℝ => |value' ξ 0|) 1 (P.map (mark 0)) from
      (hmark 0).map_eq.symm ▸ hμ).comp_of_map (hmark 0).aemeasurable
  have hDui : UniformIntegrable D 1 P :=
    MemLp.uniformIntegrable_of_identDistrib (by norm_num) (by norm_num) hD0 hDident
  have hGui : UniformIntegrable G 1 P := by
    have h := uniformIntegrable_average_real (p := (1 : ℝ≥0∞)) (by norm_num) hDui
    convert h using 1
    ext n field
    simp [G, Finset.sum_apply, Pi.div_apply]
  have hBmeas (n : ℕ) : Measurable (B n) :=
    measurable_const.mul ((hM n).neg.max measurable_const)
  have hboundaryμ := L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptyμ : μ nonemptySupport = 1 := by
    dsimp [μ]
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hnonempty]
  have hBbound (n : ℕ) : eLpNorm (B n) 1 P ≤ ENNReal.ofReal ((n : ℝ)⁻¹) * W := by
    rw [eLpNorm_one_eq_lintegral_eNorm (hBmeas n).aestronglyMeasurable]
    have hn : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    calc
      _ ≤ ∫⁻ field, ENNReal.ofReal ((n : ℝ)⁻¹) * ENNReal.ofReal (Real.exp (-M n field)) ∂P := by
        apply lintegral_mono
        intro field
        have hmax : max (-M n field) 0 ≤ Real.exp (-M n field) :=
          max_le ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
            (Real.exp_pos _).le
        change ‖(n : ℝ)⁻¹ * max (-M n field) 0‖ₑ ≤
          ENNReal.ofReal ((n : ℝ)⁻¹) * ENNReal.ofReal (Real.exp (-M n field))
        rw [Real.eNorm_eq_ofReal_abs, abs_of_nonneg (mul_nonneg hn (le_max_right _ _))]
        rw [← ENNReal.ofReal_mul hn]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmax hn)
      _ ≤ _ := by
        have he : Measurable (fun field => ENNReal.ofReal (Real.exp (-M n field))) :=
          (Real.continuous_exp.measurable.comp (hM n).neg).ennreal_ofReal
        rw [lintegral_const_mul _ he]
        gcongr
        simpa [M, P, ENNReal.ofReal_natCast] using
          finiteRootStepFieldLaw_lintegral_exp_neg_selectedPopulationEndpoint_le
            m N n initialPosition hm hN μ hboundaryμ hnonemptyμ
  have hBtendsto : Tendsto (fun n => eLpNorm (B n) 1 P) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hreal : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ)⁻¹)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp hinv
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ)⁻¹) * W) atTop (𝓝 0) by
        simpa only [zero_mul] using ENNReal.Tendsto.mul_const hreal (Or.inr hW))
      (fun _ => zero_le) hBbound
  have hBmem (n : ℕ) : MemLp (B n) 1 P :=
    (hBbound n).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hW.lt_top)
  have hBui := unifIntegrable_of_tendsto_Lp_zero le_rfl ENNReal.one_ne_top hBmem hBtendsto
  let K := |initialPosition ⟨0, hm⟩|
  have hK : 0 ≤ K := abs_nonneg _
  have hstart (field : FiniteRootStepField m ℕ ℝ) : M 0 field ≤ K := by
    let pop := RootIndexed.initialPopulation (α := ℕ) (Finset.univ : Finset (Fin m))
    have hp : ((⟨0, hm⟩ : Fin m), []) ∈ pop :=
      RootIndexed.mem_initialPopulation_iff.mpr ⟨_, Finset.mem_univ _, rfl⟩
    have hpop : pop.Nonempty := ⟨_, hp⟩
    let value := RootIndexed.observedPositionAtGeneration initialPosition id id 0 field
    change (if h : pop.Nonempty then pop.inf' h value else 0) ≤ K
    rw [dite_eq_left hpop]
    apply (Finset.inf'_le value hp).trans
    simpa [K, value, RootIndexed.observedPositionAtGeneration,
      RootIndexed.positionAtGeneration, RootIndexed.position] using
      le_abs_self (initialPosition ⟨0, hm⟩)
  have hstep := endpoint_succ_le_activeDisplacement_ae m N initialPosition hm hN L
    hboundary hnonempty
  have hupper : ∀ᵐ field ∂P, ∀ n, M n field ≤ K + ∑ k ∈ Finset.range n, D k field := by
    filter_upwards [hstep] with field hstep n
    induction n with
    | zero => simpa using hstart field
    | succ n ih =>
      rw [Finset.sum_range_succ, ← add_assoc]
      exact (hstep n).trans (add_le_add ih le_rfl)
  have hKui : UnifIntegrable (fun (_ : ℕ) (_ : FiniteRootStepField m ℕ ℝ) => K) 1 P :=
    unifIntegrable_const le_rfl ENNReal.one_ne_top (memLp_const K)
  have hmeasNormalized (n : ℕ) : AEStronglyMeasurable (normalized n) P :=
    (measurable_const.mul (hM n)).aestronglyMeasurable
  have hdomNormalized (n : ℕ) : ∀ᵐ field ∂P,
      ‖normalized n field‖ₑ ≤ ‖(K + G n field) + B n field‖ₑ := by
    filter_upwards [hupper] with field hupper
    have hn : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    have hsum : 0 ≤ ∑ i ∈ Finset.range n, D i field :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hdom : |M n field| ≤ K + (∑ i ∈ Finset.range n, D i field) +
        max (-M n field) 0 := by
      rw [abs_le]
      constructor
      · linarith [le_max_left (-M n field) (0 : ℝ)]
      · linarith [hupper n, le_max_right (-M n field) (0 : ℝ)]
    have hnonneg : 0 ≤ K + G n field + B n field :=
      add_nonneg (add_nonneg hK (div_nonneg hsum (Nat.cast_nonneg _)))
        (mul_nonneg hn (le_max_right _ _))
    have hinv : (n : ℝ)⁻¹ ≤ 1 := by
      by_cases h : n = 0
      · simp [h]
      · exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h)
    simp only [normalized, Real.eNorm_eq_ofReal_abs, abs_of_nonneg hnonneg,
      abs_mul, abs_of_nonneg hn]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (n : ℝ)⁻¹ * (K + (∑ i ∈ Finset.range n, D i field) + max (-M n field) 0) :=
        mul_le_mul_of_nonneg_left hdom hn
      _ ≤ _ := by
        simp only [G, B, div_eq_mul_inv, mul_add, mul_comm _ ((n : ℝ)⁻¹)]
        gcongr
        exact mul_le_of_le_one_left hK hinv
  refine ⟨fun n => ?_, ?_⟩
  · have hend : MemLp (fun field => (K + G n field) + B n field) 1 P :=
      ((memLp_const K).add (hGui.memLp n)).add (hBmem n)
    exact hend.of_le_eNorm (hmeasNormalized n) (hdomNormalized n)
  · exact ((hKui.add hGui.unifIntegrable).add hBui).ae_mono
      hmeasNormalized hdomNormalized

/-- From a nonempty deterministic initial population, the selected endpoint has
the full-capacity speed almost surely after the first capacity hit. -/
theorem smallInitialPopulation_ae_hasAsymptoticSpeed_and_L1_of_stepLaw
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (N : ℕ) (hN : 0 < N) (L : StepLaw ι ℕ X) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw)
    (hnonempty : L.raw nonemptySupport = 1) (hfirst : HasLeftmostFirstMoment L)
    (hsplit : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂L.raw) :
    ∃ speed : ℝ,
      (∀ initial : Fin N → ℝ,
        (∀ᵐ field ∂finiteRootStepFieldLaw L.sortedPotentialImage N,
          HasAsymptoticSpeed (𝕜 := ℝ)
            (selectedPopulationEndpointTrajectoryWithParameter N (initial, field)) speed) ∧
        Tendsto (fun n : ℕ => eLpNorm (fun field =>
          (n : ℝ)⁻¹ * selectedPopulationEndpointTrajectoryWithParameter N (initial, field) n -
            speed) 1 (finiteRootStepFieldLaw L.sortedPotentialImage N)) atTop (𝓝 0)) ∧
      ∀ (m : ℕ) (initialPosition : Fin m → ℝ), 0 < m → m ≤ N →
        let P := finiteRootStepFieldLaw L.sortedPotentialImage m
        let endpoint := fun field n =>
          RootIndexed.selectedPopulationEndpointWithParameter m N n (initialPosition, field)
        (∀ᵐ field ∂P, HasAsymptoticSpeed (𝕜 := ℝ) (endpoint field) speed) ∧
          (∀ n : ℕ, MemLp (fun field => (n : ℝ)⁻¹ * endpoint field n) 1 P) ∧
          Tendsto (fun n : ℕ => eLpNorm (fun field =>
            (n : ℝ)⁻¹ * endpoint field n - speed) 1 P) atTop (𝓝 0) := by
  obtain ⟨speed, hfull⟩ := selectedPopulationEndpointTrajectory_ae_hasAsymptoticSpeed_and_L1_of_stepLaw
    hN L hboundary hnonempty hfirst
  refine ⟨speed, hfull, ?_⟩
  intro m initialPosition hm hmN
  let μ := L.sortedPotentialImage
  let P := finiteRootStepFieldLaw μ m
  let Q := finiteRootStepFieldLaw μ N
  let data (field : FiniteRootStepField m ℕ ℝ) :=
    (smallInitialPopulationHitInitialPosition m N initialPosition hm field,
      smallInitialPopulationHitSubtreeField m N initialPosition hm field)
  have hsplitμ : (1 : ℝ≥0∞) < ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ := by
    dsimp [μ]
    rwa [L.lintegral_childCount_sortedPotentialImage]
  have hboundaryμ := L.sortedPotentialImage_hasBoundaryNormalization hboundary
  have hnonemptyμ : μ nonemptySupport = 1 := by
    dsimp [μ]
    rw [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport, hnonempty]
  have hgood : ∀ᵐ p ∂(P.map (fun field => (data field).1)).prod Q, HasAsymptoticSpeed (𝕜 := ℝ)
      (selectedPopulationEndpointTrajectoryWithParameter N p) speed := by
    rw [Measure.ae_prod_iff_ae_ae]
    · exact Filter.Eventually.of_forall fun initial => (hfull initial).1
    · exact measurableSet_tendsto (𝓝 speed) fun n =>
        measurable_const.mul (measurable_selectedPopulationEndpointTrajectoryWithParameter N n)
  have hdata : ∀ᵐ field ∂P, HasAsymptoticSpeed (𝕜 := ℝ)
      (selectedPopulationEndpointTrajectoryWithParameter N (data field)) speed := by
    have hmap : ∀ᵐ p ∂P.map data, HasAsymptoticSpeed (𝕜 := ℝ)
        (selectedPopulationEndpointTrajectoryWithParameter N p) speed := by
      dsimp only [P, data]
      exact hitData_law m N initialPosition hm hmN μ hboundaryμ hnonemptyμ hsplitμ |>.symm ▸ hgood
    exact ae_of_ae_map (measurable_hitData m N initialPosition hm).aemeasurable hmap
  have hlim : ∀ᵐ field ∂P,
      HasAsymptoticSpeed (𝕜 := ℝ) (fun n =>
        RootIndexed.selectedPopulationEndpointWithParameter m N n (initialPosition, field))
        speed := by
    filter_upwards [hdata, finiteRootStepFieldLaw_ae_smallInitialPopulationHitSubtreePopulation_image
      m N initialPosition hm hmN μ hboundaryμ hnonemptyμ hsplitμ,
      RootIndexed.selectedPopulationTotalized_nonempty_ae N Finset.univ
        ⟨(⟨0, hm⟩ : Fin m), Finset.mem_univ _⟩ initialPosition hN μ hboundaryμ hnonemptyμ]
      with field hs hhit hpop
    obtain ⟨n, hn, hpath⟩ := hhit
    apply (hasAsymptoticSpeed_iff_nat_add _ _ n).2
    have heq (j : ℕ) := endpoint_eq_after_hit m N n j initialPosition hm field (hpath j) (hpop (n + j))
    have hinv : Tendsto (fun j : ℕ => (j : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hratio : Tendsto (fun j : ℕ => (1 + (j : ℝ)⁻¹ * (n : ℝ))⁻¹) atTop (𝓝 1) := by
      have hden : Tendsto (fun j : ℕ => 1 + (j : ℝ)⁻¹ * (n : ℝ)) atTop (𝓝 1) := by
        simpa only [zero_mul, add_zero] using tendsto_const_nhds.add (hinv.mul_const (n : ℝ))
      simpa only [inv_one] using hden.inv₀ one_ne_zero
    have hs' : Tendsto (fun j : ℕ => (j : ℝ)⁻¹ *
        selectedPopulationEndpointTrajectoryWithParameter N (data field) j)
        atTop (𝓝 speed) := hs
    have hscaled := hratio.mul hs'
    simp only [one_mul] at hscaled
    apply hscaled.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with j hj
    rw [heq, Nat.add_comm j n, smul_eq_mul, Nat.cast_add]
    have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
    have hsum : (n : ℝ) + (j : ℝ) ≠ 0 := by positivity
    field_simp; ring
  have ⟨hmem, hui⟩ :=
    endpointNormalized_unifIntegrable m N initialPosition hm hN L hboundary hnonempty hfirst
  refine ⟨hlim, hmem, ?_⟩
  exact tendsto_Lp_finite_of_tendsto_ae (μ := P) (p := (1 : ℝ≥0∞)) le_rfl ENNReal.one_ne_top
    (fun n => (measurable_const.mul
      ((measurable_selectedPopulationEndpointWithParameter m N n).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    (memLp_const speed) hui hlim

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

end
