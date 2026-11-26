module

public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.RestartMean
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Lemmas.ReserveContinuation
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.Limit.Lemmas.RestartMoment
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.ClockFailure
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.Entrance
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.RestartEndpoint
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.TrialPosition
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.WaitingTime
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Splits

/-!
Regression of the fourth-moment proof of Theorem 1.2 in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, May 2026 manuscript.

The public speed theorem deliberately retains the weaker first-moment
hypotheses. This test assembles the original proof separately: the same
stopped restart endpoint has L² norm O(log³ N), Cauchy–Schwarz makes its
bad-event integral o(log N), and the uniform remaining-horizon expectation
completes the single-root block upper comparison. All mathematical components
are imported from their owning modules; only their strong-hypothesis assembly
is local to this regression.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace BranchingProcessTest.NSelectionSpeed

open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed

open Combinatorics.Branching Combinatorics.UlamHarris
open EndpointDeviation ProbabilityTheory.BranchingRandomWalk.Spine
open Combinatorics.Branching.Step.FiniteSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling
open SelectedPath SelectedPath.GrowthTrial SelectedPath.Completion.Lemmas

local notation "Ωf" => RootIndexed.StepField (ℕ ⊕ ℕ) ℕ ℝ
local notation "𝔽" => RootIndexed.stepFiltration (Root := ℕ ⊕ ℕ) (α := ℕ) (X := ℝ)

noncomputable local instance (m : ℕ) : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ) :=
  RootIndexed.addressLinearOrder (Fin m) ℕ

public theorem singleRootMean_via_secondMoment
    (L : StepLaw ℕ ℕ ℝ) [IsProbabilityMeasure L.raw]
    (hsuper : BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, inferInstance⟩ : BranchingProcess.OffspringConfigurationLaw ℕ ℝ))
    (hne : L.raw nonemptySupport = 1)
    (hnorm : HasBoundaryNormalization L.potential L.raw) (hfirst : HasLeftmostFirstMoment L)
    (hfour : HasLeftmostFourthMoment L)
    {c t : ℝ} (hc : 0 ≤ c) (ht : 0 < t)
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hremaining : ∀ a : ℝ, 0 < a → a < 1 → ∀ T : ℕ → ℕ,
      Tendsto (fun n => (T n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 0) →
      ∀ᶠ n in atTop, ∀ i ≤ T n,
        (∫ field, @firstNSelectedEndpointMinimum ⌊(N n : ℝ) ^ a⌋₊ (N n) (H n - i)
          (RootIndexed.addressLinearOrder _ ℕ) field
          ∂finiteRootStepFieldLaw L.sortedPotentialImage ⌊(N n : ℝ) ^ a⌋₊) ≤
          (c * t + 1) * Real.log (N n : ℝ)) :
    ∀ᶠ n in atTop, (∫ field, @firstNSelectedEndpointMinimum 1 (N n) (H n)
      (RootIndexed.addressLinearOrder (Fin 1) ℕ) field
      ∂finiteRootStepFieldLaw L.sortedPotentialImage 1) / Real.log (N n : ℝ) ≤ c * t + 6 := by
  classical
  let μ := L.sortedPotentialImage
  let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
  let logN n := Real.log (N n : ℝ)
  have hlog : Tendsto logN atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  obtain ⟨M, a, ρ, p, ha, ha1, _, hρ, hp, haM, hsplit, hsuccess, hclock⟩ :=
    exists_logarithmicTrialClock_failure_le_polynomial L hne hsuper hN ht one_pos hH
  let B := firstNBySlotOrder (α := ℕ) (X := ℝ) 2
  let R := firstOrBelowPotential B realPotential (M : ℝ)
  let growth := B.belowPotential realPotential (M : ℝ)
  let hR := firstOrBelowPotential_measurable B firstTwoBySlotOrder_measurable realPotential M
  let hgrowth := B.belowPotential_measurable firstTwoBySlotOrder_measurable realPotential M
  let d n := ⌊a * logN n / Real.log ρ⌋₊ + 2
  let lower n := ⌈(N n : ℝ) ^ a⌉₊
  let upper n := 2 ^ d n
  let m n := ⌊(N n : ℝ) ^ a⌋₊
  let τ n := Completion.time R growth hR hgrowth (lower n) (upper n) (d n) (0 : ℕ)
  let hτ n := Completion.time_isStoppingTime R growth hR hgrowth (lower n) (upper n) (d n) (0 : ℕ)
  obtain ⟨hRne, hmarks⟩ := firstOrBelowPotential_field_marks_ae L hne (M : ℝ)
  obtain ⟨θ, hθ, hratio⟩ := exists_splitWaitingTime_expParameter μ R hsplit
  let δ : ℝ := 1 / ((M : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let cost := δ + a / Real.log ρ + δ / θ *
    Real.log (μ (splitBy R) / (1 - ENNReal.ofReal (Real.exp θ) *
       (1 - μ (splitBy R)))).toReal
  let γ := cost + 1
  let K n := ⌊δ * logN n⌋₊
  let T n := ⌊γ * logN n⌋₊
  let A (n : ℕ) : Set Ωf := {ω | splitCount R 0 ((τ n ω).untopD 0 - (d n + 1))
      (RootIndexed.StepField.left ω) < K n}
  let E (n : ℕ) := A n ∩ {ω | τ n ω ≤ (T n : WithTop ℕ)}
  obtain ⟨hT, hscales, b, hb, hbad⟩ :=
    hclock δ θ γ hδ hθ hratio (lt_add_of_pos_right cost one_pos)
  have hcut : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M :=
    fun ξ j hj => ((Step.FiniteSelection.mem_filter B _ ξ j).mp hj).2
  have hbounded : growth.IsBoundedBy 2 := by
    intro ξ
    exact (Finset.card_le_card (fun i hi =>
      ((Step.FiniteSelection.mem_filter B _ ξ i).mp hi).1)).trans
      (firstNBySlotOrder_isBoundedBy 2 ξ)
  have hupper (n : ℕ) : 1 ≤ upper n := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  have hmLower (n : ℕ) : m n ≤ lower n := Nat.floor_le_ceil _
  have hmuNorm := L.sortedPotentialImage_hasBoundaryNormalization hnorm
  have hmuNe : μ nonemptySupport = 1 := by
    change L.sortedPotentialImage nonemptySupport = 1
    rwa [L.sortedPotentialImage_nonemptySupport, L.sorted_nonemptySupport]
  have hvalid : ∀ᶠ n in atTop, 0 < N n ∧ 0 < m n ∧ m n ≤ N n ∧ 0 < H n := by
    filter_upwards [hN.eventually_ge_atTop 1, hlog.eventually_gt_atTop 0,
      hH.eventually (lt_mem_nhds ht)] with n hn hln hh
    have hone : 1 ≤ (N n : ℝ) := by exact_mod_cast hn
    have hm : 0 < m n := Nat.floor_pos.mpr (Real.one_le_rpow hone ha.le)
    have hmN : m n ≤ N n := Nat.floor_le_of_le (by
      simpa using Real.rpow_le_rpow_of_exponent_le hone ha1.le)
    have hHn : 0 < H n := by
      have hh' : 0 < (H n : ℝ) := by simpa only [zero_mul] using (lt_div_iff₀ (pow_pos hln 3)).mp hh
      exact_mod_cast hh'
    exact ⟨Nat.zero_lt_of_lt hn, hm, hmN, hHn⟩
  have hexists : ∀ᶠ n in atTop,
      ∃ roots : Ωf → Fin (m n) → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ,
        (∀ v, MeasurableSet[(hτ n).measurableSpace] {ω | roots ω = v}) ∧
        (∀ ω (i : ℕ), τ n ω = i → ∀ j, (roots ω j).2.length = i) ∧
        (∀ ω, τ n ω ≠ ⊤ → Function.Injective (roots ω)) ∧
        ∀ x : ℝ, (finiteRootStepFieldLaw μ 1)
          {ω | x ≤ firstNSelectedEndpointMinimum 1 (N n) (H n) ω} ≤
          P {ω | x ≤ trialRestartEndpoint (N n) R growth hR hgrowth (lower n)
            (upper n) (d n) 0 (H n) roots ω} := by
    filter_upwards [hscales, hvalid] with n hs hn
    obtain ⟨roots, hfiber, hdepth, hinj, hmem, hcomp⟩ :=
      exists_trialRestartEndpoint_tail_comparison (m := m n) μ hmuNorm (N n) hn.1 hn.2.2.1
        R growth hR hgrowth hRne (lower n) (upper n) (d n) (hmLower n) (hupper n)
        hbounded hs.2 0
    exact ⟨roots, hfiber, hdepth, hinj,
      measure_firstNSelectedEndpointMinimum_ge_le_restart μ hmuNorm hmuNe (N n)
        hn.1 hn.2.1 R growth hR hgrowth (lower n) (upper n) (d n) (H n) roots
        hfiber hdepth hinj hmem (hcomp (H n))⟩
  let root (n : ℕ) := if h : ∃ roots : Ωf → Fin (m n) → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ,
        (∀ v, MeasurableSet[(hτ n).measurableSpace] {ω | roots ω = v}) ∧
        (∀ ω (i : ℕ), τ n ω = i → ∀ j, (roots ω j).2.length = i) ∧
        (∀ ω, τ n ω ≠ ⊤ → Function.Injective (roots ω)) ∧
        ∀ x : ℝ, (finiteRootStepFieldLaw μ 1)
          {ω | x ≤ firstNSelectedEndpointMinimum 1 (N n) (H n) ω} ≤
          P {ω | x ≤ trialRestartEndpoint (N n) R growth hR hgrowth (lower n)
            (upper n) (d n) 0 (H n) roots ω} then h.choose else fun _ _ => (Sum.inl 0, [])
  let F n := trialRestartEndpoint (N n) R growth hR hgrowth (lower n) (upper n) (d n)
    (0 : ℕ) (H n) (root n)
  have hroot := hexists.mono fun n h => show
      (∀ v, MeasurableSet[(hτ n).measurableSpace] {ω | root n ω = v}) ∧
      (∀ ω (i : ℕ), τ n ω = i → ∀ j, (root n ω j).2.length = i) ∧
      (∀ ω, τ n ω ≠ ⊤ → Function.Injective (root n ω)) ∧
      ∀ x : ℝ, (finiteRootStepFieldLaw μ 1)
        {ω | x ≤ firstNSelectedEndpointMinimum 1 (N n) (H n) ω} ≤ P {ω | x ≤ F n ω}
      from by simpa only [F, root, dite_eq_left h] using h.choose_spec
  obtain ⟨C, hC, hnormBound⟩ := restartEndpoint_memLp_two_and_eLpNorm_le
    L hnorm hne hfour (M : ℝ) (Nat.cast_nonneg _)
  have hL2 : ∀ᶠ n in atTop, MemLp (F n) 2 P ∧
      eLpNorm (F n) 2 P ≤ ENNReal.ofReal (C * (H n : ℝ)) := by
    filter_upwards [hvalid, hroot] with n hn hr
    exact hnormBound (m n) (N n) (lower n) (upper n) (d n) (H n)
      hn.1 hn.2.1 hn.2.2.2 (root n) hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hFint : ∀ᶠ n in atTop, Integrable (F n) P :=
    hL2.mono fun _ h => h.1.integrable (by norm_num)
  have hbadlim := tendsto_restartEndpoint_badIntegral_div_log P F E hN ht hC hb hH
    (hL2.mono fun _ h => h.1) (hL2.mono fun _ h => h.2) hbad
  have hshort := hremaining a ha ha1 T hT
  let offset := ((∫ ξ, max (value' ξ 0) 0 ∂μ) / μ.real (splitBy R)) / p + 2 * M
  have hoffset : ∀ᶠ n in atTop, offset ≤ logN n := hlog.eventually_ge_atTop offset
  have hδM : δ * (M : ℝ) ≤ 1 := by
    dsimp [δ]
    rw [one_div_mul_eq_div]
    exact (div_le_one (by positivity)).2 (by linarith)
  filter_upwards [hscales, hroot, hvalid, hFint, hshort, hsuccess, hoffset,
    hlog.eventually_gt_atTop 0, hbadlim.eventually (gt_mem_nhds one_pos)]
    with n hs hr hn hFi hrem hsucc hoff hln hbadn
  have hA : MeasurableSet[(hτ n).measurableSpace] (A n) := by
    exact measurableSet_splitCount_at_stopped_time R hR (hτ n) (d n) (K n)
  have hE : MeasurableSet (E n) := ((hτ n).measurableSpace_le _ hA).inter
    ((𝔽).le (T n) _ ((hτ n).measurableSet_le (T n)))
  let cN := (c * t + 1) * logN n
  obtain ⟨hI, him⟩ := integral_firstNSelectedEndpointMinimum_le_restart_terms L hnorm hne hfirst
    (m := m n) (N n) (H n) (T n) hn.1 hn.2.1 hs.1 R growth hR hgrowth
    (lower n) (upper n) (d n) (root n) hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 hFi
    (A n) hA cN hrem
  have hentry := integral_trialResetPosition_le L hnorm hfirst
    R growth hR hgrowth M (Nat.cast_nonneg _) hcut (lower n) (upper n) (d n) (K n) (T n)
    (hn.2.1.trans_le (hmLower n)) (hupper n) hRne hsplit (hp.trans_le hsucc) hmarks hE hI
  let posMean := ∫ ξ, max (value' ξ 0) 0 ∂μ
  have hposMean : 0 ≤ posMean := integral_nonneg fun _ => le_max_right _ _
  have hconst := div_le_div_of_nonneg_left
    (div_nonneg hposMean ENNReal.toReal_nonneg : 0 ≤ posMean / μ.real (splitBy R)) hp hsucc
  dsimp only [posMean] at hconst
  have hK : (K n : ℝ) ≤ δ * logN n := Nat.floor_le (mul_nonneg hδ.le hln.le)
  have hd := trialDuration_le hρ ha.le (N n)
  change (d n : ℝ) ≤ a * logN n / Real.log ρ + 2 at hd
  have hKbound : (K n : ℝ) * M ≤ logN n := calc
    _ ≤ (δ * logN n) * M := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _)
    _ = (δ * M) * logN n := by ring
    _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hδM hln.le
  have hDbound : (M : ℝ) * d n ≤ logN n + 2 * M := calc
    _ ≤ (M : ℝ) * (a * logN n / Real.log ρ + 2) :=
      mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)
    _ = (M : ℝ) * (a / Real.log ρ) * logN n + 2 * M := by ring
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_right haM.le hln.le]
  have hpositions : _ ≤ 3 * logN n := hentry.trans (by dsimp [offset] at hoff; linarith)
  have hprob : P.real (E n) ≤ 1 :=
    (measureReal_mono (Set.subset_univ (E n))).trans_eq (probReal_univ (μ := P))
  have hGood : P.real (E n) * cN ≤ cN := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hprob (by dsimp [cN]; positivity)
  have hbadbound : (∫ ω in (E n)ᶜ, F n ω ∂P) ≤ logN n :=
    ((div_lt_iff₀ hln).mp hbadn).le.trans_eq (one_mul _)
  apply (div_le_iff₀ hln).2
  dsimp [cN] at hGood him
  exact him.trans (by linarith)



end BranchingProcessTest.NSelectionSpeed
