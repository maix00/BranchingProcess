module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Topology.ContinuousMap.Compactness

public section

/-!
# Tight families of continuous-path laws

This file turns deterministic Arzelà--Ascoli bounds into tightness of a
family of measures on continuous path space.  The statement is independent
of any increment law or stochastic-process model.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory.Process.Path

/-- Every finite measure on continuous paths assigns arbitrarily small mass
to failure of a sufficiently fine fixed oscillation bound.  This is the
measure-theoretic form of uniform continuity of each path on a compact time
space. -/
theorem exists_pos_measure_compl_hasOscillationBound_lt
    {T E : Type*} [PseudoMetricSpace T] [CompactSpace T]
    [PseudoMetricSpace E]
    (μ : Measure C(T, E)) [IsFiniteMeasure μ]
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {eta : ENNReal} (heta : 0 < eta) :
    ∃ delta > 0,
      μ {f : C(T, E) |
        ContinuousMap.HasOscillationBound delta epsilon f}ᶜ < eta := by
  let delta : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let bad : ℕ → Set C(T, E) := fun n =>
    {f | ContinuousMap.HasOscillationBound (delta n) epsilon f}ᶜ
  have hdeltaPos (n : ℕ) : 0 < delta n := by
    dsimp [delta]
    positivity
  have hbadMeasurable (n : ℕ) : MeasurableSet (bad n) := by
    exact (ContinuousMap.isClosed_setOf_hasOscillationBound
      (delta n) epsilon).measurableSet.compl
  have hbadAntitone : Antitone bad := by
    intro m n hmn
    apply compl_subset_compl.mpr
    intro f hf s t hst
    exact hf s t <| lt_of_lt_of_le hst (by
      dsimp [delta]
      gcongr)
  have hbadInter : ⋂ n, bad n = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro f hf
    have huniform := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous f.continuous)
        epsilon hepsilon
    obtain ⟨d, hd, huniform⟩ := huniform
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
    have hgood : ContinuousMap.HasOscillationBound (delta n) epsilon f := by
      intro s t hst
      exact (huniform (lt_trans hst (by simpa [delta] using hn))).le
    exact (Set.mem_iInter.mp hf n) hgood
  have htendsto : Tendsto (fun n => μ (bad n)) atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_measure_iInter_atTop
      (μ := μ) (s := bad)
      (fun n => (hbadMeasurable n).nullMeasurableSet)
      hbadAntitone ⟨0, measure_ne_top μ (bad 0)⟩
    change Tendsto (fun n => μ (bad n)) atTop
      (nhds (μ (⋂ n, bad n))) at h
    rw [hbadInter, measure_empty] at h
    exact h
  have heventually : ∀ᶠ n : ℕ in atTop, μ (bad n) < eta :=
    htendsto.eventually (Iio_mem_nhds heta)
  obtain ⟨n, hn⟩ := heventually.exists
  exact ⟨delta n, hdeltaPos n, hn⟩

/-- One time scale can be chosen simultaneously for any finite prefix of a
sequence of finite continuous-path measures. -/
theorem exists_pos_forall_lt_measure_compl_hasOscillationBound_lt
    {T E : Type*} [PseudoMetricSpace T] [CompactSpace T]
    [PseudoMetricSpace E]
    (μ : ℕ → Measure C(T, E)) (hfinite : ∀ i, IsFiniteMeasure (μ i))
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {eta : ENNReal} (heta : 0 < eta) (N : ℕ) :
    ∃ delta > 0, ∀ i < N,
      μ i {f : C(T, E) |
        ContinuousMap.HasOscillationBound delta epsilon f}ᶜ < eta := by
  induction N with
  | zero => exact ⟨1, by norm_num, by simp⟩
  | succ N ih =>
      obtain ⟨oldDelta, holdDelta, hold⟩ := ih
      let _ : IsFiniteMeasure (μ N) := hfinite N
      obtain ⟨newDelta, hnewDelta, hnew⟩ :=
        exists_pos_measure_compl_hasOscillationBound_lt
          (μ N) hepsilon heta
      refine ⟨min oldDelta newDelta, lt_min holdDelta hnewDelta, ?_⟩
      intro i hi
      by_cases hiN : i < N
      · exact (measure_mono (compl_subset_compl.mpr <| by
          intro f hf s t hst
          exact hf s t (lt_of_lt_of_le hst (min_le_left _ _)))).trans_lt
            (hold i hiN)
      · have hiEq : i = N := by omega
        subst i
        exact (measure_mono (compl_subset_compl.mpr <| by
          intro f hf s t hst
          exact hf s t (lt_of_lt_of_le hst (min_le_right _ _)))).trans_lt
            hnew

/-- Eventual one-scale oscillation estimates can be diagonalized into one
sequence of scales that controls every measure and every oscillation level
simultaneously.  The finitely many measures preceding each eventual estimate
are absorbed using `exists_pos_forall_lt_measure_compl_hasOscillationBound_lt`.
-/
theorem exists_oscillationBounds_of_eventually_single
    {T E : Type*} [PseudoMetricSpace T] [CompactSpace T]
    [PseudoMetricSpace E]
    (μ : ℕ → Measure C(T, E)) (hfinite : ∀ i, IsFiniteMeasure (μ i))
    (hsingle : ∀ {epsilon : ℝ}, 0 < epsilon →
      ∀ {eta : ENNReal}, 0 < eta →
        ∃ delta > 0, ∀ᶠ i : ℕ in atTop,
          μ i {f : C(T, E) |
            ContinuousMap.HasOscillationBound delta epsilon f}ᶜ < eta)
    {eta : ENNReal} (heta : 0 < eta) :
    ∃ delta epsilon : ℕ → ℝ,
      (∀ m, 0 < delta m) ∧
      Tendsto epsilon atTop (nhds 0) ∧
      ∀ i, μ i {f : C(T, E) |
        ContinuousMap.HasOscillationBounds delta epsilon f}ᶜ ≤ eta := by
  let epsilon : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  let budget : ℕ → ENNReal := fun m =>
    (eta / 2) * (2⁻¹ : ENNReal) ^ m
  have hepsilon (m : ℕ) : 0 < epsilon m := by
    dsimp [epsilon]
    positivity
  have hbudget (m : ℕ) : 0 < budget m := by
    dsimp [budget]
    exact ENNReal.mul_pos
      (ne_of_gt (ENNReal.div_pos (ne_of_gt heta) (by norm_num)))
      (pow_ne_zero _ (by norm_num))
  choose tailDelta htailDelta htail using fun m =>
    hsingle (hepsilon m) (hbudget m)
  choose cutoff hcutoff using fun m => Filter.eventually_atTop.mp (htail m)
  choose prefixDelta hprefixDelta hprefix using fun m =>
    exists_pos_forall_lt_measure_compl_hasOscillationBound_lt
      μ hfinite (hepsilon m) (hbudget m) (cutoff m)
  let delta : ℕ → ℝ := fun m => min (tailDelta m) (prefixDelta m)
  have hdelta (m : ℕ) : 0 < delta m := by
    exact lt_min (htailDelta m) (hprefixDelta m)
  have hlevel (m i : ℕ) :
      μ i {f : C(T, E) |
        ContinuousMap.HasOscillationBound (delta m) (epsilon m) f}ᶜ ≤
          budget m := by
    by_cases hi : i < cutoff m
    · exact (measure_mono (compl_subset_compl.mpr <| by
          intro f hf s t hst
          exact hf s t (lt_of_lt_of_le hst (min_le_right _ _)))).trans
        (hprefix m i hi).le
    · exact (measure_mono (compl_subset_compl.mpr <| by
          intro f hf s t hst
          exact hf s t (lt_of_lt_of_le hst (min_le_left _ _)))).trans
        (hcutoff m i (Nat.le_of_not_gt hi)).le
  refine ⟨delta, epsilon, hdelta,
    tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
  intro i
  calc
    μ i {f : C(T, E) |
        ContinuousMap.HasOscillationBounds delta epsilon f}ᶜ ≤
        μ i (⋃ m, {f : C(T, E) |
          ContinuousMap.HasOscillationBound (delta m) (epsilon m) f}ᶜ) := by
      apply measure_mono
      intro f hf
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq,
        ContinuousMap.HasOscillationBounds] at hf
      simp only [Set.mem_iUnion, Set.mem_compl_iff, Set.mem_ofPred_eq]
      push Not at hf
      exact hf
    _ ≤ ∑' m, μ i {f : C(T, E) |
          ContinuousMap.HasOscillationBound (delta m) (epsilon m) f}ᶜ :=
      measure_iUnion_le _
    _ ≤ ∑' m, budget m := ENNReal.tsum_le_tsum (hlevel · i)
    _ = eta := by
      simp only [budget, ENNReal.tsum_mul_left,
        ENNReal.tsum_geometric_two]
      rw [ENNReal.div_eq_inv_mul]
      calc
        2⁻¹ * eta * 2 = eta * (2⁻¹ * 2) := by ac_rfl
        _ = eta := by
          rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

/-- A family of continuous-path measures is tight if, outside arbitrarily
small mass, its paths belong to one equicontinuous family with a common
pointwise bound. -/
theorem isTightMeasureSet_of_equicontinuous_bounded
    {I T E : Type*} [TopologicalSpace T] [CompactlyCoherentSpace T]
    [MetricSpace E] [ProperSpace E]
    (mu : I → Measure C(T, E))
    (h : ∀ epsilon, 0 < epsilon →
      ∃ S : Set C(T, E),
        Equicontinuous ((↑) : S → T → E) ∧
        ∃ origin : E, ∃ radius : ℝ,
          (∀ f ∈ S, ∀ t, dist (f t) origin ≤ radius) ∧
          ∀ i, mu i Sᶜ ≤ epsilon) :
    IsTightMeasureSet (range mu) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  obtain ⟨S, hS, origin, radius, hbound, hmass⟩ := h epsilon hepsilon
  refine ⟨closure S,
    ContinuousMap.isCompact_closure_of_equicontinuous_of_bounded
      S hS origin radius hbound, ?_⟩
  intro nu hnu
  obtain ⟨i, rfl⟩ := hnu
  exact (measure_mono (compl_subset_compl.mpr subset_closure)).trans (hmass i)

/-- Modulus-of-continuity form of the path-law tightness criterion.  This is
the interface used by stochastic estimates: for each error tolerance one may
choose a new deterministic modulus and new bounds. -/
theorem isTightMeasureSet_of_uniformModulus
    {I T E : Type*} [PseudoMetricSpace T] [CompactlyCoherentSpace T]
    [MetricSpace E] [ProperSpace E]
    (mu : I → Measure C(T, E))
    (h : ∀ epsilon, 0 < epsilon →
      ∃ modulus : ℝ → ℝ,
      ∃ anchor : T, ∃ origin : E,
      ∃ anchorRadius modulusBound : ℝ,
        Tendsto modulus (nhds 0) (nhds 0) ∧
        (∀ t, modulus (dist t anchor) ≤ modulusBound) ∧
        ∀ i, mu i {f : C(T, E) |
          ContinuousMap.HasUniformModulus modulus f ∧
            dist (f anchor) origin ≤ anchorRadius}ᶜ ≤ epsilon) :
    IsTightMeasureSet (range mu) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro epsilon hepsilon
  obtain ⟨modulus, anchor, origin, anchorRadius, modulusBound,
    hmodulus, hmodulusBound, hmass⟩ := h epsilon hepsilon
  let S : Set C(T, E) := {f |
    ContinuousMap.HasUniformModulus modulus f ∧
      dist (f anchor) origin ≤ anchorRadius}
  refine ⟨closure S,
    ContinuousMap.isCompact_closure_setOf_hasUniformModulus
      modulus hmodulus anchor origin anchorRadius modulusBound
        hmodulusBound, ?_⟩
  intro nu hnu
  obtain ⟨i, rfl⟩ := hnu
  exact (measure_mono (compl_subset_compl.mpr subset_closure)).trans (hmass i)

/-- Multiscale form of the continuous-path tightness criterion.  Each error
tolerance may use its own decreasing oscillation thresholds and positive
time scales. -/
theorem isTightMeasureSet_of_oscillationBounds
    {I T E : Type*} [PseudoMetricSpace T] [CompactlyCoherentSpace T]
    [MetricSpace E] [ProperSpace E]
    (mu : I → Measure C(T, E))
    (h : ∀ eta, 0 < eta →
      ∃ delta epsilon : ℕ → ℝ,
      ∃ origin : E, ∃ radius : ℝ,
        (∀ m, 0 < delta m) ∧
        Tendsto epsilon atTop (nhds 0) ∧
        ∀ i, mu i {f : C(T, E) |
          ContinuousMap.HasOscillationBounds delta epsilon f ∧
            ∀ t, dist (f t) origin ≤ radius}ᶜ ≤ eta) :
    IsTightMeasureSet (range mu) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro eta heta
  obtain ⟨delta, epsilon, origin, radius, hdelta, hepsilon, hmass⟩ :=
    h eta heta
  let S : Set C(T, E) := {f |
    ContinuousMap.HasOscillationBounds delta epsilon f ∧
      ∀ t, dist (f t) origin ≤ radius}
  refine ⟨closure S,
    ContinuousMap.isCompact_closure_setOf_hasOscillationBounds
      delta epsilon hdelta hepsilon origin radius, ?_⟩
  intro nu hnu
  obtain ⟨i, rfl⟩ := hnu
  exact (measure_mono (compl_subset_compl.mpr subset_closure)).trans (hmass i)

/-- A one-scale asymptotic oscillation estimate, together with a uniform
path bound in probability, implies tightness.  The diagonal choice of scales
is handled internally, so stochastic applications only have to prove one
oscillation estimate at a time. -/
theorem isTightMeasureSet_of_eventually_singleOscillationBound
    {T E : Type*} [PseudoMetricSpace T] [CompactSpace T]
    [SecondCountableTopology T] [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [ProperSpace E]
    (μ : ℕ → Measure C(T, E)) (hfinite : ∀ i, IsFiniteMeasure (μ i))
    (hsingle : ∀ {epsilon : ℝ}, 0 < epsilon →
      ∀ {eta : ENNReal}, 0 < eta →
        ∃ delta > 0, ∀ᶠ i : ℕ in atTop,
          μ i {f : C(T, E) |
            ContinuousMap.HasOscillationBound delta epsilon f}ᶜ < eta)
    (hbounded : ∀ {eta : ENNReal}, 0 < eta →
      ∃ origin : E, ∃ radius : ℝ,
        ∀ i, μ i {f : C(T, E) |
          ∀ t, dist (f t) origin ≤ radius}ᶜ ≤ eta) :
    IsTightMeasureSet (range μ) := by
  classical
  apply isTightMeasureSet_of_oscillationBounds μ
  intro eta heta
  have hhalf : 0 < eta / 2 := ENNReal.div_pos (ne_of_gt heta) (by norm_num)
  obtain ⟨delta, epsilon, hdelta, hepsilon, hosc⟩ :=
    exists_oscillationBounds_of_eventually_single μ hfinite hsingle hhalf
  obtain ⟨origin, radius, hbound⟩ := hbounded hhalf
  refine ⟨delta, epsilon, origin, radius, hdelta, hepsilon, ?_⟩
  intro i
  calc
    μ i {f : C(T, E) |
        ContinuousMap.HasOscillationBounds delta epsilon f ∧
          ∀ t, dist (f t) origin ≤ radius}ᶜ ≤
        μ i {f : C(T, E) |
          ContinuousMap.HasOscillationBounds delta epsilon f}ᶜ +
        μ i {f : C(T, E) |
          ∀ t, dist (f t) origin ≤ radius}ᶜ := by
      rw [show {f : C(T, E) |
          ContinuousMap.HasOscillationBounds delta epsilon f ∧
            ∀ t, dist (f t) origin ≤ radius}ᶜ =
          {f : C(T, E) |
            ContinuousMap.HasOscillationBounds delta epsilon f}ᶜ ∪
          {f : C(T, E) |
            ∀ t, dist (f t) origin ≤ radius}ᶜ by
        ext f
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_union]
        tauto]
      exact measure_union_le _ _
    _ ≤ eta / 2 + eta / 2 := add_le_add (hosc i) (hbound i)
    _ = eta := ENNReal.add_halves eta

/-- A finite family of finite measures on a Polish continuous-path space is
tight.  This local form is used to absorb the finitely many indices preceding
an asymptotic tightness estimate. -/
private theorem isTightMeasureSet_of_finite
    {T E : Type*} [PseudoMetricSpace T] [CompactSpace T]
    [SecondCountableTopology T] [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
    (S : Set (Measure C(T, E))) (hS : S.Finite)
    (hfinite : ∀ μ ∈ S, IsFiniteMeasure μ) :
    IsTightMeasureSet S := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      exact (isTightMeasureSet_singleton (μ := 0)).subset (by simp)
  | @insert μ S hμ hS ih =>
      rw [Set.forall_mem_insert] at hfinite
      let _ : IsFiniteMeasure μ := hfinite.1
      exact (isTightMeasureSet_singleton (μ := μ)).union
        (ih hfinite.2)

/-- Asymptotic multiscale criterion for tightness of continuous-path laws.
The stochastic estimates need only hold eventually: the finitely many
exceptional initial laws are tight individually and are absorbed into the
compact set chosen for each error tolerance. -/
theorem isTightMeasureSet_of_eventually_oscillationBounds
    {T E : Type*} [PseudoMetricSpace T] [CompactSpace T]
    [SecondCountableTopology T] [MetricSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [ProperSpace E]
    (μ : ℕ → Measure C(T, E))
    (hfinite : ∀ i, IsFiniteMeasure (μ i))
    (h : ∀ η, 0 < η →
      ∃ δ ε : ℕ → ℝ,
      ∃ origin : E, ∃ radius : ℝ,
        (∀ m, 0 < δ m) ∧
        Tendsto ε atTop (nhds 0) ∧
        ∀ᶠ i in atTop, μ i {f : C(T, E) |
          ContinuousMap.HasOscillationBounds δ ε f ∧
            ∀ t, dist (f t) origin ≤ radius}ᶜ ≤ η) :
    IsTightMeasureSet (range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro η hη
  obtain ⟨δ, ε, origin, radius, hδ, hε, hmass⟩ := h η hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 hmass
  let S : Set C(T, E) := {f |
    ContinuousMap.HasOscillationBounds δ ε f ∧
      ∀ t, dist (f t) origin ≤ radius}
  let tailK := closure S
  have htailK : IsCompact tailK :=
    ContinuousMap.isCompact_closure_setOf_hasOscillationBounds
      δ ε hδ hε origin radius
  let initialLaws : Set (Measure C(T, E)) := μ '' Set.Iio N
  have hinitialFinite : initialLaws.Finite :=
    Set.Finite.image μ (Set.finite_Iio N)
  have hinitialTight : IsTightMeasureSet initialLaws :=
    isTightMeasureSet_of_finite initialLaws hinitialFinite (by
      intro ν hν
      obtain ⟨i, -, rfl⟩ := hν
      exact hfinite i)
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    at hinitialTight
  obtain ⟨initialK, hinitialK, hinitialMass⟩ := hinitialTight η hη
  refine ⟨tailK ∪ initialK, htailK.union hinitialK, ?_⟩
  intro ν hν
  obtain ⟨i, rfl⟩ := hν
  by_cases hi : i < N
  · exact (measure_mono (by
        simp only [compl_union]
        exact inter_subset_right)).trans
      (hinitialMass (μ i) ⟨i, hi, rfl⟩)
  · exact (measure_mono (by
        simp only [compl_union]
        exact inter_subset_left)).trans
      ((measure_mono (compl_subset_compl.mpr subset_closure)).trans
        (hN i (Nat.le_of_not_gt hi)))

end ProbabilityTheory.Process.Path
