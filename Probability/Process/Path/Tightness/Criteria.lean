module

public import Probability.Process.Path.Tightness.Oscillation
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Topology.ContinuousMap.Compactness

public section

/-!
# Tightness criteria for continuous-path laws

This file turns deterministic Arzelà--Ascoli bounds into tightness of a
family of measures on continuous path space.  The statements are independent
of any increment law or stochastic-process model.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace ProbabilityTheory.Process.Path
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
