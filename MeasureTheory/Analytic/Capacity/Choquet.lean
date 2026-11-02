/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, WANG Yiyang
-/

module

public import MeasureTheory.Analytic.Capacity.Projection
public import MeasureTheory.Analytic.Paving.Analytic.Measurable
import Topology.Compactness.CompactSystem.Operations

/-!
# Choquet capacitability and analytic-set projections

## Public declarations

- `IsPavingAnalyticFor.isCapacitable` and
  `IsPavingAnalytic.isCapacitable` state that
  `\(\operatorname{IsPavingAnalyticFor}(p,\mathcal K,s)
  \to \operatorname{IsCapacitable}(m,s)\)` and
  `\(\operatorname{IsPavingAnalytic}(p,s)
  \to \operatorname{IsCapacitable}(m,s)\)`, under the stated capacity
  hypotheses.
- `isCapacitable_measure_iff` characterizes
  `\(\operatorname{IsCapacitable}(\operatorname{measureCapacity}(\mu),s)
  \iff \operatorname{NullMeasurableSet}(s,\mu)\)` for finite `μ`.
  `IsPavingAnalytic.nullMeasurableSet` and
  `IsMeasurableAnalytic.nullMeasurableSet` imply that analytic sets are
  `\(\operatorname{NullMeasurableSet}(s,\mu)\)` for every finite `μ`.
- `IsPavingAnalytic.nullMeasurableSet_fst`,
  `IsPavingAnalytic.nullMeasurableSet_snd`,
  `IsMeasurableAnalytic.nullMeasurableSet_fst`,
  `IsMeasurableAnalytic.nullMeasurableSet_snd`,
  `MeasurableSet.nullMeasurableSet_fst`, and
  `MeasurableSet.nullMeasurableSet_snd` state
  `\(\operatorname{NullMeasurableSet}(\operatorname{Prod.fst}''s,\mu)\)`
  or the corresponding second-coordinate projection under the stated
  compactness and standard Borel hypotheses.
- `isPavingAnalytic_swap` and `isPavingAnalytic_measurableSet_swap` transport
  analytic sets under the coordinate swap.

The capacitability proof uses Theorems 1.34 and 1.35 of He, Wang, and Yan,
*Semimartingale Theory and Stochastic Calculus*, first edition, Routledge
(1992), ISBN 978-0-8493-7715-0.
-/

@[expose] public section

open Filter
open MeasureTheory
open MeasureTheory.Analytic
open scoped ENNReal NNReal Topology MeasureTheory

namespace MeasureTheory.Analytic.Paving

variable {𝓧 𝓚 : Type*} {x y : 𝓧} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)}
  {s t : Set 𝓧} {f : ℕ → Set 𝓧}


variable {m : Capacity p}

/-- **Choquet's capacitability theorem**. -/
lemma IsPavingAnalyticFor.isCapacitable (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p)
    (hp_union : SupClosed p) (hs : IsPavingAnalyticFor p 𝓚 s) :
    IsCapacitable m s := by
  obtain ⟨q, hq_empty, hq, A, hA, rfl⟩ := hs
  have hq'_empty : ∅ ∈ infClosure q := subset_infClosure hq_empty
  have hq' : IsCompactSystem (infClosure q) :=
    IsCompactSystem.infClosure hq
  refine IsCapacitable.fst hp_empty hp_inter hp_union m hq'_empty infClosed_infClosure hq' ?_
  refine isCapacitable_mem_countableInfClosure_countableSupClosure _ ?_ ?_ ?_ ?_
  · exact subset_supClosure ⟨∅, hp_empty, ∅, hq'_empty, by simp⟩
  · exact InfClosed.supClosure
      (MeasureTheory.Analytic.Paving.InfClosed.image2_prod
        hp_inter infClosed_infClosure)
  · exact fun s hs t ht ↦ supClosed_supClosure hs ht
  · unfold prodSigmaDelta at hA
    rw [mem_countableInfClosure_iff_iInf] at hA ⊢
    obtain ⟨B, hB, rfl⟩ := hA
    refine ⟨B, fun n ↦ ?_, rfl⟩
    simp_rw [mem_countableSupClosure_iff_iSup] at hB ⊢
    obtain ⟨C, hC, hB_eq⟩ := hB n
    simp_rw [← hB_eq]
    refine ⟨C, fun m ↦ ?_, rfl⟩
    refine subset_supClosure ?_
    obtain ⟨u, v, hu, hv, h_eq⟩ := hC m
    exact ⟨u, v, hu, subset_infClosure hv, h_eq⟩

/-- **Choquet's capacitability theorem**. Every analytic set for a paving stable by intersection
and union is capacitable. -/
theorem IsPavingAnalytic.isCapacitable (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p)
    (hp_union : SupClosed p) (hs : IsPavingAnalytic p s) :
    IsCapacitable m s := by
  obtain ⟨𝓚, h𝓚, hs𝓚⟩ := hs
  exact hs𝓚.isCapacitable hp_empty hp_inter hp_union

lemma isCapacitable_measure_iff {m𝓧 : MeasurableSpace 𝓧} (μ : Measure 𝓧) [IsFiniteMeasure μ]
    (s : Set 𝓧) :
    IsCapacitable (measureCapacity μ) s ↔ NullMeasurableSet s μ := by
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · by_cases! hcs : (measureCapacity μ) s = 0
    · exact NullMeasurableSet.of_null hcs
    · have (n : ℕ) : (measureCapacity μ) s * (1 - (n + 1 : ℝ≥0∞)⁻¹) < (measureCapacity μ) s := by
        nth_rw 2 [← mul_one ((measureCapacity μ) s)]
        refine (ENNReal.mul_lt_mul_iff_right hcs (by simp)).2 (ENNReal.sub_lt_of_lt_add ?_ ?_)
        · simp
        · exact ENNReal.lt_add_right (by simp) (by simp)
      have (n : ℕ) := hs (((measureCapacity μ) s) * (1 - (n + 1 : ℝ≥0∞)⁻¹)) (this n)
      choose f hf using this
      have hsub : ⋃ i, f i ⊆ s := Set.iUnion_subset fun i => (hf i).2.1
      have hm := MeasurableSet.iUnion fun i ↦
        MeasureTheory.Analytic.Paving.MeasurableSet.of_mem_countableInfClosure
          (hf i).1
      refine ⟨⋃ i, f i, hm, ae_eq_set.2 ⟨?_, ?_⟩⟩
      · rw [measure_sdiff hsub hm.nullMeasurableSet (by finiteness)]
        suffices μ (⋃ i, f i) = μ s from by simp_all
        refine le_antisymm (measure_mono hsub) ?_
        have : Tendsto (fun n : ℕ => μ s * (1 - (n + 1 : ℝ≥0∞)⁻¹)) atTop (𝓝 (μ s)) := by
          nth_rw 2 [← mul_one (μ s)]
          refine ENNReal.Tendsto.const_mul ?_ (by simp)
          nth_rw 3 [← tsub_zero 1]
          refine ENNReal.Tendsto.sub tendsto_const_nhds ?_ (by simp)
          convert ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1) with n
          simp
        refine le_of_tendsto_of_tendsto' this tendsto_const_nhds fun n => (hf n).2.2.trans ?_
        simpa using measure_mono (Set.subset_iUnion _ _)
      · simp_all [← Set.sdiff_eq_empty]
  · refine fun a ha ↦ ⟨(toMeasurable μ sᶜ)ᶜ, subset_countableInfClosure ?_, ?_, ?_⟩
    · exact (measurableSet_toMeasurable _ _).compl
    · rw [Set.compl_subset_comm]
      exact subset_toMeasurable μ sᶜ
    · simp only [measureCapacity_apply, measurableSet_toMeasurable, measure_toMeasurable, ne_eq,
        measure_ne_top, not_false_eq_true, measure_compl] at ha ⊢
      rw [← measure_compl₀ hs.compl (by simp), compl_compl]
      exact ha.le

/-- An analytic set is universally measurable: it is null-measurable with respect to any
finite measure. -/
lemma IsPavingAnalytic.nullMeasurableSet {m𝓧 : MeasurableSpace 𝓧}
    (hs : IsPavingAnalytic {t | MeasurableSet t} s) (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet s μ := by
  rw [← isCapacitable_measure_iff μ]
  refine IsPavingAnalytic.isCapacitable (p := {t : Set 𝓧 | MeasurableSet t}) MeasurableSet.empty
    ?_ ?_ hs
  · exact fun s hs t ht ↦ hs.inter ht
  · exact fun s hs t ht ↦ hs.union ht

/-- An analytic set is universally measurable: it is null-measurable with respect to any
finite measure. -/
lemma IsMeasurableAnalytic.nullMeasurableSet {m𝓧 : MeasurableSpace 𝓧} (hs : IsMeasurableAnalytic s)
    (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet s μ := by
  exact hs.isPavingAnalytic.nullMeasurableSet μ

theorem IsPavingAnalytic.nullMeasurableSet_fst {ι : Type} [LinearOrder ι] [DenselyOrdered ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] [CompactIccSpace ι]
    [Nonempty ι] {_ : MeasurableSpace ι} [BorelSpace ι]
    {_m𝓧 : MeasurableSpace 𝓧} {s : Set (𝓧 × ι)}
    (hs : IsPavingAnalytic {t | MeasurableSet t} s) (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet (Prod.fst '' s) μ := by
  refine IsPavingAnalytic.nullMeasurableSet ?_ μ
  refine isPavingAnalytic_fst_of_image2_prod_measurableSet_Icc (s := s) ?_
  rwa [isPavingAnalytic_image2_prod_measurableSet_Icc_iff]

-- todo: swap could be any measurable embedding?
lemma isPavingAnalytic_swap {Ω 𝓧 : Type*} {s : Set (𝓧 × Ω)}
    {p : Set (Set (𝓧 × Ω))} (hs : IsPavingAnalytic p s) :
    IsPavingAnalytic ((fun s ↦ Prod.swap '' s) '' p) (Prod.swap '' s) := by
  obtain ⟨𝓚, h𝓚, q, hq_empty, hq_compact, t, ht_mem, h_eq⟩ := hs
  refine ⟨𝓚, h𝓚, q, hq_empty, hq_compact, Prod.map Prod.swap id '' t, ?_, ?_⟩
  · rw [mem_prodSigmaDelta_iff] at ht_mem ⊢
    obtain ⟨A, hA, K, hK, rfl⟩ := ht_mem
    refine ⟨fun n m ↦ Prod.swap '' (A n m), fun n m ↦ ?_, K, hK, ?_⟩
    · simp only [Set.mem_image]
      exact ⟨A n m, hA n m, rfl⟩
    · rw [Set.image_iInter]
      swap; · exact Prod.swap_bijective.prodMap Function.bijective_id
      simp_rw [Set.image_iUnion]
      congr with n x
      simp
      grind
  · ext; simp; grind

lemma isPavingAnalytic_measurableSet_swap {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {s : Set (𝓧 × Ω)}
    (hs : IsPavingAnalytic {t | MeasurableSet t} s) :
    IsPavingAnalytic {t | MeasurableSet t} (Prod.swap '' s) := by
  convert isPavingAnalytic_swap hs
  ext s
  simp only [Set.mem_image]
  refine ⟨fun hs ↦ ⟨Prod.swap ⁻¹' s, MeasurableSet.preimage ?_ measurable_swap, ?_⟩,
    fun ⟨t, ht, ht_eq⟩ ↦ ?_⟩
  · exact hs
  · ext; simp; grind
  · rw [← ht_eq, Set.image_swap_eq_preimage_swap]
    refine MeasurableSet.preimage ?_ measurable_swap
    exact ht

lemma IsPavingAnalytic.nullMeasurableSet_snd {ι : Type} [LinearOrder ι] [DenselyOrdered ι]
    [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] [CompactIccSpace ι]
    [Nonempty ι] {_ : MeasurableSpace ι} [BorelSpace ι]
    {_m𝓧 : MeasurableSpace 𝓧} {s : Set (ι × 𝓧)}
    (hs : IsPavingAnalytic {t | MeasurableSet t} s) (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet (Prod.snd '' s) μ := by
  convert IsPavingAnalytic.nullMeasurableSet_fst (s := Prod.swap ⁻¹' s) (_m𝓧 := _m𝓧) ?_ μ
  · ext; simp
  · convert isPavingAnalytic_measurableSet_swap hs
    ext; simp; grind

theorem IsMeasurableAnalytic.nullMeasurableSet_fst {𝓨 : Type*}
    {_m𝓧 : MeasurableSpace 𝓧} {_m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] {s : Set (𝓧 × 𝓨)}
    (hs : IsMeasurableAnalytic s) (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet (Prod.fst '' s) μ := by
  have hs_for : IsMeasurableAnalyticFor (𝓨 × ℝ) (Prod.fst '' s) := by
    obtain ⟨t, ht, h_eq⟩ := hs
    rw [h_eq]
    refine ⟨MeasurableEquiv.prodAssoc '' t, ?_, by ext; simp [MeasurableEquiv.prodAssoc]⟩
    exact MeasurableEquiv.prodAssoc.measurableSet_image.mpr ht
  exact hs_for.isMeasurableAnalytic.nullMeasurableSet μ

theorem IsMeasurableAnalytic.nullMeasurableSet_snd {𝓨 : Type*}
    {_m𝓧 : MeasurableSpace 𝓧} {_m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] {s : Set (𝓨 × 𝓧)}
    (hs : IsMeasurableAnalytic s) (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet (Prod.snd '' s) μ := by
  convert IsMeasurableAnalytic.nullMeasurableSet_fst (s := Prod.swap ⁻¹' s) (_m𝓧 := _m𝓧)
    (_m𝓨 := _m𝓨) ?_ μ
  · ext; simp
  · obtain ⟨t, ht, h_eq⟩ := hs
    rw [h_eq]
    refine ⟨{u | ((u.1.2, u.1.1), u.2) ∈ t}, ?_, by ext; simp [Prod.swap]⟩
    exact ht.preimage (by fun_prop)

/-- **Measurable projection** theorem: the projection of a measurable set is universally measurable
(null-measurable for any finite measure). -/
theorem MeasurableSet.nullMeasurableSet_fst {𝓨 : Type*}
    {_m𝓧 : MeasurableSpace 𝓧} {_m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] {s : Set (𝓧 × 𝓨)}
    (hs : MeasurableSet s) (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet (Prod.fst '' s) μ :=
  hs.isMeasurableAnalytic.nullMeasurableSet_fst μ

theorem MeasurableSet.nullMeasurableSet_snd {𝓨 : Type*}
    {_m𝓧 : MeasurableSpace 𝓧} {_m𝓨 : MeasurableSpace 𝓨} [StandardBorelSpace 𝓨] {s : Set (𝓨 × 𝓧)}
    (hs : MeasurableSet s) (μ : Measure 𝓧) [IsFiniteMeasure μ] :
    NullMeasurableSet (Prod.snd '' s) μ :=
  hs.isMeasurableAnalytic.nullMeasurableSet_snd μ

end MeasureTheory.Analytic.Paving

end
