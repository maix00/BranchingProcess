/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, WANG Yiyang
-/
module

public import MeasureTheory.Analytic.Paving.Analytic.Projection
public import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Topology.Compactness.CompactSystem.Operations

/-!
# Measurable and interval-paving analytic sets

This module characterizes measurable sets as analytic for interval pavings and relates measurable
analytic sets to paving-analytic projections.

## Public declarations

- `isPavingAnalytic_of_measurableSet_generateFrom` proves $IsPavingAnalytic(p,s)$ when s is
  measurable for $generateFrom(p)$ and each generator and its complement is paving-analytic.
- `Iic_mem_countableSupClosure_Icc`, `Ici_mem_countableSupClosure_Icc`,
  `Iio_mem_countableSupClosure_Icc`, `Ioi_mem_countableSupClosure_Icc`, and
  `univ_mem_countableSupClosure_Icc` express order rays and the whole space as countable unions
  of closed intervals.
- `borel_eq_generateFrom_isCompact` gives
  $borel(\mathbb R)=generateFrom\{K\mid IsCompact(K)\}$.
  The interval-family equality used internally follows Mathlib's borel_eq_generateFrom_Icc
  and remains private.
- `MeasurableSet.isPavingAnalytic_Icc` states that
  $MeasurableSet(s)\Rightarrow IsPavingAnalytic(\{\varnothing\}\cup\{Icc(a,b)\},s)$
  under the stated ordered Borel hypotheses.
  `IsPavingAnalytic_measurableSet_iff_isPavingAnalytic_Icc` gives the equivalence between
  analyticity for measurable sets and for the closed-interval paving.
- `isCountablySpanning_insert_empty_Icc` states that
  $\{\varnothing\}\cup\{Icc(a,b)\}$ is countably spanning under its order and topology hypotheses.
- `MeasurableSet.isPavingAnalytic_image2_prod` and
  `isPavingAnalytic_image2_prod_measurableSet_Icc_iff` represent measurable product sets as
  analytic for product interval pavings.
  `isPavingAnalytic_fst_of_image2_prod_measurableSet_Icc` and
  `MeasurableSet.isPavingAnalytic_fst` show that their first-coordinate projections are
  paving-analytic.
- `IsMeasurableAnalyticFor` K s means
  $\exists t,\ MeasurableSet(t)\land s=Prod.fst''t$ for t subset of X times K;
  `IsMeasurableAnalytic` s specializes to K = ℝ.
- `isMeasurableAnalyticFor_of_snd` and `isMeasurableAnalytic_of_snd` transport this representation
  under coordinate swap. `IsMeasurableAnalyticFor.isMeasurableAnalytic` gives a real witness
  for standard Borel K; `MeasurableSet.isMeasurableAnalytic` and
  `IsMeasurableAnalytic.isPavingAnalytic` give the inclusion of measurable sets into these classes.

## References

The interval-paving arguments follow He, Wang, and Yan, Semimartingale Theory and Stochastic
Calculus, first edition, Routledge (1992), Theorems 1.31–1.32, ISBN 978-0-8493-7715-0.
-/
@[expose] public section

open scoped MeasureTheory
open MeasureTheory

namespace MeasureTheory.Analytic.Paving

variable {𝓧 𝓨 𝓚 𝓚' ι : Type*} {p : Set (Set 𝓧)} {q : Set (Set 𝓚)}
  {s t : Set 𝓧} {f : ℕ → Set 𝓧}

lemma isPavingAnalytic_of_measurableSet_generateFrom (hp_empty : ∅ ∈ p)
    (hp : ∀ s, s ∈ p → IsPavingAnalytic p sᶜ)
    (hs : MeasurableSet[MeasurableSpace.generateFrom p] s) :
    IsPavingAnalytic p s := by
  let G : Set (Set 𝓧) := {t | IsPavingAnalytic p t ∧ IsPavingAnalytic p tᶜ}
  suffices s ∈ G by
    simp only [Set.mem_ofPred_eq, G] at this
    exact this.1
  have hsG : MeasurableSet[MeasurableSpace.generateFrom G] s := by
    have h_subset : {t | p t} ⊆ G := by
      intro t ht
      simp only [Set.mem_ofPred_eq, G]
      exact ⟨isPavingAnalytic_of_mem ht, hp t ht⟩
    have h_mono := MeasurableSpace.generateFrom_mono h_subset
    exact h_mono s hs
  refine MeasurableSpace.induction_on_inter (s := G) (C := fun s hs ↦ s ∈ G) ?_ ?_ ?_ ?_ ?_ ?_ s hsG
  · rfl
  · intro s hs t ht hst
    simp only [Set.mem_ofPred_eq, G] at hs ht ⊢
    rw [Set.compl_inter]
    exact ⟨hs.1.inter ht.1, hs.2.union ht.2⟩
  · simp only [Set.mem_ofPred_eq, Set.compl_empty, G]
    specialize hp ∅ hp_empty
    simp only [Set.compl_empty] at hp
    exact ⟨isPavingAnalytic_of_mem hp_empty, hp⟩
  · exact fun _ ↦ id
  · simp only [Set.mem_ofPred_eq, compl_compl, and_imp, G]
    intro t _ ht htc
    exact ⟨htc, ht⟩
  · intro f hf_disj hf_meas hfG
    simp only [Set.mem_ofPred_eq, Set.compl_iUnion, G] at hfG ⊢
    exact ⟨IsPavingAnalytic.iUnion fun n ↦ (hfG n).1,
      IsPavingAnalytic.iInter fun n ↦ (hfG n).2⟩

lemma Iic_mem_countableSupClosure_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    (u : ι) :
  Set.Iic u ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  by_cases h_bot : ∃ x : ι, IsBot x
  · obtain ⟨x, hx_bot⟩ := h_bot
    refine subset_countableSupClosure ⟨x, u, ?_⟩
    ext y
    simp only [Set.mem_Icc, Set.mem_Iic, and_iff_right_iff_imp]
    exact fun _ ↦ hx_bot y
  obtain ⟨u₁, hu₁_anti, hu₁_tendsto⟩ := Filter.exists_seq_antitone_tendsto_atTop_atBot ι
  rw [mem_countableSupClosure_iff_iSup]
  refine ⟨fun n ↦ Set.Icc (u₁ n) u, fun n ↦ ⟨u₁ n, u, rfl⟩, ?_⟩
  ext x
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_Icc, exists_and_right, Set.mem_Iic,
    and_iff_right_iff_imp]
  intro hxu
  exact (hu₁_tendsto.eventually_le_atBot x).exists

lemma Ici_mem_countableSupClosure_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    (u : ι) :
  Set.Ici u ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  by_cases h_top : ∃ x : ι, IsTop x
  · obtain ⟨x, hx_top⟩ := h_top
    refine subset_countableSupClosure ⟨u, x, ?_⟩
    ext y
    simp only [Set.mem_Icc, Set.mem_Ici, and_iff_left_iff_imp]
    exact fun _ ↦ hx_top y
  obtain ⟨u₁, hu₁_anti, hu₁_tendsto⟩ := Filter.exists_seq_monotone_tendsto_atTop_atTop ι
  rw [mem_countableSupClosure_iff_iSup]
  refine ⟨fun n ↦ Set.Icc u (u₁ n), fun n ↦ ⟨u, u₁ n, rfl⟩, ?_⟩
  ext x
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Set.mem_Icc, exists_and_left, Set.mem_Ici,
    and_iff_left_iff_imp]
  intro hxu
  exact (hu₁_tendsto.eventually_ge_atTop x).exists

lemma Iio_mem_countableSupClosure_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    [DenselyOrdered ι]
    (u : ι) :
    Set.Iio u ∈ countableSupClosure (insert ∅ {t | ∃ a b, Set.Icc a b = t}) := by
  by_cases h_bot : IsBot u
  · have : Set.Iio u = ∅ := by
      ext x
      simp only [Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact h_bot x
    rw [this]
    refine subset_countableSupClosure (Or.inl rfl)
  obtain ⟨v, hvu⟩ : ∃ v, v < u := by simpa [IsBot] using h_bot
  obtain ⟨s, hs_mono, hs_lt, hs_tendsto⟩ := exists_seq_strictMono_tendsto' hvu
  have : Set.Iio u = ⋃ n, Set.Iic (s n) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    refine ⟨fun hxu ↦ ?_, fun ⟨i, hi⟩ ↦ hi.trans_lt (hs_lt i).2⟩
    exact (hs_tendsto.eventually_const_le hxu).exists
  rw [this]
  have h_mem := countableSupClosed_countableSupClosure.iSup_mem
    fun n ↦ Iic_mem_countableSupClosure_Icc (s n)
  exact (countableSupClosure_mono fun s hs ↦ Set.mem_insert_of_mem _ hs) h_mem

lemma Ioi_mem_countableSupClosure_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι]
    [DenselyOrdered ι]
    (u : ι) :
    Set.Ioi u ∈ countableSupClosure (insert ∅ {t | ∃ a b, Set.Icc a b = t}) := by
  by_cases h_top : IsTop u
  · have : Set.Ioi u = ∅ := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_empty_iff_false, iff_false, not_lt]
      exact h_top x
    rw [this]
    refine subset_countableSupClosure (Or.inl rfl)
  obtain ⟨v, huv⟩ : ∃ v, u < v := by simpa [IsTop] using h_top
  obtain ⟨s, hs_mono, hs_gt, hs_tendsto⟩ := exists_seq_strictAnti_tendsto' huv
  have : Set.Ioi u = ⋃ n, Set.Ici (s n) := by
    ext x
    simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ici]
    refine ⟨fun hxu ↦ ?_, fun ⟨i, hi⟩ ↦ (hs_gt i).1.trans_le hi⟩
    exact (hs_tendsto.eventually_le_const hxu).exists
  rw [this]
  have h_mem := countableSupClosed_countableSupClosure.iSup_mem
    fun n ↦ Ici_mem_countableSupClosure_Icc (s n)
  exact (countableSupClosure_mono fun s hs ↦ Set.mem_insert_of_mem _ hs) h_mem

lemma univ_mem_countableSupClosure_Icc {ι : Type*} [hι : Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] :
    (Set.univ : Set ι) ∈ countableSupClosure {t | ∃ a b, Set.Icc a b = t} := by
  obtain x : ι := hι.some
  have : (Set.univ : Set ι) = Set.Iic x ∪ Set.Ici x := by ext; simp
  rw [this]
  exact supClosed_countableSupClosure (Iic_mem_countableSupClosure_Icc x)
    (Ici_mem_countableSupClosure_Icc x)

private lemma complement_Icc_mem_countableSupClosure_insert_empty {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] (l u : ι) :
    (Set.Icc l u)ᶜ ∈ countableSupClosure (insert ∅ {t | ∃ a b, Set.Icc a b = t}) := by
  rcases lt_or_ge u l with hlu | hlu
  · simp only [not_le, hlu, Set.Icc_eq_empty, Set.compl_empty]
    exact (countableSupClosure_mono fun s hs ↦ Set.mem_insert_of_mem _ hs)
      univ_mem_countableSupClosure_Icc
  · have : (Set.Icc l u)ᶜ = Set.Iio l ∪ Set.Ioi u := by ext; simp; grind
    rw [this]
    exact supClosed_countableSupClosure (Iio_mem_countableSupClosure_Icc l)
      (Ioi_mem_countableSupClosure_Icc u)

private lemma complement_prod_mem_countableSupClosure_measurableSet_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [MeasurableSpace 𝓧] (s : Set (𝓧 × ι))
    (hs : s ∈ Set.image2 (· ×ˢ ·) MeasurableSet (insert ∅ {t | ∃ a b, Set.Icc a b = t})) :
     sᶜ ∈ countableSupClosure
       (Set.image2 (· ×ˢ ·) MeasurableSet (insert ∅ {t | ∃ a b, Set.Icc a b = t})) := by
  obtain ⟨A, hA, K, hK_eq, rfl⟩ := hs
  simp only [Set.mem_insert_iff, Set.mem_ofPred_eq] at hK_eq
  cases hK_eq with
  | inl hK_eq =>
    simp only [hK_eq, Set.prod_empty, Set.compl_empty]
    refine (countableSupClosure_mono
      (a := Set.image2 (· ×ˢ ·) MeasurableSet {t | ∃ a b : ι, Set.Icc a b = t}) ?_) ?_
    · intro s hs
      refine mem_image2_prod_mono (p := Set.ofPred (MeasurableSet (α := 𝓧)))
        (q := {t | ∃ a b : ι, Set.Icc a b = t}) (fun _ hs ↦ hs) ?_ hs
      exact fun _ hs ↦ Set.mem_insert_of_mem _ hs
    have h_mem_sigma := univ_mem_countableSupClosure_Icc (ι := ι)
    rw [mem_countableSupClosure_iff_iSup] at h_mem_sigma ⊢
    obtain ⟨B, hB, h_eq⟩ := h_mem_sigma
    have h_univ_prod : (Set.univ : Set 𝓧) ×ˢ (Set.univ : Set ι) = Set.univ := by simp
    rw [← h_univ_prod, ← h_eq, Set.iSup_eq_iUnion, Set.prod_iUnion]
    refine ⟨fun i ↦ Set.univ ×ˢ B i, fun n ↦ ?_, rfl⟩
    exact ⟨Set.univ, .univ, B n, hB n, rfl⟩
  | inr hK_eq =>
    obtain ⟨l, u, rfl⟩ := hK_eq
    have hK' := complement_Icc_mem_countableSupClosure_insert_empty l u
    rw [Set.compl_prod_eq_union]
    refine supClosed_countableSupClosure ?_ ?_
    · have h := univ_mem_countableSupClosure_Icc (ι := ι)
      rw [mem_countableSupClosure_iff_iSup] at h ⊢
      obtain ⟨B, hB, h_eq⟩ := h
      rw [← h_eq, Set.iSup_eq_iUnion, Set.prod_iUnion]
      refine ⟨fun i ↦ Aᶜ ×ˢ B i, fun n ↦ ?_, rfl⟩
      exact ⟨Aᶜ, hA.compl, B n, Set.mem_insert_of_mem _ (hB n), rfl⟩
    · have h := complement_Icc_mem_countableSupClosure_insert_empty l u
      rw [mem_countableSupClosure_iff_iSup] at h ⊢
      obtain ⟨B, hB, h_eq⟩ := h
      rw [← h_eq, Set.iSup_eq_iUnion, Set.prod_iUnion]
      refine ⟨fun i ↦ Set.univ ×ˢ B i, fun n ↦ ?_, rfl⟩
      exact ⟨Set.univ, .univ, B n, hB n, rfl⟩

lemma borel_eq_generateFrom_isCompact :
    borel ℝ = MeasurableSpace.generateFrom {s : Set ℝ | IsCompact s} := by
  refine le_antisymm ?_ ?_
  · rw [borel_eq_generateFrom_Icc]
    refine MeasurableSpace.generateFrom_mono fun s hs ↦ ?_
    obtain ⟨a, b, hab, rfl⟩ := hs
    exact isCompact_Icc
  · rw [MeasurableSpace.generateFrom_le_iff]
    exact fun _ hs ↦ hs.measurableSet

private lemma borel_eq_generateFrom_all_Icc (α : Type*)
    [TopologicalSpace α] [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] :
    borel α = .generateFrom {S : Set α | ∃ l u, Set.Icc l u = S} := by
  rw [borel_eq_generateFrom_Icc]
  refine le_antisymm ?_ ?_
  · exact MeasurableSpace.generateFrom_mono fun s ⟨l, u, hlu, hs⟩ ↦ ⟨l, u, hs⟩
  · rw [MeasurableSpace.generateFrom_le_iff]
    rintro s ⟨a, b, rfl⟩
    rcases le_or_gt a b with hab | hab
    · exact MeasurableSpace.measurableSet_generateFrom ⟨a, b, hab, rfl⟩
    · simp [hab]

private lemma borel_eq_generateFrom_insert_empty_Icc (α : Type*)
    [TopologicalSpace α] [SecondCountableTopology α] [LinearOrder α] [OrderTopology α] :
    borel α = .generateFrom (insert ∅ {S : Set α | ∃ l u, Set.Icc l u = S}) := by
  rw [MeasurableSpace.generateFrom_insert_empty]
  exact borel_eq_generateFrom_all_Icc α

-- Interval-paving specialization of He, Wang, and Yan, Theorem 1.32(i).
lemma MeasurableSet.isPavingAnalytic_Icc {ι : Type*} {mι : MeasurableSpace ι}
    [LinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [BorelSpace ι]
    {s : Set ι} (hs : MeasurableSet s) :
    IsPavingAnalytic (insert ∅ {t | ∃ a b, Set.Icc a b = t}) s := by
  by_cases! h_lt : ∃ l u : ι, l < u
  swap
  · rcases isEmpty_or_nonempty ι with h_empty | h_nonempty
    · simp only [IsEmpty.exists_iff, Set.ofPred_false, insert_empty_eq]
      refine isPavingAnalytic_of_mem ?_
      simp [Set.eq_empty_of_isEmpty s]
    · obtain ⟨x⟩ := h_nonempty
      have : Subsingleton ι := ⟨fun y z ↦ le_antisymm (h_lt z y) (h_lt y z)⟩
      have : {t | ∃ a b, Set.Icc a b = t} = {{x}} := by
        refine subset_antisymm ?_ ?_
        · rintro _ ⟨l, u, rfl⟩
          simp [Subsingleton.elim _ x]
        · intro s
          simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
          rintro rfl
          exact ⟨x, x, by simp⟩
      simp only [this]
      refine isPavingAnalytic_of_mem ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hxs : x ∈ s
      · right; ext; simp [hxs, Subsingleton.elim _ x]
      · left; ext; simp [hxs, Subsingleton.elim _ x]
  obtain ⟨l₀, u₀, hlu₀⟩ := h_lt
  have : Nonempty ι := ⟨l₀⟩
  have hmι : mι = borel ι := BorelSpace.measurable_eq
  have hs' : MeasurableSet[MeasurableSpace.generateFrom
      (insert ∅ {t | ∃ a b, Set.Icc a b = t})] s := by
    rwa [hmι, borel_eq_generateFrom_insert_empty_Icc] at hs
  refine isPavingAnalytic_of_measurableSet_generateFrom ?_ ?_ hs'
  · simp
  · intro s hs
    refine isPavingAnalytic_of_mem_countableSupClosure_of_imp
      (p' := insert ∅ {t | ∃ a b, Set.Icc a b = t}) ?_ (fun K hK ↦ isPavingAnalytic_of_mem hK)
    simp only [Set.mem_insert_iff, Set.mem_ofPred_eq] at hs
    cases hs with
    | inl h =>
      simp only [h, Set.compl_empty]
      exact (countableSupClosure_mono fun s hs ↦ Set.mem_insert_of_mem _ hs)
        univ_mem_countableSupClosure_Icc
    | inr h =>
      obtain ⟨l, u, rfl⟩ := h
      exact complement_Icc_mem_countableSupClosure_insert_empty l u

lemma IsPavingAnalytic_measurableSet_iff_isPavingAnalytic_Icc {ι : Type*} {mι : MeasurableSpace ι}
    [LinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [BorelSpace ι]
    (s : Set ι) :
    IsPavingAnalytic {t | MeasurableSet t} s ↔
      IsPavingAnalytic (insert ∅ {t | ∃ a b, Set.Icc a b = t}) s := by
  refine ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩
  · rw [← isPavingAnalytic_isPavingAnalytic_iff]
    exact hs.mono fun s hs ↦ MeasurableSet.isPavingAnalytic_Icc hs
  · refine hs.mono fun s hs ↦ ?_
    simp only [Set.mem_insert_iff, Set.mem_ofPred_eq] at hs
    cases hs with
    | inl h => simp [h]
    | inr h =>
      obtain ⟨l, u, rfl⟩ := h
      simp

lemma isCountablySpanning_insert_empty_Icc {ι : Type*} [Nonempty ι]
    [LinearOrder ι] [TopologicalSpace ι] [SecondCountableTopology ι] [OrderTopology ι] :
    IsCountablySpanning (insert ∅ {t | ∃ a b : ι, Set.Icc a b = t}) := by
  have h := univ_mem_countableSupClosure_Icc (ι := ι)
  rw [mem_countableSupClosure_iff_iSup] at h
  obtain ⟨A, hA, h_eq⟩ := h
  exact ⟨A, fun n ↦ Set.mem_insert_of_mem _ (hA n), h_eq⟩

-- Interval-paving specialization of He, Wang, and Yan, Theorem 1.32(ii).
lemma _root_.MeasurableSet.isPavingAnalytic_image2_prod {ι : Type*} {mι : MeasurableSpace ι}
    [LinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [BorelSpace ι] [Nonempty ι]
    {s : Set (𝓧 × ι)} {m𝓧 : MeasurableSpace 𝓧}
    (hs : MeasurableSet s) :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) MeasurableSet
      (insert ∅ {t | ∃ a b, Set.Icc a b = t})) s := by
  have h_compl (t : Set (𝓧 × ι))
        (ht : t ∈ Set.image2 (· ×ˢ ·) MeasurableSet (insert ∅ {t | ∃ a b, Set.Icc a b = t})) :
      IsPavingAnalytic (Set.image2 (· ×ˢ ·) MeasurableSet
        (insert ∅ {t | ∃ a b, Set.Icc a b = t})) tᶜ :=
    isPavingAnalytic_of_mem_countableSupClosure_of_imp (complement_prod_mem_countableSupClosure_measurableSet_Icc _ ht)
      fun s hs ↦ isPavingAnalytic_of_mem hs
  refine isPavingAnalytic_of_measurableSet_generateFrom ?_ h_compl ?_
  · have : (∅ : Set (𝓧 × ι)) = ∅ ×ˢ ∅ := by simp
    rw [this]
    exact ⟨∅, MeasurableSet.empty, ∅, by simp, rfl⟩
  · convert hs
    have h_prod_eq := generateFrom_eq_prod (α := 𝓧) (β := ι)
      (C := Set.ofPred (MeasurableSet (α := 𝓧)))
      (D := insert ∅ {t | ∃ a b, Set.Icc a b = t}) MeasurableSpace.generateFrom_measurableSet ?_
      isCountablySpanning_measurableSet isCountablySpanning_insert_empty_Icc
    swap
    · have : mι = borel ι := BorelSpace.measurable_eq
      rw [this, borel_eq_generateFrom_insert_empty_Icc]
    rw [← h_prod_eq]
    congr with s

-- Interval-paving specialization of He, Wang, and Yan, Theorem 1.32(ii).
lemma isPavingAnalytic_image2_prod_measurableSet_Icc_iff {ι : Type*} {mι : MeasurableSpace ι}
    [LinearOrder ι] [DenselyOrdered ι] [TopologicalSpace ι] [SecondCountableTopology ι]
    [OrderTopology ι] [BorelSpace ι] [Nonempty ι]
    {s : Set (𝓧 × ι)} [MeasurableSpace 𝓧] :
    IsPavingAnalytic (Set.image2 (· ×ˢ ·) {t | MeasurableSet t}
        (insert ∅ {t | ∃ a b, Set.Icc a b = t})) s ↔
      IsPavingAnalytic {t | MeasurableSet t} s := by
  refine ⟨fun hs ↦ hs.mono fun s hs ↦ ?_, fun hs ↦ ?_⟩
  · obtain ⟨A, hA, K, hK, rfl⟩ := hs
    cases hK with
    | inl h =>
      simp only [h, Set.prod_empty]
      change MeasurableSet (∅ : Set (𝓧 × ι))
      exact MeasurableSet.empty
    | inr h =>
      obtain ⟨l, u, rfl⟩ := h
      exact hA.prod measurableSet_Icc
  · exact isPavingAnalytic_isPavingAnalytic
      (hs.mono fun _ ↦ MeasurableSet.isPavingAnalytic_image2_prod)

-- Interval-paving specialization of He, Wang, and Yan, Theorem 1.32(iii).
-- note that here `ι` is in `Type`, not `Type*`
lemma isPavingAnalytic_fst_of_image2_prod_measurableSet_Icc {ι : Type} [LinearOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [CompactIccSpace ι] [Nonempty ι] [MeasurableSpace 𝓧]
    {s : Set (𝓧 × ι)}
    (hs : IsPavingAnalytic (Set.image2 (· ×ˢ ·) {t | MeasurableSet t}
      (insert ∅ {t | ∃ a b, Set.Icc a b = t})) s) :
    IsPavingAnalytic {t | MeasurableSet t} (Prod.fst '' s) :=
  hs.fst (by simp : ∅ ∈ insert ∅ {t | ∃ a b, Set.Icc a b = t}) (isCompactSystem_insert_empty_Icc ι)

lemma _root_.MeasurableSet.isPavingAnalytic_fst {m𝓧 : MeasurableSpace 𝓧} {s : Set (𝓧 × ℝ)}
    (hs : MeasurableSet s) :
    IsPavingAnalytic MeasurableSet (Prod.fst '' s) :=
  isPavingAnalytic_fst_of_image2_prod_measurableSet_Icc
    (MeasurableSet.isPavingAnalytic_image2_prod hs)

/-- A set `s` of a measurable space `𝓧` is measurably analytic for a measurable space `𝓚` if it
is the projection of a measurable set of `𝓧 × 𝓚`. -/
def IsMeasurableAnalyticFor (𝓚 : Type*) [MeasurableSpace 𝓚] [MeasurableSpace 𝓧] (s : Set 𝓧) :
    Prop :=
  ∃ t : Set (𝓧 × 𝓚), MeasurableSet t ∧ s = Prod.fst '' t

lemma isMeasurableAnalyticFor_of_snd {_ : MeasurableSpace 𝓚} [MeasurableSpace 𝓧]
    {s : Set 𝓧} (t : Set (𝓚 × 𝓧)) (ht : MeasurableSet t) (hst : s = Prod.snd '' t) :
    IsMeasurableAnalyticFor 𝓚 s :=
  ⟨Prod.swap ⁻¹' t, ht.preimage (by fun_prop), by ext; simp [hst]⟩

/-- A set `s` of a measurable space `𝓧` is measurably analytic if it is the projection of
a measurable set of `𝓧 × ℝ`. -/
def IsMeasurableAnalytic [MeasurableSpace 𝓧] (s : Set 𝓧) : Prop := IsMeasurableAnalyticFor ℝ s

lemma isMeasurableAnalytic_of_snd [MeasurableSpace 𝓧] {s : Set 𝓧} (t : Set (ℝ × 𝓧))
    (ht : MeasurableSet t) (hst : s = Prod.snd '' t) :
    IsMeasurableAnalytic s :=
  isMeasurableAnalyticFor_of_snd t ht hst

/-- If a set is measurably analytic for any standard Borel space `𝓚`,
then it is measurably analytic for `ℝ`. -/
lemma IsMeasurableAnalyticFor.isMeasurableAnalytic {m𝓧 : MeasurableSpace 𝓧}
    {m𝓚 : MeasurableSpace 𝓚} [StandardBorelSpace 𝓚]
    (hs : IsMeasurableAnalyticFor 𝓚 s) :
    IsMeasurableAnalytic s := by
  obtain ⟨t, ht, rfl⟩ := hs
  refine ⟨Prod.map id (embeddingReal 𝓚) '' t, ?_, by ext; simp⟩
  refine MeasurableEmbedding.measurableSet_image' ?_ ht
  exact MeasurableEmbedding.id.prodMap (measurableEmbedding_embeddingReal 𝓚)

lemma _root_.MeasurableSet.isMeasurableAnalytic {m𝓧 : MeasurableSpace 𝓧} (hs : MeasurableSet s) :
    IsMeasurableAnalytic s :=
  ⟨s ×ˢ Set.univ, hs.prod .univ, by ext; simp⟩

lemma IsMeasurableAnalytic.isPavingAnalytic {m𝓧 : MeasurableSpace 𝓧} (hs : IsMeasurableAnalytic s) :
    IsPavingAnalytic MeasurableSet s := by
  obtain ⟨t, ht, rfl⟩ := hs
  exact MeasurableSet.isPavingAnalytic_fst ht


end MeasureTheory.Analytic.Paving

end
