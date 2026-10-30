/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, WANG Yiyang
-/

module

public import MeasureTheory.Analytic.Capacity.Basic
import Order.SetDissipate

/-!
# Capacitability of countable paving closures

## Public declarations

- `MeasureTheory.Analytic.Paving.isCapacitable_mem_countableInfClosure_countableSupClosure`:
  for a capacity $m$ on $p$, if $p$ contains $\varnothing$ and is closed under
  finite intersections and unions, and
  $s\in\operatorname{countableInfClosure}
      (\operatorname{countableSupClosure}(p))$,
  then every $a<m(s)$ admits $t\in\operatorname{countableInfClosure}(p)$
  such that $t\subseteq s$ and $a\le m(t)$.

This is Theorem 1.34 of He, Wang, and Yan, *Semimartingale Theory and
Stochastic Calculus*, first edition, Routledge (1992), ISBN
978-0-8493-7715-0.
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

section Aux

/-- Auxiliary definition for `isCapacitable_mem_countableInfClosure_countableSupClosure`. -/
private noncomputable
def qaux (m : Capacity p) (s : Set 𝓧) (A : ℕ → ℕ → Set 𝓧) (a : ℝ≥0∞) (k : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j ≤ n, a < m (s ∩ Set.dissipate (fun i ↦ A i (k i)) j)

/-- Auxiliary definition for `isCapacitable_mem_countableInfClosure_countableSupClosure`. -/
private noncomputable
def nat0 {A : ℕ → ℕ → Set 𝓧} (hA_mono : ∀ (n : ℕ), Monotone (A n))
    (hs_eq : ⋂ n, ⋃ m, A n m = s) (a : ℝ≥0∞) (ha : a < m s) :
    {n : ℕ | a < m (s ∩ A 0 n)} :=
  have : m s = ⨆ n, m (s ∩ A 0 n) := by
    rw [← capacity_iUnion]
    · rw [← Set.inter_iUnion]
      congr
      refine subset_antisymm ?_ Set.inter_subset_left
      rw [← hs_eq]
      simp only [Set.subset_inter_iff, subset_refl, true_and]
      exact Set.iInter_subset _ 0
    · intro i j hij
      simp only [Set.subset_inter_iff, Set.inter_subset_left, true_and]
      refine Set.inter_subset_right.trans ?_
      exact hA_mono 0 hij
  have : ∃ n, a < m (s ∩ A 0 n) := by
    rw [this] at ha
    exact lt_iSup_iff.mp ha
  ⟨this.choose, this.choose_spec⟩

/-- Auxiliary definition for `isCapacitable_mem_countableInfClosure_countableSupClosure`. -/
private noncomputable
def succ {A : ℕ → ℕ → Set 𝓧} (hA_mono : ∀ (n : ℕ), Monotone (A n))
    (hs_eq : ⋂ n, ⋃ m, A n m = s) {a : ℝ≥0∞} {n : ℕ}
    (k : {seq : ℕ → ℕ | qaux m s A a seq n}) :
    {j : ℕ → ℕ | qaux m s A a j (n + 1)} :=
  have : m (s ∩ Set.dissipate (fun i ↦ A i (k.1 i)) n)
      = ⨆ j, m (s ∩ Set.dissipate (fun i ↦ A i (k.1 i)) n ∩ A (n + 1) j) := by
    rw [← capacity_iUnion]
    · rw [← Set.inter_iUnion]
      congr 1
      refine subset_antisymm ?_ Set.inter_subset_left
      rw [Set.inter_assoc, Set.inter_comm _ (⋃ i, _), ← Set.inter_assoc]
      refine Set.inter_subset_inter_left _ ?_
      rw [← hs_eq]
      simp only [Set.subset_inter_iff, subset_refl, true_and]
      exact Set.iInter_subset _ (n + 1)
    · intro i j hij
      simp only [Set.mem_ofPred_eq, Set.subset_inter_iff]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact Set.inter_subset_left.trans Set.inter_subset_left
      · exact Set.inter_subset_left.trans Set.inter_subset_right
      · refine Set.inter_subset_right.trans ?_
        exact hA_mono (n + 1) hij
  have : ∃ j, a < m (s ∩ Set.dissipate (fun i ↦ A i (k.1 i)) n ∩ A (n + 1) j) := by
    have hk := k.2 n le_rfl
    rw [this] at hk
    exact lt_iSup_iff.mp hk
  ⟨fun i ↦ if i ≤ n then k.1 i else this.choose, by
    simp only [qaux, Set.mem_ofPred_eq]
    intro j hj
    rw [Nat.le_succ_iff] at hj
    cases hj with
    | inl h_le =>
      convert k.2 j h_le using 3
      exact Set.dissipate_congr fun i hi ↦ by simp [hi.trans h_le]
    | inr h_eq =>
      simp only [h_eq, Nat.succ_eq_add_one, Set.dissipate_succ, add_le_iff_nonpos_right,
        nonpos_iff_eq_zero, one_ne_zero, ↓reduceIte]
      convert this.choose_spec using 2
      rw [Set.inter_assoc]
      congr 2
      exact Set.dissipate_congr fun i hi ↦ by simp [hi]⟩

/-- Auxiliary definition for `isCapacitable_mem_countableInfClosure_countableSupClosure`. -/
private noncomputable
def seqAux (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (A : ℕ → ℕ → Set 𝓧) (hpA : ∀ (n m : ℕ), A n m ∈ p) (hA_mono : ∀ (n : ℕ), Monotone (A n))
    (hs_eq : ⋂ n, ⋃ m, A n m = s) (a : ℝ≥0∞) (ha : a < m s) :
    (n : ℕ) → {seq : ℕ → ℕ | qaux m s A a seq n}
  | 0 => ⟨fun _ ↦ nat0 hA_mono hs_eq a ha, by
    simp only [qaux, nonpos_iff_eq_zero, forall_eq, Set.dissipate_zero_nat, Set.mem_ofPred_eq]
    exact (nat0 hA_mono hs_eq a ha).2⟩
  | n + 1 => succ hA_mono hs_eq
    (seqAux hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha n)

private lemma seqAux_add_one (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (A : ℕ → ℕ → Set 𝓧) (hpA : ∀ (n m : ℕ), A n m ∈ p) (hA_mono : ∀ (n : ℕ), Monotone (A n))
    (hs_eq : ⋂ n, ⋃ m, A n m = s) (a : ℝ≥0∞) (ha : a < m s) (n : ℕ) :
    seqAux hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha (n + 1) =
      succ hA_mono hs_eq
        (seqAux hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha n) := rfl

private lemma seqAux_add_one_apply_of_le (hp_empty : ∅ ∈ p)
    (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (A : ℕ → ℕ → Set 𝓧) (hpA : ∀ (n m : ℕ), A n m ∈ p) (hA_mono : ∀ (n : ℕ), Monotone (A n))
    (hs_eq : ⋂ n, ⋃ m, A n m = s) (a : ℝ≥0∞) (ha : a < m s) {n i : ℕ} (hin : i ≤ n) :
    (seqAux hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha (n + 1)).1 i =
      (seqAux hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha n).1 i := by
  rw [seqAux_add_one]
  simp only [Set.mem_ofPred_eq, succ, ite_eq_left_iff, not_le]
  intro hni
  grind

private lemma seqAux_of_le (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (A : ℕ → ℕ → Set 𝓧) (hpA : ∀ (n m : ℕ), A n m ∈ p) (hA_mono : ∀ (n : ℕ), Monotone (A n))
    (hs_eq : ⋂ n, ⋃ m, A n m = s) (a : ℝ≥0∞) (ha : a < m s) {i j : ℕ} (hij : i ≤ j) :
    (seqAux hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha i).1 i =
      (seqAux hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha j).1 i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ n hin ih => rw [ih, seqAux_add_one_apply_of_le]; exact hin

/-- Auxiliary definition for `isCapacitable_mem_countableInfClosure_countableSupClosure`. -/
private noncomputable
def seq (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (A : ℕ → ℕ → Set 𝓧) (hpA : ∀ (n m : ℕ), A n m ∈ p) (hA_mono : ∀ (n : ℕ), Monotone (A n))
    (hs_eq : ⋂ n, ⋃ m, A n m = s) (a : ℝ≥0∞) (ha : a < m s) (n : ℕ) : ℕ :=
  (seqAux hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha n).1 n

private lemma seq_prop (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (A : ℕ → ℕ → Set 𝓧) (hpA : ∀ (n m : ℕ), A n m ∈ p) (hA_mono : ∀ (n : ℕ), Monotone (A n))
    (hs_eq : ⋂ n, ⋃ m, A n m = s) (a : ℝ≥0∞) (ha : a < m s) (n : ℕ) :
    qaux m s A a (seq hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha) n := by
  simp only [qaux]
  have h1 := (seqAux hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha n).2
  simp only [qaux] at h1
  intro j hj
  convert h1 j hj using 3
  refine Set.dissipate_congr fun i hi ↦ ?_
  congr
  simp only [seq, Set.mem_ofPred_eq]
  exact seqAux_of_le hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha (hi.trans hj)

end Aux

-- He, Wang, and Yan, Theorem 1.34.
lemma isCapacitable_mem_countableInfClosure_countableSupClosure (m : Capacity p)
    (hp_empty : ∅ ∈ p) (hp_inter : InfClosed p) (hp_union : SupClosed p)
    (hs : s ∈ countableInfClosure (countableSupClosure p)) :
    IsCapacitable m s := by
  rw [mem_countableInfClosure_iff_iInf] at hs
  obtain ⟨A, hA, hs_eq⟩ := hs
  simp_rw [SupClosed.mem_countableSupClosure_iff hp_union] at hA
  choose A hpA hA_mono h_eq using hA
  simp_rw [h_eq] at hs_eq
  intro a ha
  obtain ⟨k, hk⟩ : ∃ k : ℕ → ℕ, ∀ n, a < m (s ∩ Set.dissipate (fun i ↦ A i (k i)) n) := by
    refine ⟨seq hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha, fun n ↦ ?_⟩
    exact seq_prop hp_empty hp_inter hp_union A hpA hA_mono hs_eq a ha n n le_rfl
  let B n := Set.dissipate (fun i ↦ A i (k i)) n
  have hB_gt n : a < m (B n) := (hk n).trans_le (m.mono Set.inter_subset_right)
  have hB_mem n : B n ∈ p := by
    unfold B
    induction n with
    | zero => simp [hpA]
    | succ n hn =>
      rw [Set.dissipate_succ]
      exact hp_inter hn (hpA _ _)
  simp_rw [mem_countableInfClosure_iff_iInf]
  refine ⟨⋂ n, B n, ⟨B, hB_mem, rfl⟩, ?_, ?_⟩
  · rw [← hs_eq, Set.iInf_eq_iInter]
    gcongr with n
    calc B n
    _ ⊆ A n (k n) := Set.dissipate_subset le_rfl
    _ ⊆ ⋃ m, A n m := by intro x hx; simp only [Set.mem_iUnion]; exact ⟨k n, hx⟩
  · rw [capacity_iInter Set.antitone_dissipate hB_mem]
    simp only [le_iInf_iff]
    exact fun n ↦ (hB_gt n).le

end MeasureTheory.Analytic.Paving

end
