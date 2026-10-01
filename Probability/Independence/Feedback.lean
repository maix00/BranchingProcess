module

public import Probability.Independence.FinitePartition

/-!
# A binary choice based on independent past information

The choice of one of two future events can depend on the past. Independence
is applied separately on the two measurable cells of the past.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- A past-measurable binary choice between two independent future events
has at least the smaller of their probabilities, conditional on an admissible
past event. -/
theorem measure_adaptiveChoice_ge_mul
    {Ω Past Future : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Past] [MeasurableSpace Future]
    (P : Measure Ω) (past : Ω → Past) (next : Ω → Future)
    (hindep : past ⟂ᵢ[P] next)
    (hpast : AEMeasurable past P) (hnext : AEMeasurable next P)
    (U S : Set Past) (Vplus Vminus : Set Future)
    (hU : MeasurableSet U) (hS : MeasurableSet S)
    (hVplus : MeasurableSet Vplus) (hVminus : MeasurableSet Vminus)
    (q : ENNReal)
    (hqplus : q ≤ P (next ⁻¹' Vplus))
    (hqminus : q ≤ P (next ⁻¹' Vminus)) :
    q * P (past ⁻¹' U) ≤
      P (((past ⁻¹' (U ∩ S)) ∩ (next ⁻¹' Vminus)) ∪
        ((past ⁻¹' (U ∩ Sᶜ)) ∩ (next ⁻¹' Vplus))) := by
  let A : Bool → Set Ω := fun b =>
    past ⁻¹' (U ∩ if b then S else Sᶜ)
  let B : Bool → Set Ω := fun b =>
    next ⁻¹' if b then Vminus else Vplus
  have hA : ∀ b, NullMeasurableSet (A b) P := by
    intro b
    change NullMeasurableSet (past ⁻¹' (U ∩ if b then S else Sᶜ)) P
    split_ifs
    · exact hpast.nullMeasurableSet_preimage (hU.inter hS)
    · exact hpast.nullMeasurableSet_preimage (hU.inter hS.compl)
  have hB : ∀ b, NullMeasurableSet (B b) P := by
    intro b
    change NullMeasurableSet (next ⁻¹' if b then Vminus else Vplus) P
    split_ifs
    · exact hnext.nullMeasurableSet_preimage hVminus
    · exact hnext.nullMeasurableSet_preimage hVplus
  have hdisj : Pairwise (fun b c => Disjoint (A b) (A c)) := by
    intro b c hbc
    cases b <;> cases c <;> simp_all [A, Set.disjoint_left]
  have hfactor : ∀ b, P (A b ∩ B b) = P (A b) * P (B b) := by
    intro b
    cases b
    · exact hindep.measure_inter_preimage_eq_mul _ _
        (hU.inter hS.compl) hVplus
    · exact hindep.measure_inter_preimage_eq_mul _ _
        (hU.inter hS) hVminus
  have hlower : ∀ b, q ≤ P (B b) := by
    intro b
    cases b
    · simpa [B] using hqplus
    · simpa [B] using hqminus
  have hbound := measure_iUnion_inter_ge_mul_of_finite_partition
    P A B q hA hB hdisj hfactor hlower
  have hunion : (⋃ b, A b) = past ⁻¹' U := by
    ext ω
    by_cases hs : past ω ∈ S <;>
      simp [A, Set.mem_iUnion, Bool.exists_bool, hs]
  rw [hunion] at hbound
  have hrhs : (⋃ b, A b ∩ B b) =
      ((past ⁻¹' (U ∩ S)) ∩ (next ⁻¹' Vminus)) ∪
        ((past ⁻¹' (U ∩ Sᶜ)) ∩ (next ⁻¹' Vplus)) := by
    ext ω
    simp [A, B, Bool.exists_bool, or_comm]
  rw [hrhs] at hbound
  exact hbound

/-- Finite feedback induction from independence of each fresh block from
the information used to select it. No independence is assumed for the
adaptively selected event itself. -/
theorem measure_adaptiveSuccess_ge_pow
    {Ω Past Future : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Past] [MeasurableSpace Future]
    (P : Measure Ω) (past : ℕ → Ω → Past) (next : ℕ → Ω → Future)
    (U S : ℕ → Set Past) (Vplus Vminus : ℕ → Set Future)
    (q : ENNReal)
    (hzero : P (past 0 ⁻¹' U 0) = 1)
    (hindep : ∀ k, past k ⟂ᵢ[P] next k)
    (hpast : ∀ k, AEMeasurable (past k) P)
    (hnext : ∀ k, AEMeasurable (next k) P)
    (hU : ∀ k, MeasurableSet (U k))
    (hS : ∀ k, MeasurableSet (S k))
    (hVplus : ∀ k, MeasurableSet (Vplus k))
    (hVminus : ∀ k, MeasurableSet (Vminus k))
    (hqplus : ∀ k, q ≤ P (next k ⁻¹' Vplus k))
    (hqminus : ∀ k, q ≤ P (next k ⁻¹' Vminus k))
    (hstep : ∀ k,
      ((past k ⁻¹' (U k ∩ S k)) ∩ (next k ⁻¹' Vminus k)) ∪
        ((past k ⁻¹' (U k ∩ (S k)ᶜ)) ∩ (next k ⁻¹' Vplus k)) ⊆
          past (k + 1) ⁻¹' U (k + 1)) :
    ∀ n, q ^ n ≤ P (past n ⁻¹' U n) := by
  intro n
  induction n with
  | zero => simp [hzero]
  | succ k ih =>
    have hchoice := measure_adaptiveChoice_ge_mul P (past k) (next k)
      (hindep k) (hpast k) (hnext k)
      (U k) (S k) (Vplus k) (Vminus k)
      (hU k) (hS k) (hVplus k) (hVminus k) q
      (hqplus k) (hqminus k)
    calc
      q ^ (k + 1) = q * q ^ k := pow_succ' q k
      _ ≤ q * P (past k ⁻¹' U k) := by
        simpa [mul_comm] using mul_le_mul_left ih q
      _ ≤ P (((past k ⁻¹' (U k ∩ S k)) ∩
          (next k ⁻¹' Vminus k)) ∪
          ((past k ⁻¹' (U k ∩ (S k)ᶜ)) ∩
          (next k ⁻¹' Vplus k))) := hchoice
      _ ≤ P (past (k + 1) ⁻¹' U (k + 1)) :=
        measure_mono (hstep k)

end ProbabilityTheory

end
