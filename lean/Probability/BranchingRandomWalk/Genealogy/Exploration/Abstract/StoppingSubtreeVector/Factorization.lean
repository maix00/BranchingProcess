import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.StoppingSubtreeVector.Cell

/-!
# Factorization of stopped subtree-vector events

A measurable vector of distinct nodes at the finite stopping generation has
fresh descendant step fields, independent of the stopped past with product law.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


theorem stopped_selectedSubtreeStepFieldVector_event_factorization
    {κ α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (τ : (TreeNode α → Step α X) → WithTop ℕ)
    (hτ : IsStoppingTime
      (generationFiltration (M := Step α X)) τ)
    (hfinite : ∀ ω, τ ω ≠ ⊤)
    (roots : (TreeNode α → Step α X) → κ → TreeNode α)
    (hcount : (Set.range roots).Countable)
    (hfiber : ∀ r, MeasurableSet[hτ.measurableSpace]
      {ω | roots ω = r})
    (hdepth : ∀ ω (n : ℕ), τ ω = (n : WithTop ℕ) →
      ∀ i, (roots ω i).length = n)
    (hinj : ∀ ω, Function.Injective (roots ω))
    (A : Set (TreeNode α → Step α X))
    (B : Set (κ → TreeNode α → Step α X))
    (hA : MeasurableSet[hτ.measurableSpace] A)
    (hB : MeasurableSet B) :
    stepFieldLaw μ
        (A ∩ selectedSubtreeStepFieldVector roots ⁻¹' B) =
      stepFieldLaw μ A *
        (Measure.infinitePi (fun _ : κ => stepFieldLaw μ)) B := by
  let P := stepFieldLaw μ
  let Q := Measure.infinitePi (fun _ : κ => stepFieldLaw μ)
  let S : Set (κ → TreeNode α) := Set.range roots
  let _ : Countable S := Set.countable_coe_iff.mpr hcount
  let C := fun p : ℕ × S =>
    abstractStoppedVectorCell τ roots A (p.1, p.2.1)
  let D := fun p : ℕ × S =>
    C p ∩ subtreeStepFieldVector p.2.1 ⁻¹' B
  have hCmeas (p : ℕ × S) : MeasurableSet (C p) :=
    (generationFiltration (M := Step α X) |>.le p.1) _
      (abstractStoppedVectorCell_measurable τ hτ roots A hA
        (p.1, p.2.1) (hfiber p.2.1))
  have hDmeas (p : ℕ × S) : MeasurableSet (D p) :=
    (hCmeas p).inter ((subtreeStepFieldVector_measurable p.2.1) hB)
  have hcell (p : ℕ × S) :
      P (D p) = P (C p) * Q B := by
    by_cases hvalid : (∀ i, (p.2.1 i).length = p.1) ∧
        Function.Injective p.2.1
    · have hgen := abstractStoppedVectorCell_measurable
        τ hτ roots A hA (p.1, p.2.1) (hfiber p.2.1)
      exact fixed_subtreeStepFieldVector_event_factorization μ p.2.1
        hvalid.1 hvalid.2 (C p) B hgen hB
    · have hempty : C p = ∅ := by
        ext ω
        simp only [C, abstractStoppedVectorCell, Set.mem_inter_iff,
          Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨⟨_, htime⟩, hroot⟩
        apply hvalid
        constructor
        · intro i
          simpa [← hroot] using hdepth ω p.1 htime i
        · simpa [← hroot] using hinj ω
      simp [D, hempty]
  have hCpair : Pairwise (fun p q => Disjoint (C p) (C q)) := by
    rintro ⟨n, r⟩ ⟨l, s⟩ hpq
    apply Set.disjoint_left.mpr
    intro ω hp hq
    apply hpq
    exact Prod.ext
      (WithTop.coe_injective (hp.1.2.symm.trans hq.1.2))
      (Subtype.ext (hp.2.symm.trans hq.2))
  have hDpair : Pairwise (fun p q => Disjoint (D p) (D q)) := by
    intro p q hpq
    exact (hCpair hpq).mono Set.inter_subset_left Set.inter_subset_left
  have hCunion : (⋃ p, C p) = A := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, C, abstractStoppedVectorCell,
        Set.mem_inter_iff, Set.mem_ofPred_eq]
      rintro ⟨p, ⟨hAω, _⟩, _⟩
      exact hAω
    · intro hAω
      cases htime : τ ω with
      | top => exact False.elim (hfinite ω htime)
      | coe n =>
          exact Set.mem_iUnion.mpr
            ⟨(n, ⟨roots ω, Set.mem_range_self ω⟩),
              ⟨⟨hAω, htime⟩, rfl⟩⟩
  have hDunion : (⋃ p, D p) =
      A ∩ selectedSubtreeStepFieldVector roots ⁻¹' B := by
    ext ω
    constructor
    · simp only [Set.mem_iUnion, D, C, abstractStoppedVectorCell,
        Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage,
        selectedSubtreeStepFieldVector]
      rintro ⟨p, ⟨⟨⟨hAω, _⟩, hroot⟩, hBω⟩⟩
      exact ⟨hAω, by simpa [hroot] using hBω⟩
    · rintro ⟨hAω, hBω⟩
      cases htime : τ ω with
      | top => exact False.elim (hfinite ω htime)
      | coe n =>
          exact Set.mem_iUnion.mpr
            ⟨(n, ⟨roots ω, Set.mem_range_self ω⟩),
              ⟨⟨⟨hAω, htime⟩, rfl⟩, hBω⟩⟩
  have hCsum : (∑' p, P (C p)) = P A := by
    rw [← hCunion]
    exact (measure_iUnion hCpair hCmeas).symm
  calc
    P (A ∩ selectedSubtreeStepFieldVector roots ⁻¹' B) =
        P (⋃ p, D p) := by rw [hDunion]
    _ = ∑' p, P (D p) := measure_iUnion hDpair hDmeas
    _ = ∑' p, P (C p) * Q B := tsum_congr hcell
    _ = (∑' p, P (C p)) * Q B := ENNReal.tsum_mul_right
    _ = P A * Q B := by rw [hCsum]

end ProbabilityTheory.BranchingRandomWalk
