/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Marked
public import Probability.BranchingRandomWalk.Spine.Path.FamilySelection
import MeasureTheory.Function.FinPartialSum

/-!
# Many-to-one for actual whole-family selected path counts

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.pathManyToOne_selectFamily`:
  let `μ_A=μ.map (Step.selectFamily {ξ | mark ξ∈A})`. For any measurable
  nonnegative position-history test `F`,
  `E_μA Zₙ(F,x)=E_ν̂[exp(Sₙ) F(x+S₀,…,x+Sₙ) 1_(Bⱼ∈A, j<n)]`,
  where `ν̂` is the original joint law of the displacement and family mark.

The count is the existing `pathGeneration` under the actual selected
reproduction law. The full family is tested at every strict ancestor; the
endpoint's own family is not tested. Only the original law is boundary
normalized. No moment assumption, finite offspring bound or independence
between a displacement and its reproductive mark is imposed.

This is the all-ancestor family-cutoff many-to-one step in B. Mallein,
*N-branching random walk with α-stable spine*, §2.1 and proof of Lemma 3.4,
arXiv:1503.03762v2, and *Necessary and sufficient conditions for the
convergence of the consistent maximal displacement of the branching random
walk*, §2.1 and proof of Lemma 3.4, arXiv:1510.00602v2. The proof specializes
the existing complete-record many-to-one identity and native field pushforward.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Spine
open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

/-- The original marked spine represents the actual whole-family selected
count, as in B. Mallein, *N-branching random walk with α-stable spine*,
proof of Lemma 3.4 (arXiv:1503.03762v2). No normalization of the selected
law is performed. -/
theorem pathManyToOne_selectFamily {ι X M : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace X] [MeasurableSpace M]
    (φ : Potential X) (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {mark : Step ι X → M} (hm : Measurable mark)
    {accepted : Set M} (ha : MeasurableSet accepted)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) (x : ℝ) :
    (∫⁻ field, pathGeneration φ n F x field
      ∂offspringFieldLaw (μ.map (Step.selectFamily (mark ⁻¹' accepted)))) =
      ∫⁻ sequence, ENNReal.ofReal (Real.exp (AdditivePath.displacement n (fun j => (sequence j).1))) *
        (if ∀ j < n, (sequence j).2 ∈ accepted then
          F (history n x (fun j => (sequence j).1)) else 0)
        ∂iidSequenceLaw (tiltedMarkedPotentialLaw φ (-1) μ (fun p => mark p.1)) := by
  let A := mark ⁻¹' accepted
  have hA : MeasurableSet A := ha.preimage hm
  let G (v : Fin n → ℝ × M) : ℝ≥0∞ :=
    if ∀ j, (v j).2 ∈ accepted then
      F (AdditivePath.finitePrefix x (fun j => (v j).1)) else 0
  have hG : Measurable G := by
    have hprefix : Measurable (fun v : Fin n → ℝ × M =>
        AdditivePath.finitePrefix x (fun j => (v j).1)) :=
      measurable_pi_iff.mpr fun k => measurable_const.add
        ((Fin.measurable_partialSum k).comp (by fun_prop))
    apply (hF.comp hprefix).ite _ measurable_const
    convert MeasurableSet.iInter
      (fun j : Fin n => ha.preimage (measurable_snd.comp (measurable_pi_apply j))) using 1
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Function.comp_apply]
  have hfield : Measurable (fun field : StepField ι X =>
      fun u => Step.selectFamily A (field u)) := by
    exact measurable_pi_iff.mpr fun u => (Step.selectFamily_measurable hA).comp (measurable_pi_apply u)
  rw [← offspringFieldLaw_map_selectFamily μ hA,
    lintegral_map (pathGeneration_measurable φ n hF x) hfield]
  have hcount (field : StepField ι X) :
      pathGeneration φ n F x (fun u => Step.selectFamily A (field u)) =
        ∑' z : Fin n → ι, if surviveAlong field [] (List.ofFn z) then
          G (fun j => ((Mark.pathRecords field z j).1.potentialValue' φ
            (Mark.pathRecords field z j).2, mark (Mark.pathRecords field z j).1)) else 0 := by
    rw [pathGeneration_eq_tsum_fin]
    apply tsum_congr
    intro z
    have hs : surviveAlong (fun u => Step.selectFamily A (field u)) [] (List.ofFn z) ↔
        surviveAlong field [] (List.ofFn z) ∧ ∀ j : Fin n, mark (Mark.pathRecords field z j).1 ∈ accepted := by
      have h := surviveAlong_selectFamily_iff A field [] (List.ofFn z)
      constructor
      · intro hsel
        refine ⟨(h.mp hsel).1, ?_⟩
        intro j
        exact (h.mp hsel).2 ⟨j.val, by simpa only [List.length_ofFn] using j.isLt⟩
      · rintro ⟨hraw, hmarks⟩
        apply h.mpr
        refine ⟨hraw, ?_⟩
        intro j
        exact hmarks ⟨j.val, by simpa only [List.length_ofFn] using j.isLt⟩
    by_cases hraw : surviveAlong field [] (List.ofFn z)
    · by_cases hmarks : ∀ j : Fin n, mark (Mark.pathRecords field z j).1 ∈ accepted
      · have hsel := hs.mpr ⟨hraw, hmarks⟩
        simp [hsel, hraw, G, hmarks,
          pathHistory_selectFamily_eq_of_survive φ A n x field (List.ofFn z) hsel,
          pathHistory_eq_finitePrefix_records]
      · have hsel : ¬surviveAlong (fun u => Step.selectFamily A (field u)) [] (List.ofFn z) :=
          fun h => hmarks (hs.mp h).2
        simp only [hsel, hraw, ↓reduceIte, G, hmarks]
    · have hsel : ¬surviveAlong (fun u => Step.selectFamily A (field u)) [] (List.ofFn z) :=
        fun h => hraw (hs.mp h).1
      simp only [hsel, hraw, ↓reduceIte]
  simp_rw [hcount]
  refine (markedPathManyToOne φ μ hboundary (hm.comp measurable_fst) n hG).trans ?_
  apply lintegral_congr
  intro sequence
  have hsum : (∑ j : Fin n, (sequence j).1) =
      AdditivePath.displacement n (fun j => (sequence j).1) := by
    exact Fin.sum_univ_eq_sum_range (fun j => (sequence j).1) n
  rw [hsum]
  congr 1
  have heq : (∀ j : Fin n, (sequence j).2 ∈ accepted) ↔
      ∀ j < n, (sequence j).2 ∈ accepted := by
    constructor
    · intro h j hj; exact h ⟨j, hj⟩
    · intro h j; exact h j j.isLt
  have hp : AdditivePath.finitePrefix x (fun j : Fin n => (sequence j).1) =
      history n x (fun j => (sequence j).1) := by
    simpa only [history_eq_fromIncrements] using
      AdditivePath.finitePrefix_restrict_eq_fromIncrements x (fun j => (sequence j).1)
  simp only [G, heq, hp]

end ProbabilityTheory.BranchingRandomWalk.Spine
