/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Basic
public import Probability.Process.RandomWalk.Path.Adapted.Filtration
public import Probability.Kernel.IonescuTulcea.Uniqueness
public import Probability.Kernel.IonescuTulcea.Markov

/-!
# Complete IID random-walk path law as a canonical Markov trajectory

## Public declarations

In `ProbabilityTheory.RandomWalk`:

* `map_positionProcess_eq_trajMeasure` proves
  `Law(x+∑_(j<n) ξ_j) = trajMeasure (dirac x) (historyKernel (incrementKernel ν))`
  for IID increments of probability law `ν`, on any measurable additive
  commutative monoid with measurable addition. No standard-Borel assumption
  or moments are required.

This identifies two realizations of one path law. It uses independent prefix
and next-increment laws, then the existing Ionescu--Tulcea uniqueness theorem;
compare O. Kallenberg, *Foundations of Modern Probability*, third edition
(2021), Theorem 8.24, DOI 10.1007/978-3-030-61871-1. It defines no second
random-walk or Markov-process interface.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open MeasureTheory Finset Preorder

set_option backward.isDefEq.respectTransparency false

/-- IID partial sums realize the complete canonical trajectory of the
increment kernel, on arbitrary measurable additive state spaces. -/
theorem map_positionProcess_eq_trajMeasure {E : Type*} [MeasurableSpace E]
    [AddCommMonoid E] [MeasurableAdd₂ E]
    (ν : Measure E) [IsProbabilityMeasure ν] (x : E) :
    (iidSequenceLaw ν).map (fun ξ n => positionProcess x n ξ) =
      Kernel.trajMeasure (Measure.dirac x) (Kernel.historyKernel (incrementKernel ν)) := by
  let X (ξ : ℕ → E) (n : ℕ) := positionProcess x n ξ
  have hX : Measurable X := positionProcess_path_measurable x
  apply Kernel.eq_trajMeasure
  · rw [Measure.map_map (measurable_pi_apply 0) hX]
    change (iidSequenceLaw ν).map (fun ξ => positionProcess x 0 ξ) = _
    simp
  · intro n
    let A (ξ : ℕ → E) := frestrictLe n (X ξ)
    let B (ξ : ℕ → E) := ξ n
    have hA : Measurable A := (measurable_frestrictLe n).comp hX
    have hB : Measurable B := measurable_pi_apply n
    have hAm : Measurable[sequencePrefixFiltration (E := E) n] A := by
      let m := sequencePrefixFiltration (E := E) n
      let : MeasurableSpace (ℕ → E) := m
      change Measurable A
      apply measurable_pi_iff.mpr
      intro k
      exact (positionProcess_adapted x k.1).mono
        ((sequencePrefixFiltration (E := E)).mono (mem_Iic.mp k.2)) le_rfl
    have hi := indepFun_sequencePrefix_blockSum ν n 1
    have hblock : AdditivePath.blockSum (E := E) n 1 = B := by
      funext ξ
      simp [AdditivePath.blockSum, B]
    rw [hblock] at hi
    have hle : MeasurableSpace.comap A inferInstance ≤
        MeasurableSpace.comap (Combinatorics.Sequence.blockCoordinates 0 (E := E) n)
          inferInstance := by
      rw [← sequencePrefixFiltration_eq_comap_blockCoordinates]
      exact hAm.comap_le
    have hind : IndepFun A B (iidSequenceLaw ν) :=
      indep_of_indep_of_le hi hle le_rfl
    have hpair := hind.map_prod_eq_prod_map_map hA.aemeasurable hB.aemeasurable
    change (iidSequenceLaw ν).map (fun ξ => (A ξ, B ξ)) =
      ((iidSequenceLaw ν).map A).prod ((iidSequenceLaw ν).map (fun ξ => ξ n)) at hpair
    rw [iidSequenceLaw_map_apply] at hpair
    let D (p : (Iic n → E) × E) := (p.1, p.1 ⟨n, by simp⟩ + p.2)
    have hD : Measurable D := measurable_fst.prodMk
      (((measurable_pi_apply _).comp measurable_fst).add measurable_snd)
    have hlift : (((iidSequenceLaw ν).map A).prod ν).map D =
        ((iidSequenceLaw ν).map A) ⊗ₘ Kernel.historyKernel (incrementKernel ν) n := by
      ext C hC
      rw [Measure.map_apply hD hC, Measure.prod_apply (hC.preimage hD),
        Measure.compProd_apply hC]
      apply lintegral_congr
      intro p
      change ν ((fun z => (p, p ⟨n, by simp⟩ + z)) ⁻¹' C) =
        incrementKernel ν (p ⟨n, by simp⟩) ((Prod.mk p) ⁻¹' C)
      have hx : Measurable (fun z : E => p ⟨n, by simp⟩ + z) :=
        measurable_const.add measurable_id
      rw [incrementKernel_apply, Measure.map_apply hx (measurable_prodMk_left hC)]
      rfl
    have hp := congrArg (fun m => m.map D) hpair
    rw [Measure.map_map hD (hA.prodMk hB), hlift] at hp
    have he : (fun ξ => D (A ξ, B ξ)) =
        (fun ξ => (frestrictLe n (X ξ), X ξ (n + 1))) := by
      funext ξ
      change (A ξ, (A ξ) ⟨n, by simp⟩ + B ξ) =
        (frestrictLe n (X ξ), X ξ (n + 1))
      refine Prod.ext rfl ?_
      exact (positionProcess_succ x ξ n).symm
    change (iidSequenceLaw ν).map (fun ξ => D (A ξ, B ξ)) =
      ((iidSequenceLaw ν).map A) ⊗ₘ Kernel.historyKernel (incrementKernel ν) n at hp
    rw [he] at hp
    rw [Measure.map_map (measurable_frestrictLe n) hX,
      Measure.map_map (by fun_prop) hX]
    exact hp.symm

end ProbabilityTheory.RandomWalk
