/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Algebra.BigOperators.PartialSum
import Mathlib.Data.Set.Defs
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Composition.EndpointProbability
import Combinatorics.Enumerative.Composition.FirstPart

/-!
# Internal composition derivation of the finite endpoint recurrence

## Internal proof declarations

- `signedLastPartWeight` and `compositionCoefficient` encode the signed weights
  in the finite composition expansion.
- `weight_prepend_nonempty`, `weight_prepend_empty`, and `sum_weight_prepend`
  calculate the change in those weights after adjoining the first part.
- `compositionCoefficient_eq_firstPart_sum` and
  `compositionCoefficient_recurrence` derive the coefficient recurrence.
- `last_eq_blocksFun` and `prod_eq_blocksFun` identify the terminal part and
  product coordinates used in the endpoint expansion.
- `nonnegativeSurvivalProbability`, `nonnegativeEndpointProbability`,
  `nonnegativeEndpointProbability_eq_compositionCoefficient`, and
  `nonnegativeEndpointProbability_recurrence` connect the composition identity
  to finite random-walk probabilities.

These declarations support only
`Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Survival.Recurrence`.

If $C_n$ is the signed composition coefficient, $F(n)$ the survival
probability, and $Q(n)$ the nonnegative-endpoint probability, then
\[
  Q(n)=C_n,
  \qquad C_n=nF(n)-\sum_{r=0}^{n-2}F(r+1)C_{n-r-1}.
\]
-/

open MeasureTheory
open Composition

namespace ProbabilityTheory.RandomWalk

def signedLastPartWeight (F : ℕ → ℝ) {n : ℕ} (c : Composition n) : ℝ :=
  (c.blocks.getLastI : ℝ) * ((-1 : ℝ) ^ (c.length + 1) * (c.blocks.map F).prod)

def compositionCoefficient (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ c : Composition n, signedLastPartWeight F c

lemma weight_prepend_nonempty (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (r : Fin n) (d : Composition (n - (r.val + 1)))
    (h : d.blocks ≠ []) :
    signedLastPartWeight F (prependPositive hn r d) =
      - F (r.val + 1) * signedLastPartWeight F d := by
  have hlast : ((r.val + 1) :: d.blocks).getLastI = d.blocks.getLastI := by
    cases hb : d.blocks with
    | nil => exact False.elim (h hb)
    | cons a l => simp [List.getLastI_eq_getLast?_getD]
  unfold signedLastPartWeight
  simp only [Composition.blocks_prependPositive, Composition.length_prependPositive,
    List.map_cons, List.prod_cons, hlast]
  ring

lemma weight_prepend_empty (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (r : Fin n) (d : Composition (n - (r.val + 1)))
    (h : d.blocks = []) :
    signedLastPartWeight F (prependPositive hn r d) = (n : ℝ) * F n := by
  have hm : n - (r.val + 1) = 0 := (d.blocks_eq_nil).mp h
  have hr : r.val + 1 = n := by omega
  unfold signedLastPartWeight
  simp [Composition.prependPositive, Composition.length, h, hr,
    List.getLastI_eq_getLast?_getD]

lemma sum_weight_prepend (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (r : Fin n) :
    (∑ d : Composition (n - (r.val + 1)), signedLastPartWeight F (prependPositive hn r d)) =
      if n - (r.val + 1) = 0 then (n : ℝ) * F n
      else - F (r.val + 1) * compositionCoefficient F (n - (r.val + 1)) := by
  split_ifs with hm
  · calc
      (∑ d : Composition (n - (r.val + 1)), signedLastPartWeight F (prependPositive hn r d)) =
          ∑ _d : Composition (n - (r.val + 1)), (n : ℝ) * F n := by
            apply Finset.sum_congr rfl
            intro d _
            exact weight_prepend_empty F hn r d ((d.blocks_eq_nil).mpr hm)
      _ = (n : ℝ) * F n := by
        simp [composition_card, hm]
  · calc
      (∑ d : Composition (n - (r.val + 1)), signedLastPartWeight F (prependPositive hn r d)) =
          ∑ d : Composition (n - (r.val + 1)),
            - F (r.val + 1) * signedLastPartWeight F d := by
              apply Finset.sum_congr rfl
              intro d _
              exact weight_prepend_nonempty F hn r d
                (fun h => hm ((d.blocks_eq_nil).mp h))
      _ = - F (r.val + 1) * compositionCoefficient F (n - (r.val + 1)) := by
        rw [← Finset.mul_sum]
        rfl

lemma compositionCoefficient_eq_firstPart_sum (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    compositionCoefficient F n = ∑ r : Fin n,
      if n - (r.val + 1) = 0 then (n : ℝ) * F n
      else - F (r.val + 1) * compositionCoefficient F (n - (r.val + 1)) := by
  change (∑ c : Composition n, signedLastPartWeight F c) = _
  rw [Composition.sum_firstPart hn]
  simp_rw [sum_weight_prepend F hn]

lemma compositionCoefficient_recurrence (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    compositionCoefficient F n = (n : ℝ) * F n -
      ∑ r : Fin (n - 1), F (r.val + 1) * compositionCoefficient F (n - (r.val + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [compositionCoefficient_eq_firstPart_sum F (by omega), Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have htail (r : Fin m) : m + 1 - (r.val + 1) ≠ 0 := by omega
  simp_rw [ite_eq_right (htail _)]
  simp
  ring

lemma last_eq_blocksFun {n : ℕ} (hn : 0 < n) (c : Composition n) :
    c.blocks.getLastI = c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩ := by
  have hne : c.blocks ≠ [] := by
    intro h
    have := (c.blocks_eq_nil).mp h
    omega
  simp [Composition.blocksFun, Composition.length,
    List.getLastI_eq_getLast?_getD,
    List.getLast?_eq_getLast_of_ne_nil hne]
  exact (List.get_length_sub_one
    (by simpa [Composition.length] using c.length_pos_of_pos hn)).symm

lemma prod_eq_blocksFun (F : ℕ → ℝ) {n : ℕ} (c : Composition n) :
    (c.blocks.map F).prod = ∏ j : Fin c.length, F (c.blocksFun j) := by
  rw [← c.ofFn_blocksFun, List.map_ofFn, List.prod_ofFn]
  rfl

noncomputable def nonnegativeSurvivalProbability (ν : Measure ℝ) (k : ℕ) : ℝ :=
  (Measure.pi (fun _ : Fin k => ν)).real
    {z : Fin k → ℝ | ∀ t : Fin (k + 1), 0 ≤ Fin.partialSum z t}

noncomputable def nonnegativeEndpointProbability (ν : Measure ℝ) (n : ℕ) : ℝ :=
  (Measure.pi (fun _ : Fin n => ν)).real
    {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)}

lemma nonnegativeEndpointProbability_eq_compositionCoefficient
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    nonnegativeEndpointProbability ν n =
      compositionCoefficient (nonnegativeSurvivalProbability ν) n := by
  rw [nonnegativeEndpointProbability, measureReal_nonnegative_endpoint_eq_composition_sum ν hn]
  change (∑ c : Composition n,
    (c.blocksFun ⟨c.length - 1,
      Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩ : ℝ) *
      ((-1 : ℝ) ^ (c.length + 1) *
        ∏ j : Fin c.length, nonnegativeSurvivalProbability ν (c.blocksFun j))) = _
  unfold compositionCoefficient
  apply Finset.sum_congr rfl
  intro c _
  rw [← last_eq_blocksFun hn c, ← prod_eq_blocksFun]
  rfl

lemma nonnegativeEndpointProbability_recurrence
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    nonnegativeEndpointProbability ν n = (n : ℝ) * nonnegativeSurvivalProbability ν n -
      ∑ r : Fin (n - 1),
        nonnegativeSurvivalProbability ν (r.val + 1) *
          nonnegativeEndpointProbability ν (n - (r.val + 1)) := by
  calc
    nonnegativeEndpointProbability ν n =
        compositionCoefficient (nonnegativeSurvivalProbability ν) n :=
      nonnegativeEndpointProbability_eq_compositionCoefficient ν hn
    _ = (n : ℝ) * nonnegativeSurvivalProbability ν n -
        ∑ r : Fin (n - 1),
          nonnegativeSurvivalProbability ν (r.val + 1) *
            compositionCoefficient (nonnegativeSurvivalProbability ν)
              (n - (r.val + 1)) :=
      compositionCoefficient_recurrence (nonnegativeSurvivalProbability ν) hn
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [nonnegativeEndpointProbability_eq_compositionCoefficient ν
        (by omega : 0 < n - (r.val + 1))]


end ProbabilityTheory.RandomWalk
