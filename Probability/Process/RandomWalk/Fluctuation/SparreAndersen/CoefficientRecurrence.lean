/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.CompositionFormula
public import Combinatorics.Enumerative.Composition.FirstPart

/-!
# Finite coefficient recurrence for nonnegative random-walk paths

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.measureReal_nonnegative_endpoint_recurrence`:
  for every positive $n$, the endpoint sign probability $P_n$ and
  nonnegative-survival probabilities $F_j$ satisfy
  $P_n=nF_n-\sum_{j=1}^{n-1}F_jP_{n-j}$.

This is the coefficient identity behind equation (A.7) of M. Bauer,
C. Godrèche, and J.-M. Luck, *Statistics of persistent events in the
binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A (arXiv:cond-mat/9905252). It follows by grouping their
composition sum by the first part; the singleton composition contributes
$nF_n$, and each longer composition contributes a convolution term.
-/

@[expose] public section

open MeasureTheory
open Composition

namespace ProbabilityTheory.RandomWalk

private def signedLastPartWeight (F : ℕ → ℝ) {n : ℕ} (c : Composition n) : ℝ :=
  (c.blocks.getLastI : ℝ) * ((-1 : ℝ) ^ (c.length + 1) * (c.blocks.map F).prod)

private def compositionCoefficient (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ c : Composition n, signedLastPartWeight F c

private theorem weight_prepend_nonempty (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
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

private theorem weight_prepend_empty (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (r : Fin n) (d : Composition (n - (r.val + 1)))
    (h : d.blocks = []) :
    signedLastPartWeight F (prependPositive hn r d) = (n : ℝ) * F n := by
  have hm : n - (r.val + 1) = 0 := (d.blocks_eq_nil).mp h
  have hr : r.val + 1 = n := by omega
  unfold signedLastPartWeight
  simp [Composition.prependPositive, Composition.length, h, hr,
    List.getLastI_eq_getLast?_getD]

private theorem sum_weight_prepend (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
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

private theorem compositionCoefficient_eq_firstPart_sum (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    compositionCoefficient F n = ∑ r : Fin n,
      if n - (r.val + 1) = 0 then (n : ℝ) * F n
      else - F (r.val + 1) * compositionCoefficient F (n - (r.val + 1)) := by
  change (∑ c : Composition n, signedLastPartWeight F c) = _
  rw [Composition.sum_firstPart hn]
  simp_rw [sum_weight_prepend F hn]

private theorem compositionCoefficient_recurrence (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    compositionCoefficient F n = (n : ℝ) * F n -
      ∑ r : Fin (n - 1), F (r.val + 1) * compositionCoefficient F (n - (r.val + 1)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [compositionCoefficient_eq_firstPart_sum F (by omega), Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have htail (r : Fin m) : m + 1 - (r.val + 1) ≠ 0 := by omega
  simp_rw [ite_eq_right (htail _)]
  simp
  ring

private theorem last_eq_blocksFun {n : ℕ} (hn : 0 < n) (c : Composition n) :
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

private theorem prod_eq_blocksFun (F : ℕ → ℝ) {n : ℕ} (c : Composition n) :
    (c.blocks.map F).prod = ∏ j : Fin c.length, F (c.blocksFun j) := by
  rw [← c.ofFn_blocksFun, List.map_ofFn, List.prod_ofFn]
  rfl

private noncomputable def nonnegativeSurvivalProbability (ν : Measure ℝ) (k : ℕ) : ℝ :=
  (Measure.pi (fun _ : Fin k => ν)).real
    {z : Fin k → ℝ | ∀ t : Fin (k + 1), 0 ≤ Fin.partialSum z t}

private noncomputable def nonnegativeEndpointProbability (ν : Measure ℝ) (n : ℕ) : ℝ :=
  (Measure.pi (fun _ : Fin n => ν)).real
    {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)}

private theorem nonnegativeEndpointProbability_eq_compositionCoefficient
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

private theorem nonnegativeEndpointProbability_recurrence
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


/-- The finite coefficient recurrence corresponding to Bauer--Godrèche--Luck,
Appendix A, equation (A.7). The left side is $P_n$, and the path-confinement
probabilities in the right side are $F_j$. -/
theorem measureReal_nonnegative_endpoint_recurrence
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n) :
    (Measure.pi (fun _ : Fin n => ν)).real
      {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)} =
      (n : ℝ) *
        (Measure.pi (fun _ : Fin n => ν)).real
          {z : Fin n → ℝ |
            ∀ t : Fin (n + 1), 0 ≤ Fin.partialSum z t} -
      ∑ r : Fin (n - 1),
        (Measure.pi (fun _ : Fin (r.val + 1) => ν)).real
          {z : Fin (r.val + 1) → ℝ |
            ∀ t : Fin (r.val + 1 + 1), 0 ≤ Fin.partialSum z t} *
        (Measure.pi (fun _ : Fin (n - (r.val + 1)) => ν)).real
          {x : Fin (n - (r.val + 1)) → ℝ |
            0 ≤ Fin.partialSum x (Fin.last (n - (r.val + 1)))} := by
  exact nonnegativeEndpointProbability_recurrence ν hn

end ProbabilityTheory.RandomWalk

end
