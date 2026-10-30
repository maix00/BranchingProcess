/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Topology.Cadlag.Skorokhod.EDistance.Logarithmic.Completion.AlignedCauchy

/-!
# Cauchy subsequence extraction for logarithmic Skorokhod completeness

## Internal proof declarations

`Skorokhod.Completion.Lemmas.cauchySeq_subsequence_has_summableLogAlignment`
states that, for a Cauchy sequence $(f_n)$ in Billingsley's path metric over a
complete metric state space, there exist a strictly increasing index map $k$,
a summable error sequence $(\varepsilon_n)$, time changes $(\lambda_n)$, and a
càdlàg path $g$ such that
\[
  \sum_n \varepsilon_n < \infty,\qquad
  \operatorname{billingsleyCost}
    (f_{k(n+1)}^{\mathrm{cad}},f_{k(n)}^{\mathrm{cad}},\lambda_n)
      <\varepsilon_n,\qquad
  \operatorname{alignedPath}
    \bigl((f_{k(m)}^{\mathrm{cad}})_{m\ge0},(\lambda_m)_{m\ge0},n\bigr)
      \longrightarrow g
  \quad\text{uniformly in }n.
\]
Here $f_j^{\mathrm{cad}}$ is the underlying càdlàg path of the Billingsley
path $f_j$, and `alignedPath` composes it with the cumulative time changes.

A Cauchy sequence in Billingsley's metric has a subsequence with summably
small consecutive distances. Choosing time changes that witness these
distances produces a uniformly convergent aligned subsequence. This is the
extraction and clock-selection part of Theorem 14.2 in Patrick Billingsley,
*Convergence of Probability Measures*, 1st ed., Wiley, 1968, Chapter 3, §14,
equations (A4.27)–(A4.29), p. 115
([text](https://ru.djvu.online/file/vaaIHv9IWlVeK)).
-/

section

open Filter
open scoped NNReal UniformConvergence

namespace Skorokhod

namespace Completion

namespace Lemmas

/-- From a Cauchy sequence of Billingsley paths into a complete metric state
space, extract a subsequence, summably small cost-witnessing time changes, and
a càdlàg uniform limit after alignment. -/
lemma cauchySeq_subsequence_has_summableLogAlignment
    {E : Type*} [MetricSpace E] [CompleteSpace E]
    (path : ℕ → BillingsleyPath E) (hpath : CauchySeq path) :
    ∃ (index : ℕ → ℕ) (clock : ℕ → TimeChange) (error : ℕ → ℝ≥0)
      (limit : CadlagPath unitInterval E),
      StrictMono index ∧ Summable error ∧
        (∀ n, billingsleyCost (path (index n.succ)).toCadlagPath
          (path (index n)).toCadlagPath (clock n) < error n) ∧
        TendstoUniformly
          (fun n t => alignedPath
            (fun k => (path (index k)).toCadlagPath) clock n t) limit atTop := by
  classical
  obtain ⟨index, hindex, hdistSummable⟩ :=
    Metric.exists_subseq_summable_dist_of_cauchySeq path hpath
  let delta : ℕ → ℝ := fun n =>
    dist (path (index n.succ)) (path (index n)) + (1 / 2 : ℝ) ^ n
  have hdelta_nonneg (n : ℕ) : 0 ≤ delta n := by
    dsimp [delta]
    positivity
  have hdelta_summable : Summable delta := by
    dsimp [delta]
    exact hdistSummable.add summable_geometric_two
  let error : ℕ → ℝ≥0 := fun n => ⟨delta n, hdelta_nonneg n⟩
  have herror : Summable error :=
    (NNReal.summable_mk hdelta_nonneg).2 hdelta_summable
  have hsmallReal (n : ℕ) :
      dist (path (index n.succ)) (path (index n)) < (error n : ℝ) := by
    change dist (path (index n.succ)) (path (index n)) < delta n
    dsimp [delta]
    have hpositive : 0 < (1 / 2 : ℝ) ^ n := by positivity
    exact lt_add_of_pos_right _ hpositive
  have hdist_lt_error (n : ℕ) :
      edist (path (index n.succ)) (path (index n)) < error n := by
    rw [edist_dist, ENNReal.ofReal_lt_coe_iff (dist_nonneg)]
    exact hsmallReal n
  let selectedPath : ℕ → CadlagPath unitInterval E :=
    fun n => (path (index n)).toCadlagPath
  let clock : ℕ → TimeChange := fun n =>
    Classical.choose (exists_timeChange_billingsleyCost_lt
      (f := selectedPath n.succ) (g := selectedPath n)
      (ε := error n)
      (by
        change edist (path (index n.succ)) (path (index n)) < error n
        exact hdist_lt_error n))
  have hcost (n : ℕ) :
      billingsleyCost (selectedPath n.succ) (selectedPath n) (clock n) < error n :=
    Classical.choose_spec (exists_timeChange_billingsleyCost_lt
      (f := selectedPath n.succ) (g := selectedPath n)
      (ε := error n)
      (by
        change edist (path (index n.succ)) (path (index n)) < error n
        exact hdist_lt_error n))
  have hclose : ∀ n,
      uniformEDist ((clock n).act (selectedPath n.succ)) (selectedPath n) ≤ error n := by
    intro n
    unfold billingsleyCost at hcost
    exact (le_max_right _ _).trans (le_of_lt (hcost n))
  obtain ⟨limit, hlimit⟩ := exists_cadlag_uniformLimit_of_summably_aligned
    selectedPath clock error hclose herror
  exact ⟨index, clock, error, limit, hindex, herror, hcost, by
    simpa [selectedPath] using hlimit⟩

end Lemmas

end Completion

end Skorokhod
