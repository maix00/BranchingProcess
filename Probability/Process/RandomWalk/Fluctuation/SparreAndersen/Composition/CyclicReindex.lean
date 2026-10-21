/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Fluctuation.SparreAndersen.Composition.Cyclic
public import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Reindexing cyclic gap sums by compositions

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.cyclicGapCompositionEquiv`: for $n>0$,
  nonempty subsets of `Fin n` are equivalent to pairs consisting of a
  positive composition $c$ of $n$ and an offset in its final part.
- `ProbabilityTheory.RandomWalk.sum_cyclicGap_products_eq_composition_sum`:
  for functions $g,w : \mathbb N \to \mathbb R$, the sum over nonempty
  cyclic start sets $u$ of $g(|u|)\prod_j w(\ell_j(u))$ equals the sum over
  positive compositions $c$ of $n$ of
  $c_{|c|-1}g(|c|)\prod_j w(c_j)$. Here $\ell_j(u)$ is the $j$-th cyclic
  gap length from `Cyclic.lean`; the final part contributes its length
  because this counts the valid offsets into the last gap.

This finite reindexing is the summation step in M. Bauer, C. Godrèche, and
J.-M. Luck, *Statistics of persistent events in the binomial random walk:
Will the drunken sailor hit the sober man?*, Appendix A, equation (A.6),
in the derivation of equation (A.7), *Journal of Statistical Physics* 96
(1999), 963--1019, DOI 10.1023/A:1004636216365,
arXiv:cond-mat/9905252. The sum theorem allows arbitrary real-valued
weights $g$ and $w$.
-/

@[expose] public section


namespace ProbabilityTheory.RandomWalk

/-- Reindex the nonempty cyclic start sets by their positive gap
compositions and the position of their first start in the terminal gap.
For fixed gap lengths, the last gap determines the number of offsets. -/
noncomputable def cyclicGapCompositionEquiv {n : ℕ} (hn : 0 < n) :
    (Σ c : Composition n,
      Fin (c.blocksFun
        ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) ≃
      {u : Finset (Fin n) // u.Nonempty} := by
  let f : (Σ c : Composition n,
      Fin (c.blocksFun
        ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) →
      {u : Finset (Fin n) // u.Nonempty} :=
    fun p => ⟨compositionSelectedStarts p.1 hn p.2,
      compositionSelectedStarts_nonempty p.1 hn p.2⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hp
    rcases p with ⟨c, a⟩
    rcases q with ⟨d, b⟩
    have hc : c = d := by
      have h := congrArg
        (fun s : {u : Finset (Fin n) // u.Nonempty} =>
          cyclicGapComposition s.val s.property) hp
      simpa only [f, cyclicGapComposition_compositionSelectedStarts] using h
    subst d
    have hu : compositionSelectedStarts c hn a =
        compositionSelectedStarts c hn b :=
      congrArg Subtype.val hp
    have ha : a = b := by
      apply Fin.ext
      let firstValue : Finset (Fin n) → ℕ := fun s =>
        if h : s.Nonempty then (s.min' h).val else 0
      have hfirstA := compositionSelectedStarts_first_val c hn a
      have hfirstB := compositionSelectedStarts_first_val c hn b
      rw [Finset.orderEmbOfFin_zero rfl
        (Finset.card_pos.mpr
          (compositionSelectedStarts_nonempty c hn a))] at hfirstA
      rw [Finset.orderEmbOfFin_zero rfl
        (Finset.card_pos.mpr
          (compositionSelectedStarts_nonempty c hn b))] at hfirstB
      have hfirstA' : firstValue (compositionSelectedStarts c hn a) = a.val := by
        simpa [firstValue,
          compositionSelectedStarts_nonempty c hn a] using hfirstA
      have hfirstB' : firstValue (compositionSelectedStarts c hn b) = b.val := by
        simpa [firstValue,
          compositionSelectedStarts_nonempty c hn b] using hfirstB
      exact hfirstA'.symm.trans
        ((congrArg firstValue hu).trans hfirstB')
    cases ha
    rfl
  · intro s
    rcases s with ⟨u, hu⟩
    obtain ⟨hn', a, ha⟩ :=
      exists_compositionSelectedStarts_cyclicGapComposition u hu
    refine ⟨⟨cyclicGapComposition u hu, a⟩, ?_⟩
    apply Subtype.ext
    exact ha

/-- Reindex any product weight on cyclic gaps by positive compositions.
The last part contributes its length as a multiplicity, as in the
reindexing of Bauer--Godrèche--Luck, Appendix A, equation (A.6), used in the
derivation of equation (A.7). -/
theorem sum_cyclicGap_products_eq_composition_sum {n : ℕ} (hn : 0 < n)
    (g w : ℕ → ℝ) :
    ∑ u : {u : Finset (Fin n) // u.Nonempty},
      g u.val.card *
        ∏ j : Fin u.val.card,
          w (cyclicGapLength u.val u.property j) =
      ∑ c : Composition n,
        (c.blocksFun
          ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩ : ℝ) *
          (g c.length * ∏ j : Fin c.length, w (c.blocksFun j)) := by
  let e := cyclicGapCompositionEquiv hn
  have hchange := Fintype.sum_equiv e
    (fun p =>
      g p.1.length * ∏ j : Fin p.1.length, w (p.1.blocksFun j))
    (fun u : {u : Finset (Fin n) // u.Nonempty} =>
      g u.val.card *
        ∏ j : Fin u.val.card,
          w (cyclicGapLength u.val u.property j))
    (by
      intro p
      rcases p with ⟨c, a⟩
      change g c.length * ∏ j : Fin c.length, w (c.blocksFun j) =
        g (compositionSelectedStarts c hn a).card *
          ∏ j : Fin (compositionSelectedStarts c hn a).card,
            w (cyclicGapLength (compositionSelectedStarts c hn a)
              (compositionSelectedStarts_nonempty c hn a) j)
      let u := compositionSelectedStarts c hn a
      have hcard : u.card = c.length := compositionSelectedStarts_card c hn a
      have hprod :
          (∏ j : Fin u.card,
            w (cyclicGapLength u
              (compositionSelectedStarts_nonempty c hn a) j)) =
            ∏ j : Fin c.length, w (c.blocksFun j) := by
        apply Fintype.prod_equiv (finCongr hcard)
        intro j
        have hgap := cyclicGapLength_compositionSelectedStarts c hn a
          (finCongr hcard j)
        have hidx : (finCongr hcard j).cast hcard.symm = j := by
          apply Fin.ext
          rfl
        rw [hidx] at hgap
        exact congrArg w hgap
      calc
        g c.length * ∏ j : Fin c.length, w (c.blocksFun j) =
            g u.card * ∏ j : Fin c.length, w (c.blocksFun j) := by
          exact congrArg (fun t : ℝ =>
            t * ∏ j : Fin c.length, w (c.blocksFun j))
              (congrArg g hcard.symm)
        _ = g u.card * ∏ j : Fin u.card,
            w (cyclicGapLength u
              (compositionSelectedStarts_nonempty c hn a) j) := by
          exact (congrArg (fun t : ℝ => g u.card * t) hprod).symm)
  rw [← hchange]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  change (∑ _ : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩),
        g c.length * ∏ j : Fin c.length, w (c.blocksFun j)) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]


end ProbabilityTheory.RandomWalk
