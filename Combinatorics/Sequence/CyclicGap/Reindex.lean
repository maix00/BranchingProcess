/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Sequence.CyclicGap.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
import all Combinatorics.Sequence.CyclicGap.Lemmas.Composition

/-!
# Reindexing cyclic subsets by positive compositions

## Public declarations

For $n>0$, let $\mathcal U_n$ be the nonempty subsets of $\mathrm{Fin}(n)$.
For a composition $c$ of $n$, put $m_c=c.\mathrm{length}$ and
$c_j=c.\mathrm{blocksFun}(j)$ for $j\in\mathrm{Fin}(m_c)$.

* `Combinatorics.Sequence.compositionSelectedStartsMap` sends a composition
  and an offset $a<c_{m_c-1}$ to the cyclic start set
  $\{a+\sum_{i<j.\mathrm{val}}c_i:j\in\mathrm{Fin}(m_c)\}\in\mathcal U_n$.
  `Combinatorics.Sequence.compositionSelectedStartsMap_bijective` proves this
  map bijective, and
  `Combinatorics.Sequence.cyclicGapCompositionEquiv` packages the bijection
  as an equivalence.
* For a commutative semiring $R$ and $g,w:\mathbb N\to R$,
  `Combinatorics.Sequence.sum_cyclicGap_products_eq_composition_sum` states
  \[
    \sum_{u\in\mathcal U_n}g(|u|)
      \prod_{j\in\mathrm{Fin}(|u|)}
        w(\operatorname{cyclicGapLength}(u,j))
    =\sum_{c\in\operatorname{Composition}(n)}
      c_{m_c-1}\,g(m_c)\prod_{j\in\mathrm{Fin}(m_c)}w(c_j).
  \]
  The factor $c_{m_c-1}$ counts the offsets in the last part.

Mathlib provides positive `Composition n`, its boundary-set representation,
and their equivalence. This module supplies the cyclic subset/marked-gap
correspondence and its weighted finite-sum reindexing. The random-walk
specialization appears in Bauer, Godrèche, and Luck, *Statistics of persistent
events in the binomial random walk: Will the drunken sailor hit the sober
man?*, Appendix A, equation (A.6), in the derivation of equation (A.7),
*Journal of Statistical Physics* 96 (1999), 963--1019,
DOI 10.1023/A:1004636216365, arXiv:cond-mat/9905252.
-/

@[expose] public section

namespace Combinatorics.Sequence


/-- Map a composition marked by an offset in its final part to the
corresponding nonempty set of cyclic starts. -/
def compositionSelectedStartsMap {n : ℕ} (hn : 0 < n) :
    (Σ c : Composition n,
      Fin (c.blocksFun
        ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) →
      {u : Finset (Fin n) // u.Nonempty} :=
  fun p => ⟨compositionSelectedStarts p.1 hn p.2,
    compositionSelectedStarts_nonempty p.1 hn p.2⟩

/-- The composition-and-offset map gives every nonempty cyclic start set
exactly once. -/
theorem compositionSelectedStartsMap_bijective {n : ℕ} (hn : 0 < n) :
    Function.Bijective (compositionSelectedStartsMap hn) := by
  constructor
  · intro p q hp
    rcases p with ⟨c, a⟩
    rcases q with ⟨d, b⟩
    have hc : c = d := by
      have h := congrArg
        (fun s : {u : Finset (Fin n) // u.Nonempty} =>
          cyclicGapComposition s.val s.property) hp
      simpa only [compositionSelectedStartsMap,
        cyclicGapComposition_compositionSelectedStarts] using h
    subst d
    have hu : compositionSelectedStarts c hn a =
        compositionSelectedStarts c hn b := by
      exact congrArg Subtype.val hp
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

/-- Reindex nonempty cyclic start sets by positive compositions marked by an
offset in their final part. -/
noncomputable def cyclicGapCompositionEquiv {n : ℕ} (hn : 0 < n) :
    (Σ c : Composition n,
      Fin (c.blocksFun
        ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩)) ≃
      {u : Finset (Fin n) // u.Nonempty} :=
  Equiv.ofBijective (compositionSelectedStartsMap hn)
    (compositionSelectedStartsMap_bijective hn)

/-- Reindex any product weight on cyclic gaps by positive compositions.
The last part contributes its length as a multiplicity, as in the
reindexing of Bauer--Godrèche--Luck, Appendix A, equation (A.6), used in the
derivation of equation (A.7). -/
theorem sum_cyclicGap_products_eq_composition_sum {n : ℕ} (hn : 0 < n)
    {R : Type*} [CommSemiring R] (g w : ℕ → R) :
    ∑ u : {u : Finset (Fin n) // u.Nonempty},
      g u.val.card *
        ∏ j : Fin u.val.card,
          w (cyclicGapLength u.val u.property j) =
      ∑ c : Composition n,
        (c.blocksFun
          ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩ : R) *
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
          exact congrArg (fun t : R =>
            t * ∏ j : Fin c.length, w (c.blocksFun j))
              (congrArg g hcard.symm)
        _ = g u.card * ∏ j : Fin u.card,
            w (cyclicGapLength u
              (compositionSelectedStarts_nonempty c hn a) j) := by
          exact (congrArg (fun t : R => g u.card * t) hprod).symm)
  rw [← hchange]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c _
  change (∑ _ : Fin (c.blocksFun
      ⟨c.length - 1, Nat.sub_lt (c.length_pos_of_pos hn) (by omega)⟩),
        g c.length * ∏ j : Fin c.length, w (c.blocksFun j)) = _
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]


end Combinatorics.Sequence

end
