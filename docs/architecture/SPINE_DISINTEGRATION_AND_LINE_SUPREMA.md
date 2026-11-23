# Complete-subtree disintegration and countable optional-line suprema

## Reference and upstream review

The spinal recursion follows Zhan Shi, *Branching Random Walks* (2015),
§4.5, proof of Theorem 4.3 between (4.12) and (4.13): first fix the terminal
spine address, integrate ordinary sibling subtrees, then sum over terminal
addresses. [Author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).
The recursion implemented here fixes the first child while retaining its
complete descendant trees. It is not the all-depth identity (4.12).

Mathlib was checked at `26573066084e6e2aa8526ea358bc43b66d96f970`:

- `Kernel.trajMeasure_compProd_traj` supplies the history/future joint law.
- `Measure.compProd_map` and `Measure.map_compProd_eq_of_ae` transport that law.
- `Kernel.condExp_of_jointLaw` derives the conditional expectation from it.
- `Measurable.lintegral_kernel_prod_right'` integrates arbitrary measurable
  nonnegative complete-subtree observables.

The [official trajectory API](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/IonescuTulcea/Traj.html)
provides the canonical law and conditional-integration operations. The local
results identify their branching-coordinate observations; they do not define
a second extension or conditional-law mechanism.

For lines, A. E. Kyprianou, *Martingale convergence and the stopped branching
random walk* (2000), §2, pp. 408–409,
[DOI 10.1007/s004409900036](https://doi.org/10.1007/s004409900036), supplies
ancestral precedence and the optionality test. The countable-supremum result
below is derived from these definitions, rather than cited as a numbered
result of that article. Mathlib's antichain API does not supply descendant
closure or ancestral-frontier suprema. Existing local `IsLine`, `Precedes`,
`firstEntrance`, and stopped-information definitions are reused.

## Mathematical scope and ownership

`State.descendantTrees_jointLaw` allows arbitrary jointly distributed initial
states and distinct fixed-generation roots. The descendant-tree family,
jointly with the observed past, has the product continuation kernel.
`condExp_descendantTrees` now follows from this joint law; its previous
separate derivation has been removed.

`State/Descendants/Disintegration.lean` identifies the root-family/complete-
child-tree joint law

$$\mathcal L(\xi,(T_j)_j)=K_\bot(s,d\xi)\otimes\bigotimes_j P_{\xi_j}.$$

Absent children are included. State and slot spaces are arbitrary. This is a
reusable branching Markov law, independent of spine bias, BRW, moments, or
standard-Borel assumptions, so it belongs outside `Lemmas/`.

`Spine/Tree/BranchingProperty.lean` applies this law to the existing canonical
normal/distinguished tree and the joint biased-family/child law:

$$\mathbb E[\mathbf1_{\{w_1=i\}}g(\xi,(T_j)_j)]
=\int\frac{h(\xi_i)}{h(s)}
 \int g(\xi,(T_j)_j)\,d\bigotimes_j P_{\operatorname{distinguish}_i(\xi)_j}
 \,Q(s,d\xi).$$

The payoff may inspect future spine tags or whole ordinary sibling trees.
Ordinary zero-weight children are retained and can later produce positive-
weight descendants. This reusable recursive law is public; tactical values
and calculations stay local to its proof.

`Combinatorics/UlamHarris/Line/Supremum.lean` defines the deterministic
ancestral supremum by

$$\sup_i L_i=\operatorname{firstEntrance}\left(\bigcap_i D_{L_i}\right),
\qquad D_{\sup_i L_i}=\bigcap_i D_{L_i}.$$

It accepts arbitrary index families. Its universal property is
`Precedes (supremum L) M ↔ ∀ i, Precedes (L i) M`.
`Probability/Process/Tree/Line/Supremum.lean` proves measurable random-line
membership and optionality for **countable** families, without requiring a
countable node space or that every line meet every infinite ray. It proves
`⨆ i, F_(L_i) ≤ F_(sup_i L_i)`, without asserting equality for an arbitrary
supplied deterministic-past family. These are independent line operations,
so neither module belongs in `Lemmas/`. There are six direct deterministic
line modules and eight direct probabilistic line modules after this change.
Import-boundary checks keep these owners independent of branching models.

## Verification and remaining obligations

Regression examples inspect a sibling's third-generation descendant and a
family of partial lines where one root stops immediately while another
recedes to infinity. The supremum retains only the first root.

The all-depth fixed-address identity (Shi (4.12)), higher-generation tree
density, and full conditional spine decomposition remain open. The general
strong branching property at arbitrary optional lines also remains open.
Closure of optionality and stopped-information inclusion do not establish it.
