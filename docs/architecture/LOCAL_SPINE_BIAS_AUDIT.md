# Local-density spine and many-to-one core

Reviewed on 2026-11-23 against Mathlib
`26573066084e6e2aa8526ea358bc43b66d96f970`.

## Mathematical scope

The original offspring-state kernel is `Q : Kernel S (Step ι S)` with
`IsMarkovKernel Q`. The state space is arbitrary measurable; child slots
are countable with measurable singletons. `Spine.LocalBias` records an
eligible domain D and a nonnegative local density r(s,ξ,i). Its admissibility
property requires:

* D is measurable and each fixed-index r is jointly measurable in (s,ξ).
* For s in D, `∫ ∑_i r(s,ξ,i) Q(s,dξ) = 1`.
* For s in D, Q(s)-almost surely, nonzero r(s,ξ,i) implies that child i
  exists and its state lies in D.

No normalization is imposed on ordinary states outside D. The local density
may depend on the complete child family and its index. It need not factor
through the child's state, and no harmonic function, finite expected number
of children, bounded tree depth or payoff integrability is required.
The formulas concern nonnegative payoffs, so infinite integrals are allowed.
This is a density-based change of branching law in the indexed framework;
it does not claim to describe arbitrary singular changes of offspring law.

The joint family/index kernel is the native sum of mapped density kernels,
`Q(s,dξ) r(s,ξ,i)`. Normal parents retain Q; eligible distinguished parents
use this joint kernel and distinguish the selected child. The existing
`State.treeKernel` constructs the complete role-valued tree. The unique
realized ray follows from local normalization/support and the existing
Ulam--Harris ray theorem.

For a fixed address, R_u is the product of local factors read from each
parent and its entire next-generation child family. The single fixed-address
induction proves the full finite-history density. Factoring measurable node
payoffs through that history and applying Tonelli gives

    E_Q[Σ_u R_u F_u(T)] = E_bias[Σ_(u in spine) F_u(erase(T))].

Each F_u is measurable at generation |u| and may use other branches through
that generation. No antichain or optional-line hypothesis is used. The
fixed-generation ancestral-path formula concentrates the same payoff on
one generation and uses the unique realized ray.

## Reference proof and native APIs

The proof keeps the fixed-address induction in Zhan Shi, *Branching Random
Walks* (2015), Theorem 4.3, (4.12)–(4.13), DOI
[10.1007/978-3-319-25372-5](https://doi.org/10.1007/978-3-319-25372-5).
Only the local Radon--Nikodym factor is generalized. The all-depth summation
extends the proof of Lemma 14.1 in J. D. Biggins and A. E. Kyprianou,
*Measure change in multitype branching* (2004), pp. 577–578, DOI
[10.1239/aap/1086957585](https://doi.org/10.1239/aap/1086957585).

The pinned Mathlib source and current official documentation were compared:

* [`Kernel.withDensity`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Kernel/WithDensity.html),
  `Kernel.lintegral_withDensity`, native kernel sum, map and comap are the
  existing measure-change operations. No replacement kernel type is defined.
* `Kernel.partialTraj`, `partialTraj_succ_of_le`, `Measure.infinitePi_map_pi`,
  `iIndepFun_infinitePi` and the existing independence interfaces provide
  the finite-history and ordinary-parent product integration. The private
  one-parent transfer assembly does not expose another product-measure API.
* `State.treeKernel` and the existing measurable state-tree/ray observations
  provide the only complete branching-process construction. Structural
  spine observations are now in `Tree/Observation/Path`, independent of h.

## General-to-special dependency chain

`LocalBias/Normalization` gives weighted child bias h(child)/a(s), where
`a(s)=Mh(s)` is finite positive on D={0<h<∞}. Taking a=Mh needs no
harmonicity; a=h is the harmonic specialization; a=ρh or a=c(s)h uses the
same theorem. Multiplicative generation factors therefore need no separate
probabilistic many-to-one induction.

The pre-existing harmonic family and tree definitions now substitute
`LocalBias.ofWeight h` into the local construction. The harmonic
fixed-address, adapted-node and path identities directly call the general
local-bias theorem. Their public assumptions and ordinary zero-weight
branches are preserved. The harmonic endpoint/root telescoping result is a
mathematical corollary, not an alternative definition of the density product.
BRW pre-sampled-field and tilted-walk law transports remain model-specific
adapters into this chain.

The two former `Tree/Density/Lemmas/{Generation,Induction}` files are removed.
There is only one probabilistic fixed-address density induction, under
`LocalBias/Lemmas`. No old-path compatibility file or theorem alias is added.
Enumeration-free analytic random-measure formulas retain their weaker
(non-probability and non-counting-valued) inputs; this migration adds no
indexed-tree assumptions to them.

## Ownership and regressions

`LocalBias` has eight direct semantic modules: Basic, Normalization, Tree,
Ray, Weight, Density, ManyToOne, Path. Each is a complete construction or
reusable result and stays outside Lemmas. Its single Lemmas directory holds
only the tagged-generation transfer assembly and raw finite-history
induction; same-file tactical helpers are private. The former harmonic
entries present genuine harmonic constructions/corollaries and have no
independent tree construction or density induction.

`BranchingProcessTest/Branching/LocalSpineBias.lean` checks a family-dependent
choice that selects the second child when present and otherwise the first,
with the first child's state fixed. It also checks the constant h=1 for
binary reproduction, whose mean is 2 rather than 1, and validates the
locally normalized kernel and the general adapted-payoff formula. Its axiom
inventory includes the generic construction-to-formula chain and the
harmonic corollaries. The existing spine-density and BRW tests continue to
cover zero-weight return branches, finite-generation density, first-entry,
and the auxiliary IID path-law identification.
