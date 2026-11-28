# Canonical many-to-one law transport

Reviewed on 2026-11-23 against Mathlib `26573066084e6e2aa8526ea358bc43b66d96f970`.
References: Zhan Shi, *Branching Random Walks* (2015), Theorems 1.1, 4.3,
4.4(ii), DOI 10.1007/978-3-319-25372-5;
[author lecture notes](https://igor-kortchemski.perso.math.cnrs.fr/MAP575/docs/brw.pdf).

## One law and its realizations

* `BranchingProcess.State.map_stateTree_offspringFieldLaw` is the existing
  complete-field pushforward theorem. `BRW.Spine.Additive.StateKernel`
  specializes its update to `F(x,e)=x+φ(e)` and proves mean harmonicity of
  `h(x)=exp(-x)` from boundary normalization. Raw marks need no zero,
  order, nonextinction or moment hypothesis.
* `BranchingProcess.Spine.lintegral_pathPayoff_eq` specializes
  `lintegral_adaptedPayoff_eq` to generation-n ancestral paths and uses the
  unique realized spine. This is the sole probabilistic tree proof.
* `RandomWalk.map_positionProcess_eq_trajMeasure` identifies IID sums with
  the canonical Markov trajectory law. It requires only a measurable additive
  commutative monoid with measurable addition and a probability increment law;
  no standard-Borel or measurable-singleton condition is added. It uses the
  existing native trajectory uniqueness interface. `Kernel.Step.ofStep_apply`
  and `incrementKernel_apply` no longer impose measurable singletons: the
  measurable integrand supplies `lintegral_dirac'` directly.
* `BRW.Spine.Additive.map_spinePath_law` combines native kernel mapping, the
  general spine state-chain law and the IID trajectory theorem.
* `Path/ManyToOne/Identity` derives the original field formula through these
  laws. Its deterministic survival/prefix and weight-cancellation helpers are
  private in the same file; they do not need a `Lemmas/` directory.
  Endpoint formulas specialize the last coordinate; first-entry formulas sum
  the disjoint first-entry path events. Old public hypotheses are unchanged.

The new observation, complete-law and path-payoff results are reusable
constructions/theorems, so they belong outside `Lemmas/`. The additive
realization adapters remain in the BRW-specific `Spine.Additive` namespace.
No second canonical tree, Markov process or IID law is defined.

## Random-measure audit and removed duplicates

`PointMeasure/Endpoint` and `Path/ManyToOne/PointMeasure` accept
`law : Measure (Measure E)`. Their analytic intensities need neither
`IsProbabilityMeasure law` nor a counting-valued assumption. Normalization
makes the *tilted intensity* a probability law. These results cannot be
forced through indexed probability trees without losing this generality or
introducing measurable enumeration hypotheses. Retained inductions concern
analytic operators, not another law of an indexed branching process.
Their indexed-field representation adapters use the unified path formula.

The redundant `PointMeasure/RandomWalk` module is deleted: use
`iidSequenceLaw (RandomMeasure.tiltedLaw φ (-1) law)` and the existing generic
IID-coordinate and random-walk APIs directly. The local partial-sum
independence and iterate proofs in `ManyToOne/ProductField` are deleted in
favor of `RandomWalk.Kernel.Endpoint`. No old-name aliases remain.

`ManyToOneLawTransport.lean` checks the interfaces without a zero raw mark,
without measurable singletons on the additive state space, and without a
probability/counting assumption on mean-measure inputs. It also checks the
axioms of the complete generic-to-BRW dependency chain.

## Which expectation?

For a root at zero and boundary normalization, write P for the original
branching law, ν for its normalized tilted intensity, and P-hat for the
distinguished-tree law. Then

    E_P[Σ_(|u|=n) exp(-V(u)) g(V(u|0),…,V(u))]
      = E_(ν^ℕ)[g(Y_0,…,Y_n)]
      = E_(P-hat)[g(V(ξ_0),…,V(ξ_n))].

The auxiliary IID law is not the original law of an arbitrarily chosen
ancestor. One may realize those auxiliary increments on an enlargement and
use a common expectation symbol after declaring their law. The finite-tree
marginal of P-hat has density W_n with respect to P. A global infinite-tree
density W_infinity requires additional uniform integrability; it is not a
consequence of the finite-generation identities.
