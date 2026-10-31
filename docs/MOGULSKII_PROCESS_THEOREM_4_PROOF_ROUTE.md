# Mogul'skii Theorem 4: source-faithful formalization route

## Source statement

This note follows Section 5 of A. A. Mogul'skii, *Small Deviations in the
Sample Function Space* (Russian original, *Theory of Probability and Its
Applications* 19:4 (1974), 755--765; English translation, 19:1 (1975),
726--736, [DOI 10.1137/1119081](https://doi.org/10.1137/1119081)). Theorem 4
assumes a homogeneous process `ξ(t)`, `t ≥ 0`, with independent increments,
almost-surely right-continuous paths, and the stable domain-of-attraction
condition

```text
P(ξ(n) < x B(n)) → Fα(x),       0 < α ≤ 2,
B*(B(n)) / n → 1,
```

with the centering convention in the article. Here `B*(u) = u^α / L*(u)` and
`L*(u) = u^(α-2) ∫_{[-u,u]} z² ν(dz)` for the unit-time marginal `ν`. For
`x(n) → ∞` with `x(n) / B(n) → 0`, the process path is
`s_n(t) = ξ(nt) / x(n)`, with the terminal value taken as the left limit. The
conclusion for every `G ∈ 𝔐` is

```text
log P(s_n ∈ G)  ~  C Hα(G) n x(n)^(-α) L*(x(n)),
```

where `C < 0` is the constant from Theorem 1. In the proof, Theorem 4 is
reduced to the stable-process tube estimate of Lemma 1 and then to the same
geometric proof used for Theorem 1.

The article's pinned tube is
\[
I_c^b = \{f\in D(0,1): f(0)=0,\ \inf_{0\le t\le1} f(t)>c,\
                         \sup_{0\le t\le1} f(t)<b\}.
\]
Thus `a⁻¹ I¹₋₁` is the set of paths starting at zero and staying strictly
between `-a⁻¹` and `a⁻¹`; the terminal value in `D(0,1)` is the left limit.

## Existing Lean interfaces

- `Probability/Process/Levy/Basic.lean` defines `IsLevyProcess` and proves
  closure under continuous measurable additive state maps and continuous
  additive time changes. Thus `t ↦ ξ(nt) / B(n)` has the required process
  structure once the source process has been packaged as an `IsLevyProcess`.
- `Probability/Process/StationaryIncrements/Basic.lean` proves that a
  zero-start process with stationary increments satisfies
  `Law(X(s+t) - X(s)) = Law(X(t))` for every `s,t ≥ 0`. The same layer now
  supplies the increment-to-marginal identity used by path-law convergence.
- `Probability/Process/Levy/MarginalLaws.lean` proves that every fixed-time
  marginal of a real-valued Lévy process is infinitely divisible: for every
  `n ≥ 1`, `Law(X(t))` is the `n`-fold convolution of the common law of `n`
  equal-length stationary increments. This places the process marginals in
  the measure-level framework used by the Lévy--Khintchine semigroup API.
- `Probability/Process/Levy/PathLaw/UnitInterval.lean` constructs the law of
  `t ↦ X(Tt)` on `CadlagPath unitInterval ℝ`, identifies every finite
  evaluation law, identifies the unit-interval law of `t ↦ X(Tt)` with the
  horizon-`T` law, and proves that spatial scaling by `q` pushes this law
  forward by `f ↦ qf`. These are the path-law interfaces needed for the
  normalized process in equation (38).
- `Probability/Process/Levy/PathLaw/Convergence.lean` proves that tightness of
  a family of unit-interval Lévy path laws and convergence of every interval
  increment law imply weak convergence of the path laws. It uses
  `Probability.Process.IndepIncrements.Convergence` to assemble the finite-grid
  position limits and the generic tightness-plus-finite-grid theorem to
  identify the path-space limit. Its Lévy-process corollary derives the
  increment limits from convergence of every rescaled one-time marginal, using
  stationary increments and the zero-start property. This completes the
  path-level assembly once tightness and the rescaled marginal limits have
  been supplied.
- `Probability/Distributions/InfinitelyDivisible/LevyKhintchine/Semigroup/Convergence.lean`
  proves that pointwise convergence of the exponents of a sequence of
  convolution semigroups implies weak convergence of each fixed positive-time
  member, using `ProbabilityMeasure.tendsto_iff_tendsto_charFun`. This gives a
  reusable route from exponent limits to the marginal inputs above; obtaining
  those exponent limits from Theorem 4's scalar domain-of-attraction
  assumption remains a separate obligation.
- `Probability/Process/Levy/PathContinuity.lean` proves
  `IsLevyProcess.ae_leftLim_eq_eval`: a càdlàg Lévy process has no jump at
  any fixed positive time, almost surely. At time `1`, this identifies the
  value-at-1 path law with Mogul'skii's terminal-left convention in Theorem 4,
  Section 5.
- `Probability/Process/Stable/PathLaw/UnitInterval.lean` and the stable
  process escape-rate modules provide the limiting stable path law and its
  tube-rate input.
- The deterministic corridor comparisons and the finite-partition extension
  for Theorem 1 are already formalized under
  `Probability/Process/RandomWalk/SmallDeviation/Mogulskii/Rate/`.

## The proof in the article

Mogul'skii states that the proof of Theorem 4 is “almost verbatim” the proof
of Theorem 1. The proof on Russian-original pages 762--763 (English
translation, pp. 733--734) proceeds through equations (38)--(44):

1. **Fixed-tube transfer, equation (38).** For each fixed `a > 0`, functional
   convergence of `t ↦ ξ(nt)/B(n)` to the strictly stable process transfers
   the probability of the fixed tube `a⁻¹ I¹₋₁`. Written in terms of
   `s_n(t) = ξ(nt)/x(n)`, this gives the probability comparison for
   `s_n ∈ a⁻¹ B(n) x(n)⁻¹ I¹₋₁`.
2. **Change the observation horizon, equations (39)--(41).** For a sequence
   `y(n) → ∞`, the article compares that tube event with the same process
   observed for `⌊y(n)⌋` units of time. It then sets
   `y(n) = ⌊B*(a x(n))⌋`. The asymptotic-inverse relation gives
   `B(⌊B*(a x(n))⌋)/(a x(n)) → 1`, yielding the fixed-scale stable tube
   comparison.
3. **Slowly increase `a`, equations (42)--(44).** Choose `a(n) → ∞` slowly
   enough that the preceding eventual comparisons remain valid. Apply
   Lemma 1 to the stable-process tube at width `a(n)⁻¹`; regular variation of
   `B*` then gives the exponent `n x(n)⁻α L*(x(n))` and the constant `C`.
4. **Extend from the tube to `G ∈ 𝔐`.** The article finishes by reusing the
   proof of Theorem 1. The finite partition, inner and outer tube comparisons,
   and the functional `Hα` are the same deterministic argument as there.

Accordingly, a separate nonstable block-concatenation or one-block squeeze is
not part of this proof route. Equation (38) is the process-level convergence
input; the rest is the scaling comparison in equations (39)--(44) and the
reuse of Theorem 1.

## Process-convergence input and literature

The introduction invokes a known functional limit theorem for normalized
process paths (equation (6)) and cites I. I. Gikhman and A. V. Skorokhod,
*Theory of Random Processes*, Vol. I (1972), and Yu. V. Prokhorov,
“Convergence of Random Processes and Limit Theorems in Probability Theory,”
*Theory of Probability and Its Applications* 1 (1956), 177--238. In Section 5,
equation (38) uses precisely this kind of process convergence for the
rescaled Lévy processes.

A modern general criterion suitable for formalization is Jacod and Shiryaev,
*Limit Theorems for Stochastic Processes*, 2nd ed. (2003), Chapter VII,
Section 3.a, Corollary 3.6, p. 415. It states that for zero-start real Lévy
processes, weak convergence of the marginal at one positive time is
equivalent to weak convergence of the process laws on `D([0,∞), ℝ)`. The
statement is reproduced as Theorem B.8 in Broutin, Duquesne, and Wang,
“Limits of Multiplicative Inhomogeneous Random Graphs and Lévy Trees: Limit
Theorems,” *Probability Theory and Related Fields* 181 (2021), 865--973.
See the [Springer record for Jacod--Shiryaev](https://link.springer.com/book/10.1007/978-3-662-02514-7)
and [Theorem B.8 in Broutin--Duquesne--Wang](https://perso.lpsm.paris/~tduquesne/Documents/Broutin_Duquesne_Wang_Limits_Mult_graphs_PTRF_2021.pdf).

For Mogul'skii's Theorem 4, apply this criterion to
`Zⁿ(t) = ξ(nt)/B(n)`: the process closure results give the Lévy hypotheses,
and the theorem's scalar convergence at time `1` gives `Zⁿ(1) ⇒ Fα`. The
resulting process limit is identified with the strictly stable Lévy process
by its increment laws. Restriction from
`[0,∞)` to `[0,1]` requires the usual continuity-at-the-terminal-time
argument; the fixed-time no-jump result above supplies that condition once
the process in Theorem 4 has been given a càdlàg version.

## Remaining formalization work, in source order

1. **Package the process.** Mogul'skii's Theorem 4 assumes almost-sure right
   continuity. The current `IsLevyProcess` requires càdlàg paths. Prove the
   left-limit existence needed for a right-continuous independent-increment
   process under the article's hypotheses, or state exactly which standard
   càdlàg modification theorem is being formalized. Preserve the original
   assumptions and centering, especially at `α = 1`.
2. **Obtain tightness and rescaled marginal convergence from the scalar domain
   of attraction input.** The reusable path-level conclusion is formalized in
   `Probability.Process.Levy.PathLaw.Convergence`: one result takes convergence
   of all interval-increment laws, and its Lévy-process corollary takes
   convergence of every rescaled one-time marginal and derives the increment
   limits from stationarity and zero start. The semigroup result in
   `Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Semigroup.Convergence`
   turns pointwise exponent convergence into fixed-time marginal convergence.
   For the article's hypotheses, the remaining step is to derive those
   exponent limits from the scalar limit and norming relations, or formalize
   the cited Jacod--Shiryaev criterion directly; also establish tightness,
   identify the limit as the stable unit-interval path law, and restrict from
   `[0,∞)` to `[0,1]`.
3. **Formalize equations (38)--(44) exactly.** First establish the fixed-tube
   transfer, with the event-boundary condition needed for weak convergence.
   Then formalize the arbitrary `y(n)` comparison, the choice
   `y(n) = ⌊B*(a x(n))⌋`, the asymptotic-inverse estimate, the slowly
   increasing diagonal `a(n)`, and the regular-variation calculation in
   (43)--(44). Reuse the existing regular-variation and inverse-scale APIs
   after checking their hypotheses against the article.
4. **Reuse Theorem 1's geometric proof.** Apply the existing finite-partition
   and inner/outer corridor argument to extend the tube estimate to every
   `G ∈ 𝔐` and recover `Hα(G)`. Keep this proof structurally aligned with the
   statement in Section 5 that Theorem 4 repeats the proof of Theorem 1.

## Status

Theorem 4 is **not implemented**. The unit-interval path law, its
finite-evaluation identity, its spatial-scaling pushforward, and the generic
tightness-plus-increment-convergence path-law theorem are available. The next
substantive step is deriving those convergence inputs from Theorem 4's scalar
domain-of-attraction assumptions, followed by Mogul'skii's scaling comparison
in equations (39)--(44). The previous proposed nonstable block-squeeze route
has been removed because it does not follow the article's proof.
