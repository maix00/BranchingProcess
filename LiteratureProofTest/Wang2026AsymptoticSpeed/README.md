# WANG Yiyang (2026): endpoint and speed arguments

Reference: WANG Yiyang, *Asymptotic Speed of the N-Branching Random Walk with
Infinite Offspring*, Fudan University dissertation (2026), Chapter 4,
Theorem 1.1 and Theorem 1.2. Result numbers here are the displayed PDF numbers.
The manifest records the exact recovery and source-checkout revisions.

## Preserved endpoint argument

`EndpointUpperTail/Theorem.lean` recovers the complete positive-initial-
exponent argument from the parent of `c8009bf1d` (the commit replacing that
argument by the weak-tail theorem). Its namespace is now
`LiteratureProofTest.Wang2026AsymptoticSpeed`; it is not a compatibility alias
for a production declaration. The mathematical statement retains the same
finite-cross-weight, centered finite positive spinal variance, positive
initial exponent, and cubic horizon assumptions. Production keeps one generic
weak-tail implementation and derives its finite-cross-weight case from it.

For `L=log N`, the preserved proof follows these source steps:

1. Choose `b,v,c` satisfying the endpoint and capacity margins.
2. Up to `ell=floor(L^(5/2))`, retain the horizontal-tube population in
   `[-bL,0]`, with endpoint window `[-bL,(-b+v)L]`.
3. From its selected roots, retain descendants in the tilted corridor of
   duration `D=H-ell`, slope `κ c^(-2) D^(-2/3)`, width `c D^(1/3)`, and
   terminal width `v D^(1/3)`, where `κ=π²σ²/2`.
4. Control the cumulative population by the two-stage first moments and
   Markov's inequality (`SecondStage/Capacity/Bound.lean`).
5. Control a small first-stage root count and subsequent independent failures
   (`SecondStage/Failure/Critical.lean`). The one-root corridor input remains
   the reusable critical-corridor theorem from Chapter 3.
6. Compare the actual selected process to this constructed population and
   combine terminal emptiness with capacity failure to get the polynomial tail.

All source-specific population, window, cutoff, root-selection, and comparison
support formerly stranded under production `FirstStage/`, `SecondStage/`,
and the dedicated `Population/` modules is now inside this citation directory.
The unused lower-count wrapper formerly in `Population/LowCount.lean` is
removed: the preserved proof already calls the shared lower-count foundation
through its root-count step. Every retained literature module belongs to one
of the manifested entry dependencies.
Shared branching, coupling, many-to-one and small-deviation interfaces remain
in production. Four source-independent cubic-scale limit lemmas were moved
to `Analysis/Asymptotics/Sequence/CubicScale.lean` with general scale names;
the tests reference that owner rather than duplicate its arithmetic.

`EndpointConvergence.lean` recovers the historical `L²` assembly from the parent
of `24e272fd`. Its positive-exponent and full-capacity arguments call the
preserved two-stage upper tail. The single-root argument's remaining-horizon
adapter is preserved in `EndpointUpperTail/HorizonWindow.lean` and
`EndpointUpperTail/SingleRoot/`: it also calls the preserved positive-start
argument. The fourth-moment closure and lower-tail foundations are reused.
The extra positive exponential moment for the single-root `L²` case remains
explicit. Namespace/qualification repairs and import changes preserve these
statements and calculations; no additional axiom or assumed conclusion is used.

## Original fourth-moment speed argument

`Speed/FourthMoment.lean` preserves the fourth-moment/Cauchy–Schwarz
argument for Theorem 1.2 formerly in the required regression root. Its
`Speed/RestartSecondMoment.lean` bound controls the exceptional event
using the restart endpoint second moment. The remaining-horizon mean in
`Speed/Lemmas/RemainingHorizon.lean` now calls the preserved endpoint L2
argument. The final block-speed squeeze therefore uses the archived two-stage
proof rather than the replacement weak-tail endpoint upper theorem. The
stronger original hypotheses remain explicit. The named final assertion also
retains the almost-sure and L1 identification of its speed with the actual
selected process, rather than merely asserting existence of a numeric sequence. Shared stopping, reset, branching
and moment foundations remain in their production owners.

## Historical speed variant and verification boundary

`Speed/Limit.lean` preserves the finite-cross-weight, first-moment speed implementation
from the parent of `c8009bf1d`. In particular its continuation-mean calculation
calls the archived two-stage positive-start upper tail, not the new weak-tail
upper tail or public weak-tail endpoint mean. Its private exceptional-event
calculation is retained as test support; production uses the more general
measure-level interface.

This historical implementation weakens the moment requirements compared with
the original endpoint-based speed exposition: it uses the first-moment restart
bound before the block-speed squeeze. It is preserved as a separately
identified historical argument. Compilation and its named axiom audit verify
that argument under its recorded hypotheses. They do not certify stepwise
identity with every line of the dissertation's Theorem 1.2 proof, which also
uses an endpoint-based passage to expectations. The manifest and report keep
that distinction explicit; a source discrepancy must be investigated before
it is called an error in the dissertation. No LaTeX source is changed here.
