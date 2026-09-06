# Proof architecture

[日本語版](PROOF_ARCHITECTURE.ja.md)

This note describes the proof strategy and module responsibilities of
lean-hahn-kaplansky.

## Public completion points

The canonical public theorem for a full Hahn field is:

~~~lean
hahnKaplansky_realClosed_of_realClosed_divisible
  : IsRealClosed (HahnField k Γ)
~~~

It assumes a real closed ordered coefficient field k and a divisible ordered
additive commutative value group Γ.

For the bounded-denominator subfield of the rational Hahn field, the public
theorem is:

~~~lean
puiseuxSeries_isRealClosed
  : IsRealClosed (PuiseuxSeries k)
~~~

The concrete coefficient-field instance used by the examples is:

~~~lean
instIsRealClosedReal : IsRealClosed ℝ
~~~

The root module also exposes the concrete corollaries
`realPuiseuxSeries_isRealClosed` and `realRationalHahnField_isRealClosed`.

The root module imports the public Hahn, Puiseux, and real-number endpoints.
Downstream users should import HahnKaplanskyRealClosedness rather than
proof-internal modules.

## Hahn proof spine

The Hahn proof follows the ordered-field criterion for real closedness.

~~~text
Hahn series field and lexicographic order
  -> nonnegative elements are squares
  -> odd-cluster root problem
  -> multiplicity-one positive core
  -> fixed-lift root-or-step continuation
  -> full ordinal-prefix closure
  -> odd-degree roots
  -> IsRealClosed (HahnField k Γ)
~~~

The foundational algebra and valuation contracts live under Basic.  The
SimpleCluster modules define the odd-cluster data and the local correction
steps.  The positive core constructs the multiplicity-one root through
ordinal-stack recursion.

The fixed-lift route is the same-multiplicity engine.  Its maintained layers
are:

- SimpleCluster.Fixed.Foundation: fixed-step contracts and lower-edge/affine
  Newton resolution, including obstruction data and the root-or-step bridge.
- SimpleCluster.Fixed.Chain: chain construction, summability/evaluation
  algebra, and terminal obstruction data.
- SimpleCluster.Fixed.ShiftState: terminal translation and the fixed-lift state
  operations consumed by ordinal recursion.
- SimpleCluster.Fixed.OrdinalSupport: generic ordinal-prefix support utilities.
- SimpleCluster.Fixed.OrdinalPrefix: the resolver-free ordinal-prefix
  recursion and its strict rank invariant.

Fixed-step contracts and affine Newton resolution share the single
`SimpleCluster.Fixed.Foundation` module; consumers import it directly.

The multiplicity-one ordinal recursion under `OmegaLimit` is grouped by
responsibility:

- `OmegaLimit.Foundation`: ordinal, natural-chain, and limit-extension data.
- `OmegaLimit.Components`: compatible positive component fields.
- `OmegaLimit.PositiveRecursion`: the recursion core and the component
  assembly declarations used downstream.
- `OmegaTail.Endpoints`: the generated recursion endpoint consumed by `Main`.

The positive generated core is organized in the following responsibility families:

- OmegaTail.Data: the primitive generated limit-step and
  block-projection-core records.
- OmegaTail.CoreRoutes: generated-core projection constructors,
  ordinal cases, segment systems, below-chain
  projections, limit extensions, towers, compatibility, and final constructors.

`Main` consumes only the canonical positive endpoint and the fixed-lift
ordinal-prefix consumer.

## Puiseux proof spine

PuiseuxSeries k is represented as a bounded-denominator subfield of
HahnField k ℚ.  The main additional obligation is to preserve one common
denominator bound while constructing an odd-degree root.

~~~text
bounded-denominator Hahn support
  -> fixed denominator valuation level
  -> power-series simple-root lift
  -> residue/root translation and scaling
  -> lower multiplicity induction
  -> same-multiplicity fixed-level chain
  -> bounded-denominator Hahn root
  -> odd-degree Puiseux root
  -> IsRealClosed (PuiseuxSeries k)
~~~

The maintained Puiseux layers are:

- Puiseux.Support: bounded-denominator support, the subfield embedding,
  finite levels, and root witnesses.
- Puiseux.Valuation: valuation and cluster predicates.
- Puiseux.Lift: fixed-level residue data and power-series/Hensel lifting.
- Puiseux.Newton: polynomial support, lower-edge analysis, multiplicity
  induction, and same-multiplicity continuation.
- Puiseux.Roots: scaling, bounded roots, and square roots.
- Puiseux.lean: stable public names and the direct real-closedness assembly.

The full-multiplicity branch is where denominator control is load-bearing:
the Newton correction exponent remains in the original denominator lattice.
The resulting strictly increasing step values are therefore unbounded inside
the common lattice, so the Hahn candidate is a root in the bounded-denominator
subfield.

## Dependency boundaries

The public root module has three sibling imports:

~~~text
HahnKaplanskyRealClosedness
  +-> Main
  +-> Puiseux
  `-> RealClosedReal
~~~

Main does not depend on the Puiseux proof.  Puiseux uses the shared Basic and
SimpleCluster foundations, but its real-closedness endpoint is proved through
the fixed-level route rather than by invoking the full Hahn real-closedness
theorem.  This avoids a circular shortcut from a real-closed ambient field to
its Puiseux subfield.

The public completion points are audited by AxiomAudit.lean and exercised by
Examples.lean, Smoke.lean, and PuiseuxSmoke.lean.

## Mathematical write-up

The English and Japanese mathematical proofs corresponding to this architecture
are `docs/hahn_kaplansky_proof.tex` and
`docs/hahn_kaplansky_proof_ja.tex`.  Both can be compiled with
`task proof-pdf`; the generated PDFs are refreshed under
`docs/hahn_kaplansky_proof.pdf` and `docs/hahn_kaplansky_proof_ja.pdf`, while
auxiliary build files are kept under the ignored `docs/build/` directory.
The documents present the mathematical proof, with a correspondence appendix
linking its steps to Lean declarations and modules.

## Verification surface

The public verification surface is defined by `Taskfile.yml`: `task verify`
builds the library, exercises the public examples and smoke tests, audits the
public theorem axioms, and runs the style and whitespace checks.  `Taskfile.yml`
and the CI workflow are the canonical verification contract.
