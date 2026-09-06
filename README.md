# Hahn--Kaplansky real closedness

[日本語版](README.ja.md)

This repository formalizes real closedness results for Hahn and Puiseux series
fields in Lean 4 with mathlib.

## Main theorems

If k is a real closed ordered field and Γ is a divisible ordered additive
commutative group, the lexicographically ordered full Hahn field is real
closed:

~~~lean
hahnKaplansky_realClosed_of_realClosed_divisible
  : IsRealClosed (HahnField k Γ)
~~~

The bounded-denominator Puiseux series field over a real closed ordered field
is real closed as well:

~~~lean
puiseuxSeries_isRealClosed
  : IsRealClosed (PuiseuxSeries k)
~~~

The repository also supplies the real-number instance used by the concrete
examples:

~~~lean
instIsRealClosedReal : IsRealClosed ℝ
~~~

Consequently, the concrete real-coefficient fields are available as named
corollaries:

~~~lean
realPuiseuxSeries_isRealClosed : IsRealClosed (PuiseuxSeries ℝ)
realRationalHahnField_isRealClosed : IsRealClosed (HahnField ℝ ℚ)
~~~

The stable public entry points are imported by:

~~~lean
import HahnKaplanskyRealClosedness
~~~

These public theorems introduce no project-specific axioms.

## Build and verification

The project uses the pinned Lean toolchain in lean-toolchain and mathlib
through Lake.

~~~text
lake exe cache get
lake build
lake build HahnKaplanskyRealClosedness.Examples
lake env lean HahnKaplanskyRealClosedness/AxiomAudit.lean
lake env lean HahnKaplanskyRealClosedness/Smoke.lean
lake env lean HahnKaplanskyRealClosedness/PuiseuxSmoke.lean
~~~

The same checks are grouped in Taskfile.yml:

~~~text
task verify
~~~

The style check is available separately:

~~~text
task lint
~~~

## Mathematical proof write-up

The English and Japanese TeX proofs are available at
[`docs/hahn_kaplansky_proof.tex`](docs/hahn_kaplansky_proof.tex) and
[`docs/hahn_kaplansky_proof_ja.tex`](docs/hahn_kaplansky_proof_ja.tex).
The corresponding PDFs are committed at
[`docs/hahn_kaplansky_proof.pdf`](docs/hahn_kaplansky_proof.pdf) and
[`docs/hahn_kaplansky_proof_ja.pdf`](docs/hahn_kaplansky_proof_ja.pdf).
The documents present the mathematical proof and an appendix linking its
steps to Lean declarations and modules.
With a TeX installation, build both with:

~~~text
task proof-pdf
~~~

The reproducible build uses `docs/build/` as its working directory and replaces
the committed PDFs only when their bytes change.  Repository VS Code settings
send LaTeX Workshop output to the same ignored directory and build on save, not
merely when a TeX file is opened.

Examples.lean is a small downstream-style API test.  AxiomAudit.lean checks
that the public theorems depend only on the standard
classical Lean/mathlib axioms propext, Classical.choice, and Quot.sound.

## Proof architecture

The stable mathematical and module architecture is described in
[PROOF_ARCHITECTURE.md](PROOF_ARCHITECTURE.md).  A Japanese translation is
available as [PROOF_ARCHITECTURE.ja.md](PROOF_ARCHITECTURE.ja.md).  In outline:

1. Hahn series provide the ordered field and square-root construction.
2. Odd-cluster root problems are solved by an ordinal-stack positive core and
   a resolver-free fixed-lift ordinal-prefix argument.
3. The ordered-field criterion yields real closedness of the full Hahn field.
4. For Puiseux series, bounded-denominator support is preserved through
   fixed-level Newton--Puiseux continuation.
5. The Puiseux odd-cluster criterion and square-root criterion yield
   puiseuxSeries_isRealClosed.

## Documentation map

The repository separates its public overview, proof architecture, complete
mathematical write-up, and citation metadata:

| Document | Role |
| --- | --- |
| `README.md` | English public entry point: theorems, quick verification, and links. |
| `README.ja.md` | Japanese public counterpart with the same scope. |
| `PROOF_ARCHITECTURE.md` and `.ja.md` | Stable mathematical proof spine and module ownership. |
| `docs/hahn_kaplansky_proof*.tex` and committed PDFs | Mathematical proofs with a correspondence to the Lean formalization. |
| `CITATION.cff` | Machine-readable citation metadata only. |

## License and citation

The project is released under Apache-2.0.  Citation metadata is available in
CITATION.cff.
