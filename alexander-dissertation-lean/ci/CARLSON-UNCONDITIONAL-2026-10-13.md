# Unconditional targets and literal source schemas — 13 October 2026

**All three unconditional comparator targets pass locally.** The combined
completion gate also checks stronger source-schema witnesses, including the
literal particular-code formula with its existential outside knowledge.
The focused development covers 320 project modules; 101 axiom reports pass
with only `propext`, `Classical.choice` and `Quot.sound`.

The online starting point is
[`b95d340194b9d47dfb5224e3e6259e9f0b728280`](https://github.com/avg-netizen/alexander-thesis-3-1-1-lean/commit/b95d340194b9d47dfb5224e3e6259e9f0b728280).
PRs 30–31 construct terminating finite comparison, duplicate-free enumeration
of the entire actual Carlson core, its relation Programs, and the effective
ordinal package. `Thesis313Unconditional.lean` uses this package to discharge
the sole remaining premise of the checked stage argument. The exact comparator,
solution specification, syntax, arithmetic-coding interface and semantics are
unchanged from the earlier checkpoint.

## This local continuation

No subagents were used. The Git branch is
`codex/local-source-completion-2026-10-13` in the adjacent
`alexander-thesis-3-1-1-lean` checkout.

The existing [SourceParticularCode.lean](../Alexander313/SourceParticularCode.lean)
is imported unchanged into that checkout. Its arithmetic-coherence argument
already proves the connection between external natural code witnesses and
Alexander's literal formula:

\[
\exists e\,K_i\forall x\,(K_j\varphi(x)\leftrightarrow x\in W_e).
\]

[SourceUnconditional.lean](../Alexander313/SourceUnconditional.lean) removes
the last ordinal-package premise from this stronger 3-1-3 witness, then derives
the stronger 3-1-2 witness by projection. Each theorem supplies one family for
every unrestricted unary formula, for an arbitrary recursively enumerable
well-founded relation. It retains the canonical arithmetic template and all
original solution fields.

The incoming completion gate checked only `thesis312` and `thesis313`.
[Completion.lean](../Completion.lean) now checks `thesis311` too, and checks
the expanded literal source formula without an ordinal-package premise. It
imports the proved target modules directly. The focused workflow builds the
new source module before running this gate.

## Validation

The [local receipt](local-completion-2026-10-13.json) records the commands,
exit codes, log hashes and every source in the 320-module import closure.
It also pins the five unchanged specification/semantics files. The gate
logs are [completion.log](../build-logs/2026-10-13-unconditional/completion.log)
and [core-presentation.log](../build-logs/2026-10-13-unconditional/core-presentation.log).
Seven completion reports and 94 core reports passed their axiom whitelists.
The build completed successfully; its warnings are retained in
[build.log](../build-logs/2026-10-13-unconditional/build.log).

From the Git checkout, reproduce the theorem checks with:

```sh
lake build +Alexander313.Thesis313Unconditional +Alexander313.SourceUnconditional +Alexander313.Carlson.CorePresentationExamples
lake env lean Completion.lean > completion.log
python3 scripts/check_axioms.py completion.log
lake env lean CompileCarlsonCorePresentation.lean > core-presentation.log
python3 scripts/check_axioms.py core-presentation.log
```

The [online CI receipt](online-ci-38432008534.json) separately records the
nine successful workflows for the imported PR 31 head and its matching merged
tree. These online checks predate the local source-schema strengthening; that
strengthening has local kernel checks and has not been pushed.

## Scope and remaining work

No construction premise remains for the three formal comparator targets.
The prior source/model audit is in
`../../samuel-allen-alexander/review-finite-guards-2026-10-09/final-semantic-faithfulness-audit.md`;
its ordinal-package boundary is now discharged, and its literal code bridge
is unconditional. The concrete arithmetic formula uses domains of Mathlib's
partial-recursive program numbering. A separately fixed numbering or formula
requires a translation theorem.

The full legacy Wilken library was not rebuilt. Its wider tracking/evaluation
development and any additional source-fidelity review remain separate scopes;
they are not premises of the proved comparator targets. The October 9 metadata
and declaration map remain historical snapshots. This checkpoint, its receipt
and the project README own the current verified theorem status.
