# A symmetric universal machine with identically zero universal intelligence

**21-page explanatory manuscript, 17 November 2026.**
[Read the paper](paper.pdf) · [LaTeX source](paper.tex) · [Source and proof scope](SOURCES.md)

The paper addresses the intelligence-sign question in Section 5 of Samuel
Allen Alexander and Marcus Hutter, *Reward-Punishment Symmetric Universal
Intelligence*. For every fixed suffix-free reinforcement-learning encoding,
it constructs an ordinary symmetric prefix-free universal Turing machine
whose original shortest-description-weighted universal intelligence is zero
for every policy. The strong sign is therefore computed by the constant-zero
algorithm; the weak-sign requirement follows as well.

The original class of well-behaved environments is retained: convergence
and the value bound must hold for every policy. The theorem includes
noncomputable rational-output policies. The environment sum uses actual
full kernels and the shortest length among all complete descriptions.
Universality is retained on arbitrary inputs. The construction is effective
as an ordinary partial machine, even though its semantic pairing need not
be computably chosen from an environment description.

The paper supplies the delayed cancellation transform, full-history probe,
finite inverse tests, unique backward core, partial-program guards,
prefix-free framing, exact shortest-weight equality, and absolute convergence
argument. This is an answer through a zero aggregate score. A nonzero or
policy-discriminating strengthening is not established here.

## Build and review

Run `python3 build_pdf.py` here with Python 3 and a standard TeX Live or MiKTeX
installation. The script runs pdfLaTeX three times and downloads nothing.
The PDF uses embedded Latin Modern and AMS fonts. Its complete LaTeX source
and bibliography are in `paper.tex`.

All 21 pages were rendered and visually inspected. The final build has no
unresolved references or layout warnings. [VERIFICATION.json](VERIFICATION.json)
pins the PDF and build observations; `SHA256SUMS` identifies the committed
edition. Rebuilding can change PDF metadata and hence its byte hash.

The result and exposition were developed by OpenAI Codex under the repository
owner's direction. This is a hand-proof manuscript with AI review, without a
proof-assistant certificate, independent human mathematical review, or a
historical priority finding. The repository's dissertation Lean results do
not certify this paper.
