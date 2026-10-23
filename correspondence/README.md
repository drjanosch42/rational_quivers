# Correspondence between the manuscript and the Lean code

Machine-readable tables that link the labelled statements of `latex/rational_quivers.tex` to Lean
declarations. They are copied verbatim from the development repository's census (the census in
force at the exported commit; see `EXPORT-PROVENANCE`). `CORRESPONDENCE.md` is a readable table
generated from `LABEL-DECL.tsv`.

All files are UTF-8, tab-separated, one row per labelled statement. The manuscript is cited by its
LaTeX `\label`, never by number or line, so the tables stay valid when the PDF is re-typeset.

## `LABEL-DECL.tsv`

The label-to-declaration map. The first line is a comment naming the command that generated it in
the development repository; the second line is the header.

| Column | Meaning |
|---|---|
| `census_id` | Statement id `RQ2-<section>.<nn>`; section 0 is the introduction. These are the ids that the `@census` tags in the Lean docstrings cite. |
| `latex_label` | The statement's `\label` in `latex/rational_quivers.tex`. |
| `kind` | The kind of statement (see below). |
| `claimant` | The fully qualified Lean declaration that formalizes the statement, or `-` if the statement is not formalized. |
| `module` | The Lean module that contains the claimant (`RationalQuivers.Gelfand.Main` is `lean/RationalQuivers/Gelfand/Main.lean`), or `-`. |

Every claimant is checked by `lean/Check/Axioms.lean` (built by `lake build Check`): it must exist
and depend on no axiom other than `propext`, `Classical.choice` and `Quot.sound`.

## `STATEMENTS.tsv`

The census proper: what each labelled statement says, in plain-text paraphrase.

| Column | Meaning |
|---|---|
| `census_id` | As above. |
| `kind` | As above. |
| `latex_label` | As above. |
| `working_name` | The Lean name the statement was planned under. `(planned)` marks a name fixed before the code was written; the authoritative claimant is the one in `LABEL-DECL.tsv`. |
| `section` | The manuscript section. |
| `enunciation` | The statement, paraphrased in ASCII. |
| `quantifiers` | The quantifier prefix, or `-`. |
| `hypotheses` | The hypotheses, as the census reads them. |
| `conclusion` | The conclusion. |
| `cited_externals` | Results of other works the statement relies on, or `-`. |
| `in_scope` | `IN` (to be formalized), `OPTIONAL` or `OUT` (stated in the manuscript but outside the formalization). |
| `in_scope_per_plan` | The same classification as fixed by the development plan. |
| `scope_note` | Free-text note: disclosures, cross-references to other rows, and identifiers of the development record. |

### Kinds

`theorem`, `proposition`, `lemma`, `corollary`, `definition` and `example` are statements of
those kinds. The suffix `-claim` marks a remark, a definition, a displayed equation or a paragraph of
a proof that asserts a mathematical fact (`remark-claim`, `definition-claim`, `proposition-claim`); a
plain `remark` asserts nothing that needs proof. `definition-proposition` is a definition whose
construction carries an assertion (for example, that a diagram commutes), and `definition-cited` is a
definition taken from the literature. A `latex_label` cell may name several labels separated by
` / ` when one row covers several displayed equations.

### Identifiers of the development record

The `scope_note` column and the Lean docstrings cite identifiers of the private development
record: exception ids (`EX-…`), open questions (`OQ-…`), rulings (`R-…`), stage names (`T0`–`T6`)
and paths under `workflow/`. The `scope_note` column also mentions rulings and authorizations of the
author and of the team lead that coordinated the development (by date, for example "team-lead ruling
2026-10-19", or by the record file `AUTHOR-QUEUE.md` that holds them), and short commit ids of the
development repository; these commits are not part of this repository's history. That record (plans, reviews, audits and gate logs) is archived
privately and is available from the author on request. Neither the build nor the checks need it.
