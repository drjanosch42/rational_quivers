# Rational quivers: manuscript and Lean 4 formalization

This repository contains the manuscript

> Fabian Januszewski, *Rational structures on quivers and a generalization of Gelfand's equivalence*

(LaTeX source in [`latex/`](latex/)) and its complete formalization in Lean 4 with mathlib
(Lean package in [`lean/`](lean/)).

The main result (Theorem B, `thm:introB`) states the following. Let `E` be a field of characteristic 0,
let `ℓ ≥ 0` and `λ = ℓ²`. Then the functor `𝔼_E` is an equivalence of abelian categories

    𝔼_E : HC_λ(𝔰𝔩₂, SO(2))_E  ≃  Rep^nil(Γ_E)

between the `E`-rational Harish-Chandra modules with infinitesimal character `λ` and the nilpotent
representations of the `E`-rational Gelfand quiver `Γ_E` (the cyclic quiver when `ℓ = 0`). Theorem A
(`thm:introA`) is the case `E = ℚ`, and Gelfand's classical equivalence is the case `E = ℂ`. The
manuscript also proves the equivalence for the twisted forms attached to any quadratic extension
`D'/E` (§5.6).

Every theorem of the manuscript that the formalization claims (109 labelled statements, listed in
[`correspondence/`](correspondence/)) is proved in Lean without `sorry` and with no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`. CI checks both on every push.

Exported from the development repository at commit `a155fd7173150417b85225af1b8956c0afa29275` (version 1.0.1).

## Paper ↔ Lean

The complete map, one row per labelled statement, is
[`correspondence/CORRESPONDENCE.md`](correspondence/CORRESPONDENCE.md) (machine-readable:
[`correspondence/LABEL-DECL.tsv`](correspondence/LABEL-DECL.tsv)). The main results are below. All Lean names are in the namespace
`RationalQuivers`, which is omitted.

| Manuscript (`\label`) | Lean declaration | File (`lean/RationalQuivers/`) |
|---|---|---|
| Theorem A (`thm:introA`), over `ℚ` | `Gelfand.Rational.theoremA` | `Gelfand/Rational.lean` |
| Theorem B (`thm:introB`), every field of characteristic 0 | `Gelfand.gelfand_equivalence` | `Gelfand/Main.lean` |
| `thm:EEequivalence` (`ℓ ≥ 1`) | `Gelfand.gelfand_equivalence_pos` | `Gelfand/Main.lean` |
| `thm:cyclicEEequivalence` (`ℓ = 0`) | `Gelfand.gelfand_equivalence_zero` | `Gelfand/Main.lean` |
| `thm:EEQQequivalence`, `thm:cyclicEEQQequivalence` | `Gelfand.Rational.E_Q_equivalence`, `Gelfand.Rational.cyclic_E_Q_equivalence` | `Gelfand/Rational.lean` |
| `cor:gelfandspecies`, `cor:cyclicspecies` | `Gelfand.Species.species_equivalence_intrinsic`, `Gelfand.Species.cyclic_species_equivalence` | `Gelfand/Species/Rational.lean` |
| `thm:speciesE` (species form over `E`) | `Gelfand.Species.speciesE` | `Gelfand/Species/Equivalence.lean` |
| `rmk:classicalcases` (`E = ℂ`, `E = ℝ`) | `Gelfand.Rational.gelfand_equivalence_complex`, `…_real` | `Gelfand/Rational.lean` |
| `def:GammaE` | `Gelfand.GammaE` | `Gelfand/Target.lean` |
| `lem:GammaEbasechange` | `Gelfand.GammaE_eq_baseChange` | `Gelfand/TargetBaseChange.lean` |
| `prop:basechange` | `Gelfand.BaseChange.basechange` | `Gelfand/BaseChange/Native.lean` |
| `thm:twistedEEequivalence` (twisted forms) | `Gelfand.gelfand_equivalence_twisted` | `Gelfand/TwistedForms.lean` |
| `thm:galoisdescent` (§1) | `Descent.galoisDescent` | `Descent/Galois.lean` |
| `thm:KrationalquiveretaleKspeciesantiequivalence` (§2) | `speciesAntiEquivalence` | `Species/AntiEquivalence.lean` |
| `thm:species_equivalence` (§2) | `RationalQuiver.species_equivalence` | `Species/Rep/Equivalence.lean` |
| `ex:finitedimensional`, `ex:discreteseries`, `ex:principalseries` (§6) | `Examples.F`, `Examples.D`, `Examples.P` | `Examples/` |

The Lean sources follow the sections of the manuscript:

| Manuscript | Lean (`lean/RationalQuivers/`) |
|---|---|
| §1 Rational structures on quivers, Galois descent | `Descent/`, `Quiver/` |
| §2 Étale species and their representations | `Species/` |
| §3 Rational Harish-Chandra modules | `HC/` |
| §4 Unipotent stabilization and square roots | `Unipotent/` |
| §5 The equivalence over `E`, over `ℚ`, base change, twisted forms | `Gelfand/` |
| §6 Examples | `Examples/` |

## Building

The toolchain is `leanprover/lean4:v4.31.0` (`lean/lean-toolchain`), and mathlib is pinned to commit
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (`lean/lakefile.toml`, `lean/lake-manifest.json`). With
[elan](https://github.com/leanprover/elan) installed:

```
cd lean
lake exe cache get     # download the prebuilt mathlib cache
lake build             # build the formalization (library RationalQuivers)
lake build Check       # check the claimed declarations (see below)
```

Without `lake exe cache get`, `lake build` compiles mathlib from source, which takes hours.

The manuscript builds with a standard TeX Live installation:

```
cd latex
latexmk -pdf rational_quivers.tex
```

(Without `latexmk`, run `pdflatex rational_quivers.tex` three times: the cross-references and the
table of Appendix A settle on the third pass.)

## What is checked

* **No `sorry`, no extra axioms.** `lean/Check/Axioms.lean` is generated from
  `correspondence/LABEL-DECL.tsv`. For each claimed declaration it fails the build if the
  declaration is missing or depends on an axiom other than `propext`, `Classical.choice` and
  `Quot.sound` (a `sorry` shows up as the axiom `sorryAx`). CI also runs
  [axiom-audit](https://github.com/leanprover-community/axiom-audit) over every declaration in the
  namespace `RationalQuivers` (through
  [lean-action](https://github.com/leanprover/lean-action)).
* **No imported mathematics.** No theorem takes a result of the literature as a hypothesis. The
  results of other works that the manuscript cites but does not reprove are listed in
  `correspondence/STATEMENTS.tsv` (column `cited_externals`).
* **What the statements say.** That the Lean statements formalize the printed ones has to be read
  rather than computed. Every claimed declaration's docstring has a `@divergence` field that
  states how the Lean statement differs from the printed text, if at all (`none`,
  `JUSTIFIED_REFORMULATION` or `WEAKENED_OR_PARTIAL`, with the affected clauses).

## Scope and modelling choices

* **Harish-Chandra modules are modelled by Galois descent.** `HC ℓ E D` (`HC/Category.lean`) presents
  an object of `HC_λ(𝔤,K)_E` as an `E`-vector space `M_E` with weight data on
  `M_{L_E} = L_E ⊗_E M_E`, `L_E = E[√-1]`, and the Galois action as a property. The intrinsic reading
  as `(𝔤_E, K_E)`-modules is not formalized; for `E = ℂ` the model is proved equivalent to the
  classical category of Harish-Chandra modules. The twisted forms `HCTwisted` use the same
  presentation.
* **Main equivalences are pinned to the manuscript's functor.** They are stated as
  `∃ e, e.functor = …`, so they are statements about `𝔼_E`, not about some equivalence.
  `Rep^nil(Γ_E)` carries the abelian structure transported along `𝔼_E`, as in `rmk:EEabelian`.
* **Not formalized.** 17 labelled statements have no Lean claimant (claimant `-` in
  `correspondence/LABEL-DECL.tsv`). They are remarks that are not used elsewhere in the paper (for
  example the `H¹` classification of rational structures, the stack remarks, the alternative split
  construction `rmk:asymmetricsplitES`, and the `E`-forms of `SO(2)`), plus one definition taken from
  the literature (`def:rationalpairs`). Their scope is recorded in `correspondence/STATEMENTS.tsv`
  (`in_scope`, `scope_note`).

## Docstring conventions

The Lean docstrings cite the development record:

* `@census RQ2-<sec>.<nn>` (and clause ids `RQ2-<sec>.<nn>-<C|H|S…>`) name census rows. They resolve
  through `correspondence/STATEMENTS.tsv` and `correspondence/LABEL-DECL.tsv`.
* `@divergence` states how a declaration departs from the printed statement (see above).
* Stage names (`T0`–`T6`, `S0`–`S10`), rule, ruling and exception ids (`R…`, `EX-…`), and paths under
  `workflow/` refer to the private development repository. That repository holds the process record:
  plans, the full census, reviews, audits and gate logs. It is archived privately and is available
  from the author on request. Nothing in this repository needs it to build or to check.

## Use of AI

The formalization was carried out with the assistance of AI agents. Claude Code and Anthropic's
Claude models (Claude Sonnet 5.5, Claude Opus 5.5 and Claude Fable 5.1) were used, under the author's
direction, for the auto-formalization of the results and proofs of the manuscript in Lean and to
prepare the final revision of the manuscript. The author reviewed and edited the results as needed
and takes full responsibility for the content.

## Licence

* The Lean code (`lean/`) and the other files of this repository: Apache License 2.0, see
  [`LICENSE`](LICENSE).
* The manuscript source (`latex/`): Creative Commons Attribution 4.0 International (CC BY 4.0), see
  [`LICENSE-paper.md`](LICENSE-paper.md).

## Citing

See [`CITATION.cff`](CITATION.cff). Please cite the paper, and the archived version of this
repository (Zenodo DOI `10.5281/zenodo.23735853`) together with the commit you used.

## Provenance

This repository is a snapshot export of a private development repository, produced by a script and
never edited by hand. [`EXPORT-PROVENANCE`](EXPORT-PROVENANCE) names the source commit and lists the
SHA-256 of every exported file. Every Lean module under `lean/RationalQuivers/` is byte-identical to
the development tree at that commit; only `lean/RationalQuivers.lean`, `lean/lakefile.toml` and
`lean/Check/` are generated. The development tree also contains an audit instrument and an
archived interface to the literature, both of which are left out: no exported module imports them.
