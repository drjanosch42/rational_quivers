module

public import RationalQuivers.Gelfand.BaseChange.Cyclic
public import RationalQuivers.Gelfand.BaseChange.Hom

@[expose] public section

/-!
# `rmk:generalbases`, *Base change*: `𝔼` is compatible with base change (WP-15, T1 umbrella)

*Provenance.*  Relocated in stage T4 (WP-11) from `GF/BaseChangeMain.lean` (v1 `RationalQuivers.Gelfand.GF`) by `workflow/v2/stages/T4/VALIDATION/scripts/relocate_bc.py`: whole file, declarations moved from `GF.x` to `Gelfand.BaseChange.x` (renames in the T4 `DECL-ALLOWLIST.tsv`), references qualified, the imports of v1's `GF/Main`/`GF/Species` cut; statements and proofs otherwise unchanged.  The native statement on `HC ℓ E D`/`𝔼_E` (`prop:basechange`, `RQ2-5.14`) is in `Gelfand/BaseChange/Native.lean`.

*(2026-10-21, O-V2-6 round 2.)*  The census paragraphs below are v1's (final-release WP-16b). They
name `GF.E_E_equivalence_general` as the claimant of `RQ-5.08`.  That declaration and v1's
`Gelfand/GeneralField/Main.lean` were deleted at WP-13 (`44df340`).  The v2 census retired `RQ-5.08`
as a row and carries `rmk:generalbases` through clause rows (`CROSSWALK-v1-v2.tsv`); the equivalence
for every `E` is Theorem B, `Gelfand.gelfand_equivalence` (`Gelfand/Main.lean`), and
`prop:basechange` (`RQ2-5.14`) is claimed by `Gelfand.BaseChange.basechange`
(`Gelfand/BaseChange/Native.lean`).

*(2026-10-22, O-V2-6 round 3.)*  The three-shape list below names the quiver-side functors as
S10's `qBCss`, `qBCnn`, `qBCns`.  `qBCss` and `qBCns` were deleted with the GF residue at WP-13
(`44df340`).  No declaration named `qBCnn` was ever in the Lean package; S10's probe
`workflow/stages/S10/VALIDATION/probes/T0a-C4a-C4b-split.lean` had an `abbrev qBCnn` (a functor
type, beside `abbrev qBCss` and `abbrev qBCns`).  `E_E_baseChange_compat` states the squares
with `qBCssRel` and `qBCnsRel` (`Gelfand/BaseChange/QuiverRel.lean`) and `qBCnnRel`
(`Gelfand/BaseChange/NNRep.lean`) for `ℓ ≥ 1`, and with `RepNil.toSplitFunctor` (shapes 1 and 3) and
`qBCnnC` (`Gelfand/BaseChange/Cyclic.lean`, shape 2) for `ℓ = 0`.

Author decision of 2026-10-02: the equivalences `𝔼_E` are proved independently for each
characteristic-zero `E` (`GF.E_E_equivalence_general`); what `rmk:generalbases` additionally calls
"to be expected" is their **compatibility with base change** along an arbitrary extension `E''/E`.
`E_E_baseChange_compat` below proves it in all three shapes and for every `ℓ ≥ 0`:

1. split → split (`√-1 ∈ E`): `hcBaseChange ⋙ 𝔼_{E''} ≅ 𝔼_E ⋙ qBCss`;
2. non-split → non-split (`√-1 ∉ E''`): `hcBaseChangeNN ⋙ 𝔼_{E''} ≅ 𝔼_E ⋙ qBCnn`;
3. non-split → split (`√-1 ∉ E`, `√-1 ∈ E''`): `hcBaseChangeNS ⋙ 𝔼_{E''} ≅ 𝔼_E ⋙ qBCns`, with the
   identification `E'' ⊗_E E(√-1) ≅ E'' × E''` (`tensorSplitEquiv`) that makes `E'' ⊗_E Γ_E` split.

Each square is a **natural isomorphism between named composites** — no functor is existentially
bound — and holds for **every** specification `h : E_QSpec` (a `Prop`, so there is one `𝔼_E`).
The components are the canonical maps `E'' ⊗ M_n → (E'' ⊗ M)_n` at the vertices.  Essential
surjectivity of base change is **not** claimed: it is false for `ℓ ≥ 1`
(`BASECHANGE-ANALYSIS.md` §2, the `D̃₄` band `M_λ`).  `Hom` commutes with base change (T2) is
`BaseChange.classicalHom_baseChange` / `BaseChange.homModule_baseChange_ns`.
-/

namespace RationalQuivers.Gelfand.BaseChange

open RationalQuivers.HC RationalQuivers.Gelfand RationalQuivers.RationalQuiver CategoryTheory
open scoped TensorProduct

/-- **`rmk:generalbases`, *Base change* — T1, all three shapes, every `ℓ ≥ 0`.**

* (1) split → split, any extension `F → F''` of characteristic-zero fields: `ℓ ≥ 1` (Gelfand
  quiver, relation-carrying target) and `ℓ = 0` (cyclic quiver);
* (3) non-split → split, any `E`-algebra map `E(√-1) → E''`, `ℓ ≥ 1` and `ℓ = 0`; together with
  the identification `E'' ⊗_E E(√-1) ≅ E'' × E''` for `√-1 ∉ E`;
* (2) non-split → non-split, any `E → E''` and `E(√-1) → E''(√-1)` over it, `√-1 ∉ E''`
  and a chosen `s ∈ D'` with `s * s = -1` (which make the conjugations compatible,
  `conjCompat_of_noSqrtNegOne`), `ℓ ≥ 1` and `ℓ = 0`.  Since the v2 amendment T4-a1 the root `s` is
  an explicit binder of this conjunct; before, it was a field of `D`.  The mathematical content
  is unchanged.

**Census role (docstring-only `R-PROC-4` amendment of frozen S10, coordinator ruling `R-FR-9`,
final-release WP-16b, 2026-10-03).** This is the faithful witness of statement (T1) of
`rmk:generalbases` as rewritten by WP-17 (`330d50f`), i.e. of clause `RQ-5.08-C4` once census r20
re-syncs it. It is a **clause witness**, not the row's claimant. `RQ-5.08` is claimed by
`GF.E_E_equivalence_general` (`Main.lean`; equivalence for every `E`, clauses `H1`–`C3`), and
`rqaudit coverage` admits one claimant per row. Because this module is not the claimant's,
`rqaudit clauses` does not count the citation below toward `C4`'s coverage. The claimant cites `C4`
and its divergence field points here. The r19 text of `C4` (base change along `E(√-1)/E` only)
is the instance `E'' = E(√-1)` of shape (3). Not stated here: that the components are the
canonical maps `E'' ⊗ M_n → (E'' ⊗ M)_n` (true of the constructions `E_bc_*_iso`, but this
umbrella states `Nonempty`), and the essential-surjectivity remarks.

*(Disclosure, 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S10, coordinator ruling
`R-FR-9`, final-release WP-16c, on layer-2 finding `V3-02` of `VERIFICATION-REVIEW-2.md`.)* In
shape (3) both vertical functors of the square are stated on the underlying `E(√-1)`-objects:
`hcBaseChangeNS` is `forgetDescent ⋙ hcBaseChange` along `ι : E(√-1) → E''`, and `qBCnsRel` is
`Rep.toSplit E''`. Their identifications with `E'' ⊗_E −` are canonical (HC side: `E'' ⊗_E M_E ≅
E'' ⊗_{E(√-1)} (E(√-1) ⊗_E M_E)`; quiver side: `tensorSplitEquiv` and `1 ⊗ φ_{v,c}`) but neither is
stated as a theorem. The conjunct `Nonempty (E'' ⊗[E] E(√-1) ≃ₐ[E''] E'' × E'')`
(`tensorSplitEquiv`) is **free-standing**: the shape-(3) square does not use it, and the module
note's "the identification … that makes `E'' ⊗_E Γ_E` split" is prose, not a connection the
statement makes.

@census    none (WP-15; T1 of `BASECHANGE-ANALYSIS.md`; the *Base change* paragraph of
`rmk:generalbases`; clause witness for `RQ-5.08-C4` as rewritten by WP-17)
@source    rmk:generalbases
@clauses   RQ-5.08-C4
@imports   none
@divergence WEAKENED_OR_PARTIAL (canonicity of the components rendered as `Nonempty`; HC-side T2
and the essential-surjectivity remarks not formalized). -/
theorem E_E_baseChange_compat :
    -- (1) split → split
    (∀ (F F'' : Type) [Field F] [CharZero F] [Field F''] [CharZero F''] [Algebra F F''],
      (∀ (ℓ : ℕ) (hℓ : 1 ≤ ℓ),
        Nonempty (hcBaseChange ℓ F F'' ⋙ Split.hcLambdaToF F'' ℓ ⋙ Split.E_FNil ℓ hℓ ≅
          (Split.hcLambdaToF F ℓ ⋙ Split.E_FNil ℓ hℓ) ⋙ qBCssRel F F'')) ∧
      Nonempty (hcBaseChange 0 F F'' ⋙ Split.hcLambdaToF F'' 0 ⋙ Split.E_CycSplitFunctor ≅
        (Split.hcLambdaToF F 0 ⋙ Split.E_CycSplitFunctor) ⋙ RationalQuiver.RepNil.toSplitFunctor F'')) ∧
    -- (3) non-split → split
    (∀ (E : Type) [Field E] [CharZero E] (D : SqrtNegOneExt E)
        (E'' : Type) [Field E''] [CharZero E''] [Algebra D.carrier E''],
      (∀ (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (h : Gelfand.RationalStructure.E_QSpec D.card_gal hℓ),
        Nonempty (hcBaseChangeNS ℓ E D E'' ⋙ Split.hcLambdaToF E'' ℓ ⋙ Split.E_FNil ℓ hℓ ≅
          Gelfand.Equivalence.E_QFunctor D.card_gal hℓ h ⋙ qBCnsRel E D.carrier E'' D.card_gal)) ∧
      (∀ h : Gelfand.Cyclic.E_CycSpec D.card_gal,
        Nonempty (hcBaseChangeNS 0 E D E'' ⋙ Split.hcLambdaToF E'' 0 ⋙ Split.E_CycSplitFunctor ≅
          Gelfand.Cyclic.E_CycFunctor D.card_gal h ⋙ RationalQuiver.RepNil.toSplitFunctor E''))) ∧
    (∀ (E : Type) [Field E] [CharZero E] [NoSqrtNegOne E] (D : SqrtNegOneExt E)
        (E'' : Type) [Field E''] [CharZero E''] [Algebra E E''] [Algebra D.carrier E'']
        [IsScalarTower E D.carrier E''],
      Nonempty ((E'' ⊗[E] D.carrier) ≃ₐ[E''] E'' × E'')) ∧
    -- (2) non-split → non-split
    (∀ (E : Type) [Field E] [CharZero E] (D : SqrtNegOneExt E)
        (E'' : Type) [Field E''] [CharZero E''] [NoSqrtNegOne E''] (D'' : SqrtNegOneExt E'')
        [Algebra E E''] [Algebra D.carrier D''.carrier] [Algebra E D''.carrier]
        [IsScalarTower E E'' D''.carrier] [IsScalarTower E D.carrier D''.carrier]
        (s : D.carrier) (hs : s * s = -1),
      ∃ hι : ConjCompat D D'',
        (∀ (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (h : Gelfand.RationalStructure.E_QSpec D.card_gal hℓ) (h'' : Gelfand.RationalStructure.E_QSpec D''.card_gal hℓ),
          Nonempty (hcBaseChangeNN ℓ E D E'' D'' hι ⋙ Gelfand.Equivalence.E_QFunctor D''.card_gal hℓ h'' ≅
            Gelfand.Equivalence.E_QFunctor D.card_gal hℓ h ⋙ qBCnnRel (h'' := D''.card_gal) (restrictionDatum D D'' hι))) ∧
        (∀ (h : Gelfand.Cyclic.E_CycSpec D.card_gal) (h'' : Gelfand.Cyclic.E_CycSpec D''.card_gal),
          Nonempty (hcBaseChangeNN 0 E D E'' D'' hι ⋙ Gelfand.Cyclic.E_CycFunctor D''.card_gal h'' ≅
            Gelfand.Cyclic.E_CycFunctor D.card_gal h ⋙ qBCnnC (h'' := D''.card_gal) (restrictionDatum D D'' hι)))) := by
  refine ⟨fun F F'' _ _ _ _ _ => ⟨fun ℓ hℓ => ⟨E_bc_split_iso F F'' ℓ hℓ⟩,
      ⟨E_bc_cyc_split_iso F F''⟩⟩,
    fun E _ _ D E'' _ _ _ => ⟨fun ℓ hℓ h => ⟨E_bc_mixed_iso ℓ E D E'' hℓ h⟩,
      fun h => ⟨E_bc_cyc_mixed_iso E D E'' h⟩⟩,
    fun E _ _ _ D E'' _ _ _ _ _ => ⟨tensorSplitEquiv D E''⟩,
    fun E _ _ D E'' _ _ _ D'' _ _ _ _ _ s hs => ?_⟩
  refine ⟨conjCompat_of_noSqrtNegOne D D'' s hs, fun ℓ hℓ h h'' => ?_, fun h h'' => ?_⟩
  · exact ⟨E_bc_nn_iso ℓ E D E'' D'' _ hℓ h h''⟩
  · exact ⟨E_bc_cyc_nn_iso E D E'' D'' _ h h''⟩

end RationalQuivers.Gelfand.BaseChange
