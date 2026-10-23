import RationalQuivers.Gelfand.RationalStructure.Bridge
import RationalQuivers.Gelfand.GeneralField.Basic
import RationalQuivers.Gelfand.Split.Chains
import RationalQuivers.HC.Normalization

/-!
# `eq:conjugatenormalizedcomparison` (§5.2, Step O-8)

The conjugate comparison diagram: complex conjugation transforms `eq:normalizedcomparison` into
`eq:conjugatenormalizedcomparison` (claimant of `RQ2-5.03`, `conjugate_diagram_commutes`), and
`conj_normalized_operators` (`T₋^c = T₊`, `X⋆^c = Y⋆`, used by Step O-9).

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Conjugate.lean` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.RationalStructure.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

*(2026-10-21, O-V2-6 round 2.)*  The carried docstrings and `@divergence` fields below compare with
S8's `HC.RationalSetup` and `Gelfand.HCQObj`, the v1 `ℚ`-forms.  They were moved at WP-8 (`d2a2a47`)
and deleted at WP-13 (`9c6b193`, with `Gelfand/QNormalization.lean` and `Gelfand/Category.lean`).
The v2 presentation is `RationalSetupOver`/`HCEObj`, reached from `HC ℓ E D` through the `R-V2-3`
bridges.

@census none (module)
-/

/-- S10's `RationalSetupOver` forgets onto the generic `QiSetup`, as S8's `HC.RationalSetup`
forgets onto `QiSetup`.  @census none (helper; WP-8c) -/
def RationalQuivers.Gelfand.RationalSetupOver.toQiSetup {ℓ : ℕ} {E : Type} [Field E] [CharZero E]
    {D : RationalQuivers.Gelfand.SqrtNegOneExt E} {Mq : Type} [AddCommGroup Mq] [Module E Mq]
    {Mi : Type} [AddCommGroup Mi] [Module D.carrier Mi]
    (S : RationalQuivers.Gelfand.RationalSetupOver ℓ E D Mq Mi) :
    RationalQuivers.Gelfand.Split.QiSetup D.carrier ℓ Mi :=
  ⟨S.weight, S.gic⟩


namespace RationalQuivers.Gelfand.RationalStructure

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {D : SqrtNegOneExt E}
open scoped TensorProduct

variable {ℓ : ℕ} {Mq : Type} [AddCommGroup Mq] [Module E Mq]
variable {Mi : Type} [AddCommGroup Mi] [Module D.carrier Mi]


/-- Conjugation swaps the powers: `c ∘ X^k ∘ c = Y^k`.  The `k`-fold iterate of S7's
`RQ-3.10-C3` (`S.conj_X`), and the whole content of `X⋆^c = Y⋆` once the scalar `γ⋆⁻¹` is seen to
be `Gal`-fixed (`conj_gammaStarF`).  @census none (helper) -/
theorem conj_pow_X (S : RationalSetupOver ℓ E D Mq Mi) (k : ℕ) (v : Mi) :
    S.conj ((S.weight.X ^ k) v) = (S.weight.Y ^ k) (S.conj v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, S.conj_X']

/-- **`RQ-5.03-C1`** — complex conjugation *transforms* `eq:normalizedcomparison` into
`eq:conjugatenormalizedcomparison`: it carries each arrow of the one to the corresponding arrow of
the other.  `X ↔ Y` is S7's `RQ-3.10-C3` (`S.conj_X`, `S.conj_Y`, both **proved** on `stage/S7`);
`X⋆ ↦ Y⋆` and `T₋ ↦ T₊` are the §5.2 content, and they reappear as census clause `RQ-5.04-C3`
("`T₋^c = T₊` and `X⋆^c = Y⋆`"), which is what drives the simultaneous stabilization.

@census    none (auxiliary; discharges census clause `RQ-5.03-C1`)
@source    eq:conjugatenormalizedcomparison
@clauses   RQ2-5.03-C1,
           RQ2-5.03-S-O8
@imports   none
@divergence Stated for a bare `RationalSetup` (`gic` only), not `Gelfand.HCQObj` (`RQ-5.05`'s own
category, which additionally requires admissibility, finite generation and the central character,
`DESIGN-NOTES.md` §4.3) — a **true generalization** (`CONVENTIONS.md` §3: legitimate, disclosed),
since the proof uses none of the three extra conditions (2026-09-03, `R-S8-16`(c), `V-S8-D1-4`(b)). -/
theorem conj_normalized_operators (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ) :
    (∀ v : Mi, S.conj (S.weight.X (S.conj v)) = S.weight.Y v) ∧
    (∀ v : Mi, S.conj (S.weight.Y (S.conj v)) = S.weight.X v) ∧
    (∀ v : Mi, S.conj (Split.xStar S.toQiSetup (S.conj v)) = Split.yStar S.toQiSetup v) ∧
    (∀ v : Mi, S.conj (Split.tMinus S.toQiSetup (S.conj v)) = Split.tPlus S.toQiSetup v) := by
  have hγinv : D.conj ((Split.gammaStarF D.carrier ℓ)⁻¹) = (Split.gammaStarF D.carrier ℓ)⁻¹ := by
    rw [map_inv₀, GF.conj_gammaStarF]
  have hc₀ : D.conj (((4 : D.carrier) ^ (ℓ - 1) * Split.gammaStarF D.carrier ℓ ^ 2)⁻¹)
      = ((4 : D.carrier) ^ (ℓ - 1) * Split.gammaStarF D.carrier ℓ ^ 2)⁻¹ := by
    rw [map_inv₀, map_mul, map_pow, map_pow, GF.conj_gammaStarF, GF.conj_ofNat]
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [S.conj_X', S.conj_involutive' v]
  · rw [S.conj_Y', S.conj_involutive' v]
  · show S.conj (((Split.gammaStarF D.carrier ℓ)⁻¹ • S.weight.X ^ (ℓ - 1)) (S.conj v))
        = ((Split.gammaStarF D.carrier ℓ)⁻¹ • S.weight.Y ^ (ℓ - 1)) v
    rw [LinearMap.smul_apply, LinearMap.smul_apply, S.conj_smul_fixed hγinv, conj_pow_X,
      S.conj_involutive' v]
  · show S.conj (((((4 : D.carrier) ^ (ℓ - 1) * Split.gammaStarF D.carrier ℓ ^ 2)⁻¹)
          • casimirFactorProd S.weight.casimir ((ℓ : ℤ) - 2) (ℓ - 1)) (S.conj v))
        = ((((4 : D.carrier) ^ (ℓ - 1) * Split.gammaStarF D.carrier ℓ ^ 2)⁻¹)
          • casimirFactorProd S.weight.casimir ((ℓ : ℤ) - 2) (ℓ - 1)) v
    rw [LinearMap.smul_apply, LinearMap.smul_apply, S.conj_smul_fixed hc₀,
      S.conj_casimirFactorProd, S.conj_involutive' v]

/-- **`RQ-5.03`** (`eq:conjugatenormalizedcomparison`) — the conjugate comparison diagram.

For `ℓ ≥ 1` and a `ℚ[√-1]`-rational Harish-Chandra module that descends to `ℚ` (`H1`), complex
conjugation transforms `eq:normalizedcomparison` into the diagram whose two rows are unchanged, whose
verticals point **upward** and are `𝟏_{M_{-(ℓ+1)}}`, `Y⋆ : M_{ℓ-1} → M_{-(ℓ-1)}` and
`T₊ : M_{ℓ+1} → M_{ℓ+1}` (`C3`), and all four of whose squares commute (`C2`).

The four conjuncts below are the four squares, in the source's own order: front-left and front-right
(the right-facing horizontal arrows), then back-left and back-right (the left-facing arrows). Each is
stated on the weight component its bottom-left corner names, since the verticals point upward.

@census    RQ2-5.03
@source    eq:conjugatenormalizedcomparison
@clauses   RQ2-5.03-H1, RQ2-5.03-H2, RQ2-5.03-C1, RQ2-5.03-C2, RQ2-5.03-C3, RQ2-5.03-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation, `R-V2-3`).  `H1`/`H2` (`M_{L_E} = L_E ⊗_E M_E`,
`√-1 ∉ E`): the statement is over the engine datum `S : RationalSetupOver` (the base change with `c`),
which an object of `HC ℓ E D` with `√-1 ∉ E` provides through the bridge `HC.setup` (`conj := galAct c`);
for `√-1 ∈ E` there is nothing to show (plan §4.3, Step O-8 vacuous).  `C1` is `conj_normalized_operators`
(same module).  Census clause `RQ2-5.03-C4` (v1 `RQ-5.03-C4`) records that the source offers a **second route** to `C2`:
"whose commutativity can also be verified directly", i.e. independently of the conjugation argument
of `C1`. Only one route is rendered — the conjugation one, which is the argument the source actually
writes and the one §5.2 goes on to use. `C4` is therefore cited as a `JUSTIFIED_REFORMULATION` in the
census's own sense (its `if_missing` cell reads `JUSTIFIED_REFORMULATION`, `notes`: "an alternative
proof route"): the *claim* of `C4` is that the direct verification exists, and what is rendered is
the claim `C2` that both routes establish. No conclusion of the source is dropped; a redundant proof
route is. Separately: stated for a bare `RationalSetup`, not `Gelfand.HCQObj` (`RQ-5.05`'s own
category, admissibility/fg/central-character) — a **true generalization** (`CONVENTIONS.md` §3),
since the proof uses none of the three extra conditions (2026-09-03, `R-S8-16`(c), `V-S8-D1-4`(b)). -/
theorem conjugate_diagram_commutes (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup)
    (hℓ : 1 ≤ ℓ) :
    -- front-left: `Y⋆ ∘ (Y⋆⁻¹ ∘ X) = X ∘ 𝟏`, on `M_{-(ℓ+1)}`
    (∀ v ∈ S.weight.comp (-((ℓ : ℤ) + 1)),
        Split.yStar S.toQiSetup (I.yStarInv (S.weight.X v)) = S.weight.X v) ∧
    -- front-right: `T₊ ∘ X = (X ∘ X⋆) ∘ Y⋆`, on `M_{ℓ-1}`
    (∀ v ∈ S.weight.comp ((ℓ : ℤ) - 1),
        Split.tPlus S.toQiSetup (S.weight.X v)
          = S.weight.X (Split.xStar S.toQiSetup (Split.yStar S.toQiSetup v))) ∧
    -- back-left: `Y ∘ Y⋆ = 𝟏 ∘ (Y ∘ Y⋆)`, on `M_{ℓ-1}`
    (∀ v ∈ S.weight.comp ((ℓ : ℤ) - 1),
        S.weight.Y (Split.yStar S.toQiSetup v) = (S.weight.Y.comp (Split.yStar S.toQiSetup)) v) ∧
    -- back-right: `(X⋆⁻¹ ∘ Y) ∘ T₊ = Y⋆ ∘ Y`, on `M_{ℓ+1}`
    (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1),
        I.xStarInv (S.weight.Y (Split.tPlus S.toQiSetup v))
          = Split.yStar S.toQiSetup (S.weight.Y v)) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v _ => rfl, fun v hv => ?_⟩
  · -- front-left, on `M_{-(ℓ+1)}`: `Y⋆ ∘ (Y⋆⁻¹ ∘ X) = X`, i.e. `Y⋆⁻¹` is a right inverse of `Y⋆`
    exact Split.yStar_yStarInv S.toQiSetup I _
      (Split.x_mem (Q := S.toQiSetup) (m := -((ℓ : ℤ) + 1)) (by ring) hv)
  · -- front-right, on `M_{ℓ-1}`: `T₊ ∘ X = X ∘ (X⋆ ∘ Y⋆)`
    rw [Split.xStar_yStar_apply S.toQiSetup hℓ v hv, Split.tPlus_eq_tMinus]
    exact Split.tMinus_X_apply S.toQiSetup v
  · -- back-right, on `M_{ℓ+1}`: `X⋆⁻¹ ∘ Y ∘ T₊ = Y⋆ ∘ Y`
    have hYv : S.weight.Y v ∈ S.toQiSetup.comp ((ℓ : ℤ) - 1) :=
      Split.y_mem (Q := S.toQiSetup) (m := (ℓ : ℤ) + 1) (by ring) hv
    have h1 : Split.xStar S.toQiSetup (Split.yStar S.toQiSetup (S.weight.Y v))
        = Split.tMinus S.toQiSetup (S.weight.Y v) := Split.xStar_yStar_apply S.toQiSetup hℓ _ hYv
    have hys : Split.yStar S.toQiSetup (S.weight.Y v) ∈ S.toQiSetup.comp (-((ℓ : ℤ) - 1)) :=
      Split.yStar_mem (Q := S.toQiSetup) (m := (ℓ : ℤ) - 1) (by ring) hℓ hYv
    have h2 : S.weight.Y (Split.tMinus S.toQiSetup v) = Split.tMinus S.toQiSetup (S.weight.Y v) :=
      (Split.tMinus_Y_apply S.toQiSetup v).symm
    rw [Split.tPlus_eq_tMinus, h2, ← h1, Split.xStarInv_xStar S.toQiSetup I _ hys]


end RationalQuivers.Gelfand.RationalStructure
