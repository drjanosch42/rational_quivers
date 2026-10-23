import RationalQuivers.Gelfand.Cyclic.EssSurj
import RationalQuivers.HC.Abelian
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Preadditive.Transfer

/-!
# `thm:EEequivalence`, `thm:cyclicEEequivalence`, Theorem B (§5.3, stage T3)

The `E`-rational categorical equivalence over **every** field `E` of characteristic `0`
(plan rev 3a §3.4, D-1):

  `𝔼_E : HC_λ(𝔤,K)_E ≃ Rep^nil(Γ_E)`,

with `HC_λ(𝔤,K)_E = HC ℓ E D` (`def:HClambdaE`, the descent presentation, `EX-HC`), `Γ_E = GammaE D ℓ`
(`def:GammaE`) and `Rep^nil(Γ_E) = RepNilTarget D ℓ` (with the relation `a₋b₋ = a₊b₊` for `ℓ ≥ 1`).

`𝔼_E` is built exactly as in the tex: `𝔼_{L_E}` of the base change `M_{L_E} = L_E ⊗_E M_E`
together with `φ_{•,σ}` by **dispatch on `χ_E(σ)`** (plan §7, A-4) — `φ_{•,1} = 1`, and for
`χ_E(σ) = -1` (i.e. `σ = c`, `√-1 ∉ E`) the semi-linear maps `c ∘ φ^{(∞)}_•` of `eq:varphiplus`,
`eq:varphiminus`, `eq:varphistar` (`ℓ ≥ 1`, `RationalStructure.E_E_φ`) resp. `c` itself
(`eq:varphicyclic`, `ℓ = 0`, `Cyclic.E_Cyc_φ`).  It is defined by recursion on `ℓ`, like `Γ_E`.

The proofs follow the author's proof of `thm:EEQQequivalence`/`thm:cyclicEEQQequivalence` step by step
(`workflow/v2/census/PROOF-ROUTE.tsv`): well-definedness (Step O-14, `Equivalence.E_E_rep`),
functoriality (O-15, `Equivalence.E_EGel`), faithfulness (O-16, `Equivalence.E_E_faithful`), fullness
by the `ζ`-argument (O-17, `Equivalence.E_E_full`), essential surjectivity (O-18 … O-24,
`EssSurj.E_E_essSurj`; for `√-1 ∈ E` the split construction of tex §5.1, Step O-7h); at `ℓ = 0` the
Steps C-1 … C-7 (`Cyclic.*`).  When `√-1 ∈ E` (`G_E = 1`) every step marked "vacuous" in the plan has
nothing to show and the theorem is the equivalence over `E = L_E` itself.

The non-split steps run the relocated engine through the `R-V2-3` bridges
(`RationalStructure/Bridge.lean`): an identification of presentations, disclosed in the T3 packet.

The acceptance commands of plan §3.4 (D-1, A-28, A-29, A-32): `E = ℝ` (`ImagUnit.real`, `L_ℝ = ℂ`,
`√-1 ∉ ℝ`) and `E = ℂ` (`ImagUnit.complex`, split) are instances — the two `example`s at the end.
The named claimants of the `ℝ`/`ℂ` sentence (`rmk:classicalcases`, `RQ2-5.19`) are T4's (OQ-14).
-/

namespace RationalQuivers.Gelfand

open RationalQuivers.HC CategoryTheory

variable {E : Type} [Field E] [CharZero E] {D : ImagUnit E} {ℓ : ℕ}

/-- The equivalence for `ℓ ≥ 1`, stated on the Gelfand target `RepNilGel D` (= `RepNilTarget D ℓ`
for `ℓ ≥ 1`): faithful (O-16), full (O-17), essentially surjective (O-18 … O-24).
@census none (helper) -/
theorem gelfand_equivalence_gel (hℓ : 1 ≤ ℓ) :
    ∃ e : HC ℓ E D ≌ (Equivalence.RepNilGel D).FullSubcategory, e.functor = Equivalence.E_EGel hℓ := by
  haveI := Equivalence.E_E_faithful (D := D) hℓ
  haveI := Equivalence.E_E_full (D := D) hℓ
  haveI := EssSurj.E_E_essSurj (D := D) hℓ
  haveI : (Equivalence.E_EGel (D := D) hℓ).IsEquivalence := { }
  exact ⟨(Equivalence.E_EGel hℓ).asEquivalence, rfl⟩


/-- **`RQ2-5.12-C3`, second half**: the `L_E`-representation underlying `𝔼_E(M_E)` is
`𝔼_{L_E}(M_{L_E})` — the same vertex spaces and the same edge maps as T2's split functor
`Split.E_F_rep` at `M_{L_E}` (by construction, `rfl`).  @census none (helper; `RQ2-5.12-C3`) -/
theorem E_E_underlying_split (hℓ : 1 ≤ ℓ) (A : HC ℓ E D) :
    (Equivalence.E_E_rep hℓ A).M = (Split.E_F_rep A.qi (A.qi.starInverses hℓ) hℓ).M ∧
      ∀ e : Fin 4, HEq ((Equivalence.E_E_rep hℓ A).φEdge e)
        ((Split.E_F_rep A.qi (A.qi.starInverses hℓ) hℓ).φEdge e) :=
  ⟨rfl, fun _ => HEq.rfl⟩

variable (E D) in
/-- **`𝔼_E`**, the functor of `thm:EEequivalence` (`ℓ ≥ 1`) and `thm:cyclicEEequivalence`
(`ℓ = 0`): `M_E ↦ (𝔼_{L_E}(M_{L_E}), φ_•)`, by recursion on `ℓ` like `Γ_E` (`GammaE`).
@census none (auxiliary; the functor `E_E` of `RQ2-5.12`, `RQ2-5.13`, `RQ2-0.02`) -/
noncomputable def E_E : (ℓ : ℕ) → HC ℓ E D ⥤ (RepNilTarget D ℓ).FullSubcategory
  | 0 => Cyclic.E_ECyc
  | k + 1 => Equivalence.E_EGel (ℓ := k + 1) (by omega)

/-- **Theorem** (`thm:EEequivalence`).  Let `E` be a field of characteristic `0` and `ℓ ≥ 1`.  The
assignment `𝔼_E : M_E ↦ (𝔼_{L_E}(M_{L_E}), φ_•)` from `HC_λ(𝔤,K)_E` to `Rep^nil(Γ_E)` is
well-defined and an equivalence of categories; here `φ_{•,1} = 1` and, if `√-1 ∉ E`, `φ_{•,c}` is
given by `eq:varphiplus`, `eq:varphiminus`, `eq:varphistar`.

@census    RQ2-5.12
@source    thm:EEequivalence
@clauses   RQ2-5.12-H1, RQ2-5.12-H2, RQ2-5.12-H3, RQ2-5.12-C1, RQ2-5.12-C2, RQ2-5.12-C3,
  RQ2-5.12-C4,
  RQ2-5.12-S-O13
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation): `HC_λ(𝔤,K)_E` is `HC ℓ E D`, the descent
presentation of `def:HClambdaE` (`EX-HC`); `C3`'s "the `L_E`-representation underlying `𝔼_E(M_E)`
is `𝔼_{L_E}(M_{L_E})`" holds by construction: `E_E_underlying_split` (same module).  For `√-1 ∉ E` the non-split steps are run through the `R-V2-3`
bridges (identification of presentations).  The equivalence is stated as `∃ e, e.functor = E_E E D ℓ`
(the functor is the tex's, not merely some equivalence).
-/
theorem gelfand_equivalence_pos (hℓ : 1 ≤ ℓ) :
    ∃ e : HC ℓ E D ≌ (RepNilTarget D ℓ).FullSubcategory, e.functor = E_E E D ℓ := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  exact gelfand_equivalence_gel (D := D) (ℓ := k + 1) (by omega)

/-- **Theorem** (`thm:cyclicEEequivalence`).  Let `E` be a field of characteristic `0` and `ℓ = 0`.
The assignment `𝔼_E : M_E ↦ (𝔼_{L_E}(M_{L_E}), φ_•)` from `HC_0(𝔤,K)_E` to `Rep^nil(Γ_E)`, `Γ_E` the
`E`-rational cyclic quiver, is well-defined and an equivalence of categories; `φ_{•,1} = 1` and, if
`√-1 ∉ E`, `φ_{±,c} := c` (`eq:varphicyclic`): no unipotent stabilization is involved.

@census    RQ2-5.13
@source    thm:cyclicEEequivalence
@clauses   RQ2-5.13-H1, RQ2-5.13-H2, RQ2-5.13-H3, RQ2-5.13-C1, RQ2-5.13-C2, RQ2-5.13-C3,
  RQ2-5.13-C4, RQ2-5.13-C5,
  RQ2-5.13-S-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation): `HC_0(𝔤,K)_E` is `HC 0 E D` (descent
presentation, `EX-HC`); `φ_{•,σ}` is `galAct σ` (`Cyclic.E_Cyc_φ`), which is `1` for `σ = 1` and `c`
for `σ = c`.
-/
theorem gelfand_equivalence_zero :
    ∃ e : HC 0 E D ≌ (RepNilTarget D 0).FullSubcategory, e.functor = E_E E D 0 := by
  haveI := Cyclic.E_ECyc_faithful (D := D)
  haveI := Cyclic.E_Cyc_full (D := D)
  haveI := Cyclic.cycEssSurj (D := D)
  haveI : (Cyclic.E_ECyc (D := D)).IsEquivalence := { }
  exact ⟨(Cyclic.E_ECyc (D := D)).asEquivalence, rfl⟩

/-- **Theorem B** (`thm:introB`).  Let `E` be a field of characteristic `0`, `ℓ ≥ 0` and `λ = ℓ²`.
The functor `𝔼_E` defines an equivalence `HC_λ(𝔰𝔩₂, SO(2))_E ≃ Rep^nil(Γ_E)`, where `Γ_E` is the
`E`-rational Gelfand quiver if `ℓ ≥ 1` and the `E`-rational cyclic quiver if `ℓ = 0`
(`def:GammaE`).  `|G_E| ∈ {1, 2}`; if `√-1 ∈ E` the rational structure is trivial and the statement
is the equivalence over `E` itself.

@census    RQ2-0.02
@source    thm:introB
@clauses   RQ2-0.02-H1, RQ2-0.02-H2, RQ2-0.02-C1, RQ2-0.02-C2, RQ2-0.02-C3
@imports   none
@divergence JUSTIFIED_REFORMULATION.  `C3` ("equivalence of **abelian** categories"): both sides are
abelian — `HC.HC.abelian` (in `HC/Abelian.lean`, author decision T1-A (a)) and `repNilTarget_abelian` (in
this module, `Gelfand/Main.lean`: the abelian structure of `Rep^nil(Γ_E)` transported along `𝔼_E`, with
`e.inverse` additive); this theorem states the equivalence, `repNilTarget_abelian` the abelian structures.
The transported structure is the intended one because an additive structure is unique when it exists
(hom-group addition is determined by biproducts); the tree has no native `Preadditive` instance on
`Rep^nil(Γ_E)` to compare it with componentwise addition of the `ψ_v`, so that agreement is a
meta-argument, disclosed here.  `C1`, `C2`: the uniform statement over all `ℓ`, combining
`gelfand_equivalence_pos` (`ℓ ≥ 1`) and `gelfand_equivalence_zero` (`ℓ = 0`) by a case split on `ℓ`
inside the proof; `HC_λ(𝔤,K)_E` in the descent presentation (`EX-HC`).
-/
theorem gelfand_equivalence (E : Type) [Field E] [CharZero E] (D : ImagUnit E) (ℓ : ℕ) :
    ∃ e : HC ℓ E D ≌ (RepNilTarget D ℓ).FullSubcategory, e.functor = E_E E D ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with h | h
  · subst h; exact gelfand_equivalence_zero
  · exact gelfand_equivalence_pos h


/-! ### Both sides abelian (`thm:introB`, clause `C3`; AUTHOR-QUEUE T1-A (a)) -/

/-- **`Rep^nil(Γ_E)` is abelian**, by transport along the equivalence `𝔼_E` from `HC_λ(𝔤,K)_E`, which
is abelian (`HC.HC.abelian`, `HC/Abelian.lean`, author decision T1-A (a), 2026-10-17): the preadditive
structure is pulled back along the fully faithful `e.inverse` (`Preadditive.ofFullyFaithful`), finite
limits along the equivalence, and `abelianOfEquivalence` gives the rest; `e.inverse` is additive for
it.  @census none (auxiliary; discharges `RQ2-0.02-C3` for the representation side) -/
theorem repNilTarget_abelian (E : Type) [Field E] [CharZero E] (D : ImagUnit E) (ℓ : ℕ) :
    ∃ e : HC ℓ E D ≌ (RepNilTarget D ℓ).FullSubcategory, e.functor = E_E E D ℓ ∧
      ∃ A : Abelian (RepNilTarget D ℓ).FullSubcategory,
        @Functor.Additive _ _ _ _ A.toPreadditive HC.HC.abelianStr.toPreadditive e.inverse := by
  obtain ⟨e, he⟩ := gelfand_equivalence E D ℓ
  letI : Abelian (HC ℓ E D) := HC.HC.abelianStr
  letI : Preadditive (RepNilTarget D ℓ).FullSubcategory :=
    Preadditive.ofFullyFaithful e.symm.fullyFaithfulFunctor
  haveI : Limits.HasFiniteLimits (RepNilTarget D ℓ).FullSubcategory :=
    ⟨fun _ _ _ => Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  haveI : e.inverse.Additive := e.symm.fullyFaithfulFunctor.additive_ofFullyFaithful
  exact ⟨e, he, abelianOfEquivalence e.inverse, inferInstance⟩

/-! ### Acceptance commands (D-1): `E = ℝ` and `E = ℂ` -/

/-- `E = ℝ`: `L_ℝ = ℂ`, `√-1 ∉ ℝ`, `Γ_ℝ` non-split — the real form of Gelfand's equivalence. -/
example (ℓ : ℕ) := gelfand_equivalence ℝ ImagUnit.real ℓ

/-- `E = ℂ`: `L_ℂ = ℂ`, `Γ_ℂ` split — Gelfand's equivalence reproved. -/
example (ℓ : ℕ) := gelfand_equivalence ℂ ImagUnit.complex ℓ

end RationalQuivers.Gelfand
