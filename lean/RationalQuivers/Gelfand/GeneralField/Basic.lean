import RationalQuivers.Gelfand.GeneralBaseCategory
import RationalQuivers.Gelfand.Split.Construction

/-!
# `rmk:generalbases` over an arbitrary field — vocabulary of the field-generic proof (WP-8c)

Final-release work package **WP-8c** (author decision 2026-10-02 on `FA-07`, design note
`workflow/analysis/GENERAL-E-DESIGN-2026-10-02.md` §2).  The tree's proof of
`thm:EEQQequivalence` / `thm:cyclicEEQQequivalence` (S8) is written over the *type* `ℚ[√-1] ⊆ ℂ`
and over `ℚ`; its mathematics is field-generic.  The v1 modules under `Gelfand/GeneralField/` (none
but this one is still there, note below) re-ran that proof with the base field abstracted: a
characteristic-zero field `F` in the split case, and a characteristic-zero field `E` with a chosen
quadratic Galois extension `D : SqrtNegOneExt E` in the non-split case.  **No frozen declaration is
edited.**  This module's declarations live in the namespace `RationalQuivers.Gelfand.GF`, except
`HCEObj.toF` (in `RationalQuivers.Gelfand`) and the `RationalSetupOver.*` lemmas (in
`RationalQuivers.Gelfand.RationalSetupOver`), which sit in the namespaces of the structures they
extend.

This module supplies the vocabulary the copies need:

* `HCEObj.toF`, `baseChangeE` — the forgetful functor `HCEObj ℓ E D ⥤ HCF D.carrier ℓ`
  (the analogue of S8's `baseChangeQ`), with the G5 inhabitants `trivialHCFObj`, `trivialHCFHom`;
* `conj_ofNat`, …, `conj_nilpScalar` — `D.conj` on scalars; `RationalSetupOver.conj_smul_fixed`,
  `conj_casimir`, `conj_casimirFactorProd` — the Galois equivariance of the Casimir operator for
  S10's `RationalSetupOver` (`Gelfand/GeneralBaseCategory.lean`), the counterpart of
  `HC/Normalization.lean`'s `galAct_casimir`, `galAct_casimirFactorProd` on `HC ℓ E D`;
* `zeta`, `conj_zeta`, `zeta_ne_zero` — a Galois-anti-invariant unit of `D'` (last section).

`HCFObj F ℓ` / `HCF F ℓ` (v1's `HCQiObj ℓ` / `HCQi ℓ` with `ℚ[√-1]` replaced by `F`), the comparison
`hcLambdaFEquiv : HCLambda ℓ F ≌ HCF F ℓ` (a copy of v1's `hcLambdaQiEquiv`) and `gammaStarF`,
`bijOn_scalar_add_nilpotent`, … (copies of `HC/Normalization.lean`'s `WeightData.gammaStar`,
`WeightData.bijOn_scalar_add_nilpotent`, …, which are generic over a field `F` already) are not in
this module: they are `Gelfand.Split.*`, in `Gelfand/Split/Construction.lean`.  The v1 declarations
`HCQObj.toQi`, `baseChangeQ`, `HCQiObj`, `HCQi` and `hcLambdaQiEquiv` named in this module were
deleted at WP-13 (`9c6b193`); S10's `trivialHCEObj`, `trivialHCEHom` and `RationalSetupOver` are in
`Gelfand/GeneralBaseCategory.lean`.  *(2026-10-21, T2-a5, V-OV2-4, V-OV2-5.)*

*(v2 WP-13, 2026-10-18: module kept in place and assigned to stage T5 by WP-13 option I (stage T2 since
the perimeter amendment T2-a1, next note); the other
`Gelfand/GeneralField/` modules still in the tree and the import of the deleted v1
`Gelfand/QNormalization.lean` were removed.
Its declarations are unchanged; frozen T3 `RationalStructure/Conjugate` imports it.)*
*(2026-10-21, O-V2-6, V-OV2R2-6.)*  Of the 22 v1 modules under `Gelfand/GeneralField/`, five
(`Conjugate`, `Normalization`, `Stabilization`, `Equivalence`, `Cyclic`) were removed at WP-10
(`adb2821`, the switch-over to stage T3's modules); ten (`BaseChange`, `BaseChangeCyclic`,
`BaseChangeHom`, `BaseChangeHomNN`, `BaseChangeMain`, `BaseChangeMixed`, `BaseChangeNN`,
`BaseChangeNNHC`, `BaseChangeNNRep`, `BaseChangeNNStab`) were relocated to `Gelfand/BaseChange/` at
WP-11 (`c64b17b`, stage T4); six (`IdentificationQuiver`, `IdentificationRelation`,
`IdentificationRing`, `IdentificationSpecies`, `Main`, `Species`) were deleted at WP-13 (`44df340`);
this module is the twenty-second.
*(WP-15, 2026-10-19, G2-V2II-F05: the module belongs to stage T2 since the perimeter amendment T2-a1
(`STAGE-MAP.tsv`); since T2-a2, `D : SqrtNegOneExt E` is any quadratic Galois extension `D'/E`, and
`E(√-1)` in the docstrings below means `D'`.)*
-/

namespace RationalQuivers.Gelfand.GF

open RationalQuivers.HC RationalQuivers.Gelfand CategoryTheory


/-! ## Forgetting the descent datum: `HCEObj ℓ E D ⥤ HCF D.carrier ℓ` -/

section Forget

variable {ℓ : ℕ} {E : Type} [Field E] [CharZero E] {D : SqrtNegOneExt E}

/-- `M_E ↦ M_{D'}`, `D'` the carrier of `D`: the analogue of S8's `HCQObj.toQi`.  @census none (helper; WP-8c) -/
@[reducible] noncomputable def _root_.RationalQuivers.Gelfand.HCEObj.toF (A : HCEObj ℓ E D) :
    Split.HCFObj D.carrier ℓ where
  carrier := A.carrier
  weight := A.setup.weight
  gic := A.setup.gic
  admissible := A.admissible
  centralCharacter := A.centralCharacter
  fg := A.fg

variable (ℓ E D) in
/-- The base-change functor `HC_λ(𝔤,K_{D'/E})_E → HC_λ(𝔤,K)_{D'}` on the concrete categories (the
analogue of S8's `baseChangeQ`).  @census none (helper; WP-8c) -/
noncomputable def baseChangeE : HCEObj ℓ E D ⥤ Split.HCF D.carrier ℓ where
  obj A := A.toF
  map f := ⟨f.toLinearMap, f.map_H, f.map_X, f.map_Y, f.map_comp⟩
  map_id _ := by apply Split.HCFHom.hom_ext; rfl
  map_comp _ _ := by apply Split.HCFHom.hom_ext; rfl

variable (E D) in
/-- **G5 inhabitant of `HCFObj`**: `trivialHCEObj E D` (S10's non-zero `ℓ = 1` object) with its
descent datum forgotten.  Non-degenerate: its carrier `D.carrier` is nontrivial.  *(Added 2026-10-03,
`R-PROC-4` amendment of `S10`, final-release WP-9.)*  @census none (G5 inhabitant) -/
noncomputable def trivialHCFObj : Split.HCFObj D.carrier 1 := (trivialHCEObj E D).toF

variable (E D) in
/-- **G5 inhabitant of `HCFHom`**: the identity of `trivialHCFObj` (the analogue of S10's
`trivialHCEHom`).  *(Added 2026-10-03, `R-PROC-4` amendment of `S10`, final-release WP-9:
`rqaudit models` reported `HCFHom` `MODEL-MISSING`.)*  @census none (G5 inhabitant) -/
noncomputable def trivialHCFHom : Split.HCFHom (trivialHCFObj E D) (trivialHCFObj E D) :=
  ⟨LinearMap.id, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ h => h⟩

/-- The same witness at `E = ℚ`, `D = ℚ[√-1]`: no explicit binder.  @census none (G5 inhabitant) -/
noncomputable def trivialHCFHom_qi :
    Split.HCFHom (trivialHCFObj ℚ SqrtNegOneExt.qi) (trivialHCFObj ℚ SqrtNegOneExt.qi) :=
  trivialHCFHom ℚ SqrtNegOneExt.qi

end Forget


/-! ## The Galois-equivariance lemmas for `RationalSetupOver` -/

section SetupOver

variable {ℓ : ℕ} {E : Type} [Field E] [CharZero E] {D : SqrtNegOneExt E}
  {Mq : Type} [AddCommGroup Mq] [Module E Mq]
  {Mi : Type} [AddCommGroup Mi] [Module D.carrier Mi]

theorem conj_ofNat (n : ℕ) [n.AtLeastTwo] :
    D.conj (OfNat.ofNat n : D.carrier) = OfNat.ofNat n := map_ofNat D.conj n

theorem conj_intCast (a : ℤ) : D.conj ((a : ℤ) : D.carrier) = (a : D.carrier) :=
  map_intCast D.conj a

theorem conj_natCast (a : ℕ) : D.conj ((a : ℕ) : D.carrier) = (a : D.carrier) :=
  map_natCast D.conj a

theorem conj_gammaStarF (ℓ : ℕ) : D.conj (Split.gammaStarF D.carrier ℓ) = Split.gammaStarF D.carrier ℓ :=
  map_natCast D.conj _

theorem conj_mul_self : D.conj * D.conj = 1 := by
  ext a; exact D.conj_conj a

theorem conj_nilpScalar (ℓ : ℕ) (k : ℤ) (m : ℕ) :
    D.conj (nilpScalar ℓ k m D.carrier) = nilpScalar ℓ k m D.carrier := by
  induction m generalizing k with
  | zero => rw [nilpScalar_zero]; simp
  | succ m ih =>
    rw [nilpScalar_succ, map_mul, map_sub, map_pow, map_pow, map_natCast, conj_intCast, ih]

end SetupOver

end RationalQuivers.Gelfand.GF

namespace RationalQuivers.Gelfand.RationalSetupOver

open RationalQuivers.HC RationalQuivers.Gelfand.GF

variable {ℓ : ℕ} {E : Type} [Field E] [CharZero E] {D : SqrtNegOneExt E}
  {Mq : Type} [AddCommGroup Mq] [Module E Mq]
  {Mi : Type} [AddCommGroup Mi] [Module D.carrier Mi]

variable (S : RationalSetupOver ℓ E D Mq Mi)

theorem conj_smul_fixed {a : D.carrier} (ha : D.conj a = a) (v : Mi) :
    S.conj (a • v) = a • S.conj v := by
  rw [S.conj_smul, ha]

theorem conj_casimir (v : Mi) :
    S.conj (S.weight.casimir v) = S.weight.casimir (S.conj v) := by
  have hH1 : S.conj (S.weight.H v) = -S.weight.H (S.conj v) := S.conj_H v
  have hH2 : S.conj (S.weight.H (S.weight.H v)) = S.weight.H (S.weight.H (S.conj v)) := by
    rw [S.conj_H, hH1, map_neg, neg_neg]
  have hXY : S.conj (S.weight.X (S.weight.Y v)) = S.weight.Y (S.weight.X (S.conj v)) := by
    rw [S.conj_X, S.conj_Y]
  rw [S.weight.casimir_apply v, map_add, map_add, map_sub, hH2,
    S.conj_smul_fixed (conj_ofNat 2), S.conj_smul_fixed (conj_ofNat 4), hH1, hXY,
    S.weight.casimir_apply (S.conj v), S.weight.Y_X_apply (S.conj v)]
  module

theorem conj_casimirFactorProd (k : ℤ) (m : ℕ) (v : Mi) :
    S.conj (casimirFactorProd S.weight.casimir k m v)
      = casimirFactorProd S.weight.casimir k m (S.conj v) := by
  induction m generalizing k v with
  | zero => rw [casimirFactorProd_zero]; rfl
  | succ m ih =>
    rw [casimirFactorProd_succ, Module.End.mul_apply, Module.End.mul_apply, LinearMap.sub_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply,
      Module.End.one_apply, map_sub, S.conj_casimir,
      S.conj_smul_fixed (by rw [map_pow, conj_intCast]), ih]

end RationalQuivers.Gelfand.RationalSetupOver

namespace RationalQuivers.Gelfand.GF

open RationalQuivers.HC RationalQuivers.Gelfand CategoryTheory

/-! ## A Galois-anti-invariant unit: the replacement for `√-1` in engine `E5`

The `ℚ` proof uses `√-1 ∈ ℚ[√-1]` only through `c(√-1) = -√-1 ≠ 0` (engine `E5`, now
`Gelfand/Equivalence/Full.lean`, which takes any `ζ` with `c(ζ) = -ζ ≠ 0` as an argument).  In any
quadratic Galois `D.carrier / E` such an element exists: `a - c(a)` for any `a` not fixed by `c`. -/

section Zeta

variable {E : Type} [Field E] [CharZero E] (D : SqrtNegOneExt E)

theorem exists_conj_ne : ∃ a : D.carrier, D.conj a ≠ a := by
  by_contra h
  push Not at h
  exact D.conj_ne_one (AlgEquiv.ext h)

/-- A non-zero `ζ ∈ D'` with `c(ζ) = -ζ`: `ζ := a - c(a)` for some `a ∈ D' \ E`
(`thm:twistedEEequivalence`, last paragraph of the proof).  @census none (helper; WP-8c)
@clauses   RQ2-5.24-S-TW3 -/
noncomputable def zeta : D.carrier :=
  (exists_conj_ne D).choose - D.conj (exists_conj_ne D).choose

theorem conj_zeta : D.conj (zeta D) = -zeta D := by
  unfold zeta
  rw [map_sub, D.conj_conj]; ring

theorem zeta_ne_zero : zeta D ≠ 0 := by
  unfold zeta
  intro h
  exact (exists_conj_ne D).choose_spec (sub_eq_zero.mp h).symm

end Zeta

end RationalQuivers.Gelfand.GF
