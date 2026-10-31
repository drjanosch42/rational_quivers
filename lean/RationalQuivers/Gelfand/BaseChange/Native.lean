module

public import RationalQuivers.Gelfand.BaseChange.Main
public import RationalQuivers.Gelfand.BaseChange.HomNN
public import RationalQuivers.Gelfand.Compat

@[expose] public section

/-!
# `prop:basechange` on `HC_λ(𝔤,K)_E` and `𝔼_E` (tex §5.5, stage T4)

`prop:basechange` (census `RQ2-5.14`): `𝔼_E` is compatible with base change.  The relocated v1
modules (`Gelfand/BaseChange/{Split, …, Main}`) prove it on the engine's presentations (`HCEObj`,
`HCLambda`/`HCF`, `Rep^nil(gelfandOfCardTwo)`, `Rep^nil(gelfandSplit)`); this module states it on the
v2 presentations `HC ℓ E D` and `Rep^nil(Γ_E)` with the native functor `𝔼_E` of stage T3, and proves
it by transport along the `WP-11a` identifications (`Gelfand/Compat.lean`: `hcEquivHCEObj`,
`HC.lambdaEquiv`/`ofLambdaFunctor`, `targetEquivCardTwo(Z)`, `targetEquivSplit(Z)`, `engineNative(Z)`,
`splitNative(Z)`), all with identity components (ruling `R-V2-3` §1.1: identifications of
presentations).

* (T1) `bcIsoSS(Z)`, `bcIsoNN(Z)`, `bcIsoMx(Z)`: `E'' ⊗_E 𝔼_E(M_E) ≅ 𝔼_{E''}(E'' ⊗_E M_E)` naturally, in
  the three cases (a) `√-1 ∈ E`, (b) `√-1 ∉ E''`, (c) `√-1 ∉ E`, `√-1 ∈ E''`, for `ℓ ≥ 1` and `ℓ = 0`;
  the HC-side base change `bcHC…` and the quiver-side base change `bcQ…` are the relocated
  constructions read in the v2 presentations.  `bcIsoNN_app_ψ`: the components are the canonical
  weight-space maps.
* (T2), quiver side: `homBC_split`, `homBC_nn`, `homBC_nnZ` (the last new: v1 had the Gelfand quiver
  only); HC side (new, C9): `homBC_HC_*`.

@census none (module; claimant of `RQ2-5.14` below)
-/

namespace RationalQuivers.Gelfand.BaseChange

open RationalQuivers.HC CategoryTheory

section NN

variable {E : Type} [Field E] [CharZero E] {D : ImagUnit E}
variable {E'' : Type} [Field E''] [CharZero E''] {D'' : ImagUnit E''}
variable [Algebra E E''] [Algebra D.L D''.L] [Algebra E D''.L]
  [IsScalarTower E E'' D''.L] [IsScalarTower E D.L D''.L]
variable (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) (hc'' : ∃ σ : D''.L ≃ₐ[E''] D''.L, D''.chi σ = -1)

/-- `ι ∘ c = c'' ∘ ι`.  @census none (helper) -/
theorem conjCompatE : ConjCompat (D.sqrtExt hc) (D''.sqrtExt hc'') := by
  haveI : NoSqrtNegOne E'' := ⟨fun b hb => (D''.exists_chi_neg_one_iff.mp hc'') ⟨b, hb⟩⟩
  exact conjCompat_of_noSqrtNegOne _ _ D.i D.i_mul_i

/-- HC-side base change, non-split → non-split.  @census none (helper) -/
noncomputable def bcHCnn (ℓ : ℕ) : HC ℓ E D ⥤ HC ℓ E'' D'' :=
  Compat.toHCEObjFunctor hc ⋙ hcBaseChangeNN ℓ E (D.sqrtExt hc) E'' (D''.sqrtExt hc'') (conjCompatE hc hc'') ⋙
    Compat.ofHCEObjFunctor hc''

/-- Quiver-side base change, non-split → non-split, `ℓ ≥ 1`.  @census none (helper) -/
noncomputable def bcQnn :
    (Equivalence.RepNilGel D).FullSubcategory ⥤ (Equivalence.RepNilGel D'').FullSubcategory :=
  (Compat.targetEquivCardTwo hc).functor ⋙
    qBCnnRel (h'' := (D''.sqrtExt hc'').card_gal) (restrictionDatum (D.sqrtExt hc) (D''.sqrtExt hc'') (conjCompatE hc hc'')) ⋙
    (Compat.targetEquivCardTwo hc'').inverse

/-- T1, non-split → non-split, `ℓ ≥ 1`.  @census none (helper) -/
noncomputable def bcIsoNN {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    bcHCnn hc hc'' ℓ ⋙ Equivalence.E_EGel hℓ ≅ Equivalence.E_EGel hℓ ⋙ bcQnn hc hc'' :=
  let T'' := Compat.targetEquivCardTwo hc''
  let h₁ := Equivalence.E_Q_spec (D.sqrtExt hc).card_gal hℓ
  let h₂ := Equivalence.E_Q_spec (D''.sqrtExt hc'').card_gal hℓ
  (Functor.isoWhiskerLeft (bcHCnn hc hc'' ℓ ⋙ Equivalence.E_EGel hℓ) T''.unitIso ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc ⋙ hcBaseChangeNN ℓ E (D.sqrtExt hc) E'' (D''.sqrtExt hc'') (conjCompatE hc hc''))
      (Functor.isoWhiskerRight (Compat.engineNative hc'' hℓ h₂).symm T''.inverse) ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc)
      (Functor.isoWhiskerRight (E_bc_nn_iso ℓ E (D.sqrtExt hc) E'' (D''.sqrtExt hc'') (conjCompatE hc hc'') hℓ h₁ h₂) T''.inverse) ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc)
      (Functor.isoWhiskerRight (Compat.engineNative hc hℓ h₁)
        (qBCnnRel (h'' := (D''.sqrtExt hc'').card_gal) (restrictionDatum (D.sqrtExt hc) (D''.sqrtExt hc'') (conjCompatE hc hc'')) ⋙ T''.inverse)) ≪≫
    Functor.isoWhiskerRight (Compat.hcEquivHCEObj hc).unitIso.symm
      (Equivalence.E_EGel hℓ ⋙ bcQnn hc hc''))

set_option backward.isDefEq.respectTransparency.types false in
/-- **`RQ2-5.14-C3`**, case (b), `ℓ ≥ 1`: the component of the native isomorphism at a vertex **is**
the component of the relocated `E_bc_nn_iso`, i.e. the canonical vertex map `bcVtx`
(`L'' ⊗_{L_E} M_n → (L'' ⊗ M)_n`, `b ⊗ m ↦ b ⊗ m`): every other factor has identity components.
@census none (helper; clause `RQ2-5.14-C3`) -/
theorem bcIsoNN_app_ψ {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A : HC ℓ E D) (v : Fin 3) :
    ((bcIsoNN hc hc'' hℓ).app A).hom.hom.ψ v
      = ((E_bc_nn_iso ℓ E (D.sqrtExt hc) E'' (D''.sqrtExt hc'') (conjCompatE hc hc'') hℓ
          (Equivalence.E_Q_spec (D.sqrtExt hc).card_gal hℓ)
          (Equivalence.E_Q_spec (D''.sqrtExt hc'').card_gal hℓ)).app
            ((Compat.toHCEObjFunctor hc).obj A)).hom.hom.ψ v :=
  by
    ext x
    simp [bcIsoNN, Compat.engineNative, Compat.engineNativeApp, Compat.targetEquivCardTwo, Compat.reρSubEquiv, Compat.reρEquiv, Compat.hcEquivHCEObj, EssSurj.fdRepIsoOfComponents]
    erw [CategoryTheory.Functor.map_id]
    simp only [qBCnnRel, Rep.Hom.bcNN, Compat.reρFunctor, Compat.reρHom]
    erw [LinearMap.baseChange_id]
    rfl

/-- Quiver-side base change, non-split → non-split, `ℓ = 0`.  @census none (helper) -/
noncomputable def bcQnnZ :
    (RepNilTarget D 0).FullSubcategory ⥤ (RepNilTarget D'' 0).FullSubcategory :=
  (Compat.targetEquivCardTwoZ hc).functor ⋙
    qBCnnC (h'' := (D''.sqrtExt hc'').card_gal) (restrictionDatum (D.sqrtExt hc) (D''.sqrtExt hc'') (conjCompatE hc hc'')) ⋙
    (Compat.targetEquivCardTwoZ hc'').inverse

/-- T1, non-split → non-split, `ℓ = 0`.  @census none (helper) -/
noncomputable def bcIsoNNZ :
    bcHCnn hc hc'' 0 ⋙ Cyclic.E_ECyc ≅ Cyclic.E_ECyc ⋙ bcQnnZ hc hc'' :=
  let T'' := Compat.targetEquivCardTwoZ hc''
  let h₁ := Cyclic.E_Cyc_spec (D.sqrtExt hc).card_gal
  let h₂ := Cyclic.E_Cyc_spec (D''.sqrtExt hc'').card_gal
  (Functor.isoWhiskerLeft (bcHCnn hc hc'' 0 ⋙ Cyclic.E_ECyc) T''.unitIso ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc ⋙ hcBaseChangeNN 0 E (D.sqrtExt hc) E'' (D''.sqrtExt hc'') (conjCompatE hc hc''))
      (Functor.isoWhiskerRight (Compat.engineNativeZ hc'' h₂).symm T''.inverse) ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc)
      (Functor.isoWhiskerRight (E_bc_cyc_nn_iso E (D.sqrtExt hc) E'' (D''.sqrtExt hc'') (conjCompatE hc hc'') h₁ h₂) T''.inverse) ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc)
      (Functor.isoWhiskerRight (Compat.engineNativeZ hc h₁)
        (qBCnnC (h'' := (D''.sqrtExt hc'').card_gal) (restrictionDatum (D.sqrtExt hc) (D''.sqrtExt hc'') (conjCompatE hc hc'')) ⋙ T''.inverse)) ≪≫
    Functor.isoWhiskerRight (Compat.hcEquivHCEObj hc).unitIso.symm (Cyclic.E_ECyc ⋙ bcQnnZ hc hc''))

set_option backward.isDefEq.respectTransparency.types false in
/-- `C3` for case (b), `ℓ = 0`: the components of the (T1) isomorphism are those of the relocated v1 isomorphism,
whose components are the canonical vertex maps.  @census none (helper; clause `RQ2-5.14-C3`) -/
theorem bcIsoNNZ_app_ψ (A : HC 0 E D) (v : Fin 2) :
    ((bcIsoNNZ hc hc'').app A).hom.hom.ψ v
      = ((E_bc_cyc_nn_iso E (D.sqrtExt hc) E'' (D''.sqrtExt hc'') (conjCompatE hc hc'')
          (Cyclic.E_Cyc_spec (D.sqrtExt hc).card_gal)
          (Cyclic.E_Cyc_spec (D''.sqrtExt hc'').card_gal)).app
            ((Compat.toHCEObjFunctor hc).obj A)).hom.hom.ψ v := by
  ext x
  simp [bcIsoNNZ, Compat.engineNativeZ, Compat.engineNativeAppZ, Compat.targetEquivCardTwoZ, Compat.reρSubEquiv, Compat.reρEquiv, Compat.hcEquivHCEObj, EssSurj.fdRepIsoOfComponents]
  repeat erw [CategoryTheory.Functor.map_id]
  simp only [qBCnnC, Rep.Hom.bcNNC, Compat.reρFunctor, Compat.reρHom]
  erw [LinearMap.baseChange_id]
  rfl

end NN

/-! ## `√-1 ∈ E''`: the explicit inverse of `HC.lambdaEquiv` -/

section OfLambda

variable {E : Type} [Field E] [CharZero E] {D : ImagUnit E} {ℓ : ℕ} (h : ∃ a : E, a * a = -1)

/-- T1's `HC.ofLambda` as a functor `HCLambda ℓ L_E ⥤ HC ℓ E D` (`√-1 ∈ E`).  @census none (helper) -/
noncomputable def ofLambdaFunctor : HCLambda.{0} ℓ D.L ⥤ HC ℓ E D where
  obj B := HC.ofLambda h B
  map {B B'} g := (⟨g.hom.toLinearMap, g.hom.map_H, g.hom.map_X, g.hom.map_Y,
      fun n v hv => WeightData.map_comp_of_map_H _ _ g.hom.toLinearMap g.hom.map_H n v hv,
      fun σ v => by
        rw [D.eq_one_of_sqrt h σ]
        show g.hom.toLinearMap (galActOf D (HC.ofLambda h B).baseChange 1 v)
          = galActOf D (HC.ofLambda h B').baseChange 1 _
        rw [galActOf_one, galActOf_one]
        rfl⟩ : HC.Hom (HC.ofLambda h B) (HC.ofLambda h B'))
  map_id _ := HC.Hom.ext' rfl
  map_comp _ _ := HC.Hom.ext' rfl

/-- `toLambda ∘ ofLambda = id` (identity components).  @census none (helper) -/
noncomputable def ofLambdaToLambda : ofLambdaFunctor (ℓ := ℓ) (D := D) h ⋙ HC.toLambda D ℓ ≅ 𝟭 _ :=
  NatIso.ofComponents (fun B => Iso.refl B) (fun _ => ObjectProperty.hom_ext _ rfl)

end OfLambda

section SS

variable {E : Type} [Field E] [CharZero E] (a : E) (ha : a * a = -1)
variable {E'' : Type} [Field E''] [CharZero E''] [Algebra E E''] (a'' : E'') (ha'' : a'' * a'' = -1)

/-- HC-side base change, split → split.  @census none (helper) -/
noncomputable def bcHCss (ℓ : ℕ) : HC ℓ E (ImagUnit.ofSplit a ha) ⥤ HC ℓ E'' (ImagUnit.ofSplit a'' ha'') :=
  HC.toLambda (ImagUnit.ofSplit a ha) ℓ ⋙ hcBaseChange ℓ E E'' ⋙ ofLambdaFunctor (D := ImagUnit.ofSplit a'' ha'') ⟨a'', ha''⟩

/-- Quiver-side base change, split → split, `ℓ ≥ 1`.  @census none (helper) -/
noncomputable def bcQss :
    (Equivalence.RepNilGel (ImagUnit.ofSplit a ha)).FullSubcategory ⥤
      (Equivalence.RepNilGel (ImagUnit.ofSplit a'' ha'')).FullSubcategory :=
  (Compat.targetEquivSplit a ha).functor ⋙ qBCssRel E E'' ⋙ (Compat.targetEquivSplit a'' ha'').inverse

/-- T1, split → split, `ℓ ≥ 1`.  @census none (helper) -/
noncomputable def bcIsoSS {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    bcHCss a ha a'' ha'' ℓ ⋙ Equivalence.E_EGel hℓ ≅ Equivalence.E_EGel hℓ ⋙ bcQss a ha a'' ha'' :=
  let T'' := Compat.targetEquivSplit a'' ha''
  Functor.isoWhiskerLeft (bcHCss a ha a'' ha'' ℓ ⋙ Equivalence.E_EGel hℓ) T''.unitIso ≪≫
    Functor.isoWhiskerLeft (HC.toLambda (ImagUnit.ofSplit a ha) ℓ ⋙ hcBaseChange ℓ E E'' ⋙ ofLambdaFunctor (D := ImagUnit.ofSplit a'' ha'') ⟨a'', ha''⟩)
      (Functor.isoWhiskerRight (Compat.splitNative a'' ha'' hℓ) T''.inverse) ≪≫
    Functor.isoWhiskerLeft (HC.toLambda (ImagUnit.ofSplit a ha) ℓ ⋙ hcBaseChange ℓ E E'')
      (Functor.isoWhiskerRight (ofLambdaToLambda (D := ImagUnit.ofSplit a'' ha'') ⟨a'', ha''⟩)
        (Split.hcLambdaToF E'' ℓ ⋙ Split.E_FNil ℓ hℓ ⋙ T''.inverse)) ≪≫
    Functor.isoWhiskerLeft (HC.toLambda (ImagUnit.ofSplit a ha) ℓ)
      (Functor.isoWhiskerRight (E_bc_split_iso E E'' ℓ hℓ) T''.inverse) ≪≫
    Functor.isoWhiskerRight (Compat.splitNative a ha hℓ).symm (qBCssRel E E'' ⋙ T''.inverse)

/-- Quiver-side base change, split → split, `ℓ = 0`.  @census none (helper) -/
noncomputable def bcQssZ :
    (RepNilTarget (ImagUnit.ofSplit a ha) 0).FullSubcategory ⥤
      (RepNilTarget (ImagUnit.ofSplit a'' ha'') 0).FullSubcategory :=
  (Compat.targetEquivSplitZ a ha).functor ⋙ RationalQuiver.RepNil.toSplitFunctor E'' ⋙
    (Compat.targetEquivSplitZ a'' ha'').inverse

/-- T1, split → split, `ℓ = 0`.  @census none (helper) -/
noncomputable def bcIsoSSZ :
    bcHCss a ha a'' ha'' 0 ⋙ Cyclic.E_ECyc ≅ Cyclic.E_ECyc ⋙ bcQssZ a ha a'' ha'' :=
  let T'' := Compat.targetEquivSplitZ a'' ha''
  Functor.isoWhiskerLeft (bcHCss a ha a'' ha'' 0 ⋙ Cyclic.E_ECyc) T''.unitIso ≪≫
    Functor.isoWhiskerLeft (HC.toLambda (ImagUnit.ofSplit a ha) 0 ⋙ hcBaseChange 0 E E'' ⋙ ofLambdaFunctor (D := ImagUnit.ofSplit a'' ha'') ⟨a'', ha''⟩)
      (Functor.isoWhiskerRight (Compat.splitNativeZ a'' ha'') T''.inverse) ≪≫
    Functor.isoWhiskerLeft (HC.toLambda (ImagUnit.ofSplit a ha) 0 ⋙ hcBaseChange 0 E E'')
      (Functor.isoWhiskerRight (ofLambdaToLambda (D := ImagUnit.ofSplit a'' ha'') ⟨a'', ha''⟩)
        (Split.hcLambdaToF E'' 0 ⋙ Split.E_CycSplitFunctor ⋙ T''.inverse)) ≪≫
    Functor.isoWhiskerLeft (HC.toLambda (ImagUnit.ofSplit a ha) 0)
      (Functor.isoWhiskerRight (E_bc_cyc_split_iso E E'') T''.inverse) ≪≫
    Functor.isoWhiskerRight (Compat.splitNativeZ a ha).symm
      (RationalQuiver.RepNil.toSplitFunctor E'' ⋙ T''.inverse)

set_option backward.isDefEq.respectTransparency.types false in
/-- `C3` for case (a), `ℓ ≥ 1`: the components of the (T1) isomorphism are those of the relocated v1 isomorphism,
whose components are the canonical vertex maps.  @census none (helper; clause `RQ2-5.14-C3`) -/
theorem bcIsoSS_app_ψ {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A : HC ℓ E (ImagUnit.ofSplit a ha)) (v : Fin 3) :
    ((bcIsoSS a ha a'' ha'' hℓ).app A).hom.hom.ψ v
      = ((E_bc_split_iso E E'' ℓ hℓ).app ((HC.toLambda (ImagUnit.ofSplit a ha) ℓ).obj A)).hom.hom.ψ v := by
  ext x
  simp [bcIsoSS, Compat.splitNative, Compat.splitNativeApp, Compat.targetEquivSplit, Compat.reρSubEquiv, Compat.reρEquiv, ofLambdaToLambda, EssSurj.fdRepIsoOfComponents]
  simp only [qBCssRel, RationalQuiver.Rep.Hom.toSplit, Compat.reρFunctor, Compat.reρHom]
  erw [LinearMap.baseChange_id]
  repeat erw [CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `C3` for case (a), `ℓ = 0`: the components of the (T1) isomorphism are those of the relocated v1 isomorphism,
whose components are the canonical vertex maps.  @census none (helper; clause `RQ2-5.14-C3`) -/
theorem bcIsoSSZ_app_ψ (A : HC 0 E (ImagUnit.ofSplit a ha)) (v : Fin 2) :
    ((bcIsoSSZ a ha a'' ha'').app A).hom.hom.ψ v
      = ((E_bc_cyc_split_iso E E'').app ((HC.toLambda (ImagUnit.ofSplit a ha) 0).obj A)).hom.hom.ψ v := by
  ext x
  simp [bcIsoSSZ, Compat.splitNativeZ, Compat.splitNativeAppZ, Compat.targetEquivSplitZ, Compat.reρSubEquiv, Compat.reρEquiv, ofLambdaToLambda, EssSurj.fdRepIsoOfComponents]
  simp only [RationalQuiver.RepNil.toSplitFunctor, RationalQuiver.Rep.Hom.toSplit, Compat.reρFunctor, Compat.reρHom]
  erw [LinearMap.baseChange_id]
  repeat erw [CategoryTheory.Functor.map_id]
  rfl

end SS

section Mixed

variable {E : Type} [Field E] [CharZero E] {D : ImagUnit E}
  (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1)
variable {E'' : Type} [Field E''] [CharZero E''] [Algebra D.L E''] (a'' : E'') (ha'' : a'' * a'' = -1)

/-- HC-side base change, non-split → split.  @census none (helper) -/
noncomputable def bcHCmx (ℓ : ℕ) : HC ℓ E D ⥤ HC ℓ E'' (ImagUnit.ofSplit a'' ha'') :=
  Compat.toHCEObjFunctor hc ⋙ hcBaseChangeNS ℓ E (D.sqrtExt hc) E'' ⋙ ofLambdaFunctor (D := ImagUnit.ofSplit a'' ha'') ⟨a'', ha''⟩

/-- Quiver-side base change, non-split → split, `ℓ ≥ 1`.  @census none (helper) -/
noncomputable def bcQmx :
    (Equivalence.RepNilGel D).FullSubcategory ⥤
      (Equivalence.RepNilGel (ImagUnit.ofSplit a'' ha'')).FullSubcategory :=
  (Compat.targetEquivCardTwo hc).functor ⋙ qBCnsRel E D.L E'' (D.sqrtExt hc).card_gal ⋙
    (Compat.targetEquivSplit a'' ha'').inverse

/-- T1, non-split → split, `ℓ ≥ 1`.  @census none (helper) -/
noncomputable def bcIsoMx {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    bcHCmx hc a'' ha'' ℓ ⋙ Equivalence.E_EGel hℓ ≅ Equivalence.E_EGel hℓ ⋙ bcQmx hc a'' ha'' :=
  let T'' := Compat.targetEquivSplit a'' ha''
  let h₁ := Equivalence.E_Q_spec (D.sqrtExt hc).card_gal hℓ
  Functor.isoWhiskerLeft (bcHCmx hc a'' ha'' ℓ ⋙ Equivalence.E_EGel hℓ) T''.unitIso ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc ⋙ hcBaseChangeNS ℓ E (D.sqrtExt hc) E'' ⋙
        ofLambdaFunctor (D := ImagUnit.ofSplit a'' ha'') ⟨a'', ha''⟩)
      (Functor.isoWhiskerRight (Compat.splitNative a'' ha'' hℓ) T''.inverse) ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc ⋙ hcBaseChangeNS ℓ E (D.sqrtExt hc) E'')
      (Functor.isoWhiskerRight (ofLambdaToLambda (D := ImagUnit.ofSplit a'' ha'') ⟨a'', ha''⟩)
        (Split.hcLambdaToF E'' ℓ ⋙ Split.E_FNil ℓ hℓ ⋙ T''.inverse)) ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc)
      (Functor.isoWhiskerRight (E_bc_mixed_iso ℓ E (D.sqrtExt hc) E'' hℓ h₁) T''.inverse) ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc)
      (Functor.isoWhiskerRight (Compat.engineNative hc hℓ h₁)
        (qBCnsRel E D.L E'' (D.sqrtExt hc).card_gal ⋙ T''.inverse)) ≪≫
    Functor.isoWhiskerRight (Compat.hcEquivHCEObj hc).unitIso.symm
      (Equivalence.E_EGel hℓ ⋙ bcQmx hc a'' ha'')

/-- Quiver-side base change, non-split → split, `ℓ = 0`.  @census none (helper) -/
noncomputable def bcQmxZ :
    (RepNilTarget D 0).FullSubcategory ⥤ (RepNilTarget (ImagUnit.ofSplit a'' ha'') 0).FullSubcategory :=
  (Compat.targetEquivCardTwoZ hc).functor ⋙ RationalQuiver.RepNil.toSplitFunctor E'' ⋙
    (Compat.targetEquivSplitZ a'' ha'').inverse

/-- T1, non-split → split, `ℓ = 0`.  @census none (helper) -/
noncomputable def bcIsoMxZ :
    bcHCmx hc a'' ha'' 0 ⋙ Cyclic.E_ECyc ≅ Cyclic.E_ECyc ⋙ bcQmxZ hc a'' ha'' :=
  let T'' := Compat.targetEquivSplitZ a'' ha''
  let h₁ := Cyclic.E_Cyc_spec (D.sqrtExt hc).card_gal
  Functor.isoWhiskerLeft (bcHCmx hc a'' ha'' 0 ⋙ Cyclic.E_ECyc) T''.unitIso ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc ⋙ hcBaseChangeNS 0 E (D.sqrtExt hc) E'' ⋙
        ofLambdaFunctor (D := ImagUnit.ofSplit a'' ha'') ⟨a'', ha''⟩)
      (Functor.isoWhiskerRight (Compat.splitNativeZ a'' ha'') T''.inverse) ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc ⋙ hcBaseChangeNS 0 E (D.sqrtExt hc) E'')
      (Functor.isoWhiskerRight (ofLambdaToLambda (D := ImagUnit.ofSplit a'' ha'') ⟨a'', ha''⟩)
        (Split.hcLambdaToF E'' 0 ⋙ Split.E_CycSplitFunctor ⋙ T''.inverse)) ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc)
      (Functor.isoWhiskerRight (E_bc_cyc_mixed_iso E (D.sqrtExt hc) E'' h₁) T''.inverse) ≪≫
    Functor.isoWhiskerLeft (Compat.toHCEObjFunctor hc)
      (Functor.isoWhiskerRight (Compat.engineNativeZ hc h₁)
        (RationalQuiver.RepNil.toSplitFunctor E'' ⋙ T''.inverse)) ≪≫
    Functor.isoWhiskerRight (Compat.hcEquivHCEObj hc).unitIso.symm
      (Cyclic.E_ECyc ⋙ bcQmxZ hc a'' ha'')

set_option backward.isDefEq.respectTransparency.types false in
/-- `C3` for case (c), `ℓ ≥ 1`: the components of the (T1) isomorphism are those of the relocated v1 isomorphism,
whose components are the canonical vertex maps.  @census none (helper; clause `RQ2-5.14-C3`) -/
theorem bcIsoMx_app_ψ {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A : HC ℓ E D) (v : Fin 3) :
    ((bcIsoMx hc a'' ha'' hℓ).app A).hom.hom.ψ v
      = ((E_bc_mixed_iso ℓ E (D.sqrtExt hc) E'' hℓ (Equivalence.E_Q_spec (D.sqrtExt hc).card_gal hℓ)).app
            ((Compat.toHCEObjFunctor hc).obj A)).hom.hom.ψ v := by
  ext x
  simp [bcIsoMx, Compat.splitNative, Compat.splitNativeApp, Compat.targetEquivSplit, Compat.engineNative,
    Compat.engineNativeApp, Compat.targetEquivCardTwo, Compat.reρSubEquiv, Compat.reρEquiv, Compat.hcEquivHCEObj,
    ofLambdaToLambda, EssSurj.fdRepIsoOfComponents]
  repeat erw [CategoryTheory.Functor.map_id]
  simp only [qBCnsRel, RationalQuiver.Rep.Hom.toSplit, Compat.reρFunctor, Compat.reρHom]
  erw [LinearMap.baseChange_id]
  repeat erw [CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `C3` for case (c), `ℓ = 0`: the components of the (T1) isomorphism are those of the relocated v1 isomorphism,
whose components are the canonical vertex maps.  @census none (helper; clause `RQ2-5.14-C3`) -/
theorem bcIsoMxZ_app_ψ (A : HC 0 E D) (v : Fin 2) :
    ((bcIsoMxZ hc a'' ha'').app A).hom.hom.ψ v
      = ((E_bc_cyc_mixed_iso E (D.sqrtExt hc) E'' (Cyclic.E_Cyc_spec (D.sqrtExt hc).card_gal)).app
            ((Compat.toHCEObjFunctor hc).obj A)).hom.hom.ψ v := by
  ext x
  simp [bcIsoMxZ, Compat.splitNativeZ, Compat.splitNativeAppZ, Compat.targetEquivSplitZ, Compat.engineNativeZ,
    Compat.engineNativeAppZ, Compat.targetEquivCardTwoZ, Compat.reρSubEquiv, Compat.reρEquiv, Compat.hcEquivHCEObj,
    ofLambdaToLambda, EssSurj.fdRepIsoOfComponents]
  repeat erw [CategoryTheory.Functor.map_id]
  simp only [RationalQuiver.RepNil.toSplitFunctor, RationalQuiver.Rep.Hom.toSplit, Compat.reρFunctor, Compat.reρHom]
  erw [LinearMap.baseChange_id]
  repeat erw [CategoryTheory.Functor.map_id]
  rfl

end Mixed

section HomNNC

open RationalQuivers.RationalQuiver
open scoped TensorProduct

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable {h : Nat.card Gal(L/K) = 2}
variable {K'' L'' : Type} [Field K''] [Field L''] [Algebra K'' L''] [IsGalois K'' L'']
  [FiniteDimensional K'' L''] {h'' : Nat.card Gal(L''/K'') = 2}
variable [Algebra L L''] [Algebra K K''] [Algebra K L''] [IsScalarTower K L L'']
  [IsScalarTower K K'' L'']
variable (R : RestrictionDatum K L K'' L'')

set_option backward.isDefEq.respectTransparency.types false in
/-- The `nn` base change of a finite-dimensional representation.  @census none (helper; WP-15) -/
noncomputable def fdBcNNC (M : FDRep (cyclicOfCardTwo K L h)) :
    FDRep (cyclicOfCardTwo K'' L'' h'') where
  toRep := Rep.bcNNC R M.toRep
  finiteDimensional v := by
    haveI := M.finiteDimensional v
    exact Module.Finite.base_change L L'' (M.toRep.M v)

/-- **T2, non-split → non-split, `ℓ = 0`** (the cyclic companion of v1's `homModule_baseChange_nn`, which v1
stated for the Gelfand quiver only; same proof).  The canonical map
`K'' ⊗_K Hom_{Γ_K}(M,N) → Hom_{Γ_{K''}}(L'' ⊗_L M, L'' ⊗_L N)`, `a ⊗ ψ ↦ a · (L'' ⊗ ψ_v)_v`, is an
isomorphism of `K''`-vector spaces.

@census none (helper; clause `RQ2-5.14-C4`, case (b), `ℓ = 0`) -/
theorem homModule_baseChange_nnC (M N : FDRep (cyclicOfCardTwo K L h)) :
    ∃ f : K'' ⊗[K] Rep.homModule M N ≃ₗ[K'']
        Rep.homModule (fdBcNNC (h'' := h'') R M) (fdBcNNC (h'' := h'') R N),
      ∀ (a : K'') (ψ : Rep.homModule M N) (v : (cyclicOfCardTwo K L h).V),
        Rep.homFam _ _ (f (a ⊗ₜ[K] ψ)).1 v
          = algebraMap K'' L'' a • LinearMap.baseChange L'' (Rep.homFam M N ψ.1 v) := by
  obtain ⟨g, hg⟩ := homModule_baseChange_ns L'' M N
  let ιK : K'' ⊗[K] Rep.homModule M N →ₗ[K''] L'' ⊗[K] Rep.homModule M N :=
    TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K'' L'') LinearMap.id
  have hιK : Function.Injective ιK := tensor_algebraMap_injective _
  let j : K'' ⊗[K] Rep.homModule M N →ₗ[K'']
      (Rep.homVecK (fdBcNNC (h'' := h'') R M) (fdBcNNC (h'' := h'') R N)).carrier :=
    { toFun := fun x => g (ιK x)
      map_add' := fun x y => (congrArg g (map_add ιK x y)).trans (map_add g _ _)
      map_smul' := fun c x => by
        have h1 : ιK (c • x) = algebraMap K'' L'' c • ιK x := by rw [map_smul, algebraMap_smul]
        exact (congrArg g h1).trans (map_smul g _ _) }
  have hj : Function.Injective j := fun x y hxy => hιK (g.injective hxy)
  have hjtmul : ∀ (a : K'') (ψ : Rep.homModule M N) (v : (cyclicOfCardTwo K L h).V),
      Rep.homFam _ _ (j (a ⊗ₜ[K] ψ)) v
        = algebraMap K'' L'' a • LinearMap.baseChange L'' (Rep.homFam M N ψ.1 v) :=
    fun a ψ v => hg (algebraMap K'' L'' a) ψ v
  -- the image lies in `Hom_{Γ_{K''}}`
  have hle : LinearMap.range j ≤ Rep.homModule (fdBcNNC (h'' := h'') R M) (fdBcNNC (h'' := h'') R N) := by
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul a ψ =>
      let ψ'' := Rep.homEquiv (fdBcNNC (h'' := h'') R M) (fdBcNNC (h'' := h'') R N)
        (Rep.Hom.bcNNC R ((Rep.homEquiv M N).symm ψ))
      have heq : j (a ⊗ₜ[K] ψ) = a • (ψ'' : (Rep.homVecK _ _).carrier) := by
        apply Subtype.ext
        funext v
        exact hjtmul a ψ v
      rw [heq]
      exact Submodule.smul_mem _ a ψ''.2
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  -- dimensions agree
  haveI : FiniteDimensional K (Rep.homModule M N) := Rep.finiteDimensional_homModule M N
  have hdimH'' : Module.finrank K''
      (Rep.homModule (fdBcNNC (h'' := h'') R M) (fdBcNNC (h'' := h'') R N))
      = Module.finrank K (Rep.homModule M N) := by
    rw [Rep.homModule, Descent.finrank_fixedPoints K'']
    rw [show Module.finrank L'' (Rep.homVecK (fdBcNNC (h'' := h'') R M)
        (fdBcNNC (h'' := h'') R N)).carrier
        = Module.finrank L'' (L'' ⊗[K] Rep.homModule M N) from g.finrank_eq.symm,
      Module.finrank_baseChange]
  haveI : FiniteDimensional K'' (Rep.homModule (fdBcNNC (h'' := h'') R M) (fdBcNNC (h'' := h'') R N)) :=
    Rep.finiteDimensional_homModule _ _
  have hrange : LinearMap.range j
      = Rep.homModule (fdBcNNC (h'' := h'') R M) (fdBcNNC (h'' := h'') R N) := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [LinearMap.finrank_range_of_inj hj, Module.finrank_baseChange, hdimH'']
  refine ⟨(LinearEquiv.ofInjective j hj).trans (LinearEquiv.ofEq _ _ hrange), fun a ψ v => ?_⟩
  exact hjtmul a ψ v

end HomNNC

/-! ## T2, quiver side (`RQ2-5.14-C4`) on `Rep^nil(Γ_E)` -/

section HomQ

open RationalQuivers.RationalQuiver
open scoped TensorProduct

variable {E : Type} [Field E] [CharZero E] (D : ImagUnit E)

/-- **T2, quiver side, split target** (cases (a) and (c)): for `V, W ∈ Rep^nil(Γ_E)` and any
`L_E → E''`, the canonical map `E'' ⊗_E Hom_{Γ_E}(V, W) → Hom(E'' ⊗_{L_E} V, E'' ⊗_{L_E} W)`,
`a ⊗ ψ ↦ a·(E'' ⊗ ψ_v)_v`, is an isomorphism (the relocated `homModule_baseChange_ns`, at `Γ = Γ_E`).
@census none (helper; clause `RQ2-5.14-C4`, cases (a), (c)) -/
theorem homBC_split (E'' : Type) [Field E''] [Algebra E E''] [Algebra D.L E''] [IsScalarTower E D.L E'']
    {ℓ : ℕ} (V W : (RepNilTarget D ℓ).FullSubcategory) :
    ∃ f : E'' ⊗[E] Rep.homModule V.obj W.obj ≃ₗ[E'']
        Rep.classicalHom (V.obj.toRep.toSplit E'') (W.obj.toRep.toSplit E''),
      ∀ (a : E'') (ψ : Rep.homModule V.obj W.obj) (v : (GammaE D ℓ).V),
        (f (a ⊗ₜ[E] ψ)).1 v = a • LinearMap.baseChange E'' (Rep.homFam V.obj W.obj ψ.1 v) :=
  homModule_baseChange_ns E'' V.obj W.obj

variable {D}
variable {E'' : Type} [Field E''] [CharZero E''] {D'' : ImagUnit E''}
variable [Algebra E E''] [Algebra D.L D''.L] [Algebra E D''.L]
  [IsScalarTower E E'' D''.L] [IsScalarTower E D.L D''.L]
variable (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) (hc'' : ∃ σ : D''.L ≃ₐ[E''] D''.L, D''.chi σ = -1)

set_option backward.isDefEq.respectTransparency.types false in
/-- **T2, quiver side, non-split → non-split** (case (b)), `ℓ ≥ 1`: for `V, W ∈ Rep^nil(Γ_E)`, read in
the `gelfandOfCardTwo` presentation (`Compat.targetEquivCardTwo`, identity on spaces), the canonical
map `E'' ⊗_E Hom(V, W) → Hom(L'' ⊗_{L_E} V, L'' ⊗_{L_E} W)` is an isomorphism.
@census none (helper; clause `RQ2-5.14-C4`, case (b)) -/
theorem homBC_nn (V W : (Equivalence.RepNilGel D).FullSubcategory) :
    ∃ f : E'' ⊗[E] Rep.homModule ((Compat.targetEquivCardTwo hc).functor.obj V).obj
          ((Compat.targetEquivCardTwo hc).functor.obj W).obj ≃ₗ[E'']
        Rep.homModule
          (fdBcNN (h'' := (D''.sqrtExt hc'').card_gal) (restrictionDatum (D.sqrtExt hc) (D''.sqrtExt hc'') (conjCompatE hc hc''))
            ((Compat.targetEquivCardTwo hc).functor.obj V).obj)
          (fdBcNN (h'' := (D''.sqrtExt hc'').card_gal) (restrictionDatum (D.sqrtExt hc) (D''.sqrtExt hc'') (conjCompatE hc hc''))
            ((Compat.targetEquivCardTwo hc).functor.obj W).obj),
      ∀ (a : E'') (ψ : Rep.homModule ((Compat.targetEquivCardTwo hc).functor.obj V).obj
          ((Compat.targetEquivCardTwo hc).functor.obj W).obj) (v : Fin 3),
        Rep.homFam _ _ (f (a ⊗ₜ[E] ψ)).1 v
          = algebraMap E'' D''.L a • LinearMap.baseChange D''.L (Rep.homFam _ _ ψ.1 v) :=
  homModule_baseChange_nn _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- **T2, quiver side, non-split → non-split**, `ℓ = 0` (`homModule_baseChange_nnC`).
@census none (helper; clause `RQ2-5.14-C4`, case (b), `ℓ = 0`) -/
theorem homBC_nnZ (V W : (RepNilTarget D 0).FullSubcategory) :
    ∃ f : E'' ⊗[E] Rep.homModule ((Compat.targetEquivCardTwoZ hc).functor.obj V).obj
          ((Compat.targetEquivCardTwoZ hc).functor.obj W).obj ≃ₗ[E'']
        Rep.homModule
          (fdBcNNC (h'' := (D''.sqrtExt hc'').card_gal) (restrictionDatum (D.sqrtExt hc) (D''.sqrtExt hc'') (conjCompatE hc hc''))
            ((Compat.targetEquivCardTwoZ hc).functor.obj V).obj)
          (fdBcNNC (h'' := (D''.sqrtExt hc'').card_gal) (restrictionDatum (D.sqrtExt hc) (D''.sqrtExt hc'') (conjCompatE hc hc''))
            ((Compat.targetEquivCardTwoZ hc).functor.obj W).obj),
      ∀ (a : E'') (ψ : Rep.homModule ((Compat.targetEquivCardTwoZ hc).functor.obj V).obj
          ((Compat.targetEquivCardTwoZ hc).functor.obj W).obj) (v : Fin 2),
        Rep.homFam _ _ (f (a ⊗ₜ[E] ψ)).1 v
          = algebraMap E'' D''.L a • LinearMap.baseChange D''.L (Rep.homFam _ _ ψ.1 v) :=
  homModule_baseChange_nnC _ _ _

end HomQ


/-! ## T2, HC side (`RQ2-5.14-C5`, the new clause C9) -/

section C5

open RationalQuivers.RationalQuiver
open scoped TensorProduct

section Generic

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] {Γ : RationalQuiver K L}

/-- Conjugation by isomorphisms of representations is a `K`-linear isomorphism of `Hom`-modules.
@census none (helper) -/
noncomputable def homModuleCongr {M M' N N' : FDRep Γ} (eM : M ≅ M') (eN : N ≅ N') :
    Rep.homModule M N ≃ₗ[K] Rep.homModule M' N' where
  toFun ψ := Rep.homEquiv M' N' (eM.inv ≫ (Rep.homEquiv M N).symm ψ ≫ eN.hom)
  invFun ψ := Rep.homEquiv M N (eM.hom ≫ (Rep.homEquiv M' N').symm ψ ≫ eN.inv)
  left_inv ψ := by
    apply (Rep.homEquiv M N).symm.injective
    rw [Equiv.symm_apply_apply]
    show eM.hom ≫ (eM.inv ≫ _ ≫ eN.hom) ≫ eN.inv = _
    simp
  right_inv ψ := by
    apply (Rep.homEquiv M' N').symm.injective
    rw [Equiv.symm_apply_apply]
    show eM.inv ≫ (eM.hom ≫ _ ≫ eN.inv) ≫ eN.hom = _
    simp
  map_add' ψ χ := by
    apply Subtype.ext; apply Subtype.ext; funext v; apply LinearMap.ext; intro x
    show (eN.hom.ψ v) ((ψ.1.1 v + χ.1.1 v) (eM.inv.ψ v x)) = _
    simp only [LinearMap.add_apply, map_add]; rfl
  map_smul' a ψ := by
    apply Subtype.ext; apply Subtype.ext; funext v; apply LinearMap.ext; intro x
    show (eN.hom.ψ v) ((algebraMap K L a • ψ.1.1 v) (eM.inv.ψ v x)) = _
    simp only [LinearMap.smul_apply, map_smul]; rfl

/-- A fully faithful functor into a full subcategory of `Rep(Γ)` whose action on morphisms is
`K`-linear (componentwise) identifies `Hom`-spaces with `Hom_Γ`-modules, `K`-linearly.  @census none (helper) -/
noncomputable def homLinOfFF {C : Type*} [Category C] [Preadditive C] [Linear K C]
    {P : ObjectProperty (FDRep Γ)} (F : C ⥤ P.FullSubcategory) (hF : F.FullyFaithful)
    (hadd : ∀ {A B : C} (f g : A ⟶ B) (v : Γ.V),
      (F.map (f + g)).hom.ψ v = (F.map f).hom.ψ v + (F.map g).hom.ψ v)
    (hsmul : ∀ {A B : C} (a : K) (f : A ⟶ B) (v : Γ.V),
      (F.map (a • f)).hom.ψ v = algebraMap K L a • (F.map f).hom.ψ v) (A B : C) :
    (A ⟶ B) ≃ₗ[K] Rep.homModule (F.obj A).obj (F.obj B).obj :=
  LinearEquiv.ofBijective
    { toFun := fun f => Rep.homEquiv _ _ (F.map f).hom
      map_add' := fun f g => Subtype.ext (Subtype.ext (funext fun v => hadd f g v))
      map_smul' := fun a f => by
        apply Subtype.ext; apply Subtype.ext; funext v; exact hsmul a f v }
    ⟨fun f g h => hF.map_injective (ObjectProperty.hom_ext _ ((Rep.homEquiv _ _).injective h)),
      fun ψ => ⟨hF.preimage (ObjectProperty.homMk ((Rep.homEquiv _ _).symm ψ)), by
        show Rep.homEquiv _ _ (F.map (hF.preimage _)).hom = ψ
        rw [hF.map_preimage]; exact (Rep.homEquiv _ _).apply_symm_apply ψ⟩⟩

/-- On a split rational quiver every classical homomorphism is rational: `Hom_Γ = classicalHom`,
`F`-linearly (`splitHomEquiv` on the module level).  @census none (helper) -/
noncomputable def homModuleSplitEquiv {F : Type} [Field F] {Q : RQuiver.{0}}
    (M N : FDRep (splitOf F Q)) : Rep.homModule M N ≃ₗ[F] Rep.classicalHom M.toRep N.toRep where
  toFun ψ := ψ.1
  invFun χ := ⟨χ, (Rep.mem_homModule_iff M N χ).2 fun σ v m => by
    rw [splitOf_φ_eq M.toRep σ v m, splitOf_φ_eq N.toRep σ v]; rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The core of canonicity: conjugating by a natural isomorphism `j : B ⋙ F ≅ Pf` and pulling back
along `Lin` (componentwise `F` on morphisms) turns a family that is componentwise `c • (Pf.map f)` into
`c • B.map f`.  @census none (helper) -/
theorem homLin_symm_congr {C C' : Type*} [Category C] [Category C'] [Preadditive C'] [Linear K C']
    {P : ObjectProperty (FDRep Γ)} (F : C' ⥤ P.FullSubcategory)
    (hsmul : ∀ {A B : C'} (c : K) (f : A ⟶ B) (v : Γ.V),
      (F.map (c • f)).hom.ψ v = algebraMap K L c • (F.map f).hom.ψ v)
    (B : C ⥤ C') (Pf : C ⥤ P.FullSubcategory) (j : ∀ X, F.obj (B.obj X) ≅ Pf.obj X)
    (nat : ∀ {X Y : C} (g : X ⟶ Y), F.map (B.map g) ≫ (j Y).hom = (j X).hom ≫ Pf.map g)
    {X Y : C} (Lin : (B.obj X ⟶ B.obj Y) ≃ₗ[K] Rep.homModule (F.obj (B.obj X)).obj (F.obj (B.obj Y)).obj)
    (hLin : ∀ g v, (Lin g).1.1 v = (F.map g).hom.ψ v)
    (f : X ⟶ Y) (c : K) (ψ : Rep.homModule (Pf.obj X).obj (Pf.obj Y).obj)
    (hψ : ∀ v, ψ.1.1 v = algebraMap K L c • (Pf.map f).hom.ψ v) :
    Lin.symm
        (homModuleCongr ((ObjectProperty.ι _).mapIso (j X)).symm ((ObjectProperty.ι _).mapIso (j Y)).symm ψ)
      = c • B.map f := by
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext; apply Subtype.ext; funext v
  have hn := congrArg (fun φ => φ.hom.ψ v) ((Iso.eq_comp_inv (j Y)).mpr (nat f))
  rw [hLin]
  change (j Y).inv.hom.ψ v ∘ₗ ψ.1.1 v ∘ₗ (j X).hom.hom.ψ v = (F.map (c • B.map f)).hom.ψ v
  rw [hsmul, hψ, hn]
  ext x
  change (j Y).inv.hom.ψ v (algebraMap K L c • _) = algebraMap K L c • (j Y).inv.hom.ψ v _
  rw [map_smul]
  rfl

/-- `homLin_symm_congr` for the (T1) isomorphisms of this file, which all have the shape
`B ⋙ 𝔼'' ≅ 𝔼 ⋙ (Q₁ ⋙ Q₂ ⋙ T''⁻¹)`: the conjugating isomorphism is `T''(iso) ≫ ε`.  @census none (helper) -/
theorem homLin_canon {C C' R R' S : Type*} [Category C] [Category C'] [Category R] [Category R']
    [Category S] [Preadditive C'] [Linear K C'] {P : ObjectProperty (FDRep Γ)}
    (B : C ⥤ C') (𝔼 : C ⥤ R) (𝔼'' : C' ⥤ R') (Q₁ : R ⥤ S) (Q₂ : S ⥤ P.FullSubcategory)
    (T'' : R' ≌ P.FullSubcategory) (iso : B ⋙ 𝔼'' ≅ 𝔼 ⋙ Q₁ ⋙ Q₂ ⋙ T''.inverse)
    (hsmul : ∀ {A B : C'} (c : K) (f : A ⟶ B) (v : Γ.V),
      ((𝔼'' ⋙ T''.functor).map (c • f)).hom.ψ v = algebraMap K L c • ((𝔼'' ⋙ T''.functor).map f).hom.ψ v)
    {X Y : C} (Lin : (B.obj X ⟶ B.obj Y) ≃ₗ[K]
      Rep.homModule (T''.functor.obj (𝔼''.obj (B.obj X))).obj (T''.functor.obj (𝔼''.obj (B.obj Y))).obj)
    (hLin : ∀ g v, (Lin g).1.1 v = (T''.functor.map (𝔼''.map g)).hom.ψ v)
    (f : X ⟶ Y) (c : K) (ψ : Rep.homModule (Q₂.obj (Q₁.obj (𝔼.obj X))).obj (Q₂.obj (Q₁.obj (𝔼.obj Y))).obj)
    (hψ : ∀ v, ψ.1.1 v = algebraMap K L c • (Q₂.map (Q₁.map (𝔼.map f))).hom.ψ v) :
    Lin.symm (homModuleCongr
        ((ObjectProperty.ι _).mapIso (T''.functor.mapIso (iso.app X) ≪≫ T''.counitIso.app _)).symm
        ((ObjectProperty.ι _).mapIso (T''.functor.mapIso (iso.app Y) ≪≫ T''.counitIso.app _)).symm ψ)
      = c • B.map f := by
  refine homLin_symm_congr (𝔼'' ⋙ T''.functor) hsmul B (𝔼 ⋙ Q₁ ⋙ Q₂)
    (fun X => T''.functor.mapIso (iso.app X) ≪≫ T''.counitIso.app _) ?_ Lin hLin f c ψ hψ
  intro X Y g
  have h1 := iso.hom.naturality g
  have h2 := T''.counit.naturality (Q₂.map (Q₁.map (𝔼.map g)))
  simp only [Functor.comp_map] at h1 h2
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.comp_map]
  erw [← Category.assoc, ← Functor.map_comp, h1, Functor.map_comp]
  simp only [Category.assoc]
  exact congrArg (fun t => _ ≫ t) h2

end Generic

section NNHom

variable {E : Type} [Field E] [CharZero E] {D : ImagUnit E} {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
  (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1)

/-- `𝔼_E`, read in the `gelfandOfCardTwo` presentation, on `Hom`-spaces.  @census none (helper) -/
noncomputable def homLinNN (A B : HC ℓ E D) :
    (A ⟶ B) ≃ₗ[E] Rep.homModule
      ((Equivalence.E_EGel hℓ ⋙ (Compat.targetEquivCardTwo hc).functor).obj A).obj
      ((Equivalence.E_EGel hℓ ⋙ (Compat.targetEquivCardTwo hc).functor).obj B).obj :=
  haveI := Equivalence.E_E_faithful (D := D) hℓ
  haveI := Equivalence.E_E_full (D := D) hℓ
  homLinOfFF (Equivalence.E_EGel hℓ ⋙ (Compat.targetEquivCardTwo hc).functor)
    (Functor.FullyFaithful.ofFullyFaithful _)
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl)
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl) A B

/-- `𝔼_E` at `ℓ = 0`, read in the `cyclicOfCardTwo` presentation, on `Hom`-spaces.  @census none (helper) -/
noncomputable def homLinNNZ (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) (A B : HC 0 E D) :
    (A ⟶ B) ≃ₗ[E] Rep.homModule
      ((Cyclic.E_ECyc ⋙ (Compat.targetEquivCardTwoZ hc).functor).obj A).obj
      ((Cyclic.E_ECyc ⋙ (Compat.targetEquivCardTwoZ hc).functor).obj B).obj :=
  haveI := Cyclic.E_ECyc_faithful (D := D)
  haveI := Cyclic.E_Cyc_full (D := D)
  homLinOfFF (Cyclic.E_ECyc ⋙ (Compat.targetEquivCardTwoZ hc).functor)
    (Functor.FullyFaithful.ofFullyFaithful _)
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl)
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl) A B

end NNHom

section SSHom

variable {E : Type} [Field E] [CharZero E] (a : E) (ha : a * a = -1)

/-- `𝔼_E`, `√-1 ∈ E`, read in the split presentation, on `Hom`-spaces (`ℓ ≥ 1`).  @census none (helper) -/
noncomputable def homLinSS {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A B : HC ℓ E (ImagUnit.ofSplit a ha)) :
    (A ⟶ B) ≃ₗ[E] Rep.homModule
      ((Equivalence.E_EGel hℓ ⋙ (Compat.targetEquivSplit a ha).functor).obj A).obj
      ((Equivalence.E_EGel hℓ ⋙ (Compat.targetEquivSplit a ha).functor).obj B).obj :=
  haveI := Equivalence.E_E_faithful (D := ImagUnit.ofSplit a ha) hℓ
  haveI := Equivalence.E_E_full (D := ImagUnit.ofSplit a ha) hℓ
  homLinOfFF (Equivalence.E_EGel hℓ ⋙ (Compat.targetEquivSplit a ha).functor)
    (Functor.FullyFaithful.ofFullyFaithful _)
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl)
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl) A B

/-- The same at `ℓ = 0`.  @census none (helper) -/
noncomputable def homLinSSZ (A B : HC 0 E (ImagUnit.ofSplit a ha)) :
    (A ⟶ B) ≃ₗ[E] Rep.homModule
      ((Cyclic.E_ECyc ⋙ (Compat.targetEquivSplitZ a ha).functor).obj A).obj
      ((Cyclic.E_ECyc ⋙ (Compat.targetEquivSplitZ a ha).functor).obj B).obj :=
  haveI := Cyclic.E_ECyc_faithful (D := ImagUnit.ofSplit a ha)
  haveI := Cyclic.E_Cyc_full (D := ImagUnit.ofSplit a ha)
  homLinOfFF (Cyclic.E_ECyc ⋙ (Compat.targetEquivSplitZ a ha).functor)
    (Functor.FullyFaithful.ofFullyFaithful _)
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl)
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl) A B

end SSHom

section NNHC

variable {E : Type} [Field E] [CharZero E] {D : ImagUnit E}
variable {E'' : Type} [Field E''] [CharZero E''] {D'' : ImagUnit E''}
variable [Algebra E E''] [Algebra D.L D''.L] [Algebra E D''.L]
  [IsScalarTower E E'' D''.L] [IsScalarTower E D.L D''.L]
variable (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) (hc'' : ∃ σ : D''.L ≃ₐ[E''] D''.L, D''.chi σ = -1)

/-- **T2, HC side** (`RQ2-5.14-C5`, the new clause C9), case (b), `ℓ ≥ 1`: the canonical map
`E'' ⊗_E Hom(M_E, N_E) → Hom(E'' ⊗_E M_E, E'' ⊗_E N_E)`, `c ⊗ f ↦ c·(E'' ⊗ f)`, is an isomorphism of
`E''`-vector spaces, deduced from (T1) and the equivalences `𝔼_E`, `𝔼_{E''}` as in the tex:
`Hom ≅ Hom_{Γ_E}(𝔼_E M, 𝔼_E N)` (full faithfulness), the quiver side of (T2), and conjugation by the
(T1) isomorphism; the composite sends `c ⊗ f` to `c·(E'' ⊗ f)` (`homLin_canon`).  @census none (helper; clause `RQ2-5.14-C5`) -/
theorem homBC_HC_nn {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A B : HC ℓ E D) :
    ∃ e : E'' ⊗[E] (A ⟶ B) ≃ₗ[E''] ((bcHCnn hc hc'' ℓ).obj A ⟶ (bcHCnn hc hc'' ℓ).obj B),
      ∀ (c : E'') (f : A ⟶ B), e (c ⊗ₜ f) = c • (bcHCnn hc hc'' ℓ).map f := by
  obtain ⟨f₂, hf₂⟩ := homBC_nn hc hc'' ((Equivalence.E_EGel hℓ).obj A) ((Equivalence.E_EGel hℓ).obj B)
  let T'' := Compat.targetEquivCardTwo hc''
  let i := fun X : HC ℓ E D =>
    (ObjectProperty.ι _).mapIso (T''.functor.mapIso ((bcIsoNN hc hc'' hℓ).app X) ≪≫ T''.counitIso.app _)
  refine ⟨(LinearEquiv.baseChange E E'' _ _ (homLinNN hℓ hc A B)).trans
    (f₂.trans ((homModuleCongr (i A).symm (i B).symm).trans (homLinNN hℓ hc'' _ _).symm)), fun c f => ?_⟩
  exact homLin_canon (bcHCnn hc hc'' ℓ) (Equivalence.E_EGel hℓ) _ (Compat.targetEquivCardTwo hc).functor
    (qBCnnRel (h := (D.sqrtExt hc).card_gal) (h'' := (D''.sqrtExt hc'').card_gal)
      (restrictionDatum (D.sqrtExt hc) (D''.sqrtExt hc'') (conjCompatE hc hc''))) T'' (bcIsoNN hc hc'' hℓ)
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl) (homLinNN hℓ hc'' _ _) (fun _ _ => rfl) f c _
    (fun v => hf₂ c _ v)

/-- **T2, HC side**, case (b), `ℓ = 0`.  @census none (helper; clause `RQ2-5.14-C5`) -/
theorem homBC_HC_nnZ (A B : HC 0 E D) :
    ∃ e : E'' ⊗[E] (A ⟶ B) ≃ₗ[E''] ((bcHCnn hc hc'' 0).obj A ⟶ (bcHCnn hc hc'' 0).obj B),
      ∀ (c : E'') (f : A ⟶ B), e (c ⊗ₜ f) = c • (bcHCnn hc hc'' 0).map f := by
  obtain ⟨f₂, hf₂⟩ := homBC_nnZ hc hc'' (Cyclic.E_ECyc.obj A) (Cyclic.E_ECyc.obj B)
  let T'' := Compat.targetEquivCardTwoZ hc''
  let i := fun X : HC 0 E D =>
    (ObjectProperty.ι _).mapIso (T''.functor.mapIso ((bcIsoNNZ hc hc'').app X) ≪≫ T''.counitIso.app _)
  refine ⟨(LinearEquiv.baseChange E E'' _ _ (homLinNNZ hc A B)).trans
    (f₂.trans ((homModuleCongr (i A).symm (i B).symm).trans (homLinNNZ hc'' _ _).symm)), fun c f => ?_⟩
  exact homLin_canon (bcHCnn hc hc'' 0) (Cyclic.E_ECyc) _ (Compat.targetEquivCardTwoZ hc).functor
    (qBCnnC (h := (D.sqrtExt hc).card_gal) (h'' := (D''.sqrtExt hc'').card_gal)
      (restrictionDatum (D.sqrtExt hc) (D''.sqrtExt hc'') (conjCompatE hc hc''))) T'' (bcIsoNNZ hc hc'')
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl) (homLinNNZ hc'' _ _) (fun _ _ => rfl) f c _
    (fun v => hf₂ c _ v)

end NNHC

section SSHC

variable {E : Type} [Field E] [CharZero E] (a : E) (ha : a * a = -1)
variable {E'' : Type} [Field E''] [CharZero E''] [Algebra E E''] (a'' : E'') (ha'' : a'' * a'' = -1)

/-- **T2, HC side**, case (a), `ℓ ≥ 1`.  @census none (helper; clause `RQ2-5.14-C5`) -/
theorem homBC_HC_ss {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A B : HC ℓ E (ImagUnit.ofSplit a ha)) :
    ∃ e : E'' ⊗[E] (A ⟶ B) ≃ₗ[E'']
      ((bcHCss a ha a'' ha'' ℓ).obj A ⟶ (bcHCss a ha a'' ha'' ℓ).obj B),
      ∀ (c : E'') (f : A ⟶ B), e (c ⊗ₜ f) = c • (bcHCss a ha a'' ha'' ℓ).map f := by
  let G := Equivalence.E_EGel (D := ImagUnit.ofSplit a ha) hℓ ⋙ (Compat.targetEquivSplit a ha).functor
  obtain ⟨f₂, hf₂⟩ := homModule_baseChange_ns E'' (G.obj A).obj (G.obj B).obj
  let T'' := Compat.targetEquivSplit a'' ha''
  let i := fun X : HC ℓ E (ImagUnit.ofSplit a ha) =>
    (ObjectProperty.ι _).mapIso (T''.functor.mapIso ((bcIsoSS a ha a'' ha'' hℓ).app X) ≪≫ T''.counitIso.app _)
  refine ⟨(LinearEquiv.baseChange E E'' _ _ (homLinSS a ha hℓ A B)).trans
    (f₂.trans ((homModuleSplitEquiv _ _).symm.trans
      ((homModuleCongr (i A).symm (i B).symm).trans (homLinSS a'' ha'' hℓ _ _).symm))), fun c f => ?_⟩
  exact homLin_canon (bcHCss a ha a'' ha'' ℓ) (Equivalence.E_EGel hℓ) _ (Compat.targetEquivSplit a ha).functor
    (qBCssRel E E'') T'' (bcIsoSS a ha a'' ha'' hℓ)
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl) (homLinSS a'' ha'' hℓ _ _) (fun _ _ => rfl) f c _
    (fun v => hf₂ c _ v)

/-- **T2, HC side**, case (a), `ℓ = 0`.  @census none (helper; clause `RQ2-5.14-C5`) -/
theorem homBC_HC_ssZ (A B : HC 0 E (ImagUnit.ofSplit a ha)) :
    ∃ e : E'' ⊗[E] (A ⟶ B) ≃ₗ[E'']
      ((bcHCss a ha a'' ha'' 0).obj A ⟶ (bcHCss a ha a'' ha'' 0).obj B),
      ∀ (c : E'') (f : A ⟶ B), e (c ⊗ₜ f) = c • (bcHCss a ha a'' ha'' 0).map f := by
  let G := Cyclic.E_ECyc (D := ImagUnit.ofSplit a ha) ⋙ (Compat.targetEquivSplitZ a ha).functor
  obtain ⟨f₂, hf₂⟩ := homModule_baseChange_ns E'' (G.obj A).obj (G.obj B).obj
  let T'' := Compat.targetEquivSplitZ a'' ha''
  let i := fun X : HC 0 E (ImagUnit.ofSplit a ha) =>
    (ObjectProperty.ι _).mapIso (T''.functor.mapIso ((bcIsoSSZ a ha a'' ha'').app X) ≪≫ T''.counitIso.app _)
  refine ⟨(LinearEquiv.baseChange E E'' _ _ (homLinSSZ a ha A B)).trans
    (f₂.trans ((homModuleSplitEquiv _ _).symm.trans
      ((homModuleCongr (i A).symm (i B).symm).trans (homLinSSZ a'' ha'' _ _).symm))), fun c f => ?_⟩
  exact homLin_canon (bcHCss a ha a'' ha'' 0) (Cyclic.E_ECyc) _ (Compat.targetEquivSplitZ a ha).functor
    (RationalQuiver.RepNil.toSplitFunctor E'') T'' (bcIsoSSZ a ha a'' ha'')
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl) (homLinSSZ a'' ha'' _ _) (fun _ _ => rfl) f c _
    (fun v => hf₂ c _ v)

end SSHC

section MxHC

variable {E : Type} [Field E] [CharZero E] {D : ImagUnit E}
  (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1)
variable {E'' : Type} [Field E''] [CharZero E''] [Algebra D.L E''] [Algebra E E'']
  [IsScalarTower E D.L E''] (a'' : E'') (ha'' : a'' * a'' = -1)

/-- **T2, HC side**, case (c), `ℓ ≥ 1`.  @census none (helper; clause `RQ2-5.14-C5`) -/
theorem homBC_HC_mx {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A B : HC ℓ E D) :
    ∃ e : E'' ⊗[E] (A ⟶ B) ≃ₗ[E'']
      ((bcHCmx hc a'' ha'' ℓ).obj A ⟶ (bcHCmx hc a'' ha'' ℓ).obj B),
      ∀ (c : E'') (f : A ⟶ B), e (c ⊗ₜ f) = c • (bcHCmx hc a'' ha'' ℓ).map f := by
  let G := Equivalence.E_EGel (D := D) hℓ ⋙ (Compat.targetEquivCardTwo hc).functor
  obtain ⟨f₂, hf₂⟩ := homModule_baseChange_ns E'' (G.obj A).obj (G.obj B).obj
  let T'' := Compat.targetEquivSplit a'' ha''
  let i := fun X : HC ℓ E D =>
    (ObjectProperty.ι _).mapIso (T''.functor.mapIso ((bcIsoMx hc a'' ha'' hℓ).app X) ≪≫ T''.counitIso.app _)
  refine ⟨(LinearEquiv.baseChange E E'' _ _ (homLinNN hℓ hc A B)).trans
    (f₂.trans ((homModuleSplitEquiv _ _).symm.trans
      ((homModuleCongr (i A).symm (i B).symm).trans (homLinSS a'' ha'' hℓ _ _).symm))), fun c f => ?_⟩
  exact homLin_canon (bcHCmx hc a'' ha'' ℓ) (Equivalence.E_EGel hℓ) _ (Compat.targetEquivCardTwo hc).functor
    (qBCnsRel E D.L E'' (D.sqrtExt hc).card_gal) T'' (bcIsoMx hc a'' ha'' hℓ)
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl) (homLinSS a'' ha'' hℓ _ _) (fun _ _ => rfl) f c _
    (fun v => hf₂ c _ v)

/-- **T2, HC side**, case (c), `ℓ = 0`.  @census none (helper; clause `RQ2-5.14-C5`) -/
theorem homBC_HC_mxZ (A B : HC 0 E D) :
    ∃ e : E'' ⊗[E] (A ⟶ B) ≃ₗ[E'']
      ((bcHCmx hc a'' ha'' 0).obj A ⟶ (bcHCmx hc a'' ha'' 0).obj B),
      ∀ (c : E'') (f : A ⟶ B), e (c ⊗ₜ f) = c • (bcHCmx hc a'' ha'' 0).map f := by
  let G := Cyclic.E_ECyc (D := D) ⋙ (Compat.targetEquivCardTwoZ hc).functor
  obtain ⟨f₂, hf₂⟩ := homModule_baseChange_ns E'' (G.obj A).obj (G.obj B).obj
  let T'' := Compat.targetEquivSplitZ a'' ha''
  let i := fun X : HC 0 E D =>
    (ObjectProperty.ι _).mapIso (T''.functor.mapIso ((bcIsoMxZ hc a'' ha'').app X) ≪≫ T''.counitIso.app _)
  refine ⟨(LinearEquiv.baseChange E E'' _ _ (homLinNNZ hc A B)).trans
    (f₂.trans ((homModuleSplitEquiv _ _).symm.trans
      ((homModuleCongr (i A).symm (i B).symm).trans (homLinSSZ a'' ha'' _ _).symm))), fun c f => ?_⟩
  exact homLin_canon (bcHCmx hc a'' ha'' 0) (Cyclic.E_ECyc) _ (Compat.targetEquivCardTwoZ hc).functor
    (RationalQuiver.RepNil.toSplitFunctor E'') T'' (bcIsoMxZ hc a'' ha'')
    (fun _ _ _ => LinearMap.ext fun _ => Subtype.ext rfl) (homLinSSZ a'' ha'' _ _) (fun _ _ => rfl) f c _
    (fun v => hf₂ c _ v)

end MxHC


end C5

/-! ## The proposition -/

/-- **Proposition** (`prop:basechange`).  `𝔼_E` is compatible with base change along `L_E/E` by
construction (the `L_E`-representation underlying `𝔼_E(M_E)` is `𝔼_{L_E}(L_E ⊗_E M_E)`), and for every
`ℓ ≥ 0`, every extension `E''/E` of fields of characteristic `0`, in each of the cases (a) `√-1 ∈ E`,
(b) `√-1 ∉ E''`, (c) `√-1 ∉ E` but `√-1 ∈ E''`: (T1) there is a natural isomorphism
`E'' ⊗_E 𝔼_E(M_E) ≅ 𝔼_{E''}(E'' ⊗_E M_E)` of functors `HC_λ(𝔤,K)_E → Rep^nil(Γ_{E''})`, whose
components are the canonical maps; (T2) the canonical maps `E'' ⊗_E Hom → Hom` are isomorphisms.

@census    RQ2-5.14
@source    prop:basechange
@clauses   RQ2-5.14-H1, RQ2-5.14-H2, RQ2-5.14-C1, RQ2-5.14-C2, RQ2-5.14-C3, RQ2-5.14-C4,
  RQ2-5.14-C5
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation).  `HC_λ(𝔤,K)_E` is `HC ℓ E D` (`EX-HC`); for `√-1 ∈ E` (resp. `E''`) the presentation
`L_E = E` (`ImagUnit.ofSplit`) is used.  `H1`: every `ℓ` as `ℓ ≥ 1` (`E_EGel`) and `ℓ = 0` (`E_ECyc`).
`H2`: the quiver-side base change is the relocated v1 construction (`qBCssRel`, `qBCnnRel`/`qBCnnC`,
`qBCnsRel`/`RepNil.toSplitFunctor`) read through the re-indexing; in case (b) the embedding
`L_E → L_{E''}` over `E → E''` is an instance argument (`Algebra D.L D''.L` with its scalar towers),
in case (c) `L_E → E''`.  `C1` is T3's `E_E_underlying_split` (`rfl`): vertex spaces and edge maps (`HEq`, the edge maps live over
the same spaces only definitionally).  `C2` is the conjunction below
(the HC-side base change `bcHC…` is the relocated construction through the identifications).
`C3`: `bcIso{SS,SSZ,NN,NNZ,Mx,MxZ}_app_ψ` — in all six shapes the vertex components of the (T1)
isomorphism are those of the relocated v1 isomorphism (`E_bc_*_iso`), i.e. the canonical maps (`bcVtx`).
`C4`: `homBC_split` (cases (a), (c)), `homBC_nn`/`homBC_nnZ` (case (b), in the `gelfandOfCardTwo`
presentation of `Rep^nil(Γ_E)`), each with the formula of the canonical map on `c ⊗ ψ`.  `C5` (the HC side of (T2), new): `homBC_HC_{ss,ssZ,nn,nnZ,mx,mxZ}`
show that the canonical map `E'' ⊗_E Hom(M_E, N_E) → Hom(E'' ⊗_E M_E, E'' ⊗_E N_E)`, `c ⊗ f ↦ c·(E'' ⊗ f)`,
is an `E''`-linear isomorphism, for all six shapes: the isomorphism is built from (T1), the quiver side of
(T2) and the equivalences `𝔼_E`, `𝔼_{E''}` as in the tex, and is shown to send `c ⊗ f` to `c·(E'' ⊗ f)`
(`homLin_canon`: naturality of the (T1) isomorphism plus the quiver-side formula).
-/
theorem basechange :
    (∀ (E : Type) [Field E] [CharZero E] (D : ImagUnit E) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (A : HC ℓ E D),
      (Equivalence.E_E_rep hℓ A).M = (Split.E_F_rep A.qi (A.qi.starInverses hℓ) hℓ).M ∧
        ∀ e : Fin 4, HEq ((Equivalence.E_E_rep hℓ A).φEdge e)
          ((Split.E_F_rep A.qi (A.qi.starInverses hℓ) hℓ).φEdge e)) ∧
    (∀ (E : Type) [Field E] [CharZero E] (a : E) (ha : a * a = -1)
        (E'' : Type) [Field E''] [CharZero E''] [Algebra E E''] (a'' : E'') (ha'' : a'' * a'' = -1),
      (∀ {ℓ : ℕ} (hℓ : 1 ≤ ℓ), Nonempty (bcHCss a ha a'' ha'' ℓ ⋙ Equivalence.E_EGel hℓ ≅
        Equivalence.E_EGel hℓ ⋙ bcQss a ha a'' ha'')) ∧
      Nonempty (bcHCss a ha a'' ha'' 0 ⋙ Cyclic.E_ECyc ≅ Cyclic.E_ECyc ⋙ bcQssZ a ha a'' ha'')) ∧
    (∀ (E : Type) [Field E] [CharZero E] (D : ImagUnit E)
        (E'' : Type) [Field E''] [CharZero E''] (D'' : ImagUnit E'')
        [Algebra E E''] [Algebra D.L D''.L] [Algebra E D''.L]
        [IsScalarTower E E'' D''.L] [IsScalarTower E D.L D''.L]
        (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) (hc'' : ∃ σ : D''.L ≃ₐ[E''] D''.L, D''.chi σ = -1),
      (∀ {ℓ : ℕ} (hℓ : 1 ≤ ℓ), Nonempty (bcHCnn hc hc'' ℓ ⋙ Equivalence.E_EGel hℓ ≅
        Equivalence.E_EGel hℓ ⋙ bcQnn hc hc'')) ∧
      Nonempty (bcHCnn hc hc'' 0 ⋙ Cyclic.E_ECyc ≅ Cyclic.E_ECyc ⋙ bcQnnZ hc hc'')) ∧
    (∀ (E : Type) [Field E] [CharZero E] (D : ImagUnit E) (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1)
        (E'' : Type) [Field E''] [CharZero E''] [Algebra D.L E''] (a'' : E'') (ha'' : a'' * a'' = -1),
      (∀ {ℓ : ℕ} (hℓ : 1 ≤ ℓ), Nonempty (bcHCmx hc a'' ha'' ℓ ⋙ Equivalence.E_EGel hℓ ≅
        Equivalence.E_EGel hℓ ⋙ bcQmx hc a'' ha'')) ∧
      Nonempty (bcHCmx hc a'' ha'' 0 ⋙ Cyclic.E_ECyc ≅ Cyclic.E_ECyc ⋙ bcQmxZ hc a'' ha'')) :=
  ⟨fun _ _ _ _ _ hℓ A => E_E_underlying_split hℓ A,
    fun _ _ _ a ha _ _ _ _ a'' ha'' => ⟨fun hℓ => ⟨bcIsoSS a ha a'' ha'' hℓ⟩, ⟨bcIsoSSZ a ha a'' ha''⟩⟩,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ hc hc'' => ⟨fun hℓ => ⟨bcIsoNN hc hc'' hℓ⟩, ⟨bcIsoNNZ hc hc''⟩⟩,
    fun _ _ _ _ hc _ _ _ _ a'' ha'' => ⟨fun hℓ => ⟨bcIsoMx hc a'' ha'' hℓ⟩, ⟨bcIsoMxZ hc a'' ha''⟩⟩⟩

end RationalQuivers.Gelfand.BaseChange
