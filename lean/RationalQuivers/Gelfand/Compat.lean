import RationalQuivers.Gelfand.Main

/-!
# The compatibility layer (stage T4, WP-11a): identifications of presentations

The native `𝔼_E` of stage T3 lives on `HC ℓ E D → Rep^nil(Γ_E)`.  The relocated engine and the split
construction are stated on other presentations: `HCEObj ℓ E D'` over a quadratic
`D' : SqrtNegOneExt E` with target `Rep^nil(gelfandOfCardTwo)`, and `HCLambda ℓ L_E` with target
`Rep^nil(gelfandSplit L_E)`.  This module gives the identifications between them (ruling `R-V2-3`
§1.1: thin adapters, the identity on the underlying modules, no second engine), for use by §5.3's
species form (`Species/Equivalence`), §5.4 (`Rational`), base change and `Meta/Crosswalk`.
*(2026-10-22, O-V2-6 round 3.)*  `Meta/Crosswalk.lean`, which used `targetEquivSplit(Z)`,
`targetEquivCardTwo(Z)`, `ofSqrtExt` and `hcEquivHCEObj`, was removed at `5485c9a` (2026-10-18).

* `reρEquiv`, `reρSubEquiv`: two rational quivers that differ only in their rational structure `ρ`,
  acting by the same permutations, have equivalent representation categories (identity on spaces
  and edges, `φ` transported).
* `targetEquivCardTwo(Z)`, `targetEquivSplit(Z)`: `Rep^nil(Γ_E)` in the engine's and the split
  presentation.
* `ofSqrtExt`: a quadratic `SqrtNegOneExt` over `E ∌ √-1`, with a square root of `-1` in it, is an
  `ImagUnit`.
* `hcEquivHCEObj`: `HC ℓ E D ≌ HCEObj ℓ E (D.sqrtExt h)` for `√-1 ∉ E`, from T3's bridges.
* `cyclicOfSign_eq_cyclicOfCardTwo`: the `ℓ = 0` companion of T0's
  `gelfandOfSign_eq_gelfandOfCardTwo` (plan risk R-3).

Placement: §5.3, directly after `Gelfand/Main.lean` (HELPER), because §5.3's `thm:speciesE` already
needs the re-indexing; plan rev 3a §6.2 lists the compat layer under `Rational.lean`, which keeps the
§5.4 claimants (disclosed in the T4 packet).

@census none (helper module)
-/

namespace RationalQuivers.Gelfand.Compat

open RationalQuivers.HC CategoryTheory

/-! ## Re-indexing along a change of rational structure -/

section Reindex

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable {Γ : RationalQuiver K L} {ρ' : Gal(L/K) →* RQuiver.Aut Γ.toRQuiver}
variable (hV : ∀ (σ : Gal(L/K)) (v : Γ.V), σ • v = (σ • EssSurj.wV ρ' v : (Γ.withρ ρ').V))
  (hE : ∀ (σ : Gal(L/K)) (e : Γ.E), σ • e = (σ • EssSurj.wE ρ' e : (Γ.withρ ρ').E))

/-- A morphism of representations, re-indexed: the same components.  @census none (helper) -/
def reρHom {M N : RationalQuiver.Rep Γ} (f : RationalQuiver.Rep.Hom M N) :
    RationalQuiver.Rep.Hom (M.reρ hV hE) (N.reρ hV hE) where
  ψ := f.ψ
  edge := f.edge
  rational σ v m := by
    show f.ψ _ (M.eqCast (hV σ v) (M.φ σ v m)) = N.eqCast (hV σ v) (N.φ σ v (f.ψ v m))
    rw [EssSurj.eqCast_natural' f.ψ, f.rational]

/-- A finite-dimensional representation, re-indexed.  @census none (helper) -/
noncomputable def reρFD (M : RationalQuiver.FDRep Γ) : RationalQuiver.FDRep (Γ.withρ ρ') where
  toRep := M.toRep.reρ hV hE
  finiteDimensional := M.finiteDimensional

/-- Re-indexing as a functor.  @census none (helper) -/
noncomputable def reρFunctor : RationalQuiver.FDRep Γ ⥤ RationalQuiver.FDRep (Γ.withρ ρ') where
  obj := reρFD hV hE
  map f := reρHom hV hE f
  map_id _ := RationalQuiver.Rep.Hom.ext rfl
  map_comp _ _ := RationalQuiver.Rep.Hom.ext rfl

omit [IsGalois K L] [FiniteDimensional K L] in
/-- Two transports are one.  @census none (helper) -/
theorem eqCast_trans' (M : RationalQuiver.Rep Γ) {u v w : Γ.V} (h₁ : u = v) (h₂ : v = w)
    (x : M.M u) : M.eqCast h₂ (M.eqCast h₁ x) = M.eqCast (h₁.trans h₂) x := by
  subst h₁; subst h₂; rfl


include hV in
/-- The way back: re-index along `Γ.ρ` (`(Γ.withρ ρ').withρ Γ.ρ` is `Γ`).  @census none (helper) -/
theorem hV_symm : ∀ (σ : Gal(L/K)) (v : (Γ.withρ ρ').V),
    σ • v = (σ • EssSurj.wV Γ.ρ v : ((Γ.withρ ρ').withρ Γ.ρ).V) := fun σ v => (hV σ v).symm

include hE in
theorem hE_symm : ∀ (σ : Gal(L/K)) (e : (Γ.withρ ρ').E),
    σ • e = (σ • EssSurj.wE Γ.ρ e : ((Γ.withρ ρ').withρ Γ.ρ).E) := fun σ e => (hE σ e).symm

/-- **Re-indexing is an equivalence** `Rep(Γ) ≌ Rep(Γ.withρ ρ')`, the identity on spaces and edges.
@census none (helper) -/
noncomputable def reρEquiv : RationalQuiver.FDRep Γ ≌ RationalQuiver.FDRep (Γ.withρ ρ') where
  functor := reρFunctor hV hE
  inverse := (reρFunctor (Γ := Γ.withρ ρ') (ρ' := Γ.ρ) (hV_symm (Γ := Γ) (ρ' := ρ') hV) (hE_symm (Γ := Γ) (ρ' := ρ') hE) : RationalQuiver.FDRep (Γ.withρ ρ') ⥤ RationalQuiver.FDRep Γ)
  unitIso := NatIso.ofComponents (fun M => EssSurj.fdRepIsoOfComponents
      (M := M) (N := (reρFD (Γ := Γ.withρ ρ') (ρ' := Γ.ρ) (hV_symm (Γ := Γ) (ρ' := ρ') hV) (hE_symm (Γ := Γ) (ρ' := ρ') hE) (reρFD hV hE M) : RationalQuiver.FDRep Γ))
      ⟨fun _ => LinearMap.id, fun _ _ => rfl, fun σ v m =>
        (eqCast_trans' M.toRep (hV σ v) (hV_symm (Γ := Γ) (ρ' := ρ') hV σ v) (M.toRep.φ σ v m)).symm⟩
      (fun _ => LinearMap.id) (fun _ _ => rfl) (fun _ _ => rfl))
    (fun _ => RationalQuiver.Rep.Hom.ext rfl)
  counitIso := NatIso.ofComponents (fun M => EssSurj.fdRepIsoOfComponents
      (M := reρFD (Γ := Γ) (ρ' := ρ') hV hE (reρFD (Γ := Γ.withρ ρ') (ρ' := Γ.ρ) (hV_symm (Γ := Γ) (ρ' := ρ') hV) (hE_symm (Γ := Γ) (ρ' := ρ') hE) M)) (N := M)
      ⟨fun _ => LinearMap.id, fun _ _ => rfl, fun σ v m =>
        eqCast_trans' M.toRep (hV_symm (Γ := Γ) (ρ' := ρ') hV σ v) (hV σ v) (M.toRep.φ σ v m)⟩
      (fun _ => LinearMap.id) (fun _ _ => rfl) (fun _ _ => rfl))
    (fun _ => RationalQuiver.Rep.Hom.ext rfl)
  functor_unitIso_comp _ := RationalQuiver.Rep.Hom.ext rfl

/-- Re-indexing restricted to full subcategories that it preserves in both directions (explicit:
functor and inverse are the re-indexings, unit and counit have identity components).
@census none (helper) -/
noncomputable def reρSubEquiv (P : ObjectProperty (RationalQuiver.FDRep Γ))
    (P' : ObjectProperty (RationalQuiver.FDRep (Γ.withρ ρ')))
    (h₁ : ∀ M, P M → P' ((reρEquiv hV hE).functor.obj M))
    (h₂ : ∀ M, P' M → P ((reρEquiv hV hE).inverse.obj M)) :
    P.FullSubcategory ≌ P'.FullSubcategory where
  functor := P'.lift (P.ι ⋙ (reρEquiv hV hE).functor) (fun X => h₁ _ X.2)
  inverse := P.lift (P'.ι ⋙ (reρEquiv hV hE).inverse) (fun Y => h₂ _ Y.2)
  unitIso := NatIso.ofComponents (fun X => P.isoMk ((reρEquiv hV hE).unitIso.app X.obj))
    (fun _ => ObjectProperty.hom_ext _ (RationalQuiver.Rep.Hom.ext rfl))
  counitIso := NatIso.ofComponents (fun Y => P'.isoMk ((reρEquiv hV hE).counitIso.app Y.obj))
    (fun _ => ObjectProperty.hom_ext _ (RationalQuiver.Rep.Hom.ext rfl))
  functor_unitIso_comp _ := ObjectProperty.hom_ext _ (RationalQuiver.Rep.Hom.ext rfl)

@[simp] theorem reρSubEquiv_functor_obj_obj (P : ObjectProperty (RationalQuiver.FDRep Γ))
    (P' : ObjectProperty (RationalQuiver.FDRep (Γ.withρ ρ')))
    (h₁ : ∀ M, P M → P' ((reρEquiv hV hE).functor.obj M))
    (h₂ : ∀ M, P' M → P ((reρEquiv hV hE).inverse.obj M)) (X : P.FullSubcategory) :
    ((reρSubEquiv hV hE P P' h₁ h₂).functor.obj X).obj = reρFD hV hE X.obj := rfl

end Reindex

/-! ## The target, in the engine's and the split presentation -/

section Target

variable {E : Type} [Field E] [CharZero E] {D : ImagUnit E}

/-- **`Rep^nil(Γ_E) ≌ Rep^nil(gelfandOfCardTwo)`**, `ℓ ≥ 1`, `√-1 ∉ E` (T1's
`gelfandOfSign = gelfandOfCardTwo`, on representations; object map T3's `EssSurj.toCardTwo`).
@census none (helper) -/
noncomputable def targetEquivCardTwo (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) :
    (Equivalence.RepNilGel D).FullSubcategory ≌
      RationalStructure.RepNilQ (Dq := D.sqrtExt hc) (D.sqrtExt hc).card_gal :=
  reρSubEquiv (EssSurj.gammaE_smul_vertex_cardTwo hc) (EssSurj.gammaE_smul_edge_cardTwo hc)
    (Equivalence.RepNilGel D) (RationalStructure.RepNilRelQ (Dq := D.sqrtExt hc) (D.sqrtExt hc).card_gal)
    (fun _ h => h) (fun _ h => h)

/-- **`Rep^nil(Γ_E) ≌ Rep^nil(cyclicOfCardTwo)`**, `ℓ = 0`, `√-1 ∉ E` (object map T3's
`Cyclic.toCardTwoZ`).  @census none (helper) -/
noncomputable def targetEquivCardTwoZ (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) :
    (RepNilTarget D 0).FullSubcategory ≌
      Cyclic.RepNilCycQ (Dq := D.sqrtExt hc) (D.sqrtExt hc).card_gal :=
  reρSubEquiv (Cyclic.cycE_smul_vertex_cardTwo hc) (Cyclic.cycE_smul_edge_cardTwo hc)
    (RepNilTarget D 0) (RationalQuiver.RepNil (Cyclic.cyclicQ (Dq := D.sqrtExt hc) (D.sqrtExt hc).card_gal))
    (fun _ h => h) (fun _ h => h)

end Target

section TargetSplit

variable {E : Type} [Field E] [CharZero E] (a : E) (ha : a * a = -1)

/-- **`Rep^nil(Γ_E) ≌ Rep^nil(gelfandSplit E)`**, `ℓ ≥ 1`, `√-1 = a ∈ E` (`L_E = E`, `G_E = 1`, so
both rational structures are trivial).  @census none (helper) -/
noncomputable def targetEquivSplit :
    (Equivalence.RepNilGel (ImagUnit.ofSplit a ha)).FullSubcategory ≌ (RepNilRelSplit E).FullSubcategory :=
  reρSubEquiv (Γ := RationalQuiver.gelfandOfSign E (ImagUnit.ofSplit a ha).L (ImagUnit.ofSplit a ha).chiHom)
    (ρ' := (gelfandSplit E).ρ)
    (fun σ v => by
      obtain rfl : σ = 1 := AlgEquiv.ext fun x => σ.commutes x
      rw [one_smul, one_smul])
    (fun σ e => by
      obtain rfl : σ = 1 := AlgEquiv.ext fun x => σ.commutes x
      rw [one_smul, one_smul])
    (Equivalence.RepNilGel (ImagUnit.ofSplit a ha)) (RepNilRelSplit E) (fun _ h => h) (fun _ h => h)

/-- **`Rep^nil(Γ_E) ≌ Rep^nil(cyclicSplit E)`**, `ℓ = 0`, `√-1 = a ∈ E`.  @census none (helper) -/
noncomputable def targetEquivSplitZ :
    (RepNilTarget (ImagUnit.ofSplit a ha) 0).FullSubcategory ≌
      (RationalQuiver.RepNil (cyclicSplit E)).FullSubcategory :=
  reρSubEquiv (Γ := GammaE (ImagUnit.ofSplit a ha) 0) (ρ' := (cyclicSplit E).ρ)
    (fun σ v => by
      obtain rfl : σ = 1 := AlgEquiv.ext fun x => σ.commutes x
      rw [one_smul, one_smul])
    (fun σ e => by
      obtain rfl : σ = 1 := AlgEquiv.ext fun x => σ.commutes x
      rw [one_smul, one_smul])
    (RepNilTarget (ImagUnit.ofSplit a ha) 0) (RationalQuiver.RepNil (cyclicSplit E))
    (fun _ h => h) (fun _ h => h)

end TargetSplit

/-! ## A quadratic `SqrtNegOneExt` over an `E ∌ √-1` is an `ImagUnit` -/

section OfSqrtExt

variable {E : Type} [Field E] [CharZero E]

/-- For `√-1 ∉ E`, a square root `s` of `-1` in a quadratic `D' : SqrtNegOneExt E` generates it.
The root is an explicit argument since the v2 amendment T4-a1 (`SqrtNegOneExt` is root-free).
@census none (helper) -/
theorem adjoin_sqrt_eq_top (D' : SqrtNegOneExt E) (s : D'.carrier) (hs : s * s = -1)
    (h : ¬ ∃ a : E, a * a = -1) :
    Algebra.adjoin E {s} = ⊤ := by
  set A := Algebra.adjoin E {s}
  have h2 : Module.finrank E D'.carrier = 2 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact D'.card_gal
  have hmem : s ∈ A := Algebra.subset_adjoin rfl
  have hle : Module.finrank E A ≤ 2 := h2 ▸ Submodule.finrank_le (Subalgebra.toSubmodule A)
  have hne1 : Module.finrank E A ≠ 1 := by
    intro h1
    rw [Subalgebra.finrank_eq_one_iff.mp h1] at hmem
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hmem
    exact h ⟨a, (algebraMap E D'.carrier).injective (by
      rw [map_mul, ha, hs, map_neg, map_one])⟩
  have hpos : 0 < Module.finrank E A := Module.finrank_pos
  have hA : Module.finrank E (Subalgebra.toSubmodule A) = Module.finrank E D'.carrier := by
    show Module.finrank E A = _
    omega
  exact Algebra.toSubmodule_eq_top.1 (Submodule.eq_top_of_finrank_eq hA)

/-- **A quadratic `D' : SqrtNegOneExt E` over `E ∌ √-1`, with a square root `s` of `-1` in it, as
an `ImagUnit`**: `L := D'.carrier`, `i := s`.  Its bridge `sqrtExt` is `D'` again
(`ofSqrtExt_sqrtExt`).  The root is an explicit argument since the v2 amendment T4-a1: a general
`D'` need not contain `√-1`.  @census none (helper) -/
noncomputable def ofSqrtExt (D' : SqrtNegOneExt E) (s : D'.carrier) (hs : s * s = -1)
    (h : ¬ ∃ a : E, a * a = -1) : ImagUnit E where
  L := D'.carrier
  i := s
  i_mul_i := hs
  adjoin_eq_top := adjoin_sqrt_eq_top D' s hs h

theorem ofSqrtExt_sqrtExt (D' : SqrtNegOneExt E) (s : D'.carrier) (hs : s * s = -1)
    (h : ¬ ∃ a : E, a * a = -1)
    (hc : ∃ σ : (ofSqrtExt D' s hs h).L ≃ₐ[E] (ofSqrtExt D' s hs h).L,
      (ofSqrtExt D' s hs h).chi σ = -1) :
    (ofSqrtExt D' s hs h).sqrtExt hc = D' := rfl

end OfSqrtExt

/-! ## `HC ℓ E D ≌ HCEObj ℓ E (D.sqrtExt h)` for `√-1 ∉ E` -/

section HCEObjEquiv

variable {E : Type} [Field E] [CharZero E] {D : ImagUnit E} {ℓ : ℕ}
variable (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1)

/-- T3's bridge `HC → HCEObj` as a functor (identity on modules and maps).  @census none (helper) -/
noncomputable def toHCEObjFunctor : HC ℓ E D ⥤ HCEObj ℓ E (D.sqrtExt h) where
  obj A := A.toHCEObj h
  map f := HC.Hom.toHCEHom h f
  map_id _ := HCEHom.hom_ext rfl
  map_comp _ _ := HCEHom.hom_ext rfl

instance : (toHCEObjFunctor (ℓ := ℓ) h).Faithful where
  map_injective {_ _} f g hfg := by
    apply HC.Hom.ext'
    exact congrArg HCEHom.toLinearMap hfg

instance : (toHCEObjFunctor (ℓ := ℓ) h).Full where
  map_surjective {_ _} g := ⟨HC.ofHCEHom g, HCEHom.hom_ext rfl⟩

instance : (toHCEObjFunctor (ℓ := ℓ) h).EssSurj where
  mem_essImage B := ⟨B.toHC, ⟨eqToIso (HCEObj.toHC_toHCEObj B)⟩⟩

/-- T3's bridge `HCEObj → HC` as a functor (identity on modules and maps).  @census none (helper) -/
noncomputable def ofHCEObjFunctor : HCEObj ℓ E (D.sqrtExt h) ⥤ HC ℓ E D where
  obj B := B.toHC
  map f := HC.ofHCEHom f
  map_id _ := HC.Hom.ext' rfl
  map_comp _ _ := HC.Hom.ext' rfl

/-- The identity of `B`, read from `(B.toHC).toHCEObj h` (same module, the conjugation of the
former is `galActOf c`, which is `B`'s, `HCEObj.galActOf_conj`).  @census none (helper) -/
noncomputable def toHCtoHCEObjIso (B : HCEObj ℓ E (D.sqrtExt h)) : B.toHC.toHCEObj h ≅ B where
  hom := ⟨LinearMap.id, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ hv => hv,
    fun v => HCEObj.galActOf_conj B v⟩
  inv := ⟨LinearMap.id, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ hv => hv,
    fun v => (HCEObj.galActOf_conj B v).symm⟩
  hom_inv_id := HCEHom.hom_ext rfl
  inv_hom_id := HCEHom.hom_ext rfl

/-- **`HC_λ(𝔤,K)_E ≌ HCEObj ℓ E (D.sqrtExt h)`**, `√-1 ∉ E`: the two presentations of
`def:HClambdaE` (descent datum as a property over all `σ ∈ G_E`, resp. as the conjugation `c`).
An identification of presentations (`R-V2-3` §1.1); both functors are T3's bridges and both round
trips are the identity on modules.  @census none (helper) -/
noncomputable def hcEquivHCEObj : HC ℓ E D ≌ HCEObj ℓ E (D.sqrtExt h) where
  functor := toHCEObjFunctor h
  inverse := ofHCEObjFunctor h
  unitIso := NatIso.ofComponents (fun A => Iso.refl A) (fun _ => HC.Hom.ext' rfl)
  counitIso := NatIso.ofComponents (fun B => toHCtoHCEObjIso h B) (fun _ => HCEHom.hom_ext rfl)
  functor_unitIso_comp _ := HCEHom.hom_ext rfl

theorem hcEquivHCEObj_functor : (hcEquivHCEObj (ℓ := ℓ) h).functor = toHCEObjFunctor h := rfl

theorem hcEquivHCEObj_inverse : (hcEquivHCEObj (ℓ := ℓ) h).inverse = ofHCEObjFunctor h := rfl

end HCEObjEquiv

/-! ## `Γ_E` for a quadratic `L_E/E` is the quiver of `ex:gelfand` resp. `ex:cyclic` -/

section CardTwo

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

/-- For a quadratic `L/K` and an **injective** sign character `χ`, `cyclicOfSign χ` is, as a
structure, the quiver `cyclicOfCardTwo K L h` of `ex:cyclic` (the `ℓ = 0` companion of T0's
`gelfandOfSign_eq_gelfandOfCardTwo`, plan risk R-3).  @census none (helper) -/
theorem cyclicOfSign_eq_cyclicOfCardTwo (h : Nat.card Gal(L/K) = 2) {χ : Gal(L/K) →* ℤˣ}
    (hχ : Function.Injective χ) :
    RationalQuiver.cyclicOfSign K L χ = RationalQuiver.cyclicOfCardTwo K L h := by
  have hρ : (RationalQuiver.cyclicOfSign K L χ).ρ = (RationalQuiver.cyclicOfCardTwo K L h).ρ := by
    ext1 σ
    by_cases hσ : σ = 1
    · subst hσ; rw [map_one, map_one]
    · have hχσ : χ σ ≠ 1 := fun h1 => hσ (hχ (h1.trans (map_one χ).symm))
      rw [show (RationalQuiver.cyclicOfSign K L χ).ρ σ = if χ σ = 1 then 1 else RQuiver.cyclicSignSwap
        from rfl, if_neg hχσ]
      letI := Classical.decEq Gal(L/K)
      have hsw : RQuiver.cyclicSignSwap = RQuiver.cyclicSwap := by
        refine CategoryTheory.Aut.ext ?_
        refine RQuiver.Hom.ext ?_ ?_ <;> (funext x; revert x; decide)
      rw [hsw]
      exact ((show (RationalQuiver.cyclicOfCardTwo K L h).ρ σ
        = if σ = 1 then 1 else RQuiver.cyclicSwap from rfl).trans (if_neg hσ)).symm
  unfold RationalQuiver.cyclicOfSign RationalQuiver.ofSign at hρ ⊢
  unfold RationalQuiver.cyclicOfCardTwo at hρ ⊢
  congr 1

end CardTwo

/-! ## The native `𝔼_E` in the engine's and the split presentation (functors)

Used by `Gelfand/BaseChange/Native.lean`.  *(2026-10-22, O-V2-6 round 3.)*  The WP-11a text
also named `Meta/Crosswalk.lean` (removed at `5485c9a`, 2026-10-18) as a user; that file never
referenced a declaration of this section. -/

section EngineNative
variable {E : Type} [Field E] [CharZero E] {D : ImagUnit E} {ℓ : ℕ}
variable (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1)

/-- The engine's `𝔼(B)` is T3's native `𝔼_E(B.toHC)`, re-indexed to `gelfandOfCardTwo`: identity
components; the rational structures agree by T3's `E_E_φ_eq_phiC`, `phiC_toHC`.  @census none (helper) -/
noncomputable def engineNativeApp (hℓ : 1 ≤ ℓ) (B : HCEObj ℓ E (D.sqrtExt hc))
    (hB : RationalStructure.ObjSpec (D.sqrtExt hc).card_gal hℓ B) :
    Equivalence.E_Q_obj (D.sqrtExt hc).card_gal hℓ B hB ≅
      (targetEquivCardTwo hc).functor.obj ((Equivalence.E_EGel hℓ).obj B.toHC) :=
  ObjectProperty.isoMk _ (EssSurj.fdRepIsoOfComponents
    ⟨fun _ => LinearMap.id, fun _ _ => rfl, fun σ v m => by
      refine Subtype.ext ?_
      change Equivalence.galAct hℓ B σ v m.1
        = (((Equivalence.E_E_rep hℓ B.toHC).eqCast (EssSurj.gammaE_smul_vertex_cardTwo hc σ v)
            ((Equivalence.E_E_rep hℓ B.toHC).φ σ v m) : Split.V3 B.toHC.qi _)).1
      rw [EssSurj.E_E_rep_eqCast_val]
      show Equivalence.galAct hℓ B σ v m.1 = RationalStructure.E_E_φ hℓ B.toHC σ v m.1
      rcases D.chi_cases σ with hσ | hσ
      · obtain rfl := D.eq_one_of_chi_one hσ
        rw [RationalStructure.E_E_φ_of_one hℓ _ hσ]
        exact Equivalence.galAct_one hℓ B v m.1
      · rw [RationalStructure.E_E_φ_eq_phiC hℓ _ hσ, RationalStructure.phiC_toHC,
          Equivalence.galAct_of_ne hℓ B (D.chi_eq_neg_one_iff_ne_one.mp hσ)]⟩
    (fun _ => LinearMap.id) (fun _ _ => rfl) (fun _ _ => rfl))

/-- **Engine ↔ native**, `ℓ ≥ 1`, `√-1 ∉ E`: the relocated engine's functor is T3's native `𝔼_E`
through the bridges and the re-indexing.  @census none (helper) -/
noncomputable def engineNative (hℓ : 1 ≤ ℓ)
    (h' : RationalStructure.E_QSpec (D.sqrtExt hc).card_gal hℓ) :
    Equivalence.E_QFunctor (D.sqrtExt hc).card_gal hℓ h' ≅
      ofHCEObjFunctor hc ⋙ Equivalence.E_EGel hℓ ⋙ (targetEquivCardTwo hc).functor :=
  NatIso.ofComponents (fun B => engineNativeApp hc hℓ B (h'.1 B))
    (fun _ => ObjectProperty.hom_ext _ (RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)))

/-- `ℓ = 0`: the engine's object is T3's native one (`φ_c = c`, `phiCyc_eq_conj`), re-indexed.
@census none (helper) -/
noncomputable def engineNativeAppZ (B : HCEObj 0 E (D.sqrtExt hc))
    (hB : Cyclic.ObjSpecC (D.sqrtExt hc).card_gal B) :
    Cyclic.E_Cyc_obj (D.sqrtExt hc).card_gal B hB ≅
      (targetEquivCardTwoZ hc).functor.obj (Cyclic.E_ECyc.obj B.toHC) :=
  ObjectProperty.isoMk _ (EssSurj.fdRepIsoOfComponents
    ⟨fun _ => LinearMap.id, fun _ _ => rfl, fun σ v m => by
      refine Subtype.ext ?_
      change Cyclic.galActC B σ v m.1
        = (((Cyclic.E_Cyc_repZ B.toHC).eqCast (Cyclic.cycE_smul_vertex_cardTwo hc σ v)
            ((Cyclic.E_Cyc_repZ B.toHC).φ σ v m) : Cyclic.V2Z B.toHC _)).1
      rw [Cyclic.E_Cyc_repZ_eqCast_val]
      show Cyclic.galActC B σ v m.1 = B.toHC.galAct σ m.1
      rcases D.chi_cases σ with hσ | hσ
      · obtain rfl := D.eq_one_of_chi_one hσ
        rw [Cyclic.galActC_one, HC.galAct_of_chi_one _ hσ]
      · rw [Cyclic.galActC_of_ne B (D.chi_eq_neg_one_iff_ne_one.mp hσ),
          HCEObj.toHC_galAct_neg _ hσ]
        exact Cyclic.phiCyc_eq_conj B v m.1 m.2⟩
    (fun _ => LinearMap.id) (fun _ _ => rfl) (fun _ _ => rfl))

/-- **Engine ↔ native**, `ℓ = 0`, `√-1 ∉ E`.  @census none (helper) -/
noncomputable def engineNativeZ (h' : Cyclic.E_CycSpec (D.sqrtExt hc).card_gal) :
    Cyclic.E_CycFunctor (D.sqrtExt hc).card_gal h' ≅
      ofHCEObjFunctor hc ⋙ Cyclic.E_ECyc ⋙ (targetEquivCardTwoZ hc).functor :=
  NatIso.ofComponents (fun B => engineNativeAppZ hc B (h'.1 B))
    (fun _ => ObjectProperty.hom_ext _ (RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)))

end EngineNative

section SplitNative
variable {E : Type} [Field E] [CharZero E] (a : E) (ha : a * a = -1) {ℓ : ℕ}

/-- `√-1 = a ∈ E`: native `𝔼_E(A)`, re-indexed to `gelfandSplit E`, is T2's split `𝔼_E` of
`A` read in `HC_λ(𝔤,K)_{L_E}` (`G_E = 1`; identity components).  @census none (helper) -/
noncomputable def splitNativeApp (hℓ : 1 ≤ ℓ) (A : HC ℓ E (ImagUnit.ofSplit a ha)) :
    (targetEquivSplit a ha).functor.obj ((Equivalence.E_EGel hℓ).obj A) ≅
      (Split.E_FNil ℓ hℓ).obj ((Split.hcLambdaToF E ℓ).obj ((HC.lambdaEquiv ⟨a, ha⟩).functor.obj A)) :=
  ObjectProperty.isoMk _ (EssSurj.fdRepIsoOfComponents
    ⟨fun _ => LinearMap.id, fun _ _ => rfl, fun σ v m => by
      obtain rfl : σ = 1 := AlgEquiv.ext fun x => σ.commutes x
      exact EssSurj.rational_one
        (M := ((targetEquivSplit a ha).functor.obj ((Equivalence.E_EGel hℓ).obj A)).obj.toRep)
        (N := ((Split.E_FNil ℓ hℓ).obj ((Split.hcLambdaToF E ℓ).obj
          ((HC.lambdaEquiv ⟨a, ha⟩).functor.obj A))).obj.toRep) (fun _ => LinearMap.id) v m⟩
    (fun _ => LinearMap.id) (fun _ _ => rfl) (fun _ _ => rfl))

/-- **Split ↔ native**, `ℓ ≥ 1`, `√-1 ∈ E`.  @census none (helper) -/
noncomputable def splitNative (hℓ : 1 ≤ ℓ) :
    Equivalence.E_EGel (D := ImagUnit.ofSplit a ha) hℓ ⋙ (targetEquivSplit a ha).functor ≅
      (HC.lambdaEquiv (D := ImagUnit.ofSplit a ha) (ℓ := ℓ) ⟨a, ha⟩).functor ⋙
        Split.hcLambdaToF E ℓ ⋙ Split.E_FNil ℓ hℓ :=
  NatIso.ofComponents (fun A => splitNativeApp a ha hℓ A)
    (fun _ => ObjectProperty.hom_ext _ (RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)))

/-- `ℓ = 0`, `√-1 = a ∈ E`, at an object.  @census none (helper) -/
noncomputable def splitNativeAppZ (A : HC 0 E (ImagUnit.ofSplit a ha)) :
    (targetEquivSplitZ a ha).functor.obj (Cyclic.E_ECyc.obj A) ≅
      Split.E_CycSplitFunctor.obj ((Split.hcLambdaToF E 0).obj ((HC.lambdaEquiv ⟨a, ha⟩).functor.obj A)) :=
  ObjectProperty.isoMk _ (EssSurj.fdRepIsoOfComponents
    ⟨fun _ => LinearMap.id, fun _ _ => rfl, fun σ v m => by
      obtain rfl : σ = 1 := AlgEquiv.ext fun x => σ.commutes x
      exact EssSurj.rational_one
        (M := ((targetEquivSplitZ a ha).functor.obj (Cyclic.E_ECyc.obj A)).obj.toRep)
        (N := (Split.E_CycSplitFunctor.obj ((Split.hcLambdaToF E 0).obj
          ((HC.lambdaEquiv ⟨a, ha⟩).functor.obj A))).obj.toRep) (fun _ => LinearMap.id) v m⟩
    (fun _ => LinearMap.id) (fun _ _ => rfl) (fun _ _ => rfl))

/-- **Split ↔ native**, `ℓ = 0`, `√-1 ∈ E`.  @census none (helper) -/
noncomputable def splitNativeZ :
    Cyclic.E_ECyc (D := ImagUnit.ofSplit a ha) ⋙ (targetEquivSplitZ a ha).functor ≅
      (HC.lambdaEquiv (D := ImagUnit.ofSplit a ha) (ℓ := 0) ⟨a, ha⟩).functor ⋙
        Split.hcLambdaToF E 0 ⋙ Split.E_CycSplitFunctor :=
  NatIso.ofComponents (fun A => splitNativeAppZ a ha A)
    (fun _ => ObjectProperty.hom_ext _ (RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)))

end SplitNative

end RationalQuivers.Gelfand.Compat
