module

public import RQPalomar.Statement
public import RationalQuivers.Gelfand.Main

/-!
# Bridge: the statement-surface copies (`RQStatement.*`) ↔ the formalization (`RationalQuivers.*`)

`RQStatementDefs` is a verbatim copy of the definitions of `Challenge.lean`, so its constants are
the Challenge's constants (Comparator checks this).  This file builds equivalences of categories
between those copies and the formalization's own `HC` and `Rep^nil(Γ_E)`, so that Theorem B of
the formalization (`RationalQuivers.Gelfand.gelfand_equivalence`) transfers.
-/

@[expose] public section

namespace RQBridge

noncomputable section

open CategoryTheory

/-! ## `L_E`, weight data, `HC` -/

section HCSide

variable {E : Type} [Field E]

/-- The datum `L_E = E(√-1)`, read in the formalization. -/
abbrev imag (D : RQStatement.HC.ImagUnit E) : RationalQuivers.HC.ImagUnit E where
  L := D.L
  field := D.field
  algebra := D.algebra
  i := D.i
  i_mul_i := D.i_mul_i
  adjoin_eq_top := D.adjoin_eq_top

universe u v

def wdTo {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]
    (W : RQStatement.HC.WeightData F M) : RationalQuivers.HC.WeightData F M where
  comp := W.comp
  isInternal := W.isInternal
  H := W.H
  X := W.X
  Y := W.Y
  H_apply := W.H_apply
  X_mem := W.X_mem
  Y_mem := W.Y_mem
  lie_H_X := W.lie_H_X
  lie_H_Y := W.lie_H_Y
  lie_X_Y := W.lie_X_Y

def wdFrom {F : Type u} [Field F] {M : Type v} [AddCommGroup M] [Module F M]
    (W : RationalQuivers.HC.WeightData F M) : RQStatement.HC.WeightData F M where
  comp := W.comp
  isInternal := W.isInternal
  H := W.H
  X := W.X
  Y := W.Y
  H_apply := W.H_apply
  X_mem := W.X_mem
  Y_mem := W.Y_mem
  lie_H_X := W.lie_H_X
  lie_H_Y := W.lie_H_Y
  lie_X_Y := W.lie_X_Y

variable [CharZero E] {D : RQStatement.HC.ImagUnit E} {ℓ : ℕ}

theorem chi_eq (σ : D.L ≃ₐ[E] D.L) : (imag D).chi σ = D.chi σ := by
  unfold RationalQuivers.HC.ImagUnit.chi RQStatement.HC.ImagUnit.chi
  by_cases h : σ D.i = D.i
  · simp only [imag, h, ite_true]
  · simp only [imag, h, ite_false]

def hcTo (A : RQStatement.HC.HC ℓ E D) : RationalQuivers.HC.HC ℓ E (imag D) where
  formAddCommGroup := A.formAddCommGroup
  formModule := A.formModule
  addCommGroup := A.addCommGroup
  module := A.module
  form := A.form
  carrier := A.carrier
  baseChange := A.baseChange
  weight := wdTo A.weight
  gic := A.gic
  galCompat σ := by
    have h := A.galCompat σ
    rw [← chi_eq] at h
    exact ⟨h.comp, h.H, h.X_one, h.Y_one, h.X_neg, h.Y_neg⟩
  admissible := A.admissible
  centralCharacter := A.centralCharacter
  fg := A.fg

def hcFrom (A : RationalQuivers.HC.HC ℓ E (imag D)) : RQStatement.HC.HC ℓ E D where
  formAddCommGroup := A.formAddCommGroup
  formModule := A.formModule
  addCommGroup := A.addCommGroup
  module := A.module
  form := A.form
  carrier := A.carrier
  baseChange := A.baseChange
  weight := @wdFrom D.L _ A.carrier _ A.module A.weight
  gic := A.gic
  galCompat σ := by
    have h := A.galCompat σ
    rw [chi_eq] at h
    obtain ⟨a, b, c, d, e, f⟩ := h
    exact @RQStatement.HC.GalCompat.mk E _ D A.carrier _ A.module _ _ _ a b c d e f
  admissible := A.admissible
  centralCharacter := A.centralCharacter
  fg := A.fg

def hcFunctor : RQStatement.HC.HC ℓ E D ⥤ RationalQuivers.HC.HC ℓ E (imag D) where
  obj := hcTo
  map f := ⟨f.toLinearMap, f.map_H, f.map_X, f.map_Y, f.map_comp, f.map_gal⟩

def hcInverse : RationalQuivers.HC.HC ℓ E (imag D) ⥤ RQStatement.HC.HC ℓ E D where
  obj := hcFrom
  map f := ⟨f.toLinearMap, f.map_H, f.map_X, f.map_Y, f.map_comp, f.map_gal⟩

/-- `HC_λ(𝔤,K)_E` of the statement ≌ `HC_λ(𝔤,K)_E` of the formalization. -/
def hcEquiv : RQStatement.HC.HC ℓ E D ≌ RationalQuivers.HC.HC ℓ E (imag D) where
  functor := hcFunctor
  inverse := hcInverse
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  functor_unitIso_comp _ := by apply RationalQuivers.HC.HC.Hom.ext'; rfl

end HCSide

/-! ## Quivers, rational quivers, representations -/

section QuiverSide

universe u

abbrev rq (Γ : RQStatement.RQuiver.{u}) : RationalQuivers.RQuiver.{u} :=
  ⟨Γ.V, Γ.E, Γ.source, Γ.target, Γ.finite_V, Γ.finite_E⟩

def rqHom {Γ Γ' : RQStatement.RQuiver.{u}} (f : RQStatement.RQuiver.Hom Γ Γ') :
    RationalQuivers.RQuiver.Hom (rq Γ) (rq Γ') :=
  ⟨f.onV, f.onE, f.onV_source, f.onV_target⟩

def rqAut (Γ : RQStatement.RQuiver.{u}) :
    RQStatement.RQuiver.Aut Γ →* RationalQuivers.RQuiver.Aut (rq Γ) where
  toFun a :=
    CategoryTheory.Aut.of
      { hom := rqHom a.asIso.hom
        inv := rqHom a.asIso.inv
        hom_inv_id := RationalQuivers.RQuiver.Hom.ext
          (congrArg RQStatement.RQuiver.Hom.onV a.asIso.hom_inv_id)
          (congrArg RQStatement.RQuiver.Hom.onE a.asIso.hom_inv_id)
        inv_hom_id := RationalQuivers.RQuiver.Hom.ext
          (congrArg RQStatement.RQuiver.Hom.onV a.asIso.inv_hom_id)
          (congrArg RQStatement.RQuiver.Hom.onE a.asIso.inv_hom_id) }
  map_one' := rfl
  map_mul' _ _ := rfl

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

abbrev rat (Γ : RQStatement.RationalQuiver K L) : RationalQuivers.RationalQuiver K L where
  galois := Γ.galois
  toRQuiver := rq Γ.toRQuiver
  ρ := (rqAut Γ.toRQuiver).comp Γ.ρ
  smooth_V := Γ.smooth_V
  smooth_E := Γ.smooth_E

variable {Γ : RQStatement.RationalQuiver K L}

def repTo (M : RQStatement.RationalQuiver.Rep Γ) : RationalQuivers.RationalQuiver.Rep (rat Γ) where
  M := M.M
  φ := M.φ
  semilinear := M.semilinear
  cocycle := M.cocycle
  smooth := M.smooth
  φEdge := M.φEdge
  edge_equivariance := M.edge_equivariance

def repFrom (M : RationalQuivers.RationalQuiver.Rep (rat Γ)) : RQStatement.RationalQuiver.Rep Γ where
  M := M.M
  φ := M.φ
  semilinear := M.semilinear
  cocycle := M.cocycle
  smooth := M.smooth
  φEdge := M.φEdge
  edge_equivariance := M.edge_equivariance

def fdFunctor : RQStatement.RationalQuiver.FDRep Γ ⥤ RationalQuivers.RationalQuiver.FDRep (rat Γ) where
  obj M := ⟨repTo M.toRep, M.finiteDimensional⟩
  map f := ⟨f.ψ, f.edge, f.rational⟩

def fdInverse : RationalQuivers.RationalQuiver.FDRep (rat Γ) ⥤ RQStatement.RationalQuiver.FDRep Γ where
  obj M := ⟨repFrom M.toRep, M.finiteDimensional⟩
  map f := ⟨f.ψ, f.edge, f.rational⟩

def fdEquiv : RQStatement.RationalQuiver.FDRep Γ ≌ RationalQuivers.RationalQuiver.FDRep (rat Γ) where
  functor := fdFunctor
  inverse := fdInverse
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  functor_unitIso_comp _ := rfl

theorem famCast_eq {V : Type u} (X : V → Type u) [∀ v, AddCommGroup (X v)] [∀ v, Module L (X v)]
    {v w : V} (h : v = w) :
    RationalQuivers.RationalQuiver.famCast (L := L) X h = RQStatement.RationalQuiver.famCast X h := by
  cases h; rfl

theorem pathCompose_eq {Q : RQStatement.RQuiver.{u}} (X : Q.V → Type u) [∀ v, AddCommGroup (X v)]
    [∀ v, Module L (X v)] (f : ∀ e : Q.E, X (Q.source e) →ₗ[L] X (Q.target e)) {a b : Q.V}
    (p : @Quiver.Path Q.V (RQStatement.RQuiver.instQuiverV Q) a b) :
    RationalQuivers.RationalQuiver.pathCompose (Q := rq Q) X f p
      = RQStatement.RationalQuiver.pathCompose X f p := by
  induction p with
  | nil =>
    exact (RationalQuivers.RationalQuiver.pathCompose_nil (Q := rq Q) X f _).trans
      (RQStatement.RationalQuiver.pathCompose.eq_1 X f _).symm
  | cons p g ih =>
    refine (RationalQuivers.RationalQuiver.pathCompose_cons (Q := rq Q) X f p g).trans ?_
    refine Eq.trans ?_ (RQStatement.RationalQuiver.pathCompose.eq_2 X f _ _ _ p g).symm
    rw [ih]
    congr 1

theorem isNilpotent_iff (M : RQStatement.RationalQuiver.Rep Γ) :
    (repTo M).IsNilpotent ↔ M.IsNilpotent := by
  unfold RationalQuivers.RationalQuiver.Rep.IsNilpotent RQStatement.RationalQuiver.Rep.IsNilpotent
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, fun a b p hp => (pathCompose_eq _ _ p).symm.trans (hn a b p hp)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, fun a b p hp => (pathCompose_eq _ _ p).trans (hn a b p hp)⟩

end QuiverSide

/-! ## `Γ_E` and `Rep^nil(Γ_E)` -/

section Target

variable {E : Type} [Field E] [CharZero E] (D : RQStatement.HC.ImagUnit E)

theorem chiHom_eq : (imag D).chiHom = D.chiHom := by
  ext σ; exact congrArg Units.val (chi_eq σ)

theorem rat_GammaE (ℓ : ℕ) :
    rat (RQStatement.Gelfand.GammaE D ℓ) = RationalQuivers.Gelfand.GammaE (imag D) ℓ := by
  cases ℓ with
  | zero =>
    show rat (RQStatement.RationalQuiver.cyclicOfSign E D.L D.chiHom)
      = RationalQuivers.RationalQuiver.cyclicOfSign E D.L (imag D).chiHom
    rw [chiHom_eq]
    unfold rat RQStatement.RationalQuiver.cyclicOfSign RationalQuivers.RationalQuiver.cyclicOfSign
      RQStatement.RationalQuiver.ofSign RationalQuivers.RationalQuiver.ofSign
    congr 1
    ext σ : 1
    apply CategoryTheory.Aut.ext
    apply CategoryTheory.Iso.ext
    by_cases h : D.chiHom σ = 1 <;>
      simp [h, RQStatement.MonoidHom.signToInvolution, RationalQuivers.MonoidHom.signToInvolution,
        rqAut, rqHom, rq] <;> rfl
  | succ k =>
    show rat (RQStatement.RationalQuiver.gelfandOfSign E D.L D.chiHom)
      = RationalQuivers.RationalQuiver.gelfandOfSign E D.L (imag D).chiHom
    rw [chiHom_eq]
    unfold rat RQStatement.RationalQuiver.gelfandOfSign RationalQuivers.RationalQuiver.gelfandOfSign
      RQStatement.RationalQuiver.ofSign RationalQuivers.RationalQuiver.ofSign
    congr 1
    ext σ : 1
    apply CategoryTheory.Aut.ext
    apply CategoryTheory.Iso.ext
    by_cases h : D.chiHom σ = 1 <;>
      simp [h, RQStatement.MonoidHom.signToInvolution, RationalQuivers.MonoidHom.signToInvolution,
        rqAut, rqHom, rq] <;> rfl

end Target

/-! ## Full subcategories, transport, and the final assembly -/

section Final

/-- An equivalence restricts to full subcategories whose predicates correspond. -/
def restrictEquiv {C D : Type*} [Category C] [Category D] (e : C ≌ D)
    {P : ObjectProperty C} {Q : ObjectProperty D}
    (hPQ : ∀ X, P X → Q (e.functor.obj X)) (hQP : ∀ Y, Q Y → P (e.inverse.obj Y)) :
    P.FullSubcategory ≌ Q.FullSubcategory where
  functor := Q.lift (P.ι ⋙ e.functor) (fun X => hPQ _ X.2)
  inverse := P.lift (Q.ι ⋙ e.inverse) (fun Y => hQP _ Y.2)
  unitIso := (P.fullyFaithfulι.whiskeringRight _).preimageIso (P.ι.isoWhiskerLeft e.unitIso)
  counitIso := (Q.fullyFaithfulι.whiskeringRight _).preimageIso (Q.ι.isoWhiskerLeft e.counitIso)
  functor_unitIso_comp X := ObjectProperty.hom_ext _ (e.functor_unit_comp X.obj)

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]

open RationalQuivers in
/-- A rational quiver structure on the quiver `Q`, with arbitrary Galois action `ρ`. -/
abbrev gq (Q : RQuiver.{0}) (ρ : Gal(L/K) →* RQuiver.Aut Q)
    (hV : IsSmooth ((RQuiver.Aut.toPermV Q).comp ρ)) (hE : IsSmooth ((RQuiver.Aut.toPermE Q).comp ρ)) :
    RationalQuiver K L :=
  ⟨Q, ρ, hV, hE⟩

open RationalQuivers in
/-- `Rep^nil` of the Gelfand quiver (with the relation `a₋b₋ = a₊b₊`), any Galois action. -/
def gPred (ρ : Gal(L/K) →* RQuiver.Aut RQuiver.gelfand) (hV hE) :
    ObjectProperty (RationalQuiver.FDRep (gq RQuiver.gelfand ρ hV hE)) :=
  fun M => M.toRep.IsNilpotent ∧
    M.toRep.pathMap (a := (1 : Fin 3)) (b := (1 : Fin 3)) RQuiver.pathMinus
      = M.toRep.pathMap (a := (1 : Fin 3)) (b := (1 : Fin 3)) RQuiver.pathPlus

open RationalQuivers in
/-- `Rep^nil` of the cyclic quiver, any Galois action. -/
def cPred (ρ : Gal(L/K) →* RQuiver.Aut RQuiver.cyclic) (hV hE) :
    ObjectProperty (RationalQuiver.FDRep (gq RQuiver.cyclic ρ hV hE)) :=
  fun M => M.toRep.IsNilpotent

open RationalQuivers in
def gTransport {ρ₁ ρ₂ : Gal(L/K) →* RQuiver.Aut RQuiver.gelfand} (h : ρ₁ = ρ₂) (hV₁ hE₁ hV₂ hE₂) :
    (gPred ρ₁ hV₁ hE₁).FullSubcategory ≌ (gPred ρ₂ hV₂ hE₂).FullSubcategory := by
  subst h; exact CategoryTheory.Equivalence.refl

open RationalQuivers in
def cTransport {ρ₁ ρ₂ : Gal(L/K) →* RQuiver.Aut RQuiver.cyclic} (h : ρ₁ = ρ₂) (hV₁ hE₁ hV₂ hE₂) :
    (cPred ρ₁ hV₁ hE₁).FullSubcategory ≌ (cPred ρ₂ hV₂ hE₂).FullSubcategory := by
  subst h; exact CategoryTheory.Equivalence.refl

variable {E : Type} [Field E] [CharZero E] (D : RQStatement.HC.ImagUnit E)

theorem rho_succ (k : ℕ) :
    (rat (RQStatement.Gelfand.GammaE D (k + 1))).ρ
      = (RationalQuivers.Gelfand.GammaE (imag D) (k + 1)).ρ := by
  show (rqAut _).comp ((RQStatement.MonoidHom.signToInvolution _ _).comp D.chiHom)
    = (RationalQuivers.MonoidHom.signToInvolution _ _).comp (imag D).chiHom
  rw [chiHom_eq]
  ext σ : 1
  apply CategoryTheory.Aut.ext
  apply CategoryTheory.Iso.ext
  by_cases h : D.chiHom σ = 1 <;>
    simp [h, RQStatement.MonoidHom.signToInvolution, RationalQuivers.MonoidHom.signToInvolution,
      rqAut, rqHom, rq] <;> rfl

theorem rho_zero :
    (rat (RQStatement.Gelfand.GammaE D 0)).ρ = (RationalQuivers.Gelfand.GammaE (imag D) 0).ρ := by
  show (rqAut _).comp ((RQStatement.MonoidHom.signToInvolution _ _).comp D.chiHom)
    = (RationalQuivers.MonoidHom.signToInvolution _ _).comp (imag D).chiHom
  rw [chiHom_eq]
  ext σ : 1
  apply CategoryTheory.Aut.ext
  apply CategoryTheory.Iso.ext
  by_cases h : D.chiHom σ = 1 <;>
    simp [h, RQStatement.MonoidHom.signToInvolution, RationalQuivers.MonoidHom.signToInvolution,
      rqAut, rqHom, rq] <;> rfl

/-- `Rep^nil(Γ_E)` of the statement ≌ `Rep^nil(Γ_E)` of the formalization. -/
def targetEquiv : (ℓ : ℕ) →
    (RQStatement.Gelfand.RepNilTarget D ℓ).FullSubcategory
      ≌ (RationalQuivers.Gelfand.RepNilTarget (imag D) ℓ).FullSubcategory
  | 0 =>
    let Γ := rat (RQStatement.Gelfand.GammaE D 0)
    let e₁ : (RQStatement.Gelfand.RepNilTarget D 0).FullSubcategory
        ≌ (cPred Γ.ρ Γ.smooth_V Γ.smooth_E).FullSubcategory :=
      restrictEquiv fdEquiv (fun M hM => (isNilpotent_iff M.toRep).mpr hM)
        (fun Y hY => (isNilpotent_iff (repFrom Y.toRep)).mp hY)
    e₁.trans (cTransport (rho_zero D) _ _ _ _)
  | k + 1 =>
    let Γ := rat (RQStatement.Gelfand.GammaE D (k + 1))
    let e₁ : (RQStatement.Gelfand.RepNilTarget D (k + 1)).FullSubcategory
        ≌ (gPred Γ.ρ Γ.smooth_V Γ.smooth_E).FullSubcategory :=
      restrictEquiv fdEquiv
        (fun M hM => ⟨(isNilpotent_iff M.toRep).mpr hM.1,
          (@pathCompose_eq _ _ _ M.toRep.M (fun v => M.toRep.addCommGroup v)
              (fun v => M.toRep.module v) M.toRep.φEdge _ _ RQStatement.RQuiver.pathMinus).trans
            (hM.2.trans (@pathCompose_eq _ _ _ M.toRep.M (fun v => M.toRep.addCommGroup v)
              (fun v => M.toRep.module v) M.toRep.φEdge _ _ RQStatement.RQuiver.pathPlus).symm)⟩)
        (fun Y hY => ⟨(isNilpotent_iff (repFrom Y.toRep)).mp hY.1,
          (@pathCompose_eq _ _ _ Y.toRep.M (fun v => Y.toRep.addCommGroup v)
              (fun v => Y.toRep.module v) Y.toRep.φEdge _ _ RQStatement.RQuiver.pathMinus).symm.trans
            (hY.2.trans (@pathCompose_eq _ _ _ Y.toRep.M (fun v => Y.toRep.addCommGroup v)
              (fun v => Y.toRep.module v) Y.toRep.φEdge _ _ RQStatement.RQuiver.pathPlus))⟩)
    e₁.trans (gTransport (rho_succ D k) _ _ _ _)

/-- Back from the formalization's `ImagUnit`. -/
def imagFrom {E : Type} [Field E] (D : RationalQuivers.HC.ImagUnit E) : RQStatement.HC.ImagUnit E where
  L := D.L
  field := D.field
  algebra := D.algebra
  i := D.i
  i_mul_i := D.i_mul_i
  adjoin_eq_top := D.adjoin_eq_top

theorem imagUnit_nonempty (E : Type) [Field E] : Nonempty (RQStatement.HC.ImagUnit E) :=
  ⟨imagFrom (RationalQuivers.HC.ImagUnit.std E)⟩

/-- **Theorem B**, for the statement-surface definitions, from the formalization's
`RationalQuivers.Gelfand.gelfand_equivalence`. -/
theorem theoremB (E : Type) [Field E] [CharZero E] (D : RQStatement.HC.ImagUnit E) (ℓ : ℕ) :
    Nonempty (RQStatement.HC.HC ℓ E D ≌ (RQStatement.Gelfand.RepNilTarget D ℓ).FullSubcategory) := by
  obtain ⟨e, -⟩ := RationalQuivers.Gelfand.gelfand_equivalence E (imag D) ℓ
  exact ⟨hcEquiv.trans (e.trans (targetEquiv D ℓ).symm)⟩

end Final

end

end RQBridge
