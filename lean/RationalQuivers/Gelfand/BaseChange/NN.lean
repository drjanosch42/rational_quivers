import RationalQuivers.Gelfand.BaseChange.NNRep

/-!
# `𝔼` is compatible with base change: non-split → non-split (WP-15, T1 case (2))

*Provenance.*  Relocated in stage T4 (WP-11) from `GF/BaseChangeNN.lean` (v1 `RationalQuivers.Gelfand.GF`) by `workflow/v2/stages/T4/VALIDATION/scripts/relocate_bc.py`: whole file, declarations moved from `GF.x` to `Gelfand.BaseChange.x` (renames in the T4 `DECL-ALLOWLIST.tsv`), references qualified, the imports of v1's `GF/Main`/`GF/Species` cut; statements and proofs otherwise unchanged.  The native statement on `HC ℓ E D`/`𝔼_E` (`prop:basechange`, `RQ2-5.14`) is in `Gelfand/BaseChange/Native.lean`.

`√-1 ∉ E''` (hence `√-1 ∉ E`), `E → E''`, `ι : E(√-1) → E''(√-1)` over `E → E''`.

`E_bc_nn_iso`: `hcBaseChangeNN ⋙ 𝔼_{E''} ≅ 𝔼_E ⋙ qBCnnRel`.  The components are the vertex
isomorphisms `bcVtx` of the split core along `ι` (the `E''(√-1)`-representation underlying
`𝔼_{E''}(E'' ⊗ M)` is `𝔼_{E''(√-1)}` of `E''(√-1) ⊗_{E(√-1)} M_{E(√-1)}`); what is new is that they
intertwine the **rational structures**:

  `φ''_{v,c''}(b ⊗ m) = c''(b) ⊗ φ_{v,c}(m)`

(`galAct_bcNN`), which is `c''(b ⊗ m) = c''(b) ⊗ c(m)` (construction of `hcBaseChangeNN`) together
with the canonicity of the unipotent stabilization `φ''^{(∞)}(1 ⊗ m) = 1 ⊗ φ^{(∞)}(m)`
(`limAt_bcNN`).
-/

namespace RationalQuivers.Gelfand.BaseChange

open RationalQuivers.HC RationalQuivers.Gelfand RationalQuivers.RationalQuiver CategoryTheory
open scoped TensorProduct

section NN

variable {ℓ : ℕ}
variable {E : Type} [Field E] [CharZero E] {D : SqrtNegOneExt E}
variable {E'' : Type} [Field E''] [CharZero E''] {D'' : SqrtNegOneExt E''}
variable [Algebra E E''] [Algebra D.carrier D''.carrier] [Algebra E D''.carrier]
  [IsScalarTower E E'' D''.carrier] [IsScalarTower E D.carrier D''.carrier]

omit [Algebra E E''] [Algebra D.carrier D''.carrier] [Algebra E D''.carrier]
  [IsScalarTower E E'' D''.carrier] [IsScalarTower E D.carrier D''.carrier] in
/-- The underlying vector of an element of a vertex space of `𝔼(M)`.  @census none (helper) -/
abbrev vval (A : HCEObj ℓ E D) {w : Fin 3} (x : Split.V3 A.qi w) : A.carrier := (x : A.carrier)

omit [Algebra E E''] [Algebra D.carrier D''.carrier] [Algebra E D''.carrier]
  [IsScalarTower E E'' D''.carrier] [IsScalarTower E D.carrier D''.carrier] in
/-- The transported structure maps of `𝔼_E(M)`, on underlying vectors.
@census none (helper; WP-15) -/
theorem E_Q_φ'_val (hcard : Nat.card (D.carrier ≃ₐ[E] D.carrier) = 2) (hℓ : 1 ≤ ℓ)
    (A : HCEObj ℓ E D) (hA : Gelfand.RationalStructure.ObjSpec hcard hℓ A) (g : D.carrier ≃ₐ[E] D.carrier)
    {v w : (Gelfand.RationalStructure.gelfandQ hcard).V} (hvw : g • v = w) (m : Split.V3 A.qi v) :
    vval A (w := w) ((Gelfand.Equivalence.E_Q_rep hcard hℓ A hA).φ' g hvw m) = Gelfand.Equivalence.galAct hℓ A g v (vval A m) := by
  subst hvw; rfl

/-- **The rational structures commute with base change**:
`σ(b) ⊗ φ_{v,θ(σ)}(m) = φ''_{v,σ}(b ⊗ m)` on underlying vectors.
@census none (helper; WP-15) -/
theorem galAct_bcNN (hι : ConjCompat D D'') (hℓ : 1 ≤ ℓ) (A : HCEObj ℓ E D)
    (σ : D''.carrier ≃ₐ[E''] D''.carrier) (v : Fin 3) (b : D''.carrier) (m : A.carrier) :
    σ b ⊗ₜ[D.carrier] Gelfand.Equivalence.galAct hℓ A ((restrictionDatum D D'' hι).θ σ) v m
      = Gelfand.Equivalence.galAct hℓ (A.bcNN hι) σ v (b ⊗ₜ[D.carrier] m) := by
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, Gelfand.Equivalence.galAct_one, Gelfand.Equivalence.galAct_one, AlgEquiv.one_apply]
  · rw [Gelfand.Equivalence.galAct_of_ne hℓ A ((restrictionDatum D D'' hι).θ_ne_one hσ),
      Gelfand.Equivalence.galAct_of_ne hℓ (A.bcNN hι) hσ]
    show σ b ⊗ₜ[D.carrier] A.setup.conj (Gelfand.RationalStructure.limAt hℓ A v m)
      = (A.bcNN hι).setup.conj (Gelfand.RationalStructure.limAt hℓ (A.bcNN hι) v (b ⊗ₜ[D.carrier] m))
    have h1 : b ⊗ₜ[D.carrier] m = b • ((1 : D''.carrier) ⊗ₜ[D.carrier] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, limAt_bcNN hι hℓ A v m, (A.bcNN hι).setup.conj_smul]
    show σ b ⊗ₜ[D.carrier] A.setup.conj (Gelfand.RationalStructure.limAt hℓ A v m)
      = D''.conj b • conjBC hι A.setup.conj A.setup.conj_smul A.setup.conj_involutive
          ((1 : D''.carrier) ⊗ₜ[D.carrier] Gelfand.RationalStructure.limAt hℓ A v m)
    rw [conjBC_tmul, map_one, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      D''.eq_conj_of_ne_one hσ]

variable (D D'') in
/-- `E''(√-1) ⊗ 𝔼_E(M)` as a finite-dimensional representation of `Γ_{E''}`.
@census none (helper; WP-15) -/
noncomputable def E_Q_fdrep_bcNN (hι : ConjCompat D D'') (hℓ : 1 ≤ ℓ) (A : HCEObj ℓ E D)
    (hA : Gelfand.RationalStructure.ObjSpec D.card_gal hℓ A) :
    RationalQuiver.FDRep (gelfandOfCardTwo E'' D''.carrier D''.card_gal) where
  toRep := Rep.bcNN (h'' := D''.card_gal) (restrictionDatum D D'' hι) (Gelfand.Equivalence.E_Q_rep D.card_gal hℓ A hA)
  finiteDimensional v := by
    haveI : Module.Finite D.carrier (Split.V3 A.qi v) := A.admissible _
    exact Module.Finite.base_change D.carrier D''.carrier (Split.V3 A.qi v)

/-- The rational-structure square of the component, as an identity of additive maps.
@census none (helper; WP-15) -/
theorem bcNN_hrat (hι : ConjCompat D D'') (hℓ : 1 ≤ ℓ) (A : HCEObj ℓ E D)
    (hA : Gelfand.RationalStructure.ObjSpec D.card_gal hℓ A) (hA'' : Gelfand.RationalStructure.ObjSpec D''.card_gal hℓ (A.bcNN hι))
    (σ : D''.carrier ≃ₐ[E''] D''.carrier) (v : (Gelfand.RationalStructure.gelfandQ D''.card_gal).V) :
    (((bcVtx D''.carrier A.toF (vtxIdx ℓ (σ • v))).toLinearMap.toAddMonoidHom.comp
        (phiNNEquiv (h := D.card_gal) (h'' := D''.card_gal) (restrictionDatum D D'' hι)
          (Gelfand.Equivalence.E_Q_rep D.card_gal hℓ A hA) σ v).toAddMonoidHom :
        D''.carrier ⊗[D.carrier] Split.V3 A.qi v →+ Split.V3 (A.bcNN hι).qi (σ • v)))
      = (Gelfand.Equivalence.E_Q_φ D''.card_gal hℓ (A.bcNN hι) hA'' σ v).toAddMonoidHom.comp
          (bcVtx D''.carrier A.toF (vtxIdx ℓ v)).toLinearMap.toAddMonoidHom := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b m =>
    apply Subtype.ext
    show σ b ⊗ₜ[D.carrier] vval A ((Gelfand.Equivalence.E_Q_rep D.card_gal hℓ A hA).φ' ((restrictionDatum D D'' hι).θ σ)
        ((restrictionDatum D D'' hι).smul_vertex (h := D.card_gal) (h'' := D''.card_gal) σ v) m)
      = Gelfand.Equivalence.galAct hℓ (A.bcNN hι) σ v (b ⊗ₜ[D.carrier] vval A m)
    rw [E_Q_φ'_val]
    exact galAct_bcNN hι hℓ A σ v b m
  | add x y hx hy => simp only [map_add, hx, hy]

variable (D D'') in
/-- **The component of case (2)**: `E''(√-1) ⊗ 𝔼_E(M) ≅ 𝔼_{E''}(E'' ⊗ M)` as `E''`-rational
representations of `Γ_{E''}`.  @census none (helper; WP-15) -/
noncomputable def bcNNRepIso (hι : ConjCompat D D'') (hℓ : 1 ≤ ℓ) (A : HCEObj ℓ E D)
    (hA : Gelfand.RationalStructure.ObjSpec D.card_gal hℓ A) (hA'' : Gelfand.RationalStructure.ObjSpec D''.card_gal hℓ (A.bcNN hι)) :
    E_Q_fdrep_bcNN D D'' hι hℓ A hA ≅ Gelfand.Equivalence.E_Q_fdrep D''.card_gal hℓ (A.bcNN hι) hA'' :=
  fdRepIsoOfEquivs (fun v => bcVtx D''.carrier A.toF (vtxIdx ℓ v))
    (fun e x => bcEdge_comm hℓ A.toF e x)
    (fun σ v x => DFunLike.congr_fun (bcNN_hrat hι hℓ A hA hA'' σ v) x)

variable (ℓ E D E'' D'') in
/-- The square of case (2), in the direction the components are built in.
@census none (helper; WP-15) -/
noncomputable def E_bc_nn_iso' (hι : ConjCompat D D'') (hℓ : 1 ≤ ℓ) (h : Gelfand.RationalStructure.E_QSpec D.card_gal hℓ)
    (h'' : Gelfand.RationalStructure.E_QSpec D''.card_gal hℓ) :
    Gelfand.Equivalence.E_QFunctor D.card_gal hℓ h ⋙ qBCnnRel (h'' := D''.card_gal) (restrictionDatum D D'' hι) ≅
      hcBaseChangeNN ℓ E D E'' D'' hι ⋙ Gelfand.Equivalence.E_QFunctor D''.card_gal hℓ h'' :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ (bcNNRepIso D D'' hι hℓ A (h.1 A) (h''.1 _)))
    (fun {A B} f => by
      apply ObjectProperty.hom_ext
      apply RationalQuiver.Rep.Hom.ext
      funext v
      exact bcRepIso_natural D''.carrier ((GF.baseChangeE ℓ E D).map f)
        ((GF.baseChangeE ℓ E'' D'').map ((hcBaseChangeNN ℓ E D E'' D'' hι).map f))
        (fun a m => LinearMap.baseChange_tmul _ _ _) v)

variable (ℓ E D E'' D'') in
/-- **T1, case (2) — `𝔼` commutes with base change, non-split → non-split**, for every `ℓ ≥ 1`,
every extension `E → E''` and every `ι : E(√-1) → E''(√-1)` compatible with the conjugations:

  `hcBaseChangeNN ⋙ 𝔼_{E''} ≅ 𝔼_E ⋙ qBCnnRel`

as functors `HC_λ(𝔤,K)_E ⥤ Rep^nil_rel(Γ_{E''})`, `Γ_{E''}` the `E''`-rational Gelfand quiver.  The
components are the canonical maps `E''(√-1) ⊗_{E(√-1)} M_n → (E''(√-1) ⊗_{E(√-1)} M)_n`; they
intertwine the rational structures because the unipotent stabilization is canonical
(`limAt_bcNN`).  For `√-1 ∉ E''` and a square root of `-1` in `D'` the compatibility `hι` is
automatic: `E_bc_nn_compat`.

@census none (WP-15; T1 of `BASECHANGE-ANALYSIS.md`, `rmk:generalbases`, base change, case (2)) -/
noncomputable def E_bc_nn_iso (hι : ConjCompat D D'') (hℓ : 1 ≤ ℓ) (h : Gelfand.RationalStructure.E_QSpec D.card_gal hℓ)
    (h'' : Gelfand.RationalStructure.E_QSpec D''.card_gal hℓ) :
    hcBaseChangeNN ℓ E D E'' D'' hι ⋙ Gelfand.Equivalence.E_QFunctor D''.card_gal hℓ h'' ≅
      Gelfand.Equivalence.E_QFunctor D.card_gal hℓ h ⋙ qBCnnRel (h'' := D''.card_gal) (restrictionDatum D D'' hι) :=
  (E_bc_nn_iso' ℓ E D E'' D'' hι hℓ h h'').symm

variable (ℓ E D E'' D'') in
/-- **T1, case (2), pinned to the equivalences, for `√-1 ∉ E''`**: the compatibility of
`ι : E(√-1) → E''(√-1)` with the conjugations is proved (`conjCompat_of_noSqrtNegOne`), there are
equivalences whose functors **are** `𝔼_E` and `𝔼_{E''}`, and the base-change square commutes up to
natural isomorphism.

The square root `s` of `-1` in `D'` is an explicit argument since the v2 amendment T4-a1 (before,
it was a field of `D`; the mathematical content is unchanged).

@census none (WP-15; T1, case (2)) -/
theorem E_bc_nn_compat [NoSqrtNegOne E''] (s : D.carrier) (hs : s * s = -1) (hℓ : 1 ≤ ℓ) :
    ∃ (hι : ConjCompat D D'') (h : Gelfand.RationalStructure.E_QSpec D.card_gal hℓ) (h'' : Gelfand.RationalStructure.E_QSpec D''.card_gal hℓ)
      (e : HCEObj ℓ E D ≌ (repNilRelGel E D.carrier D.card_gal).FullSubcategory)
      (e'' : HCEObj ℓ E'' D'' ≌ (repNilRelGel E'' D''.carrier D''.card_gal).FullSubcategory),
      e.functor = Gelfand.Equivalence.E_QFunctor D.card_gal hℓ h ∧
      e''.functor = Gelfand.Equivalence.E_QFunctor D''.card_gal hℓ h'' ∧
      Nonempty (hcBaseChangeNN ℓ E D E'' D'' hι ⋙ e''.functor ≅
        e.functor ⋙ qBCnnRel (h'' := D''.card_gal) (restrictionDatum D D'' hι)) := by
  obtain ⟨h, e, he⟩ := Gelfand.EssSurj.E_Q_equivalence (Dq := D) hℓ
  obtain ⟨h'', e'', he''⟩ := Gelfand.EssSurj.E_Q_equivalence (Dq := D'') hℓ
  have hι : ConjCompat D D'' := conjCompat_of_noSqrtNegOne D D'' s hs
  refine ⟨hι, h, h'', e, e'', he, he'', ?_⟩
  rw [he, he'']
  exact ⟨E_bc_nn_iso ℓ E D E'' D'' hι hℓ h h''⟩

end NN

end RationalQuivers.Gelfand.BaseChange
