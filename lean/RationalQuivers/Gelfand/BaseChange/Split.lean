module

public import RationalQuivers.Gelfand.Main
public import RationalQuivers.Gelfand.BaseChange.QuiverRel
public import RationalQuivers.Gelfand.Split.Cyclic

@[expose] public section

/-!
# `𝔼` is compatible with base change: the core and the split case (WP-15, T1)

*Provenance.*  Relocated in stage T4 (WP-11) from `GF/BaseChange.lean` (v1 `RationalQuivers.Gelfand.GF`) by `workflow/v2/stages/T4/VALIDATION/scripts/relocate_bc.py`: whole file, declarations moved from `GF.x` to `Gelfand.BaseChange.x` (renames in the T4 `DECL-ALLOWLIST.tsv`), references qualified, the imports of v1's `GF/Main`/`GF/Species` cut; statements and proofs otherwise unchanged.  The native statement on `HC ℓ E D`/`𝔼_E` (`prop:basechange`, `RQ2-5.14`) is in `Gelfand/BaseChange/Native.lean`.

Author decision of 2026-10-02 (`workflow/audit/final-release-2026-10-02/BASECHANGE-ANALYSIS.md`,
(T1)): for every extension `F → F''` of characteristic-zero fields, base change commutes with `𝔼`
up to a natural isomorphism.  Design note: `workflow/analysis/BASECHANGE-T1-DESIGN-2026-10-02.md`.

This module proves the **split → split** case (`√-1 ∈ F`) and builds the core every case uses:

* `HCFObj.bcF` — `F'' ⊗_F −` on the concrete category `HCF F ℓ`; it *is* `hcBaseChange` read
  through `hcLambdaToF` (`hcLambdaToF_hcBaseChange`, `rfl`).
* `bcVtx` — the canonical vertex isomorphism `F'' ⊗_F M_n ≅ (F'' ⊗_F M)_n`, `a ⊗ m ↦ a ⊗ m`
  (mathlib's `Submodule.toBaseChange`, bijective by flatness).
* `bcEdge_val` — the four edge maps `X`, `Y`, `X⋆⁻¹Y`, `XX⋆` of `𝔼` commute with `m ↦ 1 ⊗ m`.  The
  only non-formal one is `X⋆⁻¹`, the canonical inverse of `X⋆ : M_{-(ℓ-1)} → M_{ℓ-1}`; it commutes
  with `1 ⊗ −` by the uniqueness of two-sided inverses (`map_xStarInv_bc`).
* `bcRepHom` / `bcRepIso` — `𝔼_F(M)` base-changed to `F''` is isomorphic to `𝔼_{F''}(F'' ⊗ M)`,
  by the vertex isomorphisms; `bcRepIso_natural` — naturally in `M`.
* `E_bc_split_iso` (**T1, case (1)**) — `hcBaseChange ⋙ 𝔼_{F''} ≅ 𝔼_F ⋙ qBCssRel`, and the
  pinned form `E_bc_split_compat`.

No existing declaration is edited.
-/

namespace RationalQuivers.Gelfand.BaseChange

open RationalQuivers.HC RationalQuivers.Gelfand CategoryTheory
open scoped TensorProduct

/-! ## A representation isomorphism from vertexwise linear equivalences -/

section RepIso

variable {K L : Type} [Field K] [Field L] [Algebra K L] {Γ : RationalQuiver.{0} K L}

/-- A family of vertexwise linear equivalences commuting with the edge maps and the rational
structures is an isomorphism in `Rep(Γ)`.  @census none (helper; WP-15) -/
noncomputable def fdRepIsoOfEquivs {M N : RationalQuiver.FDRep Γ}
    (e : ∀ v : Γ.V, M.toRep.M v ≃ₗ[L] N.toRep.M v)
    (hedge : ∀ (a : Γ.E) (m : M.toRep.M (Γ.toRQuiver.source a)),
      e (Γ.toRQuiver.target a) (M.toRep.φEdge a m) = N.toRep.φEdge a (e (Γ.toRQuiver.source a) m))
    (hrat : ∀ (σ : Gal(L/K)) (v : Γ.V) (m : M.toRep.M v),
      e (σ • v) (M.toRep.φ σ v m) = N.toRep.φ σ v (e v m)) : M ≅ N where
  hom :=
    { ψ := fun v => (e v).toLinearMap
      edge := hedge
      rational := hrat }
  inv :=
    { ψ := fun v => (e v).symm.toLinearMap
      edge := fun a m => by
        apply (e (Γ.toRQuiver.target a)).injective
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        rw [hedge, LinearEquiv.apply_symm_apply]
      rational := fun σ v m => by
        apply (e (σ • v)).injective
        simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        rw [hrat, LinearEquiv.apply_symm_apply] }
  hom_inv_id := by
    apply RationalQuiver.Rep.Hom.ext
    funext v
    exact LinearMap.ext fun x => (e v).symm_apply_apply x
  inv_hom_id := by
    apply RationalQuiver.Rep.Hom.ext
    funext v
    exact LinearMap.ext fun x => (e v).apply_symm_apply x

@[simp] theorem fdRepIsoOfEquivs_hom_ψ {M N : RationalQuiver.FDRep Γ}
    (e : ∀ v : Γ.V, M.toRep.M v ≃ₗ[L] N.toRep.M v) (hedge) (hrat) (v : Γ.V) :
    (fdRepIsoOfEquivs e hedge hrat).hom.ψ v = (e v).toLinearMap := rfl

end RepIso

/-! ## Base change on the concrete category `HCF F ℓ` -/

section Core

variable {F : Type} [Field F] [CharZero F] (F'' : Type) [Field F''] [CharZero F''] [Algebra F F'']
variable {ℓ : ℕ}

/-- **`F'' ⊗_F −` on `HC_λ(𝔤,K)_F`** (concrete category): carrier `F'' ⊗_F M`, weight datum
`W.baseChange`.  The proof fields are those of S10's `HCObjOver.baseChange`.
@census none (helper; WP-15) -/
@[reducible] noncomputable def _root_.RationalQuivers.Gelfand.Split.HCFObj.bcF (A : Split.HCFObj F ℓ) : Split.HCFObj F'' ℓ where
  carrier := F'' ⊗[F] A.carrier
  weight := A.weight.baseChange
  gic := ((hcBaseChange ℓ F F'').obj (Split.hcFToLambdaObj F ℓ A)).obj.gic
  admissible := ((hcBaseChange ℓ F F'').obj (Split.hcFToLambdaObj F ℓ A)).obj.admissible
  centralCharacter := ((hcBaseChange ℓ F F'').obj (Split.hcFToLambdaObj F ℓ A)).property
  fg := ((hcBaseChange ℓ F F'').obj (Split.hcFToLambdaObj F ℓ A)).obj.fg

/-- `bcF` **is** `hcBaseChange`, read through `hcLambdaToF`.  @census none (helper; WP-15) -/
theorem hcLambdaToF_hcBaseChange (X : HCLambda.{0} ℓ F) :
    (Split.hcLambdaToF F'' ℓ).obj ((hcBaseChange ℓ F F'').obj X) = ((Split.hcLambdaToF F ℓ).obj X).bcF F'' :=
  rfl

/-- **The vertex isomorphism** `F'' ⊗_F M_n ≅ (F'' ⊗_F M)_n`, `a ⊗ m ↦ a ⊗ m`.
@census none (helper; WP-15) -/
noncomputable def bcVtx (A : Split.HCFObj F ℓ) (n : ℤ) :
    F'' ⊗[F] ↥(A.weight.comp n) ≃ₗ[F''] ↥((A.bcF F'').weight.comp n) :=
  Submodule.toBaseChange.toLinearEquiv F'' (A.weight.comp n)

@[simp] theorem bcVtx_tmul (A : Split.HCFObj F ℓ) (n : ℤ) (a : F'') (m : ↥(A.weight.comp n)) :
    ((bcVtx F'' A n (a ⊗ₜ[F] m) : ↥((A.bcF F'').weight.comp n)) : F'' ⊗[F] A.carrier)
      = a ⊗ₜ[F] (m : A.carrier) := rfl

variable {F''}

theorem bc_X_tmul (A : Split.HCFObj F ℓ) (a : F'') (m : A.carrier) :
    (A.bcF F'').weight.X (a ⊗ₜ[F] m) = a ⊗ₜ[F] A.weight.X m := LinearMap.baseChange_tmul _ _ _

theorem bc_Y_tmul (A : Split.HCFObj F ℓ) (a : F'') (m : A.carrier) :
    (A.bcF F'').weight.Y (a ⊗ₜ[F] m) = a ⊗ₜ[F] A.weight.Y m := LinearMap.baseChange_tmul _ _ _

theorem bc_Xpow_tmul (A : Split.HCFObj F ℓ) (k : ℕ) (a : F'') (m : A.carrier) :
    ((A.bcF F'').weight.X ^ k) (a ⊗ₜ[F] m) = a ⊗ₜ[F] (A.weight.X ^ k) m := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih => rw [pow_succ, Module.End.mul_apply, bc_X_tmul, ih, pow_succ, Module.End.mul_apply]

omit [CharZero F] [CharZero F''] in
theorem algebraMap_gammaStarF (ℓ : ℕ) :
    algebraMap F F'' (Split.gammaStarF F ℓ) = Split.gammaStarF F'' ℓ := by
  simp [Split.gammaStarF]

theorem bc_xStar_tmul (A : Split.HCFObj F ℓ) (a : F'') (m : A.carrier) :
    Split.xStar (A.bcF F'').setup (a ⊗ₜ[F] m) = a ⊗ₜ[F] Split.xStar A.setup m := by
  show (Split.gammaStarF F'' ℓ)⁻¹ • ((A.bcF F'').weight.X ^ (ℓ - 1)) (a ⊗ₜ[F] m)
    = a ⊗ₜ[F] ((Split.gammaStarF F ℓ)⁻¹ • (A.weight.X ^ (ℓ - 1)) m)
  rw [bc_Xpow_tmul, TensorProduct.tmul_smul, ← algebraMap_smul F'' ((Split.gammaStarF F ℓ)⁻¹),
    map_inv₀, algebraMap_gammaStarF, TensorProduct.smul_tmul', smul_eq_mul]

/-- **`X⋆⁻¹` commutes with `1 ⊗ −`** — the uniqueness of the two-sided inverse of
`X^{ℓ-1} : M_{-(ℓ-1)} → M_{ℓ-1}`, as in `map_xStarInv`.  @census none (helper; WP-15) -/
theorem map_xStarInv_bc (hℓ : 1 ≤ ℓ) (A : Split.HCFObj F ℓ) (v : A.carrier)
    (hv : v ∈ A.setup.comp ((ℓ : ℤ) - 1)) :
    (1 : F'') ⊗ₜ[F] (A.setup.starInverses hℓ).xStarInv v
      = ((A.bcF F'').setup.starInverses hℓ).xStarInv ((1 : F'') ⊗ₜ[F] v) := by
  set IA := A.setup.starInverses hℓ
  set IB := (A.bcF F'').setup.starInverses hℓ
  have hw : IA.xInv v ∈ A.setup.comp (-((ℓ : ℤ) - 1)) := IA.xInv_mem v hv
  have hXw : (A.setup.X ^ (ℓ - 1)) (IA.xInv v) = v := IA.xInv_right v hv
  have hfw : (1 : F'') ⊗ₜ[F] IA.xInv v ∈ (A.bcF F'').setup.comp (-((ℓ : ℤ) - 1)) :=
    Submodule.tmul_mem_baseChange_of_mem _ hw
  have hfv : (1 : F'') ⊗ₜ[F] v = ((A.bcF F'').setup.X ^ (ℓ - 1)) ((1 : F'') ⊗ₜ[F] IA.xInv v) := by
    rw [show (A.bcF F'').setup.X = (A.bcF F'').weight.X from rfl, bc_Xpow_tmul]
    exact congrArg _ hXw.symm
  have key : IB.xInv ((1 : F'') ⊗ₜ[F] v) = (1 : F'') ⊗ₜ[F] IA.xInv v := by
    rw [hfv]; exact IB.xInv_left _ hfw
  show (1 : F'') ⊗ₜ[F] (Split.gammaStarF F ℓ • IA.xInv v) = Split.gammaStarF F'' ℓ • IB.xInv _
  rw [key, TensorProduct.tmul_smul, ← algebraMap_smul F'' (Split.gammaStarF F ℓ),
    algebraMap_gammaStarF]

/-- **The four edge maps of `𝔼` commute with `1 ⊗ −`**, on underlying vectors.
@census none (helper; WP-15) -/
theorem bcEdge_val (hℓ : 1 ≤ ℓ) (A : Split.HCFObj F ℓ) :
    ∀ (e : Fin 4) (m : Split.V3 A.setup (RQuiver.gelfand.source e)),
      ((Split.E_F_edge (A.bcF F'').setup ((A.bcF F'').setup.starInverses hℓ) hℓ e
          (bcVtx F'' A _ ((1 : F'') ⊗ₜ[F] m)) : Split.V3 (A.bcF F'').setup (RQuiver.gelfand.target e))
          : F'' ⊗[F] A.carrier)
        = (1 : F'') ⊗ₜ[F] ((Split.E_F_edge A.setup (A.setup.starInverses hℓ) hℓ e m
            : Split.V3 A.setup (RQuiver.gelfand.target e)) : A.carrier)
  | 0, m => bc_X_tmul A 1 (m : A.carrier)
  | 1, m => bc_Y_tmul A 1 (m : A.carrier)
  | 2, ⟨v, hv⟩ => by
    show ((A.bcF F'').setup.starInverses hℓ).xStarInv ((A.bcF F'').weight.Y ((1 : F'') ⊗ₜ[F] v))
      = (1 : F'') ⊗ₜ[F] (A.setup.starInverses hℓ).xStarInv (A.weight.Y v)
    rw [bc_Y_tmul, map_xStarInv_bc hℓ A _ (Split.y_mem (Q := A.setup) (m := (ℓ : ℤ) + 1) (by ring) hv)]
  | 3, ⟨v, hv⟩ => by
    show (A.bcF F'').weight.X (Split.xStar (A.bcF F'').setup ((1 : F'') ⊗ₜ[F] v))
      = (1 : F'') ⊗ₜ[F] A.weight.X (Split.xStar A.setup v)
    rw [bc_xStar_tmul, bc_X_tmul]

/-- `bcEdge_val` as an identity of `F''`-linear maps on `F'' ⊗_F M(s(e))`: the vertex isomorphisms
intertwine the base-changed edge maps of `𝔼_F(M)` with the edge maps of `𝔼_{F''}(F'' ⊗ M)`.
@census none (helper; WP-15) -/
theorem bcEdge_comm (hℓ : 1 ≤ ℓ) (A : Split.HCFObj F ℓ) (e : Fin 4)
    (x : F'' ⊗[F] Split.V3 A.setup (RQuiver.gelfand.source e)) :
    bcVtx F'' A _ (LinearMap.baseChange F'' (Split.E_F_edge A.setup (A.setup.starInverses hℓ) hℓ e) x)
      = Split.E_F_edge (A.bcF F'').setup ((A.bcF F'').setup.starInverses hℓ) hℓ e (bcVtx F'' A _ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c m =>
    have h2 : bcVtx F'' A _ (c ⊗ₜ[F] m) = c • bcVtx F'' A _ ((1 : F'') ⊗ₜ[F] m) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearMap.baseChange_tmul, h2, map_smul]
    apply Subtype.ext
    rw [Submodule.coe_smul, bcEdge_val hℓ A e m, bcVtx_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (F'')

/-- **`𝔼_F(M)` base-changed to `F''` is `𝔼_{F''}(F'' ⊗_F M)`**, by the vertex isomorphisms
`bcVtx`.  The rational structures are trivial on both sides (split quivers).
@census none (helper; WP-15) -/
noncomputable def bcRepIso (hℓ : 1 ≤ ℓ) (A : Split.HCFObj F ℓ) :
    ((Split.E_F_obj ℓ hℓ A).toSplit F'' : RationalQuiver.FDRep (gelfandSplit F''))
      ≅ Split.E_F_obj ℓ hℓ (A.bcF F'') :=
  fdRepIsoOfEquivs (fun v => bcVtx F'' A (vtxIdx ℓ v))
    (fun e x => bcEdge_comm hℓ A e x) (fun _ _ _ => rfl)

/-- **Naturality of `bcRepIso`**: for `f : A ⟶ B` and any `g : F'' ⊗ A ⟶ F'' ⊗ B` acting as
`a ⊗ m ↦ a ⊗ f(m)` (i.e. `g` is the base change of `f`), the vertex isomorphisms intertwine
`F'' ⊗ 𝔼_F(f)` with `𝔼_{F''}(g)`.  @census none (helper; WP-15) -/
theorem bcRepIso_natural {A B : Split.HCFObj F ℓ} (f : A ⟶ B)
    (g : A.bcF F'' ⟶ B.bcF F'')
    (hg : ∀ (a : F'') (m : A.carrier), g.toLinearMap (a ⊗ₜ[F] m) = a ⊗ₜ[F] f.toLinearMap m)
    (v : Fin 3) :
    (bcVtx F'' B (vtxIdx ℓ v)).toLinearMap ∘ₗ LinearMap.baseChange F'' (Split.E_F_map_ψ ℓ f v)
      = Split.E_F_map_ψ ℓ g v ∘ₗ (bcVtx F'' A (vtxIdx ℓ v)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  apply Subtype.ext
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, bcVtx_tmul, Split.E_F_map_ψ_val, Split.E_F_map_ψ_val]
  exact (hg a m).symm

end Core

/-! ## T1, case (1): split → split -/

section Split

variable (F F'' : Type) [Field F] [CharZero F] [Field F''] [CharZero F''] [Algebra F F'']
variable (ℓ : ℕ)

/-- The square, in the direction the components are built in.  @census none (helper; WP-15) -/
noncomputable def E_bc_split_iso' (hℓ : 1 ≤ ℓ) :
    (Split.hcLambdaToF F ℓ ⋙ Split.E_FNil ℓ hℓ) ⋙ qBCssRel F F'' ≅
      hcBaseChange ℓ F F'' ⋙ Split.hcLambdaToF F'' ℓ ⋙ Split.E_FNil ℓ hℓ :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk (RepNilRelSplit F'') (bcRepIso F'' hℓ ((Split.hcLambdaToF F ℓ).obj X)))
    (fun {X Y} f => by
      apply ObjectProperty.hom_ext
      apply RationalQuiver.Rep.Hom.ext
      funext v
      exact bcRepIso_natural F'' ((Split.hcLambdaToF F ℓ).map f)
        ((Split.hcLambdaToF F'' ℓ).map ((hcBaseChange ℓ F F'').map f))
        (fun a m => LinearMap.baseChange_tmul _ _ _) v)

/-- **T1, case (1) — `𝔼` commutes with base change, split → split** (`√-1 ∈ F`), for an
**arbitrary** extension `F → F''` of characteristic-zero fields and every `ℓ ≥ 1`:

  `hcBaseChange ⋙ 𝔼_{F''} ≅ 𝔼_F ⋙ qBCssRel`

as functors `HC_λ(𝔤,K)_F ⥤ Rep^nil_rel(Γ_{F''})`.  The components are the canonical maps
`F'' ⊗_F M_n → (F'' ⊗_F M)_n`, `a ⊗ m ↦ a ⊗ m`, at the three vertices.

@census none (WP-15; T1 of `BASECHANGE-ANALYSIS.md`, `rmk:generalbases`, base change, case (1)) -/
noncomputable def E_bc_split_iso (hℓ : 1 ≤ ℓ) :
    hcBaseChange ℓ F F'' ⋙ Split.hcLambdaToF F'' ℓ ⋙ Split.E_FNil ℓ hℓ ≅
      (Split.hcLambdaToF F ℓ ⋙ Split.E_FNil ℓ hℓ) ⋙ qBCssRel F F'' :=
  (E_bc_split_iso' F F'' ℓ hℓ).symm

/-- **T1, case (1), pinned to the equivalences.**  For every extension `F → F''` of
characteristic-zero fields and every `ℓ ≥ 1` there are equivalences
`e : HC_λ(𝔤,K)_F ≌ Rep^nil_rel(Γ_F)`, `e'' : HC_λ(𝔤,K)_{F''} ≌ Rep^nil_rel(Γ_{F''})` whose functors
**are** the constructed `𝔼_F`, `𝔼_{F''}`, and the base-change square commutes up to natural
isomorphism.

@census none (WP-15; T1, case (1)) -/
theorem E_bc_split_compat (hℓ : 1 ≤ ℓ) :
    ∃ (e : HCLambda.{0} ℓ F ≌ (RepNilRelSplit F).FullSubcategory)
      (e'' : HCLambda.{0} ℓ F'' ≌ (RepNilRelSplit F'').FullSubcategory),
      e.functor = Split.hcLambdaToF F ℓ ⋙ Split.E_FNil ℓ hℓ ∧
      e''.functor = Split.hcLambdaToF F'' ℓ ⋙ Split.E_FNil ℓ hℓ ∧
      Nonempty (hcBaseChange ℓ F F'' ⋙ e''.functor ≅ e.functor ⋙ qBCssRel F F'') := by
  haveI := Split.E_FNil_full (F := F) ℓ hℓ
  haveI := Split.E_FNil_faithful (F := F) ℓ hℓ
  haveI := Split.essSurj (L := F) ℓ hℓ
  haveI : (Split.E_FNil (F := F) ℓ hℓ).IsEquivalence := { }
  haveI := Split.E_FNil_full (F := F'') ℓ hℓ
  haveI := Split.E_FNil_faithful (F := F'') ℓ hℓ
  haveI := Split.essSurj (L := F'') ℓ hℓ
  haveI : (Split.E_FNil (F := F'') ℓ hℓ).IsEquivalence := { }
  exact ⟨(Split.hcLambdaFEquiv F ℓ).trans (Split.E_FNil (F := F) ℓ hℓ).asEquivalence,
    (Split.hcLambdaFEquiv F'' ℓ).trans (Split.E_FNil (F := F'') ℓ hℓ).asEquivalence, rfl, rfl,
    ⟨E_bc_split_iso F F'' ℓ hℓ⟩⟩

end Split

end RationalQuivers.Gelfand.BaseChange
