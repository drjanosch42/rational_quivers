module

public import RationalQuivers.Gelfand.BaseChange.NN

@[expose] public section

/-!
# `𝔼` is compatible with base change at `ℓ = 0` (the cyclic quiver; WP-15, T1)

*Provenance.*  Relocated in stage T4 (WP-11) from `GF/BaseChangeCyclic.lean` (v1 `RationalQuivers.Gelfand.GF`) by `workflow/v2/stages/T4/VALIDATION/scripts/relocate_bc.py`: whole file, declarations moved from `GF.x` to `Gelfand.BaseChange.x` (renames in the T4 `DECL-ALLOWLIST.tsv`), references qualified, the imports of v1's `GF/Main`/`GF/Species` cut; statements and proofs otherwise unchanged.  The native statement on `HC ℓ E D`/`𝔼_E` (`prop:basechange`, `RQ2-5.14`) is in `Gelfand/BaseChange/Native.lean`.

*(2026-10-21, O-V2-6 round 2.)*  S10's `qBCss`/`qBCns`, `targetSplit_eq_cyclicSplit` and
`targetForm_zero`, which the paragraph below describes in the present tense, were deleted with the
GF residue at WP-13 (`44df340`).  The split base change here is `RepNil.toSplitFunctor`.

The three cases of T1 at `ℓ = 0`, where `Γ` is the cyclic quiver `− ⇄ +` and `𝔼(M)` has vertex
spaces `M_{∓1}` and edge maps `X`, `Y`:

* `E_bc_cyc_split_iso` — split → split: `hcBaseChange ⋙ 𝔼_{F''} ≅ 𝔼_F ⋙ toSplit`;
* `E_bc_cyc_mixed_iso` — non-split → split: `𝔼_E ⋙ toSplit ≅ hcBaseChangeNS ⋙ 𝔼_{E''}`;
* `E_bc_cyc_nn_iso` — non-split → non-split: `hcBaseChangeNN ⋙ 𝔼_{E''} ≅ 𝔼_E ⋙ qBCnnC`.

The quiver-side split base change is `RepNil.toSplitFunctor`, which is S10's `qBCss 0` resp.
`qBCns 0` read on `cyclicSplit` resp. `cyclicQ` (S10 states those on `targetSplit 0 = cyclicSplit`,
`targetForm 0 = cyclicQ`, which are equal only propositionally: `targetSplit_eq_cyclicSplit`,
`targetForm_zero`).  The `nn` quiver side `qBCnnC` is `BaseChangeNNRep`'s construction for the
cyclic quiver.  At `ℓ = 0` the stabilization is trivial (`φ_{v,c} = c` on the vertex spaces,
`phiCyc_eq_conj`), so the rational-structure square is `c''(b ⊗ m) = c''(b) ⊗ c(m)` alone.
-/

namespace RationalQuivers.Gelfand.BaseChange

open RationalQuivers.HC RationalQuivers.Gelfand RationalQuivers.RationalQuiver CategoryTheory
open scoped TensorProduct

/-! ## The split core at `ℓ = 0` -/

section CoreC

variable {F : Type} [Field F] [CharZero F] {F'' : Type} [Field F''] [CharZero F''] [Algebra F F'']

/-- The two edge maps `X`, `Y` of `𝔼` at `ℓ = 0` commute with `1 ⊗ −`, on underlying vectors.
@census none (helper; WP-15) -/
theorem bcEdgeC_val (A : Split.HCFObj F 0) :
    ∀ (e : Fin 2) (m : Split.V2i A (RQuiver.cyclic.source e)),
      ((Split.E_CycSplit_edge (A.bcF F'') e (bcVtx F'' A _ ((1 : F'') ⊗ₜ[F] m))
          : Split.V2i (A.bcF F'') (RQuiver.cyclic.target e)) : F'' ⊗[F] A.carrier)
        = (1 : F'') ⊗ₜ[F] ((Split.E_CycSplit_edge A e m : Split.V2i A (RQuiver.cyclic.target e)) : A.carrier)
  | 0, m => bc_X_tmul A 1 (m : A.carrier)
  | 1, m => bc_Y_tmul A 1 (m : A.carrier)

/-- `bcEdgeC_val` as an identity of `F''`-linear maps.  @census none (helper; WP-15) -/
theorem bcEdgeC_comm (A : Split.HCFObj F 0) (e : Fin 2)
    (x : F'' ⊗[F] Split.V2i A (RQuiver.cyclic.source e)) :
    bcVtx F'' A _ (LinearMap.baseChange F'' (Split.E_CycSplit_edge A e) x)
      = Split.E_CycSplit_edge (A.bcF F'') e (bcVtx F'' A _ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul c m =>
    have h2 : bcVtx F'' A _ (c ⊗ₜ[F] m) = c • bcVtx F'' A _ ((1 : F'') ⊗ₜ[F] m) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [LinearMap.baseChange_tmul, h2, map_smul]
    apply Subtype.ext
    rw [Submodule.coe_smul, bcEdgeC_val A e m, bcVtx_tmul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (F'') in
/-- **`𝔼_F(M)` base-changed to `F''` is `𝔼_{F''}(F'' ⊗_F M)`** at `ℓ = 0`.
@census none (helper; WP-15) -/
noncomputable def bcRepIsoC (A : Split.HCFObj F 0) :
    ((Split.E_CycSplit_obj A).obj.toSplit F'' : RationalQuiver.FDRep (cyclicSplit F''))
      ≅ (Split.E_CycSplit_obj (A.bcF F'')).obj :=
  fdRepIsoOfEquivs (fun v => bcVtx F'' A (cycIdx v))
    (fun e x => bcEdgeC_comm A e x) (fun _ _ _ => rfl)

variable (F'') in
/-- Naturality of `bcRepIsoC`.  @census none (helper; WP-15) -/
theorem bcRepIsoC_natural {A B : Split.HCFObj F 0} (f : A ⟶ B) (g : A.bcF F'' ⟶ B.bcF F'')
    (hg : ∀ (a : F'') (m : A.carrier), g.toLinearMap (a ⊗ₜ[F] m) = a ⊗ₜ[F] f.toLinearMap m)
    (v : Fin 2) :
    (bcVtx F'' B (cycIdx v)).toLinearMap ∘ₗ LinearMap.baseChange F'' (Split.E_CycSplit_map_ψ f v)
      = Split.E_CycSplit_map_ψ g v ∘ₗ (bcVtx F'' A (cycIdx v)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a m
  apply Subtype.ext
  show a ⊗ₜ[F] f.toLinearMap (m : A.carrier) = g.toLinearMap (a ⊗ₜ[F] (m : A.carrier))
  exact (hg a m).symm

end CoreC

/-! ## `ℓ = 0`, split → split and non-split → split -/

section SplitC

variable (F F'' : Type) [Field F] [CharZero F] [Field F''] [CharZero F''] [Algebra F F'']

/-- The square, in the direction the components are built in.  @census none (helper; WP-15) -/
noncomputable def E_bc_cyc_split_iso' :
    (Split.hcLambdaToF F 0 ⋙ Split.E_CycSplitFunctor) ⋙ RationalQuiver.RepNil.toSplitFunctor F'' ≅
      hcBaseChange 0 F F'' ⋙ Split.hcLambdaToF F'' 0 ⋙ Split.E_CycSplitFunctor :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _ (bcRepIsoC F'' ((Split.hcLambdaToF F 0).obj X)))
    (fun {X Y} f => by
      apply ObjectProperty.hom_ext
      apply RationalQuiver.Rep.Hom.ext
      funext v
      exact bcRepIsoC_natural F'' ((Split.hcLambdaToF F 0).map f)
        ((Split.hcLambdaToF F'' 0).map ((hcBaseChange 0 F F'').map f))
        (fun a m => LinearMap.baseChange_tmul _ _ _) v)

/-- **T1, case (1), `ℓ = 0`** — `hcBaseChange ⋙ 𝔼_{F''} ≅ 𝔼_F ⋙ toSplit` as functors
`HC_0(𝔤,K)_F ⥤ Rep^nil(cyclic_{F''})`, for every extension `F → F''` of characteristic-zero fields.

@census none (WP-15; T1, case (1), `ℓ = 0`) -/
noncomputable def E_bc_cyc_split_iso :
    hcBaseChange 0 F F'' ⋙ Split.hcLambdaToF F'' 0 ⋙ Split.E_CycSplitFunctor ≅
      (Split.hcLambdaToF F 0 ⋙ Split.E_CycSplitFunctor) ⋙ RationalQuiver.RepNil.toSplitFunctor F'' :=
  (E_bc_cyc_split_iso' F F'').symm

variable (E : Type) [Field E] [CharZero E] (D : SqrtNegOneExt E)
variable (E'' : Type) [Field E''] [CharZero E''] [Algebra D.carrier E'']

/-- The mixed square at `ℓ = 0`, in the direction the components are built in.
@census none (helper; WP-15) -/
noncomputable def E_bc_cyc_mixed_iso' (h : Gelfand.Cyclic.E_CycSpec D.card_gal) :
    Gelfand.Cyclic.E_CycFunctor D.card_gal h ⋙ RationalQuiver.RepNil.toSplitFunctor E'' ≅
      hcBaseChangeNS 0 E D E'' ⋙ Split.hcLambdaToF E'' 0 ⋙ Split.E_CycSplitFunctor :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ (bcRepIsoC E'' A.toF))
    (fun {A B} f => by
      apply ObjectProperty.hom_ext
      apply RationalQuiver.Rep.Hom.ext
      funext v
      exact bcRepIsoC_natural E'' ((GF.baseChangeE 0 E D).map f)
        ((Split.hcLambdaToF E'' 0).map ((hcBaseChange 0 D.carrier E'').map ((forgetDescent 0 E D).map f)))
        (fun a m => LinearMap.baseChange_tmul _ _ _) v)

/-- **T1, case (3), `ℓ = 0`** — `hcBaseChangeNS ⋙ 𝔼_{E''} ≅ 𝔼_E ⋙ toSplit` as functors
`HC_0(𝔤,K)_E ⥤ Rep^nil(cyclic_{E''})`, for every `E`-algebra map `E(√-1) → E''`.

@census none (WP-15; T1, case (3), `ℓ = 0`) -/
noncomputable def E_bc_cyc_mixed_iso (h : Gelfand.Cyclic.E_CycSpec D.card_gal) :
    hcBaseChangeNS 0 E D E'' ⋙ Split.hcLambdaToF E'' 0 ⋙ Split.E_CycSplitFunctor ≅
      Gelfand.Cyclic.E_CycFunctor D.card_gal h ⋙ RationalQuiver.RepNil.toSplitFunctor E'' :=
  (E_bc_cyc_mixed_iso' E D E'' h).symm

end SplitC

/-! ## `ℓ = 0`, non-split → non-split: the quiver side for the cyclic quiver -/

section CycSmul

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

/-- The non-trivial Galois element acts on the cyclic quiver by the swap.
@census none (helper; WP-15) -/
theorem cyclicOfCardTwo_rho_apply' (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) :
    (cyclicOfCardTwo K L h).ρ z = RQuiver.cyclicSwap := by
  letI := Classical.decEq Gal(L/K)
  have hr : (cyclicOfCardTwo K L h).ρ z = if z = 1 then 1 else RQuiver.cyclicSwap := rfl
  rw [hr, if_neg hz]

theorem cyclic_smul_vertex (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (v : (cyclicOfCardTwo K L h).V) :
    z • v = (RQuiver.Aut.toPermV RQuiver.cyclic RQuiver.cyclicSwap) v := by
  show (RQuiver.Aut.toPermV _ ((cyclicOfCardTwo K L h).ρ z)) v = _
  rw [cyclicOfCardTwo_rho_apply' K L h hz]
  rfl

theorem cyclic_smul_edge (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (e : (cyclicOfCardTwo K L h).E) :
    z • e = (RQuiver.Aut.toPermE RQuiver.cyclic RQuiver.cyclicSwap) e := by
  show (RQuiver.Aut.toPermE _ ((cyclicOfCardTwo K L h).ρ z)) e = _
  rw [cyclicOfCardTwo_rho_apply' K L h hz]
  rfl

end CycSmul

section RepNNC

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable {h : Nat.card Gal(L/K) = 2}
variable {K'' L'' : Type} [Field K''] [Field L''] [Algebra K'' L''] [IsGalois K'' L'']
  [FiniteDimensional K'' L''] {h'' : Nat.card Gal(L''/K'') = 2}
variable [Algebra L L'']

variable (R : RestrictionDatum K L K'' L'')

variable (h'') in
/-- A vertex of `Γ_K`, read as a vertex of `Γ_{K''}`: both quivers are the cyclic quiver.
@census none (helper; WP-15) -/
abbrev liftVC (v : (cyclicOfCardTwo K L h).V) : (cyclicOfCardTwo K'' L'' h'').V := v

variable (h) in
/-- A vertex of `Γ_{K''}`, read as a vertex of `Γ_K`.  @census none (helper; WP-15) -/
abbrev lowerVC (v : (cyclicOfCardTwo K'' L'' h'').V) : (cyclicOfCardTwo K L h).V := v

variable (h'') in
/-- An edge of `Γ_K`, read as an edge of `Γ_{K''}`.  @census none (helper; WP-15) -/
abbrev liftEC (e : (cyclicOfCardTwo K L h).E) : (cyclicOfCardTwo K'' L'' h'').E := e

/-- `θ(σ)` and `σ` act alike on the vertices.  @census none (helper; WP-15) -/
theorem RestrictionDatum.smul_vertexC (σ : Gal(L''/K'')) (v : (cyclicOfCardTwo K L h).V) :
    (R.θ σ • v : (cyclicOfCardTwo K L h).V) = σ • liftVC h'' v := by
  by_cases hσ : σ = 1
  · subst hσ; rw [map_one, one_smul, one_smul]
  · have e1 := cyclic_smul_vertex K L h (R.θ_ne_one hσ) v
    have e2 := cyclic_smul_vertex K'' L'' h'' hσ v
    exact e1.trans e2.symm

/-- `θ(σ)` and `σ` act alike on the edges.  @census none (helper; WP-15) -/
theorem RestrictionDatum.smul_edgeC (σ : Gal(L''/K'')) (e : (cyclicOfCardTwo K L h).E) :
    (R.θ σ • e : (cyclicOfCardTwo K L h).E) = σ • liftEC h'' e := by
  by_cases hσ : σ = 1
  · subst hσ; rw [map_one, one_smul, one_smul]
  · have e1 := cyclic_smul_edge K L h (R.θ_ne_one hσ) e
    have e2 := cyclic_smul_edge K'' L'' h'' hσ e
    exact e1.trans e2.symm

variable {R}

/-- The additive map `b ⊗ m ↦ τ(b) ⊗ φ'_g(m)`, for `τ ∘ ι = ι ∘ g`.
@census none (helper; WP-15) -/
noncomputable def phiNNC (M : Rep (cyclicOfCardTwo K L h)) (τ : Gal(L''/K'')) (g : Gal(L/K))
    (hg : ∀ a : L, τ (algebraMap L L'' a) = algebraMap L L'' (g a))
    {v w : (cyclicOfCardTwo K L h).V} (hvw : g • v = w) :
    L'' ⊗[L] M.M v →+ L'' ⊗[L] M.M w :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun m => τ b ⊗ₜ[L] M.φ' g hvw m)
      (fun m m' => by rw [map_add, TensorProduct.tmul_add]))
      (fun b b' => by ext m; simp [map_add, TensorProduct.add_tmul]))
    (fun a b m => by
      show τ (a • b) ⊗ₜ[L] M.φ' g hvw m = τ b ⊗ₜ[L] M.φ' g hvw (a • m)
      rw [M.φ'_smul, Algebra.smul_def, map_mul, hg, ← Algebra.smul_def, TensorProduct.smul_tmul])

omit [IsGalois K'' L''] [FiniteDimensional K'' L''] in
@[simp] theorem phiNNC_tmul (M : Rep (cyclicOfCardTwo K L h)) (τ : Gal(L''/K'')) (g : Gal(L/K))
    (hg : ∀ a : L, τ (algebraMap L L'' a) = algebraMap L L'' (g a))
    {v w : (cyclicOfCardTwo K L h).V} (hvw : g • v = w) (b : L'') (m : M.M v) :
    phiNNC M τ g hg hvw (b ⊗ₜ[L] m) = τ b ⊗ₜ[L] M.φ' g hvw m := rfl

theorem RestrictionDatum.inv_smul_vertexC (R : RestrictionDatum K L K'' L'') (σ : Gal(L''/K''))
    (v : (cyclicOfCardTwo K L h).V) :
    ((R.θ σ)⁻¹ • lowerVC h (σ • liftVC h'' v) : (cyclicOfCardTwo K L h).V) = v := by
  rw [← R.smul_vertexC (h := h) (h'' := h''), inv_smul_smul]

variable (R)

set_option backward.isDefEq.respectTransparency.types false in
/-- **The structure maps of the base change**, `φ''_{v,σ}(b ⊗ m) = σ(b) ⊗ φ_{v,θ(σ)}(m)`.
@census none (helper; WP-15) -/
noncomputable def phiNNEquivC (M : Rep (cyclicOfCardTwo K L h)) (σ : Gal(L''/K''))
    (v : (cyclicOfCardTwo K L h).V) :
    L'' ⊗[L] M.M v ≃+ L'' ⊗[L] M.M (σ • liftVC h'' v) where
  toFun := phiNNC M σ (R.θ σ) (R.θ_ι σ) (R.smul_vertexC σ v)
  invFun := phiNNC M σ⁻¹ (R.θ σ)⁻¹ (R.θ_ι_inv σ) (R.inv_smul_vertexC σ v)
  left_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m => rw [phiNNC_tmul, phiNNC_tmul, gal_inv_apply_apply, M.φ'_inv]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m => rw [phiNNC_tmul, phiNNC_tmul, gal_apply_inv_apply, M.φ'_inv']
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_add' x y := map_add _ x y

set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem phiNNEquivC_tmul (M : Rep (cyclicOfCardTwo K L h)) (σ : Gal(L''/K''))
    (v : (cyclicOfCardTwo K L h).V) (b : L'') (m : M.M v) :
    phiNNEquivC (h'' := h'') R M σ v (b ⊗ₜ[L] m)
      = σ b ⊗ₜ[L] M.φ' (R.θ σ) (R.smul_vertexC (h'' := h'') σ v) m := rfl

theorem famCastC_tmul (M : Rep (cyclicOfCardTwo K L h)) {v w : (cyclicOfCardTwo K L h).V}
    (hvw : v = w) (b : L'') (m : M.M v) :
    famCast (L := L'') (fun u => L'' ⊗[L] M.M u) hvw (b ⊗ₜ[L] m) = b ⊗ₜ[L] M.eqCast hvw m := by
  subst hvw; rfl

theorem eqCast_φ'_transC (M : Rep (cyclicOfCardTwo K L h)) (g : Gal(L/K))
    {v w x : (cyclicOfCardTwo K L h).V} (h1 : g • v = w) (h2 : w = x) (m : M.M v) :
    M.eqCast h2 (M.φ' g h1 m) = M.φ' g (h1.trans h2) m := by
  subst h2; rfl

variable (h'') in
set_option backward.isDefEq.respectTransparency.types false in
/-- Transport in the base-changed family, indexed by the vertices of `Γ_{K''}`.
@census none (helper; WP-15) -/
noncomputable def castNNC (M : Rep (cyclicOfCardTwo K L h))
    {v w : (cyclicOfCardTwo K'' L'' h'').V} (hvw : v = w) :
    L'' ⊗[L] M.M v ≃ₗ[L''] L'' ⊗[L] M.M w :=
  famCast (L := L'') (fun u : (cyclicOfCardTwo K'' L'' h'').V => L'' ⊗[L] M.M u) hvw

set_option backward.isDefEq.respectTransparency.types false in
theorem castNNC_tmul (M : Rep (cyclicOfCardTwo K L h)) {v w : (cyclicOfCardTwo K'' L'' h'').V}
    (hvw : v = w) (b : L'') (m : M.M v) :
    castNNC h'' M hvw (b ⊗ₜ[L] m) = b ⊗ₜ[L] M.eqCast hvw m := by
  subst hvw; rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The cocycle condition for `φ''`, transported.  @census none (helper; WP-15) -/
theorem phiNNC_cocycle (M : Rep (cyclicOfCardTwo K L h)) (σ τ : Gal(L''/K''))
    (v : (cyclicOfCardTwo K'' L'' h'').V) (x : L'' ⊗[L] M.M v) :
    castNNC h'' M (mul_smul σ τ v).symm
        (phiNNEquivC (h'' := h'') R M σ (τ • v) (phiNNEquivC (h'' := h'') R M τ v x))
      = phiNNEquivC (h'' := h'') R M (σ * τ) v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b m =>
    have e1 : (R.θ τ • lowerVC h v : (cyclicOfCardTwo K L h).V) = lowerVC h (τ • v) :=
      R.smul_vertexC τ v
    have h3 : ((R.θ σ * R.θ τ) • lowerVC h v : (cyclicOfCardTwo K L h).V)
        = lowerVC h ((σ * τ) • v) := by
      rw [mul_smul, e1]
      exact (R.smul_vertexC σ (lowerVC h (τ • v))).trans (mul_smul σ τ v).symm
    rw [phiNNEquivC_tmul, phiNNEquivC_tmul, castNNC_tmul, phiNNEquivC_tmul, eqCast_φ'_transC,
      M.φ'_comp (R.θ σ) (R.θ τ) _ _ h3, AlgEquiv.mul_apply]
    congr 1
    exact M.φ'_congr (map_mul R.θ σ τ).symm _ _ m
  | add x y hx hy => simp only [map_add, hx, hy]

theorem eqCast_φEdge'_transC (M : Rep (cyclicOfCardTwo K L h)) (e : (cyclicOfCardTwo K L h).E)
    {a b b' : (cyclicOfCardTwo K L h).V} (ha : (cyclicOfCardTwo K L h).toRQuiver.source e = a)
    (hb : (cyclicOfCardTwo K L h).toRQuiver.target e = b) (hb2 : b = b') (x : M.M a) :
    M.eqCast hb2 (M.φEdge' e ha hb x) = M.φEdge' e ha (hb.trans hb2) x := by
  subst hb2; rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The edge equivariance for `φ''`, transported.  The edge maps are written as `φEdge'` with
endpoints named in `Γ_{K''}`, so that every vertex term is one of `Γ_{K''}`.
@census none (helper; WP-15) -/
theorem phiNNC_edge (M : Rep (cyclicOfCardTwo K L h)) (σ : Gal(L''/K''))
    (e : (cyclicOfCardTwo K'' L'' h'').E)
    (x : L'' ⊗[L] M.M ((cyclicOfCardTwo K'' L'' h'').toRQuiver.source e)) :
    castNNC h'' M ((cyclicOfCardTwo K'' L'' h'').target_smul σ e)
        (LinearMap.baseChange L''
          (M.φEdge' (σ • e) (a := (cyclicOfCardTwo K'' L'' h'').toRQuiver.source (σ • e))
            (b := (cyclicOfCardTwo K'' L'' h'').toRQuiver.target (σ • e)) rfl rfl)
          (castNNC h'' M ((cyclicOfCardTwo K'' L'' h'').source_smul σ e).symm
            (phiNNEquivC (h'' := h'') R M σ ((cyclicOfCardTwo K'' L'' h'').toRQuiver.source e) x)))
      = phiNNEquivC (h'' := h'') R M σ ((cyclicOfCardTwo K'' L'' h'').toRQuiver.target e)
          (LinearMap.baseChange L''
            (M.φEdge' e (a := (cyclicOfCardTwo K'' L'' h'').toRQuiver.source e)
              (b := (cyclicOfCardTwo K'' L'' h'').toRQuiver.target e) rfl rfl) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b m =>
    rw [phiNNEquivC_tmul, castNNC_tmul, LinearMap.baseChange_tmul, castNNC_tmul,
      LinearMap.baseChange_tmul, phiNNEquivC_tmul]
    congr 1
    rw [eqCast_φEdge'_transC, eqCast_φ'_transC]
    exact M.φEdge'_φ' (R.θ σ) (R.smul_edgeC σ e) rfl rfl rfl _ _ _ m
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency.types false in
/-- **The `nn` base change of a representation of the cyclic quiver.**
@census none (helper; WP-15; the `nn` shape of `RQ-5.08-C4`, quiver side) -/
noncomputable def Rep.bcNNC (M : Rep (cyclicOfCardTwo K L h)) :
    Rep (cyclicOfCardTwo K'' L'' h'') :=
  Rep.ofFiniteDimensional (Γ := cyclicOfCardTwo K'' L'' h'') (fun v => L'' ⊗[L] M.M v)
    (fun σ v => phiNNEquivC (h'' := h'') R M σ v)
    (fun σ v a x => by
      induction x using TensorProduct.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | tmul b m =>
        rw [TensorProduct.smul_tmul', phiNNEquivC_tmul, phiNNEquivC_tmul, smul_eq_mul, map_mul,
          TensorProduct.smul_tmul', smul_eq_mul]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add])
    (fun σ τ v x => sigma_mk_eq_of_famCast (L := L'') (fun u => L'' ⊗[L] M.M u)
        (mul_smul σ τ v).symm _ _ (phiNNC_cocycle R M σ τ v x))
    (fun e => LinearMap.baseChange L'' (M.φEdge e))
    (fun σ e x x' hxx' => by
      have hx' : x' = castNNC h'' M ((cyclicOfCardTwo K'' L'' h'').source_smul σ e).symm
          (phiNNEquivC (h'' := h'') R M σ _ x) :=
        (famCast_of_sigma_mk_eq (L := L'') (fun u => L'' ⊗[L] M.M u)
          ((cyclicOfCardTwo K'' L'' h'').source_smul σ e).symm _ _ hxx'.symm).symm
      subst hx'
      exact sigma_mk_eq_of_famCast (L := L'') (fun u => L'' ⊗[L] M.M u)
        ((cyclicOfCardTwo K'' L'' h'').target_smul σ e) _ _ (phiNNC_edge R M σ e x))

set_option backward.isDefEq.respectTransparency.types false in
@[simp] theorem Rep.bcNNC_M (M : Rep (cyclicOfCardTwo K L h)) (v : (cyclicOfCardTwo K L h).V) :
    (Rep.bcNNC (h'' := h'') R M).M v = L'' ⊗[L] M.M v := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem Rep.bcNNC_φEdge (M : Rep (cyclicOfCardTwo K L h)) (e : (cyclicOfCardTwo K L h).E) :
    (Rep.bcNNC (h'' := h'') R M).φEdge e = LinearMap.baseChange L'' (M.φEdge e) := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem Rep.bcNNC_φ_tmul (M : Rep (cyclicOfCardTwo K L h)) (σ : Gal(L''/K''))
    (v : (cyclicOfCardTwo K L h).V) (b : L'') (m : M.M v) :
    (Rep.bcNNC (h'' := h'') R M).φ σ v (b ⊗ₜ[L] m)
      = σ b ⊗ₜ[L] M.φ' (R.θ σ) (R.smul_vertexC (h'' := h'') σ v) m := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Path composites of the `nn` base change.  @census none (helper; WP-15) -/
theorem Rep.pathMap_bcNNC (M : Rep (cyclicOfCardTwo K L h)) {a b : (cyclicOfCardTwo K L h).V}
    (p : Quiver.Path a b) :
    (Rep.bcNNC (h'' := h'') R M).pathMap p = LinearMap.baseChange L'' (M.pathMap p) :=
  pathCompose_baseChange (L'' := L'') M.M M.φEdge p

/-- A morphism commutes with the transported structure maps.  @census none (helper; WP-15) -/
theorem ψ_φ'C {M N : Rep (cyclicOfCardTwo K L h)} (f : Rep.Hom M N) (g : Gal(L/K))
    {v w : (cyclicOfCardTwo K L h).V} (hvw : g • v = w) (m : M.M v) :
    f.ψ w (M.φ' g hvw m) = N.φ' g hvw (f.ψ v m) := by
  subst hvw; exact f.rational g v m

set_option backward.isDefEq.respectTransparency.types false in
/-- The `nn` base change of a morphism.  @census none (helper; WP-15) -/
noncomputable def Rep.Hom.bcNNC {M N : Rep (cyclicOfCardTwo K L h)} (f : Rep.Hom M N) :
    Rep.Hom (Rep.bcNNC (h'' := h'') R M) (Rep.bcNNC (h'' := h'') R N) where
  ψ v := LinearMap.baseChange L'' (f.ψ v)
  edge e m := by
    have h1 : (f.ψ _) ∘ₗ M.φEdge e = N.φEdge e ∘ₗ (f.ψ _) := LinearMap.ext (f.edge e)
    have h2 := congrArg (LinearMap.baseChange L'') h1
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h2
    exact congrArg (fun g : (L'' ⊗[L] M.M _) →ₗ[L''] (L'' ⊗[L] N.M _) => g m) h2
  rational σ v x := by
    show LinearMap.baseChange L'' (f.ψ _) (phiNNEquivC (h'' := h'') R M σ v x)
      = phiNNEquivC (h'' := h'') R N σ v (LinearMap.baseChange L'' (f.ψ v) x)
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b m =>
      rw [phiNNEquivC_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, phiNNEquivC_tmul]
      congr 1
      exact ψ_φ'C f _ _ m
    | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency.types false in
/-- **The `nn` quiver-side base-change functor for the cyclic quiver**
`Rep^nil(cyclic_K) ⥤ Rep^nil(cyclic_{K''})`, constructed.
@census none (helper; WP-15; the `nn` shape of `RQ-5.08-C4` at `ℓ = 0`) -/
noncomputable def qBCnnC :
    (RationalQuiver.RepNil (cyclicOfCardTwo K L h)).FullSubcategory ⥤
      (RationalQuiver.RepNil (cyclicOfCardTwo K'' L'' h'')).FullSubcategory where
  obj M :=
    ⟨{ toRep := Rep.bcNNC R M.obj.toRep
       finiteDimensional := fun v => by
         haveI := M.obj.finiteDimensional v
         exact Module.Finite.base_change L L'' (M.obj.toRep.M v) },
      by
        obtain ⟨n, hn⟩ := M.property
        refine ⟨n, fun a b p hp => ?_⟩
        show (Rep.bcNNC R M.obj.toRep).pathMap p = 0
        rw [Rep.pathMap_bcNNC]
        exact (congrArg (LinearMap.baseChange L'') (hn a b p hp)).trans LinearMap.baseChange_zero⟩
  map f := ⟨Rep.Hom.bcNNC R f.hom⟩
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply Rep.Hom.ext
    funext v
    show LinearMap.baseChange L'' LinearMap.id = _
    rw [LinearMap.baseChange_id]
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply Rep.Hom.ext
    funext v
    show LinearMap.baseChange L'' (_ ∘ₗ _) = _
    rw [LinearMap.baseChange_comp]
    rfl

end RepNNC

/-! ## `ℓ = 0`, non-split → non-split: the square -/

section NNC

variable {E : Type} [Field E] [CharZero E] {D : SqrtNegOneExt E}
variable {E'' : Type} [Field E''] [CharZero E''] {D'' : SqrtNegOneExt E''}
variable [Algebra E E''] [Algebra D.carrier D''.carrier] [Algebra E D''.carrier]
  [IsScalarTower E E'' D''.carrier] [IsScalarTower E D.carrier D''.carrier]

omit [Algebra E E''] [Algebra D.carrier D''.carrier] [Algebra E D''.carrier]
  [IsScalarTower E E'' D''.carrier] [IsScalarTower E D.carrier D''.carrier] in
/-- The underlying vector of an element of a vertex space of `𝔼(M)` at `ℓ = 0`.
@census none (helper) -/
abbrev vvalC (A : HCEObj 0 E D) {w : Fin 2} (x : Gelfand.Cyclic.V2 A w) : A.carrier := (x : A.carrier)

omit [Algebra E E''] [Algebra D.carrier D''.carrier] [Algebra E D''.carrier]
  [IsScalarTower E E'' D''.carrier] [IsScalarTower E D.carrier D''.carrier] in
/-- The transported structure maps of `𝔼_E(M)` at `ℓ = 0`, on underlying vectors.
@census none (helper; WP-15) -/
theorem E_Cyc_φ'_val (hcard : Nat.card (D.carrier ≃ₐ[E] D.carrier) = 2) (A : HCEObj 0 E D)
    (hA : Gelfand.Cyclic.ObjSpecC hcard A) (g : D.carrier ≃ₐ[E] D.carrier) {v w : (Gelfand.Cyclic.cyclicQ hcard).V}
    (hvw : g • v = w) (m : Gelfand.Cyclic.V2 A v) :
    vvalC A (w := w) ((Gelfand.Cyclic.E_Cyc_rep hcard A hA).φ' g hvw m) = Gelfand.Cyclic.galActC A g v (vvalC A m) := by
  subst hvw; rfl

/-- **The rational structures commute with base change at `ℓ = 0`**: there `φ_{v,c} = c` on the
vertex spaces, so this is `c''(b ⊗ m) = c''(b) ⊗ c(m)`.  @census none (helper; WP-15) -/
theorem galActC_bcNN (hι : ConjCompat D D'') (A : HCEObj 0 E D)
    (σ : D''.carrier ≃ₐ[E''] D''.carrier) (v : Fin 2) (b : D''.carrier) (m : A.carrier)
    (hm : m ∈ A.setup.weight.comp (cycIdx v)) :
    σ b ⊗ₜ[D.carrier] Gelfand.Cyclic.galActC A ((restrictionDatum D D'' hι).θ σ) v m
      = Gelfand.Cyclic.galActC (A.bcNN hι) σ v (b ⊗ₜ[D.carrier] m) := by
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, Gelfand.Cyclic.galActC_one, Gelfand.Cyclic.galActC_one, AlgEquiv.one_apply]
  · rw [Gelfand.Cyclic.galActC_of_ne A ((restrictionDatum D D'' hι).θ_ne_one hσ),
      Gelfand.Cyclic.galActC_of_ne (A.bcNN hι) hσ, Gelfand.Cyclic.phiCyc_eq_conj A v m hm,
      Gelfand.Cyclic.phiCyc_eq_conj (A.bcNN hι) v _ (Submodule.tmul_mem_baseChange_of_mem _ hm)]
    show σ b ⊗ₜ[D.carrier] A.setup.conj m
      = conjBC hι A.setup.conj A.setup.conj_smul A.setup.conj_involutive (b ⊗ₜ[D.carrier] m)
    rw [conjBC_tmul, D''.eq_conj_of_ne_one hσ]

variable (D D'') in
set_option backward.isDefEq.respectTransparency.types false in
/-- `E''(√-1) ⊗ 𝔼_E(M)` at `ℓ = 0`.  @census none (helper; WP-15) -/
noncomputable def E_Cyc_fdrep_bcNN (hι : ConjCompat D D'') (A : HCEObj 0 E D)
    (hA : Gelfand.Cyclic.ObjSpecC D.card_gal A) :
    RationalQuiver.FDRep (cyclicOfCardTwo E'' D''.carrier D''.card_gal) where
  toRep := Rep.bcNNC (h'' := D''.card_gal) (restrictionDatum D D'' hι) (Gelfand.Cyclic.E_Cyc_rep D.card_gal A hA)
  finiteDimensional v := by
    haveI : Module.Finite D.carrier (Gelfand.Cyclic.V2 A v) := A.admissible _
    exact Module.Finite.base_change D.carrier D''.carrier (Gelfand.Cyclic.V2 A v)

set_option backward.isDefEq.respectTransparency.types false in
/-- The rational-structure square of the component at `ℓ = 0`, as an identity of additive maps.
@census none (helper; WP-15) -/
theorem bcNNC_hrat (hι : ConjCompat D D'') (A : HCEObj 0 E D) (hA : Gelfand.Cyclic.ObjSpecC D.card_gal A)
    (hA'' : Gelfand.Cyclic.ObjSpecC D''.card_gal (A.bcNN hι)) (σ : D''.carrier ≃ₐ[E''] D''.carrier)
    (v : (Gelfand.Cyclic.cyclicQ D''.card_gal).V) :
    (((bcVtx D''.carrier A.toF (cycIdx (σ • v))).toLinearMap.toAddMonoidHom.comp
        (phiNNEquivC (h := D.card_gal) (h'' := D''.card_gal) (restrictionDatum D D'' hι)
          (Gelfand.Cyclic.E_Cyc_rep D.card_gal A hA) σ v).toAddMonoidHom :
        D''.carrier ⊗[D.carrier] Gelfand.Cyclic.V2 A v →+ Gelfand.Cyclic.V2 (A.bcNN hι) (σ • v)))
      = (Gelfand.Cyclic.E_Cyc_φS D''.card_gal (A.bcNN hι) hA'' σ v).toAddMonoidHom.comp
          (bcVtx D''.carrier A.toF (cycIdx v)).toLinearMap.toAddMonoidHom := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b m =>
    apply Subtype.ext
    show σ b ⊗ₜ[D.carrier] vvalC A ((Gelfand.Cyclic.E_Cyc_rep D.card_gal A hA).φ'
        ((restrictionDatum D D'' hι).θ σ)
        ((restrictionDatum D D'' hι).smul_vertexC (h := D.card_gal) (h'' := D''.card_gal) σ v) m)
      = Gelfand.Cyclic.galActC (A.bcNN hι) σ v (b ⊗ₜ[D.carrier] vvalC A m)
    rw [E_Cyc_φ'_val]
    exact galActC_bcNN hι A σ v b m m.2
  | add x y hx hy => simp only [map_add, hx, hy]

variable (D D'') in
/-- **The component of case (2) at `ℓ = 0`.**  @census none (helper; WP-15) -/
noncomputable def bcNNRepIsoC (hι : ConjCompat D D'') (A : HCEObj 0 E D)
    (hA : Gelfand.Cyclic.ObjSpecC D.card_gal A) (hA'' : Gelfand.Cyclic.ObjSpecC D''.card_gal (A.bcNN hι)) :
    E_Cyc_fdrep_bcNN D D'' hι A hA ≅ (Gelfand.Cyclic.E_Cyc_obj D''.card_gal (A.bcNN hι) hA'').obj :=
  fdRepIsoOfEquivs (fun v => bcVtx D''.carrier A.toF (cycIdx v))
    (fun e x => bcEdgeC_comm A.toF e x)
    (fun σ v x => DFunLike.congr_fun (bcNNC_hrat hι A hA hA'' σ v) x)

variable (E D E'' D'') in
set_option backward.isDefEq.respectTransparency.types false in
/-- The square of case (2) at `ℓ = 0`, in the direction the components are built in.
@census none (helper; WP-15) -/
noncomputable def E_bc_cyc_nn_iso' (hι : ConjCompat D D'') (h : Gelfand.Cyclic.E_CycSpec D.card_gal)
    (h'' : Gelfand.Cyclic.E_CycSpec D''.card_gal) :
    Gelfand.Cyclic.E_CycFunctor D.card_gal h ⋙ qBCnnC (h'' := D''.card_gal) (restrictionDatum D D'' hι) ≅
      hcBaseChangeNN 0 E D E'' D'' hι ⋙ Gelfand.Cyclic.E_CycFunctor D''.card_gal h'' :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ (bcNNRepIsoC D D'' hι A (h.1 A) (h''.1 _)))
    (fun {A B} f => by
      apply ObjectProperty.hom_ext
      apply RationalQuiver.Rep.Hom.ext
      funext v
      exact bcRepIsoC_natural D''.carrier ((GF.baseChangeE 0 E D).map f)
        ((GF.baseChangeE 0 E'' D'').map ((hcBaseChangeNN 0 E D E'' D'' hι).map f))
        (fun a m => LinearMap.baseChange_tmul _ _ _) v)

variable (E D E'' D'') in
/-- **T1, case (2), `ℓ = 0`** — `hcBaseChangeNN ⋙ 𝔼_{E''} ≅ 𝔼_E ⋙ qBCnnC` as functors
`HC_0(𝔤,K)_E ⥤ Rep^nil(cyclic_{E''})`, `cyclic_{E''}` the `E''`-rational cyclic quiver.

@census none (WP-15; T1, case (2), `ℓ = 0`) -/
noncomputable def E_bc_cyc_nn_iso (hι : ConjCompat D D'') (h : Gelfand.Cyclic.E_CycSpec D.card_gal)
    (h'' : Gelfand.Cyclic.E_CycSpec D''.card_gal) :
    hcBaseChangeNN 0 E D E'' D'' hι ⋙ Gelfand.Cyclic.E_CycFunctor D''.card_gal h'' ≅
      Gelfand.Cyclic.E_CycFunctor D.card_gal h ⋙ qBCnnC (h'' := D''.card_gal) (restrictionDatum D D'' hι) :=
  (E_bc_cyc_nn_iso' E D E'' D'' hι h h'').symm

end NNC

end RationalQuivers.Gelfand.BaseChange
