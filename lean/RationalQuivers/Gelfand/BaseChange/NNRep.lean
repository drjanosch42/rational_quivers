import RationalQuivers.Gelfand.BaseChange.NNStab

/-!
# Base change non-split → non-split, quiver side (WP-15, T1 case (2))

*Provenance.*  Relocated in stage T4 (WP-11) from `GF/BaseChangeNNRep.lean` (v1 `RationalQuivers.Gelfand.GF`) by `workflow/v2/stages/T4/VALIDATION/scripts/relocate_bc.py`: whole file, declarations moved from `GF.x` to `Gelfand.BaseChange.x` (renames in the T4 `DECL-ALLOWLIST.tsv`), references qualified, the imports of v1's `GF/Main`/`GF/Species` cut; statements and proofs otherwise unchanged.  The native statement on `HC ℓ E D`/`𝔼_E` (`prop:basechange`, `RQ2-5.14`) is in `Gelfand/BaseChange/Native.lean`.

For quadratic Galois `L/K`, `L''/K''`, an algebra map `ι : L → L''`, and the restriction
`θ : Gal(L''/K'') → Gal(L/K)` (`θ(1) = 1`, `θ(c'') = c`, `σ ∘ ι = ι ∘ θ(σ)`), the base change of a
`K`-rational representation `M` of the Gelfand quiver `Γ_K` is the `K''`-rational representation

* `M''(v) = L'' ⊗_L M(v)`, edge maps `L'' ⊗ φ_e`,
* `φ''_{v,σ}(b ⊗ m) = σ(b) ⊗ φ_{v,θ(σ)}(m)`

of `Γ_{K''}` (`Rep.bcNN`), and `qBCnnRel` is the functor
`Rep^nil_rel(Γ_K) ⥤ Rep^nil_rel(Γ_{K''})` — the `nn` shape that S10's `E_E_equivalence`
`@divergence` (4) left unbuilt, **constructed** here.  The two obstacles that note recorded are
handled as follows: the semilinear structure maps are *carried* (`phiNN`, via
`TensorProduct.liftAddHom` on the `ι`-balanced map `(b, m) ↦ σ(b) ⊗ φ'(m)`), and the cocycle and
edge-equivariance equations in the disjoint union `⊔_v M(v)` are reduced, by
`sigma_mk_eq_of_famCast`, to transported equations of additive maps, which are checked on pure
tensors with `Rep.φ'_comp` and `Rep.φEdge'_φ'`.
-/

namespace RationalQuivers.Gelfand.BaseChange

open RationalQuivers.HC RationalQuivers.Gelfand RationalQuivers.RationalQuiver CategoryTheory
open scoped TensorProduct

/-! ## Disjoint-union bookkeeping -/

section Sigma

variable {L : Type} [Field L] {V : Type}

/-- An equation in a disjoint union, from a transported equation.  @census none (helper; WP-15) -/
theorem sigma_mk_eq_of_famCast (X : V → Type) [∀ v, AddCommGroup (X v)] [∀ v, Module L (X v)]
    {v w : V} (h : v = w) (x : X v) (y : X w) (hxy : famCast (L := L) X h x = y) :
    (⟨v, x⟩ : (u : V) × X u) = ⟨w, y⟩ := by
  subst h; subst hxy; rfl

/-- A transported equation, from an equation in a disjoint union.  @census none (helper; WP-15) -/
theorem famCast_of_sigma_mk_eq (X : V → Type) [∀ v, AddCommGroup (X v)] [∀ v, Module L (X v)]
    {v w : V} (h : v = w) (x : X v) (y : X w) (hxy : (⟨v, x⟩ : (u : V) × X u) = ⟨w, y⟩) :
    famCast (L := L) X h x = y := by
  subst h
  have := (Sigma.mk.inj_iff.mp hxy).2
  exact eq_of_heq this

end Sigma

/-! ## The `nn` base change of a representation of the Gelfand quiver -/

section RepNN

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable {h : Nat.card Gal(L/K) = 2}
variable {K'' L'' : Type} [Field K''] [Field L''] [Algebra K'' L''] [IsGalois K'' L'']
  [FiniteDimensional K'' L''] {h'' : Nat.card Gal(L''/K'') = 2}
variable [Algebra L L'']

/-- The restriction datum `θ : Gal(L''/K'') → Gal(L/K)` along `ι : L → L''`.
@census none (helper; WP-15) -/
structure RestrictionDatum (K L K'' L'' : Type) [Field K] [Field L] [Algebra K L] [Field K'']
    [Field L''] [Algebra K'' L''] [Algebra L L''] where
  /-- the restriction map -/
  θ : Gal(L''/K'') →* Gal(L/K)
  /-- it is injective on the identity: `θ(σ) = 1 → σ = 1` -/
  θ_eq_one : ∀ σ, θ σ = 1 → σ = 1
  /-- `σ ∘ ι = ι ∘ θ(σ)` -/
  θ_ι : ∀ (σ : Gal(L''/K'')) (a : L), σ (algebraMap L L'' a) = algebraMap L L'' (θ σ a)

variable (R : RestrictionDatum K L K'' L'')

variable (h'') in
/-- A vertex of `Γ_K`, read as a vertex of `Γ_{K''}`: both quivers are the Gelfand quiver.
@census none (helper; WP-15) -/
abbrev liftV (v : (gelfandOfCardTwo K L h).V) : (gelfandOfCardTwo K'' L'' h'').V := v

variable (h) in
/-- A vertex of `Γ_{K''}`, read as a vertex of `Γ_K`.  @census none (helper; WP-15) -/
abbrev lowerV (v : (gelfandOfCardTwo K'' L'' h'').V) : (gelfandOfCardTwo K L h).V := v

variable (h'') in
/-- An edge of `Γ_K`, read as an edge of `Γ_{K''}`.  @census none (helper; WP-15) -/
abbrev liftE (e : (gelfandOfCardTwo K L h).E) : (gelfandOfCardTwo K'' L'' h'').E := e

omit [IsGalois K L] [FiniteDimensional K L] [IsGalois K'' L''] [FiniteDimensional K'' L''] in
theorem RestrictionDatum.θ_ne_one {σ : Gal(L''/K'')} (hσ : σ ≠ 1) : R.θ σ ≠ 1 :=
  fun h1 => hσ (R.θ_eq_one σ h1)

/-- `θ(σ)` and `σ` act alike on the vertices.  @census none (helper; WP-15) -/
theorem RestrictionDatum.smul_vertex (σ : Gal(L''/K'')) (v : (gelfandOfCardTwo K L h).V) :
    (R.θ σ • v : (gelfandOfCardTwo K L h).V) = σ • liftV h'' v := by
  by_cases hσ : σ = 1
  · subst hσ; rw [map_one, one_smul, one_smul]
  · have e1 := Examples.gelfand_smul_vertex K L h (R.θ_ne_one hσ) v
    have e2 := Examples.gelfand_smul_vertex K'' L'' h'' hσ v
    exact e1.trans e2.symm

/-- `θ(σ)` and `σ` act alike on the edges.  @census none (helper; WP-15) -/
theorem RestrictionDatum.smul_edge (σ : Gal(L''/K'')) (e : (gelfandOfCardTwo K L h).E) :
    (R.θ σ • e : (gelfandOfCardTwo K L h).E) = σ • liftE h'' e := by
  by_cases hσ : σ = 1
  · subst hσ; rw [map_one, one_smul, one_smul]
  · have e1 := Examples.gelfand_smul_edge K L h (R.θ_ne_one hσ) e
    have e2 := Examples.gelfand_smul_edge K'' L'' h'' hσ e
    exact e1.trans e2.symm

variable {R}

/-- The additive map `b ⊗ m ↦ τ(b) ⊗ φ'_g(m)`, for `τ ∘ ι = ι ∘ g`.
@census none (helper; WP-15) -/
noncomputable def phiNN (M : Rep (gelfandOfCardTwo K L h)) (τ : Gal(L''/K'')) (g : Gal(L/K))
    (hg : ∀ a : L, τ (algebraMap L L'' a) = algebraMap L L'' (g a))
    {v w : (gelfandOfCardTwo K L h).V} (hvw : g • v = w) :
    L'' ⊗[L] M.M v →+ L'' ⊗[L] M.M w :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun m => τ b ⊗ₜ[L] M.φ' g hvw m)
      (fun m m' => by rw [map_add, TensorProduct.tmul_add]))
      (fun b b' => by ext m; simp [map_add, TensorProduct.add_tmul]))
    (fun a b m => by
      show τ (a • b) ⊗ₜ[L] M.φ' g hvw m = τ b ⊗ₜ[L] M.φ' g hvw (a • m)
      rw [M.φ'_smul, Algebra.smul_def, map_mul, hg, ← Algebra.smul_def, TensorProduct.smul_tmul])

omit [IsGalois K'' L''] [FiniteDimensional K'' L''] in
@[simp] theorem phiNN_tmul (M : Rep (gelfandOfCardTwo K L h)) (τ : Gal(L''/K'')) (g : Gal(L/K))
    (hg : ∀ a : L, τ (algebraMap L L'' a) = algebraMap L L'' (g a))
    {v w : (gelfandOfCardTwo K L h).V} (hvw : g • v = w) (b : L'') (m : M.M v) :
    phiNN M τ g hg hvw (b ⊗ₜ[L] m) = τ b ⊗ₜ[L] M.φ' g hvw m := rfl

theorem gal_inv_apply_apply {F F' : Type} [Field F] [Field F'] [Algebra F F'] (σ : Gal(F'/F))
    (x : F') : σ⁻¹ (σ x) = x := by
  rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

theorem gal_apply_inv_apply {F F' : Type} [Field F] [Field F'] [Algebra F F'] (σ : Gal(F'/F))
    (x : F') : σ (σ⁻¹ x) = x := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

omit [IsGalois K L] [FiniteDimensional K L] [IsGalois K'' L''] [FiniteDimensional K'' L''] in
theorem RestrictionDatum.θ_ι_inv (R : RestrictionDatum K L K'' L'') (σ : Gal(L''/K'')) (a : L) :
    σ⁻¹ (algebraMap L L'' a) = algebraMap L L'' ((R.θ σ)⁻¹ a) := by
  apply σ.injective
  rw [gal_apply_inv_apply, R.θ_ι, gal_apply_inv_apply]

theorem RestrictionDatum.inv_smul_vertex (R : RestrictionDatum K L K'' L'') (σ : Gal(L''/K''))
    (v : (gelfandOfCardTwo K L h).V) :
    ((R.θ σ)⁻¹ • lowerV h (σ • liftV h'' v) : (gelfandOfCardTwo K L h).V) = v := by
  rw [← R.smul_vertex (h := h) (h'' := h''), inv_smul_smul]

variable (R)

/-- **The structure maps of the base change**, `φ''_{v,σ}(b ⊗ m) = σ(b) ⊗ φ_{v,θ(σ)}(m)`.
@census none (helper; WP-15) -/
noncomputable def phiNNEquiv (M : Rep (gelfandOfCardTwo K L h)) (σ : Gal(L''/K''))
    (v : (gelfandOfCardTwo K L h).V) :
    L'' ⊗[L] M.M v ≃+ L'' ⊗[L] M.M (σ • liftV h'' v) where
  toFun := phiNN M σ (R.θ σ) (R.θ_ι σ) (R.smul_vertex σ v)
  invFun := phiNN M σ⁻¹ (R.θ σ)⁻¹ (R.θ_ι_inv σ) (R.inv_smul_vertex σ v)
  left_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m => rw [phiNN_tmul, phiNN_tmul, gal_inv_apply_apply, M.φ'_inv]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b m => rw [phiNN_tmul, phiNN_tmul, gal_apply_inv_apply, M.φ'_inv']
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  map_add' x y := map_add _ x y

@[simp] theorem phiNNEquiv_tmul (M : Rep (gelfandOfCardTwo K L h)) (σ : Gal(L''/K''))
    (v : (gelfandOfCardTwo K L h).V) (b : L'') (m : M.M v) :
    phiNNEquiv (h'' := h'') R M σ v (b ⊗ₜ[L] m)
      = σ b ⊗ₜ[L] M.φ' (R.θ σ) (R.smul_vertex (h'' := h'') σ v) m := rfl

theorem famCast_tmul (M : Rep (gelfandOfCardTwo K L h)) {v w : (gelfandOfCardTwo K L h).V}
    (hvw : v = w) (b : L'') (m : M.M v) :
    famCast (L := L'') (fun u => L'' ⊗[L] M.M u) hvw (b ⊗ₜ[L] m) = b ⊗ₜ[L] M.eqCast hvw m := by
  subst hvw; rfl

theorem eqCast_φ'_trans (M : Rep (gelfandOfCardTwo K L h)) (g : Gal(L/K))
    {v w x : (gelfandOfCardTwo K L h).V} (h1 : g • v = w) (h2 : w = x) (m : M.M v) :
    M.eqCast h2 (M.φ' g h1 m) = M.φ' g (h1.trans h2) m := by
  subst h2; rfl

variable (h'') in
/-- Transport in the base-changed family, indexed by the vertices of `Γ_{K''}`.
@census none (helper; WP-15) -/
noncomputable def castNN (M : Rep (gelfandOfCardTwo K L h))
    {v w : (gelfandOfCardTwo K'' L'' h'').V} (hvw : v = w) :
    L'' ⊗[L] M.M v ≃ₗ[L''] L'' ⊗[L] M.M w :=
  famCast (L := L'') (fun u : (gelfandOfCardTwo K'' L'' h'').V => L'' ⊗[L] M.M u) hvw

theorem castNN_tmul (M : Rep (gelfandOfCardTwo K L h)) {v w : (gelfandOfCardTwo K'' L'' h'').V}
    (hvw : v = w) (b : L'') (m : M.M v) :
    castNN h'' M hvw (b ⊗ₜ[L] m) = b ⊗ₜ[L] M.eqCast hvw m := by
  subst hvw; rfl

/-- The cocycle condition for `φ''`, transported.  @census none (helper; WP-15) -/
theorem phiNN_cocycle (M : Rep (gelfandOfCardTwo K L h)) (σ τ : Gal(L''/K''))
    (v : (gelfandOfCardTwo K'' L'' h'').V) (x : L'' ⊗[L] M.M v) :
    castNN h'' M (mul_smul σ τ v).symm
        (phiNNEquiv (h'' := h'') R M σ (τ • v) (phiNNEquiv (h'' := h'') R M τ v x))
      = phiNNEquiv (h'' := h'') R M (σ * τ) v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b m =>
    have e1 : (R.θ τ • lowerV h v : (gelfandOfCardTwo K L h).V) = lowerV h (τ • v) :=
      R.smul_vertex τ v
    have h3 : ((R.θ σ * R.θ τ) • lowerV h v : (gelfandOfCardTwo K L h).V)
        = lowerV h ((σ * τ) • v) := by
      rw [mul_smul, e1]
      exact (R.smul_vertex σ (lowerV h (τ • v))).trans (mul_smul σ τ v).symm
    rw [phiNNEquiv_tmul, phiNNEquiv_tmul, castNN_tmul, phiNNEquiv_tmul, eqCast_φ'_trans,
      M.φ'_comp (R.θ σ) (R.θ τ) _ _ h3, AlgEquiv.mul_apply]
    congr 1
    exact M.φ'_congr (map_mul R.θ σ τ).symm _ _ m
  | add x y hx hy => simp only [map_add, hx, hy]

theorem eqCast_φEdge'_trans (M : Rep (gelfandOfCardTwo K L h)) (e : (gelfandOfCardTwo K L h).E)
    {a b b' : (gelfandOfCardTwo K L h).V} (ha : (gelfandOfCardTwo K L h).toRQuiver.source e = a)
    (hb : (gelfandOfCardTwo K L h).toRQuiver.target e = b) (hb2 : b = b') (x : M.M a) :
    M.eqCast hb2 (M.φEdge' e ha hb x) = M.φEdge' e ha (hb.trans hb2) x := by
  subst hb2; rfl

/-- The edge equivariance for `φ''`, transported.  The edge maps are written as `φEdge'` with
endpoints named in `Γ_{K''}`, so that every vertex term is one of `Γ_{K''}`.
@census none (helper; WP-15) -/
theorem phiNN_edge (M : Rep (gelfandOfCardTwo K L h)) (σ : Gal(L''/K''))
    (e : (gelfandOfCardTwo K'' L'' h'').E)
    (x : L'' ⊗[L] M.M ((gelfandOfCardTwo K'' L'' h'').toRQuiver.source e)) :
    castNN h'' M ((gelfandOfCardTwo K'' L'' h'').target_smul σ e)
        (LinearMap.baseChange L''
          (M.φEdge' (σ • e) (a := (gelfandOfCardTwo K'' L'' h'').toRQuiver.source (σ • e))
            (b := (gelfandOfCardTwo K'' L'' h'').toRQuiver.target (σ • e)) rfl rfl)
          (castNN h'' M ((gelfandOfCardTwo K'' L'' h'').source_smul σ e).symm
            (phiNNEquiv (h'' := h'') R M σ ((gelfandOfCardTwo K'' L'' h'').toRQuiver.source e) x)))
      = phiNNEquiv (h'' := h'') R M σ ((gelfandOfCardTwo K'' L'' h'').toRQuiver.target e)
          (LinearMap.baseChange L''
            (M.φEdge' e (a := (gelfandOfCardTwo K'' L'' h'').toRQuiver.source e)
              (b := (gelfandOfCardTwo K'' L'' h'').toRQuiver.target e) rfl rfl) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul b m =>
    rw [phiNNEquiv_tmul, castNN_tmul, LinearMap.baseChange_tmul, castNN_tmul,
      LinearMap.baseChange_tmul, phiNNEquiv_tmul]
    congr 1
    rw [eqCast_φEdge'_trans, eqCast_φ'_trans]
    exact M.φEdge'_φ' (R.θ σ) (R.smul_edge σ e) rfl rfl rfl _ _ _ m
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The `nn` base change of a representation of the Gelfand quiver.**
@census none (helper; WP-15; the `nn` shape of `RQ-5.08-C4`, quiver side) -/
noncomputable def Rep.bcNN (M : Rep (gelfandOfCardTwo K L h)) :
    Rep (gelfandOfCardTwo K'' L'' h'') :=
  Rep.ofFiniteDimensional (Γ := gelfandOfCardTwo K'' L'' h'') (fun v => L'' ⊗[L] M.M v)
    (fun σ v => phiNNEquiv (h'' := h'') R M σ v)
    (fun σ v a x => by
      induction x using TensorProduct.induction_on with
      | zero => simp only [smul_zero, map_zero]
      | tmul b m =>
        rw [TensorProduct.smul_tmul', phiNNEquiv_tmul, phiNNEquiv_tmul, smul_eq_mul, map_mul,
          TensorProduct.smul_tmul', smul_eq_mul]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add])
    (fun σ τ v x => sigma_mk_eq_of_famCast (L := L'') (fun u => L'' ⊗[L] M.M u)
        (mul_smul σ τ v).symm _ _ (phiNN_cocycle R M σ τ v x))
    (fun e => LinearMap.baseChange L'' (M.φEdge e))
    (fun σ e x x' hxx' => by
      have hx' : x' = castNN h'' M ((gelfandOfCardTwo K'' L'' h'').source_smul σ e).symm
          (phiNNEquiv (h'' := h'') R M σ _ x) :=
        (famCast_of_sigma_mk_eq (L := L'') (fun u => L'' ⊗[L] M.M u)
          ((gelfandOfCardTwo K'' L'' h'').source_smul σ e).symm _ _ hxx'.symm).symm
      subst hx'
      exact sigma_mk_eq_of_famCast (L := L'') (fun u => L'' ⊗[L] M.M u)
        ((gelfandOfCardTwo K'' L'' h'').target_smul σ e) _ _ (phiNN_edge R M σ e x))

@[simp] theorem Rep.bcNN_M (M : Rep (gelfandOfCardTwo K L h)) (v : (gelfandOfCardTwo K L h).V) :
    (Rep.bcNN (h'' := h'') R M).M v = L'' ⊗[L] M.M v := rfl

theorem Rep.bcNN_φEdge (M : Rep (gelfandOfCardTwo K L h)) (e : (gelfandOfCardTwo K L h).E) :
    (Rep.bcNN (h'' := h'') R M).φEdge e = LinearMap.baseChange L'' (M.φEdge e) := rfl

theorem Rep.bcNN_φ_tmul (M : Rep (gelfandOfCardTwo K L h)) (σ : Gal(L''/K''))
    (v : (gelfandOfCardTwo K L h).V) (b : L'') (m : M.M v) :
    (Rep.bcNN (h'' := h'') R M).φ σ v (b ⊗ₜ[L] m)
      = σ b ⊗ₜ[L] M.φ' (R.θ σ) (R.smul_vertex (h'' := h'') σ v) m := rfl

/-- Path composites of the `nn` base change.  @census none (helper; WP-15) -/
theorem Rep.pathMap_bcNN (M : Rep (gelfandOfCardTwo K L h)) {a b : (gelfandOfCardTwo K L h).V}
    (p : Quiver.Path a b) :
    (Rep.bcNN (h'' := h'') R M).pathMap p = LinearMap.baseChange L'' (M.pathMap p) :=
  pathCompose_baseChange (L'' := L'') M.M M.φEdge p

/-- A morphism commutes with the transported structure maps.  @census none (helper; WP-15) -/
theorem ψ_φ' {M N : Rep (gelfandOfCardTwo K L h)} (f : Rep.Hom M N) (g : Gal(L/K))
    {v w : (gelfandOfCardTwo K L h).V} (hvw : g • v = w) (m : M.M v) :
    f.ψ w (M.φ' g hvw m) = N.φ' g hvw (f.ψ v m) := by
  subst hvw; exact f.rational g v m

/-- The `nn` base change of a morphism.  @census none (helper; WP-15) -/
noncomputable def Rep.Hom.bcNN {M N : Rep (gelfandOfCardTwo K L h)} (f : Rep.Hom M N) :
    Rep.Hom (Rep.bcNN (h'' := h'') R M) (Rep.bcNN (h'' := h'') R N) where
  ψ v := LinearMap.baseChange L'' (f.ψ v)
  edge e m := by
    have h1 : (f.ψ _) ∘ₗ M.φEdge e = N.φEdge e ∘ₗ (f.ψ _) := LinearMap.ext (f.edge e)
    have h2 := congrArg (LinearMap.baseChange L'') h1
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h2
    exact congrArg (fun g : (L'' ⊗[L] M.M _) →ₗ[L''] (L'' ⊗[L] N.M _) => g m) h2
  rational σ v x := by
    show LinearMap.baseChange L'' (f.ψ _) (phiNNEquiv (h'' := h'') R M σ v x)
      = phiNNEquiv (h'' := h'') R N σ v (LinearMap.baseChange L'' (f.ψ v) x)
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b m =>
      rw [phiNNEquiv_tmul, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul, phiNNEquiv_tmul]
      congr 1
      exact ψ_φ' f _ _ m
    | add x y hx hy => simp only [map_add, hx, hy]

/-- **The `nn` quiver-side base-change functor** `Rep^nil_rel(Γ_K) ⥤ Rep^nil_rel(Γ_{K''})`,
constructed.  @census none (helper; WP-15; the `nn` shape of `RQ-5.08-C4`) -/
noncomputable def qBCnnRel :
    (repNilRelGel K L h).FullSubcategory ⥤ (repNilRelGel K'' L'' h'').FullSubcategory where
  obj M :=
    ⟨{ toRep := Rep.bcNN R M.obj.toRep
       finiteDimensional := fun v => by
         haveI := M.obj.finiteDimensional v
         exact Module.Finite.base_change L L'' (M.obj.toRep.M v) },
      ⟨by
        obtain ⟨n, hn⟩ := M.property.1
        refine ⟨n, fun a b p hp => ?_⟩
        show (Rep.bcNN R M.obj.toRep).pathMap p = 0
        rw [Rep.pathMap_bcNN]
        exact (congrArg (LinearMap.baseChange L'') (hn a b p hp)).trans LinearMap.baseChange_zero,
       by
        show (Rep.bcNN R M.obj.toRep).pathMap _ = (Rep.bcNN R M.obj.toRep).pathMap _
        rw [Rep.pathMap_bcNN, Rep.pathMap_bcNN]
        exact congrArg (LinearMap.baseChange L'') M.property.2⟩⟩
  map f := ⟨Rep.Hom.bcNN R f.hom⟩
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

end RepNN

/-! ## The restriction datum of `E(√-1) → E''(√-1)` -/

section Datum

variable {E : Type} [Field E] [CharZero E] (D : SqrtNegOneExt E)
variable {E'' : Type} [Field E''] [CharZero E''] (D'' : SqrtNegOneExt E'')
variable [Algebra D.carrier D''.carrier]

/-- `θ(1) = 1`, `θ(c'') = c`, from `ι ∘ c = c'' ∘ ι`.  @census none (helper; WP-15) -/
noncomputable def restrictionDatum (hι : ConjCompat D D'') :
    RestrictionDatum E D.carrier E'' D''.carrier where
  θ := MonoidHom.ofInvolutionOfCardTwo D''.card_gal D.conj (Gelfand.RationalStructure.galConj_mul_self (D := D))
  θ_eq_one σ hσ := by
    classical
    by_contra hne
    have : (MonoidHom.ofInvolutionOfCardTwo D''.card_gal D.conj (Gelfand.RationalStructure.galConj_mul_self (D := D))) σ
        = D.conj := by
      show (if σ = 1 then 1 else D.conj) = D.conj
      rw [if_neg hne]
    exact D.conj_ne_one (this.symm.trans hσ)
  θ_ι σ a := by
    classical
    by_cases hσ : σ = 1
    · subst hσ; simp
    · have h1 : (MonoidHom.ofInvolutionOfCardTwo D''.card_gal D.conj (Gelfand.RationalStructure.galConj_mul_self (D := D)))
          σ = D.conj := by
        show (if σ = 1 then 1 else D.conj) = D.conj
        rw [if_neg hσ]
      rw [h1, hι, D''.eq_conj_of_ne_one hσ]

end Datum

end RationalQuivers.Gelfand.BaseChange
