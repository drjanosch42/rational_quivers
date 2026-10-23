import RationalQuivers.Quiver.Rep.HomDescent
import RationalQuivers.Quiver.Rep.GeneralBaseChange
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# `Hom` commutes with base change (WP-15, T2)

*Provenance.*  Relocated in stage T4 (WP-11) from `GF/BaseChangeHom.lean` (v1 `RationalQuivers.Gelfand.GF`) by `workflow/v2/stages/T4/VALIDATION/scripts/relocate_bc.py`: whole file, declarations moved from `GF.x` to `Gelfand.BaseChange.x` (renames in the T4 `DECL-ALLOWLIST.tsv`), references qualified, the imports of v1's `GF/Main`/`GF/Species` cut; statements and proofs otherwise unchanged.  The native statement on `HC ℓ E D`/`𝔼_E` (`prop:basechange`, `RQ2-5.14`) is in `Gelfand/BaseChange/Native.lean`.

*(2026-10-21, O-V2-6 round 2.)*  The phrase "the row's claimant `GF.E_E_equivalence_general`" in
the census paragraphs below is v1's.  That declaration was deleted at WP-13 (`44df340`), and the v2
census retired `RQ-5.08` as a row (`CROSSWALK-v1-v2.tsv`).  S10's `qBCss`/`qBCns` were deleted at
the same commit.

`BASECHANGE-ANALYSIS.md` (T2): for an **arbitrary** field extension `L → L''` and representations
`M`, `N` of a quiver with finite-dimensional vertex spaces, the canonical `L''`-linear map

  `L'' ⊗_L Hom(M, N) → Hom(L'' ⊗_L M, L'' ⊗_L N)`,   `a ⊗ ψ ↦ a · (L'' ⊗ ψ_v)_v`

is an isomorphism (`classicalHom_baseChange`).  Here `Hom` is the space of homomorphisms of the
underlying classical quiver representations (`Rep.classicalHom`, the space `W` of
`prop:homdescent`), and `L'' ⊗_L −` is `Rep.toSplit L''`, the quiver-side base change of S10's
`qBCss` (`L = E`) and `qBCns` (`L = E(√-1)`).  For a split rational quiver `classicalHom` *is*
`Hom` (`splitHomEquiv`), so this is T2 for case (1) as stated; for the non-split source of case
(3) the `E`-rational `Hom` is a `E`-form of `classicalHom` over `E(√-1)` by `prop:homdescent`, and
the composite `E'' ⊗_E Hom_{Γ_E} ≅ E'' ⊗_{E(√-1)} classicalHom ≅ classicalHom''` is
`classicalHom_baseChange_ns`.

*Proof.*  `Hom(M,N)` is the kernel of the `L`-linear map
`Φ : ∏_v Hom(M_v, N_v) → ∏_e Hom(M_{s e}, N_{t e})`, `ψ ↦ (ψ_{t e} φ_e − φ_e ψ_{s e})_e`.  For
finite-dimensional vertex spaces `L'' ⊗ ∏_v Hom(M_v,N_v) ≅ ∏_v Hom(L'' ⊗ M_v, L'' ⊗ N_v)`
(mathlib's `IsBaseChange.linearMapLeftRight` and `TensorProduct.piRight`), compatibly with `Φ`;
`L''` is flat over `L`, so `L'' ⊗ ker Φ = ker (L'' ⊗ Φ)` (`Module.Flat.ker_lTensor_eq`).

**"Fully faithful" in the literal sense is false for `L'' ≠ L`**: a morphism
`L'' ⊗ M → L'' ⊗ N` is an `L''`-linear combination of base-changed morphisms, not one of them.  The
bijectivity of the canonical map is the correct form of T2, and it is what is proved.
-/

namespace RationalQuivers.Gelfand.BaseChange

open RationalQuivers.RationalQuiver CategoryTheory
open scoped TensorProduct

section HomBC

variable {L L'' : Type} [Field L] [Field L''] [Algebra L L'']

/-- The canonical map `L'' ⊗_L Hom_L(X, Y) → Hom_{L''}(L'' ⊗ X, L'' ⊗ Y)` is an isomorphism for
finite-dimensional `X`.  @census none (helper; WP-15) -/
noncomputable def homBCEquiv (X Y : Type) [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    [AddCommGroup Y] [Module L Y] :
    L'' ⊗[L] (X →ₗ[L] Y) ≃ₗ[L''] ((L'' ⊗[L] X) →ₗ[L''] (L'' ⊗[L] Y)) :=
  (IsBaseChange.linearMapLeftRight (TensorProduct.isBaseChange L X L'')
    (TensorProduct.isBaseChange L Y L'')).equiv

theorem homBCEquiv_tmul (X Y : Type) [AddCommGroup X] [Module L X] [FiniteDimensional L X]
    [AddCommGroup Y] [Module L Y] (a : L'') (f : X →ₗ[L] Y) :
    homBCEquiv X Y (a ⊗ₜ[L] f) = a • LinearMap.baseChange L'' f := by
  rw [homBCEquiv, IsBaseChange.equiv_tmul]
  congr 1
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  have h1 : b ⊗ₜ[L] x = b • ((TensorProduct.mk L L'' X) 1 x) := by
    rw [TensorProduct.mk_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, map_smul, IsBaseChange.linearMapLeftRightHom_comp_apply]
  simp only [TensorProduct.mk_apply, LinearMap.baseChange_tmul]

end HomBC

section ClassicalHom

variable {K L : Type} [Field K] [Field L] [Algebra K L] {Γ : RationalQuiver.{0} K L}
variable (L'' : Type) [Field L''] [Algebra L L'']

/-- The defect map `Φ`, whose kernel is `Hom(M,N)`.  @census none (helper; WP-15) -/
noncomputable def homDefect (M N : Rep Γ) :
    (∀ v : Γ.V, M.M v →ₗ[L] N.M v) →ₗ[L]
      (∀ e : Γ.E, M.M (Γ.toRQuiver.source e) →ₗ[L] N.M (Γ.toRQuiver.target e)) where
  toFun ψ e := ψ (Γ.toRQuiver.target e) ∘ₗ M.φEdge e - N.φEdge e ∘ₗ ψ (Γ.toRQuiver.source e)
  map_add' ψ χ := by
    funext e
    simp only [Pi.add_apply, LinearMap.add_comp, LinearMap.comp_add]
    abel
  map_smul' a ψ := by
    funext e
    simp only [Pi.smul_apply, LinearMap.smul_comp, LinearMap.comp_smul, smul_sub, RingHom.id_apply]

theorem classicalHom_eq_ker (M N : Rep Γ) :
    Rep.classicalHom M N = LinearMap.ker (homDefect M N) := by
  ext ψ
  rw [Rep.mem_classicalHom, LinearMap.mem_ker]
  constructor
  · intro h
    funext e
    refine LinearMap.ext fun m => ?_
    simp [homDefect, h e m]
  · intro h e m
    have := congrArg (fun F => F e m) h
    simpa [homDefect, sub_eq_zero] using this

variable (M N : FDRep Γ)

/-- The defect map of the base change, on the explicit tensor products.
@census none (helper; WP-15) -/
noncomputable def homDefectBC :
    (∀ v : Γ.V, (L'' ⊗[L] M.toRep.M v) →ₗ[L''] (L'' ⊗[L] N.toRep.M v)) →ₗ[L'']
      (∀ e : Γ.E, (L'' ⊗[L] M.toRep.M (Γ.toRQuiver.source e)) →ₗ[L'']
        (L'' ⊗[L] N.toRep.M (Γ.toRQuiver.target e))) where
  toFun ψ e := ψ (Γ.toRQuiver.target e) ∘ₗ LinearMap.baseChange L'' (M.toRep.φEdge e)
    - LinearMap.baseChange L'' (N.toRep.φEdge e) ∘ₗ ψ (Γ.toRQuiver.source e)
  map_add' ψ χ := by
    funext e
    simp only [Pi.add_apply, LinearMap.add_comp, LinearMap.comp_add]
    abel
  map_smul' a ψ := by
    funext e
    refine LinearMap.ext fun m => ?_
    simp only [Pi.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      RingHom.id_apply, map_smul, smul_sub]

theorem classicalHom_toSplit_eq_ker :
    (Rep.classicalHom (M.toRep.toSplit L'') (N.toRep.toSplit L'') :
        Submodule L'' (∀ v : Γ.V, (L'' ⊗[L] M.toRep.M v) →ₗ[L''] (L'' ⊗[L] N.toRep.M v)))
      = LinearMap.ker (homDefectBC L'' M N) := by
  refine Submodule.ext fun ψ => ?_
  show (∀ (e : Γ.E) (m : L'' ⊗[L] M.toRep.M (Γ.toRQuiver.source e)),
      ψ (Γ.toRQuiver.target e) (LinearMap.baseChange L'' (M.toRep.φEdge e) m)
        = LinearMap.baseChange L'' (N.toRep.φEdge e) (ψ (Γ.toRQuiver.source e) m))
    ↔ homDefectBC L'' M N ψ = 0
  constructor
  · intro h
    funext e
    refine LinearMap.ext fun m => ?_
    simp only [homDefectBC, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
      LinearMap.comp_apply, Pi.zero_apply, LinearMap.zero_apply]
    exact sub_eq_zero.mpr (h e m)
  · intro h e m
    have := congrArg (fun F => F e m) h
    simp only [homDefectBC, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sub_apply,
      LinearMap.comp_apply, Pi.zero_apply, LinearMap.zero_apply] at this
    exact sub_eq_zero.mp this

/-- `L'' ⊗ ∏_v Hom(M_v, N_v) ≅ ∏_v Hom(L'' ⊗ M_v, L'' ⊗ N_v)`.  @census none (helper; WP-15) -/
noncomputable def piHomBCEquiv :
    L'' ⊗[L] (∀ v : Γ.V, M.toRep.M v →ₗ[L] N.toRep.M v) ≃ₗ[L'']
      (∀ v : Γ.V, (L'' ⊗[L] M.toRep.M v) →ₗ[L''] (L'' ⊗[L] N.toRep.M v)) := by
  classical
  haveI : Fintype Γ.V := Fintype.ofFinite _
  exact (TensorProduct.piRight L L'' L'' (fun v => M.toRep.M v →ₗ[L] N.toRep.M v)).trans
    (LinearEquiv.piCongrRight fun v => homBCEquiv (M.toRep.M v) (N.toRep.M v))

theorem piHomBCEquiv_tmul (a : L'') (ψ : ∀ v : Γ.V, M.toRep.M v →ₗ[L] N.toRep.M v) (v : Γ.V) :
    piHomBCEquiv L'' M N (a ⊗ₜ[L] ψ) v = a • LinearMap.baseChange L'' (ψ v) := by
  classical
  simp only [piHomBCEquiv, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  exact homBCEquiv_tmul _ _ a (ψ v)

/-- `L'' ⊗ ∏_e Hom(M_{s e}, N_{t e}) ≅ ∏_e Hom(L'' ⊗ M_{s e}, L'' ⊗ N_{t e})`.
@census none (helper; WP-15) -/
noncomputable def piEdgeBCEquiv :
    L'' ⊗[L] (∀ e : Γ.E, M.toRep.M (Γ.toRQuiver.source e) →ₗ[L] N.toRep.M (Γ.toRQuiver.target e))
      ≃ₗ[L''] (∀ e : Γ.E, (L'' ⊗[L] M.toRep.M (Γ.toRQuiver.source e)) →ₗ[L'']
        (L'' ⊗[L] N.toRep.M (Γ.toRQuiver.target e))) := by
  classical
  haveI : Fintype Γ.E := Fintype.ofFinite _
  exact (TensorProduct.piRight L L'' L''
      (fun e => M.toRep.M (Γ.toRQuiver.source e) →ₗ[L] N.toRep.M (Γ.toRQuiver.target e))).trans
    (LinearEquiv.piCongrRight fun e => homBCEquiv _ _)

theorem piEdgeBCEquiv_tmul (a : L'')
    (χ : ∀ e : Γ.E, M.toRep.M (Γ.toRQuiver.source e) →ₗ[L] N.toRep.M (Γ.toRQuiver.target e))
    (e : Γ.E) :
    piEdgeBCEquiv L'' M N (a ⊗ₜ[L] χ) e = a • LinearMap.baseChange L'' (χ e) := by
  classical
  simp only [piEdgeBCEquiv, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  exact homBCEquiv_tmul _ _ a (χ e)

/-- The base-changed defect map is the defect map of the base change.
@census none (helper; WP-15) -/
theorem homDefect_bc :
    (piEdgeBCEquiv L'' M N).toLinearMap ∘ₗ
        TensorProduct.AlgebraTensorModule.lTensor L'' L'' (homDefect M.toRep N.toRep)
      = homDefectBC L'' M N ∘ₗ (piHomBCEquiv L'' M N).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a ψ
  funext e
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.lTensor_tmul]
  rw [piEdgeBCEquiv_tmul]
  show a • LinearMap.baseChange L'' (homDefect M.toRep N.toRep ψ e)
    = piHomBCEquiv L'' M N (a ⊗ₜ[L] ψ) _ ∘ₗ LinearMap.baseChange L'' (M.toRep.φEdge e)
      - LinearMap.baseChange L'' (N.toRep.φEdge e) ∘ₗ piHomBCEquiv L'' M N (a ⊗ₜ[L] ψ) _
  rw [piHomBCEquiv_tmul, piHomBCEquiv_tmul]
  simp only [homDefect, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.baseChange_sub,
    LinearMap.baseChange_comp]
  refine LinearMap.ext fun m => ?_
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_sub]

/-- **T2 — `Hom` commutes with base change**, along an **arbitrary** field extension `L → L''`:
the canonical map `L'' ⊗_L Hom(M,N) → Hom(L'' ⊗ M, L'' ⊗ N)`, `a ⊗ ψ ↦ a · (L'' ⊗ ψ_v)_v`, is an
isomorphism of `L''`-vector spaces.

*(Census role, 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S10, coordinator ruling
`R-FR-9`, final-release WP-16b.)* A witness of statement (T2), quiver side, of `rmk:generalbases`
as rewritten by WP-17 (`330d50f`). Census r20 (2026-10-03) books (T2), quiver side, as `RQ-5.08-C8`
(WP-16c, same-day `R-FR-9` follow-up). The citation below is a witness citation: this module is not
the claimant's, so `rqaudit clauses` does not count it. The row's claimant
`GF.E_E_equivalence_general` cites `C8` and points here.

@census none (WP-15; T2 of `BASECHANGE-ANALYSIS.md`)
@source    rmk:generalbases
@clauses   RQ-5.08-C8
@imports   none
@divergence WEAKENED_OR_PARTIAL as a witness of `C8`: split → split only (with
`splitHomEquiv`); non-split → split is `homModule_baseChange_ns`, non-split → non-split is
`homModule_baseChange_nn`. -/
theorem classicalHom_baseChange :
    ∃ f : L'' ⊗[L] Rep.classicalHom M.toRep N.toRep ≃ₗ[L'']
        Rep.classicalHom (M.toRep.toSplit L'') (N.toRep.toSplit L''),
      ∀ (a : L'') (ψ : Rep.classicalHom M.toRep N.toRep) (v : Γ.V),
        (f (a ⊗ₜ[L] ψ)).1 v = a • LinearMap.baseChange L'' (ψ.1 v) := by
  set p := Rep.classicalHom M.toRep N.toRep
  -- `L'' ⊗ p ≅ p.baseChange L''`, by flatness
  let e₁ : L'' ⊗[L] p ≃ₗ[L''] p.baseChange L'' := Submodule.toBaseChange.toLinearEquiv L'' p
  -- `Θ` carries `p.baseChange L''` onto `Hom''`
  have hmap : (p.baseChange L'').map (piHomBCEquiv L'' M N).toLinearMap
      = (Rep.classicalHom (M.toRep.toSplit L'') (N.toRep.toSplit L'') :
          Submodule L'' (∀ v : Γ.V, (L'' ⊗[L] M.toRep.M v) →ₗ[L''] (L'' ⊗[L] N.toRep.M v))) := by
    rw [classicalHom_toSplit_eq_ker]
    have hker : p.baseChange L''
        = LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor L'' L''
            (homDefect M.toRep N.toRep)) := by
      rw [show p = LinearMap.ker (homDefect M.toRep N.toRep) from classicalHom_eq_ker _ _,
        Module.Flat.ker_lTensor_eq]
      rfl
    rw [hker]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker] at hx ⊢
      have h := congrArg (fun F => F x) (homDefect_bc L'' M N)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hx, map_zero] at h
      exact h.symm
    · intro hy
      refine ⟨(piHomBCEquiv L'' M N).symm y, ?_, by simp⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker] at hy ⊢
      apply (piEdgeBCEquiv L'' M N).injective
      have h := congrArg (fun F => F ((piHomBCEquiv L'' M N).symm y)) (homDefect_bc L'' M N)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h
      rw [h, map_zero, LinearEquiv.apply_symm_apply]
      exact hy
  let e₂ := ((piHomBCEquiv L'' M N).submoduleMap (p.baseChange L'')).trans (LinearEquiv.ofEq _ _ hmap)
  refine ⟨e₁.trans e₂, fun a ψ v => ?_⟩
  show piHomBCEquiv L'' M N (a ⊗ₜ[L] ψ.1) v = _
  exact piHomBCEquiv_tmul L'' M N a ψ.1 v

end ClassicalHom

/-! ## For a split rational quiver, `classicalHom` is `Hom` -/

section Split

variable {F : Type} [Field F] {Q : RQuiver.{0}}

/-- On a split rational quiver the Galois action on a representation is trivial.
@census none (helper; WP-15) -/
theorem splitOf_φ_eq (M : Rep (splitOf F Q)) (σ : Gal(F/F)) (v : (splitOf F Q).V) (m : M.M v) :
    M.φ σ v m = m := by
  have hσ : σ = 1 := AlgEquiv.ext (fun a => galSelf_apply' σ a)
  have h : σ • v = v := rfl
  have h1 : (1 : Gal(F/F)) • v = v := rfl
  calc M.φ σ v m = M.φ' σ h m := rfl
    _ = M.φ' 1 h1 m := M.φ'_congr hσ h h1 m
    _ = m := by rw [M.φ'_one h1 m]; rfl

/-- **For a split rational quiver, `Hom = classicalHom`**: every homomorphism of the underlying
classical representations is a homomorphism of rational representations.  So `classicalHom_baseChange`
is T2 for the split case (1) as stated.  @census none (helper; WP-15) -/
noncomputable def splitHomEquiv (M N : Rep (splitOf F Q)) :
    Rep.Hom M N ≃ Rep.classicalHom M N where
  toFun f := ⟨f.ψ, f.edge⟩
  invFun ψ :=
    { ψ := ψ.1
      edge := ψ.2
      rational := fun σ v m => by
        rw [splitOf_φ_eq M σ v m, splitOf_φ_eq N σ v]
        rfl }
  left_inv _ := rfl
  right_inv _ := rfl

end Split

/-! ## T2 for the non-split source of case (3) -/

section NS

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] {Γ : RationalQuiver.{0} K L}
variable (K'' : Type) [Field K''] [Algebra K K''] [Algebra L K''] [IsScalarTower K L K'']

/-- **T2, non-split source** (case (3), `√-1 ∉ E`, `E(√-1) → E''`): the canonical map
`E'' ⊗_E Hom_{Γ_E}(M,N) → Hom(E'' ⊗_{E(√-1)} M, E'' ⊗_{E(√-1)} N)`, `a ⊗ ψ ↦ a · (E'' ⊗ ψ_v)_v`,
is an isomorphism.  `Hom_{Γ_E}(M,N)` is `homModule` (= `Rep.Hom`, `Rep.homEquiv`); the proof is
Galois descent `E(√-1) ⊗_E Hom_{Γ_E} ≅ classicalHom` (`Descent.descentCounit_bijective`) followed by
`classicalHom_baseChange` along `E(√-1) → E''`.

*(Census role, 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S10, coordinator ruling
`R-FR-9`, final-release WP-16b.)* A witness of statement (T2), quiver side, of `rmk:generalbases`
as rewritten by WP-17 (`330d50f`). Census r20 (2026-10-03) books (T2), quiver side, as `RQ-5.08-C8`
(WP-16c, same-day `R-FR-9` follow-up). The citation below is a witness citation: this module is not
the claimant's, so `rqaudit clauses` does not count it. The row's claimant
`GF.E_E_equivalence_general` cites `C8` and points here.

@census none (WP-15; T2, case (3))
@source    rmk:generalbases
@clauses   RQ-5.08-C8
@imports   none
@divergence WEAKENED_OR_PARTIAL as a witness of `C8`: non-split → split only; the other shapes
are `classicalHom_baseChange` with `splitHomEquiv` and `homModule_baseChange_nn`. -/
theorem homModule_baseChange_ns (M N : FDRep Γ) :
    ∃ f : K'' ⊗[K] Rep.homModule M N ≃ₗ[K'']
        Rep.classicalHom (M.toRep.toSplit K'') (N.toRep.toSplit K''),
      ∀ (a : K'') (ψ : Rep.homModule M N) (v : Γ.V),
        (f (a ⊗ₜ[K] ψ)).1 v = a • LinearMap.baseChange K'' (Rep.homFam M N ψ.1 v) := by
  obtain ⟨g, hg⟩ := classicalHom_baseChange K'' M N
  let d : L ⊗[K] Rep.homModule M N ≃ₗ[L] Rep.classicalHom M.toRep N.toRep :=
    LinearEquiv.ofBijective (Descent.descentCounit K L (Rep.homVecK M N))
      (Descent.descentCounit_bijective K L (Rep.homVecK M N))
  let e₁ : K'' ⊗[K] Rep.homModule M N ≃ₗ[K''] K'' ⊗[L] (L ⊗[K] Rep.homModule M N) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange K L K'' K'' (Rep.homModule M N)).symm
  let e₂ : K'' ⊗[L] (L ⊗[K] Rep.homModule M N) ≃ₗ[K''] K'' ⊗[L] Rep.classicalHom M.toRep N.toRep :=
    LinearEquiv.baseChange L K'' _ _ d
  refine ⟨e₁.trans (e₂.trans g), fun a ψ v => ?_⟩
  show (g (e₂ (e₁ (a ⊗ₜ[K] ψ)))).1 v = _
  have h1 : e₁ (a ⊗ₜ[K] ψ) = a ⊗ₜ[L] ((1 : L) ⊗ₜ[K] ψ) := rfl
  have h2 : e₂ (a ⊗ₜ[L] ((1 : L) ⊗ₜ[K] ψ)) = a ⊗ₜ[L] d ((1 : L) ⊗ₜ[K] ψ) := rfl
  have h3 : d ((1 : L) ⊗ₜ[K] ψ) = ψ.1 := by
    show Descent.descentCounit K L (Rep.homVecK M N) ((1 : L) ⊗ₜ[K] ψ) = ψ.1
    rw [Descent.descentCounit_tmul, one_smul]
  rw [h1, h2, h3, hg]

end NS

end RationalQuivers.Gelfand.BaseChange
