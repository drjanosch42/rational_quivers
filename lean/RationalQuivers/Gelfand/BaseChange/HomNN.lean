import RationalQuivers.Gelfand.BaseChange.NNRep
import RationalQuivers.Gelfand.BaseChange.Hom

/-!
# `Hom` commutes with base change, non-split → non-split (WP-15, T2 case (2))

*Provenance.*  Relocated in stage T4 (WP-11) from `GF/BaseChangeHomNN.lean` (v1 `RationalQuivers.Gelfand.GF`) by `workflow/v2/stages/T4/VALIDATION/scripts/relocate_bc.py`: whole file, declarations moved from `GF.x` to `Gelfand.BaseChange.x` (renames in the T4 `DECL-ALLOWLIST.tsv`), references qualified, the imports of v1's `GF/Main`/`GF/Species` cut; statements and proofs otherwise unchanged.  The native statement on `HC ℓ E D`/`𝔼_E` (`prop:basechange`, `RQ2-5.14`) is in `Gelfand/BaseChange/Native.lean`.

*(2026-10-21, O-V2-6 round 2.)*  The phrase "the row's claimant `GF.E_E_equivalence_general`" in
the census paragraph below is v1's.  That declaration was deleted at WP-13 (`44df340`), and the v2
census retired `RQ-5.08` as a row (`CROSSWALK-v1-v2.tsv`).

For the `nn` base change `M ↦ L'' ⊗_L M` of representations of the `K`-rational Gelfand quiver
(`Rep.bcNN`), the canonical map

  `K'' ⊗_K Hom_{Γ_K}(M, N) → Hom_{Γ_{K''}}(L'' ⊗_L M, L'' ⊗_L N)`,  `a ⊗ ψ ↦ a · (L'' ⊗ ψ_v)_v`

is an isomorphism of `K''`-vector spaces (`homModule_baseChange_nn`).

*Proof.*  It is injective: composed with `Hom_{Γ_{K''}} ⊆ classicalHom''` it is
`K'' ⊗_K Hom → L'' ⊗_K Hom ≅ classicalHom''` (flatness of `Hom` over `K`, then
`homModule_baseChange_ns` along `L → L''`).  Its image lies in `Hom_{Γ_{K''}}`, since the base
change of a rational morphism is rational (`Rep.Hom.bcNN`).  Dimensions agree:
`dim_{K''} Hom_{Γ_{K''}} = dim_{L''} classicalHom'' = dim_K Hom_{Γ_K}` (Galois descent over `K''`,
then `homModule_baseChange_ns`).
-/

namespace RationalQuivers.Gelfand.BaseChange

open RationalQuivers.RationalQuiver CategoryTheory
open scoped TensorProduct

section HomNN

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
variable {h : Nat.card Gal(L/K) = 2}
variable {K'' L'' : Type} [Field K''] [Field L''] [Algebra K'' L''] [IsGalois K'' L'']
  [FiniteDimensional K'' L''] {h'' : Nat.card Gal(L''/K'') = 2}
variable [Algebra L L''] [Algebra K K''] [Algebra K L''] [IsScalarTower K L L'']
  [IsScalarTower K K'' L'']
variable (R : RestrictionDatum K L K'' L'')

/-- The `nn` base change of a finite-dimensional representation.  @census none (helper; WP-15) -/
noncomputable def fdBcNN (M : FDRep (gelfandOfCardTwo K L h)) :
    FDRep (gelfandOfCardTwo K'' L'' h'') where
  toRep := Rep.bcNN R M.toRep
  finiteDimensional v := by
    haveI := M.finiteDimensional v
    exact Module.Finite.base_change L L'' (M.toRep.M v)

omit [IsGalois K L] [FiniteDimensional K L] [IsGalois K'' L''] [FiniteDimensional K'' L'']
  [Algebra L L''] [IsScalarTower K L L''] in
/-- `K'' ⊗_K H → L'' ⊗_K H` is injective.  @census none (helper; WP-15) -/
theorem tensor_algebraMap_injective (H : Type) [AddCommGroup H] [Module K H] :
    Function.Injective (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K'' L'')
      (LinearMap.id : H →ₗ[K] H)) := by
  have h1 : (TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K'' L'')
      (LinearMap.id : H →ₗ[K] H) : K'' ⊗[K] H → L'' ⊗[K] H)
      = LinearMap.rTensor H ((Algebra.linearMap K'' L'').restrictScalars K) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [h1]
  exact Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap K'' L'').injective

/-- **T2, non-split → non-split.**  The canonical map
`K'' ⊗_K Hom_{Γ_K}(M,N) → Hom_{Γ_{K''}}(L'' ⊗_L M, L'' ⊗_L N)`, `a ⊗ ψ ↦ a · (L'' ⊗ ψ_v)_v`, is an
isomorphism of `K''`-vector spaces.

*(Census role, 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S10, coordinator ruling
`R-FR-9`, final-release WP-16b.)* A witness of statement (T2), quiver side, of `rmk:generalbases`
as rewritten by WP-17 (`330d50f`). Census r20 (2026-10-03) books (T2), quiver side, as `RQ-5.08-C8`
(WP-16c, same-day `R-FR-9` follow-up). The citation below is a witness citation: this module is not
the claimant's, so `rqaudit clauses` does not count it. The row's claimant
`GF.E_E_equivalence_general` cites `C8` and points here.

@census none (WP-15; T2, case (2))
@source    rmk:generalbases
@clauses   RQ-5.08-C8
@imports   none
@divergence WEAKENED_OR_PARTIAL as a witness of `C8`: non-split → non-split only; the other
shapes are `classicalHom_baseChange` with `splitHomEquiv` and `homModule_baseChange_ns`. -/
theorem homModule_baseChange_nn (M N : FDRep (gelfandOfCardTwo K L h)) :
    ∃ f : K'' ⊗[K] Rep.homModule M N ≃ₗ[K'']
        Rep.homModule (fdBcNN (h'' := h'') R M) (fdBcNN (h'' := h'') R N),
      ∀ (a : K'') (ψ : Rep.homModule M N) (v : (gelfandOfCardTwo K L h).V),
        Rep.homFam _ _ (f (a ⊗ₜ[K] ψ)).1 v
          = algebraMap K'' L'' a • LinearMap.baseChange L'' (Rep.homFam M N ψ.1 v) := by
  obtain ⟨g, hg⟩ := homModule_baseChange_ns L'' M N
  let ιK : K'' ⊗[K] Rep.homModule M N →ₗ[K''] L'' ⊗[K] Rep.homModule M N :=
    TensorProduct.AlgebraTensorModule.map (Algebra.linearMap K'' L'') LinearMap.id
  have hιK : Function.Injective ιK := tensor_algebraMap_injective _
  let j : K'' ⊗[K] Rep.homModule M N →ₗ[K'']
      (Rep.homVecK (fdBcNN (h'' := h'') R M) (fdBcNN (h'' := h'') R N)).carrier :=
    { toFun := fun x => g (ιK x)
      map_add' := fun x y => (congrArg g (map_add ιK x y)).trans (map_add g _ _)
      map_smul' := fun c x => by
        have h1 : ιK (c • x) = algebraMap K'' L'' c • ιK x := by rw [map_smul, algebraMap_smul]
        exact (congrArg g h1).trans (map_smul g _ _) }
  have hj : Function.Injective j := fun x y hxy => hιK (g.injective hxy)
  have hjtmul : ∀ (a : K'') (ψ : Rep.homModule M N) (v : (gelfandOfCardTwo K L h).V),
      Rep.homFam _ _ (j (a ⊗ₜ[K] ψ)) v
        = algebraMap K'' L'' a • LinearMap.baseChange L'' (Rep.homFam M N ψ.1 v) :=
    fun a ψ v => hg (algebraMap K'' L'' a) ψ v
  -- the image lies in `Hom_{Γ_{K''}}`
  have hle : LinearMap.range j ≤ Rep.homModule (fdBcNN (h'' := h'') R M) (fdBcNN (h'' := h'') R N) := by
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | tmul a ψ =>
      let ψ'' := Rep.homEquiv (fdBcNN (h'' := h'') R M) (fdBcNN (h'' := h'') R N)
        (Rep.Hom.bcNN R ((Rep.homEquiv M N).symm ψ))
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
      (Rep.homModule (fdBcNN (h'' := h'') R M) (fdBcNN (h'' := h'') R N))
      = Module.finrank K (Rep.homModule M N) := by
    rw [Rep.homModule, Descent.finrank_fixedPoints K'']
    rw [show Module.finrank L'' (Rep.homVecK (fdBcNN (h'' := h'') R M)
        (fdBcNN (h'' := h'') R N)).carrier
        = Module.finrank L'' (L'' ⊗[K] Rep.homModule M N) from g.finrank_eq.symm,
      Module.finrank_baseChange]
  haveI : FiniteDimensional K'' (Rep.homModule (fdBcNN (h'' := h'') R M) (fdBcNN (h'' := h'') R N)) :=
    Rep.finiteDimensional_homModule _ _
  have hrange : LinearMap.range j
      = Rep.homModule (fdBcNN (h'' := h'') R M) (fdBcNN (h'' := h'') R N) := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [LinearMap.finrank_range_of_inj hj, Module.finrank_baseChange, hdimH'']
  refine ⟨(LinearEquiv.ofInjective j hj).trans (LinearEquiv.ofEq _ _ hrange), fun a ψ v => ?_⟩
  exact hjtmul a ψ v

end HomNN

end RationalQuivers.Gelfand.BaseChange
