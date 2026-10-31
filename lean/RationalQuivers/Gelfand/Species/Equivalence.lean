module

public import RationalQuivers.Gelfand.Compat
public import RationalQuivers.Gelfand.TargetBaseChange
public import RationalQuivers.Species.Rep.SpeciesBridge
public import RationalQuivers.Species.Rep.GelfandRelation

@[expose] public section

/-!
# The species form of `𝔼_E` over every `E` (tex §5.3, `thm:speciesE`, stage T4)

`thm:speciesE` (census `RQ2-5.16`, OQ-2 revised by the author 2026-10-16): for every field `E` of
characteristic `0`, with `S(Γ_E)` the étale `E`-species of `Γ_E` (`def:speciesofquiver`):

* (a) `ℓ = 0`, **every** `E`: `HC_0(𝔤,K)_E ≃ Rep^nil(S(Γ_E))` (`speciesE_zero`);
* (b) `ℓ ≥ 1`, `√-1 ∉ E`: `HC_λ(𝔤,K)_E ≃ Rep^nil(S(Γ_E), R_E)` with `R_E := E·√-1` (`speciesE_pos`);
* in both cases `S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E` (`speciesBaseChangeIso`), and in case (b)
  `R_E = R_Gelfand ⊗_ℚ E` (`relation_baseChange`); the relation may not be omitted in (b)
  (`relation_not_omittable`).

The proofs compose stage T3's `thm:EEequivalence`/`thm:cyclicEEequivalence` with T0's
`Rep(Γ) ≃ Rep(S(Γ))` (`RQ2-2.29`, `FFunctor`) and S5's coincidence of `a₋b₋ = a₊b₊` with `R_E`
(`repNilRel_RGelfand_iff`, `RQ2-2.37`), as v1's `cor:gelfandspecies`/`cor:cyclicspecies` do over
`ℚ`.  `S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E` is `lem:GammaEbasechange` (`Gelfand/TargetBaseChange.lean`) carried
through `S(−)` and the counit of the anti-equivalence (`thm:KrationalquiveretaleKspeciesantiequivalence`).

*Provenance.* The `√-1 ∉ E` parts (`R_E`, the coincidence, `κ`, `Φ`, `relation_baseChange`, the
species shape) re-base v1's `GF/Species`, `GF/IdentificationRing`, `GF/IdentificationSpecies` (part B)
and `GF/IdentificationRelation` on `ImagUnit`/`GammaE`; the `C7` witness generalizes v1's
`Species.relation_not_omittable_descent` (`Gelfand/ReleaseAddenda.lean`) from `ℚ` to every `E ∌ √-1`;
the generic path-map helpers are copied from v1's `Gelfand/Corollaries.lean` (to `Quiver/Rep/` at WP-13).

@census none (module; claimant of `RQ2-5.16` below)
-/

namespace RationalQuivers.Gelfand.Species

open RationalQuivers.HC CategoryTheory

section Generic

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
  (Γ : RationalQuiver K L)

/-- Every nilpotent representation of `S(Γ)` is `F` of a nilpotent representation of `Γ`
(`F` essentially surjective, nilpotency reflected).  @census none (helper) -/
theorem exists_nil_preimage (Y : (RationalQuivers.Species.RepNil Γ.toSpecies.toSpecies).FullSubcategory) :
    ∃ X : RationalQuiver.FDRep Γ, RationalQuiver.RepNil Γ X ∧
      Nonempty ((RationalQuiver.FFunctor Γ).obj X ≅ Y.obj) := by
  haveI := RationalQuiver.FFunctor_isEquivalence Γ
  obtain ⟨X, ⟨iso⟩⟩ := Functor.EssSurj.mem_essImage (F := RationalQuiver.FFunctor Γ) Y.obj
  exact ⟨X, RationalQuiver.FObj_isNilpotent_converse X
    (RationalQuiver.Species.isNilpotent_of_iso iso.symm Y.property), ⟨iso⟩⟩

end Generic

variable {E : Type} [Field E] [CharZero E] (D : ImagUnit E)

/-- `F` restricted to `Rep^nil(Γ_E)`, `ℓ = 0`.  @census none (helper) -/
noncomputable def FRestrictZero :
    (RepNilTarget D 0).FullSubcategory ⥤
      (RationalQuivers.Species.RepNil (GammaE D 0).toSpecies.toSpecies).FullSubcategory :=
  ObjectProperty.lift _ ((RepNilTarget D 0).ι ⋙ RationalQuiver.FFunctor (GammaE D 0))
    (fun M => (RationalQuiver.FObj_isNilpotent_iff M.obj).mp M.property)

/-- **`thm:speciesE` (a)**, `ℓ = 0`, every `E`: `HC_0(𝔤,K)_E ≃ Rep^nil(S(Γ_E))`, the functor `𝔼_E`
followed by `F`.  @census none (helper; clauses `RQ2-5.16-H2`, `C1`) -/
theorem speciesE_zero :
    ∃ e : HC 0 E D ≌ (RationalQuivers.Species.RepNil (GammaE D 0).toSpecies.toSpecies).FullSubcategory,
      e.functor = E_E E D 0 ⋙ FRestrictZero D := by
  haveI := RationalQuiver.FFunctor_isEquivalence (GammaE D 0)
  obtain ⟨e₀, he₀⟩ := gelfand_equivalence_zero (D := D)
  refine ⟨e₀.trans (RationalQuiver.liftFullSubEquivalence (RationalQuiver.FFunctor (GammaE D 0))
    (RepNilTarget D 0) (RationalQuivers.Species.RepNil (GammaE D 0).toSpecies.toSpecies)
    (fun M => (RationalQuiver.FObj_isNilpotent_iff M.obj).mp M.property)
    (exists_nil_preimage (GammaE D 0))), ?_⟩
  rw [CategoryTheory.Equivalence.trans_functor, he₀]
  rfl

/-! ### (b): `ℓ ≥ 1`, `√-1 ∉ E` -/

section Pos

variable (h : ¬ ∃ a : E, a * a = -1)

include h in
/-- `c ∈ G_E`, `√-1 ∉ E`.  @census none (helper) -/
theorem hcE : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1 := D.exists_chi_neg_one_iff.mpr h

include h in
/-- `#G_E = 2`.  @census none (helper) -/
theorem cardE : Nat.card (D.L ≃ₐ[E] D.L) = 2 := (D.sqrtExt (hcE D h)).card_gal

/-- `S(Γ_E)`, `ℓ ≥ 1`, `√-1 ∉ E`: the étale `E`-species of the `E`-rational Gelfand quiver
(`gelfandOfCardTwo`, which **is** `Γ_E`, `GammaE_gel_eq`).  @census none (helper) -/
noncomputable abbrev SE : EtaleSpecies E := (RationalQuiver.gelfandOfCardTwo E D.L (cardE D h)).toSpecies

/-- `Γ_E` for `ℓ ≥ 1`, `√-1 ∉ E`, is `gelfandOfCardTwo E L_E`.  @census none (helper) -/
theorem GammaE_gel_eq (k : ℕ) :
    GammaE D (k + 1) = RationalQuiver.gelfandOfCardTwo E D.L (cardE D h) :=
  D.gelfandOfSign_eq_gelfandOfCardTwo h

/-- **`R_E := E·√-1`** inside `{}_⋆M_{(⋆,±,⋆)} = L_E`: S5's `RGelfand` at `α = √-1`.
@census none (helper) -/
noncomputable def RE : RationalQuivers.Species.Relation (SE D h).toSpecies :=
  GelfandRelation.RGelfand E D.L (cardE D h) D.i

/-- `c(√-1) = -√-1`.  @census none (helper) -/
theorem conj_i : (D.sqrtExt (hcE D h)).conj D.i = -D.i := D.sqrtExt_conj_i (hcE D h)

/-- `√-1 ≠ 0`.  @census none (helper) -/
theorem i_ne_zero : D.i ≠ 0 := by
  intro h0
  have := D.i_mul_i
  rw [h0, mul_zero] at this
  exact zero_ne_one (neg_eq_zero.mp this.symm).symm

/-- **The coincidence at `E`** (`RQ2-5.16-C6`): `Rep^nil(S(Γ_E), R_E)` is the image under `F` of the
nilpotent representations of `Γ_E` with `a₋b₋ = a₊b₊` (S5's `repNilRel_RGelfand_iff` at `α = √-1`).
@census none (helper; clause `RQ2-5.16-C6`) -/
theorem repNilRel_RE_iff (W : EtaleSpecies.Rep (SE D h)) :
    RationalQuivers.Species.RepNilRel (SE D h).toSpecies (RE D h) W ↔
      (W.IsNilpotent ∧ ∃ M : RationalQuiver.FDRep (RationalQuiver.gelfandOfCardTwo E D.L (cardE D h)),
        Examples.SatisfiesGelfandRelation E D.L (cardE D h) M.toRep ∧
        Nonempty ((RationalQuiver.FFunctor _).obj M ≅ W)) :=
  GelfandRelation.repNilRel_RGelfand_iff E D.L (cardE D h) (D.sqrtExt (hcE D h)).conj_ne_one
    (conj_i D h) (i_ne_zero D) W

/-- `F` carries `Rep^nil(Γ_E)` into `Rep^nil(S(Γ_E), R_E)`.  @census none (helper) -/
theorem hF_pos : ∀ M : RationalStructure.RepNilQ (Dq := D.sqrtExt (hcE D h)) (cardE D h),
    RationalQuivers.Species.RepNilRel (SE D h).toSpecies (RE D h)
      ((RationalQuiver.FFunctor (RationalQuiver.gelfandOfCardTwo E D.L (cardE D h))).obj M.obj) :=
  fun M => (repNilRel_RE_iff D h _).mpr
    ⟨(RationalQuiver.FObj_isNilpotent_iff M.obj).mp M.property.1, M.obj, M.property.2, ⟨Iso.refl _⟩⟩

/-- Every object of `Rep^nil(S(Γ_E), R_E)` is `F` of an object of `Rep^nil(Γ_E)`.  @census none (helper) -/
theorem hQ_pos : ∀ Y : (RationalQuivers.Species.RepNilRel (SE D h).toSpecies (RE D h)).FullSubcategory,
    ∃ X : RationalQuiver.FDRep (RationalQuiver.gelfandOfCardTwo E D.L (cardE D h)),
      RationalStructure.RepNilRelQ (Dq := D.sqrtExt (hcE D h)) (cardE D h) X ∧
      Nonempty ((RationalQuiver.FFunctor _).obj X ≅ Y.obj) := by
  intro Y
  obtain ⟨hnil, M, hrel, ⟨iso⟩⟩ := (repNilRel_RE_iff D h Y.obj).mp Y.property
  exact ⟨M, ⟨RationalQuiver.FObj_isNilpotent_converse M
    (RationalQuiver.Species.isNilpotent_of_iso iso.symm hnil), hrel⟩, ⟨iso⟩⟩

/-- `F`, after re-indexing `Rep^nil(Γ_E)` to `gelfandOfCardTwo`, restricted to
`Rep^nil(S(Γ_E), R_E)`.  @census none (helper) -/
noncomputable def FRestrictPos :
    (Equivalence.RepNilGel D).FullSubcategory ⥤
      (RationalQuivers.Species.RepNilRel (SE D h).toSpecies (RE D h)).FullSubcategory :=
  (Compat.targetEquivCardTwo (hcE D h)).functor ⋙
    ObjectProperty.lift _ ((RationalStructure.RepNilRelQ (Dq := D.sqrtExt (hcE D h)) (cardE D h)).ι ⋙
      RationalQuiver.FFunctor _) (hF_pos D h)

set_option backward.isDefEq.respectTransparency.types false in
/-- **`thm:speciesE` (b)**, `ℓ ≥ 1`, `√-1 ∉ E`: `HC_λ(𝔤,K)_E ≃ Rep^nil(S(Γ_E), R_E)`, the functor `𝔼_E`
followed by the re-indexing and `F`.  @census none (helper; clauses `RQ2-5.16-H3`, `C2`, `C6`) -/
theorem speciesE_pos (k : ℕ) :
    ∃ e : HC (k + 1) E D ≌
        (RationalQuivers.Species.RepNilRel (SE D h).toSpecies (RE D h)).FullSubcategory,
      e.functor = E_E E D (k + 1) ⋙ FRestrictPos D h := by
  haveI := RationalQuiver.FFunctor_isEquivalence
    (RationalStructure.gelfandQ (Dq := D.sqrtExt (hcE D h)) (cardE D h))
  obtain ⟨e₀, he₀⟩ := gelfand_equivalence_pos (E := E) (D := D) (ℓ := k + 1) (by omega)
  refine ⟨e₀.trans ((Compat.targetEquivCardTwo (hcE D h)).trans
    (RationalQuiver.liftFullSubEquivalence (RationalQuiver.FFunctor _)
      (RationalStructure.RepNilRelQ (Dq := D.sqrtExt (hcE D h)) (cardE D h))
      (RationalQuivers.Species.RepNilRel (SE D h).toSpecies (RE D h)) (hF_pos D h) (hQ_pos D h))), ?_⟩
  rw [CategoryTheory.Equivalence.trans_functor, he₀]
  rfl

end Pos

/-! ### `C3`: `S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E` -/

/-- `S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E` for every `E` and `ℓ`.  @census none (helper; clause `RQ2-5.16-C3`) -/
noncomputable def speciesBaseChangeIso (ℓ : ℕ) :
    (GammaE D ℓ).toSpecies ≅ (GammaE ImagUnit.qi ℓ).toSpecies.baseChange E :=
  ((toSpeciesFunctor E D.L).mapIso (GammaE_eq_baseChange D ℓ)).unop.symm ≪≫
    ((EtaleSpecies.splitBy E D.L).ι.mapIso
      (counitIsoSplit (⟨(GammaE ImagUnit.qi ℓ).toSpecies.baseChange E, GammaE_isSplitBy D ℓ⟩ :
        SplitSpecies E D.L))).symm

/-! ### `ℚ[√-1] ⊗_ℚ E = L_E` for `√-1 ∉ E` (C5) and `R_E = R_Gelfand ⊗_ℚ E` (C4) -/

section Kappa

open scoped TensorProduct

noncomputable local instance (priority := high) instAlgebraQiS : Algebra ℚ ImagUnit.qi.L :=
  ImagUnit.qi.algebra

local instance instIsGaloisQiS : IsGalois ℚ ImagUnit.qi.L := ImagUnit.isGalois _

local instance instFiniteDimensionalQiS : FiniteDimensional ℚ ImagUnit.qi.L :=
  ImagUnit.finiteDimensional _

/-- `κ : E ⊗_ℚ ℚ[√-1] → L_E`, `a ⊗ q ↦ a·ι(q)`.  @census none (helper) -/
noncomputable def qiTensorHom : E ⊗[ℚ] ImagUnit.qi.L →ₐ[E] D.L :=
  Algebra.TensorProduct.lift (Algebra.ofId E D.L) (qiEmb D) (fun _ _ => Commute.all _ _)

/-- `κ(a ⊗ q) = a·ι(q)`.  @census none (helper) -/
theorem qiTensorHom_tmul (a : E) (q : ImagUnit.qi.L) :
    qiTensorHom D (a ⊗ₜ q) = algebraMap E D.L a * qiEmb D q :=
  Algebra.TensorProduct.lift_tmul _ _ _ a q

variable (h : ¬ ∃ a : E, a * a = -1)

include h in
/-- `κ` is surjective (`L_E = E[√-1]`).  @census none (helper) -/
theorem qiTensorHom_surjective : Function.Surjective (qiTensorHom D) := by
  intro y
  have hy : y ∈ Algebra.adjoin E {D.i} := D.adjoin_eq_top ▸ Algebra.mem_top
  have hsub : Algebra.adjoin E {D.i} ≤ (qiTensorHom D).range := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    refine ⟨(1 : E) ⊗ₜ ImagUnit.qi.i, ?_⟩
    show qiTensorHom D ((1 : E) ⊗ₜ ImagUnit.qi.i) = D.i
    rw [qiTensorHom_tmul, map_one, one_mul, qiEmb_i]
  exact hsub hy

include h in
/-- **`ℚ[√-1] ⊗_ℚ E = L_E` for `√-1 ∉ E`**: `κ` is an isomorphism of `E`-algebras (`RQ2-5.16-C5`).
@census none (helper; clause `RQ2-5.16-C5`) -/
theorem qiTensorHom_bijective : Function.Bijective (qiTensorHom D) := by
  have hrank : Module.finrank E (E ⊗[ℚ] ImagUnit.qi.L) = Module.finrank E D.L := by
    rw [Module.finrank_baseChange, ImagUnit.qi.finrank_eq_two_of_not_sqrt qi_not_sqrt',
      D.finrank_eq_two_of_not_sqrt h]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr
    (show Function.Surjective (qiTensorHom D).toLinearMap from qiTensorHom_surjective D h),
    qiTensorHom_surjective D h⟩

/-- `κ` as an isomorphism.  @census none (helper) -/
noncomputable def qiTensorEquiv : E ⊗[ℚ] ImagUnit.qi.L ≃ₐ[E] D.L :=
  AlgEquiv.ofBijective (qiTensorHom D) (qiTensorHom_bijective D h)

end Kappa

section RelBC

open scoped TensorProduct
open GelfandRelation

noncomputable local instance (priority := high) instAlgebraQiR : Algebra ℚ ImagUnit.qi.L :=
  ImagUnit.qi.algebra

local instance instIsGaloisQiR : IsGalois ℚ ImagUnit.qi.L := ImagUnit.isGalois _

local instance instFiniteDimensionalQiR : FiniteDimensional ℚ ImagUnit.qi.L :=
  ImagUnit.finiteDimensional _

/-- `#Gal(ℚ[√-1]/ℚ) = 2`.  @census none (helper) -/
theorem cardQ : Nat.card (ImagUnit.qi.L ≃ₐ[ℚ] ImagUnit.qi.L) = 2 :=
  ImagUnit.qi.card_gal_of_not_sqrt qi_not_sqrt'

/-- `R_Gelfand = ℚ·√-1` on `S_Gelfand = S(Γ_ℚ)`.  @census none (helper) -/
noncomputable def RGelfandQ : RationalQuivers.Species.Relation (SG ℚ ImagUnit.qi.L cardQ) :=
  RGelfand ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i

variable (h : ¬ ∃ a : E, a * a = -1)

/-- `Φ = θ_E⁻¹ ∘ κ ∘ (E ⊗ θ_ℚ) : E ⊗_ℚ {}_⋆M_p(S_Gelfand) ≃ₗ[E] {}_⋆M_p(S(Γ_E))`, `p = (⋆, ±, ⋆)`.
@census none (helper) -/
noncomputable def relPhi :
    E ⊗[ℚ] (RationalQuivers.Species.pathBimod (SG ℚ ImagUnit.qi.L cardQ) (idxG ℚ ImagUnit.qi.L cardQ) 1).carrier
      ≃ₗ[E] (RationalQuivers.Species.pathBimod (SG E D.L (cardE D h)) (idxG E D.L (cardE D h)) 1).carrier :=
  ((LinearEquiv.baseChange ℚ E _ _ (thetaEquiv ℚ ImagUnit.qi.L cardQ)).trans
    (qiTensorEquiv D h).toLinearEquiv).trans (thetaEquiv E D.L (cardE D h)).symm

/-- `Φ` sends the generator of `R_Gelfand` to that of `R_E`.  @census none (helper) -/
theorem relPhi_relGen :
    relPhi D h ((1 : E) ⊗ₜ[ℚ] relGen ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i (idxG ℚ ImagUnit.qi.L cardQ)) =
      relGen E D.L (cardE D h) D.i (idxG E D.L (cardE D h)) := by
  apply (thetaEquiv E D.L (cardE D h)).injective
  show thetaEquiv E D.L (cardE D h) ((thetaEquiv E D.L (cardE D h)).symm
    (qiTensorEquiv D h ((1 : E) ⊗ₜ[ℚ] thetaEquiv ℚ ImagUnit.qi.L cardQ
      (relGen ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i (idxG ℚ ImagUnit.qi.L cardQ))))) = _
  rw [LinearEquiv.apply_symm_apply]
  show qiTensorHom D ((1 : E) ⊗ₜ[ℚ] theta ℚ ImagUnit.qi.L cardQ
      (relGen ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i (idxG ℚ ImagUnit.qi.L cardQ))) =
    theta E D.L (cardE D h) (relGen E D.L (cardE D h) D.i (idxG E D.L (cardE D h)))
  rw [theta_relGen, theta_relGen, qiTensorHom_tmul, map_one, one_mul, qiEmb_i]

/-- Over the vertex field `L_⋆ = K`, an `L_⋆`-line is a `K`-line (copied from v1's
`GF.span_star_restrictScalars`).  @census none (helper) -/
theorem span_star_restrictScalars' {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (hc : Nat.card Gal(L/K) = 2)
    (x : (RationalQuivers.Species.pathBimod (SG K L hc) (idxG K L hc) 1).carrier) :
    (Submodule.span ((SG K L hc).L (idxG K L hc 0)) {x}).restrictScalars K = Submodule.span K {x} := by
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le_restrictScalars K _ _)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨k, rfl⟩ := exists_algebraMap_star K L hc (idxG_zero K L hc) c
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ k (Submodule.subset_span rfl)

/-- `(R_Gelfand)_p = K·(α ⊗ 1)` as a `K`-subspace (copied from v1).  @census none (helper) -/
theorem RGelfand_p_restrictScalars' {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (hc : Nat.card Gal(L/K) = 2) (α : L) :
    (RGelfand K L hc α (idxG K L hc) 1).toSubmodule.restrictScalars K =
      Submodule.span K {relGen K L hc α (idxG K L hc)} := by
  rw [RGelfand_one, RGelfandAt_pos K L hc α ⟨idxG_zero K L hc, idxG_one K L hc, idxG_two K L hc⟩]
  exact span_star_restrictScalars' hc _

/-- **`R_E = R_Gelfand ⊗_ℚ E`** (`RQ2-5.16-C4`): under `Φ`, the `E`-span of `1 ⊗ (R_Gelfand)_p` is
exactly `(R_E)_p = E·√-1`, at the path `p = (⋆, ±, ⋆)` (the path index `(idxG, 1)`); both relations are zero
at every other path by the definition of `RGelfandAt` — not restated here.
@census none (helper; clause `RQ2-5.16-C4`) -/
theorem relation_baseChange :
    (Submodule.span E ((fun x => (1 : E) ⊗ₜ[ℚ] x) ''
        (SetLike.coe (RGelfandQ (idxG ℚ ImagUnit.qi.L cardQ) 1).toSubmodule))).map
          (relPhi D h).toLinearMap =
      (RE D h (idxG E D.L (cardE D h)) 1).toSubmodule.restrictScalars E := by
  show (Submodule.span E ((fun x => (1 : E) ⊗ₜ[ℚ] x) ''
      (SetLike.coe (RGelfand ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i (idxG ℚ ImagUnit.qi.L cardQ)
        1).toSubmodule))).map (relPhi D h).toLinearMap =
    (RGelfand E D.L (cardE D h) D.i (idxG E D.L (cardE D h)) 1).toSubmodule.restrictScalars E
  set g := relGen ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i (idxG ℚ ImagUnit.qi.L cardQ)
  have hQ : SetLike.coe (RGelfand ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i (idxG ℚ ImagUnit.qi.L cardQ)
      1).toSubmodule = (SetLike.coe (Submodule.span ℚ {g}) : Set _) := by
    rw [← RGelfand_p_restrictScalars' cardQ ImagUnit.qi.i, Submodule.coe_restrictScalars]
  have hspan : Submodule.span E ((fun x => (1 : E) ⊗ₜ[ℚ] x) ''
      (Submodule.span ℚ {g} : Set _)) = Submodule.span E {(1 : E) ⊗ₜ[ℚ] g} := by
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨q, rfl⟩ := Submodule.mem_span_singleton.mp hx
      dsimp only
      rw [TensorProduct.tmul_smul]
      have hq : q • ((1 : E) ⊗ₜ[ℚ] g) = (algebraMap ℚ E q) • ((1 : E) ⊗ₜ[ℚ] g) :=
        (algebraMap_smul E q _).symm
      rw [hq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    · rintro _ rfl
      exact ⟨g, Submodule.subset_span rfl, rfl⟩
  rw [hQ, hspan, Submodule.map_span, Set.image_singleton]
  show Submodule.span E {relPhi D h ((1 : E) ⊗ₜ[ℚ] g)} = _
  rw [relPhi_relGen]
  exact (RGelfand_p_restrictScalars' (cardE D h) D.i).symm

end RelBC

/-! ### C7: the relation may not be omitted -/

section NotOmittable

variable {K' L' : Type} [Field K'] [Field L'] [Algebra K' L'] {Γ : RationalQuiver K' L'}

/-- A homomorphism of rational representations commutes with the transported edge map of an arrow
(copied from v1's `Corollaries`).  @census none (helper) -/
theorem arrowMap_hom' {M N : RationalQuiver.Rep Γ} (f : RationalQuiver.Rep.Hom M N)
    {a b : Γ.V} (g : a ⟶ b) (m : M.M a) :
    f.ψ b (M.arrowMap g m) = N.arrowMap g (f.ψ a m) := by
  obtain ⟨e, hs, ht⟩ := g
  subst hs
  subst ht
  exact f.edge e m

/-- A homomorphism commutes with every path composite (copied from v1).  @census none (helper) -/
theorem pathMap_hom' {M N : RationalQuiver.Rep Γ} (f : RationalQuiver.Rep.Hom M N) :
    ∀ {a b : Γ.V} (p : Quiver.Path a b) (m : M.M a),
      f.ψ b (M.pathMap p m) = N.pathMap p (f.ψ a m)
  | _, _, Quiver.Path.nil, m => by
      rw [RationalQuiver.Rep.pathMap_nil, RationalQuiver.Rep.pathMap_nil]
      rfl
  | _, _, Quiver.Path.cons p g, m => by
      rw [RationalQuiver.Rep.pathMap_cons, RationalQuiver.Rep.pathMap_cons]
      simp only [LinearMap.comp_apply]
      rw [arrowMap_hom' f g, pathMap_hom' f p m]

/-- An equality of two path composites is invariant under isomorphism (copied from v1).
@census none (helper) -/
theorem pathMap_eq_of_inv' {M N : RationalQuiver.Rep Γ} (f : RationalQuiver.Rep.Hom M N)
    (g : RationalQuiver.Rep.Hom N M) (hgf : ∀ (v : Γ.V) (y : N.M v), f.ψ v (g.ψ v y) = y)
    {a b : Γ.V} (p q : Quiver.Path a b) (h : M.pathMap p = M.pathMap q) :
    N.pathMap p = N.pathMap q := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ : ∃ y, f.ψ a y = x := ⟨g.ψ a x, hgf a x⟩
  rw [← pathMap_hom' f p y, ← pathMap_hom' f q y, LinearMap.congr_fun h y]

end NotOmittable

section NotOmittableE

variable (h : ¬ ∃ a : E, a * a = -1)

/-- `ex:gelfand`'s relation is invariant under isomorphism.  @census none (helper) -/
theorem satisfiesGelfandRelation_of_iso'
    {M N : RationalQuiver.FDRep (RationalQuiver.gelfandOfCardTwo E D.L (cardE D h))}
    (e : M ≅ N) (hM : Examples.SatisfiesGelfandRelation E D.L (cardE D h) M.toRep) :
    Examples.SatisfiesGelfandRelation E D.L (cardE D h) N.toRep := by
  refine pathMap_eq_of_inv' (e.hom : RationalQuiver.Rep.Hom M.toRep N.toRep)
    (e.inv : RationalQuiver.Rep.Hom N.toRep M.toRep) (fun v y => ?_) _ _ hM
  have h1 := congrArg (fun t : N ⟶ N => (t : RationalQuiver.Rep.Hom N.toRep N.toRep).ψ v y)
    e.inv_hom_id
  simpa only [RationalQuiver.FDRep.comp_ψ, RationalQuiver.FDRep.id_ψ, LinearMap.comp_apply,
    LinearMap.id_coe, id_eq] using h1

/-- S5's `gelfandNilTwist` over `(E, L_E)`: nilpotent, and the relation fails on it for `α = √-1`.
@census none (helper; the witness of `RQ2-5.16-C7`) -/
noncomputable def nilTwistE : RationalQuiver.FDRep (RationalQuiver.gelfandOfCardTwo E D.L (cardE D h)) where
  toRep := Examples.gelfandNilTwist E D.L (cardE D h) (D.sqrtExt (hcE D h)).conj_ne_one D.i
  finiteDimensional _ := inferInstanceAs (FiniteDimensional D.L (Prod D.L D.L))

/-- `c(√-1) ≠ √-1`.  @census none (helper) -/
theorem conj_i_ne : (D.sqrtExt (hcE D h)).conj D.i ≠ D.i := by
  rw [conj_i D h]
  intro hh
  have h2 : (2 : D.L) * D.i = 0 := by linear_combination -hh
  have h4 : algebraMap E D.L 4 = 0 := by
    have := congrArg (fun x => x * x) h2
    simp only [zero_mul] at this
    have hi := D.i_mul_i
    rw [map_ofNat]
    linear_combination (-1 : D.L) * this + 4 * hi
  have : (4 : E) = 0 := (algebraMap E D.L).injective (by rw [map_zero]; exact h4)
  norm_num at this

/-- **`RQ2-5.16-C7`: the relation may not be omitted** (`√-1 ∉ E`). For every representation of
`Γ_E`: `G_E`-equivariance makes the two composites `φ_{a₋}φ_{b₋}` and `φ_{a₊}φ_{b₊}` conjugate under
`φ_{⋆,c}`; the relation holds iff `φ_{a₋}φ_{b₋}` commutes with `φ_{⋆,c}`, i.e. is `E`-rational; and
there is a nilpotent representation of `S(Γ_E)` which does **not** satisfy `R_E`.
@census none (helper; clause `RQ2-5.16-C7`) -/
theorem relation_not_omittable :
    (∀ M : RationalQuiver.Rep (RationalQuiver.gelfandOfCardTwo E D.L (cardE D h)),
        (∀ m : M.M (Examples.gelfandStar E D.L (cardE D h)),
          M.φ' (D.sqrtExt (hcE D h)).conj
              (Examples.gelfand_smul_star E D.L (cardE D h) (D.sqrtExt (hcE D h)).conj_ne_one)
              (M.pathMap (Examples.gelfandPathMinus E D.L (cardE D h)) m)
            = M.pathMap (Examples.gelfandPathPlus E D.L (cardE D h))
                (M.φ' (D.sqrtExt (hcE D h)).conj
                  (Examples.gelfand_smul_star E D.L (cardE D h) (D.sqrtExt (hcE D h)).conj_ne_one) m)) ∧
        (Examples.SatisfiesGelfandRelation E D.L (cardE D h) M ↔
          ∀ m : M.M (Examples.gelfandStar E D.L (cardE D h)),
            M.φ' (D.sqrtExt (hcE D h)).conj
                (Examples.gelfand_smul_star E D.L (cardE D h) (D.sqrtExt (hcE D h)).conj_ne_one)
                (M.pathMap (Examples.gelfandPathMinus E D.L (cardE D h)) m)
              = M.pathMap (Examples.gelfandPathMinus E D.L (cardE D h))
                  (M.φ' (D.sqrtExt (hcE D h)).conj
                    (Examples.gelfand_smul_star E D.L (cardE D h) (D.sqrtExt (hcE D h)).conj_ne_one) m))) ∧
      ∃ W : EtaleSpecies.Rep (SE D h),
        RationalQuivers.Species.RepNil (SE D h).toSpecies W ∧
          ¬ RationalQuivers.Species.RepNilRel (SE D h).toSpecies (RE D h) W := by
  classical
  haveI := RationalQuiver.FFunctor_isEquivalence (RationalQuiver.gelfandOfCardTwo E D.L (cardE D h))
  refine ⟨fun M => ⟨fun m => Examples.gelfand_relation_conjugate E D.L (cardE D h)
      (D.sqrtExt (hcE D h)).conj_ne_one M m,
    (Examples.gelfand_relation_iff_transpose E D.L (cardE D h) (D.sqrtExt (hcE D h)).conj_ne_one M).2⟩, ?_⟩
  refine ⟨(RationalQuiver.FFunctor _).obj (nilTwistE D h), ?_, ?_⟩
  · exact (RationalQuiver.FObj_isNilpotent_iff (nilTwistE D h)).mp
      (Examples.gelfandNilTwist_isNilpotent E D.L (cardE D h) (D.sqrtExt (hcE D h)).conj_ne_one D.i)
  · intro hW
    obtain ⟨-, M, hrel, ⟨iso⟩⟩ := (repNilRel_RE_iff D h _).mp hW
    exact Examples.gelfand_relation_not_consequence_nil E D.L (cardE D h)
      (D.sqrtExt (hcE D h)).conj_ne_one D.i (conj_i_ne D h)
      (satisfiesGelfandRelation_of_iso' D h ((RationalQuiver.FFunctor _).preimageIso iso) hrel)

end NotOmittableE

/-! ### C5: the shape of `S(Γ_E)` for `√-1 ∉ E` -/

section Shape

open GelfandRelation GelfandDescent

variable (h : ¬ ∃ a : E, a * a = -1)

/-- **`RQ2-5.16-C5`**: for `√-1 ∉ E`, `ℚ[√-1] ⊗_ℚ E = L_E` is a field (`κ` bijective), and
`S(Γ_E)` has the two vertices `⋆`, `±` with `L_⋆ = E`, `L_± = L_E` and edge bimodules `L_E`
(`{}_⋆M_± = L_± ` via the right, `{}_±M_⋆ = L_±` via the left structure map).
@census none (helper; clause `RQ2-5.16-C5`) -/
theorem species_shape :
    Function.Bijective (qiTensorHom D) ∧
    (∀ i : (SE D h).I, i = nStar E D.L (cardE D h) ∨ i = nPm E D.L (cardE D h)) ∧
    nStar E D.L (cardE D h) ≠ nPm E D.L (cardE D h) ∧
    (GΓ E D.L (cardE D h)).vertexOrbitField (nStar E D.L (cardE D h)) = ⊥ ∧
    (GΓ E D.L (cardE D h)).vertexOrbitField (nPm E D.L (cardE D h)) = ⊤ ∧
    Function.Bijective ((SE D h).right (nStar E D.L (cardE D h)) (nPm E D.L (cardE D h))) := by
  refine ⟨qiTensorHom_bijective D h, fun i => ?_, star_ne_pm E D.L (cardE D h),
    Examples.gelfand_vertexOrbitField_star E D.L (cardE D h),
    Examples.gelfand_vertexOrbitField_pm E D.L (cardE D h), ?_⟩
  · induction i using Quotient.inductionOn with
    | h v =>
      have hv : ∀ n : Fin 3, n = 0 ∨ n = 1 ∨ n = 2 := by decide
      rcases hv v with rfl | rfl | rfl
      · exact Or.inr (vertexClass_0 E D.L (cardE D h))
      · exact Or.inl (vertexClass_1 E D.L (cardE D h))
      · exact Or.inr (vertexClass_2 E D.L (cardE D h))
  · haveI : Nontrivial ((ES E D.L (cardE D h)).M (nStar E D.L (cardE D h)) (nPm E D.L (cardE D h))) :=
      (AlgEquiv.ofBijective _ (evE_bijective (i := nStar E D.L (cardE D h))
        (j := nPm E D.L (cardE D h)) E D.L (cardE D h))).toEquiv.nontrivial
    exact ⟨((ES E D.L (cardE D h)).right _ _).toRingHom.injective,
      fun x => right_surjective E D.L (cardE D h) x⟩

end Shape


/-! ### The theorem -/

/-- **Theorem** (`thm:speciesE`).  Let `E` be a field of characteristic `0` and `S(Γ_E)` the étale
`E`-species associated to `Γ_E`.  (a) For `ℓ = 0`, `HC_0(𝔤,K)_E ≃ Rep^nil(S(Γ_E))`.  (b) For `ℓ ≥ 1`
and `√-1 ∉ E`, with `R_E := E·√-1 ⊆ {}_⋆M_{(⋆,±,⋆)} = L_E`, `HC_λ(𝔤,K)_E ≃ Rep^nil(S(Γ_E), R_E)`.  In
both cases `S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E`, and in case (b) `R_E = R_Gelfand ⊗_ℚ E`.  The relation may not be
omitted in (b).

@census    RQ2-5.16
@source    thm:speciesE
@clauses   RQ2-5.16-H1, RQ2-5.16-H2, RQ2-5.16-C1, RQ2-5.16-H3, RQ2-5.16-C2, RQ2-5.16-C3,
  RQ2-5.16-C4, RQ2-5.16-C5, RQ2-5.16-C6, RQ2-5.16-C7
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation) on `H1`, `C1`, `C2`, `C3`, `C4`.  `HC_λ(𝔤,K)_E` is
`HC ℓ E D` (`EX-HC`); the equivalences are pinned (`e.functor = E_E E D ℓ ⋙ F…`).  (b) is stated for
`ℓ = k + 1` (the recursion of `Γ_E`, `E_E`), and `S(Γ_E)` for `√-1 ∉ E` as the species of
`gelfandOfCardTwo E L_E`, which **is** `Γ_E` (`GammaE_gel_eq`); its target is `Rep^nil(S(Γ_E), R_E)`,
not `Rep^nil(S(Γ_ℚ) ⊗_ℚ E, R_Gelfand ⊗_ℚ E)` (transport along a species isomorphism is not in the
tree; v1's `V4-03`).  `C3` is an isomorphism of étale `E`-species, given as data, for every `E` and
`ℓ` (`speciesBaseChangeIso`).  `C4` (`relation_baseChange`, at the path `(⋆, ±, ⋆)`; both relations
are zero elsewhere by definition): here the identification `Φ = θ_E⁻¹ ∘ κ ∘ (E ⊗ θ_ℚ)` of the path
bimodules is assembled from the manuscript's own identifications (`θ` of `ex:gelfandspeciesrelation`,
`κ`).  The form of `C4` the proof of `thm:speciesE` gives, that the map of path bimodules induced by
the isomorphism of `C3` carries `R_Gelfand ⊗_ℚ E` onto `R_E`, is `relation_baseChange_C3`
(`RQ2-5.27-C2`; for every species isomorphism, `relation_baseChange_induced`, `RQ2-5.27-C1`; stage
T6, `Gelfand/Species/RelationBaseChange.lean`).  `C5` is `species_shape`, `C6` is `repNilRel_RE_iff`
(used in (b)), `C7` is `relation_not_omittable` (conjugacy, rationality criterion, nilpotent witness).
-/
theorem speciesE :
    (∃ e : HC 0 E D ≌
        (RationalQuivers.Species.RepNil (GammaE D 0).toSpecies.toSpecies).FullSubcategory,
      e.functor = E_E E D 0 ⋙ FRestrictZero D) ∧
    (∀ (h : ¬ ∃ a : E, a * a = -1) (k : ℕ),
      ∃ e : HC (k + 1) E D ≌
          (RationalQuivers.Species.RepNilRel (SE D h).toSpecies (RE D h)).FullSubcategory,
        e.functor = E_E E D (k + 1) ⋙ FRestrictPos D h) ∧
    (∀ ℓ : ℕ, Nonempty ((GammaE D ℓ).toSpecies ≅ (GammaE ImagUnit.qi ℓ).toSpecies.baseChange E)) :=
  ⟨speciesE_zero D, fun h k => speciesE_pos D h k, fun ℓ => ⟨speciesBaseChangeIso D ℓ⟩⟩

end RationalQuivers.Gelfand.Species
