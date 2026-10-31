module

public import RationalQuivers.Gelfand.Species.Equivalence

@[expose] public section

/-!
# The species corollaries over `ℚ` (tex §5.4: `cor:gelfandspecies`, `cor:cyclicspecies`, stage T4)

`cor:gelfandspecies` (`RQ2-5.06`) and `cor:cyclicspecies` (`RQ2-5.09`) are the case `E = ℚ` of
`thm:speciesE` (b) and (a) (`Gelfand/Species/Equivalence.lean`; OQ-2 revised: not moved, now
specializations).  `L_ℚ = ℚ[√-1]` (`ImagUnit.qi`), `√-1 ∉ ℚ`, and `R_ℚ = ℚ·√-1 = R_Gelfand`
(`ex:gelfandspeciesrelation`).

@census none (module; claimants of `RQ2-5.06`, `RQ2-5.09` below)
-/

namespace RationalQuivers.Gelfand.Species

open RationalQuivers.HC CategoryTheory

/-- `√-1 ∉ ℚ`.  @census none (helper) -/
theorem not_sqrt_Q : ¬ ∃ a : ℚ, a * a = -1 := qi_not_sqrt'

/-- **Corollary** (`cor:gelfandspecies`).  For `ℓ ≥ 1`, for the étale `ℚ`-species `S(Γ_ℚ)` of the
Gelfand quiver (`ex:gelfand`) with the relation `R_Gelfand` (`ex:gelfandspeciesrelation`),
`HC_λ(𝔤,K)_ℚ ≃ Rep^nil(S(Γ_ℚ), R_Gelfand)`.

*Proof.* `thm:speciesE` (b) at `E = ℚ`.

@census    RQ2-5.06
@source    cor:gelfandspecies
@clauses   RQ2-5.06-H1, RQ2-5.06-H2, RQ2-5.06-C1, RQ2-5.06-H3
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation): `HC_λ(𝔤,K)_ℚ` is `HC ℓ ℚ ImagUnit.qi` (`EX-HC`);
`ℓ ≥ 1` is `ℓ = k + 1`; `S(Γ_ℚ)` is the species of `gelfandOfCardTwo ℚ ℚ[√-1]`, which is `Γ_ℚ`
(`GammaE_gel_eq`); `R_Gelfand = R_ℚ = ℚ·√-1` (`RE`, S5's `RGelfand` at `√-1`).  `H3`: the target is
`RationalQuivers.Species.RepNilRel`, the intrinsic nilpotency of `def:speciesrelations`
(`Species.Rep.IsNilpotent`) together with the relation, not the essential image of `F`.  The
equivalence is pinned: its functor is `𝔼_ℚ` followed by the re-indexing and `F`.
-/
theorem species_equivalence_intrinsic (k : ℕ) :
    ∃ e : HC (k + 1) ℚ ImagUnit.qi ≌
        (RationalQuivers.Species.RepNilRel (SE ImagUnit.qi not_sqrt_Q).toSpecies
          (RE ImagUnit.qi not_sqrt_Q)).FullSubcategory,
      e.functor = E_E ℚ ImagUnit.qi (k + 1) ⋙ FRestrictPos ImagUnit.qi not_sqrt_Q :=
  speciesE_pos ImagUnit.qi not_sqrt_Q k

/-- `c ∈ Gal(ℚ[√-1]/ℚ)`.  @census none (helper) -/
theorem hcQ : ∃ σ : ImagUnit.qi.L ≃ₐ[ℚ] ImagUnit.qi.L, ImagUnit.qi.chi σ = -1 :=
  hcE ImagUnit.qi not_sqrt_Q

/-- `F` on the quiver of `ex:cyclic` (`cyclicOfCardTwo`, which is `Γ_ℚ` at `ℓ = 0`), restricted to
nilpotent representations, after re-indexing `Rep^nil(Γ_ℚ)` to it.  @census none (helper) -/
noncomputable def FRestrictCyclicQ :
    (RepNilTarget ImagUnit.qi 0).FullSubcategory ⥤
      (RationalQuivers.Species.RepNil
        (Cyclic.cyclicQ (Dq := ImagUnit.qi.sqrtExt hcQ) (cardE ImagUnit.qi not_sqrt_Q)).toSpecies.toSpecies).FullSubcategory :=
  (Compat.targetEquivCardTwoZ hcQ).functor ⋙
    ObjectProperty.lift _ ((RationalQuiver.RepNil _).ι ⋙ RationalQuiver.FFunctor _)
      (fun M => (RationalQuiver.FObj_isNilpotent_iff M.obj).mp M.property)

/-- **Corollary** (`cor:cyclicspecies`).  For `ℓ = 0`, for the étale `ℚ`-species `S(Γ_ℚ)` of the
cyclic quiver (`ex:cyclic`), `HC_0(𝔤,K)_ℚ ≃ Rep^nil(S(Γ_ℚ))`.

*Proof.* `thm:speciesE` (a) at `E = ℚ`: `thm:cyclicEEequivalence` at `E = ℚ` followed by
`Rep^nil(Γ_ℚ) ≃ Rep^nil(S(Γ_ℚ))` (`RQ2-2.29`), with `Γ_ℚ` read as the quiver of `ex:cyclic`.

@census    RQ2-5.09
@source    cor:cyclicspecies
@clauses   RQ2-5.09-H1, RQ2-5.09-H2, RQ2-5.09-C1, RQ2-5.09-H3
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation): `HC_0(𝔤,K)_ℚ` is `HC 0 ℚ ImagUnit.qi` (`EX-HC`).
`S(Γ_ℚ)` is the species of the quiver of `ex:cyclic`, `cyclicOfCardTwo ℚ ℚ[√-1]` (`Cyclic.cyclicQ`),
which **is** `Γ_ℚ = GammaE ImagUnit.qi 0` (`Compat.cyclicOfSign_eq_cyclicOfCardTwo`); `thm:speciesE`
(a), stated on `S(GammaE D 0)`, is used here through its two ingredients (`gelfand_equivalence_zero`
and `F`) with the re-indexing `Compat.targetEquivCardTwoZ` in between; the quiver↔species step
`Rep^nil(Γ_ℚ) ≃ Rep^nil(S(Γ_ℚ))` is T0's `RQ2-2.29` (`RationalQuiver.FFunctor_isEquivalence`, restricted to
nilpotent objects by `RationalQuiver.liftFullSubEquivalence`).  `H3`: the target is
`RationalQuivers.Species.RepNil`, intrinsic nilpotency.  The equivalence is pinned.
-/
theorem cyclic_species_equivalence :
    ∃ e : HC 0 ℚ ImagUnit.qi ≌
        (RationalQuivers.Species.RepNil
          (Cyclic.cyclicQ (Dq := ImagUnit.qi.sqrtExt hcQ) (cardE ImagUnit.qi not_sqrt_Q)).toSpecies.toSpecies).FullSubcategory,
      e.functor = E_E ℚ ImagUnit.qi 0 ⋙ FRestrictCyclicQ := by
  haveI := RationalQuiver.FFunctor_isEquivalence
    (Cyclic.cyclicQ (Dq := ImagUnit.qi.sqrtExt hcQ) (cardE ImagUnit.qi not_sqrt_Q))
  obtain ⟨e₀, he₀⟩ := gelfand_equivalence_zero (D := ImagUnit.qi)
  refine ⟨e₀.trans ((Compat.targetEquivCardTwoZ hcQ).trans
    (RationalQuiver.liftFullSubEquivalence (RationalQuiver.FFunctor _) (RationalQuiver.RepNil _)
      (RationalQuivers.Species.RepNil _) (fun M => (RationalQuiver.FObj_isNilpotent_iff M.obj).mp M.property)
      (exists_nil_preimage _))), ?_⟩
  rw [CategoryTheory.Equivalence.trans_functor, he₀]
  rfl

end RationalQuivers.Gelfand.Species
