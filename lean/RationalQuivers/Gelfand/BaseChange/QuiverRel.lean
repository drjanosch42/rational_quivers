module

public import RationalQuivers.Gelfand.Split.Construction
public import RationalQuivers.Species.Rep.Gelfand
public import RationalQuivers.Quiver.Rep.GeneralBaseChange

@[expose] public section

/-!
# Relation-carrying quiver-side base change (stage T4, `prop:basechange`)

*Provenance.*  Relocated in stage T4 (WP-11, G2 finding F3) from v1's `Gelfand/GeneralBase.lean`
(`R-S10-14`): `repNilRelGel`, `qBCssRel`, `qBCnsRel`, statements and proofs unchanged, names unchanged,
so that the relocated base change (`Gelfand/BaseChange/*`) no longer imports the v1 Q-chain through
`Gelfand.GeneralBase`.  At the relocation (`3488bf2`) `Gelfand.GeneralBase` imported this module; v1's
`Gelfand/GeneralBase.lean` was deleted at WP-13 (`44df340`), and in today's tree this module is imported
by `Gelfand/BaseChange/Split.lean`.  *(2026-10-21, O-V2-6.)*

@census none (module; helpers of `RQ2-5.14`)
-/

namespace RationalQuivers.Gelfand

open RationalQuivers.HC RationalQuivers.RationalQuiver CategoryTheory
open scoped TensorProduct

/-- `Rep^nil` with `ex:gelfand`'s relation, for the **non-split** Gelfand quiver over any quadratic
Galois `L/K`.  v1's `Gelfand.RepNilRelQ` was this at `(ℚ, ℚ[√-1])`, definitionally; in v2,
`RationalStructure.RepNilRelQ hcard` is this at `(E, Dq.carrier)`, definitionally.  *(2026-10-21,
O-V2-6.)*

@census none (helper) -/
def repNilRelGel (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (h : Nat.card (L ≃ₐ[K] L) = 2) :
    ObjectProperty (RationalQuiver.FDRep (RationalQuiver.gelfandOfCardTwo K L h)) :=
  fun M => M.toRep.IsNilpotent ∧ Examples.SatisfiesGelfandRelation K L h M.toRep

/-- **`RQ-5.08-C4a`, `ss`, relation-carrying**: base change `Rep^nil_rel(Γ_E) ⥤ Rep^nil_rel(Γ_{E''})`
for the split Gelfand quiver, for an **arbitrary** `E → E''`.  The named quiver-side vertical of
`C4b`'s `ss` square.

@census none (helper; `RQ-5.08-C4`) -/
noncomputable def qBCssRel (E E'' : Type) [Field E] [Field E''] [Algebra E E''] :
    (RepNilRelSplit E).FullSubcategory ⥤ (RepNilRelSplit E'').FullSubcategory where
  obj M :=
    ⟨(M.obj.toSplit E'' : RationalQuiver.FDRep (gelfandSplit E'')),
      ⟨RationalQuiver.Rep.toSplit_isNilpotent E'' M.property.1,
        RationalQuiver.Rep.toSplit_pathMap_congr E'' M.obj.toRep _ _ M.property.2⟩⟩
  map f := ⟨RationalQuiver.Rep.Hom.toSplit E'' f.hom⟩
  map_id M := by
    apply CategoryTheory.ObjectProperty.hom_ext
    apply RationalQuiver.Rep.Hom.ext
    funext (v : (gelfandSplit E).V)
    exact (LinearMap.baseChange_id :
      (LinearMap.id : M.obj.toRep.M v →ₗ[E] M.obj.toRep.M v).baseChange E'' = LinearMap.id)
  map_comp {X Y Z} f g := by
    apply CategoryTheory.ObjectProperty.hom_ext
    apply RationalQuiver.Rep.Hom.ext
    funext (v : (gelfandSplit E).V)
    exact LinearMap.baseChange_comp (A := E'') (f.hom.ψ v) (g.hom.ψ v)

/-- **`RQ-5.08-C4a`, `ns`, relation-carrying**: base change `Rep^nil_rel(Γ_K) ⥤ Rep^nil_rel(Γ_{K''})`
from the non-split Gelfand quiver to the split one, along `L → K''`.  The named quiver-side
vertical of `C4b`'s `ns` square — the non-degenerate one.

@census none (helper; `RQ-5.08-C4`) -/
noncomputable def qBCnsRel (K L K'' : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [FiniteDimensional K L] (h : Nat.card (L ≃ₐ[K] L) = 2) [Field K''] [Algebra L K''] :
    (repNilRelGel K L h).FullSubcategory ⥤ (RepNilRelSplit K'').FullSubcategory where
  obj M :=
    ⟨(M.obj.toSplit K'' : RationalQuiver.FDRep (gelfandSplit K'')),
      ⟨RationalQuiver.Rep.toSplit_isNilpotent K'' M.property.1,
        RationalQuiver.Rep.toSplit_pathMap_congr K'' M.obj.toRep _ _ M.property.2⟩⟩
  map f := ⟨RationalQuiver.Rep.Hom.toSplit K'' f.hom⟩
  map_id M := by
    apply CategoryTheory.ObjectProperty.hom_ext
    apply RationalQuiver.Rep.Hom.ext
    funext (v : (RationalQuiver.gelfandOfCardTwo K L h).V)
    exact (LinearMap.baseChange_id :
      (LinearMap.id : M.obj.toRep.M v →ₗ[L] M.obj.toRep.M v).baseChange K'' = LinearMap.id)
  map_comp {X Y Z} f g := by
    apply CategoryTheory.ObjectProperty.hom_ext
    apply RationalQuiver.Rep.Hom.ext
    funext (v : (RationalQuiver.gelfandOfCardTwo K L h).V)
    exact LinearMap.baseChange_comp (A := K'') (f.hom.ψ v) (g.hom.ψ v)

end RationalQuivers.Gelfand
