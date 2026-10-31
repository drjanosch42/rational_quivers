module

public import RationalQuivers.Quiver.Basic

@[expose] public section

/-!
# Homomorphisms of `K`-rational quivers

Formalizes Definition `def:rationalquiverhom` of §1.2 of `latex/rational_quivers.tex`
(census `RQ2-1.04`).

## Main definitions / results
* `RationalQuivers.RationalQuiver.Hom` — Definition `def:rationalquiverhom` (census `RQ2-1.04`).
* `RationalQuivers.RationalQuiver.instCategory` — the category `{K-rational quivers}`, whose
  hom-sets are the paper's `Hom_K(Γ_K, Γ'_K)` and which is the ambient category of the adjunction
  `prop:quiverrestrictionbasechangeadjunction` (`RQ2-1.07`).

## Implementation notes

**AN-10.** `def:rationalquivers` fixes one Galois extension `L/K` and a homomorphism
`ρ : Gal(L/K) → Aut(Γ)`, whereas `def:rationalquiverhom` asks a morphism to commute with the
`Gal(K^sep/K)`-actions. The two cohere only through the inflation-and-factorization remark, which
the census makes its own row `RQ2-1.20`. Here `Hom` is stated over the Galois group `Gal(L/K)` that
both objects share; `RationalQuivers.RationalQuiver.homEquivInflate` in `Quiver/Inflation.lean`
proves that this is the *same* hom-set as the one taken over `Gal(K^sep/K)` after inflation, which
is what clause `RQ2-1.04-H2` asks for, and instantiating `L := K^sep` recovers the source's
formulation verbatim.
-/

universe u

namespace RationalQuivers

open CategoryTheory

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]

namespace RationalQuiver

/-- **Definition 1.4** (`def:rationalquiverhom`).
A homomorphism `φ : Γ_K → Γ'_K` of two quivers over `K` is a homomorphism of the underlying
quivers `φ : Γ → Γ'` (i.e. compatible with `s` and `t`) which commutes with the Galois actions on
`Γ_K` and `Γ'_K`.

@census    RQ2-1.04
@source    def:rationalquiverhom
@clauses   RQ2-1.04-H1, RQ2-1.04-H2, RQ2-1.04-C1, RQ2-1.04-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION of clause `RQ2-1.04-H2` (`if_missing =
JUSTIFIED_REFORMULATION`; ATTESTATION AN-10). The source writes the commutation condition for the
absolute group `Gal(K^sep/K)`, having just observed (`RQ2-1.20`) that every rational structure
inflates to a continuous `Gal(K^sep/K)`-action. We state it for the group `Gal(L/K)` that the two
objects share. This is not a weakening: (i) taking `L := K^sep` *is* the source's statement, since
a `K`-rational quiver in the absolute sense is exactly a `RationalQuiver K K^sep`; and (ii) for a
general `L`, `RationalQuiver.homEquivInflate` (`Quiver/Inflation.lean`, clause `RQ2-1.20-C2`)
exhibits a bijection between this hom-set and the hom-set of the inflations over `Gal(K^sep/K)`,
because inflation is along a *surjection* `Gal(K^sep/K) ↠ Gal(L/K)`. Clause `RQ2-1.04-C1` is the
field `toRQuiverHom`; clause `RQ2-1.04-C2` is the pair of equivariance fields.

**Residual (recorded for the G6 correspondence table).** The source's category of quivers over `K`
is not indexed by a splitting field at all: because morphisms are taken over `Gal(K^sep/K)`,
`Γ_K` and `Γ'_K` may be split by *different* extensions `L/K` and `L'/K`, and `Hom_K(Γ_K, Γ'_K)`
is still defined. `RationalQuiver.Hom` as stated requires a common `L`. This is not a loss of
generality — `RQ2-1.20` factors each structure through a finite Galois quotient, so any two objects
are split by their compositum `L L'`, and `homEquivInflate` identifies the hom-sets computed over
`L`, over `L'` and over any common overfield — but the *reindexing* is not itself formalized here.
Making it explicit would mean building the colimit category over all finite Galois `L/K`, which no
statement of §1.2–§2.6 needs: `RQ2-1.05`, `RQ2-1.06` and `RQ2-1.07` all fix one `L` and vary only the
intermediate field `E'`. Disclosed rather than silently assumed.
-/
@[ext]
structure Hom (Γ Γ' : RationalQuiver K L) : Type u where
  /-- Clause `RQ2-1.04-C1`: a homomorphism of the underlying classical quivers. -/
  toRQuiverHom : Γ.toRQuiver ⟶ Γ'.toRQuiver
  /-- Clause `RQ2-1.04-C2`, vertices: `φ` commutes with the Galois actions on the vertex sets. -/
  equivariant_V : ∀ (σ : Gal(L/K)) (v : Γ.V), toRQuiverHom.onV (σ • v) = σ • toRQuiverHom.onV v
  /-- Clause `RQ2-1.04-C2`, edges: `φ` commutes with the Galois actions on the edge sets. -/
  equivariant_E : ∀ (σ : Gal(L/K)) (e : Γ.E), toRQuiverHom.onE (σ • e) = σ • toRQuiverHom.onE e

/-- The identity homomorphism of a `K`-rational quiver.

@census none (helper)
-/
protected def Hom.id (Γ : RationalQuiver K L) : Hom Γ Γ where
  toRQuiverHom := 𝟙 Γ.toRQuiver
  equivariant_V _ _ := rfl
  equivariant_E _ _ := rfl

/-- Composition of homomorphisms of `K`-rational quivers.

@census none (helper)
-/
protected def Hom.comp {Γ Γ' Γ'' : RationalQuiver K L} (f : Hom Γ Γ') (g : Hom Γ' Γ'') :
    Hom Γ Γ'' where
  toRQuiverHom := f.toRQuiverHom ≫ g.toRQuiverHom
  equivariant_V σ v := by
    simp only [RQuiver.comp_onV, Function.comp_apply, f.equivariant_V, g.equivariant_V]
  equivariant_E σ e := by
    simp only [RQuiver.comp_onE, Function.comp_apply, f.equivariant_E, g.equivariant_E]

/-- The category `{K-rational quivers}` (with respect to the Galois extension `L/K`). Its hom-sets
are the `Hom_K(Γ_K, Γ'_K)` of the source; the paper names this category in its list of categories
(`census/NOTATION.md` §11), and `prop:quiverrestrictionbasechangeadjunction` (`RQ2-1.07`) is an
adjunction between two such categories.

@census none (helper: supplies the categories for `RQ2-1.05`–`RQ2-1.07`)
-/
instance instCategory : Category.{u, u + 1} (RationalQuiver K L) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The identity morphism of rational quivers has the identity as underlying quiver morphism.
@census none (helper) -/
@[simp] lemma id_toRQuiverHom (Γ : RationalQuiver K L) :
    Hom.toRQuiverHom (𝟙 Γ) = 𝟙 Γ.toRQuiver := rfl

/-- Composition of rational-quiver morphisms is composition of the underlying quiver morphisms.
@census none (helper) -/
@[simp] lemma comp_toRQuiverHom {Γ Γ' Γ'' : RationalQuiver K L} (f : Γ ⟶ Γ') (g : Γ' ⟶ Γ'') :
    (f ≫ g).toRQuiverHom = f.toRQuiverHom ≫ g.toRQuiverHom := rfl

/-- The forgetful functor to classical quivers: forget the rational structure. Together with
`RQuiver.toQuiv` this is the full bridge from a `K`-rational quiver to mathlib's `Quiv`
(design decision D4).

@census none (helper: D4 bridge)
-/
def forget : RationalQuiver K L ⥤ RQuiver.{u} where
  obj Γ := Γ.toRQuiver
  map f := f.toRQuiverHom
  map_id _ := rfl
  map_comp _ _ := rfl
end RationalQuiver

end RationalQuivers
