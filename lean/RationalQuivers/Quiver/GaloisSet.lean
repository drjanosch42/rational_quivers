import RationalQuivers.Quiver.Basic

/-!
# `K`-rational quivers as diagrams of finite continuous Galois sets

Formalizes the remark after `def:splitrationalquivers` in §1.2 of `latex/rational_quivers.tex`
(census `RQ2-1.23`): "we reformulated Gabriel's original definition in the category of (continuous
discrete) `Gal(L/K)`-sets".

## Main definitions / results
* `RationalQuivers.GaloisSet` — a finite continuous discrete `Gal(L/K)`-set.
* `RationalQuivers.GaloisSetDiagram` — a diagram `E ⇉ V` of such.
* `RationalQuivers.RationalQuiver.toDiagram` and
  `RationalQuivers.RationalQuiver.toDiagram_bijective` — the reformulation (census `RQ2-1.23`).
-/

universe u

namespace RationalQuivers

open CategoryTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [galoisLK : IsGalois K L]

/-- A finite continuous discrete `Gal(L/K)`-set: the objects of the category in which the source
reformulates Gabriel's definition.

`L/K` Galois is carried as a field, for the reason given at `RationalQuiver` (r6 delta): as a
header binder it was pruned, and `GaloisSet` elaborated as a `Gal`-set for an arbitrary algebra
rather than for a Galois extension.

**S1 G4 finding C-1.** As for `RationalQuiver.galois`, the field is a **term** (`X.galois`), not a
synthesizable instance, and cannot be made one: `attribute [instance] GaloisSet.galois` is rejected
by Lean (the explicit `self` does not occur in `IsGalois K L`). Use `haveI := X.galois`.

@census none (helper for `RQ2-1.23`)
-/
structure GaloisSet : Type (u + 1) where
  /-- `L/K` is a Galois extension; carried as a field so that it cannot be pruned. -/
  [galois : IsGalois K L]
  /-- The underlying set. -/
  carrier : Type u
  /-- The source's category is that of *finite* `Gal(L/K)`-sets. -/
  finite : Finite carrier
  /-- The `Gal(L/K)`-action. -/
  act : Gal(L/K) →* Equiv.Perm carrier
  /-- The action is continuous for the discrete topology on `carrier`. -/
  smooth : IsSmooth act

attribute [instance] GaloisSet.finite

/-- A diagram `E ⇉ V` (i.e. `s, t : E → V`) in the category of finite continuous discrete
`Gal(L/K)`-sets: this is what the source's remark says a `K`-rational quiver *is*.

@census none (helper for `RQ2-1.23`)
-/
structure GaloisSetDiagram : Type (u + 1) where
  /-- The `Gal(L/K)`-set of vertices. -/
  vertices : GaloisSet K L
  /-- The `Gal(L/K)`-set of edges. -/
  edges : GaloisSet K L
  /-- The source map, a morphism of `Gal(L/K)`-sets. -/
  source : edges.carrier → vertices.carrier
  /-- The target map, a morphism of `Gal(L/K)`-sets. -/
  target : edges.carrier → vertices.carrier
  /-- `s` is `Gal(L/K)`-equivariant (`eq:stgaloisequivariance`). -/
  source_equivariant : ∀ (σ : Gal(L/K)) (e : edges.carrier),
    source (edges.act σ e) = vertices.act σ (source e)
  /-- `t` is `Gal(L/K)`-equivariant (`eq:stgaloisequivariance`). -/
  target_equivariant : ∀ (σ : Gal(L/K)) (e : edges.carrier),
    target (edges.act σ e) = vertices.act σ (target e)

namespace RationalQuiver

/-- A `K`-rational quiver, read as a diagram `E ⇉ V` of finite continuous discrete
`Gal(L/K)`-sets.

@census none (helper: the forward half of `RQ2-1.23`)
-/
def toDiagram (Γ : RationalQuiver K L) : GaloisSetDiagram K L where
  vertices :=
    { carrier := Γ.V
      finite := Γ.toRQuiver.finite_V
      act := (RQuiver.Aut.toPermV Γ.toRQuiver).comp Γ.ρ
      smooth := Γ.smooth_V }
  edges :=
    { carrier := Γ.E
      finite := Γ.toRQuiver.finite_E
      act := (RQuiver.Aut.toPermE Γ.toRQuiver).comp Γ.ρ
      smooth := Γ.smooth_E }
  source := Γ.toRQuiver.source
  target := Γ.toRQuiver.target
  source_equivariant := fun σ e => Γ.source_smul σ e
  target_equivariant := fun σ e => Γ.target_smul σ e

/-- The inverse of `toDiagram`: a diagram `E ⇉ V` of finite continuous discrete `Gal(L/K)`-sets,
read back as a `K`-rational quiver. This is `RationalQuiver.ofAction` applied to the diagram's own
data, so it is the source's reformulation run backwards and adds no mathematics.

@census none (helper: the backward half of `RQ2-1.23`)
-/
private def ofDiagram (D : GaloisSetDiagram K L) : RationalQuiver K L :=
  ofAction K L
    { V := D.vertices.carrier
      E := D.edges.carrier
      source := D.source
      target := D.target
      finite_V := D.vertices.finite
      finite_E := D.edges.finite }
    D.vertices.act D.edges.act D.source_equivariant D.target_equivariant
    D.vertices.smooth D.edges.smooth

/-- **Remark** (unlabelled in the source; census `RQ2-1.23`).
A `K`-rational quiver is exactly a diagram `E ⇉ V` (via `s` and `t`) in the category of finite
continuous discrete `Gal(L/K)`-sets: Gabriel's original definition reformulated in that category.

@census    RQ2-1.23
@source    rmk:galoissetdiagram
@clauses   RQ2-1.23-H1, RQ2-1.23-C1
@imports   none
@divergence none. Clause `RQ2-1.23-H1` is the argument `Γ : RationalQuiver K L`; clause
`RQ2-1.23-C1` ("the data of `Γ_K` is *equivalent* to a diagram `s,t : E ⇉ V` of finite
`Gal(L/K)`-sets") is the bijectivity of `toDiagram`, which upgrades to the type equivalence
`RationalQuiver.diagramEquiv` below. The category of finite continuous discrete `Gal(L/K)`-sets is
realised object-wise as `GaloisSet K L`; the source's remark speaks only of the data of a diagram,
not of the morphisms, and this statement says exactly that the two kinds of data correspond.
-/
theorem toDiagram_bijective : Function.Bijective (toDiagram K L) :=
  Function.bijective_iff_has_inverse.mpr ⟨ofDiagram K L, fun _ => rfl, fun _ => rfl⟩

/-- The equivalence of clause `RQ2-1.23-C1`, packaged.

@census none (helper: clause RQ2-1.23-C1)
-/
noncomputable def diagramEquiv : RationalQuiver K L ≃ GaloisSetDiagram K L :=
  Equiv.ofBijective _ (toDiagram_bijective K L)

end RationalQuiver

end RationalQuivers
