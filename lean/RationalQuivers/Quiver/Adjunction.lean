import RationalQuivers.Quiver.Restriction

/-!
# Restriction is left adjoint to base change

Formalizes Proposition `prop:quiverrestrictionbasechangeadjunction` of §1.2 of
`latex/rational_quivers.tex` (census `RQ2-1.07`).

## Main definitions / results
* `RationalQuivers.RationalQuiver.restriction_baseChange_adjunction` — Proposition
  `prop:quiverrestrictionbasechangeadjunction` (census `RQ2-1.07`).

## Implementation notes

The source states a **natural** isomorphism of hom-sets, and its proof is "an elementary
application of the universal property of the functor `Gal(L/K) ×_{Gal(L/E')} (−)`, which is left
adjoint to the forgetful functor". We therefore state the proposition as a mathlib
`CategoryTheory.Adjunction`, not as a bare `Equiv` of hom-sets: an `Adjunction` *is* the hom-set
bijection (clause `RQ2-1.07-C1`) together with its naturality in both variables (clause
`RQ2-1.07-C2`), which the stage plan flags as a named risk and which `CONVENTIONS.md` §7 requires.
-/

universe u

namespace RationalQuivers

open CategoryTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
variable (E' : IntermediateField K L) [FiniteDimensional K E']

namespace RationalQuiver

/-! ### The unit and the counit

Both maps are the concrete ones of the source's own proof: the unit is `v ↦ 1 ⊗ v` into
`Gal(L/K) ×_{Gal(L/E')} (−)`, the counit is `g ⊗ v ↦ g • v`. Write `f := galRestrict K L E'` for
the inclusion `Gal(L/E') ↪ Gal(L/K)`; the `Gal(L/E')`-action on a base-changed quiver is by
definition the `Gal(L/K)`-action read along `f`, which is what makes the two sides of each
obligation comparable at all. -/

/-- `Gal(L/E')`-equivariance of `x ↦ 1 ⊗ x`: the computation
`f σ • (1 ⊗ x) = (f σ) ⊗ x = (f σ * f σ⁻¹) ⊗ (σ • x) = 1 ⊗ (σ • x)`
of the unit of `prop:quiverrestrictionbasechangeadjunction`, in the generality of an arbitrary
`Gal(L/E')`-set `X`.

@census none (helper for `RQ2-1.07`)
-/
private theorem mk_one_smul {X : Type u} [MulAction Gal(L/E') X] (σ : Gal(L/E')) (x : X) :
    InducedSet.mk (galRestrict K L E') 1 (σ • x)
      = InducedSet.permHom (galRestrict K L E') X (galRestrict K L E' σ)
          (InducedSet.mk (galRestrict K L E') 1 x) := by
  rw [InducedSet.permHom_apply, mul_one,
    InducedSet.mk_smul (galRestrict K L E') (galRestrict K L E' σ) σ x, map_inv, mul_inv_cancel]

/-- The unit `Γ_{E'} ⟶ E' ⊗_K (res_{E'/K} Γ_{E'})` of
`prop:quiverrestrictionbasechangeadjunction`: `v ↦ 1 ⊗ v` on vertices and `e ↦ 1 ⊗ e` on edges.
Compatibility with `s` and `t` is `InducedSet.map_mk`; `Gal(L/E')`-equivariance is `mk_one_smul`.

@census none (helper for `RQ2-1.07`)
-/
private def adjUnit :
    𝟭 (RationalQuiver (E' : Type u) L) ⟶ restriction K L E' ⋙ baseChange K L E' where
  app _ :=
    { toRQuiverHom :=
        { onV := fun v => InducedSet.mk (galRestrict K L E') 1 v
          onE := fun e => InducedSet.mk (galRestrict K L E') 1 e
          onV_source := fun _ => rfl
          onV_target := fun _ => rfl }
      equivariant_V := fun σ v => mk_one_smul K L E' σ v
      equivariant_E := fun σ e => mk_one_smul K L E' σ e }
  naturality _ _ _ := rfl

/-- The counit on vertices: `g ⊗ v ↦ g • v`. This is the one computation of
`prop:quiverrestrictionbasechangeadjunction` that has content, and it is where base change does its
work: on `E' ⊗_K Γ'_K` the element `σ : Gal(L/E')` acts as `f σ`, so the two representatives
`(g, v)` and `(g * f σ⁻¹, σ • v)` of the same class have the same image
`(g * f σ⁻¹) • (f σ • v) = g • v`.

@census none (helper for `RQ2-1.07`)
-/
private def adjCounitOnV (Γ' : RationalQuiver K L) :
    InducedSet (galRestrict K L E') ((baseChange K L E').obj Γ').V → Γ'.V :=
  Quotient.lift (fun p : Gal(L/K) × Γ'.V => p.1 • p.2) (by
    -- The `Gal(L/K)`-action on `E' ⊗_K Γ'_K` is that of `Γ'_K`; naming it locally is what
    -- lets the two sides below be written down at all.
    letI : MulAction Gal(L/K) ((baseChange K L E').obj Γ').V := mulActionV Γ'
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨σ, hσ⟩
    rw [Prod.mk.injEq] at hσ
    obtain ⟨rfl, rfl⟩ := hσ
    show a • x = (a * galRestrict K L E' σ⁻¹) • (galRestrict K L E' σ • x)
    rw [← mul_smul, map_inv, inv_mul_cancel_right])

/-- The counit on edges: `g ⊗ e ↦ g • e`; same computation as `adjCounitOnV`.

@census none (helper for `RQ2-1.07`)
-/
private def adjCounitOnE (Γ' : RationalQuiver K L) :
    InducedSet (galRestrict K L E') ((baseChange K L E').obj Γ').E → Γ'.E :=
  Quotient.lift (fun p : Gal(L/K) × Γ'.E => p.1 • p.2) (by
    -- The `Gal(L/K)`-action on `E' ⊗_K Γ'_K` is that of `Γ'_K`; naming it locally is what
    -- lets the two sides below be written down at all.
    letI : MulAction Gal(L/K) ((baseChange K L E').obj Γ').E := mulActionE Γ'
    rintro ⟨a, x⟩ ⟨b, y⟩ ⟨σ, hσ⟩
    rw [Prod.mk.injEq] at hσ
    obtain ⟨rfl, rfl⟩ := hσ
    show a • x = (a * galRestrict K L E' σ⁻¹) • (galRestrict K L E' σ • x)
    rw [← mul_smul, map_inv, inv_mul_cancel_right])

/-- The counit `res_{E'/K} (E' ⊗_K Γ'_K) ⟶ Γ'_K` of
`prop:quiverrestrictionbasechangeadjunction`: `g ⊗ v ↦ g • v`. Compatibility with `s` and `t` is
`eq:stgaloisequivariance` for `Γ'_K`; `Gal(L/K)`-equivariance is `InducedSet.permHom_apply`
followed by `mul_smul`.

@census none (helper for `RQ2-1.07`)
-/
private def adjCounit :
    baseChange K L E' ⋙ restriction K L E' ⟶ 𝟭 (RationalQuiver K L) where
  app Γ' :=
    { toRQuiverHom :=
        { onV := adjCounitOnV K L E' Γ'
          onE := adjCounitOnE K L E' Γ'
          onV_source := by
            refine Quotient.ind ?_
            rintro ⟨g, x⟩
            exact (Γ'.source_smul g x).symm
          onV_target := by
            refine Quotient.ind ?_
            rintro ⟨g, x⟩
            exact (Γ'.target_smul g x).symm }
      equivariant_V := by
        letI : MulAction Gal(L/K) ((baseChange K L E').obj Γ').V := mulActionV Γ'
        refine fun σ => Quotient.ind ?_
        rintro ⟨g, v⟩
        exact mul_smul σ g v
      equivariant_E := by
        letI : MulAction Gal(L/K) ((baseChange K L E').obj Γ').E := mulActionE Γ'
        refine fun σ => Quotient.ind ?_
        rintro ⟨g, e⟩
        exact mul_smul σ g e }
  naturality Γ' Δ' ψ := by
    refine Hom.ext (RQuiver.Hom.ext ?_ ?_)
    · funext q
      refine Quotient.inductionOn q ?_
      rintro ⟨g, v⟩
      exact (ψ.equivariant_V g v).symm
    · funext q
      refine Quotient.inductionOn q ?_
      rintro ⟨g, e⟩
      exact (ψ.equivariant_E g e).symm

/-- **Proposition 1.7** (`prop:quiverrestrictionbasechangeadjunction`).
For any intermediate field `L/E'/K` with `E'/K` finite, any `E'`-rational quiver `Γ_{E'}` and any
`K`-rational quiver `Γ'_K`, there is a natural isomorphism

`Hom_{E'}(Γ_{E'}, E' ⊗_K Γ'_K) ≅ Hom_K(res_{E'/K} Γ_{E'}, Γ'_K)`,

i.e. restriction is left adjoint to base change.

@census    RQ2-1.07
@source    prop:quiverrestrictionbasechangeadjunction
@clauses   RQ2-1.07-Hs1, RQ2-1.07-H1, RQ2-1.07-H2, RQ2-1.07-H3, RQ2-1.07-C1, RQ2-1.07-C2
@imports   none
@divergence none. Clause `RQ2-1.07-H1` is the pair of arguments `E' : IntermediateField K L`,
`[FiniteDimensional K E']`; clauses `RQ2-1.07-H2` and `RQ2-1.07-H3` are the universal quantification
built into an `Adjunction`, whose `homEquiv` ranges over *all* objects of the two categories.
Clause `RQ2-1.07-C1` is `Adjunction.homEquiv`, in the direction
`(restriction.obj Γ_{E'} ⟶ Γ'_K) ≃ (Γ_{E'} ⟶ baseChange.obj Γ'_K)`, which is the source's
displayed isomorphism read right-to-left. Clause `RQ2-1.07-C2` (naturality — the stage plan's named
risk) is the `Adjunction` structure itself: mathlib's `Adjunction` is unit/counit data satisfying
the triangle identities, so the hom-set bijection it induces is natural in both variables by
construction and cannot be a mere bijection of hom-sets.

Discharged at G4 from the universal property of `InducedSet` (`Gal(L/K) ×_{Gal(L/E')} (−)` is
left adjoint to restriction of scalars along `galRestrict`), which is the source's own proof: the
unit is `v ↦ 1 ⊗ v` (`adjUnit`), the counit is `g ⊗ v ↦ g • v` (`adjCounit`), and the two triangle
identities reduce on representatives to `mul_one` and `one_smul`.
-/

def restriction_baseChange_adjunction :
    restriction K L E' ⊣ baseChange K L E' where
  unit := adjUnit K L E'
  counit := adjCounit K L E'
  left_triangle_components Γ := by
    -- `g ⊗ v ↦ g ⊗ (1 ⊗ v) ↦ g • (1 ⊗ v) = (g * 1) ⊗ v`.
    refine Hom.ext (RQuiver.Hom.ext ?_ ?_)
    · funext q
      refine Quotient.inductionOn q ?_
      rintro ⟨g, v⟩
      show InducedSet.mk (galRestrict K L E') (g * 1) v
        = InducedSet.mk (galRestrict K L E') g v
      rw [mul_one]
    · funext q
      refine Quotient.inductionOn q ?_
      rintro ⟨g, e⟩
      show InducedSet.mk (galRestrict K L E') (g * 1) e
        = InducedSet.mk (galRestrict K L E') g e
      rw [mul_one]
  right_triangle_components Γ' := by
    -- `v ↦ 1 ⊗ v ↦ 1 • v = v`.
    letI : MulAction Gal(L/K) ((baseChange K L E').obj Γ').V := mulActionV Γ'
    letI : MulAction Gal(L/K) ((baseChange K L E').obj Γ').E := mulActionE Γ'
    refine Hom.ext (RQuiver.Hom.ext ?_ ?_)
    · funext v
      exact one_smul _ v
    · funext e
      exact one_smul _ e

end RationalQuiver

end RationalQuivers
