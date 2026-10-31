module

public import RationalQuivers.Quiver.Hom

@[expose] public section

/-!
# Transport of a rational structure along a homomorphism of Galois groups

Auxiliary module for §1.2 of `latex/rational_quivers.tex`. No census row of its own: it isolates
the single construction that both `def:quiverbasechange` (`RQ2-1.05`, restriction of `ρ` to
`Gal(L/E')`) and the inflation remark (`RQ2-1.20`, pullback of `ρ` along
`Gal(K^sep/K) ↠ Gal(L/K)`) are instances of.

## Main definitions / results
* `RationalQuivers.RationalQuiver.comap` — keep the quiver, precompose `ρ` with a **continuous**
  group homomorphism of Galois groups. Continuity of the homomorphism is exactly what preserves the
  continuity condition of `def:rationalquivers` (clauses `RQ2-1.02-C2`, `RQ2-1.02-C3`), and hence
  what makes clauses `RQ2-1.05-C2` and `RQ2-1.06-C5` true.
* `RationalQuivers.RationalQuiver.comapFunctor` — the same construction on morphisms.
-/

universe u

namespace RationalQuivers

open CategoryTheory

variable {K L K' L' : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
variable [Field K'] [Field L'] [Algebra K' L'] [IsGalois K' L']

namespace RationalQuiver

/-- Precompose the rational structure `ρ` of a `K`-rational quiver with a continuous homomorphism
`f : Gal(L'/K') → Gal(L/K)`, keeping the underlying classical quiver. Continuity of `f` is what
makes the two smoothness conditions of `def:rationalquivers` survive.

@census none (helper: the common core of `RQ2-1.05` and `RQ2-1.20`)
-/
def comap (f : Gal(L'/K') →* Gal(L/K)) (hf : Continuous f) (Γ : RationalQuiver K L) :
    RationalQuiver K' L' where
  toRQuiver := Γ.toRQuiver
  ρ := Γ.ρ.comp f
  smooth_V := Γ.smooth_V.comp f hf
  smooth_E := Γ.smooth_E.comp f hf

/-- `comap` keeps the underlying classical quiver. @census none (helper) -/
@[simp]
lemma comap_toRQuiver (f : Gal(L'/K') →* Gal(L/K)) (hf : Continuous f) (Γ : RationalQuiver K L) :
    (Γ.comap f hf).toRQuiver = Γ.toRQuiver := rfl

/-- `comap` precomposes the rational structure with `f`. @census none (helper) -/
@[simp]
lemma comap_ρ (f : Gal(L'/K') →* Gal(L/K)) (hf : Continuous f) (Γ : RationalQuiver K L)
    (σ : Gal(L'/K')) : (Γ.comap f hf).ρ σ = Γ.ρ (f σ) := rfl

/-- `comap` as a functor between the categories of rational quivers.

@census none (helper)
-/
def comapFunctor (f : Gal(L'/K') →* Gal(L/K)) (hf : Continuous f) :
    RationalQuiver K L ⥤ RationalQuiver K' L' where
  obj Γ := Γ.comap f hf
  map {_ _} φ :=
    { toRQuiverHom := φ.toRQuiverHom
      equivariant_V := fun σ v => φ.equivariant_V (f σ) v
      equivariant_E := fun σ e => φ.equivariant_E (f σ) e }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The object part of `comapFunctor` is `comap`. @census none (helper) -/
@[simp]
lemma comapFunctor_obj (f : Gal(L'/K') →* Gal(L/K)) (hf : Continuous f) (Γ : RationalQuiver K L) :
    (comapFunctor f hf).obj Γ = Γ.comap f hf := rfl

/-- `comapFunctor` keeps the underlying quiver morphism. @census none (helper) -/
@[simp]
lemma comapFunctor_map_toRQuiverHom (f : Gal(L'/K') →* Gal(L/K)) (hf : Continuous f)
    {Γ Γ' : RationalQuiver K L} (φ : Γ ⟶ Γ') :
    ((comapFunctor f hf).map φ).toRQuiverHom = φ.toRQuiverHom := rfl

end RationalQuiver

end RationalQuivers
