module

public import RationalQuivers.Species.Rep.Decomposition
public import RationalQuivers.Quiver.Rep.Category

@[expose] public section

/-!
# The functor `F : Rep(Γ_K) → Rep(S(Γ_K))` (§2.6, census `RQ2-2.26`)

Formalizes `thm:quiveretalespeciesrepresentations`.

## Shape

`F` is data that exists only once `RQ2-2.24` is proved — its object map needs the descended
structure maps `f_{ij}`, and its morphism map needs `RQ2-2.25`'s `ψ_i`. So the row is stated
existentially with the functor and the identification of its object map **both named**, in the
shape stage S4 set for `RQ2-2.13-C5` (`speciesAntiEquivalence`) and stage S0 for `RQ2-1.13`. The G4
repair is a named `def` from which this `∃` is derived; at G2 the point is that the theorem is
about *this* assignment and not about some unnamed functor.

Clause `RQ2-2.26-C4` — functoriality — is stated explicitly even though it is `Functor.map_id` and
`Functor.map_comp` by construction, so that the clause has a mechanical discharger rather than
riding silently on the bundling.

## `H2` is a real hypothesis, not scaffolding

Clause `RQ2-2.26-H2` is the sentence that makes the object map land in `Rep(S(Γ_K))` at all: the
**continuous** semi-linear `G_{v_i}`-action on `M(v_i)` makes `W_i = M(v_i)^{G_{v_i}}` a vector
space over `L_i = L^{G_{v_i}}`, and Galois descent (`RQ2-1.13`) gives `W_i ⊗_{L_i} L ≅ M(v_i)`
(`eq:WitoMvi`). The census note records that continuity was named at this application site by the
D2 source edit precisely because it is the hypothesis `RQ2-1.13` needs. It is therefore the first
conjunct of the statement, not an aside — and it is what supplies the finite-dimensionality field
of `Species.Rep`.
-/

universe u

namespace RationalQuivers

open MulAction CategoryTheory

open scoped TensorProduct DirectSum

namespace RationalQuiver

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (Γ : RationalQuiver K L)

/-! ### `F`, constructed  (G4)

The object map is `RQ2-2.24`'s descent (`edgeDescentOf`), whose `Species.Rep` instance fields are
`Rep.moduleOp_W`/`moduleK_W`/`tower_W` — already in the tree — together with
`Rep.finite_op_vertexFixed` for `finite_W`, which is where `FDRep`'s finite-dimensionality enters.
The morphism map is `RQ2-2.25`'s `ψ_i` (`Rep.Hom.vertexFixedMap`), and its `comm` field is
**`RQ2-2.25-C4` itself** (`F_map_C4`) read through `Balanced.hom_ext` — so `F` consumes `RQ2-2.25`
exactly where the source says it does.  `map_id`/`map_comp` are componentwise `rfl`, because
`ψ_i` is a restriction and restriction is functorial.

@census none (G4 engine for `RQ2-2.26`)
-/

open scoped Classical in
/-- **`F` on objects**: `M_K ↦ ((M(v_i)^{G_{v_i}})_i, (f_{ij})_{ij})`. -/
noncomputable def FObj (M : FDRep Γ) : EtaleSpecies.Rep Γ.toSpecies where
  W i := ↥(M.toRep.vertexFixed (Γ.vertexRep i))
  addCommGroup_W i := inferInstanceAs (AddCommGroup ↥(M.toRep.vertexFixed (Γ.vertexRep i)))
  module_W i := M.toRep.moduleOp_W i
  module_K_W i := M.toRep.moduleK_W i
  isScalarTower_W i := M.toRep.tower_W i
  finite_W i := M.toRep.finite_op_vertexFixed (Γ.vertexRep i)
  f i j := edgeDescentOf M.toRep i j

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **`F` on morphisms**: `ψ ↦ (ψ_i)`, `RQ2-2.25`'s descended components. -/
noncomputable def FMap {M N : FDRep Γ} (φ : M ⟶ N) :
    Species.Rep.Hom (FObj Γ M) (FObj Γ N) where
  ψ i := φ.vertexFixedMap i
  comm i j := by
    refine Balanced.hom_ext fun w m => ?_
    show edgeDescentOf N.toRep i j (Balanced.mk (φ.vertexFixedMap i w) m)
      = φ.vertexFixedMap j (edgeDescentOf M.toRep i j (Balanced.mk w m))
    exact F_map_C4 φ (fun ε => EdgeChoice.choose Γ ε) _ _ _ _
      (isEdgeDescent_edgeDescentOf M.toRep i j) (isEdgeDescent_edgeDescentOf N.toRep i j) w m

open scoped Classical in
/-- **The functor `F : Rep(Γ_K) → Rep(S(Γ_K))`** (census `RQ2-2.26`). -/
noncomputable def FFunctor :
    CategoryTheory.Functor (FDRep Γ) (EtaleSpecies.Rep Γ.toSpecies) where
  obj := FObj Γ
  map φ := FMap Γ φ
  map_id M := by
    refine Species.Rep.Hom.ext ?_
    funext i
    refine LinearMap.ext fun w => Subtype.ext ?_
    rfl
  map_comp φ χ := by
    refine Species.Rep.Hom.ext ?_
    funext i
    refine LinearMap.ext fun w => Subtype.ext ?_
    rfl

/-! ### `RQ2-2.29`'s `F`-side hypotheses, discharged for `FFunctor`  (G5, finding `V-S5G4-3`)

`RQ2-2.29` is universal over `F` and `H` and their characterising hypotheses.  These two theorems
are `hF1` and `hF2` of that bundle, stated for **this tree's own `F`** at the identity
identification `e = LinearEquiv.refl`, so that `species_equivalence` can be applied to `FFunctor`
without re-opening `F_functor`'s proof.  They are literally the two bullets of that proof, given
names.

@census none (G4/G5 engine for `RQ2-2.29`)
-/

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **`RQ2-2.29`'s hypothesis `hF1` for `FFunctor`** (= `RQ2-2.26-C1` at `e = refl`): `F`'s structure
maps are the descents `f_{ij}`, for any `IsEdgeDescent` witness.
@census none (clause witness for `RQ2-2.26-C1`; discharges `RQ2-2.29`'s `hF1`) -/
theorem FFunctor_hF1 (M : FDRep Γ) (i j : Γ.VertexOrbit)
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL M.toRep i j ≃ₗ[L] wiiMjLpreRhs M.toRep ch)
    (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.toRep.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep j)))
    (hf : IsEdgeDescent M.toRep ch e₀ f)
    (w : ((FFunctor Γ).obj M).W i) (m : Γ.toSpecies.M i j) :
    ((FFunctor Γ).obj M).f i j (Balanced.mk w m) = f (Balanced.mk w m) := by
  show edgeDescentOf M.toRep i j (Balanced.mk w m) = f (Balanced.mk w m)
  rw [edgeDescentOf_eq M.toRep ch e₀ f hf]

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **`RQ2-2.29`'s hypothesis `hF2` for `FFunctor`** (= `RQ2-2.26-C2` at `e = refl`): `F`'s morphism
map is `RQ2-2.25`'s `ψ_i`.
@census none (clause witness for `RQ2-2.26-C2`; discharges `RQ2-2.29`'s `hF2`) -/
theorem FFunctor_hF2 (M N : FDRep Γ) (φ : M ⟶ N)
    (ψ' : ∀ i : Γ.VertexOrbit,
      ↥(M.toRep.vertexFixed (Γ.vertexRep i))
        →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(N.toRep.vertexFixed (Γ.vertexRep i)))
    (hψ' : ∀ (i : Γ.VertexOrbit) (m : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
      ((ψ' i m : N.toRep.M (Γ.vertexRep i)))
        = φ.ψ (Γ.vertexRep i) (m : M.toRep.M (Γ.vertexRep i)))
    (i : Γ.VertexOrbit) (w : ((FFunctor Γ).obj M).W i) :
    ((FFunctor Γ).map φ).ψ i w = ψ' i w :=
  Subtype.ext (hψ' i w).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- **Theorem `thm:quiveretalespeciesrepresentations`** (census `RQ2-2.26`).

The assignments

* `M_K ↦ ((M(v_i)^{G_{v_i}})_{i ∈ I}, (f_{ij})_{i,j ∈ I})` on objects (clause `RQ2-2.26-C1`) and
* `((ψ_v)_v : M_K → N_K) ↦ (ψ_i)_{i ∈ I}` on morphisms (clause `RQ2-2.26-C2`)

define a **functor** `Rep(Γ_K) → Rep(S(Γ_K))` (clause `RQ2-2.26-C3`), and identities and
composition are preserved (clause `RQ2-2.26-C4`).  The first conjunct is clause `RQ2-2.26-H2`,
`eq:WitoMvi`; the hypotheses `RQ2-2.24` and `RQ2-2.25` are clause `RQ2-2.26-H1` and are consumed
through `IsEdgeDescent` and through the characterisation of `ψ_i`.

@census    RQ2-2.26
@source    thm:quiveretalespeciesrepresentations
@clauses   RQ2-2.26-H1, RQ2-2.26-H2, RQ2-2.26-C1, RQ2-2.26-C2, RQ2-2.26-C3, RQ2-2.26-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION on clauses `RQ2-2.26-C1` and `RQ2-2.26-C2`.

Both are rendered **up to the named identification `e`** of `(F.obj M).W i` with
`M(v_i)^{G_{v_i}}`, rather than as definitional equalities of the functor's fields.  `F` is
existential — its object map is built from `RQ2-2.24`'s descent, which is itself existential at G2 —
so there is no term to say "`(F.obj M).W i` **is** `M(v_i)^{G_{v_i}}`" about; what the statement
says instead is that `e` exists and that under it the structure maps of `F.obj M` are exactly the
descents (`C1`) and the components of `F.map ψ` are exactly `RQ2-2.25`'s `ψ_i` (`C2`).  That pins
both assignments, which is what the clauses assert; a bare `F.IsEquivalence`-style claim, or an `∃ F`
with no `e`, would not.  This is the standard stage S4's finding **F-1** established for
`RQ2-2.13-C5` and it is applied here for the same reason.

`C1`/`C2` are stated on **pure tensors** and componentwise respectively, so that no
`Balanced.map` and no transported family has to appear in a census-carrying signature;
`Species.Rep.Hom.comm_mk` is the lemma that the pure-tensor form is equivalent to the bundled
square.

Proof plan (G4): the object map is `RQ2-2.24`'s `f` for each `(i,j)`, with `Species.Rep`'s
`finite_W` supplied by `H2` (Galois descent turns finite-dimensionality of `M(v_i)` over `L` into
finite-dimensionality of `W_i` over `L_i`); the morphism map is `RQ2-2.25`'s `ψ'`; `map_id` and
`map_comp` are componentwise from `Rep.Hom.id`/`Rep.Hom.comp`, since `ψ_i` is the restriction of
`ψ_{v_i}` and restriction is functorial.
-/
theorem F_functor :
    -- `H2` (`eq:WitoMvi`): Galois descent identifies `W_i ⊗_{L_i} L` with `M(v_i)`
    (∀ (M : FDRep Γ) (i : Γ.VertexOrbit),
      Nonempty (Balanced K (Γ.toSpecies.L i) L L ↥(M.toRep.vertexFixed (Γ.vertexRep i))
        ≃ₗ[L] M.toRep.M (Γ.vertexRep i))) ∧
    ∃ (F : CategoryTheory.Functor (FDRep Γ) (EtaleSpecies.Rep Γ.toSpecies))
      (e : ∀ (M : FDRep Γ) (i : Γ.VertexOrbit),
        (F.obj M).W i ≃ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
      -- `C1`: on objects, the structure maps are the descents `f_{ij}` of `RQ2-2.24`
      (∀ (M : FDRep Γ) (i j : Γ.VertexOrbit)
          (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
          (e₀ : wiiMjL M.toRep i j ≃ₗ[L] wiiMjLpreRhs M.toRep ch)
          (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j
                  ↥(M.toRep.vertexFixed (Γ.vertexRep i))
                →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep j))),
        IsEdgeDescent M.toRep ch e₀ f →
        ∀ (w : (F.obj M).W i) (m : Γ.toSpecies.M i j),
          e M j ((F.obj M).f i j (Balanced.mk w m)) = f (Balanced.mk (e M i w) m)) ∧
      -- `C2`: on morphisms, the components are `RQ2-2.25`'s `ψ_i`
      (∀ (M N : FDRep Γ) (φ : M ⟶ N)
          (ψ' : ∀ i : Γ.VertexOrbit,
            ↥(M.toRep.vertexFixed (Γ.vertexRep i))
              →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(N.toRep.vertexFixed (Γ.vertexRep i))),
        (∀ (i : Γ.VertexOrbit) (m : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
          ((ψ' i m : N.toRep.M (Γ.vertexRep i)))
            = φ.ψ (Γ.vertexRep i) (m : M.toRep.M (Γ.vertexRep i))) →
        ∀ (i : Γ.VertexOrbit) (w : (F.obj M).W i),
          e N i ((F.map φ).ψ i w) = ψ' i (e M i w)) ∧
      -- `C4`: functoriality
      ((∀ M : FDRep Γ, F.map (𝟙 M) = 𝟙 (F.obj M)) ∧
        ∀ (M N P : FDRep Γ) (φ : M ⟶ N) (χ : N ⟶ P),
          F.map (φ ≫ χ) = F.map φ ≫ F.map χ) := by
  classical
  refine ⟨fun M i => ⟨vertexDescentBalanced M.toRep i⟩,
    FFunctor Γ, fun _ _ => LinearEquiv.refl _ _, ?_, ?_,
    (FFunctor Γ).map_id, fun M N P φ χ => (FFunctor Γ).map_comp φ χ⟩
  · intro M i j ch e₀ f hf w m
    show edgeDescentOf M.toRep i j (Balanced.mk w m) = f (Balanced.mk w m)
    rw [edgeDescentOf_eq M.toRep ch e₀ f hf]
  · intro M N φ ψ' hψ' i w
    exact Subtype.ext (hψ' i w).symm

end RationalQuiver

end RationalQuivers
