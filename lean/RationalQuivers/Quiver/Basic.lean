module

public import Mathlib.CategoryTheory.Category.Quiv
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.MulAction

@[expose] public section

/-!
# Classical quivers and `K`-rational structures on them

Formalizes the first half of §1.2 of `latex/rational_quivers.tex`
(census `RQ2-1.01`, `RQ2-1.02`, `RQ2-1.03`).

## Main definitions / results
* `RationalQuivers.RQuiver` — Gabriel's classical quiver `Γ = (V,E,s,t)` with `V`, `E` finite
  (census `RQ2-1.01`; the definition is unlabelled in the source).
* `RationalQuivers.RQuiver.instCategory` — the category of classical quivers, whose isomorphisms
  give `RQuiver.Aut Γ = Aut(Γ)`.
* `RationalQuivers.RQuiver.toQuiv` — the **bridge to mathlib** (design decision D4): the functor
  from our edge-set-indexed quivers to mathlib's `Hom`-indexed `CategoryTheory.Quiv`.
* `RationalQuivers.IsSmooth` — continuity of a permutation action of a topological group on a
  discrete set, in the open-stabilizer form that `census/NOTATION.md` §12 prescribes.
* `RationalQuivers.RationalQuiver` — Definition `def:rationalquivers` (census `RQ2-1.02`).
* `RationalQuivers.RationalQuiver.IsSplit` — Definition `def:splitrationalquivers`
  (census `RQ2-1.03`).

## Implementation notes

**D4.** mathlib's `Quiver` class indexes arrows by their endpoints (`Hom : V → V → Sort v`) and has
no edge set. The paper's Galois action *permutes the edge set* `E` (`ρ_E : Gal(L/K) → Sym(E)`), and
`S(Γ_K)` in §2.2 is built from the `Gal`-orbits and stabilizers **of edges**. Both are statements
about `E` as a set, so `E` must be a carrier, not an index. We therefore define `RQuiver` as our own
bundled quadruple and *build the bridge* `RQuiver.toQuiv` to mathlib's view; see
`workflow/ledger/MATHLIB-DECISIONS.tsv` rows `MD-S1-01`, `MD-S1-02`.

**Continuity.** The source requires the induced actions on `V` and `E` to be continuous for the
discrete topologies. mathlib's `continuousSMul_iff_stabilizer_isOpen` shows this is equivalent to
"every point has open stabilizer" for a topological group acting on a discrete space; that is the
form every application site of the paper uses (`census/NOTATION.md` §12), so `IsSmooth` is stated
that way and `IsSmooth.iff_continuousSMul` records that it *is* mathlib's `ContinuousSMul`.
-/

universe u

namespace RationalQuivers

open CategoryTheory

/-! ### Classical quivers -/

/-- **Definition** (Gabriel; unlabelled in the source, census `RQ2-1.01`).
A *(classical) quiver* is a quadruple `Γ = (V, E, s, t)` consisting of a finite set of vertices
`V`, a finite set of edges `E`, and two maps `s, t : E → V` assigning to each edge `e ∈ E` its
source `s e ∈ V` and its target `t e ∈ V`.

@census    RQ2-1.01
@source    def:quiver
@clauses   RQ2-1.01-H1, RQ2-1.01-H2, RQ2-1.01-C1, RQ2-1.01-C2, RQ2-1.01-C3
@imports   none
@divergence none. The quadruple is bundled as a structure rather than presented as four separate
parameters; clause `RQ2-1.01-C1` records bundling as a presentation choice
(`if_missing = JUSTIFIED_REFORMULATION`). Finiteness of `V` and `E` (clauses `RQ2-1.01-H1`,
`RQ2-1.01-H2`) is carried as the two `Finite` fields, registered as instances below, so it can never
be dropped by a downstream construction.
-/
structure RQuiver : Type (u + 1) where
  /-- The (finite) set of vertices. -/
  V : Type u
  /-- The (finite) set of edges. -/
  E : Type u
  /-- The source of an edge. -/
  source : E → V
  /-- The target of an edge. -/
  target : E → V
  /-- Clause `RQ2-1.01-H1`: the vertex set is finite. -/
  finite_V : Finite V
  /-- Clause `RQ2-1.01-H2`: the edge set is finite. -/
  finite_E : Finite E

attribute [instance] RQuiver.finite_V RQuiver.finite_E

namespace RQuiver

/-- A homomorphism of classical quivers: a map on vertices and a map on edges commuting with
`source` and `target`. This is the "homomorphism of the underlying quivers" of clause
`RQ2-1.04-C1`; the Galois-equivariance half of `def:rationalquiverhom` is added in
`RationalQuivers.RationalQuiver.Hom`.

@census none (helper: the classical-quiver half of `RQ2-1.04`)
-/
@[ext]
structure Hom (Γ Γ' : RQuiver.{u}) : Type u where
  /-- The action on vertices. -/
  onV : Γ.V → Γ'.V
  /-- The action on edges. -/
  onE : Γ.E → Γ'.E
  /-- Compatibility with the source maps. -/
  onV_source : ∀ e, onV (Γ.source e) = Γ'.source (onE e)
  /-- Compatibility with the target maps. -/
  onV_target : ∀ e, onV (Γ.target e) = Γ'.target (onE e)

/-- The identity homomorphism of a classical quiver.

@census none (helper)
-/
protected def Hom.id (Γ : RQuiver.{u}) : Hom Γ Γ where
  onV := _root_.id
  onE := _root_.id
  onV_source _ := rfl
  onV_target _ := rfl

/-- Composition of homomorphisms of classical quivers.

@census none (helper)
-/
protected def Hom.comp {Γ Γ' Γ'' : RQuiver.{u}} (f : Hom Γ Γ') (g : Hom Γ' Γ'') : Hom Γ Γ'' where
  onV := g.onV ∘ f.onV
  onE := g.onE ∘ f.onE
  onV_source e := by
    simp only [Function.comp_apply, f.onV_source e, g.onV_source (f.onE e)]
  onV_target e := by
    simp only [Function.comp_apply, f.onV_target e, g.onV_target (f.onE e)]

/-- The category of classical quivers. `Aut Γ` in this category is the paper's `Aut(Γ)`.

@census none (helper: supplies `Aut(Γ)` for `RQ2-1.02` and the ambient category for `RQ2-1.04`)
-/
instance instCategory : Category.{u, u + 1} RQuiver.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The identity morphism acts as the identity on vertices. @census none (helper) -/
@[simp] lemma id_onV (Γ : RQuiver.{u}) : Hom.onV (𝟙 Γ) = _root_.id := rfl

/-- The identity morphism acts as the identity on edges. @census none (helper) -/
@[simp] lemma id_onE (Γ : RQuiver.{u}) : Hom.onE (𝟙 Γ) = _root_.id := rfl

/-- Composition acts on vertices by composition. @census none (helper) -/
@[simp] lemma comp_onV {Γ Γ' Γ'' : RQuiver.{u}} (f : Γ ⟶ Γ') (g : Γ' ⟶ Γ'') :
    (f ≫ g).onV = g.onV ∘ f.onV := rfl

/-- Composition acts on edges by composition. @census none (helper) -/
@[simp] lemma comp_onE {Γ Γ' Γ'' : RQuiver.{u}} (f : Γ ⟶ Γ') (g : Γ' ⟶ Γ'') :
    (f ≫ g).onE = g.onE ∘ f.onE := rfl

/-- `Aut(Γ)`, the automorphism group of a classical quiver: mathlib's `CategoryTheory.Aut` in the
category `RQuiver`. It carries mathlib's `Group` structure, whose multiplication is in
`Function.comp` order, so a `MonoidHom` into it is a genuine *left* action.

@census none (helper: the codomain of `ρ` in `RQ2-1.02`)
-/
abbrev Aut (Γ : RQuiver.{u}) : Type u := CategoryTheory.Aut Γ

/-! Port v4.35 (`workflow/v2/release/PORT-V435.md`): mathlib's `CategoryTheory.Aut X` changed from
the abbreviation `X ≅ X` to a one-field structure (`Aut.of`/`Aut.asIso`). The four accessors below
restore, for `Aut Γ`, the projections `a.hom`, `a.inv`, `a.hom_inv_id`, `a.inv_hom_id` that the
old definition provided; each is by definition the corresponding projection of `a.asIso`. -/

/-- The underlying morphism of an automorphism (`= a.asIso.hom`). Port v4.35.

@census none (helper)
-/
abbrev Aut.hom {Γ : RQuiver.{u}} (a : Aut Γ) : Γ ⟶ Γ := a.asIso.hom

/-- The underlying inverse morphism of an automorphism (`= a.asIso.inv`). Port v4.35.

@census none (helper)
-/
abbrev Aut.inv {Γ : RQuiver.{u}} (a : Aut Γ) : Γ ⟶ Γ := a.asIso.inv

/-- `a.hom ≫ a.inv = 𝟙 Γ`. Port v4.35.

@census none (helper)
-/
@[reassoc]
theorem Aut.hom_inv_id {Γ : RQuiver.{u}} (a : Aut Γ) : a.hom ≫ a.inv = 𝟙 Γ :=
  a.asIso.hom_inv_id

/-- `a.inv ≫ a.hom = 𝟙 Γ`. Port v4.35.

@census none (helper)
-/
@[reassoc]
theorem Aut.inv_hom_id {Γ : RQuiver.{u}} (a : Aut Γ) : a.inv ≫ a.hom = 𝟙 Γ :=
  a.asIso.inv_hom_id

/-- Two automorphisms with the same underlying morphism are equal. Port v4.35.

@census none (helper)
-/
theorem Aut.ext {Γ : RQuiver.{u}} {a b : Aut Γ} (h : a.hom = b.hom) : a = b :=
  CategoryTheory.Aut.ext (CategoryTheory.Iso.ext h)

/-- The permutation of the vertex set underlying an automorphism of `Γ`.

@census none (helper)
-/
@[simps]
def Aut.toPermV (Γ : RQuiver.{u}) : Aut Γ →* Equiv.Perm Γ.V where
  toFun a :=
    { toFun := Aut.hom a |>.onV
      invFun := Aut.inv a |>.onV
      left_inv := fun v => congrFun (congrArg Hom.onV (Aut.hom_inv_id a)) v
      right_inv := fun v => congrFun (congrArg Hom.onV (Aut.inv_hom_id a)) v }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The permutation of the edge set underlying an automorphism of `Γ`.

@census none (helper)
-/
@[simps]
def Aut.toPermE (Γ : RQuiver.{u}) : Aut Γ →* Equiv.Perm Γ.E where
  toFun a :=
    { toFun := Aut.hom a |>.onE
      invFun := Aut.inv a |>.onE
      left_inv := fun e => congrFun (congrArg Hom.onE (Aut.hom_inv_id a)) e
      right_inv := fun e => congrFun (congrArg Hom.onE (Aut.inv_hom_id a)) e }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Assembling `Aut(Γ)` from actions on `V` and on `E`: a pair of permutation representations of a
group `G` on `V` and on `E` for which `s` and `t` are equivariant is exactly a homomorphism
`G →* Aut(Γ)`. This is `eq:stgaloisequivariance` read as a construction; it is how the rational
structure of `def:quiverrestriction` (`RQ2-1.06`) is built.

@census none (helper)
-/
def autOfAction (Γ : RQuiver.{u}) {G : Type*} [Group G]
    (aV : G →* Equiv.Perm Γ.V) (aE : G →* Equiv.Perm Γ.E)
    (hs : ∀ (g : G) (e : Γ.E), Γ.source (aE g e) = aV g (Γ.source e))
    (ht : ∀ (g : G) (e : Γ.E), Γ.target (aE g e) = aV g (Γ.target e)) :
    G →* Aut Γ where
  toFun g := .of
    { hom :=
        { onV := aV g
          onE := aE g
          onV_source := fun e => (hs g e).symm
          onV_target := fun e => (ht g e).symm }
      inv :=
        { onV := (aV g).symm
          onE := (aE g).symm
          onV_source := fun e => (aV g).injective (by
            rw [Equiv.apply_symm_apply, ← hs g ((aE g).symm e), Equiv.apply_symm_apply])
          onV_target := fun e => (aV g).injective (by
            rw [Equiv.apply_symm_apply, ← ht g ((aE g).symm e), Equiv.apply_symm_apply]) }
      hom_inv_id := by
        refine Hom.ext ?_ ?_ <;> funext x <;> simp
      inv_hom_id := by
        refine Hom.ext ?_ ?_ <;> funext x <;> simp }
  map_one' := by
    refine CategoryTheory.Aut.ext (CategoryTheory.Iso.ext (Hom.ext ?_ ?_)) <;> funext x <;> simp <;> rfl
  map_mul' _ _ := by
    refine CategoryTheory.Aut.ext (CategoryTheory.Iso.ext (Hom.ext ?_ ?_)) <;> funext x <;> simp <;> rfl

/-! ### The bridge to mathlib's `Quiver` (design decision D4) -/

/-- **D4 bridge.** The `Hom`-indexed view of a classical quiver: an arrow `a ⟶ b` is an edge with
source `a` and target `b`. This is mathlib's `Quiver` class, so every mathlib construction on
quivers (paths, prefunctors, the free category `Quiv ⥤ Cat`, …) applies to `Γ.V` unchanged.

@census none (helper: D4 bridge, `ledger/MATHLIB-DECISIONS.tsv` row MD-S1-01)
-/
instance instQuiverV (Γ : RQuiver.{u}) : _root_.Quiver Γ.V where
  Hom a b := {e : Γ.E // Γ.source e = a ∧ Γ.target e = b}

/-- **D4 bridge.** The edge set is recovered from the `Hom`-indexed view: `E ≃ Σ (a b : V), (a ⟶ b)`.
This is what makes the bridge lossless, and hence what makes it legitimate to state the paper's
theorems about `RQuiver` rather than about mathlib's `Quiver`.

@census none (helper: D4 bridge)
-/
def edgeEquiv (Γ : RQuiver.{u}) : Γ.E ≃ Σ a : Γ.V, Σ b : Γ.V, (a ⟶ b) where
  toFun e := ⟨Γ.source e, Γ.target e, e, rfl, rfl⟩
  invFun x := x.2.2.1
  left_inv _ := rfl
  right_inv := by rintro ⟨a, b, e, rfl, rfl⟩; rfl

/-- **D4 bridge.** A homomorphism of classical quivers induces a mathlib `Prefunctor`.

@census none (helper: D4 bridge)
-/
def toPrefunctor {Γ Γ' : RQuiver.{u}} (f : Γ ⟶ Γ') : Γ.V ⥤q Γ'.V where
  obj := f.onV
  map {_ _} e :=
    ⟨f.onE e.1, (f.onV_source e.1).symm.trans (congrArg f.onV e.2.1),
      (f.onV_target e.1).symm.trans (congrArg f.onV e.2.2)⟩

/-- **D4 bridge (design decision D4).** The functor from our edge-set-indexed quivers to mathlib's
`Hom`-indexed category of quivers `CategoryTheory.Quiv`. Downstream category theory may therefore
be done in mathlib's world.

@census none (helper: D4 bridge, `ledger/MATHLIB-DECISIONS.tsv` row MD-S1-02)
-/
def toQuiv : RQuiver.{u} ⥤ Quiv.{u, u} where
  obj Γ := Quiv.of Γ.V
  map f := toPrefunctor f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **D4 bridge.** The bridge functor is faithful.

@census none (helper: D4 bridge; evidence that the bridge loses nothing)
-/
instance toQuiv_faithful : toQuiv.Faithful where
  map_injective {Γ Γ'} f g h := by
    obtain ⟨fV, fE, hf1, hf2⟩ := f
    obtain ⟨gV, gE, hg1, hg2⟩ := g
    have hV : fV = gV := congrArg Prefunctor.obj h
    subst hV
    refine Hom.ext rfl ?_
    funext e
    exact congrArg
      (fun F : Quiv.of Γ.V ⟶ Quiv.of Γ'.V =>
        (F.map (show Γ.source e ⟶ Γ.target e from ⟨e, rfl, rfl⟩)).1) h

/-- **D4 bridge.** The bridge functor is full.

@census none (helper: D4 bridge; evidence that the bridge loses nothing)
-/
instance toQuiv_full : toQuiv.Full where
  map_surjective {Γ Γ'} F := by
    refine ⟨{ onV := F.obj
              onE := fun e => (F.map (show Γ.source e ⟶ Γ.target e from ⟨e, rfl, rfl⟩)).1
              onV_source := fun e =>
                ((F.map (show Γ.source e ⟶ Γ.target e from ⟨e, rfl, rfl⟩)).2.1).symm
              onV_target := fun e =>
                ((F.map (show Γ.source e ⟶ Γ.target e from ⟨e, rfl, rfl⟩)).2.2).symm }, ?_⟩
    obtain ⟨Fobj, Fmap⟩ := F
    refine congrArg (Prefunctor.mk Fobj) ?_
    funext a b arrow
    obtain ⟨e, rfl, rfl⟩ := arrow
    rfl

end RQuiver

/-! ### Continuity of an action on a discrete set -/

/-- An action of a topological group `G` on a set `X` through `ρ : G →* Equiv.Perm X` is *smooth*
if every point of `X` has open stabilizer. For `X` carrying the discrete topology this is exactly
continuity of the action map `G × X → X` (`IsSmooth.iff_continuousSMul`), which is the condition
required in `def:rationalquivers`; `census/NOTATION.md` §12 prescribes the open-stabilizer form
because that is the form every application site of the paper uses. For finite `G` (in particular
for finite `L/K`) the condition is vacuous.

@census none (helper: the continuity condition of `RQ2-1.02`, clauses C2 and C3)
-/
def IsSmooth {G X : Type*} [Group G] [TopologicalSpace G] (ρ : G →* Equiv.Perm X) : Prop :=
  ∀ x : X, IsOpen {g : G | ρ g x = x}

namespace IsSmooth

variable {G X : Type*} [Group G] [TopologicalSpace G]

/-- `IsSmooth ρ` is mathlib's `ContinuousSMul` for the induced action on the discrete space `X`.
Recorded so that our continuity condition is *mathlib's* notion and not a private restatement (R2).

@census none (helper)
-/
theorem iff_continuousSMul [IsTopologicalGroup G] (ρ : G →* Equiv.Perm X) :
    IsSmooth ρ ↔
      @ContinuousSMul G X (MulAction.compHom X ρ).toSMul ‹TopologicalSpace G› ⊥ := by
  letI : MulAction G X := MulAction.compHom X ρ
  letI : TopologicalSpace X := ⊥
  haveI : DiscreteTopology X := ⟨rfl⟩
  exact (continuousSMul_iff_stabilizer_isOpen (M := G) (X := X)).symm

/-- Smoothness is inherited along a continuous group homomorphism. This is the mechanism behind
base change (`RQ2-1.05`) and behind the inflation to `Gal(K^sep/K)` of `RQ2-1.20`.

@census none (helper)
-/
theorem comp {H : Type*} [Group H] [TopologicalSpace H] {ρ : G →* Equiv.Perm X}
    (hρ : IsSmooth ρ) (f : H →* G) (hf : Continuous f) : IsSmooth (ρ.comp f) :=
  fun x => (hρ x).preimage hf

/-- A smooth action of a group with the discrete topology; in particular every action of a finite
Galois group is smooth. Used for the split rational quivers of `RQ2-1.03` and for the concrete
models of `Quiver/Models.lean`.

@census none (helper)
-/
theorem of_discreteTopology [DiscreteTopology G] (ρ : G →* Equiv.Perm X) : IsSmooth ρ :=
  fun _ => isOpen_discrete _

end IsSmooth

/-! ### `K`-rational quivers -/

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [galoisLK : IsGalois K L]

/-- **Definition 1.2** (`def:rationalquivers`).
An *(étale) `K`-rational structure* on a classical quiver `Γ = (V,E,s,t)` is a group homomorphism
`ρ : Gal(L/K) → Aut(Γ)`, for a Galois extension `L/K` (finite or infinite), such that the induced
actions of `Gal(L/K)` on `V` and on `E` are continuous when `V` and `E` are regarded as discrete
sets. We write `Γ_K := (Γ, ρ)` and call it an *(étale) quiver over `K`*.

That `ρ` lands in `Aut(Γ)` — rather than merely in `Sym(V) × Sym(E)` — is exactly the
`Gal(L/K)`-equivariance `s(σe) = σ s(e)`, `t(σe) = σ t(e)` of `eq:stgaloisequivariance`
(clause `RQ2-1.02-C4`), which is part of the data of `RQuiver.Hom`.

@census    RQ2-1.02
@source    def:rationalquivers
@clauses   RQ2-1.02-H1, RQ2-1.02-H2, RQ2-1.02-C1, RQ2-1.02-C2, RQ2-1.02-C3, RQ2-1.02-C4, RQ2-1.02-C5
@imports   none
@divergence none. `Gal(L/K)` is mathlib's `L ≃ₐ[K] L` with the Krull topology
(`krullTopology`), which is the profinite topology and is discrete for finite `L/K`, so clause
`RQ2-1.02-H1` ("finite or infinite") is met without a finiteness hypothesis. Clauses `RQ2-1.02-C2`
and `RQ2-1.02-C3` are the two `IsSmooth` fields, equivalent to mathlib's `ContinuousSMul` for the
discrete topology by `IsSmooth.iff_continuousSMul`. Clause `RQ2-1.02-C5` is the naming of the pair,
carried by the structure itself.

**r6 delta (`census-v1.3`), clause `RQ2-1.02-H1`.** `L/K` Galois is carried as the *field*
`galois`, not as a header binder. Lean prunes an instance binder a header does not use, and no
other field below mentions the Galois structure, so as a binder it was silently dropped and this
structure elaborated as if `L/K` were an arbitrary algebra. (`include galoisLK in` was tried first
and measured not to repair it: the elaborated constant type was unchanged.) As a field the
hypothesis is not merely visible but *structural* — no `RationalQuiver K L` can be built without a
proof of `IsGalois K L` — so every declaration taking or producing one, namely `Hom` (`RQ2-1.04`),
`IsSplit` (`RQ2-1.03`), `RelationsCompat` (`RQ2-1.19`), `ofAction` and `comap`, carries it too, and
no later edit or `omit` can drop it.
**S1 G4 finding C-1 (read this before using the field).** "Carried as an instance-implicit field"
must NOT be read as "found by `inferInstance`". The field is available as a **term**, `Γ.galois`,
and not by synthesis: `example (Γ : RationalQuiver K L) : IsGalois K L := inferInstance` fails.
The correction the G4 report proposed first — `attribute [instance] RationalQuiver.galois` — is
**not available**: Lean rejects it, because the projection's major argument `self` is explicit and
does not occur in the return type `IsGalois K L`, so typeclass synthesis has nothing to key on
(measured 2026-08-29 on merge: *"This instance has 1 argument that cannot be inferred using
typeclass synthesis ... argument 6: `(self : RationalQuiver K L)`"*). Making the projection an
instance would require `RationalQuiver` to be a class, which is a statement change and is not
taken here. A later stage that needs `IsGalois K L` from a `RationalQuiver K L` argument must
therefore write `haveI := Γ.galois` by hand; a proof that forgets to will silently re-assume the
hypothesis as a binder, which is exactly how the r6 defect arose. The same applies to
`GaloisSet.galois`.
-/
structure RationalQuiver : Type (u + 1) where
  /-- Clause `RQ2-1.02-H1`: `L/K` is a Galois extension (finite or infinite). Carried as an
  instance-implicit field so that it cannot be pruned; see the r6 note above. -/
  [galois : IsGalois K L]
  /-- The underlying classical quiver `Γ = (V,E,s,t)` (clause `RQ2-1.02-H2`). -/
  toRQuiver : RQuiver.{u}
  /-- Clause `RQ2-1.02-C1`: the rational structure, a group homomorphism into `Aut(Γ)`. Landing in
  `Aut(Γ)` is clause `RQ2-1.02-C4`, `eq:stgaloisequivariance`. -/
  ρ : Gal(L/K) →* RQuiver.Aut toRQuiver
  /-- Clause `RQ2-1.02-C2`: the induced action on the discrete set `V` is continuous. -/
  smooth_V : IsSmooth ((RQuiver.Aut.toPermV toRQuiver).comp ρ)
  /-- Clause `RQ2-1.02-C3`: the induced action on the discrete set `E` is continuous. -/
  smooth_E : IsSmooth ((RQuiver.Aut.toPermE toRQuiver).comp ρ)

namespace RationalQuiver

/-- Build a `K`-rational quiver from the two smooth `Gal(L/K)`-actions of the source's own
reformulation of `def:rationalquivers`: `ρ_V : Gal(L/K) → Sym(V)`, `ρ_E : Gal(L/K) → Sym(E)` with
`s`, `t` `Gal(L/K)`-equivariant (`eq:stgaloisequivariance`).

@census none (helper)
-/
def ofAction (Γ : RQuiver.{u})
    (aV : Gal(L/K) →* Equiv.Perm Γ.V) (aE : Gal(L/K) →* Equiv.Perm Γ.E)
    (hs : ∀ (σ : Gal(L/K)) (e : Γ.E), Γ.source (aE σ e) = aV σ (Γ.source e))
    (ht : ∀ (σ : Gal(L/K)) (e : Γ.E), Γ.target (aE σ e) = aV σ (Γ.target e))
    (hV : IsSmooth aV) (hE : IsSmooth aE) : RationalQuiver K L where
  toRQuiver := Γ
  ρ := Γ.autOfAction aV aE hs ht
  smooth_V := hV
  smooth_E := hE

variable {K L}

/-- The vertex set of a `K`-rational quiver. -/
abbrev V (Γ : RationalQuiver K L) : Type u := Γ.toRQuiver.V

/-- The edge set of a `K`-rational quiver. -/
abbrev E (Γ : RationalQuiver K L) : Type u := Γ.toRQuiver.E

/-- The action of `Gal(L/K)` on the vertices of a `K`-rational quiver.

@census none (helper)
-/
instance mulActionV (Γ : RationalQuiver K L) : MulAction Gal(L/K) Γ.V :=
  MulAction.compHom _ ((RQuiver.Aut.toPermV Γ.toRQuiver).comp Γ.ρ)

/-- The action of `Gal(L/K)` on the edges of a `K`-rational quiver.

@census none (helper)
-/
instance mulActionE (Γ : RationalQuiver K L) : MulAction Gal(L/K) Γ.E :=
  MulAction.compHom _ ((RQuiver.Aut.toPermE Γ.toRQuiver).comp Γ.ρ)

/-- `eq:stgaloisequivariance`, source half: `s(σ e) = σ s(e)`. Clause `RQ2-1.02-C4`, made explicit
as the source says ("in other words: Gabriel's definition in the category of `Gal(L/K)`-sets").

@census none (helper: explicit form of clause RQ2-1.02-C4)
-/
@[simp]
theorem source_smul (Γ : RationalQuiver K L) (σ : Gal(L/K)) (e : Γ.E) :
    Γ.toRQuiver.source (σ • e) = σ • Γ.toRQuiver.source e :=
  ((Γ.ρ σ).hom.onV_source e).symm

/-- `eq:stgaloisequivariance`, target half: `t(σ e) = σ t(e)`. Clause `RQ2-1.02-C4`.

@census none (helper: explicit form of clause RQ2-1.02-C4)
-/
@[simp]
theorem target_smul (Γ : RationalQuiver K L) (σ : Gal(L/K)) (e : Γ.E) :
    Γ.toRQuiver.target (σ • e) = σ • Γ.toRQuiver.target e :=
  ((Γ.ρ σ).hom.onV_target e).symm

/-- The stabilizer `G_v` of a vertex is an open subgroup of `Gal(L/K)`; this is the
open-stabilizer form of clause `RQ2-1.02-C2`, and it is what makes `L(v) = L^{G_v}` a *finite*
extension of `K` in §2.2 (`census/NOTATION.md` §3).

@census none (helper)
-/
theorem isOpen_stabilizer_V (Γ : RationalQuiver K L) (v : Γ.V) :
    IsOpen ((MulAction.stabilizer Gal(L/K) v : Subgroup Gal(L/K)) : Set Gal(L/K)) :=
  Γ.smooth_V v

/-- The stabilizer `G_e` of an edge is an open subgroup of `Gal(L/K)`; open-stabilizer form of
clause `RQ2-1.02-C3`.

@census none (helper)
-/
theorem isOpen_stabilizer_E (Γ : RationalQuiver K L) (e : Γ.E) :
    IsOpen ((MulAction.stabilizer Gal(L/K) e : Subgroup Gal(L/K)) : Set Gal(L/K)) :=
  Γ.smooth_E e

/-- **Definition 1.3** (`def:splitrationalquivers`).
A quiver `Γ_K = (Γ, ρ)` over `K` is *constant*, or *split over `K`*, if `ρ` is the trivial group
homomorphism.

@census    RQ2-1.03
@source    def:splitrationalquivers
@clauses   RQ2-1.03-H1, RQ2-1.03-C1
@imports   none
@divergence none.
-/
def IsSplit (Γ : RationalQuiver K L) : Prop := Γ.ρ = 1

/-- **Definition 1.3, second form** (`def:splitrationalquivers`, clause `RQ2-1.03-C2`).
`Γ_K` is split over `K` if and only if the `Gal(L/K)`-actions on `V` and on `E` are *both*
trivial. The source states the two formulations as equivalent ("i.e."), so the equivalence is
itself part of the definition's content and is proved rather than assumed.

@census    none (auxiliary; discharges the second half of `RQ2-1.03`)
@source    def:splitrationalquivers
@clauses   RQ2-1.03-C2
@imports   none
@divergence none
-/
theorem isSplit_iff (Γ : RationalQuiver K L) :
    Γ.IsSplit ↔ (∀ (σ : Gal(L/K)) (v : Γ.V), σ • v = v) ∧ (∀ (σ : Gal(L/K)) (e : Γ.E), σ • e = e) := by
  constructor
  · intro h
    refine ⟨fun σ v => ?_, fun σ e => ?_⟩
    · show (Γ.ρ σ).hom.onV v = v
      rw [h]; rfl
    · show (Γ.ρ σ).hom.onE e = e
      rw [h]; rfl
  · rintro ⟨hV, hE⟩
    refine MonoidHom.ext fun σ => ?_
    have hV' : (Γ.ρ σ).hom.onV = (1 : RQuiver.Aut Γ.toRQuiver).hom.onV :=
      funext fun v => hV σ v
    have hE' : (Γ.ρ σ).hom.onE = (1 : RQuiver.Aut Γ.toRQuiver).hom.onE :=
      funext fun e => hE σ e
    exact RQuiver.Aut.ext (RQuiver.Hom.ext hV' hE')

/-- The kernel of a `K`-rational structure is an **open** subgroup of `Gal(L/K)`.

This is the engine of the finite-quotient remark `RQ2-1.20`: `ker ρ` is the intersection of the
stabilizers of all vertices and all edges, each open by clauses `RQ2-1.02-C2`/`C3`, and the
intersection is *finite* precisely because `V` and `E` are finite (clauses `RQ2-1.01-H1`,
`RQ2-1.01-H2` — which is what clause `RQ2-1.20-H2` points at). An open subgroup of a profinite
group has finite index, which is clause `RQ2-1.20-C4`, and its fixed field is the finite Galois
`L₀/K` of clause `RQ2-1.20-C3`.

@census none (helper: the engine of clauses RQ2-1.20-C3 and RQ2-1.20-C4)
-/
theorem isOpen_ker_ρ (Γ : RationalQuiver K L) :
    IsOpen ((Γ.ρ.ker : Subgroup Gal(L/K)) : Set Gal(L/K)) := by
  have hset : ((Γ.ρ.ker : Subgroup Gal(L/K)) : Set Gal(L/K))
      = (⋂ v : Γ.V, {σ : Gal(L/K) | σ • v = v}) ∩ (⋂ e : Γ.E, {σ : Gal(L/K) | σ • e = e}) := by
    ext σ
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨fun v => ?_, fun e => ?_⟩
      · show (Γ.ρ σ).hom.onV v = v
        rw [h]; rfl
      · show (Γ.ρ σ).hom.onE e = e
        rw [h]; rfl
    · rintro ⟨hV, hE⟩
      have hV' : (Γ.ρ σ).hom.onV = (1 : RQuiver.Aut Γ.toRQuiver).hom.onV := funext hV
      have hE' : (Γ.ρ σ).hom.onE = (1 : RQuiver.Aut Γ.toRQuiver).hom.onE := funext hE
      exact RQuiver.Aut.ext (RQuiver.Hom.ext hV' hE')
  rw [hset]
  exact (isOpen_iInter_of_finite fun v => Γ.smooth_V v).inter
    (isOpen_iInter_of_finite fun e => Γ.smooth_E e)

end RationalQuiver

end RationalQuivers
