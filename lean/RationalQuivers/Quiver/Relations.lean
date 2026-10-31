module

public import RationalQuivers.Quiver.Basic

@[expose] public section

/-!
# Quivers with relations and their `K`-rational structures

Formalizes the "Relations" remark of §1.2 of `latex/rational_quivers.tex` (census `RQ2-1.19`),
which is load-bearing for `ex:gelfand` (the Gelfand quiver carries the relation
`a₋ b₋ = a₊ b₊`).

## Main definitions / results
* `RationalQuivers.RQuiver.Relation` — a relation in a classical quiver, i.e. an (ordered) pair of
  parallel paths, using mathlib's `Quiver.Path` through the D4 bridge of `Quiver/Basic.lean`.
* `RationalQuivers.RQuiver.Aut.onRelation` — the induced action of `Aut(Γ)` on relations, with
  `Aut.onRelation_one` / `Aut.onRelation_one_eq_id` (the identity acts trivially).
* `RationalQuivers.RationalQuiver.RelationsCompat` — the compatibility condition of the remark
  (census `RQ2-1.19`).
-/

universe u

namespace RationalQuivers

open CategoryTheory

namespace RQuiver

/-- A *relation* in a classical quiver `Γ`: an ordered pair of parallel paths, i.e. the equation
`p = q` for two paths `p, q : a ⟶* b`. Paths are mathlib's `Quiver.Path` for the `Hom`-indexed
view of `Γ` supplied by the D4 bridge `RQuiver.instQuiverV`.

@census none (helper for `RQ2-1.19`)
-/
def Relation (Γ : RQuiver.{u}) : Type u :=
  Σ p : Γ.V × Γ.V, _root_.Quiver.Path p.1 p.2 × _root_.Quiver.Path p.1 p.2

/-- The action of `Aut(Γ)` on the relations of `Γ`, obtained by transporting both paths along the
prefunctor of the D4 bridge.

@census none (helper for `RQ2-1.19`)
-/
def Aut.onRelation {Γ : RQuiver.{u}} (f : Aut Γ) (r : Relation Γ) : Relation Γ :=
  ⟨(f.hom.onV r.1.1, f.hom.onV r.1.2),
    (toPrefunctor f.hom).mapPath r.2.1, (toPrefunctor f.hom).mapPath r.2.2⟩

/-- The identity automorphism acts trivially on relations.

The two vertex components are `id` by `rfl`; the two path components are path induction over the
identity prefunctor, which is mathlib's `Prefunctor.mapPath_id`. That lemma applies *directly*,
without transport: `toPrefunctor (𝟙 Γ)` is definitionally mathlib's `𝟭q Γ.V` — the D4 bridge's
functoriality proof `RQuiver.toQuiv.map_id` is `rfl`, since `Prefunctor.map` on the identity
returns `⟨e.1, _, _⟩` for `e : a ⟶ b` and subtype eta plus definitional proof irrelevance make
that `e`.

Without this lemma the `σ = 1` case of a `RelationsCompat` proof has to be discharged element by
element over a *concrete* relation set (`Aut.onRelation 1` is `rfl` on each concrete relation but
not on a variable one), which is what `Meta/Vacuity.lean`'s S1 probe **P4** did before this lemma
existed. With it, that case is `Set.image_id`.

@census none (helper for `RQ2-1.19`)
-/
@[simp] theorem Aut.onRelation_one {Γ : RQuiver.{u}} (r : Relation Γ) :
    Aut.onRelation (1 : Aut Γ) r = r := by
  obtain ⟨⟨a, b⟩, p, q⟩ := r
  show (⟨(a, b), (𝟭q Γ.V).mapPath p, (𝟭q Γ.V).mapPath q⟩ : Relation Γ) = ⟨(a, b), p, q⟩
  rw [Prefunctor.mapPath_id, Prefunctor.mapPath_id]

/-- `Aut.onRelation 1` is the identity function, the form the `σ = 1` case of a `RelationsCompat`
proof consumes.

@census none (helper for `RQ2-1.19`)
-/
theorem Aut.onRelation_one_eq_id {Γ : RQuiver.{u}} :
    (fun r => Aut.onRelation (1 : Aut Γ) r) = id :=
  funext Aut.onRelation_one

end RQuiver

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]

namespace RationalQuiver

/-- **Remark on relations** (unlabelled in the source; census `RQ2-1.19`).
If `Γ` is a quiver with relations `R`, a `K`-rational structure is required to respect them: each
element of the Galois group maps a given relation to a given relation.

@census    RQ2-1.19
@source    def:galoisrelations
@clauses   RQ2-1.19-Hs1, RQ2-1.19-H1, RQ2-1.19-C1, RQ2-1.19-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION of the meaning of "relation". The source does not define
"quiver with relations" — it is Gabriel's notion, cited but not restated — and the only instance it
uses is the Gelfand quiver's `a₋ b₋ = a₊ b₊` (`ex:gelfand`), an *equation between two parallel
paths*. We take `Relation Γ` to be exactly that: an ordered pair of parallel paths. In Gabriel's
general setting a relation is a `k`-linear combination of parallel paths; the content of this
remark — that `ρ` permutes the chosen set `R` of relations, equivalently that `im ρ` lies in the
automorphism group of the quiver *with* relations — is the same statement in either model, since
`Aut(Γ)` acts on either notion of relation by transport of paths, and no downstream statement of
the paper uses a non-equational relation. Clause `RQ2-1.19-H1` is the argument `R`; clause
`RQ2-1.19-C1` is the displayed condition; clause `RQ2-1.19-C2` is `relationsCompat_iff_range` below.
-/
def RelationsCompat (Γ : RationalQuiver K L) (R : Set (RQuiver.Relation Γ.toRQuiver)) : Prop :=
  ∀ σ : Gal(L/K), (fun r => RQuiver.Aut.onRelation (Γ.ρ σ) r) '' R = R

/-- Clause `RQ2-1.19-C2`: `Γ_K` respects the relations `R` if and only if the image of `ρ` lies in
the set of automorphisms of the quiver *with* relations, i.e. those automorphisms of `Γ` that
permute `R`.

@census none (helper: clause RQ2-1.19-C2)
-/
theorem relationsCompat_iff_range (Γ : RationalQuiver K L)
    (R : Set (RQuiver.Relation Γ.toRQuiver)) :
    Γ.RelationsCompat R ↔
      ∀ f ∈ Γ.ρ.range, (fun r => RQuiver.Aut.onRelation f r) '' R = R := by
  constructor
  · rintro h f ⟨σ, rfl⟩
    exact h σ
  · intro h σ
    exact h (Γ.ρ σ) ⟨σ, rfl⟩

end RationalQuiver

end RationalQuivers
