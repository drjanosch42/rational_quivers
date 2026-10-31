module

public import RationalQuivers.Species.Etale
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/-!
# Morphisms of étale `K`-species

Formalizes the morphism definition of §2.1 of `latex/rational_quivers.tex` (census `RQ2-2.04`).

## Main definitions / results
* `RationalQuivers.EtaleSpecies.Hom` — a morphism `f : S → T` of étale `K`-species
  (census `RQ2-2.04`).
* `RationalQuivers.EtaleSpecies.instCategory` — the resulting category of étale `K`-species,
  the ambient category in which `RQ2-2.08`, `RQ2-2.13` and `RQ2-2.34` are stated.

## Implementation notes

**Amended 2026-10-03 (docstring-only `R-PROC-4` amendment of frozen S3, coordinator ruling
`R-FR-9`, final-release WP-16b, stale item R4).** The definition is now **literal**. The amended
source (census r18, FA-01 / S4-F1) prints the index map as `ι : Ĩ → I` ("note the direction") and
the third datum as a `K`-algebra homomorphism compatible with the left and right structure maps
transported along `ι_s̃`, `ι_t̃`. That is exactly `Hom` below: `onI : T.I → S.I`, `onL`, `onM`, and
`compat_left`/`compat_right`. The note that stood here until this amendment said that the source
prints `ι : I → Ĩ`, that the reversal was a coordinator-sanctioned deviation, and that an author
question was queued. None of that is true of the current source. The sanction's record is
`workflow/stages/S4/DESIGN-NOTES.md` §2 and the dated banner in `workflow/stages/S3/DESIGN-NOTES.md`.
The two theorems that justified the reversal,
`RationalQuivers.Examples.printedHom_isEmpty_of_gelfand_to_point` and
`RationalQuivers.Examples.printedHom_onI_not_unique` (stage S4, `Species/Examples.lean`), stay in the
tree. They are now statements about the **superseded** printed shape.

Equivalently, and this is the invariant reading of the amendment: a morphism `S → T` **is a single
`K`-algebra homomorphism `∏_{i ∈ I} L_i → ∏_{ĩ ∈ Ĩ} L̃_ĩ`** of the underlying vertex algebras
(such a map factors, componentwise on the target, through exactly one projection of the source,
which is what `ι` and `ι_ĩ` record), together with the corresponding data on the edge algebras.

Identity and composition satisfy the category axioms by `rfl`: all three fields of a `Hom` are
functions or proofs, so structure eta closes the round trips without any transport. (This is the
`RQ2-1.23` relief recorded by stage S1, commit `655df03`; the analogue holds here.)
-/

universe u

namespace RationalQuivers

open CategoryTheory

namespace EtaleSpecies

variable {K : Type u} [Field K]

/-- **Definition** (Morphisms of étale `K`-species; unlabelled in the source, census `RQ2-2.04`).
A morphism `f : S → T` of étale `K`-species consists of (i) a map `ι : Ĩ → I` of index sets,
(ii) for each `ĩ ∈ Ĩ` a `K`-algebra homomorphism `ι_ĩ : L_{ι(ĩ)} → L̃_ĩ`, and (iii) for all
`s̃, t̃ ∈ Ĩ` a homomorphism `ι_{s̃t̃} : {}_{ι(s̃)}M_{ι(t̃)} → {}_{s̃}M̃_{t̃}` of the two-sided algebra
structures, i.e. a `K`-algebra map compatible with the structure maps transported along `ι_s̃` and
`ι_t̃`. Equivalently: a single `K`-algebra map `∏_i L_i → ∏_ĩ L̃_ĩ` of the vertex algebras plus the
corresponding edge data.

@census    RQ2-2.04
@source    def:specieshom
@clauses   RQ2-2.04-H1, RQ2-2.04-C1, RQ2-2.04-C2, RQ2-2.04-C3
@imports   none
@divergence none.  **The `JUSTIFIED_REFORMULATION` this row carried from 2026-08-30 to 2026-10-03
was retired on 2026-10-03** (docstring-only `R-PROC-4` amendment of frozen S3, coordinator ruling
`R-FR-9`, final-release WP-16b, stale item R4). It disclosed (a) the reversed index map, against a
source that printed `ι : I → Ĩ`, and (b) the rendering of an "`L_i,L_j`-bialgebra homomorphism" as
a `K`-algebra map with two commuting squares. The amended source (census r18) prints both exactly as
the structure states them: (i) `ι : Ĩ → I`, (ii) `ι_ĩ : L_{ι(ĩ)} → L̃_ĩ`, (iii) a `K`-algebra map
`ι_{s̃t̃}` whose composites with the left (right) structure maps agree, which is
`compat_left`/`compat_right`. Clauses `RQ2-2.04-C1`..`C3` now carry the corrected direction too. The
old (a) also cited clause `RQ-2.13-H2`, which census r18 retired; the functors of `RQ2-2.13` are now
constructed explicitly in the source, and no `G`-set anti-equivalence is invoked. The
counterexamples `Examples.printedHom_isEmpty_of_gelfand_to_point` and
`Examples.printedHom_onI_not_unique` remain as the record of why the printed shape was withdrawn.
-/
@[ext]
structure Hom (S T : EtaleSpecies.{u} K) : Type u where
  /-- Clause `RQ2-2.04-C1`, amended direction: the map `ι : Ĩ → I` of index sets. -/
  onI : T.I → S.I
  /-- Clause `RQ2-2.04-C2`: the `K`-algebra maps `ι_ĩ : L_{ι(ĩ)} → L̃_ĩ`. -/
  onL : ∀ t, S.L (onI t) →ₐ[K] T.L t
  /-- Clause `RQ2-2.04-C3`: the maps `ι_{s̃t̃} : {}_{ι(s̃)}M_{ι(t̃)} → {}_{s̃}M̃_{t̃}`. -/
  onM : ∀ s t, S.M (onI s) (onI t) →ₐ[K] T.M s t
  /-- Clause `RQ2-2.04-C3`: `ι_{s̃t̃}` respects the left structure map, transported along `ι_s̃`. -/
  compat_left : ∀ s t, (onM s t).comp (S.left (onI s) (onI t)) = (T.left s t).comp (onL s)
  /-- Clause `RQ2-2.04-C3`: `ι_{s̃t̃}` respects the right structure map, transported along
  `ι_t̃`. -/
  compat_right : ∀ s t, (onM s t).comp (S.right (onI s) (onI t)) = (T.right s t).comp (onL t)

namespace Hom

/-- The identity morphism of an étale `K`-species.

@census none (helper)
-/
protected def id (S : EtaleSpecies.{u} K) : Hom S S where
  onI := fun i => i
  onL := fun t => AlgHom.id K (S.L t)
  onM := fun s t => AlgHom.id K (S.M s t)
  compat_left := fun _ _ => rfl
  compat_right := fun _ _ => rfl

/-- Composition of morphisms of étale `K`-species.

@census none (helper)
-/
protected def comp {S T U : EtaleSpecies.{u} K} (f : Hom S T) (g : Hom T U) : Hom S U where
  onI := fun u => f.onI (g.onI u)
  onL := fun u => (g.onL u).comp (f.onL (g.onI u))
  onM := fun u v => (g.onM u v).comp (f.onM (g.onI u) (g.onI v))
  compat_left := fun u v => by
    rw [AlgHom.comp_assoc, f.compat_left (g.onI u) (g.onI v), ← AlgHom.comp_assoc,
      g.compat_left u v, AlgHom.comp_assoc]
  compat_right := fun u v => by
    rw [AlgHom.comp_assoc, f.compat_right (g.onI u) (g.onI v), ← AlgHom.comp_assoc,
      g.compat_right u v, AlgHom.comp_assoc]

end Hom

/-- The category of étale `K`-species (census `RQ2-2.04`): objects are étale `K`-species, morphisms
are `EtaleSpecies.Hom`. This is the ambient category in which the adjunction `RQ2-2.08`, the
anti-equivalence `RQ2-2.13` and the base-change transitivity `RQ2-2.34` are stated.

@census none (the category structure carried by `RQ2-2.04`)
-/
instance instCategory : CategoryTheory.Category.{u, u + 1} (EtaleSpecies.{u} K) where
  Hom S T := Hom S T
  id S := Hom.id S
  comp f g := Hom.comp f g

@[simp] lemma id_onI (S : EtaleSpecies.{u} K) : Hom.onI (𝟙 S) = fun i => i := rfl

@[simp] lemma comp_onI {S T U : EtaleSpecies.{u} K} (f : S ⟶ T) (g : T ⟶ U) :
    Hom.onI (f ≫ g) = fun u => f.onI (g.onI u) := rfl

/-- An isomorphism of étale `K`-species induces a **bijection** of index sets. This is what makes a
"canonical identification of index sets" (clause `RQ2-2.34-C1`) a consequence of an isomorphism of
species rather than an extra datum.

@census none (helper)
-/
theorem Iso.onI_bijective {S T : EtaleSpecies.{u} K} (e : S ≅ T) :
    Function.Bijective (Hom.onI e.hom) := by
  refine ⟨Function.LeftInverse.injective (g := Hom.onI e.inv) fun t => ?_,
    Function.RightInverse.surjective (g := Hom.onI e.inv) fun i => ?_⟩
  · exact congrFun (congrArg Hom.onI e.inv_hom_id) t
  · exact congrFun (congrArg Hom.onI e.hom_inv_id) i

end EtaleSpecies

end RationalQuivers
