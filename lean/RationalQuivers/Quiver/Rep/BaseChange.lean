module

public import RationalQuivers.Quiver.Rep.Nilpotent
public import RationalQuivers.Quiver.BaseChange

@[expose] public section

/-!
# Base change of rational quiver representations

Formalizes the unlabelled base-change proposition of §1.3 of `latex/rational_quivers.tex`
(census `RQ2-1.11` = `unlabeled:1`).

## Main definitions / results
* `RationalQuivers.RationalQuiver.Rep.baseChange` — `M_{E'} := E' ⊗_K M_K` as a representation
  of `Γ_{E'} = E' ⊗_K Γ_K` (clause `RQ2-1.11-C1`).
* `RationalQuivers.RationalQuiver.FDRep.baseChangeFunctor` — the functor
  `Rep(Γ_K) ⥤ Rep(Γ_{E'})` (census `RQ2-1.11`, clause `RQ2-1.11-C3`).
* `RationalQuivers.RationalQuiver.Rep.baseChange_isNilpotent`,
  `RationalQuivers.RationalQuiver.RepNil.baseChangeFunctor` — the parenthetical *(nilpotent)*
  clauses `RQ2-1.11-C2`, `RQ2-1.11-C4`.

## Implementation notes

**Base change of representations is restriction of the Galois action.**  Under Galois descent
(`RQ2-1.13`) a `K`-rational representation is the datum of the `L`-spaces `M(v)` together with a
continuous semi-linear `Gal(L/K)`-action; the `K`-form is `M_K = (⊔_v M(v))^{Gal(L/K)}` and
`E' ⊗_K M_K` corresponds to the *same* `L`-spaces with the action restricted along
`Gal(L/E') ↪ Gal(L/K)`.  So `Rep.baseChange` keeps `M`, `φ_e` and the `φ_{v,σ}` and precomposes
the rational structure with `galRestrict`, exactly as S1's `RationalQuiver.baseChange` does for
the quiver itself (`def:quiverbasechange`); the source's own proof says no more ("this follows by
`E`-linear extension from the definitions … the relevant action of `Gal(L/E)` being the
restriction of the continuous action attached to `M_K`").

**Finiteness (clause `RQ2-1.11-H3`).**  `[FiniteDimensional K E']` is carried, because S1's
`RationalQuiver.baseChange` — hence `Γ_{E'}` itself — requires it (`RQ2-1.05-H2`: the continuity of
the restricted action is proved from it, and the finiteness-free variant was removed from
`Quiver/BaseChange.lean` on 2026-08-29).  Since census r5 the source states the hypothesis too, so
carrying it is faithful, not a weakening.
-/

universe u

namespace RationalQuivers

namespace RationalQuiver

open CategoryTheory

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
variable {Γ : RationalQuiver K L}

namespace Rep

/-- **Base change of representations** (clause `RQ2-1.11-C1`).  For an intermediate field
`L/E'/K` with `E'/K` finite, `M_{E'} := E' ⊗_K M_K` is the representation of
`Γ_{E'} = E' ⊗_K Γ_K` with the same `L`-spaces `M(v)`, the same edge maps `φ_e`, and the
semi-linear structure maps of `M_K` restricted along `Gal(L/E') ↪ Gal(L/K)`.

@census none (helper: clause `RQ2-1.11-C1`; the census row is claimed by
`FDRep.baseChangeFunctor`)
-/
def baseChange (E' : IntermediateField K L) [FiniteDimensional K E'] (M : Rep Γ) :
    Rep ((RationalQuiver.baseChange K L E').obj Γ) where
  M v := M.M v
  addCommGroup v := M.addCommGroup v
  module v := M.module v
  φ σ v := M.φ (galRestrict K L E' σ) v
  semilinear σ v a m := M.semilinear (galRestrict K L E' σ) v a m
  cocycle σ τ v m := M.cocycle (galRestrict K L E' σ) (galRestrict K L E' τ) v m
  smooth x := (M.smooth x).preimage (continuous_galRestrict K L E')
  φEdge e := M.φEdge e
  edge_equivariance σ e m m' h := M.edge_equivariance (galRestrict K L E' σ) e m m' h

/-- Base change of a homomorphism of rational representations: the same family `(ψ_v)_v`, whose
rationality is now only required over the smaller group `Gal(L/E')`.

@census none (helper: clause `RQ2-1.11-C3`)
-/
def Hom.baseChange (E' : IntermediateField K L) [FiniteDimensional K E'] {M N : Rep Γ}
    (f : Rep.Hom M N) : Rep.Hom (M.baseChange E') (N.baseChange E') where
  ψ v := f.ψ v
  edge e m := f.edge e m
  rational σ v m := f.rational (galRestrict K L E' σ) v m

/-- Clause `RQ2-1.11-C2`: the base change of a **nilpotent** representation is nilpotent.  The
edge maps, and hence all path composites, are unchanged by base change.

`IsNilpotent` is phrased through `pathCompose`, which depends only on the **classical** quiver
`Γ.toRQuiver`, the family `M.M` and the edge maps `M.φEdge` — all three of which base change
leaves untouched — so the two statements are the same proposition up to delta and the proof is
`h` itself.  (The G4-draft repair of 2026-08-29: with the earlier `Rep`-parametrised `pathMap`
the two sides differed in their `Quiver` instance argument and neither `exact h` nor `rw`
matched.  See `workflow/stages/S2/DESIGN-NOTES.md` §8.)

@census none (helper: clause `RQ2-1.11-C2`)
-/
theorem baseChange_isNilpotent (E' : IntermediateField K L) [FiniteDimensional K E']
    {M : Rep Γ} (h : M.IsNilpotent) : (M.baseChange E').IsNilpotent := h

end Rep

namespace FDRep

/-- Base change of a finite-dimensional representation; the dimensions over `L` are unchanged.

@census none (helper: clause `RQ2-1.11-C1`)
-/
def baseChange (E' : IntermediateField K L) [FiniteDimensional K E'] (M : FDRep Γ) :
    FDRep ((RationalQuiver.baseChange K L E').obj Γ) where
  toRep := M.toRep.baseChange E'
  finiteDimensional v := M.finiteDimensional v

/-- **Proposition (base change for representations)** (`unlabeled:1`, §1.3 of the source).

If `M_K` is a representation of a `K`-rational quiver `Γ_K` (clause `RQ2-1.11-H2`) then for any
intermediate field `L/E'/K` with `E'/K` **finite** (clauses `RQ2-1.11-H1`, `RQ2-1.11-H3`) the
`E'`-vector space `M_{E'} := E' ⊗_K M_K` carries a natural structure of representation of
`E' ⊗_K Γ_K` (clause `RQ2-1.11-C1`, `Rep.baseChange`), and base change of representations is
**functorial** (clause `RQ2-1.11-C3`) — which is what this declaration is.

The parenthetical *(nilpotent)* half of the proposition is
`Rep.baseChange_isNilpotent` (clause `RQ2-1.11-C2`) and `RepNil.baseChangeFunctor`
(clause `RQ2-1.11-C4`).

@census    RQ2-1.11
@source    prop:repbasechange
@clauses   RQ2-1.11-H1, RQ2-1.11-H2, RQ2-1.11-H3, RQ2-1.11-C1, RQ2-1.11-C2, RQ2-1.11-C3, RQ2-1.11-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION (verifier-agreed, `stages/S2/VERIFICATION.md` V-2).
Clause `RQ2-1.11-H3` (`E'/K` finite) is carried as `[FiniteDimensional K E']`,
as the source now states it (census r5) and as S1's `RationalQuiver.baseChange` requires.
`M_{E'} = E' ⊗_K M_K` is realized, via Galois descent (`RQ2-1.13`), as the same `L`-spaces with the
`Gal(L/K)`-action restricted to `Gal(L/E')`; this is the standard identification the source's own
one-line proof appeals to, and it is what makes `Γ_{E'}` (which S1 defines the same way) the right
target.  Clause `RQ2-1.11-C1`'s `M_{E'} := E' ⊗_K M_K` is **proved** to agree with this realization
by `Rep.baseChange_form_iso` (`Quiver/Rep/TowerDescent.lean`), so the identification is a theorem
and not a convention (`stages/S2/VERIFICATION.md` V-3).

**Added hypothesis, disclosed** (`VERIFICATION.md` V-4, weaker form).  The functor is stated on
`FDRep Γ`, i.e. on the **finite-dimensional** representations of clause `RQ2-1.10-C1`, whereas
clause `RQ2-1.11-H2` says only "`M_K` is a representation of `Γ_K`".  Nothing is lost: the
object-level construction `Rep.baseChange` carries **no** finiteness hypothesis and covers the
general case in-tree, so the union of the two carriers is at least as strong as the source; the
functor is stated on `Rep(Γ_K)` because that is the category the source's next sentence
("base change of (nilpotent) representations is functorial") is about.
-/
def baseChangeFunctor (E' : IntermediateField K L) [FiniteDimensional K E'] :
    FDRep Γ ⥤ FDRep ((RationalQuiver.baseChange K L E').obj Γ) where
  obj M := M.baseChange E'
  map f := Rep.Hom.baseChange E' f
  map_id _ := rfl
  map_comp _ _ := rfl

end FDRep

namespace RepNil

/-- Clause `RQ2-1.11-C4`: base change of **nilpotent** representations is functorial — the functor
of `RQ2-1.11` restricts to the full subcategories `Rep^nil`.

@census none (helper: clause `RQ2-1.11-C4`)
-/
def baseChangeFunctor (E' : IntermediateField K L) [FiniteDimensional K E'] :
    (RepNil Γ).FullSubcategory ⥤ (RepNil ((RationalQuiver.baseChange K L E').obj Γ)).FullSubcategory where
  obj M := ⟨M.obj.baseChange E', Rep.baseChange_isNilpotent E' M.property⟩
  map f := ⟨(FDRep.baseChangeFunctor E').map f.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

end RepNil

end RationalQuiver

end RationalQuivers
