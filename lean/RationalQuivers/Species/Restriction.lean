module

public import RationalQuivers.Species.Hom

@[expose] public section

/-!
# Restriction of étale species along a finite separable extension

Formalizes Definition `def:restrictionforspecies` of §2.1 of `latex/rational_quivers.tex`
(census `RQ2-2.07`).

## Main definitions / results
* `RationalQuivers.EtaleSpecies.restriction` — `res_{N/K} S` (census `RQ2-2.07`).
* `RationalQuivers.EtaleSpecies.restriction_isSeparable`,
  `RationalQuivers.EtaleSpecies.restriction_etale` — clause `RQ2-2.07-C4`, the two facts that
  consume both the finiteness and the separability of `N/K` and make `res_{N/K} S` étale.
* `RationalQuivers.EtaleSpecies.restrictionFunctor` — restriction on morphisms.

## Implementation notes

"`res_{N/K} V` is the underlying `K`-vector space" (clause `RQ2-2.07-C1`) is realised by keeping the
carrier types *literally unchanged* and composing the structure maps: `algebraMap K (res L_i)` is by
definition `algebraMap N (L_i) ∘ algebraMap K N`. Consequently `restriction_I`, `restriction_L`,
`restriction_M` hold by `rfl` — no transport is needed anywhere in this file, matching the relief
stage S1 recorded for its bundled-carrier round trips.

`N/K` finite separable is carried by the instance binders `[Module.Finite K N]` and
`[Algebra.IsSeparable K N]`. Both are genuinely consumed by the body (`Module.Finite.trans`,
`Algebra.IsSeparable.trans`, `Algebra.Etale.comp`), so — unlike the situation `CONVENTIONS.md` §3
warns about — Lean retains them in the elaborated signature; this is checked by the `#check` in
`workflow/stages/S3/VALIDATION/`.
-/

universe u

namespace RationalQuivers

open CategoryTheory

namespace EtaleSpecies

variable {K N : Type u} [Field K] [Field N] [Algebra K N] [Module.Finite K N]
  [Algebra.IsSeparable K N]

/-- `N/K` finite separable makes `N` an étale `K`-algebra; this is what `restriction` composes
with. -/
theorem etale_of_finite_separable : Algebra.Etale K N :=
  ⟨Algebra.FormallyEtale.of_isSeparable K N,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- The `K`-algebra structure on `res_{N/K} L_i`: the composite `K → N → L_i`. -/
@[reducible] def restrictionAlgebraL (S : EtaleSpecies.{u} N) (i : S.I) : Algebra K (S.L i) :=
  ((algebraMap N (S.L i)).comp (algebraMap K N)).toAlgebra

/-- The `K`-algebra structure on `res_{N/K} {}_iM_j`: the composite `K → N → {}_iM_j`. -/
@[reducible] def restrictionAlgebraM (S : EtaleSpecies.{u} N) (i j : S.I) : Algebra K (S.M i j) :=
  ((algebraMap N (S.M i j)).comp (algebraMap K N)).toAlgebra

omit [Module.Finite K N] [Algebra.IsSeparable K N] in
/-- The composite `K → N → L_i` makes `L_i` a `K`-`N`-tower. (Neither the finiteness nor the
separability of `N/K` is needed for this; both are `omit`ted so the signature says so.) -/
theorem isScalarTower_KN_L (S : EtaleSpecies.{u} N) (i : S.I) :
    letI : Algebra K (S.L i) := restrictionAlgebraL (K := K) S i;
      IsScalarTower K N (S.L i) := by
  letI : Algebra K (S.L i) := restrictionAlgebraL (K := K) S i
  exact IsScalarTower.of_algebraMap_eq' rfl

omit [Module.Finite K N] [Algebra.IsSeparable K N] in
/-- The composite `K → N → {}_iM_j` makes `{}_iM_j` a `K`-`N`-tower. (As above, neither
hypothesis on `N/K` is used.) -/
theorem isScalarTower_KN_M (S : EtaleSpecies.{u} N) (i j : S.I) :
    letI : Algebra K (S.M i j) := restrictionAlgebraM (K := K) S i j;
      IsScalarTower K N (S.M i j) := by
  letI : Algebra K (S.M i j) := restrictionAlgebraM (K := K) S i j
  exact IsScalarTower.of_algebraMap_eq' rfl

omit [Algebra.IsSeparable K N] in
/-- Clause `RQ2-2.07-C4`, first half: each `res_{N/K} L_i` is a **finite** extension of `K`.
Consumes the finiteness of `N/K` (and only that; separability is `omit`ted). -/
theorem restriction_finite_L (S : EtaleSpecies.{u} N) (i : S.I) :
    letI : Algebra K (S.L i) := restrictionAlgebraL (K := K) S i; Module.Finite K (S.L i) := by
  letI : Algebra K (S.L i) := restrictionAlgebraL (K := K) S i
  haveI := isScalarTower_KN_L (K := K) S i
  exact Module.Finite.trans N (S.L i)

omit [Module.Finite K N] in
/-- Clause `RQ2-2.07-C4`, first half: each `res_{N/K} L_i` is a **separable** extension of `K`.
Consumes the separability of `N/K` (and only that; finiteness is `omit`ted). -/
theorem restriction_isSeparable (S : EtaleSpecies.{u} N) (i : S.I) :
    letI : Algebra K (S.L i) := restrictionAlgebraL (K := K) S i;
      Algebra.IsSeparable K (S.L i) := by
  letI : Algebra K (S.L i) := restrictionAlgebraL (K := K) S i
  haveI := isScalarTower_KN_L (K := K) S i
  exact Algebra.IsSeparable.trans K N (S.L i)

/-- Clause `RQ2-2.07-C4`, second half: each `res_{N/K} {}_iM_j` is **finite étale** as a
`K`-algebra. Consumes both the finiteness and the separability of `N/K`, through
`etale_of_finite_separable`. -/
theorem restriction_etale (S : EtaleSpecies.{u} N) (i j : S.I) :
    letI : Algebra K (S.M i j) := restrictionAlgebraM (K := K) S i j;
      Algebra.Etale K (S.M i j) := by
  letI : Algebra K (S.M i j) := restrictionAlgebraM (K := K) S i j
  haveI := isScalarTower_KN_M (K := K) S i j
  haveI := etale_of_finite_separable (K := K) (N := N)
  exact Algebra.Etale.comp K N (S.M i j)

/-- **Definition 2.7** (`def:restrictionforspecies`).
For a finite separable extension `N/K` and an étale `N`-species `S`, the *restriction*
`res_{N/K} S = (res_{N/K} L_i, res_{N/K} {}_iM_j)_{i,j ∈ I}` is the étale `K`-species on the **same**
index set `I` obtained by taking the underlying `K`-vector spaces, i.e. by composing every structure
map with `K → N`.

@census    RQ2-2.07
@source    def:restrictionforspecies
@clauses   RQ2-2.07-H1, RQ2-2.07-H2, RQ2-2.07-C1, RQ2-2.07-C2, RQ2-2.07-C3, RQ2-2.07-C4
@imports   none
@divergence none. `res_{N/K} V` "is the underlying `K`-vector space" is realised by keeping the
carrier and composing the structure maps, so `restriction_L` and `restriction_M` are `rfl`; the
output type is `EtaleSpecies K`, which is clause `RQ2-2.07-C3`; and the two facts that make it étale
are the separate theorems `restriction_isSeparable` and `restriction_etale` (clause `RQ2-2.07-C4`),
each of which consumes a hypothesis on `N/K` rather than reading it off the output type.
-/
def restriction (S : EtaleSpecies.{u} N) : EtaleSpecies.{u} K where
  I := S.I
  L := S.L
  algebra_L := fun i => restrictionAlgebraL (K := K) S i
  finite_L := fun i => restriction_finite_L (K := K) S i
  separable_L := fun i => restriction_isSeparable (K := K) S i
  M := S.M
  algebra_M := fun i j => restrictionAlgebraM (K := K) S i j
  etale_M := fun i j => restriction_etale (K := K) S i j
  left := fun i j =>
    letI : Algebra K (S.L i) := restrictionAlgebraL (K := K) S i
    letI : Algebra K (S.M i j) := restrictionAlgebraM (K := K) S i j
    haveI := isScalarTower_KN_L (K := K) S i
    haveI := isScalarTower_KN_M (K := K) S i j
    (S.left i j).restrictScalars K
  right := fun i j =>
    letI : Algebra K (S.L j) := restrictionAlgebraL (K := K) S j
    letI : Algebra K (S.M i j) := restrictionAlgebraM (K := K) S i j
    haveI := isScalarTower_KN_L (K := K) S j
    haveI := isScalarTower_KN_M (K := K) S i j
    (S.right i j).restrictScalars K

/-- Clause `RQ2-2.07-C2`: restriction is taken on the **same** index set `I`. -/
@[simp] theorem restriction_I (S : EtaleSpecies.{u} N) : (restriction (K := K) S).I = S.I := rfl

/-- Clause `RQ2-2.07-C1`/`RQ2-2.07-C2`: the vertex algebras are unchanged as carriers. -/
@[simp] theorem restriction_L (S : EtaleSpecies.{u} N) : (restriction (K := K) S).L = S.L := rfl

/-- Clause `RQ2-2.07-C1`/`RQ2-2.07-C2`: the edge algebras are unchanged as carriers. -/
@[simp] theorem restriction_M (S : EtaleSpecies.{u} N) : (restriction (K := K) S).M = S.M := rfl

/-- Clause `RQ2-2.07-C1`: the `K`-structure of `res_{N/K} L_i` is the one obtained by restricting
scalars along `K → N`, i.e. `res_{N/K} L_i` really is the underlying `K`-vector space of `L_i`. -/
theorem restriction_algebraMap_L (S : EtaleSpecies.{u} N) (i : S.I) :
    @algebraMap K (S.L i) _ _ ((restriction (K := K) S).algebra_L i) =
      (algebraMap N (S.L i)).comp (algebraMap K N) := rfl

/-- Clause `RQ2-2.07-C1`: likewise for the edge algebras. -/
theorem restriction_algebraMap_M (S : EtaleSpecies.{u} N) (i j : S.I) :
    @algebraMap K (S.M i j) _ _ ((restriction (K := K) S).algebra_M i j) =
      (algebraMap N (S.M i j)).comp (algebraMap K N) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction of a morphism of étale `N`-species. The index map and all component algebra maps
are unchanged; only the base of the scalars is restricted.

@census none (helper: restriction on morphisms)
-/
def restrictionMap {S T : EtaleSpecies.{u} N} (f : S ⟶ T) :
    (restriction (K := K) S) ⟶ (restriction (K := K) T) where
  onI := f.onI
  onL := fun t =>
    letI : Algebra K (S.L (f.onI t)) := restrictionAlgebraL (K := K) S (f.onI t)
    letI : Algebra K (T.L t) := restrictionAlgebraL (K := K) T t
    haveI := isScalarTower_KN_L (K := K) S (f.onI t)
    haveI := isScalarTower_KN_L (K := K) T t
    (f.onL t).restrictScalars K
  onM := fun s t =>
    letI : Algebra K (S.M (f.onI s) (f.onI t)) := restrictionAlgebraM (K := K) S (f.onI s) (f.onI t)
    letI : Algebra K (T.M s t) := restrictionAlgebraM (K := K) T s t
    haveI := isScalarTower_KN_M (K := K) S (f.onI s) (f.onI t)
    haveI := isScalarTower_KN_M (K := K) T s t
    (f.onM s t).restrictScalars K
  compat_left := fun s t => AlgHom.ext fun x => congrArg (fun g => g x) (f.compat_left s t)
  compat_right := fun s t => AlgHom.ext fun x => congrArg (fun g => g x) (f.compat_right s t)

/-- Restriction as a functor from étale `N`-species to étale `K`-species.

@census none (helper: the functorial packaging of `RQ2-2.07`)
-/
def restrictionFunctor : EtaleSpecies.{u} N ⥤ EtaleSpecies.{u} K where
  obj S := restriction (K := K) S
  map f := restrictionMap f
  map_id _ := rfl
  map_comp _ _ := rfl

end EtaleSpecies

end RationalQuivers
