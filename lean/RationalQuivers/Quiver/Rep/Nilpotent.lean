module

public import RationalQuivers.Quiver.Rep.Category
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public section

/-!
# Nilpotent representations and `Rep^nil(Γ_K)`

Formalizes the nilpotent half of the unlabelled definition of §1.3 of
`latex/rational_quivers.tex` (census `RQ2-1.10`, clauses `RQ2-1.10-C2`, `RQ2-1.10-C3`).

## Main definitions / results
* `RationalQuivers.RationalQuiver.pathCompose` — the composite `f_{e_n} ∘ … ∘ f_{e_1}` of a family
  of edge maps along a path of a **classical** quiver, using mathlib's `Quiver.Path` on the D4
  bridge `RQuiver.instQuiverV`; `RationalQuivers.RationalQuiver.Rep.pathMap` is its instance at a
  representation.  Factoring through the classical quiver is what makes nilpotency manifestly
  invariant under base change.
* `RationalQuivers.RationalQuiver.Rep.IsNilpotent` — a representation is *nilpotent* if all
  composites along paths of some fixed length and beyond vanish.
* `RationalQuivers.RationalQuiver.RepNil` — `Rep^nil(Γ_K)`, mathlib's
  `ObjectProperty.FullSubcategory` of `Rep(Γ_K)` cut out by nilpotency.

## Implementation notes

**The source never defines "nilpotent".**  `def:rationalrepresentations`'s following definition
introduces `Rep^nil(Γ_K)` as "the full subcategory consisting of finite-dimensional *nilpotent*
`K`-rational representations", and the Introduction speaks of "nilpotent complex representations of
the quiver with relation", but no definition is given anywhere in the manuscript
(`census/NOTATION.md` §11 records the same gap for species, ATTESTATION **AN-31**).  We take the
standard Gabriel–Gelfand reading, which is also the one the §5 verification uses: `M` is nilpotent
if there is `n` such that the composite of edge maps along **every** path of length `≥ n` is zero.
This is recorded as a project definition in `workflow/ledger/DEFINITIONS.tsv` (row `DEF-S2-04`)
together with the weaker alternative it is *not* — "the total edge endomorphism of `⊕_v M(v)` is
nilpotent", which admits cancellation between parallel paths and would make `Rep^nil` strictly
larger.

**mathlib's `Quiver.Path`.**  Paths are mathlib's, taken over the D4 bridge instance
`RQuiver.instQuiverV` of `Quiver/Basic.lean`, so nothing about paths is restated here
(`CONVENTIONS.md` §6 ladder step 1).  An arrow `a ⟶ b` of that instance is an edge `e` together
with proofs `s(e) = a`, `t(e) = b`; `Rep.arrowMap` transports `φ_e` along them.
-/

universe u

namespace RationalQuivers

namespace RationalQuiver

open CategoryTheory

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The edge map `φ_e` of an arrow `a ⟶ b` of the D4 bridge quiver on `Γ.V`, transported to a map
`M(a) → M(b)` along the arrow's own proofs `s(e) = a`, `t(e) = b`.

@census none (helper)
-/
def arrowCompose {Q : RQuiver.{u}} (X : Q.V → Type u) [∀ v, AddCommGroup (X v)]
    [∀ v, Module L (X v)] (f : ∀ e : Q.E, X (Q.source e) →ₗ[L] X (Q.target e))
    {a b : Q.V} (g : a ⟶ b) : X a →ₗ[L] X b :=
  (famCast X g.2.2).toLinearMap ∘ₗ f g.1 ∘ₗ (famCast X g.2.1).symm.toLinearMap

/-- The composite of a family of edge maps along a path of a classical quiver: `f_{e_n} ∘ … ∘
f_{e_1}` for a path `e_1 … e_n`.

Like `arrowCompose`, this depends only on the **classical** quiver `Q` and the family `X`, never
on a rational structure.  That is what makes `Rep.baseChange_isNilpotent` hold: `M_{E'}` has the
same `Q`, `X` and `f` as `M`, so the two path composites are the same term.

@census none (helper)
-/
def pathCompose {Q : RQuiver.{u}} (X : Q.V → Type u) [∀ v, AddCommGroup (X v)]
    [∀ v, Module L (X v)] (f : ∀ e : Q.E, X (Q.source e) →ₗ[L] X (Q.target e)) :
    ∀ {a b : Q.V}, Quiver.Path a b → (X a →ₗ[L] X b)
  | _, _, Quiver.Path.nil => LinearMap.id
  | _, _, Quiver.Path.cons p g => arrowCompose X f g ∘ₗ pathCompose X f p

/-- The empty path acts as the identity.  @census none (helper) -/
@[simp]
theorem pathCompose_nil {Q : RQuiver.{u}} (X : Q.V → Type u) [∀ v, AddCommGroup (X v)]
    [∀ v, Module L (X v)] (f : ∀ e : Q.E, X (Q.source e) →ₗ[L] X (Q.target e)) (a : Q.V) :
    pathCompose X f (Quiver.Path.nil : Quiver.Path a a) = LinearMap.id := by
  simp [pathCompose]

/-- Path composites are built one arrow at a time.  @census none (helper) -/
@[simp]
theorem pathCompose_cons {Q : RQuiver.{u}} (X : Q.V → Type u) [∀ v, AddCommGroup (X v)]
    [∀ v, Module L (X v)] (f : ∀ e : Q.E, X (Q.source e) →ₗ[L] X (Q.target e))
    {a b c : Q.V} (p : Quiver.Path a b) (g : b ⟶ c) :
    pathCompose X f (p.cons g) = arrowCompose X f g ∘ₗ pathCompose X f p := by
  simp [pathCompose]

namespace Rep

variable {Γ : RationalQuiver K L}

/-- The edge map `φ_e` of an arrow `a ⟶ b` of the D4 bridge quiver on `Γ.V`, transported to a map
`M(a) → M(b)` along the arrow's own proofs `s(e) = a`, `t(e) = b`.

@census none (helper)
-/
def arrowMap (M : Rep Γ) {a b : Γ.V} (g : a ⟶ b) : M.M a →ₗ[L] M.M b :=
  arrowCompose (Q := Γ.toRQuiver) M.M M.φEdge g

/-- The composite of the edge maps along a path of the underlying classical quiver: `φ_{e_n} ∘ …
∘ φ_{e_1}` for a path `e_1 … e_n` from `a` to `b`.

@census none (helper)
-/
def pathMap (M : Rep Γ) {a b : Γ.V} (p : Quiver.Path a b) : M.M a →ₗ[L] M.M b :=
  pathCompose (Q := Γ.toRQuiver) M.M M.φEdge p

/-- The empty path acts as the identity.  @census none (helper) -/
@[simp]
theorem pathMap_nil (M : Rep Γ) (a : Γ.V) :
    M.pathMap (Quiver.Path.nil : Quiver.Path a a) = LinearMap.id :=
  pathCompose_nil _ _ a

/-- Path composites are built one arrow at a time.  @census none (helper) -/
@[simp]
theorem pathMap_cons (M : Rep Γ) {a b c : Γ.V} (p : Quiver.Path a b) (g : b ⟶ c) :
    M.pathMap (p.cons g) = M.arrowMap g ∘ₗ M.pathMap p :=
  pathCompose_cons _ _ p g

/-- **Nilpotent representation** (the notion the source names but does not define; see the
module's implementation notes and `ledger/DEFINITIONS.tsv` row `DEF-S2-04`).

A representation `M` of `Γ_K` is *nilpotent* if there is an `n` such that the composite of the
edge maps along every path of length at least `n` in the underlying classical quiver is zero.

@census none (project definition consumed by clause `RQ2-1.10-C2`)
-/
def IsNilpotent (M : Rep Γ) : Prop :=
  ∃ n : ℕ, ∀ (a b : Γ.V) (p : Quiver.Path a b), n ≤ p.length →
    pathCompose (Q := Γ.toRQuiver) M.M M.φEdge p = 0

/-- **G5 non-vacuity**: the tautological representation with zero edge maps is nilpotent, and its
spaces `M(v) = L` and semi-linear structure maps `φ_{v,σ} = σ` are nonzero — so `Rep^nil(Γ_K)` is
inhabited by something other than the zero representation.

@census none (helper: G5 inhabitant of clause `RQ2-1.10-C2`)
-/
theorem constLZero_isNilpotent (Γ : RationalQuiver K L) : (constLZero Γ).IsNilpotent := by
  refine ⟨1, ?_⟩
  rintro a b (_ | ⟨p, g⟩) h
  · exact absurd h (by simp)
  · have hedge : (constLZero Γ).φEdge g.1 = 0 := by
      show LinearMap.mulLeft L (0 : L) = 0
      exact LinearMap.ext fun m => by simp
    have harr : arrowCompose (Q := Γ.toRQuiver) (constLZero Γ).M (constLZero Γ).φEdge g = 0 := by
      simp only [arrowCompose, hedge, LinearMap.zero_comp, LinearMap.comp_zero]
    rw [pathCompose_cons, harr, LinearMap.zero_comp]

end Rep

/-- **`Rep^nil(Γ_K)`** (unlabelled, §1.3 of the source).

The **full** subcategory of `Rep(Γ_K)` consisting of the finite-dimensional **nilpotent**
`K`-rational representations of `Γ_K` (clauses `RQ2-1.10-C2`, `RQ2-1.10-C3`).  It is mathlib's
`CategoryTheory.ObjectProperty.FullSubcategory` for the property `IsNilpotent`, so its category
structure and the fullness and faithfulness of the inclusion `Rep^nil(Γ_K) ↪ Rep(Γ_K)` are
mathlib's, not ours (`RepNil.ι_full`, `RepNil.ι_faithful`).

@census none (the category named by `RQ2-1.10`, claimed by `FDRep.instCategory`)
@source    UNLABELED-rep-categories
@clauses   RQ2-1.10-C2, RQ2-1.10-C3
@imports   none
@divergence none
-/
def RepNil (Γ : RationalQuiver K L) : ObjectProperty (FDRep Γ) :=
  fun M => M.toRep.IsNilpotent

/-- Clause `RQ2-1.10-C3`: `Rep^nil(Γ_K)` is a **full** subcategory of `Rep(Γ_K)` — the inclusion
functor is full.

@census none (helper: clause `RQ2-1.10-C3`)
-/
instance RepNil_ι_full (Γ : RationalQuiver K L) : (RepNil Γ).ι.Full := inferInstance

/-- Clause `RQ2-1.10-C3`: the inclusion `Rep^nil(Γ_K) ↪ Rep(Γ_K)` is faithful.

@census none (helper: clause `RQ2-1.10-C3`)
-/
instance RepNil_ι_faithful (Γ : RationalQuiver K L) : (RepNil Γ).ι.Faithful := inferInstance

/-- **G5 non-vacuity**: `Rep^nil(Γ_K)` is inhabited by a representation with nonzero spaces and
a nontrivial semi-linear Galois action.

@census none (helper: G5 inhabitant of clause `RQ2-1.10-C2`)
-/
def RepNil.constLZero (Γ : RationalQuiver K L) : (RepNil Γ).FullSubcategory where
  obj := FDRep.constLZero Γ
  property := Rep.constLZero_isNilpotent Γ

/-! ### Non-vacuity of nilpotency (`stages/S2/DESIGN-NOTES.md` §9, probes 3 and 4)

`IsNilpotent` would be worthless if it were satisfied by everything, and `Rep^nil(Γ_K)` would be
a vacuous notion if it were all of `Rep(Γ_K)`.  The witness is the **one-loop quiver**: its
tautological representation `constLOne` has identity edge maps, so the composite along the path of
length `n` is the identity for every `n`, and no `n` makes all long paths vanish.
-/

namespace Rep

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The one-loop classical quiver: one vertex, one edge from it to itself.  The witness for the
non-vacuity of `IsNilpotent`.

@census none (G5 probe witness)
-/
def loopQuiver : RQuiver.{u} where
  V := PUnit
  E := PUnit
  source _ := PUnit.unit
  target _ := PUnit.unit
  finite_V := inferInstance
  finite_E := inferInstance

/-- The one-loop quiver with the split (trivial) `K`-rational structure.

@census none (G5 probe witness)
-/
def loopRQ (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L] :
    RationalQuiver K L where
  toRQuiver := loopQuiver
  ρ := 1
  smooth_V v := by
    have h : {σ : Gal(L/K) |
        (((RQuiver.Aut.toPermV loopQuiver).comp 1) σ) v = v} = Set.univ := by
      ext σ; simp
    rw [h]; exact isOpen_univ
  smooth_E e := by
    have h : {σ : Gal(L/K) |
        (((RQuiver.Aut.toPermE loopQuiver).comp 1) σ) e = e} = Set.univ := by
      ext σ; simp
    rw [h]; exact isOpen_univ

section Probes

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- The unique vertex of the one-loop quiver.  Kept as a `def` with the type written as
`(loopRQ K L).V`, so that the `Quiver` instance of the D4 bridge is found.

@census none (G5 probe witness)
-/
def loopVertex : (loopRQ K L).V := PUnit.unit

/-- The loop, as an arrow of the D4 bridge quiver.  @census none (G5 probe witness) -/
def loopArrow : loopVertex K L ⟶ loopVertex K L := ⟨PUnit.unit, rfl, rfl⟩

/-- The path that goes round the loop `n` times.  @census none (G5 probe witness) -/
def loopPath : ∀ n : ℕ, Quiver.Path (loopVertex K L) (loopVertex K L)
  | 0 => Quiver.Path.nil
  | n + 1 => (loopPath n).cons (loopArrow K L)

/-- Going round the loop `n` times is a path of length `n`.  @census none (G5 probe witness) -/
theorem loopPath_length : ∀ n : ℕ, (loopPath K L n).length = n
  | 0 => rfl
  | n + 1 => by
      show (loopPath K L n).length + 1 = n + 1
      rw [loopPath_length n]

/-- Every power of the loop acts as the identity on `constLOne`.

@census none (G5 probe witness)
-/
theorem pathCompose_loopPath (n : ℕ) :
    pathCompose (Q := (loopRQ K L).toRQuiver) (constLOne (loopRQ K L)).M
      (constLOne (loopRQ K L)).φEdge (loopPath K L n) = LinearMap.id := by
  have harr : arrowCompose (Q := (loopRQ K L).toRQuiver) (constLOne (loopRQ K L)).M
      (constLOne (loopRQ K L)).φEdge (loopArrow K L) = LinearMap.id := by
    refine LinearMap.ext fun m => ?_
    exact one_mul (M := L) m
  induction n with
  | zero =>
      show pathCompose (Q := (loopRQ K L).toRQuiver) _ _ Quiver.Path.nil = LinearMap.id
      exact pathCompose_nil _ _ _
  | succ n ih =>
      show pathCompose _ _ ((loopPath K L n).cons (loopArrow K L)) = LinearMap.id
      rw [pathCompose_cons, harr, ih, LinearMap.id_comp]

/-- **G5 probe 3**: the tautological representation of the one-loop quiver is **not** nilpotent.
So `IsNilpotent` is not vacuously true, and the definition really does exclude something.

@census none (G5 non-vacuity probe, `stages/S2/DESIGN-NOTES.md` §9 probe 3)
-/
theorem not_isNilpotent_constLOne_loop : ¬ (constLOne (loopRQ K L)).IsNilpotent := by
  rintro ⟨n, hn⟩
  have h := hn (loopVertex K L) (loopVertex K L) (loopPath K L n)
    (by rw [loopPath_length])
  rw [pathCompose_loopPath K L n] at h
  have h1 : (1 : L) = 0 := congrFun (congrArg (fun f : L →ₗ[L] L => (f : L → L)) h) 1
  exact one_ne_zero h1

/-- **G5 probe 4**: `Rep^nil(Γ_K)` is **not** all of `Rep(Γ_K)` — for the one-loop quiver the
tautological object is finite-dimensional but not nilpotent.  So the full subcategory `RepNil` is
proper, and clause `RQ2-1.10-C2` is not vacuous.

@census none (G5 non-vacuity probe, `stages/S2/DESIGN-NOTES.md` §9 probe 4)
-/
theorem repNil_ne_univ :
    ¬ ∀ M : FDRep (loopRQ K L), RepNil (loopRQ K L) M := fun h =>
  not_isNilpotent_constLOne_loop K L (h (FDRep.constLOne (loopRQ K L)))

end Probes

end Rep

end RationalQuiver

end RationalQuivers
