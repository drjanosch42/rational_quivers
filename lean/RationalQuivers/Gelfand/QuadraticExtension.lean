module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Perfect
public import RationalQuivers.Gelfand.GaloisFacts

@[expose] public section

/-!
# Quadratic Galois extensions `D'/E` and the constructed `E(√-1)`, over a characteristic-zero base field

Stage **S10**, prerequisite of census row `RQ-5.08` (`rmk:generalbases`); coordinator rulings
`R-S10-3` (pin the non-split splitting field to the **constructed** `E(√-1)`), `R-S10-4` (the
construction is cheap — measured, probes `P1`–`P5`) and `R-S10-8` (module set).

*(v2, 2026-10-20, docstring-only `R-PROC-4` amendment T2-a5, obligation `O-V2-2`.)*  On the v2 line
this module belongs to stage T2 (perimeter amendment T2-a1).  Its central datum is the structure
`SqrtNegOneExt E`, which since T2-a2 is **any** quadratic Galois extension `D'/E`, in general without
`√-1`; the constructed `E(√-1)` below is one inhabitant (`SqrtNegOneExt.std`).  The text below and the
docstrings of this file keep the v1 references: stages S7/S8/S10, census ids `RQ-x.yy` (mapped to
`RQ2-` ids by `CROSSWALK-v1-v2.tsv`), `Gelfand/GeneralBase.lean`, `Gelfand.targetNonSplit` and
`Gelfand.HCQ` (`HCQ ℓ` below).  That file and those two declarations were deleted with the v1 Q-chain at
WP-13 (`44df340`; `Gelfand.HCQ` with `Gelfand/Category.lean` at `9c6b193`), and no declaration of those
names exists; their roles live on.  `GeneralBase.lean`'s relation-carrying quiver-side base change
(`repNilRelGel`, `qBCssRel`, `qBCnsRel`) was relocated to `Gelfand/BaseChange/QuiverRel.lean` (T4).
`targetNonSplit ℓ E D.carrier D.card_gal` was `gelfandOfCardTwo E D.carrier D.card_gal` for `ℓ ≥ 1`
and `cyclicOfCardTwo E D.carrier D.card_gal` for `ℓ = 0`, which are used directly
(`RationalStructure.gelfandQ`, `repNilRelGel`; `Cyclic.cyclicQ`).  The comparison with `HCQ ℓ` owed at
v1's G4 is `Gelfand.Compat.hcEquivHCEObj` (T4; note on `SqrtNegOneExt.qi`).  `Ei.map`, `Ei.liftSplit`, `Ei.algebraMapEi`, `Ei.algebraSplit`, `Ei.toQi` and
`Ei.equivQi` are used by no other module.

S7 and S8 work over the single quadratic extension `ℚ[√-1]/ℚ` (`HC.Qi = ℚ(i) ⊆ ℂ`, whose Galois
facts are `Gelfand/GaloisFacts.lean`'s).  `RQ-5.08` is about **every** characteristic-zero `E`, so
its non-split branch needs `E(√-1)` as a *construction*, with `[E(√-1) : E] = 2`,
`#Gal(E(√-1)/E) = 2` and the involution itself.  `Gelfand/GeneralBase.lean`'s standing
`@divergence` observed that the tree could not build that field; this module builds it.

## The two classes

`√-1 ∈ E` is carried as the **data** class `SqrtNegOne E` (a chosen `i` with `i * i = -1`), not as
`∃ i, i * i = -1`.  The reason is `liftSplit` below: the `E`-algebra map `E(√-1) → E''` for a
splitting `E''` is `√-1 ↦ i''`, so it *depends on the choice* of `i''`, and a `Prop`-valued
hypothesis would force a `Classical.choice` inside a definition.  `√-1 ∉ E` is the `Prop` class
`NoSqrtNegOne E`, from which `Fact (Irreducible (X² + 1))`, and hence `Field (Ei E)`, is an
instance.

## Main definitions / results

* `RationalQuivers.Gelfand.Ei` — `E(√-1) := AdjoinRoot (X² - C (-1))`, an `abbrev` so that
  mathlib's `AdjoinRoot` instances apply without re-declaration.
* `Ei.sqrt`, `Ei.sqrt_mul_sqrt` — the root and its defining equation.
* `Ei.finrank`, `Ei.instIsGalois`, `Ei.card_gal` — `[E(√-1) : E] = 2`, the extension is Galois
  (found by instance search, exactly as `Qi.instIsGalois` is), `#Gal = 2`.  `Ei.card_gal` supplies
  `SqrtNegOneExt.std`'s `card_gal` (in v1, `Gelfand.targetNonSplit`'s `hc` argument) as a
  **conclusion** rather than a binder.
* `Ei.conj`, `Ei.conj_ne_one` — the non-trivial element of `Gal(E(√-1)/E)`, `√-1 ↦ -√-1`; the
  general-`E` counterpart of S7's `galConj`, and the semi-linearity datum of
  `Gelfand/GeneralBaseCategory.lean`'s `RationalSetupOver`.
* `Ei.map`, `Ei.liftSplit` (with `Ei.algebraMapEi`, `Ei.algebraSplit`) — the functoriality
  `E → E''` induces `E(√-1) → E''(√-1)` resp. `E(√-1) → E''`: the data that `RQ-5.08-C4`'s `nn`
  and `ns` shapes tensor over.  Ruling `R-S10-3` records why this is needed — the old binder shape
  related the two splitting fields by nothing at all, so no proof could discharge it.  Both are
  supplied as `def`s and activated with `letI` at the use site: made global instances they would
  fire on every `Algebra` goal between two `AdjoinRoot` types.
* `instNoSqrtNegOneQ`, `instSqrtNegOneQi`, `Ei.toQi`, `Ei.equivQi` — the two instantiations
  `R-S10-6` restricts `C1`/`C2`/`C3` to, and the bridge `Ei ℚ ≃ₐ[ℚ] ℚ[√-1]` between the
  constructed splitting field and the tree's own `HC.Qi`.
* `SqrtNegOneExt E` — a quadratic Galois extension `D'/E` (the name is historical, see its
  docstring), with `SqrtNegOneExt.conj`, `conj_conj`, `eq_conj_of_ne_one`; its inhabitants here
  are `SqrtNegOneExt.std E` (the constructed `E(√-1)`) and `SqrtNegOneExt.qi` (`HC.Qi`), and in
  general `SqrtNegOneExt.ofNonSquare` (stage T6).

## G5

`Ei ℚ` inhabits `Ei` at a field with no `√-1`; `ℚ[√-1]` inhabits `SqrtNegOne`.  Non-degeneracy:
`Ei.conj_ne_one` — the Galois group really has two elements, so the construction is not secretly
`E` itself.
-/

universe u

namespace RationalQuivers.Gelfand

open Polynomial RationalQuivers.HC

/-- **`√-1 ∈ E`, as data**: a chosen square root of `-1`.  @census none (helper) -/
class SqrtNegOne (E : Type u) [Field E] where
  /-- the chosen square root of `-1` -/
  i : E
  /-- it squares to `-1` -/
  i_mul_i : i * i = -1

/-- The chosen square root of `-1` in a field that has one, as a function of the field.  @census none (helper) -/
abbrev sqrtI (E : Type u) [Field E] [SqrtNegOne E] : E := SqrtNegOne.i

/-- **`√-1 ∉ E`**.  @census none (helper) -/
class NoSqrtNegOne (E : Type u) [Field E] : Prop where
  /-- no element of `E` squares to `-1` -/
  no_sqrt : ∀ b : E, b * b ≠ -1

/-- `X² + 1 ∈ E[X]`, written `X² - C (-1)` so Kummer theory applies.  @census none (helper) -/
noncomputable abbrev sqPoly (E : Type u) [Field E] : E[X] := X ^ 2 - C (-1 : E)

/-- `X² + 1` is irreducible over `E` when `-1` is not a square in `E`.  @census none (helper) -/
theorem irreducible_sqPoly (E : Type u) [Field E] [NoSqrtNegOne E] :
    Irreducible (sqPoly E) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two
    (fun b hb => NoSqrtNegOne.no_sqrt b (by rw [← hb]; ring))

instance instFactIrreducibleSqPoly (E : Type u) [Field E] [NoSqrtNegOne E] :
    Fact (Irreducible (sqPoly E)) := ⟨irreducible_sqPoly E⟩

/-- **`E(√-1)`**.  @census none (helper) -/
noncomputable abbrev Ei (E : Type u) [Field E] [NoSqrtNegOne E] : Type u := AdjoinRoot (sqPoly E)

namespace Ei

variable (E : Type u) [Field E] [NoSqrtNegOne E]

/-- `√-1 ∈ E(√-1)`.  @census none (helper) -/
noncomputable def sqrt : Ei E := AdjoinRoot.root (sqPoly E)

theorem sqrt_mul_sqrt : sqrt E * sqrt E = -1 := by
  have h0 : (AdjoinRoot.root (sqPoly E)) ^ 2 - (algebraMap E (Ei E)) (-1) = 0 := by
    simpa using AdjoinRoot.eval₂_root (sqPoly E)
  have h1 : (AdjoinRoot.root (sqPoly E)) ^ 2 = -1 := by
    have := sub_eq_zero.mp h0; simpa using this
  rw [show sqrt E * sqrt E = (AdjoinRoot.root (sqPoly E)) ^ 2 by rw [sqrt]; ring, h1]

/-- `[E(√-1) : E] = 2`.  @census none (helper) -/
theorem finrank : Module.finrank E (Ei E) = 2 := by
  rw [(AdjoinRoot.powerBasis (K := E) (f := sqPoly E)
        (Fact.out (p := Irreducible (sqPoly E))).ne_zero).finrank,
      AdjoinRoot.powerBasis_dim]
  exact natDegree_X_pow_sub_C

noncomputable instance instFiniteDimensional : FiniteDimensional E (Ei E) :=
  (AdjoinRoot.powerBasis (K := E) (f := sqPoly E)
    (Fact.out (p := Irreducible (sqPoly E))).ne_zero).finite

noncomputable instance instIsQuadraticExtension : Algebra.IsQuadraticExtension E (Ei E) :=
  ⟨finrank E⟩

section CharZeroPart
variable [CharZero E]

noncomputable instance instIsGalois : IsGalois E (Ei E) := inferInstance

/-- `#Gal(E(√-1)/E) = 2`.  @census none (helper) -/
theorem card_gal : Nat.card ((Ei E) ≃ₐ[E] (Ei E)) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, finrank]

/-- `E(√-1)` has characteristic zero.  @census none (helper) -/
instance instCharZero : CharZero (Ei E) :=
  charZero_of_injective_algebraMap (algebraMap E (Ei E)).injective

/-- The non-trivial element of `Gal(E(√-1)/E)`, as an algebra hom: `√-1 ↦ -√-1`.  @census none (helper) -/
noncomputable def conjHom : Ei E →ₐ[E] Ei E :=
  AdjoinRoot.liftAlgHom (sqPoly E) (Algebra.ofId E (Ei E)) (-(sqrt E)) (by
    have h : sqrt E * sqrt E = -1 := sqrt_mul_sqrt E
    have h2 : (-(sqrt E)) ^ 2 = (-1 : Ei E) := by rw [neg_sq, sq]; exact h
    simp only [sqPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, h2]
    simp)

@[simp] theorem conjHom_sqrt : conjHom E (sqrt E) = -(sqrt E) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem conjHom_comp_conjHom : (conjHom E).comp (conjHom E) = AlgHom.id E (Ei E) :=
  AdjoinRoot.algHom_ext (by
    show conjHom E (conjHom E (sqrt E)) = sqrt E
    rw [conjHom_sqrt, map_neg, conjHom_sqrt, neg_neg])

theorem conjHom_conjHom (x : Ei E) : conjHom E (conjHom E x) = x :=
  congrArg (fun g : Ei E →ₐ[E] Ei E => g x) (conjHom_comp_conjHom E)

/-- **`Gal(E(√-1)/E)`'s non-trivial element**, as an `E`-algebra equivalence.  @census none (helper) -/
noncomputable def conj : Ei E ≃ₐ[E] Ei E :=
  AlgEquiv.ofAlgHom (conjHom E) (conjHom E) (conjHom_comp_conjHom E) (conjHom_comp_conjHom E)

@[simp] theorem conj_apply (x : Ei E) : conj E x = conjHom E x := rfl

@[simp] theorem conj_sqrt : conj E (sqrt E) = -(sqrt E) := conjHom_sqrt E

theorem sqrt_ne_zero : sqrt E ≠ 0 := by
  intro h0
  have h := sqrt_mul_sqrt E
  rw [h0, mul_zero] at h
  exact (neg_ne_zero.mpr (one_ne_zero (α := Ei E))) h.symm

/-- `conj ≠ 1`: the extension really is quadratic and its Galois group really is `ℤ/2`.  @census none (helper) -/
theorem conj_ne_one : conj E ≠ 1 := by
  intro h
  have h1 : conj E (sqrt E) = sqrt E := by rw [h]; rfl
  rw [conj_sqrt] at h1
  have h2 : (2 : Ei E) * sqrt E = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact (two_ne_zero (α := Ei E)) h'
  · exact sqrt_ne_zero E h'

end CharZeroPart

/-! ### Functoriality: `E → E''` induces `E(√-1) → E''(√-1)` -/

section Map

variable (E'' : Type u) [Field E''] [Algebra E E'']

/-- The `E`-algebra map `E(√-1) → E''(√-1)` induced by `E → E''`, as a ring homomorphism:
`√-1 ↦ √-1`.  This is the datum the `nn` shape of `RQ-5.08-C4` tensors over (`R-S10-3`).

@census none (helper) -/
noncomputable def map [NoSqrtNegOne E''] : Ei E →+* Ei E'' :=
  AdjoinRoot.lift ((algebraMap E'' (Ei E'')).comp (algebraMap E E'')) (sqrt E'') (by
    have h : sqrt E'' * sqrt E'' = -1 := sqrt_mul_sqrt E''
    have h2 : sqrt E'' ^ 2 = (-1 : Ei E'') := by rw [sq]; exact h
    simp only [sqPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, h2]
    simp)

@[simp] theorem map_sqrt [NoSqrtNegOne E''] : map E E'' (sqrt E) = sqrt E'' :=
  AdjoinRoot.lift_root _

@[simp] theorem map_algebraMap [NoSqrtNegOne E''] (a : E) :
    map E E'' (algebraMap E (Ei E) a) = algebraMap E'' (Ei E'') (algebraMap E E'' a) :=
  AdjoinRoot.lift_of _

/-- `E(√-1) → E''(√-1)` as an `Algebra` structure, so that `E''(√-1) ⊗_{E(√-1)} -` is available.
Supplied as a `def`, activated at the use site with `letI`: making it a global instance would
fire on every `Algebra` goal between two `AdjoinRoot` types.

@census none (helper) -/
@[implicit_reducible]
noncomputable def algebraMapEi [NoSqrtNegOne E''] : Algebra (Ei E) (Ei E'') :=
  (map E E'').toAlgebra

/-- The `E`-algebra map `E(√-1) → E''` when `√-1 ∈ E''`: `√-1 ↦ i`.  This is the datum the `ns`
shape of `RQ-5.08-C4` tensors over.

@census none (helper) -/
noncomputable def liftSplit [SqrtNegOne E''] : Ei E →+* E'' :=
  AdjoinRoot.lift (algebraMap E E'') (sqrtI E'') (by
    have h : sqrtI E'' * sqrtI E'' = -1 := SqrtNegOne.i_mul_i
    have h2 : sqrtI E'' ^ 2 = (-1 : E'') := by rw [sq]; exact h
    simp only [sqPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, h2]
    simp)

@[simp] theorem liftSplit_sqrt [SqrtNegOne E''] : liftSplit E E'' (sqrt E) = sqrtI E'' :=
  AdjoinRoot.lift_root _

@[simp] theorem liftSplit_algebraMap [SqrtNegOne E''] (a : E) :
    liftSplit E E'' (algebraMap E (Ei E) a) = algebraMap E E'' a :=
  AdjoinRoot.lift_of _

/-- `E(√-1) → E''` as an `Algebra` structure (`letI` at the use site, as `algebraMapEi`).  @census none (helper) -/
@[implicit_reducible]
noncomputable def algebraSplit [SqrtNegOne E''] : Algebra (Ei E) E'' :=
  (liftSplit E E'').toAlgebra

end Map

end Ei

/-! ## `SqrtNegOneExt` — a quadratic Galois extension `D'/E` (`R-S10-10`; root-free since v2 T2-a2) -/

/-- **A quadratic Galois extension `D'/E`**, bundled with its compatibility data.

**The name is historical.**  Until the v2 amendment `T2-a2` (R-PROC-4, written authorization
2026-10-18, variant (ii) of `thm:twistedEEequivalence`) the structure also carried a chosen square
root of `-1` in the carrier (fields `sqrt`, `sqrt_mul_sqrt`).  No declaration of the general-`E`
engine used that root in type or value (closure measurement S-1(d); only `ζ := a - c(a)` is used),
so the fields were removed: the datum is now exactly a quadratic Galois extension, in general
**without** `√-1`.  Declarations that genuinely need a square root `s` of `-1` in `D'` (the T4
base-change compatibility, `Gelfand/BaseChange/NNHC.lean`, and `Gelfand/Compat.lean`) take it as
an explicit argument `(s : D.carrier) (hs : s * s = -1)`.  The name `SqrtNegOneExt` is kept
because a rename would change every signature over `D` (plan `VARIANT-II-T4B-PLAN.md` §1.2).

The bundle exists because of coordinator ruling **`R-S10-10`** (amending `R-S10-3`).
`R-S10-3`'s diagnosis was right — the previous `qBC_*` binders related the two splitting fields by
*nothing at all*, so no proof could ever discharge them — but its remedy, pinning the splitting
field to the constructed `Ei E`, buys a category-level transport at `E = ℚ` (where the tree's own
splitting field is `HC.Qi = ℚ(i) ⊆ ℂ`, not `ℚ[X]/(X²+1)`) purely to repair a design choice.  A
**bundle** discharges the requirement equally well and makes `E = ℚ` definitional:
`SqrtNegOneExt.qi` *is* `HC.Qi`, so `RQ-5.05`/`RQ-5.07` instantiate with **no field-level**
transport.  (A **structure-level** comparison `HCEObj ℓ ℚ qi ≌ HCQ ℓ` was still owed at v1's G4 — see
`SqrtNegOneExt.qi` below, `V-S10R-1`.  `Gelfand.HCQ` no longer exists; the v2 form of that comparison
is `Gelfand.Compat.hcEquivHCEObj`, see the note there.)

Every field is load-bearing, not merely projected — the `V-S8-13` dead-`Realization` shape is what
this avoids.  `carrier` and the four instance fields were the arguments of v1's `Gelfand.targetNonSplit`
(deleted at WP-13), and `card_gal` was its `hc`; `card_gal` also defines `conj` below.

Non-emptiness is a **conclusion**, never an assumption: `SqrtNegOneExt.std E` (the constructed
`E(√-1)`) for an arbitrary characteristic-zero `E` with `√-1 ∉ E`, `SqrtNegOneExt.qi` at `E = ℚ`,
and, without `√-1` in the carrier, `SqrtNegOneExt.ofNonSquare` (stage T6,
`Gelfand/TwistedForms/Inhabitants.lean`).

@census none (auxiliary; the quadratic-extension datum of `RQ-5.08`'s non-split branch, `R-S10-10`,
and of `RQ2-5.22`..`RQ2-5.24`) -/
structure SqrtNegOneExt (E : Type u) [Field E] [CharZero E] where
  /-- the extension field `D'` -/
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra E carrier]
  [isGalois : IsGalois E carrier]
  [finiteDimensional : FiniteDimensional E carrier]
  /-- `#Gal(D'/E) = 2` — a datum rather than a binder (v1's `targetNonSplit`'s `hc`) -/
  card_gal : Nat.card (carrier ≃ₐ[E] carrier) = 2

attribute [instance] SqrtNegOneExt.field SqrtNegOneExt.algebra SqrtNegOneExt.isGalois
  SqrtNegOneExt.finiteDimensional

namespace SqrtNegOneExt

variable {E : Type u} [Field E] [CharZero E] (D : SqrtNegOneExt E)

/-- `D'` has characteristic zero, inherited from `E`.  Needed by
`HasGeneralizedInfinitesimalCharacter`, which is stated over a `ℚ`-algebra.

@census none (helper) -/
instance instCharZeroCarrier : CharZero D.carrier :=
  charZero_of_injective_algebraMap (algebraMap E D.carrier).injective

/-- Projection of `card_gal` (`rqaudit liveness`).  @census none (helper) -/
theorem card_gal' : Nat.card (D.carrier ≃ₐ[E] D.carrier) = 2 := D.card_gal

/-- **The non-trivial element `c` of `Gal(D'/E)`**, `D'` the carrier of `D` (for `D = std E`,
`D' = E(√-1)`; WP-15 docstring amendment, G2-V2II-F05), the general-`E` counterpart of S7's `galConj`:
the unique element other than `1`, which exists because the group has exactly two elements.

@census none (helper) -/
noncomputable def conj : D.carrier ≃ₐ[E] D.carrier :=
  ((Nat.card_eq_two_iff' (1 : D.carrier ≃ₐ[E] D.carrier)).mp D.card_gal).choose

theorem conj_ne_one : D.conj ≠ 1 :=
  ((Nat.card_eq_two_iff' (1 : D.carrier ≃ₐ[E] D.carrier)).mp D.card_gal).choose_spec.1

/-- `conj` is *the* non-trivial element: any other one is it.  @census none (helper) -/
theorem eq_conj_of_ne_one {σ : D.carrier ≃ₐ[E] D.carrier} (hσ : σ ≠ 1) : σ = D.conj :=
  ((Nat.card_eq_two_iff' (1 : D.carrier ≃ₐ[E] D.carrier)).mp D.card_gal).choose_spec.2 σ hσ

/-- `conj` is an involution: `Gal(D'/E)` has order two.  @census none (helper) -/
theorem conj_conj (x : D.carrier) : D.conj (D.conj x) = x := by
  have h2 : D.conj * D.conj = 1 := by
    have := pow_card_eq_one' (G := D.carrier ≃ₐ[E] D.carrier) (x := D.conj)
    rwa [D.card_gal, pow_two] at this
  exact congrArg (fun σ : D.carrier ≃ₐ[E] D.carrier => σ x) h2

end SqrtNegOneExt

/-! ## The two instantiations the tree already supports (`R-S10-6`) -/

instance instNoSqrtNegOneQ : NoSqrtNegOne ℚ := ⟨fun b hb => by nlinarith [mul_self_nonneg b]⟩

instance instSqrtNegOneQi : SqrtNegOne (Qi : Type) where
  i := ⟨Complex.I, IntermediateField.subset_adjoin ℚ _ rfl⟩
  i_mul_i := by
    apply Subtype.ext
    simp [Complex.I_mul_I]

/-- `ℚ(√-1)/ℚ` is quadratic.  Instance search does not find `Ei.instIsQuadraticExtension` at the
concrete `E = ℚ` (the goal's `Ei ℚ` is already unfolded to `AdjoinRoot (sqPoly ℚ)` by the time the
discrimination tree is consulted), so it is registered here by hand.

@census none (helper) -/
noncomputable instance instIsQuadraticExtensionEiQ :
    Algebra.IsQuadraticExtension ℚ (Ei ℚ) := Ei.instIsQuadraticExtension ℚ

/-- `ℚ(√-1)/ℚ` is Galois.  Registered by hand at the concrete `E = ℚ`, as above.

@census none (helper) -/
noncomputable instance instIsGaloisEiQ : IsGalois ℚ (Ei ℚ) := Ei.instIsGalois ℚ

/-- **The general-`E` witness for `SqrtNegOneExt`**: the constructed `E(√-1)`.  This is what makes
`R-S10-10`'s bundle a *conclusion* rather than an assumption at arbitrary `E`.

@census none (G5 inhabitant of `SqrtNegOneExt` at arbitrary characteristic-zero `E`) -/
noncomputable def SqrtNegOneExt.std (E : Type u) [Field E] [CharZero E] [NoSqrtNegOne E] :
    SqrtNegOneExt E where
  carrier := Ei E
  card_gal := Ei.card_gal E

@[simp] theorem SqrtNegOneExt.std_carrier (E : Type u) [Field E] [CharZero E] [NoSqrtNegOne E] :
    (SqrtNegOneExt.std E).carrier = Ei E := rfl

/-- **The witness at `E = ℚ`**: the tree's own `HC.Qi = ℚ(i) ⊆ ℂ`, the field `RQ-5.05` and
`RQ-5.07` are stated over.  Because this is the bundle `RQ-5.08`'s `ℚ`-conjuncts use, those two
theorems instantiate with **no field-level transport** — which is what `R-S10-10` bought.

**What is still owed, corrected 2026-09-07 on verifier finding `V-S10R-1`.**  An earlier draft of
this docstring said "no transport of any kind".  That is **false**, and the compiled probe `R2`
(layer 2's, exit 1 with three type mismatches against a passing positive control) settles it:
`RQ-5.05`/`RQ-5.07` are stated on `HC.HCQ ℓ`, whose descent datum is semilinear over `galConj`,
while `RQ-5.08`'s non-split conjuncts are stated on `Gelfand.HCEObj ℓ ℚ qi`, whose descent datum is
semilinear over `qi.conj`.  `SqrtNegOneExt.qi_conj` proves `qi.conj = galConj`, but only
**propositionally** — `SqrtNegOneExt.conj` is a `Classical.choose` of the unique non-trivial Galois
element — so the two are **different structures** and a structure-level equivalence
`HCEObj ℓ ℚ qi ≌ HCQ ℓ` remains a G4 obligation, with `qi_conj` as its ingredient rather than its
substitute.  What the bundle removed is the *field*-level transport along `Ei ℚ ≃ₐ[ℚ] ℚ[√-1]`;
that much is real, and it is a reduction, not a dissolution.

*(v2 note, 2026-10-20, T2-a5; revised 2026-10-21, V-OV2-1, V-OV2-3.)*  The two preceding paragraphs
describe the v1 tree.  `Gelfand.HCQ` (written `HC.HCQ` above; `Gelfand/Category.lean`, deleted at
`9c6b193`) and the v1 statements `RQ-5.05`/`RQ-5.07` on it were deleted with the v1 Q-chain (WP-13).
Their v2 claimants `Gelfand.Rational.E_Q_equivalence` (`RQ2-5.05`) and `cyclic_E_Q_equivalence`
(`RQ2-5.07`), and Theorem A (`RQ2-0.01`, `theoremA`), are stated on `HC ℓ ℚ ImagUnit.qi`
(`Gelfand/Rational.lean`).  The structure-level comparison owed at v1's G4 is discharged in v2 by
`Gelfand.Compat.hcEquivHCEObj` (T4), `HC ℓ E D ≌ HCEObj ℓ E (D.sqrtExt h)` for every `D : ImagUnit E`
and `h : ∃ σ, D.chi σ = -1`: at `E = ℚ`, `D = ImagUnit.qi`, `h = Species.hcQ` it reads
`HC ℓ ℚ ImagUnit.qi ≌ HCEObj ℓ ℚ (ImagUnit.qi.sqrtExt Species.hcQ)`, and the carrier of
`ImagUnit.qi.sqrtExt Species.hcQ` is `Qi`, as is the carrier of `qi`.

@census none (G5 inhabitant of `SqrtNegOneExt` at `E = ℚ`) -/
noncomputable def SqrtNegOneExt.qi : SqrtNegOneExt ℚ where
  carrier := (Qi : Type)
  card_gal := Qi.card_gal

@[simp] theorem SqrtNegOneExt.qi_carrier : SqrtNegOneExt.qi.carrier = (Qi : Type) := rfl

/-- The `ℚ`-algebra map `ℚ(√-1) → ℚ[√-1]`, `√-1 ↦ i`.  @census none (helper) -/
noncomputable def Ei.toQi : Ei ℚ →ₐ[ℚ] (Qi : Type) :=
  AdjoinRoot.liftAlgHom (sqPoly ℚ) (Algebra.ofId ℚ (Qi : Type)) (sqrtI (Qi : Type)) (by
    have h2 : sqrtI (Qi : Type) ^ 2 = (-1 : (Qi : Type)) := by
      rw [sq]; exact SqrtNegOne.i_mul_i
    simp only [sqPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, h2]
    simp)

/-- **`ℚ(√-1) = ℚ[√-1]`** — the constructed `E(√-1)` at `E = ℚ` is the tree's own `Qi`.

This is the bridge `R-S10-6`'s instantiation at `E = ℚ` needed in v1: `RQ-5.05`/`RQ-5.07` were
stated over `HC.Qi = ℚ(i) ⊆ ℂ`, whereas `RQ-5.08`'s non-split branch was stated over the constructed
`Ei ℚ = ℚ[X]/(X²+1)` (`R-S10-3` pins the splitting field to the construction).

@census none (helper) -/
noncomputable def Ei.equivQi : Ei ℚ ≃ₐ[ℚ] (Qi : Type) :=
  AlgEquiv.ofBijective Ei.toQi (by
    have hinj : Function.Injective (Ei.toQi : Ei ℚ →ₐ[ℚ] (Qi : Type)) :=
      Ei.toQi.toRingHom.injective
    have hrank : Module.finrank ℚ (Ei ℚ) = Module.finrank ℚ (Qi : Type) := by
      rw [Ei.finrank, Qi.finrank_eq_two]
    have hlin : Function.Injective (Ei.toQi.toLinearMap) := hinj
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hlin⟩)

@[simp] theorem Ei.equivQi_sqrt : Ei.equivQi (Ei.sqrt ℚ) = sqrtI (Qi : Type) :=
  AdjoinRoot.liftAlgHom_root (sqPoly ℚ) (Algebra.ofId ℚ (Qi : Type)) (sqrtI (Qi : Type)) (by
    have h2 : sqrtI (Qi : Type) ^ 2 = (-1 : (Qi : Type)) := by
      rw [sq]; exact SqrtNegOne.i_mul_i
    simp only [sqPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, h2]
    simp)

end RationalQuivers.Gelfand
