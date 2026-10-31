module

public import RationalQuivers.Species.Hom
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Data.Finite.Sigma
public import Mathlib.CategoryTheory.Iso
public import Mathlib.RingTheory.TensorProduct.Pi

@[expose] public section

/-!
# Base change for étale species

Formalizes Definition `def:basechangeforspecies` and the two remarks that follow it, in §2.1 of
`latex/rational_quivers.tex` (census `RQ2-2.05`, `RQ2-2.33`, `RQ2-2.34`).

## The edge formula (finding S3-F2; amended source)

*(Amended 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S3, coordinator ruling
`R-FR-9`, final-release WP-16b, stale item R5.)* The source as first printed defined clause
`RQ2-2.05-C5` as `{}_kM'_ℓ := L'_k ⊗_{L_{π(k)}} ({}_{π(k)}M_{π(ℓ)}) ⊗_{L_{π(ℓ)}} L'_ℓ`. That formula
is **inconsistent** with clause `RQ2-2.05-C7` ("`S ⊗_K N` is an étale `N`-species"). The
counterexample is in the tree: `literal_baseChange_structureMaps_ne` (with
`literal_baseChange_tmul_ne` and the dimension count `literal_baseChange_finrank`). Following the
coordinator's ruling, the tensor products were taken over the **base-changed** vertex algebras
`A_i = L_i ⊗_K N`. **The amended source (census r18, FA-02) now prints exactly that formula**, so
`baseChange` is literal on `C5` and the counterexamples concern the withdrawn text only. `RQ2-2.33`'s
two-sided decomposition was never affected; its docstring says why.

## Main definitions / results
* `RationalQuivers.VertexSplitting` — the decomposition `A ≃ₐ[N] ∏_{k ∈ J} F k` of an étale
  `N`-algebra into finite separable field extensions (`eq:speciesvertexdecomposition`), obtained
  from mathlib's `Algebra.Etale.iff_exists_algEquiv_prod`.
* `RationalQuivers.EtaleSpecies.baseChangeIndex`, `.fibreMap` — `I_N = ⨆_i J(i)` and `π : I_N → I`.
* `RationalQuivers.TwoSidedAlgebra`, `RationalQuivers.EtaleSpecies.baseChangeEdge` — the edge
  algebras `{}_kM'_ℓ` with their two structure maps.
* `RationalQuivers.EtaleSpecies.baseChange` — `S ⊗_K N` (census `RQ2-2.05`).
* `RationalQuivers.EtaleSpecies.moduleDecomposition` — `eq:speciesmoduledecomposition`
  (census `RQ2-2.33`).
* `RationalQuivers.EtaleSpecies.baseChange_trans` (census `RQ2-2.34`) **no longer lives here**: it
  was relocated to `RationalQuivers/Species/AntiEquivalence.lean` at stage S4's G2; see the status
  note below.

## `RQ2-2.34` was re-sequenced to S4 — **RELOCATION EXECUTED 2026-08-30**

> **Dated retraction banner (`WORKFLOW.md` §7, defect class 7 / R6).** The section below is
> **superseded and retained, not deleted**. Its instruction "do not edit `baseChange_trans`,
> it stays here until S4's G2" was **discharged on 2026-08-30**: stage S4's G2 relocated
> `EtaleSpecies.baseChange_trans` — docstring and statement, byte for byte from the `b3795cd`
> baseline the section names (31 lines, 2037 bytes,
> `sha256 a1527d25c9ccd92a8dce6a1b96d359e44132f4f1fcda59974305be19a4993afc`) — into the S4-owned
> module `RationalQuivers/Species/AntiEquivalence.lean`, and deleted this copy in the **same**
> commit. Nothing was discharged by the move: the `sorry` travelled with the statement and
> `RQ2-2.34` remains unproved at that commit. Accounting:
> `workflow/stages/S4/RELOCATION-RQ2-2.34.md`. The superseded text follows.

> ## `RQ2-2.34` is re-sequenced to S4 — do not edit `baseChange_trans`
>
> `EtaleSpecies.baseChange_trans` is **no longer part of stage S3's claimed set** (S3 closes on the
> seven rows `RQ2-2.01`–`RQ2-2.05`, `RQ2-2.07`, `RQ2-2.33`). It stays here, with its `sorry` body, purely
> as the typed record until S4's G2, at which point the declaration — docstring and statement
> together — moves **byte-identical** into an S4-owned module and this copy is deleted in the *same*
> commit, with explicit no-discharge accounting: that is a statement *relocation*, not a removal, and
> it is what keeps S4's proof (which consumes `RQ2-2.08` and `RQ2-2.13`) from needing a forward import
> out of this module.
>
> **Therefore: do not edit this declaration.** Any change to its text breaks the byte-identical
> relocation. The evidence for the re-sequencing is `workflow/ledger/MATHLIB-DECISIONS.tsv`
> `MD-S3-09` and `workflow/stages/S3/DESIGN-NOTES.md` §6.
>
> **Relocation baseline: commit `b3795cd`.** The `@divergence` field of `baseChange_trans` was
> rewritten under the coordinator-ordered G2 correction **V-2** (it previously read "none"). The text
> S4 is to relocate byte-identically is therefore the one at **`b3795cd`** — named by sha rather than
> as "the current text", which would be self-referential and would let any later on-branch docstring
> edit silently re-point a baseline S4 is contractually bound to (verification finding G4-4). The
> `V-2` rewrite is the only change made to this declaration since the G2 freeze at `33e7bcb`, and it
> was a coordinator-ordered disclosure correction, not an implementer edit. **If this declaration ever
> does need to change again, the new sha must be recorded here in the same commit.**

## Implementation notes

**Tensor order.** The source writes `L_i ⊗_K N`; mathlib's base-change instance
(`Algebra.Etale.baseChange`, `Algebra.TensorProduct.leftAlgebra`) is stated for `N ⊗_K L_i`. We use
mathlib's order. The two are canonically isomorphic as `N`-algebras
(`Algebra.TensorProduct.comm`), and no clause depends on the order.

**Pairwise disjointness (clause `RQ2-2.05-C3`) is free.** The source takes the `J(i)` pairwise
disjoint "without loss of generality"; we index by the *dependent sum* `Σ i, J i`, for which
disjointness is a theorem (`Sigma.mk` is injective in the first component) rather than a
convention. The clause's own `if_missing` is `JUSTIFIED_REFORMULATION`, recording it as exactly this
kind of bookkeeping choice.

**Choice.** `Algebra.Etale.iff_exists_algEquiv_prod` is an existential statement, so the splitting
is chosen with `Classical.choice`; `vertexSplitting` is therefore `noncomputable`. The paper's
"we decompose" is the same choice.

**Why the edge algebra is bundled.** `{}_iM_j` carries an `L_i`-algebra structure (through
`S.left`) *and* an `L_j`-algebra structure (through `S.right`), and when `i = j` these are two
different structures on the same pair of types — so neither may be a global `instance`. The
constructions therefore introduce them as local instances (`algLeftEdge`, `algRightEdge`, …) inside
a single definition, and the result is handed on as a `TwoSidedAlgebra`/`BaseAlgebra` bundle whose
projections *are* instances. This is the same device `VertexSplitting` uses for the chosen
decomposition, and it keeps every later field of `EtaleSpecies` a one-line projection.
-/

universe u

namespace RationalQuivers

open scoped TensorProduct
open CategoryTheory

/-- The decomposition `eq:speciesvertexdecomposition` of an étale algebra over a field `N` into a
finite product of finite separable field extensions of `N`, bundled as data.

This is `Algebra.Etale.iff_exists_algEquiv_prod` with the existential quantifiers turned into
fields, so that a *chosen* decomposition can be carried around and referred to.

@census none (helper: the bundled form of `eq:speciesvertexdecomposition`)
-/
structure VertexSplitting (N A : Type u) [Field N] [CommRing A] [Algebra N A] : Type (u + 1) where
  /-- The index set `J` of the decomposition. -/
  J : Type u
  /-- The index set is finite: the product of `eq:speciesvertexdecomposition` is finite. -/
  [finite_J : Finite J]
  /-- The factors `L'_k`. -/
  F : J → Type u
  /-- Each factor is a field. -/
  [field_F : ∀ k, Field (F k)]
  /-- Each factor is an `N`-algebra. -/
  [algebra_F : ∀ k, Algebra N (F k)]
  /-- Each factor is a **finite** extension of `N`. -/
  [finite_F : ∀ k, Module.Finite N (F k)]
  /-- Each factor is a **separable** extension of `N`. -/
  [separable_F : ∀ k, Algebra.IsSeparable N (F k)]
  /-- The decomposition itself. -/
  equiv : A ≃ₐ[N] ∀ k, F k

attribute [instance] VertexSplitting.finite_J VertexSplitting.field_F VertexSplitting.algebra_F
  VertexSplitting.finite_F VertexSplitting.separable_F

/-- A chosen decomposition of an étale algebra over a field, from mathlib's
`Algebra.Etale.iff_exists_algEquiv_prod`. This is `eq:speciesvertexdecomposition`.

@census none (helper: clauses `RQ2-2.05-C1`, `RQ2-2.05-C2` for a single vertex)
-/
noncomputable def VertexSplitting.choose (N A : Type u) [Field N] [CommRing A] [Algebra N A]
    [Algebra.Etale N A] : VertexSplitting N A := by
  choose J hJ F hF hF' e h using (Algebra.Etale.iff_exists_algEquiv_prod N A).mp inferInstance
  exact
    { J := J
      finite_J := hJ
      F := F
      field_F := hF
      algebra_F := hF'
      finite_F := fun k => (h k).1
      separable_F := fun k => (h k).2
      equiv := e }

namespace EtaleSpecies

variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]

/-- `L_i` is an étale `K`-algebra, since it is a finite separable extension of `K`
(clause `RQ2-2.05-H2`: this is exactly what makes the decomposition into fields possible, AN-9). -/
instance etale_L (i : S.I) : Algebra.Etale K (S.L i) :=
  ⟨Algebra.FormallyEtale.of_isSeparable K (S.L i),
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- The chosen decomposition `L_i ⊗_K N = ∏_{k ∈ J(i)} L'_k` of `eq:speciesvertexdecomposition`
(clauses `RQ2-2.05-C1`, `RQ2-2.05-C2`), written with mathlib's tensor order `N ⊗_K L_i`.

@census none (helper for the blocked `RQ2-2.05`)
-/
noncomputable def vertexSplitting (i : S.I) : VertexSplitting N (N ⊗[K] S.L i) :=
  VertexSplitting.choose N (N ⊗[K] S.L i)

/-- Clause `RQ2-2.05-C4`: the index set `I_N = ⨆_{i ∈ I} J(i)` of the base-changed species, as a
dependent sum — which makes clause `RQ2-2.05-C3` (the `J(i)` may be taken pairwise disjoint) a
theorem rather than a convention.

@census none (helper for the blocked `RQ2-2.05`)
-/
noncomputable def baseChangeIndex : Type u := Σ i : S.I, (S.vertexSplitting N i).J

/-- Clause `RQ2-2.05-C4`: the fibre map `π : I_N → I`, sending every `k ∈ J(i)` to `i`.

@census none (helper for the blocked `RQ2-2.05`)
-/
noncomputable def fibreMap : S.baseChangeIndex N → S.I := Sigma.fst

/-- Clause `RQ2-2.05-C3`: the sets `J(i)`, seen inside `I_N`, are pairwise disjoint — the fibres of
`π` over distinct `i` are disjoint by construction.

@census none (helper for the blocked `RQ2-2.05`)
-/
theorem fibreMap_eq_iff {i : S.I} (k : (S.vertexSplitting N i).J) :
    S.fibreMap N ⟨i, k⟩ = i := rfl

/-- The field `L'_k` attached to `k ∈ I_N` (clause `RQ2-2.05-C1`); it is a finite separable
extension of `N` (clause `RQ2-2.05-C2`) by `VertexSplitting.finite_F`/`separable_F`.

@census none (helper for the blocked `RQ2-2.05`)
-/
abbrev baseChangeField (k : S.baseChangeIndex N) : Type u :=
  (S.vertexSplitting N k.1).F k.2

/-- Clause `RQ2-2.05-C2`: each `L'_k` is a **finite** extension of `N`.

@census none (helper for the blocked `RQ2-2.05`)
-/
theorem finite_baseChangeField (k : S.baseChangeIndex N) :
    Module.Finite N (S.baseChangeField N k) :=
  (S.vertexSplitting N k.1).finite_F k.2

/-- Clause `RQ2-2.05-C2`: each `L'_k` is a **separable** extension of `N`.

@census none (helper for the blocked `RQ2-2.05`)
-/
theorem separable_baseChangeField (k : S.baseChangeIndex N) :
    Algebra.IsSeparable N (S.baseChangeField N k) :=
  (S.vertexSplitting N k.1).separable_F k.2

/-- Clause `RQ2-2.05-C1`: the projection `L_{π(k)} ⊗_K N ↠ L'_k` cut out by the chosen
decomposition `eq:speciesvertexdecomposition`. This is the map through which `L'_k` becomes an
algebra over `L_{π(k)}`, and it is the only place the chosen `VertexSplitting.equiv` is used.

@census none (helper for the blocked `RQ2-2.05`)
-/
noncomputable def baseChangeProj (k : S.baseChangeIndex N) :
    (N ⊗[K] S.L (S.fibreMap N k)) →ₐ[N] S.baseChangeField N k :=
  (Pi.evalAlgHom N _ k.2).comp (S.vertexSplitting N k.1).equiv.toAlgHom

/-- `I_N` is finite, so the base-changed species will again have a finite index set.

@census none (helper for the blocked `RQ2-2.05`)
-/
theorem finite_baseChangeIndex : Finite (S.baseChangeIndex N) := by
  haveI : Finite S.I := S.finite_I
  exact inferInstanceAs (Finite (Σ i : S.I, (S.vertexSplitting N i).J))


end EtaleSpecies

/-! ### The counterexamples that forced the corrected edge formula (finding S3-F2)

They concern the formula the source printed before census r18; the amended source prints the
corrected one (dated note in the module docstring, 2026-10-03, `R-FR-9`). -/

/-- The separating `ℝ`-algebra map `ℂ ⊗_ℝ ℂ → ℂ`, `z ⊗ w ↦ z · conj w`. Only used to prove
`literal_baseChange_tmul_ne` below. -/
noncomputable def conjSeparator : ℂ ⊗[ℝ] ℂ →ₐ[ℝ] ℂ :=
  Algebra.TensorProduct.lift (AlgHom.id ℝ ℂ) Complex.conjAe.toAlgHom fun _ _ => Commute.all _ _

/-- **Counterexample 1 for finding S3-F2**, elementary form: in `ℂ ⊗_ℝ ℂ` the element `i ⊗ 1`
differs from `1 ⊗ i`.

@census none (evidence for the `@divergence` on `RQ2-2.05`)
-/
theorem literal_baseChange_tmul_ne :
    (Complex.I ⊗ₜ[ℝ] (1 : ℂ) : ℂ ⊗[ℝ] ℂ) ≠ (1 : ℂ) ⊗ₜ[ℝ] Complex.I := by
  intro h
  have hs := congrArg conjSeparator h
  simp only [conjSeparator, Algebra.TensorProduct.lift_tmul, AlgHom.coe_id, id_eq, map_one,
    mul_one, one_mul, AlgEquiv.coe_algHom, Complex.conjAe_coe, Complex.conj_I] at hs
  norm_num [Complex.ext_iff] at hs

/-- **Counterexample 1 for finding S3-F2.**
Take `K = ℝ`, `N = ℂ` and `S` the one-vertex étale `ℝ`-species with `L_⋆ = ℝ` and
`{}_⋆M_⋆ = ℝ` (`Species.trivial`; the source offers `Gal(ℂ/ℝ)` in place of `Gal(ℚ[√-1]/ℚ)` at the
head of §2.4). Then `L_⋆ ⊗_K N = ℂ`, so `J(⋆)` is a singleton with `L'_k = ℂ`, and the **printed**
clause `RQ2-2.05-C5` formula `L'_k ⊗_{L_{π(k)}} ({}M) ⊗_{L_{π(ℓ)}} L'_ℓ` evaluates to
`ℂ ⊗_ℝ ℝ ⊗_ℝ ℂ ≅ ℂ ⊗_ℝ ℂ`. This theorem says its two structure maps — the left one `n ↦ n ⊗ 1`
through `L'_k` and the right one `n ↦ 1 ⊗ n` through `L'_ℓ` — are **different**. A `K`-species
requires the left and right base-field structures on `{}_iM_j` to agree (`RQ2-2.01-C3`, inherited by
`RQ2-2.02-H1`), so the printed formula does not produce an `N`-species, and clauses `RQ2-2.05-C5` and
`RQ2-2.05-C7` cannot both hold.

The corrected formula implemented below takes the tensor products over the **base-changed** vertex
algebras `L_{π(k)} ⊗_K N`; in this example that turns `ℂ ⊗_ℝ ℂ` into `ℂ ⊗_ℂ ℂ ≅ ℂ`, whose two
structure maps agree, matching `S(Γ_N)` for the base-changed quiver (`def:quiverbasechange` leaves
`(V,E,s,t)` unchanged, so the one loop stays one loop).

@census none (evidence for the `@divergence` on `RQ2-2.05`)
-/
theorem literal_baseChange_structureMaps_ne :
    (Algebra.TensorProduct.includeLeft : ℂ →ₐ[ℝ] ℂ ⊗[ℝ] ℂ) ≠
      Algebra.TensorProduct.includeRight := fun h =>
  literal_baseChange_tmul_ne
    (by simpa using congrArg (fun f : ℂ →ₐ[ℝ] ℂ ⊗[ℝ] ℂ => f Complex.I) h)

/-- **Counterexample 1 for finding S3-F2**, quantitative form: the printed formula's edge algebra
for the example above has `N`-dimension `2`, whereas base change of the underlying quiver leaves the
edge set unchanged, so `S(Γ_N)`'s edge algebra has `N`-dimension `1`. The printed formula therefore
*doubles* the edges, which is the same defect counted differently.

@census none (evidence for the `@divergence` on `RQ2-2.05`)
-/
theorem literal_baseChange_finrank : Module.finrank ℂ (ℂ ⊗[ℝ] ℂ) = 2 := by
  rw [Module.finrank_baseChange]; exact Complex.finrank_real_complex

/-! ### The base-changed species

**Counterexample 2 (`ex:twoloops`) is deliberately NOT a theorem here.** It compares
`S(Γ_ℚ) ⊗_ℚ N` with `S(Γ_N)`, and `S(−)` is census row `RQ2-2.09`, which belongs to stage **S4**;
stating it in S3 would create a forward stage dependency that `rqaudit deps --no-forward` must
reject. It is written out in `workflow/stages/S3/DESIGN-NOTES.md` §2 and is S4's to formalize once
`RationalQuiver.toSpecies` exists.
-/

/-- A commutative algebra over `N` equipped with algebra maps in from two given `N`-algebras
`Fk` and `Fl` — the "`L'_k,L'_ℓ`-bialgebra" of `def:basechangeforspecies` in the sense fixed by
finding S3-F1. Bundling the carrier with its instances is what lets the base-changed edge algebra be
built once, with a single chain of local instances, and then projected field by field into
`EtaleSpecies`.

@census none (helper bundle)
-/
structure TwoSidedAlgebra (N Fk Fl : Type u) [Field N] [CommRing Fk] [CommRing Fl]
    [Algebra N Fk] [Algebra N Fl] : Type (u + 1) where
  /-- The underlying algebra. -/
  carrier : Type u
  /-- Its ring structure; commutative, per clause `RQ2-2.02-C2`. -/
  [commRing : CommRing carrier]
  /-- Its `N`-algebra structure — a single one, which is exactly what the printed formula fails to
  provide (see `literal_baseChange_structureMaps_ne`). -/
  [algebra : Algebra N carrier]
  /-- The left structure map. -/
  left : Fk →ₐ[N] carrier
  /-- The right structure map. -/
  right : Fl →ₐ[N] carrier

attribute [instance] TwoSidedAlgebra.commRing TwoSidedAlgebra.algebra

/-- A commutative algebra over a base ring, bundled with its instances; used for the summands of
`eq:speciesmoduledecomposition` (`RQ2-2.33`), where the two side structures are already visible in
the summand's own definition.

@census none (helper bundle)
-/
structure BaseAlgebra (R : Type u) [CommRing R] : Type (u + 1) where
  /-- The underlying algebra. -/
  carrier : Type u
  /-- Its ring structure. -/
  [commRing : CommRing carrier]
  /-- Its `R`-algebra structure. -/
  [algebra : Algebra R carrier]

attribute [instance] BaseAlgebra.commRing BaseAlgebra.algebra

/-! ### Generic tensor-product lemmas used by `eq:speciesmoduledecomposition`

These are statements about mathlib objects only; they carry no census row. Each is the shape
`eq:speciesmoduledecomposition` needs, assembled from `Algebra.TensorProduct.cancelBaseChange`,
`.congr`, `.comm` and `.piRight`.
-/

/-- Given a decomposition `L ⊗_K N ≃ₐ[L] ∏_k L'_k` and an `L`-algebra `Y`, tensoring `Y` with `N`
over `K` splits along it: `Y ⊗_K N ≃ₐ[L] ∏_k (Y ⊗_L L'_k)`.

@census none (generic helper for `RQ2-2.33`)
-/
noncomputable def tensorSplitRight (K N L Y : Type u) [Field K] [CommRing N] [Field L] [CommRing Y]
    [Algebra K N] [Algebra K L] [Algebra K Y] [Algebra L Y] [IsScalarTower K L Y]
    (J : Type u) [Fintype J] [DecidableEq J] (F : J → Type u) [∀ k, CommRing (F k)]
    [∀ k, Algebra L (F k)] (e : (L ⊗[K] N) ≃ₐ[L] ∀ k, F k) :
    (Y ⊗[K] N) ≃ₐ[L] ∀ k, Y ⊗[L] (F k) :=
  (Algebra.TensorProduct.cancelBaseChange K L L Y N).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : Y ≃ₐ[L] Y) e).trans
      (Algebra.TensorProduct.piRight L L Y F))

/-- The mirror of `tensorSplitRight` with the split factor on the left:
`N ⊗_K Y ≃ₐ[K] ∏_k (L'_k ⊗_L Y)`.

@census none (generic helper for `RQ2-2.33`)
-/
noncomputable def piTensorSplit (K N L Y : Type u) [Field K] [CommRing N] [Field L] [CommRing Y]
    [Algebra K N] [Algebra K L] [Algebra K Y] [Algebra L Y] [IsScalarTower K L Y]
    (J : Type u) [Fintype J] [DecidableEq J] (F : J → Type u) [∀ k, CommRing (F k)]
    [∀ k, Algebra L (F k)] [∀ k, Algebra K (F k)] [∀ k, IsScalarTower K L (F k)]
    (e : (L ⊗[K] N) ≃ₐ[L] ∀ k, F k) :
    (N ⊗[K] Y) ≃ₐ[K] ∀ k, (F k) ⊗[L] Y :=
  (Algebra.TensorProduct.comm K N Y).trans <|
    AlgEquiv.restrictScalars K <|
      ((Algebra.TensorProduct.cancelBaseChange K L L Y N).symm.trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : Y ≃ₐ[L] Y) e).trans
          ((Algebra.TensorProduct.piRight L L Y F).trans
            (AlgEquiv.piCongrRight fun k => Algebra.TensorProduct.comm L Y (F k)))))

/-- Uncurrying a doubly-indexed product of algebras, `∏_b ∏_a X a b ≃ₐ ∏_{(a,b)} X a b`. All the
algebra operations are pointwise, so every field of the equivalence is `rfl`.

@census none (generic helper for `RQ2-2.33`)
-/
def piSwapCurry (K : Type u) [CommSemiring K] {A B : Type u} (X : A → B → Type u)
    [∀ a b, Semiring (X a b)] [∀ a b, Algebra K (X a b)] :
    (∀ b, ∀ a, X a b) ≃ₐ[K] (∀ p : A × B, X p.1 p.2) where
  toFun f p := f p.2 p.1
  invFun g b a := g (a, b)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

namespace EtaleSpecies

variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]

/-- `A_i := N ⊗_K L_i`, the base-changed vertex algebra, written in mathlib's tensor order. It is
étale over `N` by `Algebra.Etale.baseChange`, which is what `vertexSplitting` decomposes. -/
abbrev vertexAlg (i : S.I) : Type u := N ⊗[K] S.L i

/-- `M̃_ij := N ⊗_K {}_iM_j`, the base-changed edge algebra. -/
abbrev edgeAlg (i j : S.I) : Type u := N ⊗[K] S.M i j

/-- The base change of the left structure map, `A_i → M̃_ij`. -/
noncomputable def edgeHomLeft (i j : S.I) : S.vertexAlg N i →ₐ[N] S.edgeAlg N i j :=
  Algebra.TensorProduct.map (AlgHom.id N N) (S.left i j)

/-- The base change of the right structure map, `A_j → M̃_ij`. -/
noncomputable def edgeHomRight (i j : S.I) : S.vertexAlg N j →ₐ[N] S.edgeAlg N i j :=
  Algebra.TensorProduct.map (AlgHom.id N N) (S.right i j)

/-- `M̃_ij` as an `A_i`-algebra, through `edgeHomLeft`. -/
@[reducible] noncomputable def algLeftEdge (i j : S.I) :
    Algebra (S.vertexAlg N i) (S.edgeAlg N i j) := (S.edgeHomLeft N i j).toRingHom.toAlgebra

/-- `M̃_ij` as an `A_j`-algebra, through `edgeHomRight`. Note this is a *different* structure from
`algLeftEdge` even when `i = j`, which is why neither may be a global instance and why the edge
algebra is bundled as a `TwoSidedAlgebra`. -/
@[reducible] noncomputable def algRightEdge (i j : S.I) :
    Algebra (S.vertexAlg N j) (S.edgeAlg N i j) := (S.edgeHomRight N i j).toRingHom.toAlgebra

/-- `L'_k` as an `A_{π(k)}`-algebra, through the projection cut out by the chosen decomposition. -/
@[reducible] noncomputable def algVertexField (k : S.baseChangeIndex N) :
    Algebra (S.vertexAlg N (S.fibreMap N k)) (S.baseChangeField N k) :=
  (S.baseChangeProj N k).toRingHom.toAlgebra

@[reducible] noncomputable def towerLeftEdge (i j : S.I) :
    letI := S.algLeftEdge N i j; IsScalarTower N (S.vertexAlg N i) (S.edgeAlg N i j) :=
  letI := S.algLeftEdge N i j
  IsScalarTower.of_algebraMap_eq' (by ext n; simp [RingHom.algebraMap_toAlgebra])

@[reducible] noncomputable def towerRightEdge (i j : S.I) :
    letI := S.algRightEdge N i j; IsScalarTower N (S.vertexAlg N j) (S.edgeAlg N i j) :=
  letI := S.algRightEdge N i j
  IsScalarTower.of_algebraMap_eq' (by ext n; simp [RingHom.algebraMap_toAlgebra])

@[reducible] noncomputable def towerVertexField (k : S.baseChangeIndex N) :
    letI := S.algVertexField N k;
      IsScalarTower N (S.vertexAlg N (S.fibreMap N k)) (S.baseChangeField N k) :=
  letI := S.algVertexField N k
  IsScalarTower.of_algebraMap_eq' (by ext n; simp [RingHom.algebraMap_toAlgebra])

/-- The two base-changed vertex algebras act on `M̃_ij` through commuting maps (`M̃_ij` is
commutative). -/
@[reducible] noncomputable def smulCommEdge (i j : S.I) :
    letI := S.algLeftEdge N i j; letI := S.algRightEdge N i j;
      SMulCommClass (S.vertexAlg N j) (S.vertexAlg N i) (S.edgeAlg N i j) :=
  letI := S.algLeftEdge N i j
  letI := S.algRightEdge N i j
  ⟨fun a b m => by simp only [Algebra.smul_def, ← mul_assoc, mul_comm]⟩

/-- Clause `RQ2-2.05-C5`:
`{}_kM'_ℓ := L'_k ⊗_{A_{π(k)}} ({}_{π(k)}M_{π(ℓ)} ⊗_K N) ⊗_{A_{π(ℓ)}} L'_ℓ`, with each outer tensor
product taken over the base-changed vertex algebra `A_i = N ⊗_K L_i`. Every base ring here is an
`N`-algebra and every map an `N`-algebra map, so the result carries exactly one `N`-algebra
structure, and its two structure maps `left`, `right` are `N`-algebra maps.

*(Amended 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S3, coordinator ruling
`R-FR-9`, final-release WP-16b, stale item R5.)* Until this amendment this docstring called the
formula "corrected" against a source that tensored over `L_{π(k)}`, `L_{π(ℓ)}` (finding S3-F2). The
amended source (census r18, FA-02) prints exactly this formula, over `A_{π(k)}` and `A_{π(ℓ)}`.
`literal_baseChange_structureMaps_ne` is now a statement about the **superseded** printed formula.

@census none (the edge datum of `RQ2-2.05`; the census row is claimed by `baseChange`)
-/
noncomputable def baseChangeEdge (k l : S.baseChangeIndex N) :
    TwoSidedAlgebra N (S.baseChangeField N k) (S.baseChangeField N l) :=
  letI := S.algRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.towerVertexField N l
  letI := S.algLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.smulCommEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N k
  letI := S.towerVertexField N k
  letI Inner : Type u := (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
    ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l)
  { carrier := (S.baseChangeField N k) ⊗[S.vertexAlg N (S.fibreMap N k)] Inner
    left := Algebra.TensorProduct.includeLeft
    right := (AlgHom.restrictScalars N
        (Algebra.TensorProduct.includeRight :
          Inner →ₐ[S.vertexAlg N (S.fibreMap N k)]
            (S.baseChangeField N k) ⊗[S.vertexAlg N (S.fibreMap N k)] Inner)).comp
      (AlgHom.restrictScalars N
        (Algebra.TensorProduct.includeRight :
          S.baseChangeField N l →ₐ[S.vertexAlg N (S.fibreMap N l)] Inner)) }

/-- Each vertex algebra `L'_k` of the base-changed species is étale over `N`: it is a finite
separable extension of `N` by `VertexSplitting`.

@census none (helper for `RQ2-2.05`)
-/
theorem etale_baseChangeField (k : S.baseChangeIndex N) :
    Algebra.Etale N (S.baseChangeField N k) :=
  ⟨Algebra.FormallyEtale.of_isSeparable N (S.baseChangeField N k),
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- Clause `RQ2-2.05-C7`, the étaleness the source *asserts without proof* (census note AN-20): each
base-changed edge algebra is finite étale over `N`.

@census none (clause obligation of `RQ2-2.05`, discharged at G4)
-/
theorem baseChangeEdge_etale (k l : S.baseChangeIndex N) :
    Algebra.Etale N (S.baseChangeEdge N k l).carrier := by
  letI := S.algRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.towerVertexField N l
  letI := S.algLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.smulCommEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N k
  letI := S.towerVertexField N k
  haveI hk : Algebra.Etale N (S.baseChangeField N k) := S.etale_baseChangeField N k
  haveI hl : Algebra.Etale N (S.baseChangeField N l) := S.etale_baseChangeField N l
  -- `L'_ℓ` is étale over the base-changed vertex algebra `A_{π(ℓ)}` …
  haveI : Algebra.Etale (S.vertexAlg N (S.fibreMap N l)) (S.baseChangeField N l) :=
    Algebra.Etale.of_restrictScalars N _ _
  -- … and so is `M̃`, so the inner tensor product is étale over `M̃` and hence over `N` and
  -- over `A_{π(k)}`.
  haveI : Algebra.Etale (S.vertexAlg N (S.fibreMap N k))
      (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) := Algebra.Etale.of_restrictScalars N _ _
  haveI : Algebra.Etale (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
      ((S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
        ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l)) :=
    Algebra.Etale.baseChange _ _ _
  haveI : Algebra.Etale (S.vertexAlg N (S.fibreMap N k))
      ((S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
        ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l)) :=
    Algebra.Etale.comp _ (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) _
  -- the outer tensor product is a base change along `A_{π(k)} → L'_k`, then compose with `N`.
  show Algebra.Etale N ((S.baseChangeField N k) ⊗[S.vertexAlg N (S.fibreMap N k)]
    ((S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
      ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l)))
  haveI : Algebra.Etale (S.baseChangeField N k)
      ((S.baseChangeField N k) ⊗[S.vertexAlg N (S.fibreMap N k)]
        ((S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))
          ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l))) :=
    Algebra.Etale.baseChange _ _ _
  exact Algebra.Etale.comp N (S.baseChangeField N k) _

/-- **Definition 2.5** (`def:basechangeforspecies`).
For an extension `N/K` and an étale `K`-species `S`: decompose `L_i ⊗_K N = ∏_{k ∈ J(i)} L'_k` with
each `L'_k/N` finite separable and the `J(i)` pairwise disjoint; put `I_N = ⨆_i J(i)` with fibre map
`π`; set `{}_kM'_ℓ := L'_k ⊗_{A_{π(k)}} ({}_{π(k)}M_{π(ℓ)} ⊗_K N) ⊗_{A_{π(ℓ)}} L'_ℓ` where
`A_i = N ⊗_K L_i`. Then `S ⊗_K N := (L'_k, {}_kM'_ℓ)_{k,ℓ ∈ I_N}` is an étale `N`-species.

@census    RQ2-2.05
@source    def:basechangeforspecies
@clauses   RQ2-2.05-H1, RQ2-2.05-H2, RQ2-2.05-C1, RQ2-2.05-C2, RQ2-2.05-C3, RQ2-2.05-C4, RQ2-2.05-C5, RQ2-2.05-C6, RQ2-2.05-C7
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.05-C1` only (notational, finding V-7): the
source writes `L_i ⊗_K N` and we write `N ⊗_K L_i`, mathlib's order for `Algebra.Etale.baseChange`
and `Algebra.TensorProduct.leftAlgebra`. The two are canonically isomorphic as `N`-algebras
(`Algebra.TensorProduct.comm`), no clause depends on the order, and `splitEquivOverL` transports
across it explicitly. **Amended 2026-10-03** (docstring-only `R-PROC-4` amendment of frozen S3,
coordinator ruling `R-FR-9`, final-release WP-16b, stale item R5): until then this field also
carried a `JUSTIFIED_REFORMULATION` on clause `RQ2-2.05-C5` (finding S3-F2), on the ground that the
source took the outer tensor products over `L_{π(k)}`, `L_{π(ℓ)}`. The amended source (census r18,
FA-02) takes them over `A_{π(k)}`, `A_{π(ℓ)}`, exactly as `baseChangeEdge` does, so the defining
formula of `C5` is now **literal**. Its two "equivalently" forms (`= e_k({}_{π(k)}M_{π(ℓ)} ⊗_K N)e_ℓ`
and `L'_k ⊗_{L_{π(k)}} ({}_{π(k)}M_{π(ℓ)}) ⊗_{A_{π(ℓ)}} L'_ℓ`) are not stated as separate theorems;
they are rewrites of the definition that nothing downstream uses. The counterexamples
`literal_baseChange_structureMaps_ne`, `literal_baseChange_tmul_ne` and
`literal_baseChange_finrank` remain as the record of why the old printed formula was withdrawn.
Every other clause is literal: `C1`/`C2`
are `VertexSplitting` from `Algebra.Etale.iff_exists_algEquiv_prod`, `C3` is a theorem rather than a
WLOG because `I_N` is a dependent sum, `C4` is `fibreMap`, `C6` is the `left`/`right` pair of
`baseChangeEdge` (in the sense fixed by finding S3-F1), and `C7` is the output type together with
`baseChangeEdge_etale`.
-/
noncomputable def baseChange : EtaleSpecies.{u} N where
  I := S.baseChangeIndex N
  finite_I := S.finite_baseChangeIndex N
  L := fun k => S.baseChangeField N k
  finite_L := fun k => S.finite_baseChangeField N k
  separable_L := fun k => S.separable_baseChangeField N k
  M := fun k l => (S.baseChangeEdge N k l).carrier
  etale_M := fun k l => S.baseChangeEdge_etale N k l
  left := fun k l => (S.baseChangeEdge N k l).left
  right := fun k l => (S.baseChangeEdge N k l).right

/-- Clause `RQ2-2.05-C4`: the index set of `S ⊗_K N` is `I_N = ⨆_{i ∈ I} J(i)`. -/
@[simp] theorem baseChange_I : (S.baseChange N).I = S.baseChangeIndex N := rfl

/-- Clause `RQ2-2.05-C1`: the vertex algebras of `S ⊗_K N` are the factors `L'_k` of
`eq:speciesvertexdecomposition`. -/
@[simp] theorem baseChange_L (k : S.baseChangeIndex N) :
    (S.baseChange N).L k = S.baseChangeField N k := rfl

/-- Clause `RQ2-2.05-C5`: the edge algebras of `S ⊗_K N` are the ones built by `baseChangeEdge`. -/
@[simp] theorem baseChange_M (k l : S.baseChangeIndex N) :
    (S.baseChange N).M k l = (S.baseChangeEdge N k l).carrier := rfl

/-! ### `eq:speciesmoduledecomposition` (`RQ2-2.33`) -/

/-- `{}_iM_j` as an `L_i`-algebra, through `S.left`. -/
@[reducible] noncomputable def algLeftM (i j : S.I) : Algebra (S.L i) (S.M i j) :=
  (S.left i j).toRingHom.toAlgebra

/-- `{}_iM_j` as an `L_j`-algebra, through `S.right`. -/
@[reducible] noncomputable def algRightM (i j : S.I) : Algebra (S.L j) (S.M i j) :=
  (S.right i j).toRingHom.toAlgebra

@[reducible] noncomputable def towerLeftM (i j : S.I) :
    letI := S.algLeftM i j; IsScalarTower K (S.L i) (S.M i j) :=
  letI := S.algLeftM i j
  IsScalarTower.of_algebraMap_eq' (by ext c; simp [RingHom.algebraMap_toAlgebra])

@[reducible] noncomputable def towerRightM (i j : S.I) :
    letI := S.algRightM i j; IsScalarTower K (S.L j) (S.M i j) :=
  letI := S.algRightM i j
  IsScalarTower.of_algebraMap_eq' (by ext c; simp [RingHom.algebraMap_toAlgebra])

@[reducible] noncomputable def smulCommM (i j : S.I) :
    letI := S.algLeftM i j; letI := S.algRightM i j;
      SMulCommClass (S.L j) (S.L i) (S.M i j) :=
  letI := S.algLeftM i j
  letI := S.algRightM i j
  ⟨fun a b m => by simp only [Algebra.smul_def, ← mul_assoc, mul_comm]⟩

/-- `L'_k` as a `K`-algebra, through `N`. -/
@[reducible] noncomputable def algKField (k : S.baseChangeIndex N) :
    Algebra K (S.baseChangeField N k) :=
  ((algebraMap N (S.baseChangeField N k)).comp (algebraMap K N)).toAlgebra

@[reducible] noncomputable def towerKField (k : S.baseChangeIndex N) :
    letI := S.algKField N k; IsScalarTower K N (S.baseChangeField N k) :=
  letI := S.algKField N k
  IsScalarTower.of_algebraMap_eq' rfl

/-- The canonical `K`-algebra map `L_{π(k)} → L'_k`: include `L_{π(k)}` into `L_{π(k)} ⊗_K N` and
project onto the `k`-th factor of `eq:speciesvertexdecomposition`. This is the map along which the
summands of `eq:speciesmoduledecomposition` are formed. -/
@[reducible] noncomputable def vertexFieldHomK (k : S.baseChangeIndex N) :
    letI := S.algKField N k; S.L (S.fibreMap N k) →ₐ[K] S.baseChangeField N k :=
  letI := S.algKField N k
  letI := S.towerKField N k
  ((S.baseChangeProj N k).restrictScalars K).comp Algebra.TensorProduct.includeRight

/-- `L'_k` as an `L_{π(k)}`-algebra. -/
@[reducible] noncomputable def algLField (k : S.baseChangeIndex N) :
    letI := S.algKField N k; Algebra (S.L (S.fibreMap N k)) (S.baseChangeField N k) :=
  letI := S.algKField N k
  (S.vertexFieldHomK N k).toRingHom.toAlgebra

@[reducible] noncomputable def towerLField (k : S.baseChangeIndex N) :
    letI := S.algKField N k; letI := S.algLField N k;
      IsScalarTower K (S.L (S.fibreMap N k)) (S.baseChangeField N k) :=
  letI := S.algKField N k
  letI := S.algLField N k
  IsScalarTower.of_algebraMap_eq' (by ext c; simp [RingHom.algebraMap_toAlgebra])

/-- Clause `RQ2-2.33-C3`: the `(k,ℓ)`-summand of `eq:speciesmoduledecomposition`, namely
`L'_k ⊗_{L_{π(k)}} ({}_{π(k)}M_{π(ℓ)}) ⊗_{L_{π(ℓ)}} L'_ℓ` — **exactly as printed**: the outer tensor
products are over `L_{π(k)}` and `L_{π(ℓ)}` and **not** over `K`, and the left factor is `L'_k` and
not `L'_{π(k)}`.

Unlike the first printing of `def:basechangeforspecies`, this remark is internally consistent as
printed: its left-hand
side `N ⊗_K ({}_iM_j) ⊗_K N` is the doubled object that these summands add up to, and no clause
claims that this decomposition *is* the base-changed species. So no correction is applied here.

**These summands are therefore NOT the base-changed edge algebras** (`baseChangeEdge`), and the
census note on clause `RQ2-2.33-C3` — "Agrees with `def:basechangeforspecies`(ii)" — no longer held
after the S3-F2 correction (verification finding V-3). *(2026-10-03, `R-FR-9`: the amended source
now separates the two explicitly; its `RQ2-2.33` remark calls the edge algebras of `S ⊗_K N` the
single base change.)* At `K = ℝ`, `N = ℂ`, `L_i = L_j = M = ℂ` the
two are visibly different objects: every summand here is `ℂ`, while `baseChangeEdge` is `ℂ` on the
diagonal and `0` off it. Both are correct; they are answers to different questions.

@census none (the summand of `RQ2-2.33`)
-/
noncomputable def moduleDecompositionSummand (k l : S.baseChangeIndex N) : BaseAlgebra K :=
  letI := S.algRightM (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerRightM (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algKField N l
  letI := S.algLField N l
  letI := S.towerLField N l
  letI := S.algLeftM (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerLeftM (S.fibreMap N k) (S.fibreMap N l)
  letI := S.smulCommM (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algKField N k
  letI := S.algLField N k
  letI := S.towerLField N k
  { carrier := (S.baseChangeField N k) ⊗[S.L (S.fibreMap N k)]
      ((S.M (S.fibreMap N k) (S.fibreMap N l)) ⊗[S.L (S.fibreMap N l)]
        (S.baseChangeField N l)) }

/-- The `L_i`-algebra structure on the `k`-th factor, indexed by the vertex `i` directly. -/
@[reducible] noncomputable def algLFieldAt (i : S.I) (k : (S.vertexSplitting N i).J) :
    Algebra (S.L i) ((S.vertexSplitting N i).F k) := S.algLField N ⟨i, k⟩

/-- The `K`-algebra structure on the `k`-th factor, indexed by the vertex `i` directly. -/
@[reducible] noncomputable def algKFieldAt (i : S.I) (k : (S.vertexSplitting N i).J) :
    Algebra K ((S.vertexSplitting N i).F k) := S.algKField N ⟨i, k⟩

@[reducible] noncomputable def towerLFieldAt (i : S.I) (k : (S.vertexSplitting N i).J) :
    letI := S.algKFieldAt N i k; letI := S.algLFieldAt N i k
    IsScalarTower K (S.L i) ((S.vertexSplitting N i).F k) := S.towerLField N ⟨i, k⟩

/-- The product `∏_k L'_k` as an `L_i`-algebra. -/
@[reducible] noncomputable def algPiField (i : S.I) :
    letI := fun k => S.algLFieldAt N i k
    Algebra (S.L i) (∀ k : (S.vertexSplitting N i).J, (S.vertexSplitting N i).F k) :=
  letI := fun k => S.algLFieldAt N i k
  Pi.algebra _ _

/-- `eq:speciesvertexdecomposition` as an **`L_i`-algebra** equivalence
`L_i ⊗_K N ≃ₐ[L_i] ∏_k L'_k`. The chosen splitting is an `N`-algebra equivalence by construction;
this says it is simultaneously one over `L_i`, which is what lets the decomposition be applied on
both sides of `{}_iM_j`. The `commutes'` proof is `rfl`: `algLField` is *defined* as the composite
`L_i → N ⊗_K L_i → L'_k` this equivalence uses.

@census none (helper for `RQ2-2.33`)
-/
noncomputable def splitEquivOverL (i : S.I) :
    letI := fun k => S.algLFieldAt N i k
    letI := S.algPiField N i
    (S.L i ⊗[K] N) ≃ₐ[S.L i] ∀ k : (S.vertexSplitting N i).J, (S.vertexSplitting N i).F k :=
  letI := fun k => S.algLFieldAt N i k
  letI := S.algPiField N i
  AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm K (S.L i) N).toRingEquiv.trans
      (S.vertexSplitting N i).equiv.toRingEquiv) (fun _ => rfl)

/-- **The `RQ2-2.33` decomposition isomorphism, named.** This is the `def moduleDecompositionEquiv`
that `moduleDecomposition`'s `@divergence` promises as the G4 repair of finding V-2: the `Nonempty`
of the census statement is derived from it, not asserted independently (the "∃ for the gate, named
def for the consumers" convention, `PROCESS-CHANGELOG.md` 2026-08-30). The proof term is unchanged
from before this repair — only its statement type changed from `Nonempty (… ≃ₐ[K] …)` to the
`AlgEquiv` itself.

@census none (helper for `RQ2-2.33`)
-/
noncomputable def moduleDecompositionEquiv (i j : S.I) :
    (N ⊗[K] S.M i j) ⊗[K] N ≃ₐ[K]
      ∀ p : (S.vertexSplitting N i).J × (S.vertexSplitting N j).J,
        (S.moduleDecompositionSummand N ⟨i, p.1⟩ ⟨j, p.2⟩).carrier := by
  classical
  letI := Fintype.ofFinite (S.vertexSplitting N i).J
  letI := Fintype.ofFinite (S.vertexSplitting N j).J
  letI := S.algRightM i j
  letI := S.towerRightM i j
  letI := S.algLeftM i j
  letI := S.towerLeftM i j
  letI := S.smulCommM i j
  letI := fun k => S.algLFieldAt N i k
  letI := fun k => S.algKFieldAt N i k
  letI := fun k => S.towerLFieldAt N i k
  letI := fun l => S.algLFieldAt N j l
  letI := fun l => S.algKFieldAt N j l
  letI := fun l => S.towerLFieldAt N j l
  letI := S.algPiField N i
  letI := S.algPiField N j
  -- `(N ⊗_K M) ⊗_K N ≃ N ⊗_K (M ⊗_K N)`
  refine (Algebra.TensorProduct.assoc K K K N (S.M i j) N).trans ?_
  -- split the right-hand `N` along `eq:speciesvertexdecomposition` for `j`
  refine (Algebra.TensorProduct.congr (AlgEquiv.refl : N ≃ₐ[K] N)
    (AlgEquiv.restrictScalars K (tensorSplitRight K N (S.L j) (S.M i j) _ _
      (S.splitEquivOverL N j)))).trans ?_
  -- pull the product out
  refine (Algebra.TensorProduct.piRight K K N _).trans ?_
  -- split the left-hand `N` along `eq:speciesvertexdecomposition` for `i`
  refine (AlgEquiv.piCongrRight
    (A₂ := fun l => ∀ k : (S.vertexSplitting N i).J, ((S.vertexSplitting N i).F k)
      ⊗[S.L i] ((S.M i j) ⊗[S.L j] ((S.vertexSplitting N j).F l)))
    fun l => piTensorSplit K N (S.L i) ((S.M i j) ⊗[S.L j] ((S.vertexSplitting N j).F l))
      _ _ (S.splitEquivOverL N i)).trans ?_
  -- and re-index by pairs
  exact piSwapCurry K (fun k l => ((S.vertexSplitting N i).F k)
    ⊗[S.L i] ((S.M i j) ⊗[S.L j] ((S.vertexSplitting N j).F l)))

/-- **Remark** (`eq:speciesmoduledecomposition`, census `RQ2-2.33`).
For an extension `N/K` and an étale `K`-species `S` with the vertex decomposition
`eq:speciesvertexdecomposition`, there is a canonical decomposition
`N ⊗_K ({}_iM_j) ⊗_K N = ⨁_{k ∈ J(i), ℓ ∈ J(j)} L'_k ⊗_{L_i} ({}_iM_j) ⊗_{L_j} L'_ℓ`
of the base change of `{}_iM_j` along `N` on both sides, indexed by the `J(i)`, `J(j)` of
`eq:speciesvertexdecomposition`.

*(Amended 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S3, coordinator ruling
`R-FR-9`, final-release WP-16b, stale item R2.)* Until this amendment the docstring also said the
decomposition "mirrors" the vertex decomposition, and the divergence field called that clause
(`RQ-2.33-C2`) "literal". Census r18 **retired** `RQ-2.33-C2`: the amended source no longer prints
"which mirrors". It now says that the analogue of `eq:speciesvertexdecomposition` for the edge
algebras is the **single** base change `{}_iM_j ⊗_K N = ∏_{k ∈ J(i), ℓ ∈ J(j)} {}_kM'_ℓ`. That
statement is **not formalized** here or elsewhere in the tree. The census discloses it on clause
`RQ2-2.33-C1`, reserves the id `RQ2-2.33-C4`, and books it as `O-FR-4`; ruling `R-FR-3` declined to
add it as a row. On the v2 line (census `census-v2.0`) the retired clause has no row, so the
`@clauses` line below no longer names it (v2 T0, WP-7, 2026-10-17); on v1 it was cited only because
v1's `rqaudit clauses` required every row of `census/CLAUSES.tsv`, retired rows included, to be cited.

@census    RQ2-2.33
@source    rmk:speciesmoduledecomposition
@clauses   RQ2-2.33-H1, RQ2-2.33-H2, RQ2-2.33-C1, RQ2-2.33-C3
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.33-C1`: the source's `⨁` over `(k,ℓ)` is
rendered as the dependent product `∀ p : J(i) × J(j), …`. The index set is finite (both `J(i)` and
`J(j)` are `Finite` by `VertexSplitting`), where the finite direct sum and the product of algebras
coincide; the product is used because it is the shape that carries an algebra structure in mathlib,
and it is the same shape `Algebra.Etale.iff_exists_algEquiv_prod` produces for
`eq:speciesvertexdecomposition` itself. Clause `RQ2-2.33-C3`'s summand is
`moduleDecompositionSummand`, whose outer tensor products are over `L_{π(k)}` and `L_{π(ℓ)}`,
exactly as printed. In the amended source this is consistent with `def:basechangeforspecies`(ii),
which takes its tensor products over `A_{π(k)}`, `A_{π(ℓ)}`: the two formulas describe different
objects (two-sided versus single base change). **Not formalized** (disclosed, see the dated note
above): the remark's second display, the single-base-change decomposition
`{}_iM_j ⊗_K N = ∏_{k,ℓ} {}_kM'_ℓ`.

Two further divergences on clause `RQ2-2.33-C1`, both raised by the G2 verification (finding V-2)
and both disclosed here rather than silently accepted:

* **"canonical" is rendered as bare existence.** The clause says the decomposition is *canonical*;
  this statement asserts only `Nonempty (… ≃ₐ[K] …)`. Canonicity is not a predicate in the absence
  of a naturality statement, and bare existence is the accepted G2 shape, but it *is* less than the
  source says. **Landed 2026-09-02 (M1 process repair, finding F-M1-05):** the named
  `def moduleDecompositionEquiv` above — the map `(n ⊗ m) ⊗ n' ↦ (…)` built as an explicit chain —
  and this `Nonempty` is now *derived* from it (`⟨S.moduleDecompositionEquiv N i j⟩`), a
  re-packaging of the existing proof term, not new mathematics: the tactic chain is unchanged, only
  its statement type (the def's, not `Nonempty` of it).
* **The isomorphism is only `K`-linear.** The summands carry `L'_k`- and `L'_ℓ`-structures, and
  nothing here asserts the equivalence respects them. The source's `=` is an identification of
  objects that do carry those structures, so this is weaker; it is disclosed rather than claimed.
  **Not addressed by the 2026-09-02 repair** — upgrading `moduleDecompositionEquiv` to respect the
  `L'_k`/`L'_ℓ`-structures is new mathematics, not a re-packaging, and is out of scope for F-M1-05
  (which only discharges the bare-existence residual); it remains a disclosed residual, unbooked.

*(The paragraph on finding V-3 that closed this docstring until 2026-10-03 said that, after the
S3-F2 correction, `def:basechangeforspecies`(ii) and this remark disagreed, and that `RQ2-2.33` had
been added to a queued author question. The author has since amended the definition (census r18), so
the queued question is answered and the disagreement is gone. Retired under `R-FR-9`.)*
-/
theorem moduleDecomposition (i j : S.I) :
    Nonempty ((N ⊗[K] S.M i j) ⊗[K] N ≃ₐ[K]
      ∀ p : (S.vertexSplitting N i).J × (S.vertexSplitting N j).J,
        (S.moduleDecompositionSummand N ⟨i, p.1⟩ ⟨j, p.2⟩).carrier) :=
  ⟨S.moduleDecompositionEquiv N i j⟩

end EtaleSpecies

end RationalQuivers
