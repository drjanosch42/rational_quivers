module

public import RationalQuivers.Species.Rep.Basic
public import RationalQuivers.Species.BaseChange

@[expose] public section

/-!
# Base change of a representation (§2.5, census `RQ2-2.18`)

Formalizes Definition "Base change for representations of étale `K`-species" of §2.5 of
`latex/rational_quivers.tex`.

## Main definitions / results
* `EtaleSpecies.repBaseChangeSpace` — clause `RQ2-2.18-C1`: `W'_k := W_i ⊗_{L_i} L'_k`.
* `EtaleSpecies.repTensorBaseChange` — the right-hand side of clause `RQ2-2.18-C3`,
  `(W_i ⊗_{L_i} {}_iM_j) ⊗_{L_j} L'_ℓ`.
* `EtaleSpecies.repBaseChangeMap` — clause `RQ2-2.18-C2`: `f_{ij} ⊗ 1_{L'_ℓ}`.
* `EtaleSpecies.repBaseChange` — census `RQ2-2.18`: `W ⊗_K N` is a representation of `S ⊗_K N`,
  with `C1`, `C2` and `C3` pinned as the accompanying data.

## Implementation notes

**The `K`-algebra chain.**  `L'_k` is a factor of `N ⊗_K L_{π(k)}` and S3 gives it only as an
`N`-algebra (`VertexSplitting.algebra_F`).  Two further structures are needed and are supplied as
`@[reducible] noncomputable def`s used with `letI` — S3's own `algVertexField` idiom, chosen over
global instances because `Algebra K (L'_k)` and `Algebra (L_{π(k)}) (L'_k)` would both be new
instances on a type that already carries `Algebra N`:

* `algKBC` — `K → N → L'_k`;
* `vertexToBaseChangeField` / `algVertexBC` — `L_i → N ⊗_K L_i ↠ L'_k`, the map through which
  `L'_k` is an `L_i`-algebra and hence an `(L_i, L'_k)`-bimodule.

**Which tensor product.**  `W'_k = W_i ⊗_{L_i} L'_k` is again a *balanced* product over the
possibly-non-commutative `L_i`, so it is `Species/Rep/Tensor.lean`'s `Balanced` at
`A = L_i`, `B = Y = L'_k`, `X = W_i` (`MD-S5-01`).  Note the central field of that product is `K`,
not `N`: the base-changed representation is an object over `N`, but the space `W'_k` is built by
tensoring an object over `K`.

## Finding **S5-F2** — `RQ2-2.18-C3` is stated against a formula stage S3 refuted

*(Dated note, 2026-10-03, `R-FR-9`, final-release WP-16b, stale item R6.)* Everything in this
section and in the S5-F10 material below describes the source **before** census r18. The amended
source corrects `RQ2-2.05-C5` and prints `RQ2-2.18`'s decomposition in the fibre-summed form, with
`f'_{kℓ}` the restriction of `f_{ij} ⊗ 1_{L'_ℓ}`. `repBaseChange` is now literal on `H1`/`C1`–`C3`;
see its divergence field.

> **Dated retraction banner (`WORKFLOW.md` R6 / §7), 2026-08-31 — read this first.**  The
> conclusion below, *"`C3` **does** survive the correction"*, is **WITHDRAWN**, and so is the
> five-step chain printed under it: its step 2 → 3 replaces `L'_k` by `A_i`, and
> `A_i = ∏_{k ∈ J(i)} L'_k` is the vertex decomposition, so that step is legitimate only after
> summing over the fibre.  Under the corrected `RQ2-2.05-C5` the clause as the source prints it is
> **false**, over-counting by exactly the factor `|J(i)|` — the same over-count `S3-F2` removed
> from `RQ2-2.05-C5` itself, surviving one clause downstream.  This is finding **S5-F10**
> (coordinator-ratified 2026-08-31), and its compiled evidence is
> `repTensorBaseChange_indep_of_fibre` and `frozenC3_forces_fibre_independence` below, with the
> dimension count and the `K = ℝ`, `N = ℂ` witness in their section header and in
> `stages/S5/DESIGN-NOTES.md` §67.  `C3`'s repair is the **fibre-summed** form, `⊕_{k ∈ J(i)}` on
> the left; `repBaseChange` below states it.  The text is retained unedited because it is the
> reasoning the clause was typed against, and because the *class* it assigned — class 7,
> documentary drift — is the judgement S5-F10 overturns.

Clause `RQ2-2.18-C3` asserts the identification
`W'_k ⊗_{L'_k} {}_kM'_ℓ = (W_i ⊗_{L_i} {}_iM_j) ⊗_{L_j} L'_ℓ`.  The source states it against the
**printed** edge formula of `RQ2-2.05-C5`, `{}_kM'_ℓ = L'_k ⊗_{L_i} ({}_iM_j) ⊗_{L_j} L'_ℓ` —
which is exactly the formula stage S3 **refuted** (finding S3-F2, coordinator-ratified;
`literal_baseChange_structureMaps_ne`) and replaced by taking the tensor products over the
base-changed vertex algebras `A_i = N ⊗_K L_i`.  Against the printed formula `C3` is a one-line
cancellation; against the one `EtaleSpecies.baseChange` actually builds it is not.

`C3` **does** survive the correction, and `repTensorBaseChange` is its corrected right-hand side.
The derivation, to be discharged at G4:
*(RETRACTED 2026-08-31 by S5-F10 — the chain's step 2 → 3, flagged inline below, is invalid for a
single `k`; the fibre-summed form is what survives.)*

```
W'_k ⊗_{L'_k} {}_kM'_ℓ = (W_i ⊗_{L_i} L'_k) ⊗_{L'_k} L'_k ⊗_{A_i} (M_ij ⊗_K N) ⊗_{A_j} L'_ℓ
                       = W_i ⊗_{L_i} L'_k ⊗_{A_i} (M_ij ⊗_K N) ⊗_{A_j} L'_ℓ
                       = (W_i ⊗_K N) ⊗_{A_i} (M_ij ⊗_K N) ⊗_{A_j} L'_ℓ     [INVALID — S5-F10: replaces L'_k by A_i = ∏_{k∈J(i)} L'_k]
                       = ((W_i ⊗_{L_i} M_ij) ⊗_K N) ⊗_{A_j} L'_ℓ           [base change is monoidal]
                       = (W_i ⊗_{L_i} M_ij) ⊗_{L_j} L'_ℓ .
```

So the clause is faithful, but its **proof** is the monoidality of base change rather than a
cancellation.  Class 7 (documentary drift), not a new source defect; see
`workflow/stages/S5/DESIGN-NOTES.md` §4.1.1.

*(End of the retracted text.  S5-F10's verdict: the clause is **not** faithful as printed under the
corrected `RQ2-2.05-C5`, the class is **1**, not 7, and the monoidality argument is sound only for
the fibre-summed statement.  `DESIGN-NOTES` §67.)*
-/

universe u

namespace RationalQuivers

open scoped TensorProduct

namespace EtaleSpecies

variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K) (N : Type u) [Field N] [Algebra K N]

/-- `L'_k` as a `K`-algebra, through `N`.  @census none (helper) -/
@[reducible] noncomputable def algKBC (k : S.baseChangeIndex N) :
    Algebra K (S.baseChangeField N k) :=
  ((algebraMap N (S.baseChangeField N k)).comp (algebraMap K N)).toAlgebra

/-- The structure map `L_{π(k)} → L'_k`: include `L_{π(k)}` into `N ⊗_K L_{π(k)}` and project onto
the `k`-th factor of `eq:speciesvertexdecomposition`.

@census none (helper for clause `RQ2-2.18-C1`)
-/
noncomputable def vertexToBaseChangeField (k : S.baseChangeIndex N) :
    letI := S.algKBC N k; S.L (S.fibreMap N k) →ₐ[K] S.baseChangeField N k :=
  letI := S.algKBC N k
  haveI : IsScalarTower K N (S.baseChangeField N k) :=
    IsScalarTower.of_algebraMap_eq' (by ext c; simp [RingHom.algebraMap_toAlgebra])
  ((S.baseChangeProj N k).restrictScalars K).comp Algebra.TensorProduct.includeRight

/-- `L'_k` as an `L_{π(k)}`-algebra, through `vertexToBaseChangeField`; this is what makes it an
`(L_{π(k)}, L'_k)`-bimodule.  @census none (helper) -/
@[reducible] noncomputable def algVertexBC (k : S.baseChangeIndex N) :
    Algebra (S.L (S.fibreMap N k)) (S.baseChangeField N k) :=
  letI := S.algKBC N k
  (S.vertexToBaseChangeField N k).toRingHom.toAlgebra

set_option backward.isDefEq.respectTransparency.types false in
/-- **Clause `RQ2-2.18-C1`(i)**: `W'_k := W_i ⊗_{L_i} L'_k` for `i = π(k)`, the balanced tensor
product of the right `L_i`-space `W_i` with the `(L_i, L'_k)`-bimodule `L'_k`.  It is a right
`L'_k`-vector space.

@census none (clause witness for `RQ2-2.18-C1`)
@clauses   RQ2-2.18-C1
-/
@[reducible] noncomputable def repBaseChangeSpace (V : EtaleSpecies.Rep S) (k : S.baseChangeIndex N) :
    Type u :=
  letI := S.algKBC N k
  letI := S.algVertexBC N k
  Balanced K (S.L (S.fibreMap N k)) (S.baseChangeField N k) (S.baseChangeField N k)
    (V.W (S.fibreMap N k))

set_option backward.isDefEq.respectTransparency.types false in
/-- **The right-hand side of clause `RQ2-2.18-C3`**, corrected per findings S5-F2 and **S5-F10**:
`(W_i ⊗_{L_i} {}_iM_j) ⊗_{L_j} L'_ℓ` for `j = π(ℓ)`, indexed by a vertex `i ∈ I` **of the base
species** rather than by a vertex `k` of the base-changed one.

The re-indexing carries no content — `repTensorBaseChange` below *is* this at `i = π(k)`, and
`repTensorBaseChange_indep_of_fibre` is the `rfl` saying the old spelling already depended on `k`
only through `π(k)`.  It is a *presentation* forced by finding **S5-F10**: the corrected clause
identifies this one object with the sum over the **whole fibre** `J(i)`, so the target must be
written where the fibre can face it.

@census none (clause witness for `RQ2-2.18-C3`)
@clauses   RQ2-2.18-C3
-/
@[reducible] noncomputable def repTensorBaseChangeAt (V : EtaleSpecies.Rep S) (i : S.I)
    (l : S.baseChangeIndex N) : Type u :=
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  Balanced K (S.L (S.fibreMap N l)) (S.baseChangeField N l) (S.baseChangeField N l)
    (EtaleSpecies.Rep.tensor S i (S.fibreMap N l) (V.W i))

/-- **The right-hand side of clause `RQ2-2.18-C3`** at a vertex `k` of the base-changed species:
`(W_i ⊗_{L_i} {}_iM_j) ⊗_{L_j} L'_ℓ` for `i = π(k)`, `j = π(ℓ)`.  Definitionally
`repTensorBaseChangeAt` at `i = π(k)`, so the elaborated type is character-for-character the one
this declaration had before the S5-F10 repair.

@census none (clause witness for `RQ2-2.18-C3`)
@clauses   RQ2-2.18-C3
-/
@[reducible] noncomputable def repTensorBaseChange (V : EtaleSpecies.Rep S) (k l : S.baseChangeIndex N) :
    Type u :=
  S.repTensorBaseChangeAt N V (S.fibreMap N k) l

set_option backward.isDefEq.respectTransparency.types false in
/-- **Clause `RQ2-2.18-C2`**: `f'_{kℓ} = f_{ij} ⊗ 1_{L'_ℓ}`, the base change to `L'_ℓ` of the
structure map `f_{ij}` of `V`, read through the identification `RQ2-2.18-C3`.

Note the index on the identity: `1_{L'_ℓ}`, the *far* factor. *(Amended 2026-10-03, `R-FR-9`,
final-release WP-16b, stale item R6: this paragraph said the source prints `1_{L'_k}`; the amended
source prints `1_{L'_ℓ}`, as here.)*

@census none (clause witness for `RQ2-2.18-C2`)
@clauses   RQ2-2.18-C2
-/
noncomputable def repBaseChangeMap (V : EtaleSpecies.Rep S) (k l : S.baseChangeIndex N) :
    letI := S.algKBC N l; letI := S.algVertexBC N l;
      S.repTensorBaseChange N V k l →ₗ[(S.baseChangeField N l)ᵐᵒᵖ]
        S.repBaseChangeSpace N V l :=
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  Balanced.map (K := K) (A := S.L (S.fibreMap N l))
    (fun c x => Balanced.smul_K (A := S.L (S.fibreMap N k)) c x)
    (V.smul_K_W (S.fibreMap N l))
    (EtaleSpecies.Rep.f' S V (S.fibreMap N k) (S.fibreMap N l))
    (S.baseChangeField N l)

/-! ### `RQ2-2.18-C3`'s chain, step 0: leaving `Balanced` for mathlib's `⊗`

Every algebra in the `S5-F2` chain is a commutative field, so each `Balanced` in it is mathlib's
`⊗` by `Balanced.equivTensor` — the `S5-F3` boundary, crossed at the three places the chain needs
and named, rather than inside the chain where it could not be audited.  The `hX` is `rfl` in every
case (`smul_of_opposite`), because the left action is `moduleOfOpposite`'s.
-/

set_option backward.isDefEq.respectTransparency.types false in
/-- `W'_k = W_i ⊗_{L_i} L'_k` as a mathlib tensor product.  @census none (helper for `RQ2-2.18-C3`) -/
noncomputable def repBaseChangeSpaceEquiv (V : EtaleSpecies.Rep S) (k : S.baseChangeIndex N) :
    letI := S.algKBC N k
    letI := S.algVertexBC N k
    S.repBaseChangeSpace N V k
      ≃ₗ[(S.baseChangeField N k)ᵐᵒᵖ]
        (S.baseChangeField N k) ⊗[S.L (S.fibreMap N k)] (V.W (S.fibreMap N k)) := by
  letI := S.algKBC N k
  letI := S.algVertexBC N k
  letI := moduleOfOpposite (S.L (S.fibreMap N k)) (V.W (S.fibreMap N k))
  exact Balanced.equivTensor (smul_of_opposite _ _)


set_option backward.isDefEq.respectTransparency.types false in
/-- **Value guard from birth** (`CONVENTIONS.md` §3): the conversion on a generator, `rfl`.
@census none (guard) -/
@[simp] theorem repBaseChangeSpaceEquiv_mk (V : EtaleSpecies.Rep S) (k : S.baseChangeIndex N)
    (x : V.W (S.fibreMap N k)) (y : S.baseChangeField N k) :
    letI := S.algKBC N k
    letI := S.algVertexBC N k
    S.repBaseChangeSpaceEquiv N V k (Balanced.mk x y) = y ⊗ₜ x := rfl

/-! ### Conversions 2 and 3 — the crossings §66.3 recorded as blocked

Finding **S5-F10**'s first half (`DESIGN-NOTES` §67).  §66.3's eliminative table concluded that
conversion 2 is an *absence*, not a timeout, and §66.4 proposed retreating to a `Balanced`-only
route.  Both are **withdrawn**: conversion 2 goes through, and so does conversion 3.  What the
table missed is that its rows tested candidate fixes **separately**, and the fix is a conjunction
of two of them:

* the `letI := moduleOfOpposite …` must sit **in the type** — the `Module` gap is in the
  *statement*, since `TensorProduct R M N` needs `Module R N` (§66.3 found this half); **and**
* the instance actually missing is `Balanced.equivTensor`'s standing assumption (2) for the
  *fresh* action, `IsScalarTower K (S.L j) (W_i ⊗_{L_i} {}_iM_j)` — the **un-opposed** tower.
  §66.3's hypothesis 4 tested the **opposed** one, `IsScalarTower K (S.L j)ᵐᵒᵖ …`, and correctly
  refuted it; they are different instances.

`towerRepTensor` below is that missing tower, proved by the four-line `Rep.isScalarTower_L_W`
template (`Species/Rep/Basic.lean`).  With it, `repTensorBaseChange` does **not** destabilise:
its own elaboration is untouched, which is the fact §66.4 doubted.
-/

/-- **The un-opposed scalar tower** on `W_i ⊗_{L_i} {}_iM_j`, for the left `L_j`-action that
`moduleOfOpposite` supplies.  `Balanced.equivTensor`'s standing assumption (2) at the *fresh*
action; the opposed tower `IsScalarTower K (S.L j)ᵐᵒᵖ …` is mathlib's and is a different
instance (finding **S5-F10**; `DESIGN-NOTES` §67.1).

Not an instance: its head `Rep.tensor S i j X` is variable in `i`, `j` and `X`, which is exactly
the shape `CONVENTIONS.md` §3 and `DESIGN-NOTES` §51 forbid as ambient.  Used with `letI`, per
carrier, like `algKBC` and `algVertexBC` above.

@census none (helper for `RQ2-2.18-C3`) -/
@[reducible] noncomputable def towerRepTensor (i j : S.I) (X : Type u) [AddCommGroup X]
    [Module K X] [Module (S.L i)ᵐᵒᵖ X] [IsScalarTower K (S.L i)ᵐᵒᵖ X] :
    letI := moduleOfOpposite (S.L j) (EtaleSpecies.Rep.tensor S i j X)
    IsScalarTower K (S.L j) (EtaleSpecies.Rep.tensor S i j X) := by
  letI := moduleOfOpposite (S.L j) (EtaleSpecies.Rep.tensor S i j X)
  refine ⟨fun c a x => ?_⟩
  show (MulOpposite.op (c • a)) • x = c • ((MulOpposite.op a) • x)
  rw [← smul_assoc c (MulOpposite.op a) x]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **Conversion 2 of 3**: `(W_i ⊗_{L_i} {}_iM_j) ⊗_{L_j} L'_ℓ` as a mathlib tensor product.
This is the crossing §66.3 recorded as blocked; see the section header for why it is not.

@census none (helper for `RQ2-2.18-C3`) -/
noncomputable def repTensorBaseChangeEquiv (V : EtaleSpecies.Rep S) (k l : S.baseChangeIndex N) :
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := moduleOfOpposite (S.L (S.fibreMap N l))
      (EtaleSpecies.Rep.tensor S (S.fibreMap N k) (S.fibreMap N l) (V.W (S.fibreMap N k)))
    S.repTensorBaseChange N V k l
      ≃ₗ[(S.baseChangeField N l)ᵐᵒᵖ]
        (S.baseChangeField N l) ⊗[S.L (S.fibreMap N l)]
          (EtaleSpecies.Rep.tensor S (S.fibreMap N k) (S.fibreMap N l) (V.W (S.fibreMap N k))) := by
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := moduleOfOpposite (S.L (S.fibreMap N l))
    (EtaleSpecies.Rep.tensor S (S.fibreMap N k) (S.fibreMap N l) (V.W (S.fibreMap N k)))
  letI := S.towerRepTensor (S.fibreMap N k) (S.fibreMap N l) (V.W (S.fibreMap N k))
  exact Balanced.equivTensor (smul_of_opposite _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-- **Value guard from birth** (`CONVENTIONS.md` §3) for conversion 2, `rfl`.
@census none (guard) -/
@[simp] theorem repTensorBaseChangeEquiv_mk (V : EtaleSpecies.Rep S) (k l : S.baseChangeIndex N)
    (t : EtaleSpecies.Rep.tensor S (S.fibreMap N k) (S.fibreMap N l) (V.W (S.fibreMap N k)))
    (y : S.baseChangeField N l) :
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := moduleOfOpposite (S.L (S.fibreMap N l))
      (EtaleSpecies.Rep.tensor S (S.fibreMap N k) (S.fibreMap N l) (V.W (S.fibreMap N k)))
    S.repTensorBaseChangeEquiv N V k l (Balanced.mk t y) = y ⊗ₜ t := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **Conversion 3 of 3**: `W'_k ⊗_{L'_k} {}_kM'_ℓ`, the left-hand side of `RQ2-2.18-C3`, as a
mathlib tensor product.  Unlike conversions 1 and 2 this one is on the **base-changed** side, so
every index is `(S.baseChange N)`-headed.

@census none (helper for `RQ2-2.18-C3`) -/
noncomputable def baseChangeRepTensorEquiv (V' : EtaleSpecies.Rep (S.baseChange N))
    (k l : S.baseChangeIndex N) :
    letI := moduleOfOpposite ((S.baseChange N).L k) (V'.W k)
    EtaleSpecies.Rep.tensor (S.baseChange N) k l (V'.W k)
      ≃ₗ[((S.baseChange N).L l)ᵐᵒᵖ]
        ((S.baseChange N).M k l) ⊗[(S.baseChange N).L k] (V'.W k) := by
  letI := moduleOfOpposite ((S.baseChange N).L k) (V'.W k)
  exact Balanced.equivTensor (smul_of_opposite _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-- **Value guard from birth** (`CONVENTIONS.md` §3) for conversion 3, `rfl`.
@census none (guard) -/
@[simp] theorem baseChangeRepTensorEquiv_mk (V' : EtaleSpecies.Rep (S.baseChange N))
    (k l : S.baseChangeIndex N) (x : V'.W k) (y : (S.baseChange N).M k l) :
    letI := moduleOfOpposite ((S.baseChange N).L k) (V'.W k)
    S.baseChangeRepTensorEquiv N V' k l (Balanced.mk x y) = y ⊗ₜ x := rfl

/-! ### The `baseChangeField` head, bridged

`(S.baseChange N).L k` and `S.baseChangeField N k` are the same type by `EtaleSpecies.baseChange_L`
(a `rfl` lemma of S3), but instance search does not identify them — the same phenomenon as
finding **S5-F3**, one level down.  `RQ2-2.18-C4` has to name a representation of `S ⊗_K N`, whose
instances come out `(S.baseChange N).L`-headed, and compare it with `repBaseChangeSpace`, which is
built `baseChangeField`-headed.  Two bridges, each again *literally* the projection it re-heads, so
the `rfl`-identity guarantee of `DESIGN-NOTES` §11.3 extends to them.
-/

set_option backward.isDefEq.respectTransparency.types false in
/-- `W'_k` as a right `L'_k`-space, at the `baseChangeField` head.  @census none (helper) -/
noncomputable instance module_baseChangeField_W (V' : EtaleSpecies.Rep (S.baseChange N))
    (k : S.baseChangeIndex N) : Module (S.baseChangeField N k)ᵐᵒᵖ (V'.W k) :=
  V'.module_W k

set_option backward.isDefEq.respectTransparency.types false in
/-- `W'_k ⊗_{L'_k} {}_kM'_ℓ` as a right `L'_ℓ`-space, at the `baseChangeField` head.
@census none (helper) -/
noncomputable instance module_baseChangeField_tensor (V' : EtaleSpecies.Rep (S.baseChange N))
    (k l : S.baseChangeIndex N) :
    Module (S.baseChangeField N l)ᵐᵒᵖ (EtaleSpecies.Rep.tensor (S.baseChange N) k l (V'.W k)) :=
  inferInstanceAs
    (Module ((S.baseChange N).L l)ᵐᵒᵖ (EtaleSpecies.Rep.tensor (S.baseChange N) k l (V'.W k)))


/-! ### `RQ2-2.18-C3`'s repair, step 1: the **fibre decomposition** of the base-changed edge module

Finding **S5-F10** (`DESIGN-NOTES` §67) showed that the frozen `C3` over-counts by `|J(i)|`,
because the derivation replaces `L'_k` by `A_i` for a *single* `k` while `A_i = ∏_{k ∈ J(i)} L'_k`.
This section is that step done correctly: `∏_a L'_a = A_i` is `eq:speciesvertexdecomposition`
itself, so what the chain may legitimately do is decompose the inner factor over the **whole
fibre**.

`splitEquivOverA` is the decomposition read as an `A_i`-algebra equivalence, and its `commutes'` is
`rfl` — `baseChangeProj` is *defined* as `eval_a ∘ equiv`, so the product of the `A_i`-structure
maps **is** the equivalence.  (This is S3's `splitEquivOverL` pattern one level along.)
`edgeFibreEquiv` then reads `Z ≃ ∏_a ({}_{⟨i,a⟩}M'_ℓ)` off it, by `rid`, `congr`, `piRight` and a
pointwise `comm`.

**A note for consumers.**  `fibreMap` is a plain `def`, so `S.fibreMap N ⟨i, a⟩` does **not** reduce
to `i` during instance search: the `A_i`-algebra structure on the `a`-th factor must be introduced
by an explicit ascription (`algVertexFieldAt` below), never by a bare `letI := S.algVertexField N
⟨i, a⟩`.  Measured, and the cause of the first failure in this section.
-/


/-- The inner factor `Z = M̃_ij ⊗_{A_j} L'_ℓ` of the base-changed edge module. -/
@[reducible] noncomputable def edgeInner (i : S.I) (l : S.baseChangeIndex N) : Type u :=
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  (S.edgeAlg N i (S.fibreMap N l)) ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l)

section
variable (i : S.I) (l : S.baseChangeIndex N)

/-- `Z` is an `A_i`-algebra, through `edgeHomLeft` on the left factor. -/
@[reducible] noncomputable def algEdgeInner :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    Algebra (S.vertexAlg N i) (S.edgeInner N i l) := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  infer_instance

end

/-- The `A_i`-algebra structure on the `a`-th factor, with `π⟨i,a⟩` reduced to `i` by an explicit
ascription — `fibreMap` is a plain `def` and does not reduce for instance search. -/
@[reducible] noncomputable def algVertexFieldAt (i : S.I) (a : (S.vertexSplitting N i).J) :
    Algebra (S.vertexAlg N i) ((S.vertexSplitting N i).F a) :=
  S.algVertexField N ⟨i, a⟩

/-- The product of the factors, as an `A_i`-algebra. -/
@[reducible] noncomputable def algPiVertexField (i : S.I) :
    letI := fun a => S.algVertexFieldAt N i a
    Algebra (S.vertexAlg N i) (∀ a : (S.vertexSplitting N i).J, (S.vertexSplitting N i).F a) :=
  letI := fun a => S.algVertexFieldAt N i a
  Pi.algebra _ _

/-- **`eq:speciesvertexdecomposition` as an `A_i`-algebra equivalence**: `A_i ≃ₐ[A_i] ∏_a L'_a`.
`commutes'` is `rfl` because `baseChangeProj` is *defined* as `eval_a ∘ equiv`, so the product of
the structure maps IS the equivalence — the `splitEquivOverL` pattern of S3. -/
noncomputable def splitEquivOverA (i : S.I) :
    letI := fun a => S.algVertexFieldAt N i a
    letI := S.algPiVertexField N i
    (S.vertexAlg N i) ≃ₐ[S.vertexAlg N i]
      (∀ a : (S.vertexSplitting N i).J, (S.vertexSplitting N i).F a) :=
  letI := fun a => S.algVertexFieldAt N i a
  letI := S.algPiVertexField N i
  AlgEquiv.ofRingEquiv (f := (S.vertexSplitting N i).equiv.toRingEquiv) (fun _ => rfl)


/-- **The fibre decomposition of the base-changed edge module** (finding `S5-F10`'s repair):
`Z ≃ ∏_{a ∈ J(i)} {}_{⟨i,a⟩}M'_ℓ`, where `Z = M̃_ij ⊗_{A_j} L'_ℓ`.  This is the step the frozen
`RQ2-2.18-C3` performed for a single `a`; `∏_a L'_a = A_i` is what makes it legitimate. -/
noncomputable def edgeFibreEquiv (i : S.I) (l : S.baseChangeIndex N) :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    (S.edgeInner N i l) ≃ₐ[S.vertexAlg N i]
      (∀ a : (S.vertexSplitting N i).J,
        (S.vertexSplitting N i).F a ⊗[S.vertexAlg N i] (S.edgeInner N i l)) := by
  classical
  letI := Fintype.ofFinite (S.vertexSplitting N i).J
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := S.algPiVertexField N i
  refine (Algebra.TensorProduct.rid (S.vertexAlg N i) (S.vertexAlg N i)
      (S.edgeInner N i l)).symm.trans ?_
  refine (Algebra.TensorProduct.congr
      (AlgEquiv.refl : (S.edgeInner N i l) ≃ₐ[S.vertexAlg N i] (S.edgeInner N i l))
      (S.splitEquivOverA N i)).trans ?_
  refine (Algebra.TensorProduct.piRight (S.vertexAlg N i) (S.vertexAlg N i)
      (S.edgeInner N i l) _).trans ?_
  exact AlgEquiv.piCongrRight fun a =>
    Algebra.TensorProduct.comm (S.vertexAlg N i) (S.edgeInner N i l) ((S.vertexSplitting N i).F a)

/-! ### `RQ2-2.18-C3`'s repair, step 2: **the base change of the edge module, and `E`**

Finding **S5-F10**'s repair needs the inner factor `Z = M̃_ij ⊗_{A_j} L'_ℓ` identified with
`{}_iM_j ⊗_{L_j} L'_ℓ`, and step 1's `edgeFibreEquiv` then turns that into the whole fibre.  The
content is one identification — **`M̃_ij` is the base change of `{}_iM_j` along `L_j → A_j`**
(`edgeBaseChangeEquiv`) — and everything else is bookkeeping.

**Why it is phrased over `L_j` and not over `N`.**  `Algebra N ({}_iM_j ⊗_{L_j} L'_ℓ)` is not
found: the `N`-structure sits on the **right** factor while mathlib's `Algebra.TensorProduct` puts
the base algebra on the left (`DESIGN-NOTES` §67.6's right-factor asymmetry).  Over `L_j` the
statement elaborates.

**Why `E`'s target is a `Balanced` and not a mathlib `⊗`.**  `Balanced K L_j L'_ℓ L'_ℓ ({}_iM_j)`
is the shape `Balanced.assoc` produces, and using it is what makes the assembly's `Algebra N`
obstacle disappear — `Balanced`'s module structures are ours rather than mathlib's left-factor
ones (`DESIGN-NOTES` §67.12).

**A consumer hazard, again.**  `fibreMap` is a plain `def`, so `S.fibreMap N ⟨i, a⟩` does not
reduce to `i` for instance search, and `(S.baseChange N).L k` is not identified with
`S.baseChangeField N k` either.  Every structure below is therefore introduced at an explicit
head — the `…At` and `…BC…` families are exactly those re-headings, each *literally* the
declaration it re-heads, so the diamond is definitional by construction (the `S5-F3` pattern of
`Species/Rep/Basic.lean`, one level along).
-/

/-! ### The `K`-structures of the base-changed species, at its own head -/

set_option backward.isDefEq.respectTransparency.types false in
/-- `{}_kM'_ℓ` as a right `L'_ℓ`-space, at the `baseChangeField` head. -/
noncomputable instance module_baseChangeField_M (k l : S.baseChangeIndex N) :
    Module (S.baseChangeField N l)ᵐᵒᵖ ((S.baseChange N).M k l) :=
  inferInstanceAs (Module ((S.baseChange N).L l)ᵐᵒᵖ ((S.baseChange N).M k l))

set_option backward.isDefEq.respectTransparency.types false in
/-- `L'_k` as a `K`-algebra, at the `(S.baseChange N).L` head. -/
@[reducible] noncomputable def algKBCL (k : S.baseChangeIndex N) :
    Algebra K ((S.baseChange N).L k) := S.algKBC N k

set_option backward.isDefEq.respectTransparency.types false in
@[reducible] noncomputable def towerKBCL (k : S.baseChangeIndex N) :
    letI := S.algKBCL N k; IsScalarTower K N ((S.baseChange N).L k) :=
  letI := S.algKBCL N k
  IsScalarTower.of_algebraMap_eq' rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `{}_kM'_ℓ` as a `K`-algebra, through `N`. -/
@[reducible] noncomputable def algKBCEdge (k l : S.baseChangeIndex N) :
    Algebra K ((S.baseChange N).M k l) :=
  ((algebraMap N ((S.baseChange N).M k l)).comp (algebraMap K N)).toAlgebra

set_option backward.isDefEq.respectTransparency.types false in
@[reducible] noncomputable def towerKBCEdge (k l : S.baseChangeIndex N) :
    letI := S.algKBCEdge N k l; IsScalarTower K N ((S.baseChange N).M k l) :=
  letI := S.algKBCEdge N k l
  IsScalarTower.of_algebraMap_eq' rfl


@[reducible] noncomputable def algKBCAt (i : S.I) (a : (S.vertexSplitting N i).J) :
    Algebra K ((S.vertexSplitting N i).F a) := S.algKBC N ⟨i, a⟩

@[reducible] noncomputable def algVertexBCAt (i : S.I) (a : (S.vertexSplitting N i).J) :
    letI := S.algKBCAt N i a
    Algebra (S.L i) ((S.vertexSplitting N i).F a) := S.algVertexBC N ⟨i, a⟩

/-- `K → N → L'_k` and `K → L_{π(k)} → L'_k` agree. -/
@[reducible] noncomputable def towerVertexBCK (k : S.baseChangeIndex N) :
    letI := S.algKBC N k
    letI := S.algVertexBC N k
    IsScalarTower K (S.L (S.fibreMap N k)) (S.baseChangeField N k) := by
  letI := S.algKBC N k
  letI := S.algVertexBC N k
  exact IsScalarTower.of_algebraMap_eq' (by ext c; simp [RingHom.algebraMap_toAlgebra])

/-- `K → N → L'_k` factors through `N`. -/
@[reducible] noncomputable def towerKNBC (k : S.baseChangeIndex N) :
    letI := S.algKBC N k
    IsScalarTower K N (S.baseChangeField N k) :=
  letI := S.algKBC N k
  IsScalarTower.of_algebraMap_eq' rfl

/-- `towerVertexBCK` at the fibre index. -/
@[reducible] noncomputable def towerVertexBCKAt (i : S.I) (a : (S.vertexSplitting N i).J) :
    letI := S.algKBCAt N i a
    letI := S.algVertexBCAt N i a
    IsScalarTower K (S.L i) ((S.vertexSplitting N i).F a) := S.towerVertexBCK N ⟨i, a⟩

/-- `towerKNBC` at the fibre index. -/
@[reducible] noncomputable def towerKNBCAt (i : S.I) (a : (S.vertexSplitting N i).J) :
    letI := S.algKBCAt N i a
    IsScalarTower K N ((S.vertexSplitting N i).F a) := S.towerKNBC N ⟨i, a⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- `{}_{⟨i,a⟩}M'_ℓ` as an `L_i`-algebra, through `L_i → L'_{⟨i,a⟩} → {}_{⟨i,a⟩}M'_ℓ`. -/
@[reducible] noncomputable def algLeftBCEdgeAt (i : S.I) (a : (S.vertexSplitting N i).J)
    (l : S.baseChangeIndex N) :
    letI := S.algKBCAt N i a
    letI := S.algVertexBCAt N i a
    Algebra (S.L i) ((S.baseChange N).M ⟨i, a⟩ l) :=
  letI := S.algKBCAt N i a
  letI := S.algVertexBCAt N i a
  (((S.baseChange N).left ⟨i, a⟩ l).toRingHom.comp
    (algebraMap (S.L i) ((S.vertexSplitting N i).F a))).toAlgebra


set_option backward.isDefEq.respectTransparency.types false in
@[reducible] noncomputable def towerLeftBCEdgeAt (i : S.I) (a : (S.vertexSplitting N i).J)
    (l : S.baseChangeIndex N) :
    letI := S.algKBCAt N i a
    letI := S.algVertexBCAt N i a
    letI := S.algLeftBCEdgeAt N i a l
    letI := S.algKBCEdge N ⟨i, a⟩ l
    IsScalarTower K (S.L i) ((S.baseChange N).M ⟨i, a⟩ l) := by
  letI := S.algKBCAt N i a
  letI := S.algVertexBCAt N i a
  letI := S.algLeftBCEdgeAt N i a l
  letI := S.algKBCEdge N ⟨i, a⟩ l
  letI := S.towerVertexBCKAt N i a
  letI := S.towerKNBCAt N i a
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext c
  show algebraMap K ((S.baseChange N).M ⟨i, a⟩ l) c
      = ((S.baseChange N).left ⟨i, a⟩ l) (algebraMap (S.L i) ((S.vertexSplitting N i).F a)
          (algebraMap K (S.L i) c))
  rw [← IsScalarTower.algebraMap_apply K (S.L i) ((S.vertexSplitting N i).F a),
    IsScalarTower.algebraMap_apply K N ((S.vertexSplitting N i).F a)]
  exact (((S.baseChange N).left ⟨i, a⟩ l).commutes ((algebraMap K N) c)).symm

set_option backward.isDefEq.respectTransparency.types false in
@[reducible] noncomputable def smulCommLeftBCEdgeAt (i : S.I) (a : (S.vertexSplitting N i).J)
    (l : S.baseChangeIndex N) :
    letI := S.algKBCAt N i a
    letI := S.algVertexBCAt N i a
    letI := S.algLeftBCEdgeAt N i a l
    SMulCommClass (S.L i) (S.baseChangeField N l)ᵐᵒᵖ ((S.baseChange N).M ⟨i, a⟩ l) := by
  letI := S.algKBCAt N i a
  letI := S.algVertexBCAt N i a
  letI := S.algLeftBCEdgeAt N i a l
  exact ⟨fun α b m => by
    show algebraMap (S.L i) ((S.baseChange N).M ⟨i, a⟩ l) α * (_ * m)
        = _ * (algebraMap (S.L i) ((S.baseChange N).M ⟨i, a⟩ l) α * m)
    rw [← mul_assoc, ← mul_assoc, mul_comm (algebraMap (S.L i) _ α)]⟩


/-- `A_j = N ⊗_K L_j` as an `L_j`-algebra, through `includeRight`. -/
@[reducible] noncomputable def algRightVertex (j : S.I) : Algebra (S.L j) (S.vertexAlg N j) :=
  Algebra.TensorProduct.rightAlgebra (R := K) (A := N) (B := S.L j)

/-- `L_j → A_j → L'_ℓ` is the structure map `L_j → L'_ℓ`. -/
@[reducible] noncomputable def towerVertexBC (l : S.baseChangeIndex N) :
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.algVertexField N l
    IsScalarTower (S.L (S.fibreMap N l)) (S.vertexAlg N (S.fibreMap N l))
      (S.baseChangeField N l) := by
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.algVertexField N l
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The `L_j`-action of `algRightM` is the right one, on the nose. -/
theorem smul_algRightM (i j : S.I) (a : S.L j) (m : S.M i j) :
    (letI := S.algRightM i j; a • m) = MulOpposite.op a • m := rfl

section
variable (i j : S.I)

/-- **`M̃_ij` is the base change of `{}_iM_j` along `L_j → A_j`**: `M̃_ij ≃ A_j ⊗_{L_j} {}_iM_j` as
`A_j`-algebras. -/
noncomputable def edgeBaseChangeEquiv :
    letI := S.algRightM i j
    letI := S.towerRightM i j
    letI := S.algRightVertex N j
    letI := S.algRightEdge N i j
    S.edgeAlg N i j ≃ₐ[S.vertexAlg N j] (S.vertexAlg N j) ⊗[S.L j] (S.M i j) := by
  letI := S.algRightM i j
  letI := S.towerRightM i j
  letI := S.algRightVertex N j
  letI := S.algRightEdge N i j
  refine AlgEquiv.ofRingEquiv
    (f := ((Algebra.TensorProduct.comm K N (S.M i j)).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange K (S.L j) (S.L j) (S.M i j) N).symm.toRingEquiv.trans
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : (S.M i j) ≃ₐ[S.L j] (S.M i j))
            (Algebra.TensorProduct.commRight K (S.L j) N)).toRingEquiv.trans
          (Algebra.TensorProduct.comm (S.L j) (S.M i j) (S.vertexAlg N j)).toRingEquiv))))
    (fun a => ?_)
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a a' ha ha' => rw [map_add, map_add, ha, ha', ← map_add]
  | tmul n x =>
      show (n ⊗ₜ[K] (1 : S.L j)) ⊗ₜ[S.L j] (S.right i j x) = (n ⊗ₜ[K] x) ⊗ₜ[S.L j] (1 : S.M i j)
      have h1 : (S.right i j x) = x • (1 : S.M i j) := by
        rw [Algebra.smul_def]; simp [RingHom.algebraMap_toAlgebra]
      rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      congr 1
      show ((1 : N) ⊗ₜ[K] x) * (n ⊗ₜ[K] (1 : S.L j)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- Value guard from birth, `rfl` on a pure tensor. -/
theorem edgeBaseChangeEquiv_tmul (n : N) (m : S.M i j) :
    letI := S.algRightM i j
    letI := S.towerRightM i j
    letI := S.algRightVertex N j
    letI := S.algRightEdge N i j
    S.edgeBaseChangeEquiv N i j (n ⊗ₜ[K] m) = (n ⊗ₜ[K] (1 : S.L j)) ⊗ₜ[S.L j] m := rfl

end

section
variable (i : S.I) (l : S.baseChangeIndex N)

/-- **E, step 2**: `Z = M̃_ij ⊗_{A_j} L'_ℓ ≃ L'_ℓ ⊗_{L_j} {}_iM_j`, as rings. -/
noncomputable def edgeInnerEquiv :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    S.edgeInner N i l ≃+*
      (S.baseChangeField N l) ⊗[S.L (S.fibreMap N l)] (S.M i (S.fibreMap N l)) := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.towerVertexBC N l
  exact ((Algebra.TensorProduct.congr (S.edgeBaseChangeEquiv N i (S.fibreMap N l))
      (AlgEquiv.refl :
        (S.baseChangeField N l) ≃ₐ[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l))
    ).toRingEquiv.trans
    ((Algebra.TensorProduct.comm (S.vertexAlg N (S.fibreMap N l))
        ((S.vertexAlg N (S.fibreMap N l)) ⊗[S.L (S.fibreMap N l)] (S.M i (S.fibreMap N l)))
        (S.baseChangeField N l)).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange (S.L (S.fibreMap N l))
          (S.vertexAlg N (S.fibreMap N l)) (S.vertexAlg N (S.fibreMap N l))
          (S.baseChangeField N l) (S.M i (S.fibreMap N l))).toRingEquiv))

/-- Value guard from birth for `edgeInnerEquiv`, `rfl` on a generator. -/
theorem edgeInnerEquiv_tmul (n : N) (m : S.M i (S.fibreMap N l)) (c : S.baseChangeField N l) :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    S.edgeInnerEquiv N i l ((n ⊗ₜ[K] m) ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] c)
      = ((n ⊗ₜ[K] (1 : S.L (S.fibreMap N l))) • c) ⊗ₜ[S.L (S.fibreMap N l)] m := rfl

end

section Fibre
variable (i : S.I) (l : S.baseChangeIndex N)

set_option backward.isDefEq.respectTransparency.types false in
/-- The `a`-th base-changed edge module as an `L'_ℓ`-algebra, through the species' right
structure map. -/
@[reducible] noncomputable def algRightBCEdge (a : (S.vertexSplitting N i).J) :
    Algebra (S.baseChangeField N l) ((S.baseChange N).M ⟨i, a⟩ l) :=
  ((S.baseChange N).right ⟨i, a⟩ l).toRingHom.toAlgebra

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibre product as an `L'_ℓ`-algebra. -/
@[reducible] noncomputable def algPiBCEdge :
    letI := fun a => S.algRightBCEdge N i l a
    Algebra (S.baseChangeField N l)
      (∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l) :=
  letI := fun a => S.algRightBCEdge N i l a
  Pi.algebra _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- The right `L'_ℓ`-action on the fibre product is multiplication by the structure map. -/
theorem op_smul_piBCEdge :
    letI := fun a => S.algRightBCEdge N i l a
    letI := S.algPiBCEdge N i l
    ∀ (c : S.baseChangeField N l)
      (y : ∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l),
      (MulOpposite.op c) • y
        = algebraMap (S.baseChangeField N l)
            (∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l) c * y := by
  letI := fun a => S.algRightBCEdge N i l a
  letI := S.algPiBCEdge N i l
  intro c y
  funext a
  rfl

/-- Value guard for `edgeFibreEquiv`: `z ↦ (a ↦ 1 ⊗ z)`. -/
theorem edgeFibreEquiv_apply (z : S.edgeInner N i l) (a : (S.vertexSplitting N i).J) :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    S.edgeFibreEquiv N i l z a = (1 : (S.vertexSplitting N i).F a) ⊗ₜ[S.vertexAlg N i] z := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := S.algPiVertexField N i
  show ((S.splitEquivOverA N i) 1 a) ⊗ₜ[S.vertexAlg N i] z = _
  rw [map_one]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The composite ring equivalence `∏_a {}_{⟨i,a⟩}M'_ℓ ≃ L'_ℓ ⊗_{L_j} {}_iM_j`. -/
noncomputable def fibreEdgeRingEquiv :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    (∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l) ≃+*
      (S.baseChangeField N l) ⊗[S.L (S.fibreMap N l)] (S.M i (S.fibreMap N l)) := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.towerVertexBC N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  exact (S.edgeFibreEquiv N i l).toRingEquiv.symm.trans (S.edgeInnerEquiv N i l)

/-- The right `L'_ℓ`-action of `algRightM` on the target of `E`. -/
theorem op_smul_tensorBC :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    letI := fun a => S.algRightBCEdge N i l a
    letI := S.algPiBCEdge N i l
    ∀ (c : S.baseChangeField N l)
      (z : (S.baseChangeField N l) ⊗[S.L (S.fibreMap N l)] (S.M i (S.fibreMap N l))),
      (MulOpposite.op c) • z
        = algebraMap (S.baseChangeField N l)
            ((S.baseChangeField N l) ⊗[S.L (S.fibreMap N l)] (S.M i (S.fibreMap N l))) c * z := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.towerVertexBC N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := fun a => S.algRightBCEdge N i l a
  letI := S.algPiBCEdge N i l
  intro c z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add p q hp hq => rw [smul_add, hp, hq, mul_add]
  | tmul y x =>
      show (MulOpposite.op c • y) ⊗ₜ[S.L (S.fibreMap N l)] x = _
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      rw [Algebra.algebraMap_self, RingHom.id_apply, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op, mul_comm]

set_option backward.isDefEq.respectTransparency.types false in
/-- `fibreEdgeRingEquiv` respects the two `L'_ℓ`-structure maps. -/
theorem fibreEdgeRingEquiv_commutes :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    letI := fun a => S.algRightBCEdge N i l a
    letI := S.algPiBCEdge N i l
    ∀ c : S.baseChangeField N l,
      S.fibreEdgeRingEquiv N i l
          (algebraMap (S.baseChangeField N l)
            (∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l) c)
        = algebraMap (S.baseChangeField N l)
            ((S.baseChangeField N l) ⊗[S.L (S.fibreMap N l)] (S.M i (S.fibreMap N l))) c := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.towerVertexBC N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := fun a => S.algRightBCEdge N i l a
  letI := S.algPiBCEdge N i l
  intro c
  have hmk : (S.edgeFibreEquiv N i l)
      ((1 : S.edgeAlg N i (S.fibreMap N l)) ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] c)
      = algebraMap (S.baseChangeField N l)
          (∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l) c := by
    funext a
    rw [S.edgeFibreEquiv_apply N i l]
    rfl
  show S.edgeInnerEquiv N i l ((S.edgeFibreEquiv N i l).symm _) = _
  rw [← hmk, AlgEquiv.symm_apply_apply,
    show ((1 : S.edgeAlg N i (S.fibreMap N l)) ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] c)
      = (((1 : N) ⊗ₜ[K] (1 : S.M i (S.fibreMap N l)))
          ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] c) from rfl,
    S.edgeInnerEquiv_tmul N i l,
    show ((1 : N) ⊗ₜ[K] (1 : S.L (S.fibreMap N l)))
      = (1 : S.vertexAlg N (S.fibreMap N l)) from rfl,
    one_smul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- **E** — the fibre-summed edge identification, as a map of `(L_i, L'_ℓ)`-bimodules:
`∏_{a ∈ J(i)} {}_{⟨i,a⟩}M'_ℓ ≃ {}_iM_j ⊗_{L_j} L'_ℓ`. -/
noncomputable def repEdgeFibreIdent :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    letI := fun a => S.algRightBCEdge N i l a
    letI := S.algPiBCEdge N i l
    (∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l)
      ≃ₗ[(S.baseChangeField N l)ᵐᵒᵖ]
        Balanced K (S.L (S.fibreMap N l)) (S.baseChangeField N l) (S.baseChangeField N l)
          (S.M i (S.fibreMap N l)) := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.towerVertexBC N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := fun a => S.algRightBCEdge N i l a
  letI := S.algPiBCEdge N i l
  exact (ringEquivToOpLinear (S.op_smul_piBCEdge N i l) (S.op_smul_tensorBC N i l)
      (S.fibreEdgeRingEquiv N i l) (S.fibreEdgeRingEquiv_commutes N i l)).trans
    (Balanced.equivTensor (S.smul_algRightM i (S.fibreMap N l))).symm

end Fibre


set_option backward.isDefEq.respectTransparency.types false in
/-- `{}_{⟨i,a⟩}M'_ℓ` as an `L'_{⟨i,a⟩}`-module, at the splitting-factor head. -/
@[reducible] noncomputable def moduleFBCEdgeAt (i : S.I) (a : (S.vertexSplitting N i).J)
    (l : S.baseChangeIndex N) :
    Module ((S.vertexSplitting N i).F a) ((S.baseChange N).M ⟨i, a⟩ l) :=
  inferInstanceAs (Module ((S.baseChange N).L ⟨i, a⟩) ((S.baseChange N).M ⟨i, a⟩ l))

set_option backward.isDefEq.respectTransparency.types false in
/-- `IsScalarTower N L'_{⟨i,a⟩} {}_{⟨i,a⟩}M'_ℓ`, at the splitting-factor head. -/
@[reducible] noncomputable def towerNFBCEdgeAt (i : S.I) (a : (S.vertexSplitting N i).J)
    (l : S.baseChangeIndex N) :
    letI := S.moduleFBCEdgeAt N i a l
    IsScalarTower N ((S.vertexSplitting N i).F a) ((S.baseChange N).M ⟨i, a⟩ l) :=
  letI := S.moduleFBCEdgeAt N i a l
  inferInstanceAs (IsScalarTower N ((S.baseChange N).L ⟨i, a⟩) ((S.baseChange N).M ⟨i, a⟩ l))

set_option backward.isDefEq.respectTransparency.types false in
/-- The bimodule axiom for `{}_{⟨i,a⟩}M'_ℓ`, at the splitting-factor head. -/
@[reducible] noncomputable def smulCommFBCEdgeAt (i : S.I) (a : (S.vertexSplitting N i).J)
    (l : S.baseChangeIndex N) :
    letI := S.moduleFBCEdgeAt N i a l
    SMulCommClass ((S.vertexSplitting N i).F a) (S.baseChangeField N l)ᵐᵒᵖ
      ((S.baseChange N).M ⟨i, a⟩ l) :=
  letI := S.moduleFBCEdgeAt N i a l
  inferInstanceAs (SMulCommClass ((S.baseChange N).L ⟨i, a⟩) ((S.baseChange N).L l)ᵐᵒᵖ
    ((S.baseChange N).M ⟨i, a⟩ l))

set_option backward.isDefEq.respectTransparency.types false in
/-- `L_i → L'_{⟨i,a⟩} → {}_{⟨i,a⟩}M'_ℓ` is the `L_i`-structure map. -/
@[reducible] noncomputable def towerLiFBCEdgeAt (i : S.I) (a : (S.vertexSplitting N i).J)
    (l : S.baseChangeIndex N) :
    letI := S.algKBCAt N i a
    letI := S.algVertexBCAt N i a
    letI := S.algLeftBCEdgeAt N i a l
    letI := S.moduleFBCEdgeAt N i a l
    IsScalarTower (S.L i) ((S.vertexSplitting N i).F a) ((S.baseChange N).M ⟨i, a⟩ l) := by
  letI := S.algKBCAt N i a
  letI := S.algVertexBCAt N i a
  letI := S.algLeftBCEdgeAt N i a l
  letI := S.moduleFBCEdgeAt N i a l
  refine ⟨fun α u m => ?_⟩
  show ((S.baseChange N).left ⟨i, a⟩ l) (α • u) * m
      = algebraMap (S.L i) ((S.baseChange N).M ⟨i, a⟩ l) α
          * (((S.baseChange N).left ⟨i, a⟩ l) u * m)
  have hm : ((S.baseChange N).left ⟨i, a⟩ l) (α • u)
      = algebraMap (S.L i) ((S.baseChange N).M ⟨i, a⟩ l) α
          * ((S.baseChange N).left ⟨i, a⟩ l) u :=
    (congrArg ((S.baseChange N).left ⟨i, a⟩ l) (Algebra.smul_def α u)).trans (map_mul _ _ _)
  exact (congrArg (fun z => z * m) hm).trans (mul_assoc _ _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-- `W'_{⟨i,a⟩}`, indexed by the vertex `i` directly. -/
@[reducible] noncomputable def repBaseChangeSpaceAt (V : EtaleSpecies.Rep S) (i : S.I)
    (a : (S.vertexSplitting N i).J) : Type u :=
  letI := S.algKBCAt N i a
  letI := S.algVertexBCAt N i a
  Balanced K (S.L i) ((S.vertexSplitting N i).F a) ((S.vertexSplitting N i).F a) (V.W i)

theorem repBaseChangeSpaceAt_eq (V : EtaleSpecies.Rep S) (i : S.I)
    (a : (S.vertexSplitting N i).J) :
    S.repBaseChangeSpaceAt N V i a = S.repBaseChangeSpace N V ⟨i, a⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The bimodule axiom for `{}_kM'_ℓ` over `N`, at the `baseChangeField` head. -/
@[reducible] noncomputable def smulCommNBCEdge (k l : S.baseChangeIndex N) :
    SMulCommClass N (S.baseChangeField N l)ᵐᵒᵖ ((S.baseChange N).M k l) :=
  inferInstanceAs (SMulCommClass N ((S.baseChange N).L l)ᵐᵒᵖ ((S.baseChange N).M k l))

set_option backward.isDefEq.respectTransparency.types false in
/-- The right-hand `N`-tower for `{}_kM'_ℓ`, at the `baseChangeField` head. -/
@[reducible] noncomputable def towerNBCEdge (k l : S.baseChangeIndex N) :
    IsScalarTower N (S.baseChangeField N l)ᵐᵒᵖ ((S.baseChange N).M k l) :=
  inferInstanceAs (IsScalarTower N ((S.baseChange N).L l)ᵐᵒᵖ ((S.baseChange N).M k l))

section EFib
variable (i : S.I) (l : S.baseChangeIndex N)

/-- `L'_ℓ ⊗_{L_j} {}_iM_j` as an `L_i`-algebra, through `{}_iM_j`'s left structure map. -/
@[reducible] noncomputable def algLeftTensorBC :
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    Algebra (S.L i)
      ((S.baseChangeField N l) ⊗[S.L (S.fibreMap N l)] (S.M i (S.fibreMap N l))) :=
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  ((Algebra.TensorProduct.includeRight :
      (S.M i (S.fibreMap N l)) →ₐ[S.L (S.fibreMap N l)]
        (S.baseChangeField N l) ⊗[S.L (S.fibreMap N l)] (S.M i (S.fibreMap N l))).toRingHom.comp
    (S.left i (S.fibreMap N l)).toRingHom).toAlgebra

set_option backward.isDefEq.respectTransparency.types false in
/-- The fibre product as an `L_i`-algebra. -/
@[reducible] noncomputable def algLeftPiBCEdge :
    letI := fun a => S.algKBCAt N i a
    letI := fun a => S.algVertexBCAt N i a
    letI := fun a => S.algLeftBCEdgeAt N i a l
    Algebra (S.L i) (∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l) :=
  letI := fun a => S.algKBCAt N i a
  letI := fun a => S.algVertexBCAt N i a
  letI := fun a => S.algLeftBCEdgeAt N i a l
  Pi.algebra _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- `fibreEdgeRingEquiv` respects the two `L_i`-structure maps. -/
theorem fibreEdgeRingEquiv_commutesL :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    letI := fun a => S.algKBCAt N i a
    letI := fun a => S.algVertexBCAt N i a
    letI := fun a => S.algLeftBCEdgeAt N i a l
    letI := S.algLeftPiBCEdge N i l
    letI := S.algLeftTensorBC N i l
    ∀ α : S.L i,
      S.fibreEdgeRingEquiv N i l
          (algebraMap (S.L i)
            (∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l) α)
        = algebraMap (S.L i)
            ((S.baseChangeField N l) ⊗[S.L (S.fibreMap N l)] (S.M i (S.fibreMap N l))) α := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.towerVertexBC N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := fun a => S.algKBCAt N i a
  letI := fun a => S.algVertexBCAt N i a
  letI := fun a => S.algLeftBCEdgeAt N i a l
  letI := S.algLeftPiBCEdge N i l
  letI := S.algLeftTensorBC N i l
  intro α
  have h1 : (S.edgeFibreEquiv N i l)
      (algebraMap (S.vertexAlg N i) (S.edgeInner N i l) ((1 : N) ⊗ₜ[K] α))
      = algebraMap (S.L i)
          (∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l) α := by
    funext a
    rw [S.edgeFibreEquiv_apply N i l]
    show (1 : (S.vertexSplitting N i).F a) ⊗ₜ[S.vertexAlg N i]
        (algebraMap (S.vertexAlg N i) (S.edgeInner N i l) ((1 : N) ⊗ₜ[K] α))
      = (algebraMap (S.vertexAlg N i) ((S.vertexSplitting N i).F a) ((1 : N) ⊗ₜ[K] α))
          ⊗ₜ[S.vertexAlg N i] (1 : S.edgeInner N i l)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  show S.edgeInnerEquiv N i l ((S.edgeFibreEquiv N i l).symm _) = _
  rw [← h1, AlgEquiv.symm_apply_apply,
    show (algebraMap (S.vertexAlg N i) (S.edgeInner N i l) ((1 : N) ⊗ₜ[K] α))
      = (((1 : N) ⊗ₜ[K] (S.left i (S.fibreMap N l) α))
          ⊗ₜ[S.vertexAlg N (S.fibreMap N l)] (1 : S.baseChangeField N l)) from rfl,
    S.edgeInnerEquiv_tmul N i l,
    show ((1 : N) ⊗ₜ[K] (1 : S.L (S.fibreMap N l)))
      = (1 : S.vertexAlg N (S.fibreMap N l)) from rfl, one_smul]
  rfl

/-- The `S5-F3` bridge, `L_i`-side: `Balanced.equivTensor` is `L_i`-equivariant. -/
theorem equivTensorL_smul :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    letI := fun a => S.algKBCAt N i a
    letI := fun a => S.algVertexBCAt N i a
    letI := fun a => S.algLeftBCEdgeAt N i a l
    letI := S.algLeftPiBCEdge N i l
    letI := S.algLeftTensorBC N i l
    letI := fun a => S.algRightBCEdge N i l a
    letI := S.algPiBCEdge N i l
    letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
      (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
    ∀ (α : S.L i) (s : Balanced K (S.L (S.fibreMap N l)) (S.baseChangeField N l)
        (S.baseChangeField N l) (S.M i (S.fibreMap N l))),
      Balanced.equivTensor (S.smul_algRightM i (S.fibreMap N l)) (α • s)
        = α • Balanced.equivTensor (S.smul_algRightM i (S.fibreMap N l)) s := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.towerVertexBC N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := fun a => S.algKBCAt N i a
  letI := fun a => S.algVertexBCAt N i a
  letI := fun a => S.algLeftBCEdgeAt N i a l
  letI := S.algLeftPiBCEdge N i l
  letI := S.algLeftTensorBC N i l
  letI := fun a => S.algRightBCEdge N i l a
  letI := S.algPiBCEdge N i l
  letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
    (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
  intro α s
  refine balanced_smul_ext
    (Balanced.equivTensor (S.smul_algRightM i (S.fibreMap N l))).toAddMonoidHom α
    (fun m z => ?_) s
  show z ⊗ₜ[S.L (S.fibreMap N l)] (α • m) = α • (z ⊗ₜ[S.L (S.fibreMap N l)] m)
  rw [Algebra.smul_def]
  show _ = ((1 : S.baseChangeField N l) ⊗ₜ[S.L (S.fibreMap N l)]
      (S.left i (S.fibreMap N l) α)) * (z ⊗ₜ[S.L (S.fibreMap N l)] m)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **`E` is `L_i`-equivariant** — `congrY`'s first obligation. -/
theorem repEdgeFibreIdent_smulL :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    letI := fun a => S.algKBCAt N i a
    letI := fun a => S.algVertexBCAt N i a
    letI := fun a => S.algLeftBCEdgeAt N i a l
    letI := S.algLeftPiBCEdge N i l
    letI := S.algLeftTensorBC N i l
    letI := fun a => S.algRightBCEdge N i l a
    letI := S.algPiBCEdge N i l
    letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
      (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
    ∀ (α : S.L i) (y : ∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l),
      S.repEdgeFibreIdent N i l (α • y) = α • S.repEdgeFibreIdent N i l y := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.towerVertexBC N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := fun a => S.algKBCAt N i a
  letI := fun a => S.algVertexBCAt N i a
  letI := fun a => S.algLeftBCEdgeAt N i a l
  letI := S.algLeftPiBCEdge N i l
  letI := S.algLeftTensorBC N i l
  letI := fun a => S.algRightBCEdge N i l a
  letI := S.algPiBCEdge N i l
  letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
    (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
  intro α y
  show (Balanced.equivTensor (S.smul_algRightM i (S.fibreMap N l))).symm
      (S.fibreEdgeRingEquiv N i l (α • y)) = _
  rw [Algebra.smul_def, map_mul, S.fibreEdgeRingEquiv_commutesL N i l α, ← Algebra.smul_def]
  have h := S.equivTensorL_smul N i l α
    ((Balanced.equivTensor (S.smul_algRightM i (S.fibreMap N l))).symm
      (S.fibreEdgeRingEquiv N i l y))
  rw [LinearEquiv.apply_symm_apply] at h
  exact ((Balanced.equivTensor (S.smul_algRightM i (S.fibreMap N l))).symm_apply_eq).mpr h.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- `E.symm` is `L_i`-equivariant — `congrY`'s third obligation. -/
theorem repEdgeFibreIdent_symm_smulL :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    letI := fun a => S.algKBCAt N i a
    letI := fun a => S.algVertexBCAt N i a
    letI := fun a => S.algLeftBCEdgeAt N i a l
    letI := S.algLeftPiBCEdge N i l
    letI := S.algLeftTensorBC N i l
    letI := fun a => S.algRightBCEdge N i l a
    letI := S.algPiBCEdge N i l
    letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
      (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
    ∀ (α : S.L i) (t : Balanced K (S.L (S.fibreMap N l)) (S.baseChangeField N l)
        (S.baseChangeField N l) (S.M i (S.fibreMap N l))),
      (S.repEdgeFibreIdent N i l).symm (α • t) = α • (S.repEdgeFibreIdent N i l).symm t := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.towerVertexBC N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := fun a => S.algKBCAt N i a
  letI := fun a => S.algVertexBCAt N i a
  letI := fun a => S.algLeftBCEdgeAt N i a l
  letI := S.algLeftPiBCEdge N i l
  letI := S.algLeftTensorBC N i l
  letI := fun a => S.algRightBCEdge N i l a
  letI := S.algPiBCEdge N i l
  letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
    (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
  intro α t
  have h := S.repEdgeFibreIdent_smulL N i l α ((S.repEdgeFibreIdent N i l).symm t)
  rw [LinearEquiv.apply_symm_apply] at h
  exact ((S.repEdgeFibreIdent N i l).symm_apply_eq).mpr h.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- `E` is `K`-linear — `congrY`'s second obligation. -/
theorem repEdgeFibreIdent_smulK :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    letI := fun a => S.algKBCAt N i a
    letI := fun a => S.algVertexBCAt N i a
    letI := fun a => S.algLeftBCEdgeAt N i a l
    letI := S.algLeftPiBCEdge N i l
    letI := S.algLeftTensorBC N i l
    letI := fun a => S.algRightBCEdge N i l a
    letI := S.algPiBCEdge N i l
    letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
      (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
    letI := fun a => S.algKBCEdge N ⟨i, a⟩ l
    letI := fun a => S.towerKBCEdge N ⟨i, a⟩ l
    letI := S.towerKNBC N l
    letI := fun a => S.smulCommNBCEdge N ⟨i, a⟩ l
    letI := fun a => S.towerNBCEdge N ⟨i, a⟩ l
    letI := fun a => smulCommK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.baseChangeField N l)ᵐᵒᵖ)
    letI := fun a => towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.baseChangeField N l)ᵐᵒᵖ)
    ∀ (c : K) (y : ∀ a : (S.vertexSplitting N i).J, (S.baseChange N).M ⟨i, a⟩ l),
      S.repEdgeFibreIdent N i l (c • y) = c • S.repEdgeFibreIdent N i l y := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.towerVertexBC N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := fun a => S.algKBCAt N i a
  letI := fun a => S.algVertexBCAt N i a
  letI := fun a => S.algLeftBCEdgeAt N i a l
  letI := S.algLeftPiBCEdge N i l
  letI := S.algLeftTensorBC N i l
  letI := fun a => S.algRightBCEdge N i l a
  letI := S.algPiBCEdge N i l
  letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
    (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
  letI := fun a => S.algKBCEdge N ⟨i, a⟩ l
  letI := fun a => S.towerKBCEdge N ⟨i, a⟩ l
  letI := S.towerKNBC N l
  letI := fun a => S.smulCommNBCEdge N ⟨i, a⟩ l
  letI := fun a => S.towerNBCEdge N ⟨i, a⟩ l
  letI := fun a => smulCommK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.baseChangeField N l)ᵐᵒᵖ)
  letI := fun a => towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.baseChangeField N l)ᵐᵒᵖ)
  intro c y
  rw [smul_K_of_tower (C' := S.baseChangeField N l) c y, map_smul, ← Balanced.smul_K]

set_option backward.isDefEq.respectTransparency.types false in
/-- `E.symm` is `K`-linear — `congrY`'s fourth obligation. -/
theorem repEdgeFibreIdent_symm_smulK :
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.towerVertexBC N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    letI := fun a => S.algKBCAt N i a
    letI := fun a => S.algVertexBCAt N i a
    letI := fun a => S.algLeftBCEdgeAt N i a l
    letI := S.algLeftPiBCEdge N i l
    letI := S.algLeftTensorBC N i l
    letI := fun a => S.algRightBCEdge N i l a
    letI := S.algPiBCEdge N i l
    letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
      (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
    letI := fun a => S.algKBCEdge N ⟨i, a⟩ l
    letI := fun a => S.towerKBCEdge N ⟨i, a⟩ l
    letI := S.towerKNBC N l
    letI := fun a => S.smulCommNBCEdge N ⟨i, a⟩ l
    letI := fun a => S.towerNBCEdge N ⟨i, a⟩ l
    letI := fun a => smulCommK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.baseChangeField N l)ᵐᵒᵖ)
    letI := fun a => towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.baseChangeField N l)ᵐᵒᵖ)
    ∀ (c : K) (t : Balanced K (S.L (S.fibreMap N l)) (S.baseChangeField N l)
        (S.baseChangeField N l) (S.M i (S.fibreMap N l))),
      (S.repEdgeFibreIdent N i l).symm (c • t) = c • (S.repEdgeFibreIdent N i l).symm t := by
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.towerVertexBC N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := fun a => S.algKBCAt N i a
  letI := fun a => S.algVertexBCAt N i a
  letI := fun a => S.algLeftBCEdgeAt N i a l
  letI := S.algLeftPiBCEdge N i l
  letI := S.algLeftTensorBC N i l
  letI := fun a => S.algRightBCEdge N i l a
  letI := S.algPiBCEdge N i l
  letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
    (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
  letI := fun a => S.algKBCEdge N ⟨i, a⟩ l
  letI := fun a => S.towerKBCEdge N ⟨i, a⟩ l
  letI := S.towerKNBC N l
  letI := fun a => S.smulCommNBCEdge N ⟨i, a⟩ l
  letI := fun a => S.towerNBCEdge N ⟨i, a⟩ l
  letI := fun a => smulCommK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.baseChangeField N l)ᵐᵒᵖ)
  letI := fun a => towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.baseChangeField N l)ᵐᵒᵖ)
  intro c t
  rw [Balanced.smul_K c t, map_smul,
    ← smul_K_of_tower (C' := S.baseChangeField N l) c ((S.repEdgeFibreIdent N i l).symm t)]


end EFib

set_option backward.isDefEq.respectTransparency.types false in
/-- `W'_{⟨i,a⟩}` as a right `L'_{⟨i,a⟩}`-space, at the `(S.baseChange N).L` head. -/
@[reducible] noncomputable def moduleOpRepSpaceAt (V : EtaleSpecies.Rep S) (i : S.I)
    (a : (S.vertexSplitting N i).J) :
    Module ((S.baseChange N).L ⟨i, a⟩)ᵐᵒᵖ (S.repBaseChangeSpaceAt N V i a) :=
  inferInstanceAs (Module ((S.vertexSplitting N i).F a)ᵐᵒᵖ (S.repBaseChangeSpaceAt N V i a))

set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient `K`-tower of `W'_{⟨i,a⟩}`, at the splitting-factor head. -/
@[reducible] noncomputable def towerKFRepSpaceAt (V : EtaleSpecies.Rep S) (i : S.I)
    (a : (S.vertexSplitting N i).J) :
    letI := S.algKBCAt N i a
    letI := S.algVertexBCAt N i a
    IsScalarTower K ((S.vertexSplitting N i).F a)ᵐᵒᵖ (S.repBaseChangeSpaceAt N V i a) := by
  letI := S.algKBCAt N i a
  letI := S.algVertexBCAt N i a
  exact quotient_isScalarTower (S := K)
    (balancedRel K (S.L i) ((S.vertexSplitting N i).F a) ((S.vertexSplitting N i).F a) (V.W i))

set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient `N`-tower of `W'_{⟨i,a⟩}`, at the splitting-factor head. -/
@[reducible] noncomputable def towerNFRepSpaceAt (V : EtaleSpecies.Rep S) (i : S.I)
    (a : (S.vertexSplitting N i).J) :
    letI := S.algKBCAt N i a
    letI := S.algVertexBCAt N i a
    IsScalarTower N ((S.vertexSplitting N i).F a)ᵐᵒᵖ (S.repBaseChangeSpaceAt N V i a) := by
  letI := S.algKBCAt N i a
  letI := S.algVertexBCAt N i a
  exact quotient_isScalarTower (S := N)
    (balancedRel K (S.L i) ((S.vertexSplitting N i).F a) ((S.vertexSplitting N i).F a) (V.W i))

set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient `K`-tower of `W'_{⟨i,a⟩}`, at the `(S.baseChange N).L` head. -/
@[reducible] noncomputable def towerKOpRepSpaceAt (V : EtaleSpecies.Rep S) (i : S.I)
    (a : (S.vertexSplitting N i).J) :
    letI := S.algKBCAt N i a
    letI := S.algVertexBCAt N i a
    letI := S.algKBCL N ⟨i, a⟩
    letI := S.moduleOpRepSpaceAt N V i a
    IsScalarTower K ((S.baseChange N).L ⟨i, a⟩)ᵐᵒᵖ (S.repBaseChangeSpaceAt N V i a) := by
  letI := S.algKBCAt N i a
  letI := S.algVertexBCAt N i a
  letI := S.algKBCL N ⟨i, a⟩
  letI := S.moduleOpRepSpaceAt N V i a
  exact quotient_isScalarTower (S := K)
    (balancedRel K (S.L i) ((S.vertexSplitting N i).F a) ((S.vertexSplitting N i).F a) (V.W i))

set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient `N`-tower of `W'_{⟨i,a⟩}`, at the `(S.baseChange N).L` head. -/
@[reducible] noncomputable def towerNOpRepSpaceAt (V : EtaleSpecies.Rep S) (i : S.I)
    (a : (S.vertexSplitting N i).J) :
    letI := S.algKBCAt N i a
    letI := S.algVertexBCAt N i a
    letI := S.moduleOpRepSpaceAt N V i a
    IsScalarTower N ((S.baseChange N).L ⟨i, a⟩)ᵐᵒᵖ (S.repBaseChangeSpaceAt N V i a) := by
  letI := S.algKBCAt N i a
  letI := S.algVertexBCAt N i a
  letI := S.moduleOpRepSpaceAt N V i a
  exact quotient_isScalarTower (S := N)
    (balancedRel K (S.L i) ((S.vertexSplitting N i).F a) ((S.vertexSplitting N i).F a) (V.W i))

set_option backward.isDefEq.respectTransparency.types false in
/-- `X ⊗_{L'_k} {}_kM'_ℓ` as a right `L'_ℓ`-space, at the `baseChangeField` head.

**The carrier is an opaque variable on purpose, and that is a measurement.**  Stated at
`S.repBaseChangeSpaceAt` — a `@[reducible] def` that unfolds to a `Balanced` quotient — the
head-crossing `isDefEq` blows up: `maxHeartbeats` raised to `4000000` and the *kernel* still did
not finish, where the analogous existing bridges (`module_baseChangeField_W`,
`module_baseChangeField_tensor`) are instant because their carriers are the opaque projections
`V'.W k`.  Generalising the carrier restores that, and the bridge is then applied at the reducible
carrier with no cost.  This is `DESIGN-NOTES` §53.3's limits rule: the convenience that caused the
blow-up was *stating the bridge at the carrier it is used at*, and naming it removed the need for
any raised dial. -/
@[reducible] noncomputable def moduleOpTensorOf (k l : S.baseChangeIndex N) (X : Type u)
    [AddCommGroup X] [Module N X] [Module ((S.baseChange N).L k)ᵐᵒᵖ X]
    [IsScalarTower N ((S.baseChange N).L k)ᵐᵒᵖ X] :
    Module (S.baseChangeField N l)ᵐᵒᵖ (EtaleSpecies.Rep.tensor (S.baseChange N) k l X) :=
  inferInstanceAs
    (Module ((S.baseChange N).L l)ᵐᵒᵖ (EtaleSpecies.Rep.tensor (S.baseChange N) k l X))

section Summand
variable (V : EtaleSpecies.Rep S) (i : S.I) (a : (S.vertexSplitting N i).J)
  (l : S.baseChangeIndex N)

set_option backward.isDefEq.respectTransparency.types false in
/-- **B6 at the summand**: the `a`-th summand of the fibre sum, re-based from `N` to `K`. -/
noncomputable def summandOverK :
    letI := S.algKBCAt N i a
    letI := S.algVertexBCAt N i a
    letI := S.towerVertexBCKAt N i a
    letI := S.towerKNBCAt N i a
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.algKBCL N ⟨i, a⟩
    letI := S.algKBCL N l
    letI := S.towerKBCL N l
    letI := S.towerKNBC N l
    letI := S.smulCommNBCEdge N ⟨i, a⟩ l
    letI := S.towerNBCEdge N ⟨i, a⟩ l
    letI := S.algKBCEdge N ⟨i, a⟩ l
    letI := S.towerKBCEdge N ⟨i, a⟩ l
    letI := S.algLeftBCEdgeAt N i a l
    letI := S.towerLeftBCEdgeAt N i a l
    letI := S.smulCommLeftBCEdgeAt N i a l
    letI := S.moduleFBCEdgeAt N i a l
    letI := S.towerNFBCEdgeAt N i a l
    letI := S.smulCommFBCEdgeAt N i a l
    letI := smulCommK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.baseChangeField N l)ᵐᵒᵖ)
    letI := towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.baseChangeField N l)ᵐᵒᵖ)
    letI := towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.vertexSplitting N i).F a)
    letI := S.moduleOpRepSpaceAt N V i a
    letI := S.towerKFRepSpaceAt N V i a
    letI := S.towerNFRepSpaceAt N V i a
    letI := S.towerKOpRepSpaceAt N V i a
    letI := S.towerNOpRepSpaceAt N V i a
    letI := S.moduleOpTensorOf N ⟨i, a⟩ l (S.repBaseChangeSpaceAt N V i a)
    EtaleSpecies.Rep.tensor (S.baseChange N) ⟨i, a⟩ l (S.repBaseChangeSpaceAt N V i a)
      ≃ₗ[(S.baseChangeField N l)ᵐᵒᵖ]
        Balanced K ((S.vertexSplitting N i).F a) (S.baseChangeField N l)
          ((S.baseChange N).M ⟨i, a⟩ l) (S.repBaseChangeSpaceAt N V i a) := by
  letI := S.algKBCAt N i a
  letI := S.algVertexBCAt N i a
  letI := S.towerVertexBCKAt N i a
  letI := S.towerKNBCAt N i a
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.algKBCL N ⟨i, a⟩
  letI := S.algKBCL N l
  letI := S.towerKBCL N l
  letI := S.towerKNBC N l
  letI := S.smulCommNBCEdge N ⟨i, a⟩ l
  letI := S.towerNBCEdge N ⟨i, a⟩ l
  letI := S.algKBCEdge N ⟨i, a⟩ l
  letI := S.towerKBCEdge N ⟨i, a⟩ l
  letI := S.algLeftBCEdgeAt N i a l
  letI := S.towerLeftBCEdgeAt N i a l
  letI := S.smulCommLeftBCEdgeAt N i a l
  letI := S.moduleFBCEdgeAt N i a l
  letI := S.towerNFBCEdgeAt N i a l
  letI := S.smulCommFBCEdgeAt N i a l
  letI := smulCommK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.baseChangeField N l)ᵐᵒᵖ)
  letI := towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.baseChangeField N l)ᵐᵒᵖ)
  letI := towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.vertexSplitting N i).F a)
  letI := S.moduleOpRepSpaceAt N V i a
  letI := S.towerKFRepSpaceAt N V i a
  letI := S.towerNFRepSpaceAt N V i a
  letI := S.towerKOpRepSpaceAt N V i a
  letI := S.towerNOpRepSpaceAt N V i a
  letI := S.moduleOpTensorOf N ⟨i, a⟩ l (S.repBaseChangeSpaceAt N V i a)
  exact (Balanced.baseFieldEquiv K N ((S.vertexSplitting N i).F a) (S.baseChangeField N l)
    ((S.baseChange N).M ⟨i, a⟩ l) (S.repBaseChangeSpaceAt N V i a)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- **B4 + B5 + B2 at the summand**: `(W_i ⊗_{L_i} L'_a) ⊗_{L'_a} {}_{⟨i,a⟩}M'_ℓ
≃ W_i ⊗_{L_i} {}_{⟨i,a⟩}M'_ℓ`. -/
noncomputable def summandIdent :
    letI := S.algKBCAt N i a
    letI := S.algVertexBCAt N i a
    letI := S.towerVertexBCKAt N i a
    letI := S.towerKNBCAt N i a
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.algKBCL N ⟨i, a⟩
    letI := S.algKBCL N l
    letI := S.towerKBCL N l
    letI := S.towerKNBC N l
    letI := S.smulCommNBCEdge N ⟨i, a⟩ l
    letI := S.towerNBCEdge N ⟨i, a⟩ l
    letI := S.algKBCEdge N ⟨i, a⟩ l
    letI := S.towerKBCEdge N ⟨i, a⟩ l
    letI := S.algLeftBCEdgeAt N i a l
    letI := S.towerLeftBCEdgeAt N i a l
    letI := S.smulCommLeftBCEdgeAt N i a l
    letI := S.moduleFBCEdgeAt N i a l
    letI := S.towerNFBCEdgeAt N i a l
    letI := S.smulCommFBCEdgeAt N i a l
    letI := smulCommK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.baseChangeField N l)ᵐᵒᵖ)
    letI := towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.baseChangeField N l)ᵐᵒᵖ)
    letI := towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.vertexSplitting N i).F a)
    letI := S.moduleOpRepSpaceAt N V i a
    letI := S.towerKFRepSpaceAt N V i a
    letI := S.towerNFRepSpaceAt N V i a
    letI := S.towerKOpRepSpaceAt N V i a
    letI := S.towerNOpRepSpaceAt N V i a
    letI := S.moduleOpTensorOf N ⟨i, a⟩ l (S.repBaseChangeSpaceAt N V i a)
    letI := S.towerLiFBCEdgeAt N i a l
    letI := Balanced.moduleLeftOfY K (S.L i) ((S.vertexSplitting N i).F a)
      (S.baseChangeField N l) ((S.vertexSplitting N i).F a) ((S.baseChange N).M ⟨i, a⟩ l)
    letI := Balanced.towerLeftOfY K (S.L i) ((S.vertexSplitting N i).F a)
      (S.baseChangeField N l) ((S.vertexSplitting N i).F a) ((S.baseChange N).M ⟨i, a⟩ l)
    letI := Balanced.smulCommLeftOfY K (S.L i) ((S.vertexSplitting N i).F a)
      (S.baseChangeField N l) ((S.vertexSplitting N i).F a) ((S.baseChange N).M ⟨i, a⟩ l)
    EtaleSpecies.Rep.tensor (S.baseChange N) ⟨i, a⟩ l (S.repBaseChangeSpaceAt N V i a)
      ≃ₗ[(S.baseChangeField N l)ᵐᵒᵖ]
        Balanced K (S.L i) (S.baseChangeField N l) ((S.baseChange N).M ⟨i, a⟩ l) (V.W i) := by
  letI := S.algKBCAt N i a
  letI := S.algVertexBCAt N i a
  letI := S.towerVertexBCKAt N i a
  letI := S.towerKNBCAt N i a
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.algKBCL N ⟨i, a⟩
  letI := S.algKBCL N l
  letI := S.towerKBCL N l
  letI := S.towerKNBC N l
  letI := S.smulCommNBCEdge N ⟨i, a⟩ l
  letI := S.towerNBCEdge N ⟨i, a⟩ l
  letI := S.algKBCEdge N ⟨i, a⟩ l
  letI := S.towerKBCEdge N ⟨i, a⟩ l
  letI := S.algLeftBCEdgeAt N i a l
  letI := S.towerLeftBCEdgeAt N i a l
  letI := S.smulCommLeftBCEdgeAt N i a l
  letI := S.moduleFBCEdgeAt N i a l
  letI := S.towerNFBCEdgeAt N i a l
  letI := S.smulCommFBCEdgeAt N i a l
  letI := smulCommK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.baseChangeField N l)ᵐᵒᵖ)
  letI := towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.baseChangeField N l)ᵐᵒᵖ)
  letI := towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.vertexSplitting N i).F a)
  letI := S.moduleOpRepSpaceAt N V i a
  letI := S.towerKFRepSpaceAt N V i a
  letI := S.towerNFRepSpaceAt N V i a
  letI := S.towerKOpRepSpaceAt N V i a
  letI := S.towerNOpRepSpaceAt N V i a
  letI := S.moduleOpTensorOf N ⟨i, a⟩ l (S.repBaseChangeSpaceAt N V i a)
  letI := S.towerLiFBCEdgeAt N i a l
  letI := Balanced.moduleLeftOfY K (S.L i) ((S.vertexSplitting N i).F a)
    (S.baseChangeField N l) ((S.vertexSplitting N i).F a) ((S.baseChange N).M ⟨i, a⟩ l)
  letI := Balanced.towerLeftOfY K (S.L i) ((S.vertexSplitting N i).F a)
    (S.baseChangeField N l) ((S.vertexSplitting N i).F a) ((S.baseChange N).M ⟨i, a⟩ l)
  letI := Balanced.smulCommLeftOfY K (S.L i) ((S.vertexSplitting N i).F a)
    (S.baseChangeField N l) ((S.vertexSplitting N i).F a) ((S.baseChange N).M ⟨i, a⟩ l)
  refine (S.summandOverK N V i a l).trans ((Balanced.assoc K (S.L i)
    ((S.vertexSplitting N i).F a) (S.baseChangeField N l) ((S.vertexSplitting N i).F a)
    ((S.baseChange N).M ⟨i, a⟩ l) (V.W i)).trans
      (Balanced.congrY (K := K) (A := S.L i) (B := S.baseChangeField N l) (X := V.W i)
        (Balanced.unitX K ((S.vertexSplitting N i).F a) (S.baseChangeField N l)) ?_ ?_ ?_ ?_))
  · intro α y
    refine balanced_smul_ext (Balanced.unitX K ((S.vertexSplitting N i).F a)
      (S.baseChangeField N l)).toAddMonoidHom α (fun u m => ?_) y
    show (α • u) • m = α • (u • m)
    rw [smul_assoc]
  · intro c y
    refine balanced_smul_ext (Balanced.unitX K ((S.vertexSplitting N i).F a)
      (S.baseChangeField N l)).toAddMonoidHom c (fun u m => ?_) y
    rw [Balanced.smul_K_mk]
    show u • ((algebraMap K (S.baseChangeField N l)ᵐᵒᵖ) c • m) = c • (u • m)
    rw [smul_K_of_tower (C' := S.baseChangeField N l) c (u • m), smul_comm]
  · intro α m
    show Balanced.mk (K := K) (A := (S.vertexSplitting N i).F a)
        (B := S.baseChangeField N l) (1 : (S.vertexSplitting N i).F a) (α • m)
      = Balanced.mk (α • (1 : (S.vertexSplitting N i).F a)) m
    have hb : (α • (1 : (S.vertexSplitting N i).F a))
        = MulOpposite.op (algebraMap (S.L i) ((S.vertexSplitting N i).F a) α)
            • (1 : (S.vertexSplitting N i).F a) := by
      rw [Algebra.smul_def, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, mul_one, one_mul]
    rw [hb]
    exact (Balanced.mk_smul _ _ _).symm
  · intro c m
    show Balanced.mk (K := K) (A := (S.vertexSplitting N i).F a)
        (B := S.baseChangeField N l) (1 : (S.vertexSplitting N i).F a) (c • m)
      = c • Balanced.mk (1 : (S.vertexSplitting N i).F a) m
    rw [Balanced.smul_K_mk,
      smul_K_of_tower (C' := S.baseChangeField N l) c m]

end Summand

section Assembly
variable (V : EtaleSpecies.Rep S) (i : S.I) (l : S.baseChangeIndex N)

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The fibre-summed identification `c`** (clause `RQ2-2.18-C3`, repaired per finding
`S5-F10`). -/
noncomputable def repBaseChangeIdent :
    letI := S.algKBC N l
    letI := S.algVertexBC N l
    letI := S.algKBCL N l
    letI := S.towerKBCL N l
    letI := S.towerKNBC N l
    letI := S.algRightEdge N i (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.algRightM i (S.fibreMap N l)
    letI := S.towerRightM i (S.fibreMap N l)
    letI := S.algRightVertex N (S.fibreMap N l)
    letI := S.towerVertexBC N l
    letI := S.algLeftEdge N i (S.fibreMap N l)
    letI := S.towerLeftEdge N i (S.fibreMap N l)
    letI := S.algEdgeInner N i l
    letI := fun a => S.algVertexFieldAt N i a
    letI := S.algLeftPiBCEdge N i l
    letI := S.algLeftTensorBC N i l
    letI := fun a => S.algRightBCEdge N i l a
    letI := S.algPiBCEdge N i l
    letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
      (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
    letI := Balanced.towerLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
      (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
    letI := Balanced.smulCommLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
      (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
    letI := fun a => S.algKBCAt N i a
    letI := fun a => S.algVertexBCAt N i a
    letI := fun a => S.towerVertexBCKAt N i a
    letI := fun a => S.moduleOpRepSpaceAt N V i a
    letI := fun a => S.towerKOpRepSpaceAt N V i a
    letI := fun a => S.towerNOpRepSpaceAt N V i a
    letI := fun a => S.towerKFRepSpaceAt N V i a
    letI := fun a => S.towerNFRepSpaceAt N V i a
    letI := fun a => S.towerKNBCAt N i a
    letI := fun a => S.algKBCL N ⟨i, a⟩
    letI := fun a => S.algKBCEdge N ⟨i, a⟩ l
    letI := fun a => S.towerKBCEdge N ⟨i, a⟩ l
    letI := fun a => S.algLeftBCEdgeAt N i a l
    letI := fun a => S.towerLeftBCEdgeAt N i a l
    letI := fun a => S.smulCommLeftBCEdgeAt N i a l
    letI := fun a => S.moduleFBCEdgeAt N i a l
    letI := fun a => S.smulCommFBCEdgeAt N i a l
    letI := fun a => S.towerNFBCEdgeAt N i a l
    letI := fun a => S.towerLiFBCEdgeAt N i a l
    letI := fun a => S.smulCommNBCEdge N ⟨i, a⟩ l
    letI := fun a => S.towerNBCEdge N ⟨i, a⟩ l
    letI := fun a => smulCommK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.baseChangeField N l)ᵐᵒᵖ)
    letI := fun a => towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.baseChangeField N l)ᵐᵒᵖ)
    letI := fun a => towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
      (R := (S.vertexSplitting N i).F a)
    letI := fun a => S.moduleOpTensorOf N ⟨i, a⟩ l (S.repBaseChangeSpaceAt N V i a)
    (∀ a : (S.vertexSplitting N i).J,
        EtaleSpecies.Rep.tensor (S.baseChange N) ⟨i, a⟩ l (S.repBaseChangeSpaceAt N V i a))
      ≃ₗ[(S.baseChangeField N l)ᵐᵒᵖ] S.repTensorBaseChangeAt N V i l := by
  classical
  letI := Fintype.ofFinite (S.vertexSplitting N i).J
  letI := S.algKBC N l
  letI := S.algVertexBC N l
  letI := S.algKBCL N l
  letI := S.towerKBCL N l
  letI := S.towerKNBC N l
  letI := S.algRightEdge N i (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.algRightM i (S.fibreMap N l)
  letI := S.towerRightM i (S.fibreMap N l)
  letI := S.algRightVertex N (S.fibreMap N l)
  letI := S.towerVertexBC N l
  letI := S.algLeftEdge N i (S.fibreMap N l)
  letI := S.towerLeftEdge N i (S.fibreMap N l)
  letI := S.algEdgeInner N i l
  letI := fun a => S.algVertexFieldAt N i a
  letI := S.algLeftPiBCEdge N i l
  letI := S.algLeftTensorBC N i l
  letI := fun a => S.algRightBCEdge N i l a
  letI := S.algPiBCEdge N i l
  letI := Balanced.moduleLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
    (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
  letI := Balanced.towerLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
    (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
  letI := Balanced.smulCommLeftOfY K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
    (S.M i (S.fibreMap N l)) (S.baseChangeField N l)
  letI := fun a => S.algKBCAt N i a
  letI := fun a => S.algVertexBCAt N i a
  letI := fun a => S.towerVertexBCKAt N i a
  letI := fun a => S.moduleOpRepSpaceAt N V i a
  letI := fun a => S.towerKOpRepSpaceAt N V i a
  letI := fun a => S.towerNOpRepSpaceAt N V i a
  letI := fun a => S.towerKFRepSpaceAt N V i a
  letI := fun a => S.towerNFRepSpaceAt N V i a
  letI := fun a => S.towerKNBCAt N i a
  letI := fun a => S.algKBCL N ⟨i, a⟩
  letI := fun a => S.algKBCEdge N ⟨i, a⟩ l
  letI := fun a => S.towerKBCEdge N ⟨i, a⟩ l
  letI := fun a => S.algLeftBCEdgeAt N i a l
  letI := fun a => S.towerLeftBCEdgeAt N i a l
  letI := fun a => S.smulCommLeftBCEdgeAt N i a l
  letI := fun a => S.moduleFBCEdgeAt N i a l
  letI := fun a => S.smulCommFBCEdgeAt N i a l
  letI := fun a => S.towerNFBCEdgeAt N i a l
  letI := fun a => S.towerLiFBCEdgeAt N i a l
  letI := fun a => S.smulCommNBCEdge N ⟨i, a⟩ l
  letI := fun a => S.towerNBCEdge N ⟨i, a⟩ l
  letI := fun a => smulCommK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.baseChangeField N l)ᵐᵒᵖ)
  letI := fun a => towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.baseChangeField N l)ᵐᵒᵖ)
  letI := fun a => towerK_of_tower K N (M₁ := (S.baseChange N).M ⟨i, a⟩ l)
    (R := (S.vertexSplitting N i).F a)
  letI := fun a => S.moduleOpTensorOf N ⟨i, a⟩ l (S.repBaseChangeSpaceAt N V i a)
  have e1 := LinearEquiv.piCongrRight (fun a => S.summandIdent N V i a l)
  have e2 := (Balanced.piY (K := K) (A := S.L i) (B := S.baseChangeField N l)
    (Y := fun a => (S.baseChange N).M ⟨i, a⟩ l) (X := V.W i)).symm
  have e3 := Balanced.congrY (K := K) (A := S.L i) (B := S.baseChangeField N l) (X := V.W i)
    (S.repEdgeFibreIdent N i l) (S.repEdgeFibreIdent_smulL N i l)
    (S.repEdgeFibreIdent_smulK N i l) (S.repEdgeFibreIdent_symm_smulL N i l)
    (S.repEdgeFibreIdent_symm_smulK N i l)
  have e4 := (Balanced.assoc K (S.L i) (S.L (S.fibreMap N l)) (S.baseChangeField N l)
    (S.M i (S.fibreMap N l)) (S.baseChangeField N l) (V.W i)).symm
  exact e1.trans (e2.trans (e3.trans e4))

end Assembly


/-- The `L_i`-action of `Rep.moduleL_W` is the right one, on the nose. -/
theorem smul_moduleL_W (V : EtaleSpecies.Rep S) (i : S.I) (α : S.L i) (w : V.W i) :
    α • w = MulOpposite.op α • w := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Clause `RQ2-2.17-C1` for the base-changed spaces: `W'_k = W_i ⊗_{L_i} L'_k` is a
finite-dimensional right `L'_k`-vector space. -/
theorem finite_repBaseChangeSpace (V : EtaleSpecies.Rep S) (k : S.baseChangeIndex N) :
    letI := S.algKBC N k
    letI := S.algVertexBC N k
    Module.Finite (S.baseChangeField N k)ᵐᵒᵖ (S.repBaseChangeSpace N V k) := by
  letI := S.algKBC N k
  letI := S.algVertexBC N k
  haveI : Module.Finite (S.L (S.fibreMap N k)) (V.W (S.fibreMap N k)) :=
    finite_of_op (S.smul_moduleL_W V (S.fibreMap N k)) (V.finite_W _)
  haveI : Module.Finite K (V.W (S.fibreMap N k)) :=
    Module.Finite.trans (S.L (S.fibreMap N k)) _
  haveI : Module.Finite (S.baseChangeField N k)
      ((S.baseChangeField N k) ⊗[K] (V.W (S.fibreMap N k))) :=
    Module.Finite.base_change K (S.baseChangeField N k) (V.W (S.fibreMap N k))
  haveI : Module.Finite (S.baseChangeField N k)ᵐᵒᵖ
      ((S.baseChangeField N k) ⊗[K] (V.W (S.fibreMap N k))) := by
    refine finite_op_of (fun r x => ?_) inferInstance
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add p q hp hq => rw [smul_add, smul_add, hp, hq]
    | tmul y w =>
        show (r * y) ⊗ₜ[K] w = (y * r) ⊗ₜ[K] w
        rw [mul_comm]
  exact Module.Finite.of_surjective
    (Submodule.mkQ (balancedRel K (S.L (S.fibreMap N k)) (S.baseChangeField N k)
      (S.baseChangeField N k) (V.W (S.fibreMap N k))))
    (Submodule.mkQ_surjective _)

section Space
variable (V : EtaleSpecies.Rep S) (k : S.baseChangeIndex N)

set_option backward.isDefEq.respectTransparency.types false in
/-- `W'_k` as a right `L'_k`-space, at the base-changed head. -/
@[reducible] noncomputable def moduleOpRepSpace :
    Module ((S.baseChange N).L k)ᵐᵒᵖ (S.repBaseChangeSpace N V k) :=
  inferInstanceAs (Module (S.baseChangeField N k)ᵐᵒᵖ (S.repBaseChangeSpace N V k))

set_option backward.isDefEq.respectTransparency.types false in
/-- `W'_k`'s `N`-structure towers over the right `L'_k`-action. -/
@[reducible] noncomputable def towerNOpRepSpace :
    letI := S.moduleOpRepSpace N V k
    IsScalarTower N ((S.baseChange N).L k)ᵐᵒᵖ (S.repBaseChangeSpace N V k) := by
  letI := S.moduleOpRepSpace N V k
  letI := S.algKBC N k
  letI := S.algVertexBC N k
  exact quotient_isScalarTower (S := N)
    (balancedRel K (S.L (S.fibreMap N k)) (S.baseChangeField N k) (S.baseChangeField N k)
      (V.W (S.fibreMap N k)))

end Space

section Bundle
variable (V : EtaleSpecies.Rep S) (k l : S.baseChangeIndex N)

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Clause `RQ2-2.18-C2`**: `f'_{kℓ}` is `f_{ij} ⊗ 1` read off the `k`-th summand of the
fibre-summed identification. -/
noncomputable def repBaseChangeStructMap :
    letI := S.moduleOpRepSpace N V k
    letI := S.towerNOpRepSpace N V k
    letI := S.moduleOpTensorOf N k l (S.repBaseChangeSpace N V k)
    EtaleSpecies.Rep.tensor (S.baseChange N) k l (S.repBaseChangeSpace N V k)
      →ₗ[(S.baseChangeField N l)ᵐᵒᵖ] S.repBaseChangeSpace N V l := by
  letI := S.moduleOpRepSpace N V k
  letI := S.towerNOpRepSpace N V k
  letI := S.moduleOpTensorOf N k l (S.repBaseChangeSpace N V k)
  letI := fun a => S.moduleOpRepSpaceAt N V (S.fibreMap N k) a
  letI := fun a => S.towerNOpRepSpaceAt N V (S.fibreMap N k) a
  letI := fun a => S.moduleOpTensorOf N ⟨S.fibreMap N k, a⟩ l
    (S.repBaseChangeSpaceAt N V (S.fibreMap N k) a)
  exact (S.repBaseChangeMap N V k l).comp
    ((S.repBaseChangeIdent N V (S.fibreMap N k) l).toLinearMap.comp
      (LinearMap.single (S.baseChangeField N l)ᵐᵒᵖ
        (fun a => EtaleSpecies.Rep.tensor (S.baseChange N) ⟨S.fibreMap N k, a⟩ l
          (S.repBaseChangeSpaceAt N V (S.fibreMap N k) a)) k.2))

set_option backward.isDefEq.respectTransparency.types false in
/-- `finite_repBaseChangeSpace` at the base-changed head. -/
theorem finite_repBaseChangeSpaceOp (V : EtaleSpecies.Rep S) (k : S.baseChangeIndex N) :
    letI := S.moduleOpRepSpace N V k
    Module.Finite ((S.baseChange N).L k)ᵐᵒᵖ (S.repBaseChangeSpace N V k) :=
  S.finite_repBaseChangeSpace N V k

/-- **The base-changed representation** `W ⊗_K N` — clauses `RQ2-2.18-C1` and `-C2` bundled. -/
noncomputable def repBaseChangeRep (V : EtaleSpecies.Rep S) :
    EtaleSpecies.Rep (S.baseChange N) where
  W k := S.repBaseChangeSpace N V k
  module_W k := S.moduleOpRepSpace N V k
  module_K_W k := inferInstanceAs (Module N (S.repBaseChangeSpace N V k))
  isScalarTower_W k := S.towerNOpRepSpace N V k
  finite_W k := S.finite_repBaseChangeSpaceOp N V k
  f k l := S.repBaseChangeStructMap N V k l

end Bundle

/-! ### Finding **S5-F10** — `RQ2-2.18-C3` over-counts by the factor `|J(i)|`, compiled

**Dated finding, 2026-08-31 (`WORKFLOW.md` R6 / §7); coordinator-ratified.**  `S5-F2` above
concluded that clause `RQ2-2.18-C3` *survives* the `S3-F2` correction "by monoidality of base
change".  **That conclusion is withdrawn.**  Under the corrected `RQ2-2.05-C5` the clause is not
merely hard to prove — it is **false**, and the two theorems below are the finding, compiled.

**Where the derivation breaks.**  In the chain printed in the module header, step 2 → 3 reads

```
= W_i ⊗_{L_i} L'_k ⊗_{A_i} (M_ij ⊗_K N) ⊗_{A_j} L'_ℓ
= (W_i ⊗_K N)  ⊗_{A_i} (M_ij ⊗_K N) ⊗_{A_j} L'_ℓ     [W_i ⊗_{L_i} A_i = W_i ⊗_K N]
```

The bracketed identity is true, but the step *uses* it to replace `L'_k` by `A_i` — and
`A_i = N ⊗_K L_i = ∏_{k ∈ J(i)} L'_k` is the vertex decomposition itself
(`VertexSplitting.equiv`).  Replacing one factor by the whole product is legitimate only **after
summing over the fibre `J(i)`**, and the chain does it for a single `k`.

**Why that is fatal, not repairable in place.**  Take `V := Species.Rep.ofL` (`W_i = L_i`).  Then
the left-hand side is `{}_kM'_ℓ` and the right-hand side is `{}_iM_j ⊗_{L_j} L'_ℓ`, which does not
mention `k`; and collapsing `∏_{k ∈ J(i)} L'_k = A_i` gives

  `Σ_{k ∈ J(i)} dim_N {}_kM'_ℓ = dim_N ((N ⊗_K {}_iM_j) ⊗_{A_j} L'_ℓ) = dim_N ({}_iM_j ⊗_{L_j} L'_ℓ)`.

So if `C3` held for every `k` we would get `|J(i)| · d = d` with `d = dim_N` of the right-hand
side, forcing `d = 0` whenever `|J(i)| ≥ 2`.  It is not: `{}_iM_j ≠ 0` suffices.  The smallest
witness is `K = ℝ`, `N = ℂ`, one vertex, `L_⋆ = {}_⋆M_⋆⋆ = ℂ`, `left = right = id`: there
`dim_ℂ (ℂ ⊗_ℝ ℂ) = 2` (`Species/BaseChange.lean`, `literal_baseChange_finrank`) forces `|J(⋆)| = 2`
whatever splitting was chosen, and `{}_kM'_ℓ = δ_{kℓ} · ℂ`.

**This is the same over-count `S3-F2` removed from `RQ2-2.05-C5`** — the printed edge formula
doubled `finrank` by exactly this factor — surviving one clause downstream.  Hence `C3`'s repair
is the **fibre-summed** form, `⊕_{k ∈ J(i)}` on the left; see `repBaseChange` below and
`stages/S5/DESIGN-NOTES.md` §67.

The two theorems are the `S5-F6`/`S5-F8` evidence pattern
(`leEpsilon_decomposition_entails_untwisted_base`, `isEdgeDescent_smul`): the refuted statement is
taken as a **hypothesis**, so the record survives the repair that removed it from the tree.
-/

/-- **Finding `S5-F10`, half 1 — the over-count, `rfl`.**  `repTensorBaseChange`, the right-hand
side of `RQ2-2.18-C3`, mentions `k` only through `π(k)`; so for any two indices `a`, `b` of the
*same* fibre `J(i)` the clause's two right-hand sides are not merely isomorphic but **the same
type**.  No `▸`, no transport: `π⟨i,a⟩ = i = π⟨i,b⟩` is definitional (`fibreMap_eq_iff`).

This is what makes the frozen clause over-count: its left-hand side `W'_k ⊗_{L'_k} {}_kM'_ℓ` does
vary with `k` across a fibre, and its right-hand side cannot.

@census none (evidence for finding `S5-F10`) -/
theorem repTensorBaseChange_indep_of_fibre (V : EtaleSpecies.Rep S) (i : S.I)
    (a b : (S.vertexSplitting N i).J) (l : S.baseChangeIndex N) :
    S.repTensorBaseChange N V ⟨i, a⟩ l = S.repTensorBaseChange N V ⟨i, b⟩ l := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **Finding `S5-F10`, half 2 — the frozen clause entails an equivalence it cannot have.**
Given the identification `c` in the shape `RQ2-2.18-C3` was frozen in (one `≃ₗ` for every pair
`k, ℓ`, against `repTensorBaseChange`), the tensor spaces of **any two vertices of one fibre**
become isomorphic — because by `repTensorBaseChange_indep_of_fibre` the two `c`'s land in the same
target.  The dimension count in the section header shows they are not: their dimensions sum to
that one target's.

Stated with `c` as a **hypothesis** rather than read off `repBaseChange`, so that it stays true —
and stays the finding's compiled record — after the fibre-summed repair below.

@census none (evidence for finding `S5-F10`) -/
theorem frozenC3_forces_fibre_independence (V : EtaleSpecies.Rep S)
    (V' : EtaleSpecies.Rep (S.baseChange N))
    (c : ∀ k l, EtaleSpecies.Rep.tensor (S.baseChange N) k l (V'.W k)
            ≃ₗ[(S.baseChangeField N l)ᵐᵒᵖ] S.repTensorBaseChange N V k l)
    (i : S.I) (a b : (S.vertexSplitting N i).J) (l : S.baseChangeIndex N) :
    Nonempty (EtaleSpecies.Rep.tensor (S.baseChange N) ⟨i, a⟩ l (V'.W ⟨i, a⟩)
      ≃ₗ[(S.baseChangeField N l)ᵐᵒᵖ]
        EtaleSpecies.Rep.tensor (S.baseChange N) ⟨i, b⟩ l (V'.W ⟨i, b⟩)) :=
  ⟨(c ⟨i, a⟩ l).trans (c ⟨i, b⟩ l).symm⟩

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Definition** (Base change for representations of étale `K`-species; unlabelled in §2.5,
census `RQ2-2.18`).

For a representation `W = (W_i, f_{ij})` of `S` and an extension `N/K`, writing
`S ⊗_K N = (L'_k, {}_kM'_ℓ)_{k,ℓ ∈ I_N}` (clause `RQ2-2.18-H1`; `RQ2-2.05`'s `baseChange`), and for
`i, j ∈ I`, `k ∈ J(i)`, `ℓ ∈ J(j)` (clause `RQ2-2.18-H2`):

* **(i)** `W'_k := W_i ⊗_{L_i} L'_k` — clause `RQ2-2.18-C1`, `repBaseChangeSpace`;
* **(ii)** `f'_{kℓ} := f_{ij} ⊗ 1` — clause `RQ2-2.18-C2`, `repBaseChangeMap`, read off the
  **`k`-th summand** of `C3` (`LinearMap.single`), which is what the fibre-summed `C3` makes it;
* the identification of clause `RQ2-2.18-C3`, **fibre-summed** per finding `S5-F10`:
  `⊕_{k ∈ J(i)} (W'_k ⊗_{L'_k} {}_kM'_ℓ) = (W_i ⊗_{L_i} {}_iM_j) ⊗_{L_j} L'_ℓ`, with
  `repTensorBaseChangeAt` as its right-hand side;
* and `W ⊗_K N := (W'_k, f'_{kℓ})` **is** a representation of `S ⊗_K N` — clause `RQ2-2.18-C4`,
  the statement below.

The three witnesses are named and pinned: `e` identifies the object's spaces with `(i)`, `c` is the
identification `(iii)`, and the displayed equation says that under them the object's structure maps
are `(ii)`.  So the theorem is about *this* base change, not about some unnamed representation.

@census    RQ2-2.18
@source    def:speciesrepbasechange
@clauses   RQ2-2.18-H1, RQ2-2.18-H2, RQ2-2.18-C1, RQ2-2.18-C2, RQ2-2.18-C3, RQ2-2.18-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.18-C4`, and (notational) on the `⊕` of
`RQ2-2.18-C3`. **Rewritten 2026-10-03** (docstring-only `R-PROC-4` amendment of frozen S5,
coordinator ruling `R-FR-9`, final-release WP-16b, stale item R6) against the amended source (census
r18, AN-37(iii) / S5-F10). Until then this field also listed `H1` and `C2`, and called `C3` "false
as printed". The amended definition is exactly what this theorem states. It is set up for an
**étale** `K`-species (`H1`). It puts `W'_k := W_i ⊗_{L_i} L'_k`. Its (ii) states the canonical
decomposition `(W_i ⊗_{L_i} {}_iM_j) ⊗_{L_j} L'_ℓ = ⊕_{k ∈ J(i)} W'_k ⊗_{L'_k} {}_kM'_ℓ`, summed over
the fibre, and says that an individual summand is in general strictly smaller. It defines `f'_{kℓ}`
as the restriction of `f_{ij} ⊗ 1_{L'_ℓ}` to the `k`-th summand. So `H1`, `C1`, `C2` and `C3` are
literal. The paragraphs this replaces disclosed three things against the first printing: the
non-étale "`K`-species" of `H1`; the subscript `1_{L'_k}` in `C2`; and a per-vertex
`C3` that over-counts by `|J(i)|` against the corrected `RQ2-2.05-C5`. The source has corrected all
three. The compiled evidence for the third, `repTensorBaseChange_indep_of_fibre` and
`frozenC3_forces_fibre_independence`, stays as the record of the withdrawn text.

The finite `⊕` of `C3` is rendered as the dependent product `∀ a : J(i), …`. This is the shape
`RQ2-2.33-C1` already uses, for the same index sets and the same reason (`J(i)` is `Finite`, so
finite product and finite direct sum coincide).

`C4` — "`W ⊗_K N` **is** a representation of `S ⊗_K N`" is rendered existentially, with `C1`, `C2`
and `C3` pinned as the accompanying data, in the shape stage S4 set for `RQ2-2.13-C5`
(`speciesAntiEquivalence`): the object only exists once the row is proved, so at G2 it is an `∃`
whose witnesses are named, not an unnamed claim.  The G4 repair is a named `def` from which this
`∃` is derived, exactly as `baseChangeTransIso` is for `RQ2-2.34`; the `def` is
`EtaleSpecies.repBaseChangeRep` (with `repBaseChangeIdent` supplying `C3`'s `c`), and it is the
witness `refine` supplies below.

> **Dated correction, 2026-09-02 (`WORKFLOW.md` §7 class 7 / R6; G4 finding `V-S5G4-1`).** This
> paragraph named the G4 witness `repBaseChange'`, a constant that has never existed in the tree
> (`#check @RationalQuivers.EtaleSpecies.repBaseChange'` → `Unknown constant`, measured by the G4
> verifier at `4e91e5c`).  The obligation was discharged under the name `repBaseChangeRep`; only
> the name was wrong, and the correction is made in place per the `V-S4G4-3` precedent
> (`PROCESS-CHANGELOG` 2026-08-31).  No statement, proof or clause changes.

*(The `C3` paragraph that closed this field until 2026-10-03, on finding `S5-F10` route R1, is
retired by the rewrite above: the fibre-summed identification it introduced is now the source's own
(ii). `DESIGN-NOTES` §67 keeps its record, and S5-F2's superseded reading is retained under a dated
retraction banner in the module header and in §4.1.1.)*
-/
theorem repBaseChange (V : EtaleSpecies.Rep S) :
    ∃ (V' : EtaleSpecies.Rep (S.baseChange N))
      (e : ∀ k, V'.W k ≃ₗ[(S.baseChangeField N k)ᵐᵒᵖ] S.repBaseChangeSpace N V k)
      (c : ∀ (i : S.I) (l : S.baseChangeIndex N),
             (∀ a : (S.vertexSplitting N i).J,
                EtaleSpecies.Rep.tensor (S.baseChange N) ⟨i, a⟩ l (V'.W ⟨i, a⟩))
               ≃ₗ[(S.baseChangeField N l)ᵐᵒᵖ] S.repTensorBaseChangeAt N V i l),
      ∀ (i : S.I) (a : (S.vertexSplitting N i).J) (l : S.baseChangeIndex N),
        (e l).toLinearMap ∘ₗ (EtaleSpecies.Rep.f' (S.baseChange N) V' ⟨i, a⟩ l)
          = S.repBaseChangeMap N V ⟨i, a⟩ l ∘ₗ (c i l).toLinearMap
              ∘ₗ LinearMap.single (S.baseChangeField N l)ᵐᵒᵖ _ a := by
  refine ⟨S.repBaseChangeRep N V, fun k => LinearEquiv.refl _ _,
    fun i l => S.repBaseChangeIdent N V i l, ?_⟩
  intro i a l
  rfl

/-! ### Finding **S5-F3** — **CLOSED 2026-08-30** by the étale-side instance layer

> **Dated retraction banner (`WORKFLOW.md` R6 / §7).** A STOP+REPORT section stood here recording
> that clause `RQ2-2.18-C2` was **blocked**: `EtaleSpecies.toSpecies` is a plain `def`, so instance
> search could not see through it, and `Balanced.map`'s four parameters could not be brought onto a
> single head. It is **superseded**. The blockage was real and the three workarounds it recorded
> did all fail; what removed it is not any of them, and not the `@[reducible]` amendment either
> (applied, measured against four obligations, and **reverted** — `stages/S5/DESIGN-NOTES.md` §9).
> It is the **étale-side instance layer** of `Species/Rep/Basic.lean` (coordinator ruling option 1,
> 2026-08-30): seven declarations, each *literally* the corresponding `Species`-side projection, so
> the diamond is definitional by construction. `repBaseChangeMap` above is the demonstration the
> ruling asked for — it elaborates, `sorry`-free, with axiom closure
> `{propext, Classical.choice, Quot.sound}`. Full evidence in `DESIGN-NOTES.md` §11.
-/

end EtaleSpecies

end RationalQuivers
