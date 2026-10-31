module

public import RationalQuivers.Species.Basic
public import RationalQuivers.Species.Etale
public import RationalQuivers.Species.Rep.Tensor
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/-!
# Representations of a `K`-species, and of an étale `K`-species

Formalizes the first half of §2.5 of `latex/rational_quivers.tex` (census `RQ2-2.17`), together
with the §2.1 convention that fixes its meaning for étale species (census `RQ2-2.31`).

## Main definitions / results
* `RationalQuivers.Species.RepTensor` — the balanced tensor product
  `W_i ⊗_{L_i} {}_iM_j` of a **right** `L_i`-module with the `(L_i,L_j)`-bimodule `{}_iM_j`.
  mathlib has no tensor product over a non-commutative base (ledger `MD-S5-01`), and the paper's
  `L_i` are division rings, so this is ours; it is built as a quotient of mathlib's
  `⊗[K]` and never as a fresh universal object.
* `RationalQuivers.Species.Rep` — Definition (unlabelled, §2.5; census `RQ2-2.17`): a
  representation `(W, f)` of a `K`-species.
* `RationalQuivers.Species.Rep.Hom`, `Species.Rep.instCategory` — morphisms and the category
  `Rep(S)` of **finite-dimensional** representations (clauses `RQ2-2.17-C4`, `-C5`, `-C6`).
* `RationalQuivers.EtaleSpecies.Rep` — census `RQ2-2.31`: a representation of an étale
  `K`-species *is* a representation of the underlying `K`-species, by definition.
* `RationalQuivers.Species.Rep.ofL`, `Species.Rep.trivialOne` — the G5 inhabitants.

## Implementation notes

**The balanced tensor product (`MD-S5-01`, `DEF-S5-01`).**  The paper's `W_i` is a *right*
`L_i`-vector space and `{}_iM_j` a *left* `L_i`-vector space, with `L_i` a division ring; the
tensor product `W_i ⊗_{L_i} {}_iM_j` is therefore the **balanced** one, which mathlib does not
have: `TensorProduct R M N` requires `[CommSemiring R]` (measured, see `MD-S5-01`).  Since `K` is
central in `L_i` and every space in sight is a `K`-vector space, the balanced product is exactly

  `({}_iM_j ⊗[K] W_i) ⧸ ⟨(a·m) ⊗ w − m ⊗ (w·a) : a ∈ L_i⟩`,

which is what `RepTensor` is.  Two presentation choices, neither of them mathematical:

* the *mathlib* factor order is `{}_iM_j ⊗[K] W_i`, because mathlib's `TensorProduct.leftModule`
  puts an auxiliary module structure on the **left** factor only, and the `L_j`-structure that
  clause `RQ2-2.17-C3` speaks of is the one coming from `{}_iM_j`'s right `L_j`-action.  The
  paper's order is restored by the constructor `RepTensor.mk w m` (`= w ⊗ m`), which is the only
  way pure tensors are ever written below; the quotient carrier itself is never displayed.
* `RepTensor` is an `abbrev`, so that the `AddCommGroup`/`Module` instances of
  `Submodule.Quotient` apply unchanged rather than being restated (`CONVENTIONS.md` §6: do not
  re-`def` what mathlib supplies).

**Right modules.**  Following S3 (`Species/Basic.lean`) a right `L`-vector space is a left
`Lᵐᵒᵖ`-module — mathlib's spelling.  "`f_{ij}` is `L_j`-linear" is therefore
`→ₗ[(S.L j)ᵐᵒᵖ]`, and finite-dimensionality of `W_i` is `Module.Finite (S.L i)ᵐᵒᵖ (W i)`.

**Finite-dimensionality is a field of `Rep`, not of a separate `FDRep`.**  Unlike `RQ2-1.10`
(S2's design decision D7, where the source defines representations first and *then* restricts to
the finite-dimensional ones), clause `RQ2-2.17-C1` puts finite-dimensionality inside the definition
of a representation: "a collection `W = (W_i)` of **finite-dimensional** right `L_i`-vector
spaces".  `Rep S` is therefore already the object type of `Rep(S)` and clause `RQ2-2.17-C6` is the
category instance on it.

**The `K`-structure of `W_i` is a field.**  `W_i` is given as a right `L_i`-space; the ambient
`K`-structure it needs to sit in a `⊗[K]` is *induced*, but mathlib has no global instance
`Module K X` from `Module Lᵐᵒᵖ X` and `Algebra K L` (the same fact S2 recorded as `MD-S2-03`), and
a local one would be a diamond.  So `Rep` carries `module_K_W` as an instance field together with
`smul_K_W`, which pins it to be the induced one — exactly S2's design (B) and S3's
`Species.smul_K_agree`.
-/

universe u

namespace RationalQuivers

open scoped TensorProduct

namespace Species

variable {K : Type u} [Field K] (S : Species K)

/-- `K` is central in `L_j`, so its action on `{}_iM_j` commutes with the right `L_j`-action.
This is what mathlib's `TensorProduct.leftModule` needs in order to put the right `L_j`-action on
`{}_iM_j ⊗[K] X`.

@census none (helper for `RQ2-2.17-C3`)
-/
instance smulCommClass_K_M (i j : S.I) : SMulCommClass K (S.L j)ᵐᵒᵖ (S.M i j) where
  smul_comm c b m := by
    rw [S.smul_K_agree i j c m, S.smul_K_agree i j c (b • m), ← mul_smul, ← mul_smul]
    congr 1
    apply MulOpposite.unop_injective
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op]
    exact (Algebra.commutes _ _).symm

section Tensor

/-- Clause `RQ2-2.01-C3` as a scalar tower: the ambient `K`-structure of `{}_iM_j` is equally the
one induced from the **right** `L_j`-action.  This is `Species.smul_K_agree` in the form
`Species/Rep/Tensor.lean`'s standing assumption (2) wants it.

@census none (helper for `RQ2-2.17-C2`)
-/
instance isScalarTower_right_M (i j : S.I) : IsScalarTower K (S.L j)ᵐᵒᵖ (S.M i j) where
  smul_assoc c b m := by
    have h : (c • b) = MulOpposite.op (algebraMap K (S.L j) c) * b := by
      rw [Algebra.smul_def]; rfl
    rw [h, mul_smul, ← S.smul_K_agree i j c (b • m)]

variable (i j : S.I) (X : Type u) [AddCommGroup X] [Module K X] [Module (S.L i)ᵐᵒᵖ X]
  [IsScalarTower K (S.L i)ᵐᵒᵖ X]

/-- **The tensor product `W_i ⊗_{L_i} {}_iM_j`** of the paper, as a right `L_j`-vector space:
`Species/Rep/Tensor.lean`'s balanced product at `A = L_i`, `B = L_j`, `Y = {}_iM_j`.

The general construction is stated there and mentions nothing of species; here it is only
specialised, so `RepTensor` introduces no new content and inherits `Balanced`'s whole API
(`Balanced.mk` for the pure tensor `w ⊗ m`, `Balanced.mk_smul` for the `L_i`-balancing,
`Balanced.smul_mk` for the `L_j`-action, `Balanced.hom_ext` for the universal property,
`Balanced.map` for `ψ ⊗ 1`).  Ledger `DEF-S5-01`, `MD-S5-01`.

@census none (project definition consumed by clauses `RQ2-2.17-C2`, `RQ2-2.17-C3`)
-/
abbrev RepTensor : Type u := Balanced K (S.L i) (S.L j) (S.M i j) X

end Tensor



/-! ### `RQ2-2.17` — representations of a `K`-species -/

/-- **Definition** (Representation of a `K`-species; unlabelled in the source, census `RQ2-2.17`).

Let `S = (L_i, {}_iM_j)_{i,j ∈ I}` be a `K`-species (clause `RQ2-2.17-H1`, the argument `S`).  A
*representation* of `S` is a pair `(W, f)` consisting of

* a collection `W = (W_i)_{i ∈ I}` of **finite-dimensional right `L_i`-vector spaces**
  (clause `RQ2-2.17-C1`: the fields `W`, `module_W`, `finite_W`), and
* a collection `f = (f_{ij})_{i,j ∈ I}` of maps
  `f_{ij} : W_i ⊗_{L_i} {}_iM_j → W_j` (clause `RQ2-2.17-C2`) that are **`L_j`-linear**
  (clause `RQ2-2.17-C3`).

Since clause `RQ2-2.17-C1` already demands finite-dimensionality, `Rep S` is the object type of
the category `Rep(S)` of clause `RQ2-2.17-C6`; there is no separate `FDRep` here (contrast S2's
design decision **D7** for `RQ2-1.10`, where the source restricts only afterwards).

@census    RQ2-2.17
@source    def:speciesrepresentation
@clauses   RQ2-2.17-H1, RQ2-2.17-C1, RQ2-2.17-C2, RQ2-2.17-C3
@imports   none
@divergence none.  Right `L_i`-vector spaces are left `(L_i)ᵐᵒᵖ`-modules (mathlib's spelling,
already used by S3 for `{}_iM_j`), and `W_i ⊗_{L_i} {}_iM_j` is `Species.RepTensor`, the balanced
tensor product over the — possibly non-commutative — `L_i`, which mathlib does not have
(`MD-S5-01`) and which is built here as a quotient of `⊗[K]`, not as a fresh universal object.
The ambient `K`-structure `module_K_W` is an instance field pinned by `smul_K_W` to be the induced
one, for the reason `MD-S2-03` records: mathlib deliberately has no global instance producing it.
-/
structure Rep (S : Species K) : Type (u + 1) where
  /-- Clause `RQ2-2.17-C1`: the collection `W = (W_i)_{i ∈ I}`. -/
  W : S.I → Type u
  /-- Clause `RQ2-2.17-C1`: each `W_i` is an abelian group. -/
  [addCommGroup_W : ∀ i, AddCommGroup (W i)]
  /-- Clause `RQ2-2.17-C1`: each `W_i` is a **right** `L_i`-vector space. -/
  [module_W : ∀ i, Module (S.L i)ᵐᵒᵖ (W i)]
  /-- The ambient `K`-structure of `W_i`, needed to form `⊗[K]`; pinned by `smul_K_W`. -/
  [module_K_W : ∀ i, Module K (W i)]
  /-- The `K`-structure of `W_i` is the one induced from `L_i` through `K`'s image in the centre.
  Stated as a scalar tower, which is the form `Species/Rep/Tensor.lean`'s standing assumption (3)
  needs in order for `W_i ⊗_{L_i} {}_iM_j` to be the balanced tensor product rather than a proper
  quotient of it (verification finding **V-S5a-2**); `Rep.smul_K_W` is the equation it was
  previously stated as, now derived. -/
  [isScalarTower_W : ∀ i, IsScalarTower K (S.L i)ᵐᵒᵖ (W i)]
  /-- Clause `RQ2-2.17-C1`: each `W_i` is **finite-dimensional** over `L_i`. -/
  [finite_W : ∀ i, Module.Finite (S.L i)ᵐᵒᵖ (W i)]
  /-- Clauses `RQ2-2.17-C2` and `RQ2-2.17-C3`: the `L_j`-linear maps
  `f_{ij} : W_i ⊗_{L_i} {}_iM_j → W_j`. -/
  f : ∀ i j : S.I, S.RepTensor i j (W i) →ₗ[(S.L j)ᵐᵒᵖ] W j

attribute [instance] Rep.addCommGroup_W Rep.module_W Rep.module_K_W Rep.finite_W
  Rep.isScalarTower_W

/-- The `K`-action on `W_i` is the one induced from `L_i`: the equation form of the
`isScalarTower_W` field, and the projection that keeps it live.

@census none (clause witness for `RQ2-2.17-C1`)
-/
theorem Rep.smul_K_W {K : Type u} [Field K] {S : Species K} (V : Species.Rep S) (i : S.I) (c : K)
    (w : V.W i) : c • w = MulOpposite.op (algebraMap K (S.L i) c) • w := by
  have h : (c • (1 : (S.L i)ᵐᵒᵖ)) • w = c • ((1 : (S.L i)ᵐᵒᵖ) • w) := smul_assoc c 1 w
  rw [one_smul, Algebra.smul_def, mul_one] at h
  exact h.symm

namespace Rep

variable {S}

/-- **Definition** (morphisms of representations; part of census `RQ2-2.17`).

A morphism `ψ : (W, f) → (W', f')` is a collection of **`L_i`-linear** maps
`ψ_i : W_i → W'_i` (clause `RQ2-2.17-C4`) such that for all `i, j ∈ I` the square commutes:
`f'_{ij} ∘ (ψ_i ⊗ 1) = ψ_j ∘ f_{ij}` (clause `RQ2-2.17-C5`).

@census none (the morphism half of `RQ2-2.17`; the row is claimed by `Species.Rep`)
@clauses   RQ2-2.17-C4, RQ2-2.17-C5
-/
@[ext]
structure Hom (V V' : Rep S) : Type u where
  /-- Clause `RQ2-2.17-C4`: the `L_i`-linear components `ψ_i : W_i → W'_i`. -/
  ψ : ∀ i, V.W i →ₗ[(S.L i)ᵐᵒᵖ] V'.W i
  /-- Clause `RQ2-2.17-C5`: `f'_{ij} ∘ (ψ_i ⊗ 1) = ψ_j ∘ f_{ij}`. -/
  comm : ∀ i j : S.I,
    (V'.f i j).comp (Balanced.map (V.smul_K_W i) (V'.smul_K_W i) (ψ i) (S.L j))
      = (ψ j).comp (V.f i j)

/-- **Clause `RQ2-2.17-C5` on pure tensors**: the commuting square of a morphism, evaluated at
`w ⊗ m`.  Since pure tensors span `W_i ⊗_{L_i} {}_iM_j` (`Balanced.hom_ext`) this is equivalent to
the bundled square, and it is the form every later proof uses.  It is also the projection that
keeps the `comm` field live (`WORKFLOW.md` G5: no dead bundle field).

@census none (clause witness for `RQ2-2.17-C5`)
@clauses   RQ2-2.17-C5
-/
theorem Hom.comm_mk {V V' : Rep S} (a : Hom V V') (i j : S.I) (w : V.W i) (m : S.M i j) :
    V'.f i j (Balanced.mk (a.ψ i w) m) = a.ψ j (V.f i j (Balanced.mk w m)) := by
  have h := congrArg (fun g => g (Balanced.mk w m)) (a.comm i j)
  simpa using h

/-- The identity morphism.  @census none (helper) -/
def Hom.id (V : Rep S) : Hom V V where
  ψ _ := LinearMap.id
  comm i j := by
    refine Balanced.hom_ext fun x m => ?_
    simp only [LinearMap.comp_apply, Balanced.map_mk, LinearMap.id_coe, id_eq]

/-- Composition of morphisms.  @census none (helper) -/
def Hom.comp {V V' V'' : Rep S} (a : Hom V V') (b : Hom V' V'') : Hom V V'' where
  ψ i := (b.ψ i).comp (a.ψ i)
  comm i j := by
    refine Balanced.hom_ext fun x m => ?_
    have h1 := congrArg (fun g => g (Balanced.mk x m)) (a.comm i j)
    have h2 := congrArg (fun g => g (Balanced.mk (a.ψ i x) m)) (b.comm i j)
    simp only [LinearMap.comp_apply, Balanced.map_mk] at h1 h2 ⊢
    rw [h2, h1]

/-- **Definition** (`Rep(S)`; clause `RQ2-2.17-C6`).  The category of **finite-dimensional**
representations of the `K`-species `S`: objects are `Species.Rep S` (whose `finite_W` field is
clause `RQ2-2.17-C1`'s finite-dimensionality), morphisms are `Species.Rep.Hom`.

@census none (clause witness for `RQ2-2.17-C6`; the row is claimed by `Species.Rep`)
@clauses   RQ2-2.17-C6
-/
instance instCategory (S : Species K) : CategoryTheory.Category.{u, u + 1} (Rep S) where
  Hom V V' := Hom V V'
  id V := Hom.id V
  comp a b := a.comp b
  id_comp _ := by apply Hom.ext; rfl
  comp_id _ := by apply Hom.ext; rfl
  assoc _ _ _ := by apply Hom.ext; rfl

/-- Clause `RQ2-2.17-C1`, the *finite-dimensional* half, in the form downstream proofs use: each
`W_i` is a finitely generated right `L_i`-vector space.  This is the consumer of the `finite_W`
field (`WORKFLOW.md` G5: no dead bundle field).

@census none (clause witness for `RQ2-2.17-C1`)
@clauses   RQ2-2.17-C1
-/
theorem fg_W (V : Rep S) (i : S.I) : (⊤ : Submodule (S.L i)ᵐᵒᵖ (V.W i)).FG :=
  Module.finite_def.mp (V.finite_W i)

/-! ### G5 inhabitants -/

/-- **G5 non-vacuity** (`WORKFLOW.md` §4/G5).  For any `K`-species `S`, the collection
`W_i = L_i` (each division ring as a one-dimensional right vector space over itself) with zero
structure maps is a representation of `S`.  Its spaces are **nonzero**
(`ofL_nontrivial`), so it is not the degenerate `W_i = 0` object.

@census none (G5 inhabitant of `RQ2-2.17`)
-/
def ofL (S : Species K) : Rep S where
  W i := S.L i
  isScalarTower_W i := by
    refine ⟨fun c b a => ?_⟩
    simp only [Algebra.smul_def, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_mul,
      ← mul_assoc]
    have hcomm : MulOpposite.unop ((algebraMap K (S.L i)ᵐᵒᵖ) c) = (algebraMap K (S.L i)) c := rfl
    rw [hcomm, mul_assoc, mul_assoc, ← Algebra.commutes c (MulOpposite.unop b),
      ← mul_assoc, ← mul_assoc, ← Algebra.commutes c a]
  finite_W i := by
    haveI : Module.Finite (S.L i)ᵐᵒᵖ (S.L i)ᵐᵒᵖ := Module.Finite.self _
    refine Module.Finite.of_surjective
      (LinearMap.toSpanSingleton (S.L i)ᵐᵒᵖ (S.L i) 1) (fun a => ⟨MulOpposite.op a, ?_⟩)
    simp [LinearMap.toSpanSingleton_apply, MulOpposite.smul_eq_mul_unop]
  f _ _ := 0


/-- **G5 non-degeneracy**: the spaces of `ofL` are nonzero, so `Rep S` is not inhabited only by
the zero representation.

@census none (G5 non-degeneracy for `RQ2-2.17`)
-/
theorem ofL_nontrivial (S : Species K) (i : S.I) : Nontrivial ((ofL S).W i) :=
  inferInstanceAs (Nontrivial (S.L i))

/-! #### The **non-degenerate** G5 inhabitant (`WORKFLOW.md` §4/G5 item 2, finding `V-S5G4-3`(b))

`ofL` above inhabits `Rep S` for **every** species, which is what G5 item 1 asks for, but its
structure maps are `f _ _ := 0`.  All the content of a species representation lives in `f`
(`RepTensor` is a project-built quotient and `W` is just a vector space), so `ofL` alone leaves
open exactly the degeneracy G5 item 2 exists to exclude: for all the tree said, `Rep S` might be
inhabited only by objects whose structure maps vanish, and every clause quantifying over an
`f_{ij}` would be about nothing.  That is the G4 finding `V-S5G4-3`(b).

The witness is the one-node species `Species.trivial K` (`I = PUnit`, `L_0 = {}_0M_0 = K`) with
`W_0 = K` and `f_{00}` the **multiplication** `K ⊗_K K → K` — which is `Balanced.unitX`, the
balanced product's own unit law, so nothing new is built.  Its structure map is not merely nonzero
but **bijective** (`trivialMul_f_bijective`), and `W_0 ⊗_{L_0} {}_0M_0` is `Nontrivial`
(`trivialMul_repTensor_nontrivial`), which is the second half of the finding: the tree now states
that `RepTensor` is not the zero module.
-/

/-- The structure map of `trivialMul`: multiplication `K ⊗_K K → K`, i.e. `Balanced.unitX` at
`A = B = Y = K`.  Named (rather than inlined) so that its bijectivity is stateable without
unfolding `Species.trivial`.  @census none (G5 inhabitant for `RQ2-2.17`) -/
noncomputable def trivialMulMap (K : Type u) [Field K] (i j : (Species.trivial K).I) :
    Species.RepTensor (Species.trivial K) i j ((ofL (Species.trivial K)).W i)
      ≃ₗ[((Species.trivial K).L j)ᵐᵒᵖ] (ofL (Species.trivial K)).W j :=
  Balanced.unitX K ((Species.trivial K).L i) ((Species.trivial K).L j)

/-- **G5 non-degeneracy** (`WORKFLOW.md` §4/G5 item 2): a representation of a species whose
structure map is **not** zero — the one-node species with `W_0 = K` and `f_{00}` the
multiplication.

@census none (non-degenerate G5 inhabitant of `RQ2-2.17`)
-/
noncomputable def trivialMul (K : Type u) [Field K] : Rep (Species.trivial K) :=
  { ofL (Species.trivial K) with
    f := fun i j => (trivialMulMap K i j).toLinearMap }

/-- The structure map of `trivialMul` is a **bijection** — a fortiori nonzero.  This is what
`ofL` cannot say.  @census none (G5 non-degeneracy for `RQ2-2.17`) -/
theorem trivialMul_f_bijective (K : Type u) [Field K] (i j : (Species.trivial K).I) :
    Function.Bijective ((trivialMul K).f i j) := (trivialMulMap K i j).bijective

/-- `W_i ⊗_{L_i} {}_iM_j` is **not** the zero module in this model: the `RepTensor` quotient does
not collapse.  @census none (G5 non-degeneracy for `RQ2-2.17`) -/
theorem trivialMul_repTensor_nontrivial (K : Type u) [Field K] (i j : (Species.trivial K).I) :
    Nontrivial (Species.RepTensor (Species.trivial K) i j ((trivialMul K).W i)) := by
  haveI : Nontrivial ((trivialMul K).W j) := inferInstanceAs (Nontrivial K)
  exact (trivialMul_f_bijective K i j).surjective.nontrivial

/-- The structure map of `trivialMul` is nonzero — the statement the finding asked for, in the
form it asked for it.  @census none (G5 non-degeneracy for `RQ2-2.17`) -/
theorem trivialMul_f_ne_zero (K : Type u) [Field K] (i j : (Species.trivial K).I) :
    (trivialMul K).f i j ≠ 0 := by
  haveI hnt : Nontrivial ((trivialMul K).W j) := inferInstanceAs (Nontrivial K)
  intro h
  obtain ⟨a, b, hab⟩ := hnt
  obtain ⟨t, ht⟩ := (trivialMul_f_bijective K i j).surjective a
  obtain ⟨s, hs⟩ := (trivialMul_f_bijective K i j).surjective b
  rw [h] at ht hs
  exact hab (ht.symm.trans hs)

/-! ### Nilpotency of a species representation — **`AN-31` RESOLVED BY THE AUTHOR, 2026-08-30**

> **Dated author ruling (`WORKFLOW.md` R6 / §7 sweep).** The author has **confirmed** the
> path-composite reading — *"compositions of edge maps along sufficiently long paths are `0`"* —
> which is exactly `DEF-S2-04` for quiver representations and exactly design decision **D-S5-1**
> below for species. `AN-31` and the parallel S2 nilpotency question are **RESOLVED**; both
> definitions lose their provisional status, and stage S8's `Rep^nil` statements are unblocked.
> The text below is retained unedited, because it is the reasoning that chose the reading the
> author then confirmed, and because the *opposite-direction* risk it records (a `Rep^nil` that is
> too small) is what made the choice non-obvious. Read every "author question" and "pending the
> author" in it as **answered**.

`census/ATTESTATION.md` **AN-31** records that the source *never defines* `Rep^nil(S)` for a
species, although `RQ-5.06` and `RQ-5.09` both conclude `HC ≃ Rep^nil(S(Γ_ℚ))`; clauses
`RQ-5.06-H3` and `RQ-5.09-H3` were added post-freeze (verifier finding **F-2**) precisely to
forbid the tautological reading "`Rep^nil(S)` := the essential image of `Rep^nil(Γ_K)` under `F`",
which would make both corollaries vacuous.

The definition below is therefore **intrinsic** and is the exact species-side analogue of the
reading S2 took for quiver representations (`DEF-S2-04`, the Gabriel–Gelfand reading): a
representation is nilpotent when, for some `n`, **every** composite of structure maps along
**every** chain `i₀ → i₁ → … → i_N` of length `N ≥ n` — with an arbitrary element of `{}_{i_k}M_{i_{k+1}}`
chosen at each step — is zero.  Under `S(−)` a chain of the species is a path of the quiver and
the composite is the corresponding composite of the `φ_e`, so `RQ2-2.29` is expected to restrict to
the nilpotent subcategories; that expectation is `RQ-5.06-H3`/`RQ-5.09-H3`'s content and is
**S8's obligation**, not claimed here.

The weaker reading — "the total endomorphism of `⊕_i W_i` is `IsNilpotent`" — is **rejected** for
the same reason S2 rejected it: it permits cancellation between parallel chains and makes
`Rep^nil` strictly larger.

This is deliberately the **whole** downstream surface: two declarations and no census row.  The
author's one-sentence confirmation (2026-08-30) is now the warrant for the reading; nothing in
stage S5's census rows depends on them either way.
-/

/-- The composite `f_{i_{N-1} i_N} ∘ … ∘ f_{i₀ i₁}` of structure maps along a chain
`i₀ → i₁ → …` of `I`, with the element `m k ∈ {}_{i_k}M_{i_{k+1}}` inserted at step `k`.

@census none (project definition; see the `AN-31` note above)
-/
def pathApply (V : Rep S) (idx : ℕ → S.I) (m : ∀ k, S.M (idx k) (idx (k + 1))) :
    ∀ n : ℕ, V.W (idx 0) → V.W (idx n)
  | 0, w => w
  | (n + 1), w => V.f (idx n) (idx (n + 1)) (Balanced.mk (pathApply V idx m n w) (m n))

/-- **Nilpotent species representation** (the notion the source names but never defines; see the
`AN-31` note above and `ledger/DEFINITIONS.tsv` `DEF-S5-02`).

@census none (project definition; consumed by `RQ-5.06-H3`/`RQ-5.09-H3` at stage S8)
-/
def IsNilpotent (V : Rep S) : Prop :=
  ∃ n : ℕ, ∀ (idx : ℕ → S.I) (m : ∀ k, S.M (idx k) (idx (k + 1))) (N : ℕ), n ≤ N →
    ∀ w : V.W (idx 0), V.pathApply idx m N w = 0

/-- The representation `ofL` — all structure maps zero — is nilpotent: the G5 inhabitant of
`Rep^nil(S)`.

@census none (G5 inhabitant for `IsNilpotent`)
-/
theorem ofL_isNilpotent (S : Species K) : (ofL S).IsNilpotent := by
  refine ⟨1, fun idx m N hN w => ?_⟩
  obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
  rfl

/-- `Rep^nil(S)`, the full subcategory of nilpotent representations, as a mathlib
`ObjectProperty` — so that its fullness is mathlib's and not a private restatement.

@census none (project definition; see the `AN-31` note above)
-/
def _root_.RationalQuivers.Species.RepNil (S : Species K) :
    CategoryTheory.ObjectProperty (Rep S) :=
  fun V => V.IsNilpotent

end Rep

end Species

/-! ### `RQ2-2.31` — representations of an *étale* `K`-species -/

namespace EtaleSpecies

variable {K : Type u} [Field K]

/-- **Remark** (§2.1, census `RQ2-2.31`; the census adjudicator's `UNLABELED-etale-rep-convention`).

A representation of an **étale** `K`-species `S` is *by definition* a representation of the
underlying `K`-species `S.toSpecies` (clause `RQ2-2.31-C1`).  The additional algebra structure on
`{}_iM_j` — the multiplication that makes it a commutative `K`-algebra, which `RQ2-2.02` imposes so
that the original `K`-rational quiver can be reconstructed from the species (`RQ2-2.13`) — is
**not** part of the representation data (clause `RQ2-2.31-C2`, witnessed by
`EtaleSpecies.rep_eq_of_toSpecies_eq`): only the `(L_i,L_j)`-bimodule structure that `toSpecies`
extracts is used.

This convention is load-bearing: it is what fixes the meaning of `RQ2-2.17` for étale species and
hence the right-hand side of `RQ2-2.29`.

@census    RQ2-2.31
@source    rmk:etalerepconvention
@clauses   RQ2-2.31-H1, RQ2-2.31-C1
@imports   none
@divergence none.
-/
abbrev Rep (S : EtaleSpecies.{u} K) : Type (u + 1) := Species.Rep S.toSpecies

/-- Clause `RQ2-2.31-C2`: the representation theory of an étale `K`-species depends **only** on the
underlying `K`-species — the bialgebra structure of `RQ2-2.02` is not part of the data.

@census none (clause witness for `RQ2-2.31-C2`)
@clauses   RQ2-2.31-C2
-/
theorem rep_eq_of_toSpecies_eq {S T : EtaleSpecies.{u} K} (h : S.toSpecies = T.toSpecies) :
    EtaleSpecies.Rep S = EtaleSpecies.Rep T := by rw [EtaleSpecies.Rep, EtaleSpecies.Rep, h]

/-! ### The étale-side instance layer (verification finding **S5-F3**, coordinator ruling option 1)

`EtaleSpecies.toSpecies` is a plain `def`, so instance search does not see through it: the
representation-side instances are stated over `Species.L (toSpecies S)` and are therefore not found
when a goal is phrased over `EtaleSpecies.L S`.  §2.5–§2.6 must constantly relate an étale species
to its underlying species, so the mismatch blocks `RQ2-2.18-C2` and every later row that crosses the
boundary (`stages/S5/DESIGN-NOTES.md` §4.1.2, §9).

Measured first, then built: the **module** side of the boundary is already bridged by stage S3 —
`EtaleSpecies.moduleLeft`, `.moduleRight` and `.isScalarTower_M` are stated at the *étale* head, and
`toSpecies` does not override them, so `S.toSpecies.moduleLeft_M i j` *is* `EtaleSpecies.moduleLeft`
as a term.  Only the **representation** side is missing, and that is what the four instances below
supply.  Each is *literally the corresponding `Species`-side projection*, so the two routes to any
one of these classes are the same term and the diamond is definitional by construction — which is
the difference between this and the `instance : Field (S.toSpecies.L i)` experiment of §9.3, which
changed a `Semiring` path and broke `Algebra K (S.toSpecies.L i)`.
-/

set_option backward.isDefEq.respectTransparency.types false in
/-- `W_i` is a right `L_i`-vector space, at the étale head.  @census none (helper, S5-F3) -/
instance Rep.module_W' (S : EtaleSpecies.{u} K) (V : EtaleSpecies.Rep S) (i : S.I) :
    Module (S.L i)ᵐᵒᵖ (V.W i) := V.module_W i

set_option backward.isDefEq.respectTransparency.types false in
/-- `W_i` as a **left** `L_i`-vector space.  For an étale species `L_i` is commutative, so the
right action of `RQ2-2.17-C1` is equally a left one, read through `RingEquiv.toOpposite` — S3's
`EtaleSpecies.moduleRight` in reverse.  `RQ2-2.27-C4` needs this side, because
`W_{i,K} ⊗_K L_i → W_i` is a map of `L_i`-vector spaces in the ordinary sense.

@census none (helper, S5-F3)
-/
noncomputable instance Rep.moduleL_W (S : EtaleSpecies.{u} K) (V : EtaleSpecies.Rep S)
    (i : S.I) : Module (S.L i) (V.W i) :=
  Module.compHom _ ((RingEquiv.toOpposite (S.L i)).toRingHom)

set_option backward.isDefEq.respectTransparency.types false in
/-- `W_i`'s ambient `K`-structure, at the étale head.  @census none (helper, S5-F3) -/
instance Rep.module_K_W' (S : EtaleSpecies.{u} K) (V : EtaleSpecies.Rep S) (i : S.I) :
    Module K (V.W i) := V.module_K_W i

set_option backward.isDefEq.respectTransparency.types false in
/-- `W_i`'s `K`-structure is the induced one, at the étale head.  @census none (helper, S5-F3) -/
instance Rep.isScalarTower_W' (S : EtaleSpecies.{u} K) (V : EtaleSpecies.Rep S) (i : S.I) :
    IsScalarTower K (S.L i)ᵐᵒᵖ (V.W i) := V.isScalarTower_W i

set_option backward.isDefEq.respectTransparency.types false in
/-- The same tower on the **un-opposed** side, which is the one a base change
`L_i ⊗_K W_{i,K} → W_i` needs (`RQ2-2.27-H2`).  `L_i` is commutative, so the two agree.
@census none (helper, S5-F3) -/
instance Rep.isScalarTower_L_W (S : EtaleSpecies.{u} K) (V : EtaleSpecies.Rep S) (i : S.I) :
    IsScalarTower K (S.L i) (V.W i) where
  smul_assoc c a x := by
    show (MulOpposite.op (c • a)) • x = c • ((MulOpposite.op a) • x)
    rw [← smul_assoc c (MulOpposite.op a) x]
    rfl

/-- The bimodule axiom at the étale head: the left `L_i`- and right `L_j`-actions on `{}_iM_j`
commute.  @census none (helper, S5-F3) -/
instance smulCommClass_M' (S : EtaleSpecies.{u} K) (i j : S.I) :
    SMulCommClass (S.L i) (S.L j)ᵐᵒᵖ (S.M i j) := Species.smulCommClass_M S.toSpecies i j

/-- `{}_iM_j`'s ambient `K`-structure is equally the one induced from the right `L_j`-action, at
the étale head.  (The left-hand tower `IsScalarTower K (S.L i) (S.M i j)` is already S3's
`EtaleSpecies.isScalarTower_M`; only the right-hand one is missing.)

@census none (helper, S5-F3)
-/
instance isScalarTower_right_M' (S : EtaleSpecies.{u} K) (i j : S.I) :
    IsScalarTower K (S.L j)ᵐᵒᵖ (S.M i j) := Species.isScalarTower_right_M S.toSpecies i j

set_option backward.isDefEq.respectTransparency.types false in
/-- `W_i` is finite-dimensional, at the étale head.  @census none (helper, S5-F3) -/
instance Rep.finite_W' (S : EtaleSpecies.{u} K) (V : EtaleSpecies.Rep S) (i : S.I) :
    Module.Finite (S.L i)ᵐᵒᵖ (V.W i) := V.finite_W i

/-- **`W_i ⊗_{L_i} {}_iM_j` at the étale head.**  Definitionally `Species.RepTensor S.toSpecies`,
but written with `EtaleSpecies`'s own projections so that every instance argument is
étale-headed and the six instances above answer it.  This is what closes the S5-F3 boundary for
`RQ2-2.18` and for every §2.6 row that must relate `S(Γ_K)` to its underlying species.

@census none (helper, S5-F3)
-/
abbrev Rep.tensor (S : EtaleSpecies.{u} K) (i j : S.I) (X : Type u) [AddCommGroup X] [Module K X]
    [Module (S.L i)ᵐᵒᵖ X] [IsScalarTower K (S.L i)ᵐᵒᵖ X] : Type u :=
  Balanced K (S.L i) (S.L j) (S.M i j) X

set_option backward.isDefEq.respectTransparency.types false in
/-- The two spellings agree definitionally, which is what makes `Rep.tensor` a re-heading and not
a second object.  @census none (helper, S5-F3) -/
theorem Rep.tensor_eq (S : EtaleSpecies.{u} K) (V : EtaleSpecies.Rep S) (i j : S.I) :
    Rep.tensor S i j (V.W i) = Species.RepTensor S.toSpecies i j (V.W i) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **The structure maps `f_{ij}` at the étale head.**  Definitionally `V.f i j`; the point is the
type, whose every instance argument is now étale-headed.  This is the declaration that makes
`Balanced.map`'s four parameters agree on one head, which is what `RQ2-2.18-C2` needs.

@census none (helper, S5-F3)
-/
def Rep.f' (S : EtaleSpecies.{u} K) (V : EtaleSpecies.Rep S) (i j : S.I) :
    Rep.tensor S i j (V.W i) →ₗ[(S.L j)ᵐᵒᵖ] V.W j := V.f i j

/-- **G5 non-vacuity**: `Rep(S)` is inhabited for every étale `K`-species.

@census none (G5 inhabitant of `RQ2-2.31`)
-/
instance (S : EtaleSpecies.{u} K) : Nonempty (EtaleSpecies.Rep S) := ⟨Species.Rep.ofL _⟩

end EtaleSpecies

end RationalQuivers
