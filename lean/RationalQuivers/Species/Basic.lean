module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

/-!
# `K`-species in the sense of Gabriel–Dlab–Ringel

Formalizes the first definition of §2.1 of `latex/rational_quivers.tex` (census `RQ2-2.01`).

## Main definitions / results
* `RationalQuivers.Species` — a `K`-species `S = (L_i, {}_iM_j)_{i,j ∈ I}` (census `RQ2-2.01`;
  the definition is unlabelled in the source).
* `RationalQuivers.Species.algebraMap_mem_center` — the clause `RQ2-2.01-C1` reading of
  `Algebra K (L i)`: the image of `K` really does land in the *centre* of the division ring `L i`.
* `RationalQuivers.Species.trivial` — the one-node species on `K` itself (G5 inhabitant).

## Implementation notes

**Instance fields.** Every algebraic structure carried by the tuple is an *instance-implicit
field* (`[finite_I : Finite I]`, …). This is the pattern `WORKFLOW`/`CONVENTIONS.md` §3 prescribes
for a standing hypothesis that must survive into the elaborated signature: an instance *binder*
would be silently dropped by Lean from any declaration that does not mention it, whereas a field of
the bundle can never be dropped, and any consumer must produce it to build a `Species`. Consumers
recover the instances with `haveI := S.divisionRing_L i` (see `Species.trivial`). The fields are
instance-implicit purely so that the *later* field types of this very structure elaborate (`Module
(L i) (M i j)` needs `Semiring (L i)`); this is mathlib's own `ModuleCat`/`AlgebraCat` idiom.
`CONVENTIONS.md` §3's "paper hypotheses are explicit arguments" rule targets `Imports.*` hypothesis
bundles, of which this stage has none.

**`K` in the centre.** Clause `RQ2-2.01-C1` asks for a division ring *containing `K` in its centre*.
mathlib's `Algebra K (L i)` for a commutative `K` and a possibly non-commutative `L i` is exactly
that: its `commutes'` field says `algebraMap r * x = x * algebraMap r` for every `x`. Since `K` is a
field and `L i` is nontrivial, `algebraMap` is moreover injective, so `K` is *contained* in the
centre rather than merely mapped there. Both halves are recorded as
`Species.algebraMap_mem_center` and `Species.algebraMap_injective`, so the clause is discharged by a
checked statement and not by a reading of mathlib's definition.

**The two `K`-structures.** The paper asks that the left and right `K`-vector space structures on
`{}_iM_j` agree. We carry a `Module K (M i j)` together with `IsScalarTower K (L i) (M i j)` — so
the ambient `K`-structure *is* the left one — and then `smul_K_agree` says it also equals the right
one. Stating it this way (rather than as an equality of two `Module K` instances) keeps the clause a
first-order equation about elements, which is what `rqaudit clauses` can see.
-/

universe u

namespace RationalQuivers

open scoped MulOpposite

/-- **Definition** (Gabriel, Dlab–Ringel; unlabelled in the source, census `RQ2-2.01`).
A *`K`-species* `S = (L_i, {}_iM_j)_{i,j ∈ I}` is a finite collection `(L_i)_{i ∈ I}` of division
rings containing `K` in their centre, together with, for each pair `i, j ∈ I`, an
`L_i,L_j`-bimodule `{}_iM_j` on which the left and right `K`-vector space structures agree and
which is finite-dimensional over `K`.

The right `L_j`-action is carried, as is mathlib's convention for right modules, as a left action of
the opposite ring `(L j)ᵐᵒᵖ`; `smul_comm_M` is the bimodule axiom that the two actions commute.

@census    RQ2-2.01
@source    def:kspecies
@clauses   RQ2-2.01-H1, RQ2-2.01-C1, RQ2-2.01-C2, RQ2-2.01-C3, RQ2-2.01-C4
@imports   none
@divergence none. The tuple is bundled as a structure rather than presented as a family of separate
parameters, and the right module structure is presented as a left `(L j)ᵐᵒᵖ`-module (mathlib's
spelling for a right module); neither changes the content. `K` in the centre is `Algebra K (L i)`,
see `Species.algebraMap_mem_center`.
-/
structure Species (K : Type u) [Field K] : Type (u + 1) where
  /-- The index set `I`. -/
  I : Type u
  /-- Clause `RQ2-2.01-H1`: the index set is finite. -/
  [finite_I : Finite I]
  /-- The division rings `L_i`. -/
  L : I → Type u
  /-- Clause `RQ2-2.01-C1`: each `L_i` is a division ring. -/
  [divisionRing_L : ∀ i, DivisionRing (L i)]
  /-- Clause `RQ2-2.01-C1`: each `L_i` contains `K` in its centre — mathlib's `Algebra K (L i)`
  for a commutative `K` demands exactly that its image is central (`Algebra.commutes`). -/
  [algebra_L : ∀ i, Algebra K (L i)]
  /-- The bimodules `{}_iM_j`. -/
  M : I → I → Type u
  /-- The additive structure of `{}_iM_j`. -/
  [addCommGroup_M : ∀ i j, AddCommGroup (M i j)]
  /-- Clause `RQ2-2.01-C2`: the left `L_i`-action on `{}_iM_j`. -/
  [moduleLeft_M : ∀ i j, Module (L i) (M i j)]
  /-- Clause `RQ2-2.01-C2`: the right `L_j`-action on `{}_iM_j`, as a left `(L j)ᵐᵒᵖ`-action. -/
  [moduleRight_M : ∀ i j, Module (L j)ᵐᵒᵖ (M i j)]
  /-- Clause `RQ2-2.01-C3`: the ambient `K`-structure of `{}_iM_j`. -/
  [module_K_M : ∀ i j, Module K (M i j)]
  /-- Clause `RQ2-2.01-C2`: the bimodule axiom — the left and right actions commute. -/
  smul_comm_M : ∀ i j (a : L i) (b : (L j)ᵐᵒᵖ) (m : M i j), a • b • m = b • a • m
  /-- Clause `RQ2-2.01-C3`, first half: the ambient `K`-structure is the one induced from the left,
  through `L_i`. -/
  [isScalarTower_M : ∀ i j, IsScalarTower K (L i) (M i j)]
  /-- Clause `RQ2-2.01-C3`, second half: the `K`-structure induced from the *right*, through `L_j`,
  is the same one. Together with `isScalarTower_M` this is "the left and right `K`-vector space
  structures on `{}_iM_j` agree". -/
  smul_K_agree : ∀ i j (c : K) (m : M i j),
    c • m = (MulOpposite.op (algebraMap K (L j) c)) • m
  /-- Clause `RQ2-2.01-C4`: `{}_iM_j` is finite-dimensional over `K`. -/
  [finite_K_M : ∀ i j, Module.Finite K (M i j)]

attribute [instance] Species.finite_I Species.divisionRing_L Species.algebra_L
  Species.addCommGroup_M Species.moduleLeft_M Species.moduleRight_M Species.module_K_M
  Species.isScalarTower_M Species.finite_K_M

namespace Species

variable {K : Type u} [Field K] (S : Species K)

/-- Clause `RQ2-2.01-C1`, "containing `K` in their centre": the image of `K` in `L i` lies in the
centre of `L i`. This is the content of mathlib's `Algebra.commutes` and is recorded here so that
the clause is discharged by a checked statement rather than by a reading of a mathlib definition.

@census none (clause witness for `RQ2-2.01-C1`)
-/
theorem algebraMap_mem_center (i : S.I) (c : K) :
    algebraMap K (S.L i) c ∈ Subring.center (S.L i) :=
  Subring.mem_center_iff.2 fun x => (Algebra.commutes c x).symm

/-- Clause `RQ2-2.01-C1`, "containing": the structure map `K → L i` is injective, so `K` is a
subfield of the centre of `L i` and not merely mapped into it.

@census none (clause witness for `RQ2-2.01-C1`)
-/
theorem algebraMap_injective (i : S.I) : Function.Injective (algebraMap K (S.L i)) :=
  (algebraMap K (S.L i)).injective

/-- Clause `RQ2-2.01-C2`, the bimodule axiom in mathlib's idiom: the left `L_i`-action and the right
`L_j`-action on `{}_iM_j` commute, so mathlib's bimodule API applies to `{}_iM_j`.

@census none (clause witness for `RQ2-2.01-C2`)
-/
instance smulCommClass_M (i j : S.I) : SMulCommClass (S.L i) (S.L j)ᵐᵒᵖ (S.M i j) :=
  ⟨S.smul_comm_M i j⟩

/-- Clause `RQ2-2.01-C3` in the form the source states it: *the left and right `K`-vector space
structures on `{}_iM_j` agree*. The left one acts through `L_i`, the right one through `L_j`, and
this says they are the same map on elements.

@census none (clause witness for `RQ2-2.01-C3`)
-/
theorem smul_K_left_eq_right (i j : S.I) (c : K) (m : S.M i j) :
    (algebraMap K (S.L i) c) • m = (MulOpposite.op (algebraMap K (S.L j) c)) • m := by
  rw [← S.smul_K_agree i j c m, ← IsScalarTower.algebraMap_smul (S.L i) c m]

/-- Clause `RQ2-2.01-H1` in the form the later constructions use: the family of bimodules of `S` is
indexed by the finite set `I × I`.

@census none (clause witness for `RQ2-2.01-H1`)
-/
instance finite_pairs : Finite (S.I × S.I) := inferInstance

/-- Every `{}_iM_j` is a finite-dimensional `K`-vector space (clause `RQ2-2.01-C4`), restated as a
`FiniteDimensional` fact for downstream use.

@census none (helper)
-/
theorem finiteDimensional_M (i j : S.I) : FiniteDimensional K (S.M i j) :=
  S.finite_K_M i j

/-- **G5 inhabitant.** The one-node `K`-species with `L = K` and `{}_0M_0 = K`.

@census none (G5 inhabitant for `Species`)
-/
def trivial (K : Type u) [Field K] : Species K where
  I := PUnit
  L := fun _ => K
  M := fun _ _ => K
  smul_comm_M := fun _ _ a b m => by
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop]
    ring
  smul_K_agree := fun _ _ c m => by
    simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
      Algebra.algebraMap_self_apply]
    ring
  finite_K_M := fun _ _ => inferInstance

instance (K : Type u) [Field K] : Nonempty (Species K) := ⟨trivial K⟩

end Species

end RationalQuivers
