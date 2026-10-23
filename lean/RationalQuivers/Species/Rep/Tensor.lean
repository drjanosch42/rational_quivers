import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Algebra.Module.Opposite
import Mathlib.Algebra.Algebra.Opposite
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The balanced tensor product `X ⊗_A Y` over a non-commutative base

Supporting material for §2.5–§2.6 of `latex/rational_quivers.tex`. Nothing here mentions a quiver,
a species or any other project notion: it is a piece of general algebra that mathlib does not have
(`ledger/MATHLIB-DECISIONS.tsv` **MD-S5-01**, flagged `UPSTREAM-CANDIDATE`), isolated in its own
module so that it can be read — and upstreamed — on its own.

## The gap

`RQ2-2.17` asks for `f_{ij} : W_i ⊗_{L_i} {}_iM_j → W_j` with `W_i` a **right** `L_i`-vector space,
`{}_iM_j` a **left** one, and — by `RQ2-2.01` — `L_i` a **division ring**. mathlib's
`TensorProduct R M N` is declared under `[CommSemiring R]` and has no non-commutative counterpart
(searched two ways, `MD-S5-01`). Stating `RQ2-2.17` only for étale species would narrow clause
`RQ2-2.17-H1` — a `WEAKENED_OR_PARTIAL`.

## The construction

Let `K` be a field sitting **centrally** in a ring `A`, let `X` be a right `A`-module and `Y` a
left `A`-module, both `K`-modules. Then the balanced product is the quotient of mathlib's
`K`-tensor product by the balancing relations:

`Balanced K A B Y X = (Y ⊗[K] X) ⧸ ⟨(a·y) ⊗ x − y ⊗ (x·a) : a ∈ A⟩`.

Everything — the `AddCommGroup`, the module structures, the quotient API — is mathlib's; nothing
of mathlib is restated, weakened or forked. Two presentation points:

* **Factor order.** The parameter `B` carries the "far side" action: `Y` is an `(A, B)`-bimodule
  and the quotient inherits `Y`'s right `B`-action, which is what makes `f_{ij}` `L_j`-linear.
  mathlib's `TensorProduct.leftModule` puts an auxiliary module structure on the **left** factor
  only, so `Y` is written on the left internally. The mathematical order is restored by the
  constructor `Balanced.mk x y` (`= x ⊗ y`), the only spelling used anywhere.
* `Balanced` is an `abbrev`, so `Submodule.Quotient`'s instances apply unchanged.

## Main definitions / results
* `RationalQuivers.balancedRel`, `RationalQuivers.Balanced` — the relations and the quotient.
* `Balanced.mk`, `.mk_smul` (the balancing relation), `.mk_add_left`, `.mk_add_right`,
  `.smul_mk` — the constructor and its algebra.
* `Balanced.hom_ext` — the working form of the universal property: two `B`-linear maps out of
  `X ⊗_A Y` agreeing on pure tensors are equal.
* `Balanced.map` — `ψ ⊗ 1` for an `A`-linear `ψ : X → X'`.
-/

universe u

namespace RationalQuivers

open scoped TensorProduct

section Balanced

variable (K : Type u) [Field K]
variable (A : Type u) [Ring A] [Algebra K A]
variable (B : Type u) [Ring B] [Algebra K B]
variable (Y : Type u) [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y]
  [SMulCommClass K Bᵐᵒᵖ Y]
-- **Standing assumption (1)**: `Y` is a genuine `(A,B)`-bimodule — the two actions commute.
variable [SMulCommClass A Bᵐᵒᵖ Y]
-- **Standing assumption (2)**: `Y`'s ambient `K`-structure is the one induced from `A`…
variable [IsScalarTower K A Y]
-- …and equally the one induced from `B`.
variable [IsScalarTower K Bᵐᵒᵖ Y]
variable (X : Type u) [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X]
-- **Standing assumption (3)**: `X`'s ambient `K`-structure is the one induced from `A`.
variable [IsScalarTower K Aᵐᵒᵖ X]

/-- The `A`-balancing generators `(a·y) ⊗ x − y ⊗ (x·a)` inside `Y ⊗[K] X`.

@census none (project definition, `DEF-S5-01`)
-/
def balancedGens : Set (Y ⊗[K] X) :=
  { z | ∃ (a : A) (y : Y) (x : X),
      z = (a • y) ⊗ₜ[K] x - y ⊗ₜ[K] (MulOpposite.op a • x) }

/-- The `A`-balancing relations `(a·y) ⊗ x − y ⊗ (x·a)` inside `Y ⊗[K] X`.

The span is taken over `Bᵐᵒᵖ`, which is what makes the quotient a right `B`-module with no further
argument.  It does **not** thereby impose more than the balancing relations: standing assumption
(1) makes the generating set stable under the `Bᵐᵒᵖ`-action (`smul_mem_balancedGens`), so the
`Bᵐᵒᵖ`-span, the `K`-span and the additive span of `balancedGens` all coincide.  That is the fact
recorded here, and it is the one on which `Balanced` being *the* balanced tensor product — rather
than a proper quotient of it — depends (verification finding **V-S5a-2**).

@census none (project definition, `DEF-S5-01`)
-/
def balancedRel : Submodule Bᵐᵒᵖ (Y ⊗[K] X) :=
  Submodule.span _ (balancedGens K A Y X)

variable {K A B Y X}

/-- **Standing assumption (1) in force**: the balancing generators are stable under the right
`B`-action, because `Y`'s two actions commute.  Consequently the `Bᵐᵒᵖ`-span of `balancedGens` is
its additive span, and `Balanced` is the balanced tensor product and not a proper quotient of it.

@census none (the fact `MD-S5-01` asserted as a side remark; V-S5a-2)
-/
theorem smul_mem_balancedGens (b : Bᵐᵒᵖ) {z : Y ⊗[K] X} (hz : z ∈ balancedGens K A Y X) :
    b • z ∈ balancedGens K A Y X := by
  obtain ⟨a, y, x, rfl⟩ := hz
  refine ⟨a, b • y, x, ?_⟩
  rw [smul_sub, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
    (SMulCommClass.symm A Bᵐᵒᵖ Y).smul_comm]

variable (K A B Y X)

/-- **The balanced tensor product `X ⊗_A Y`** of a right `A`-module `X` with an `(A,B)`-bimodule
`Y`, as a right `B`-module. See the module header; `MD-S5-01`, `DEF-S5-01`.

@census none (project definition, `DEF-S5-01`)
-/
abbrev Balanced : Type u := (Y ⊗[K] X) ⧸ balancedRel K A B Y X

variable {K A B Y X}

/-- The pure tensor `x ⊗ y`, written in the mathematical factor order.

@census none (helper)
-/
def Balanced.mk (x : X) (y : Y) : Balanced K A B Y X :=
  Submodule.Quotient.mk (y ⊗ₜ[K] x)

omit [Algebra K A] in
/-- **The balancing relation** `(x·a) ⊗ y = x ⊗ (a·y)`: this is what makes `Balanced` the tensor
product **over `A`** and not merely over `K`.

@census none (helper: `DEF-S5-01` is balanced)
-/
theorem Balanced.mk_smul (a : A) (x : X) (y : Y) :
    Balanced.mk (K := K) (A := A) (B := B) (MulOpposite.op a • x) y = Balanced.mk x (a • y) := by
  symm
  show Submodule.Quotient.mk (M := Y ⊗[K] X) _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq]
  exact Submodule.subset_span ⟨a, y, x, rfl⟩

omit [Algebra K A] in
/-- Additivity in the first factor.  @census none (helper) -/
theorem Balanced.mk_add_left (x x' : X) (y : Y) :
    Balanced.mk (K := K) (A := A) (B := B) (x + x') y
      = Balanced.mk x y + Balanced.mk x' y := by
  show Submodule.Quotient.mk (M := Y ⊗[K] X) _ = _
  rw [TensorProduct.tmul_add]; rfl

omit [Algebra K A] in
/-- Additivity in the second factor.  @census none (helper) -/
theorem Balanced.mk_add_right (x : X) (y y' : Y) :
    Balanced.mk (K := K) (A := A) (B := B) x (y + y')
      = Balanced.mk x y + Balanced.mk x y' := by
  show Submodule.Quotient.mk (M := Y ⊗[K] X) _ = _
  rw [TensorProduct.add_tmul]; rfl

omit [Algebra K A] in
/-- The right `B`-action on `X ⊗_A Y` is the one coming from `Y`.

@census none (helper)
-/
theorem Balanced.smul_mk (b : Bᵐᵒᵖ) (x : X) (y : Y) :
    b • Balanced.mk (K := K) (A := A) (B := B) x y = Balanced.mk x (b • y) := rfl

section AmbientK

/-- The ambient `K`-structure of `X ⊗_A Y` is mathlib's own: standing assumption (2) gives
`IsScalarTower K Bᵐᵒᵖ (Y ⊗[K] X)`, so `Submodule.Quotient.module'` puts a `K`-module structure on
the quotient with no help from us.  This lemma records that it is the one induced from `B`, which
is what lets `X ⊗_A Y` sit inside a further `⊗[K]` — how `RQ2-2.18` and all of §2.6 use it.

Until verification finding **V-S5a-2** the module carried its own `Module K` instance here, because
without the standing assumptions mathlib could not supply one.  Adding the assumptions made
mathlib's instance available and ours a **diamond**; ours is deleted (`CONVENTIONS.md` §6: do not
restate what mathlib supplies).

@census none (helper)
-/
theorem Balanced.smul_K (c : K) (t : Balanced K A B Y X) :
    c • t = (algebraMap K Bᵐᵒᵖ) c • t := by
  have h : (c • (1 : Bᵐᵒᵖ)) • t = c • ((1 : Bᵐᵒᵖ) • t) := smul_assoc c 1 t
  rw [one_smul, Algebra.smul_def, mul_one] at h
  exact h.symm

/-- The ambient `K`-action on a pure tensor.  @census none (helper) -/
theorem Balanced.smul_K_mk (c : K) (x : X) (y : Y) :
    c • Balanced.mk (K := K) (A := A) (B := B) x y
      = Balanced.mk x ((algebraMap K Bᵐᵒᵖ) c • y) := by
  rw [Balanced.smul_K, Balanced.smul_mk]

end AmbientK

omit [Algebra K A] in
/-- **The universal property, in working form.** Pure tensors span `X ⊗_A Y`, so two `B`-linear
maps out of it that agree on every `x ⊗ y` are equal.

@census none (helper)
-/
theorem Balanced.hom_ext {Z : Type u} [AddCommGroup Z] [Module Bᵐᵒᵖ Z]
    {g h : Balanced K A B Y X →ₗ[Bᵐᵒᵖ] Z}
    (H : ∀ (x : X) (y : Y), g (Balanced.mk x y) = h (Balanced.mk x y)) : g = h := by
  refine LinearMap.ext fun t => ?_
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  induction s with
  | zero => simp
  | tmul y x => exact H x y
  | add s t hs ht =>
      have hmk : Submodule.Quotient.mk (p := balancedRel K A B Y X) (s + t)
          = Submodule.Quotient.mk s + Submodule.Quotient.mk t := rfl
      rw [hmk, map_add, map_add, hs, ht]

/-- **The universal property of `Balanced`**: a `K`-bilinear map that is `A`-**balanced** and
`Bᵐᵒᵖ`-equivariant factors through `X ⊗_A Y`, uniquely.

`Balanced.hom_ext` above is the uniqueness half and was in the tree from the start; this is the
**existence** half, and without it the only maps one can build out of `Balanced` are the
functorial ones (`Balanced.map`, which varies `X` and cannot leave the shape).  Every §2.6
decomposition row needs to leave the shape — that is what a decomposition *is* — so this is where
those proofs start.

`Submodule.liftQ` of `TensorProduct.lift`: the `K`-bilinear map lifts to `Y ⊗[K] X` for free, the
`Bᵐᵒᵖ`-equivariance makes that lift `Bᵐᵒᵖ`-linear, and `hbal` is exactly the statement that it kills
`balancedGens`, hence `balancedRel` (which is their `Bᵐᵒᵖ`-span).

@census none (helper, `DEF-S5-01`'s universal property) -/
def Balanced.lift {Z : Type u} [AddCommGroup Z] [Module K Z] [Module Bᵐᵒᵖ Z]
    [IsScalarTower K Bᵐᵒᵖ Z]
    (f : Y →ₗ[K] X →ₗ[K] Z)
    (hbal : ∀ (a : A) (y : Y) (x : X), f (a • y) x = f y (MulOpposite.op a • x))
    (hB : ∀ (b : Bᵐᵒᵖ) (y : Y) (x : X), f (b • y) x = b • f y x) :
    Balanced K A B Y X →ₗ[Bᵐᵒᵖ] Z := by
  refine Submodule.liftQ _ ?_ ?_
  · exact
      { toFun := TensorProduct.lift f
        map_add' := map_add _
        map_smul' := fun b t => by
          induction t with
          | zero => simp
          | tmul y x =>
              show TensorProduct.lift f ((b • y) ⊗ₜ[K] x) = b • TensorProduct.lift f (y ⊗ₜ[K] x)
              rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul]
              exact hB b y x
          | add s t hs ht => rw [smul_add, map_add, hs, ht, map_add, smul_add] }
  · rw [balancedRel, Submodule.span_le]
    rintro z ⟨a, y, x, rfl⟩
    show TensorProduct.lift f ((a • y) ⊗ₜ[K] x - y ⊗ₜ[K] (MulOpposite.op a • x)) = 0
    rw [map_sub, TensorProduct.lift.tmul, TensorProduct.lift.tmul, hbal a y x, sub_self]

/-- `Balanced.lift` on pure tensors, which is `rfl` — the pinning that makes it usable.
@census none (helper) -/
@[simp] theorem Balanced.lift_mk {Z : Type u} [AddCommGroup Z] [Module K Z] [Module Bᵐᵒᵖ Z]
    [IsScalarTower K Bᵐᵒᵖ Z]
    (f : Y →ₗ[K] X →ₗ[K] Z)
    (hbal : ∀ (a : A) (y : Y) (x : X), f (a • y) x = f y (MulOpposite.op a • x))
    (hB : ∀ (b : Bᵐᵒᵖ) (y : Y) (x : X), f (b • y) x = b • f y x) (x : X) (y : Y) :
    Balanced.lift (A := A) (B := B) f hbal hB (Balanced.mk x y) = f y x := rfl

end Balanced


/-! ### `balancedRel` is already the `K`-span, and the `K`-linear universal property

The module header records, as verification finding **V-S5a-2**, that "the `Bᵐᵒᵖ`-span, the `K`-span
and the additive span of `balancedGens` all coincide" — the fact on which `Balanced` being *the*
balanced tensor product, rather than a proper quotient of it, depends.  Until now that was
**asserted in prose**, with `smul_mem_balancedGens` as its input.  `balancedRel_eq_K` below is the
statement itself, compiled.

It is load-bearing, not tidying.  `Balanced.lift` produces a `→ₗ[Bᵐᵒᵖ]` map and therefore demands
`Bᵐᵒᵖ`-equivariance of its input.  The **nested** construction that finding **S5-F10** forces
`RQ2-2.18-C3` through — `Balanced.assoc`, the monoidality step (`DESIGN-NOTES` §67) — must build the
inner factor as a merely `K`-linear map out of a `Balanced`, and there no such equivariance is
available.  `Balanced.liftK` is that universal property; `balancedRel_eq_K` is exactly what
licenses it.
-/

section LiftK


variable {K : Type u} [Field K]
variable {A : Type u} [Ring A] [Algebra K A]
variable {B : Type u} [Ring B] [Algebra K B]
variable {Y : Type u} [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y]
  [SMulCommClass K Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y] [IsScalarTower K A Y] [IsScalarTower K Bᵐᵒᵖ Y]
variable {X : Type u} [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X]

variable (K A B Y X)

/-- The `K`-span of the balancing generators is stable under the right `B`-action — the
`smul_mem_balancedGens` consequence the module header calls **V-S5a-2**. -/
theorem spanK_smul_mem (b : Bᵐᵒᵖ) {z : Y ⊗[K] X}
    (hz : z ∈ Submodule.span K (balancedGens K A Y X)) :
    b • z ∈ Submodule.span K (balancedGens K A Y X) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · intro w hw; exact Submodule.subset_span (smul_mem_balancedGens (B := B) b hw)
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [smul_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [smul_comm]; exact Submodule.smul_mem _ c hx

/-- The `K`-span of the generators, packaged as the `Bᵐᵒᵖ`-submodule it already is. -/
def balancedRelK : Submodule Bᵐᵒᵖ (Y ⊗[K] X) where
  carrier := Submodule.span K (balancedGens K A Y X)
  add_mem' hx hy := Submodule.add_mem _ hx hy
  zero_mem' := Submodule.zero_mem _
  smul_mem' b _ hz := spanK_smul_mem K A B Y X b hz

/-- **`balancedRel` is the `K`-span** (V-S5a-2): the `Bᵐᵒᵖ`-span and the `K`-span of the balancing
generators coincide, so a merely `K`-linear map that kills the generators kills the relation. -/
theorem balancedRel_eq_K : balancedRel K A B Y X = balancedRelK K A B Y X := by
  refine le_antisymm ?_ ?_
  · rw [balancedRel, Submodule.span_le]; exact fun z hz => Submodule.subset_span hz
  · intro z hz
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
    · exact fun w hw => Submodule.subset_span hw
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy; exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      have : (c : K) • x = (algebraMap K Bᵐᵒᵖ c) • x := by
        have h : (c • (1 : Bᵐᵒᵖ)) • x = c • ((1 : Bᵐᵒᵖ) • x) := smul_assoc c 1 x
        rw [one_smul, Algebra.smul_def, mul_one] at h
        exact h.symm
      rw [this]; exact Submodule.smul_mem _ _ hx

variable {K A B Y X}

/-- **The `K`-linear universal property of `X ⊗_A Y`.**  `Balanced.lift` produces a `Bᵐᵒᵖ`-linear
map and so needs `Bᵐᵒᵖ`-equivariance of `f`; a nested construction (`Balanced.assoc`) needs the
inner factor to be only `K`-linear, where no such equivariance is available.  It is legitimate
because `balancedRel` is already the `K`-span (`balancedRel_eq_K`). -/
def Balanced.liftK {W : Type u} [AddCommGroup W] [Module K W]
    (f : Y →ₗ[K] X →ₗ[K] W)
    (hbal : ∀ (a : A) (y : Y) (x : X), f (a • y) x = f y (MulOpposite.op a • x)) :
    Balanced K A B Y X →ₗ[K] W := by
  refine Submodule.liftQ ((balancedRel K A B Y X).restrictScalars K) (TensorProduct.lift f) ?_
  intro z hz
  have hz' : z ∈ Submodule.span K (balancedGens K A Y X) := by
    rw [Submodule.restrictScalars_mem, balancedRel_eq_K] at hz; exact hz
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz'
  · rintro w ⟨a, y, x, rfl⟩
    refine LinearMap.mem_ker.2 ?_
    show TensorProduct.lift f ((a • y) ⊗ₜ[K] x - y ⊗ₜ[K] (MulOpposite.op a • x)) = 0
    rw [map_sub, TensorProduct.lift.tmul, TensorProduct.lift.tmul, hbal a y x, sub_self]
  · exact Submodule.zero_mem _
  · intro x y _ _ hx hy; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; exact Submodule.smul_mem _ c hx

/-- `Balanced.liftK` on pure tensors, `rfl` — the value guard from birth. -/
@[simp] theorem Balanced.liftK_mk {W : Type u} [AddCommGroup W] [Module K W]
    (f : Y →ₗ[K] X →ₗ[K] W)
    (hbal : ∀ (a : A) (y : Y) (x : X), f (a • y) x = f y (MulOpposite.op a • x)) (x : X) (y : Y) :
    Balanced.liftK (A := A) (B := B) f hbal (Balanced.mk x y) = f y x := rfl

end LiftK

/-! ### Functoriality in the right-module variable -/

section Map

variable {K : Type u} [Field K]
variable {A : Type u} [Ring A] [Algebra K A]
variable {B : Type u} [Ring B]
variable {Y : Type u} [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y]
  [SMulCommClass K Bᵐᵒᵖ Y]
variable {X X' : Type u} [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X]
variable [AddCommGroup X'] [Module K X'] [Module Aᵐᵒᵖ X']

/-- An `A`-linear map between right `A`-modules whose `K`-structures are the induced ones is
`K`-linear.  @census none (helper) -/
theorem smul_K_of_linear
    (hX : ∀ (c : K) (x : X), c • x = MulOpposite.op (algebraMap K A c) • x)
    (hX' : ∀ (c : K) (x : X'), c • x = MulOpposite.op (algebraMap K A c) • x)
    (ψ : X →ₗ[Aᵐᵒᵖ] X') (c : K) (x : X) : ψ (c • x) = c • ψ x := by
  rw [hX, map_smul, hX']

/-- `ψ ⊗ 1` before passing to the quotient.  @census none (helper) -/
def balancedMapAux
    (hX : ∀ (c : K) (x : X), c • x = MulOpposite.op (algebraMap K A c) • x)
    (hX' : ∀ (c : K) (x : X'), c • x = MulOpposite.op (algebraMap K A c) • x)
    (ψ : X →ₗ[Aᵐᵒᵖ] X') : (Y ⊗[K] X) →ₗ[Bᵐᵒᵖ] (Y ⊗[K] X') where
  toFun := LinearMap.lTensor Y
    ({ toFun := ψ, map_add' := map_add ψ,
       map_smul' := fun c x => smul_K_of_linear hX hX' ψ c x } : X →ₗ[K] X')
  map_add' t t' := map_add _ t t'
  map_smul' b t := by
    induction t with
    | zero => simp
    | tmul y x =>
        show LinearMap.lTensor Y _ ((b • y) ⊗ₜ[K] x)
            = b • LinearMap.lTensor Y _ (y ⊗ₜ[K] x)
        simp [TensorProduct.smul_tmul']
    | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, smul_add]

/-- **`ψ ⊗ 1`**: the `B`-linear map `X ⊗_A Y → X' ⊗_A Y` induced by an `A`-linear `ψ : X → X'`.

@census none (helper)
-/
def Balanced.map
    (hX : ∀ (c : K) (x : X), c • x = MulOpposite.op (algebraMap K A c) • x)
    (hX' : ∀ (c : K) (x : X'), c • x = MulOpposite.op (algebraMap K A c) • x)
    (ψ : X →ₗ[Aᵐᵒᵖ] X') (B : Type u) [Ring B] [Module Bᵐᵒᵖ Y] [SMulCommClass K Bᵐᵒᵖ Y] :
    Balanced K A B Y X →ₗ[Bᵐᵒᵖ] Balanced K A B Y X' :=
  Submodule.mapQ _ _ (balancedMapAux (B := B) hX hX' ψ) <| by
    rw [balancedRel, Submodule.span_le]
    rintro z ⟨a, y, x, rfl⟩
    refine Submodule.mem_comap.2 ?_
    have h1 : balancedMapAux (B := B) hX hX' ψ
          ((a • y) ⊗ₜ[K] x - y ⊗ₜ[K] (MulOpposite.op a • x))
        = (a • y) ⊗ₜ[K] ψ x - y ⊗ₜ[K] (MulOpposite.op a • ψ x) := by
      rw [map_sub]
      show (a • y) ⊗ₜ[K] ψ x - y ⊗ₜ[K] ψ (MulOpposite.op a • x) = _
      rw [map_smul]
    rw [h1]
    exact Submodule.subset_span ⟨a, y, ψ x, rfl⟩

/-- `ψ ⊗ 1` on pure tensors.  @census none (helper) -/
@[simp]
theorem Balanced.map_mk
    (hX : ∀ (c : K) (x : X), c • x = MulOpposite.op (algebraMap K A c) • x)
    (hX' : ∀ (c : K) (x : X'), c • x = MulOpposite.op (algebraMap K A c) • x)
    (ψ : X →ₗ[Aᵐᵒᵖ] X') (B : Type u) [Ring B] [Module Bᵐᵒᵖ Y] [SMulCommClass K Bᵐᵒᵖ Y]
    (x : X) (y : Y) :
    Balanced.map hX hX' ψ B (Balanced.mk x y) = Balanced.mk (ψ x) y := rfl

end Map


/-! ### The left action of the `X`-slot, inherited by the product (finding **S5-F10**, `§67`)

`RQ2-2.18-C3`'s repaired, fibre-summed identification is an isomorphism whose right-hand side is
`(W_i ⊗_{L_i} {}_iM_j) ⊗_{L_j} L'_ℓ` and whose left-hand side, after the fibre collapse, is
`W_i ⊗_{L_i} ({}_iM_j ⊗_{L_j} L'_ℓ)`.  Relating the two is the **monoidality of base change** — a
*heterobasic* associativity over two `K`-algebras `L_i`, `L_j` with **no map between them**.

**mathlib does not have it, and cannot be made to**: `TensorProduct.AlgebraTensorModule.assoc`
requires a tower `[Algebra R A]` between its two bases (measured, `Mathlib/LinearAlgebra/
TensorProduct/Tower.lean`), and a species supplies no `L_i → L_j`; the same binder blocks
`cancelBaseChange` from delivering `L'_ℓ`-linearity, since its `B` needs `[Algebra A B]`.  Nor is
there a right-factor `Module` instance on a tensor product — mathlib has `leftModule` only.  So
the bookkeeping has to happen in `Balanced`, which is the structure built for exactly this shape.

**This section is the prerequisite that makes the associativity statable at all.**  To write
`X ⊗_A (Y ⊗_B Z)` one needs `Y ⊗_B Z` to be an `(A, C)`-bimodule, i.e. a left `A`-action on a
`Balanced` inherited from its **`X`-slot** `Y`.  Nothing in mathlib or in this file produced one
(searched by name — `Balanced.assoc|congr|cancel|pi|prod` — and by shape — `Balanced … (Balanced`);
both empty).  It descends because the two actions on `Y` commute (`SMulCommClass A Bᵐᵒᵖ Y`, the
file's standing assumption (1)), which is exactly what `balancedLeftAux_mem` uses.

Not instances: their heads are variable in `A`, `Y` and `Z`, the shape `CONVENTIONS.md` §3 and
`DESIGN-NOTES` §51 forbid as ambient.  Used with `letI`, per carrier.
-/
section LeftOnBalanced
variable {K : Type u} [Field K]
variable {A : Type u} [Ring A] [Algebra K A]
variable {B : Type u} [Ring B] [Algebra K B]
variable {C : Type u} [Ring C] [Algebra K C]
variable {Y : Type u} [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y]
  [SMulCommClass K Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y] [IsScalarTower K A Y] [IsScalarTower K Bᵐᵒᵖ Y]
variable {Z : Type u} [AddCommGroup Z] [Module K Z] [Module B Z] [Module Cᵐᵒᵖ Z]
  [SMulCommClass K Cᵐᵒᵖ Z] [SMulCommClass B Cᵐᵒᵖ Z] [IsScalarTower K B Z] [IsScalarTower K Cᵐᵒᵖ Z]


/-- `a • (z ⊗ y) = z ⊗ (a • y)` on `Z ⊗[K] Y`, as a `Cᵐᵒᵖ`-linear map. -/
noncomputable def balancedLeftAux (K : Type u) [Field K] (A : Type u) [Ring A] [Algebra K A]
    (B C Y Z : Type u) [Ring B] [Algebra K B] [Ring C] [Algebra K C]
    [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y] [SMulCommClass K Bᵐᵒᵖ Y]
    [SMulCommClass A Bᵐᵒᵖ Y] [IsScalarTower K A Y] [IsScalarTower K Bᵐᵒᵖ Y]
    [AddCommGroup Z] [Module K Z] [Module B Z] [Module Cᵐᵒᵖ Z] [SMulCommClass K Cᵐᵒᵖ Z]
    [SMulCommClass B Cᵐᵒᵖ Z] [IsScalarTower K B Z] [IsScalarTower K Cᵐᵒᵖ Z] (a : A) : (Z ⊗[K] Y) →ₗ[Cᵐᵒᵖ] (Z ⊗[K] Y) where
  toFun := LinearMap.lTensor Z ((DistribSMul.toLinearMap K Y a) : Y →ₗ[K] Y)
  map_add' t t' := map_add _ t t'
  map_smul' c t := by
    induction t with
    | zero => simp
    | tmul z y =>
        show LinearMap.lTensor Z _ ((c • z) ⊗ₜ[K] y) = c • LinearMap.lTensor Z _ (z ⊗ₜ[K] y)
        simp [TensorProduct.smul_tmul']
    | add t t' ht ht' => rw [smul_add, map_add, ht, ht', map_add, smul_add]


theorem balancedLeftAux_mem (a : A) {t : Z ⊗[K] Y} (ht : t ∈ balancedRel K B C Z Y) :
    balancedLeftAux K A B C Y Z a t ∈ balancedRel K B C Z Y := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ ht
  · rintro z ⟨b, zz, yy, rfl⟩
    refine Submodule.subset_span ⟨b, zz, a • yy, ?_⟩
    show balancedLeftAux K A B C Y Z a _ = _
    have h : ∀ (z' : Z) (y' : Y),
        balancedLeftAux K A B C Y Z a (z' ⊗ₜ[K] y') = z' ⊗ₜ[K] (a • y') := fun _ _ => rfl
    rw [map_sub, h, h, (SMulCommClass.symm A Bᵐᵒᵖ Y).smul_comm]
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx


variable (K A B C Y Z)

/-- The left `A`-action of `Y`, as a ring map into the `Cᵐᵒᵖ`-endomorphisms of `X ⊗_B Y`. -/
noncomputable def balancedLeftHom :
    A →+* Module.End Cᵐᵒᵖ (Balanced K B C Z Y) where
  toFun a := Submodule.mapQ _ _ (balancedLeftAux K A B C Y Z a)
    (fun t ht => balancedLeftAux_mem a ht)
  map_one' := by
    refine LinearMap.ext fun t => ?_
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K B C Z Y) t
    induction s with
    | zero => simp
    | tmul z y => show Submodule.Quotient.mk (z ⊗ₜ[K] ((1 : A) • y)) = _; rw [one_smul]; rfl
    | add s s' hs hs' =>
        have hmk : Submodule.Quotient.mk (p := balancedRel K B C Z Y) (s + s')
            = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
        rw [hmk, map_add, hs, hs', map_add]
  map_mul' a a' := by
    refine LinearMap.ext fun t => ?_
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K B C Z Y) t
    induction s with
    | zero => simp
    | tmul z y => show Submodule.Quotient.mk (z ⊗ₜ[K] ((a * a') • y)) = _; rw [mul_smul]; rfl
    | add s s' hs hs' =>
        have hmk : Submodule.Quotient.mk (p := balancedRel K B C Z Y) (s + s')
            = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
        rw [hmk, map_add, hs, hs', map_add]
  map_zero' := by
    refine LinearMap.ext fun t => ?_
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K B C Z Y) t
    induction s with
    | zero => simp
    | tmul z y => show Submodule.Quotient.mk (z ⊗ₜ[K] ((0 : A) • y)) = _
                  rw [zero_smul, TensorProduct.tmul_zero]; rfl
    | add s s' hs hs' =>
        have hmk : Submodule.Quotient.mk (p := balancedRel K B C Z Y) (s + s')
            = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
        rw [hmk, map_add, hs, hs']; simp
  map_add' a a' := by
    refine LinearMap.ext fun t => ?_
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K B C Z Y) t
    induction s with
    | zero => simp
    | tmul z y => show Submodule.Quotient.mk (z ⊗ₜ[K] ((a + a') • y)) = _
                  rw [add_smul, TensorProduct.tmul_add]; rfl
    | add s s' hs hs' =>
        have hmk : Submodule.Quotient.mk (p := balancedRel K B C Z Y) (s + s')
            = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
        rw [hmk, map_add, hs, hs', map_add]

/-- **B0**: `X ⊗_B Y` inherits `Y`'s left `A`-action. -/
@[reducible] noncomputable def Balanced.moduleLeftOfY : Module A (Balanced K B C Z Y) :=
  Module.compHom _ (balancedLeftHom K A B C Y Z)


/-- **Value guard for B0, from birth**: the inherited action on a generator, `rfl`. -/
theorem Balanced.moduleLeftOfY_mk (a : A) (y : Y) (z : Z) :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    a • Balanced.mk (K := K) (A := B) (B := C) y z = Balanced.mk (a • y) z := rfl

/-- The `K`-scalar of the `X`-slot moves to the bimodule slot: `mk (c • y) z = mk y (c • z)`. -/
theorem Balanced.mk_smul_K_left (c : K) (y : Y) (z : Z) :
    Balanced.mk (K := K) (A := B) (B := C) (c • y) z
      = Balanced.mk y ((algebraMap K Cᵐᵒᵖ) c • z) := by
  have hz : (algebraMap K Cᵐᵒᵖ) c • z = c • z := by
    have h : (c • (1 : Cᵐᵒᵖ)) • z = c • ((1 : Cᵐᵒᵖ) • z) := smul_assoc c 1 z
    rw [one_smul, Algebra.smul_def, mul_one] at h
    exact h
  rw [hz]
  show Submodule.Quotient.mk (M := Z ⊗[K] Y) (z ⊗ₜ[K] (c • y))
      = Submodule.Quotient.mk ((c • z) ⊗ₜ[K] y)
  rw [TensorProduct.smul_tmul]

/-- B0's tower: the ambient `K`-structure of `X ⊗_B Y` is compatible with the inherited action. -/
@[reducible] noncomputable def Balanced.towerLeftOfY :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    IsScalarTower K A (Balanced K B C Z Y) := by
  letI := Balanced.moduleLeftOfY K A B C Y Z
  refine ⟨fun c a t => ?_⟩
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K B C Z Y) t
  induction s with
  | zero => simp
  | tmul z y =>
      show Balanced.mk (K := K) (A := B) (B := C) ((c • a) • y) z
          = c • Balanced.mk (K := K) (A := B) (B := C) (a • y) z
      rw [smul_assoc, Balanced.smul_K_mk, ← Balanced.mk_smul_K_left]
  | add s s' hs hs' =>
      have hmk : Submodule.Quotient.mk (p := balancedRel K B C Z Y) (s + s')
          = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
      rw [hmk, smul_add, smul_add, smul_add, hs, hs']


/-- B0's bimodule axiom: the inherited left `A`-action commutes with the right `C`-action. -/
@[reducible] noncomputable def Balanced.smulCommLeftOfY :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    SMulCommClass A Cᵐᵒᵖ (Balanced K B C Z Y) := by
  letI := Balanced.moduleLeftOfY K A B C Y Z
  refine ⟨fun a c t => ?_⟩
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K B C Z Y) t
  induction s with
  | zero => simp
  | tmul z y => rfl
  | add s s' hs hs' =>
      have hmk : Submodule.Quotient.mk (p := balancedRel K B C Z Y) (s + s')
          = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
      rw [hmk, smul_add, smul_add, smul_add, smul_add, hs, hs']

end LeftOnBalanced


/-! ### **`Balanced.assoc` — the monoidality of base change** (finding **S5-F10**, `§67`)

`(X ⊗_A Y) ⊗_B Z  ≅  X ⊗_A (Y ⊗_B Z)`.

This is the step `RQ2-2.18-C3`'s repaired, fibre-summed identification turns on, and it is a
*heterobasic* associativity: `A` and `B` are two `K`-algebras with **no map between them**.
mathlib's `TensorProduct.AlgebraTensorModule.assoc` requires a tower `[Algebra R A]` between its
two bases and so does not apply; nor does `cancelBaseChange` (its outer-linearity ring needs
`[Algebra A B]`), nor is there a right-factor `Module` instance to lean on (`leftModule` only).
Measured, by reading those variable blocks — see `DESIGN-NOTES` §67.6.

The construction is a **nested** lift, which is what forces the two pieces above it: the outer
factor is `Balanced.lift` (a `→ₗ[Cᵐᵒᵖ]` map), whose bilinear input's inner factor must be a merely
`K`-linear map out of a `Balanced` — hence `Balanced.liftK` — and whose target must be
`X ⊗_A (Y ⊗_B Z)`, which only exists once `Y ⊗_B Z` carries `Y`'s left `A`-action — hence
`Balanced.moduleLeftOfY`.

**Every intermediate map is named and carries a `rfl` value lemma.**  That is not tidiness: writing
these obligations with `show` instead makes the elaborator unify through the three reducible
instance `letI`s and costs a `whnf`/`isDefEq` heartbeat blow-up (measured, at the default 200000).
Named `rfl` lemmas convert that unification into rewriting — `DESIGN-NOTES` §62.20 — and no
heartbeat dial is touched anywhere in this section.
-/

section Assoc


variable {K : Type u} [Field K]
variable {A : Type u} [Ring A] [Algebra K A]
variable {B : Type u} [Ring B] [Algebra K B]
variable {C : Type u} [Ring C] [Algebra K C]
variable {Y : Type u} [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y]
  [SMulCommClass K Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y] [IsScalarTower K A Y] [IsScalarTower K Bᵐᵒᵖ Y]
variable {Z : Type u} [AddCommGroup Z] [Module K Z] [Module B Z] [Module Cᵐᵒᵖ Z]
  [SMulCommClass K Cᵐᵒᵖ Z] [SMulCommClass B Cᵐᵒᵖ Z] [IsScalarTower K B Z] [IsScalarTower K Cᵐᵒᵖ Z]
variable {X : Type u} [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X]



/-- The `K`-linear form of `Balanced.hom_ext`: pure tensors span, so two `K`-linear maps out of
`X ⊗_A Y` agreeing on every `x ⊗ y` are equal. -/
theorem Balanced.hom_extK {W : Type u} [AddCommGroup W] [Module K W]
    {g h : Balanced K A B Y X →ₗ[K] W}
    (H : ∀ (x : X) (y : Y), g (Balanced.mk x y) = h (Balanced.mk x y)) : g = h := by
  refine LinearMap.ext fun t => ?_
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K A B Y X) t
  induction s with
  | zero => simp
  | tmul y x => exact H x y
  | add s t hs ht =>
      have hmk : Submodule.Quotient.mk (p := balancedRel K A B Y X) (s + t)
          = Submodule.Quotient.mk s + Submodule.Quotient.mk t := rfl
      rw [hmk, map_add, map_add, hs, ht]

/-- Two additive statements about all of `X ⊗_A Y`, checked on generators. -/
theorem Balanced.ext_forall {W : Type u} [AddCommGroup W]
    {g h : Balanced K A B Y X →+ W}
    (H : ∀ (x : X) (y : Y), g (Balanced.mk x y) = h (Balanced.mk x y)) : g = h := by
  refine AddMonoidHom.ext fun t => ?_
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K A B Y X) t
  induction s with
  | zero => simp
  | tmul y x => exact H x y
  | add s t hs ht =>
      have hmk : Submodule.Quotient.mk (p := balancedRel K A B Y X) (s + t)
          = Submodule.Quotient.mk s + Submodule.Quotient.mk t := rfl
      rw [hmk, map_add, map_add, hs, ht]


/-- The ambient `K`-action of any `Cᵐᵒᵖ`-module with the tower is the induced one. -/
theorem smul_K_of_tower {C' : Type u} [Ring C'] [Algebra K C'] {M : Type u} [AddCommGroup M]
    [Module K M] [Module C'ᵐᵒᵖ M] [IsScalarTower K C'ᵐᵒᵖ M] (c : K) (m : M) :
    c • m = (algebraMap K C'ᵐᵒᵖ) c • m := by
  have h : (c • (1 : C'ᵐᵒᵖ)) • m = c • ((1 : C'ᵐᵒᵖ) • m) := smul_assoc c 1 m
  rw [one_smul, Algebra.smul_def, mul_one] at h
  exact h.symm

/-- The ambient `K`-scalar crosses a pure tensor: `mk (c • x) y = mk x (c • y)`.  Instance-light
on purpose — stated with its own binders, so no `Module A Y` from an enclosing section leaks into
its instance arguments and leaves `A` a metavariable at rewrite sites. -/
theorem Balanced.mk_smul_K_cross {A' B' Y' X' : Type u} [Ring A'] [Algebra K A'] [Ring B']
    [AddCommGroup Y'] [Module K Y'] [Module A' Y'] [Module B'ᵐᵒᵖ Y'] [SMulCommClass K B'ᵐᵒᵖ Y']
    [AddCommGroup X'] [Module K X'] [Module A'ᵐᵒᵖ X'] (c : K) (x : X') (y : Y') :
    Balanced.mk (K := K) (A := A') (B := B') (c • x) y = Balanced.mk x (c • y) := by
  show Submodule.Quotient.mk (M := Y' ⊗[K] X') (y ⊗ₜ[K] (c • x))
      = Submodule.Quotient.mk ((c • y) ⊗ₜ[K] x)
  rw [TensorProduct.smul_tmul]

/-- `x ⊗ 0 = 0`, instance-light (the `Bridge` section's version assumes `CommRing A`). -/
theorem Balanced.mk_zero_right' {A' B' Y' X' : Type u} [Ring A'] [Algebra K A'] [Ring B']
    [AddCommGroup Y'] [Module K Y'] [Module A' Y'] [Module B'ᵐᵒᵖ Y'] [SMulCommClass K B'ᵐᵒᵖ Y']
    [AddCommGroup X'] [Module K X'] [Module A'ᵐᵒᵖ X'] (x : X') :
    Balanced.mk (K := K) (A := A') (B := B') x (0 : Y') = 0 := by
  show Submodule.Quotient.mk (M := Y' ⊗[K] X') ((0 : Y') ⊗ₜ[K] x) = 0
  rw [TensorProduct.zero_tmul]; rfl

/-- `0 ⊗ y = 0`, instance-light. -/
theorem Balanced.mk_zero_left' {A' B' Y' X' : Type u} [Ring A'] [Algebra K A'] [Ring B']
    [AddCommGroup Y'] [Module K Y'] [Module A' Y'] [Module B'ᵐᵒᵖ Y'] [SMulCommClass K B'ᵐᵒᵖ Y']
    [AddCommGroup X'] [Module K X'] [Module A'ᵐᵒᵖ X'] (y : Y') :
    Balanced.mk (K := K) (A := A') (B := B') (0 : X') y = 0 := by
  show Submodule.Quotient.mk (M := Y' ⊗[K] X') (y ⊗ₜ[K] (0 : X')) = 0
  rw [TensorProduct.tmul_zero]; rfl

/-- `Submodule.Quotient.mk (y ⊗ₜ x)` IS `Balanced.mk x y` — the named `rfl` that lets quotient
inductions be finished by rewriting (`DESIGN-NOTES` §62.20). -/
theorem Balanced.quot_mk (x : X) (y : Y) :
    (Submodule.Quotient.mk (y ⊗ₜ[K] x) : Balanced K A B Y X) = Balanced.mk x y := rfl

variable (K A B C Y Z X)

/-- `x ⊗ y ↦ x ⊗ (y ⊗ z)`, for a fixed `z`; the inner factor of `Balanced.assoc`.
`K`-linear only, which is why `Balanced.liftK` is needed. -/
noncomputable def assocInner (z : Z) :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    letI := Balanced.towerLeftOfY K A B C Y Z
    letI := Balanced.smulCommLeftOfY K A B C Y Z
    Balanced K A B Y X →ₗ[K] Balanced K A C (Balanced K B C Z Y) X := by
  letI := Balanced.moduleLeftOfY K A B C Y Z
  letI := Balanced.towerLeftOfY K A B C Y Z
  letI := Balanced.smulCommLeftOfY K A B C Y Z
  refine Balanced.liftK (A := A) (B := B)
    ({ toFun := fun y =>
        { toFun := fun x => Balanced.mk (K := K) (A := A) (B := C) x (Balanced.mk y z)
          map_add' := fun x x' => Balanced.mk_add_left _ _ _
          map_smul' := fun c x => by
            show Balanced.mk (K := K) (A := A) (B := C) (c • x) _
                = (RingHom.id K) c • Balanced.mk (K := K) (A := A) (B := C) x _
            rw [RingHom.id_apply, Balanced.mk_smul_K_left, Balanced.smul_K_mk] }
       map_add' := fun y y' => by
         refine LinearMap.ext fun x => ?_
         show Balanced.mk (K := K) (A := A) (B := C) x (Balanced.mk (y + y') z) = _
         rw [Balanced.mk_add_left, Balanced.mk_add_right]
         rfl
       map_smul' := fun c y => by
         refine LinearMap.ext fun x => ?_
         show Balanced.mk (K := K) (A := A) (B := C) x (Balanced.mk (c • y) z) = _
         rw [Balanced.mk_smul_K_left, ← Balanced.smul_mk, ← Balanced.smul_K_mk]
         rfl }) ?_
  intro a y x
  show Balanced.mk (K := K) (A := A) (B := C) x (Balanced.mk (a • y) z)
      = Balanced.mk (MulOpposite.op a • x) (Balanced.mk y z)
  rw [Balanced.mk_smul]
  rfl

/-- Value guard from birth for `assocInner`, `rfl`. -/
theorem assocInner_mk (z : Z) (x : X) (y : Y) :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    letI := Balanced.towerLeftOfY K A B C Y Z
    letI := Balanced.smulCommLeftOfY K A B C Y Z
    assocInner K A B C Y Z X z (Balanced.mk x y)
      = Balanced.mk (K := K) (A := A) (B := C) x (Balanced.mk y z) := rfl


/-- `assocInner` as a `K`-bilinear map in `z`; named, with a `rfl` value lemma, so that
`Balanced.lift`'s obligations are discharged by REWRITING rather than by unification through the
three reducible instance `letI`s (`DESIGN-NOTES` §62.20 — stating them with `show` instead costs a
`whnf` heartbeat blow-up, measured). -/
noncomputable def assocBil :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    letI := Balanced.towerLeftOfY K A B C Y Z
    letI := Balanced.smulCommLeftOfY K A B C Y Z
    Z →ₗ[K] (Balanced K A B Y X →ₗ[K] Balanced K A C (Balanced K B C Z Y) X) := by
  letI := Balanced.moduleLeftOfY K A B C Y Z
  letI := Balanced.towerLeftOfY K A B C Y Z
  letI := Balanced.smulCommLeftOfY K A B C Y Z
  refine
    { toFun := fun z => assocInner K A B C Y Z X z
      map_add' := fun z z' => Balanced.hom_extK fun x y => ?_
      map_smul' := fun c z => Balanced.hom_extK fun x y => ?_ }
  · rw [assocInner_mk, LinearMap.add_apply, assocInner_mk, assocInner_mk,
      Balanced.mk_add_right, Balanced.mk_add_right]
  · rw [assocInner_mk, LinearMap.smul_apply, RingHom.id_apply, assocInner_mk,
      smul_K_of_tower (C' := C) c (Balanced.mk (K := K) (A := A) (B := C) x (Balanced.mk y z)),
      Balanced.smul_mk, Balanced.smul_mk, smul_K_of_tower (C' := C) c z]

/-- Value guard for `assocBil`, `rfl`. -/
theorem assocBil_mk (z : Z) (x : X) (y : Y) :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    letI := Balanced.towerLeftOfY K A B C Y Z
    letI := Balanced.smulCommLeftOfY K A B C Y Z
    assocBil K A B C Y Z X z (Balanced.mk x y)
      = Balanced.mk (K := K) (A := A) (B := C) x (Balanced.mk y z) := rfl


/-- **The forward map of `Balanced.assoc`**: `(x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z)`. -/
noncomputable def assocFwd :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    letI := Balanced.towerLeftOfY K A B C Y Z
    letI := Balanced.smulCommLeftOfY K A B C Y Z
    Balanced K B C Z (Balanced K A B Y X) →ₗ[Cᵐᵒᵖ] Balanced K A C (Balanced K B C Z Y) X := by
  letI := Balanced.moduleLeftOfY K A B C Y Z
  letI := Balanced.towerLeftOfY K A B C Y Z
  letI := Balanced.smulCommLeftOfY K A B C Y Z
  refine Balanced.lift (A := B) (B := C) (assocBil K A B C Y Z X) ?_ ?_
  · intro b z t
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K A B Y X) t
    induction s with
    | zero => simp
    | tmul y x => rw [Balanced.quot_mk, assocBil_mk, Balanced.smul_mk, assocBil_mk,
          Balanced.mk_smul]
    | add s s' hs hs' =>
        have hmk : Submodule.Quotient.mk (p := balancedRel K A B Y X) (s + s')
            = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
        rw [hmk, map_add, hs, hs', smul_add, map_add]
  · intro c z t
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K A B Y X) t
    induction s with
    | zero => simp
    | tmul y x => rw [Balanced.quot_mk, assocBil_mk, assocBil_mk, Balanced.smul_mk,
          Balanced.smul_mk]
    | add s s' hs hs' =>
        have hmk : Submodule.Quotient.mk (p := balancedRel K A B Y X) (s + s')
            = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
        rw [hmk, map_add, hs, hs', map_add, smul_add]

/-- Value guard for `assocFwd`, `rfl`. -/
@[simp] theorem assocFwd_mk (x : X) (y : Y) (z : Z) :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    letI := Balanced.towerLeftOfY K A B C Y Z
    letI := Balanced.smulCommLeftOfY K A B C Y Z
    assocFwd K A B C Y Z X (Balanced.mk (Balanced.mk x y) z)
      = Balanced.mk (K := K) (A := A) (B := C) x (Balanced.mk y z) := rfl


/-- `y ⊗ z ↦ (x ⊗ y) ⊗ z` for a fixed `x`; the inner factor of the backward map. -/
noncomputable def assocBackInner (x : X) :
    Balanced K B C Z Y →ₗ[Cᵐᵒᵖ] Balanced K B C Z (Balanced K A B Y X) := by
  refine Balanced.lift (A := B) (B := C)
    ({ toFun := fun z =>
        { toFun := fun y => Balanced.mk (K := K) (A := B) (B := C) (Balanced.mk x y) z
          map_add' := fun y y' => by
            rw [Balanced.mk_add_right, Balanced.mk_add_left]
          map_smul' := fun c y => by
            rw [RingHom.id_apply]
            have h1 : Balanced.mk (K := K) (A := A) (B := B) x (c • y)
                = c • Balanced.mk (K := K) (A := A) (B := B) x y := by
              rw [Balanced.smul_K_mk, smul_K_of_tower (C' := B) c y]
            rw [h1, Balanced.mk_smul_K_left, ← Balanced.smul_K_mk] }
       map_add' := fun z z' => by
         refine LinearMap.ext fun y => ?_
         simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
         rw [Balanced.mk_add_right]
       map_smul' := fun c z => by
         refine LinearMap.ext fun y => ?_
         simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
         rw [Balanced.smul_K_mk, smul_K_of_tower (C' := C) c z] }) ?_ ?_
  · intro b z y
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Balanced.smul_mk, Balanced.mk_smul]
  · intro c z y
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Balanced.smul_mk]


/-- Value guard for `assocBackInner`, `rfl`. -/
theorem assocBackInner_mk (x : X) (y : Y) (z : Z) :
    assocBackInner K A B C Y Z X x (Balanced.mk y z)
      = Balanced.mk (K := K) (A := B) (B := C) (Balanced.mk x y) z := rfl

/-- `assocBackInner`, `K`-linear in `x`. -/
noncomputable def assocBackBilX :
    X →ₗ[K] (Balanced K B C Z Y →ₗ[K] Balanced K B C Z (Balanced K A B Y X)) where
  toFun x := (assocBackInner K A B C Y Z X x).restrictScalars K
  map_add' x x' := by
    refine Balanced.hom_extK fun y z => ?_
    show assocBackInner K A B C Y Z X (x + x') (Balanced.mk y z) = _
    rw [assocBackInner_mk, LinearMap.add_apply]
    show _ = assocBackInner K A B C Y Z X x (Balanced.mk y z)
        + assocBackInner K A B C Y Z X x' (Balanced.mk y z)
    rw [assocBackInner_mk, assocBackInner_mk, Balanced.mk_add_left, Balanced.mk_add_left]
  map_smul' c x := by
    refine Balanced.hom_extK fun y z => ?_
    show assocBackInner K A B C Y Z X (c • x) (Balanced.mk y z) = _
    rw [assocBackInner_mk, RingHom.id_apply, LinearMap.smul_apply]
    show _ = c • assocBackInner K A B C Y Z X x (Balanced.mk y z)
    rw [assocBackInner_mk,
      Balanced.mk_smul_K_cross (A' := A) (B' := B) c x y,
      smul_K_of_tower (C' := B) c y, ← Balanced.smul_K_mk,
      Balanced.mk_smul_K_cross (A' := B) (B' := C) c (Balanced.mk x y) z,
      smul_K_of_tower (C' := C) c z, ← Balanced.smul_K_mk]


/-- **The backward map of `Balanced.assoc`**: `x ⊗ (y ⊗ z) ↦ (x ⊗ y) ⊗ z`. -/
noncomputable def assocBack :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    letI := Balanced.towerLeftOfY K A B C Y Z
    letI := Balanced.smulCommLeftOfY K A B C Y Z
    Balanced K A C (Balanced K B C Z Y) X →ₗ[Cᵐᵒᵖ] Balanced K B C Z (Balanced K A B Y X) := by
  letI := Balanced.moduleLeftOfY K A B C Y Z
  letI := Balanced.towerLeftOfY K A B C Y Z
  letI := Balanced.smulCommLeftOfY K A B C Y Z
  refine Balanced.lift (A := A) (B := C) (assocBackBilX K A B C Y Z X).flip ?_ ?_
  · intro a w x
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K B C Z Y) w
    induction s with
    | zero => simp
    | tmul z y =>
        show assocBackInner K A B C Y Z X x (a • Balanced.mk y z)
            = assocBackInner K A B C Y Z X (MulOpposite.op a • x) (Balanced.mk y z)
        rw [Balanced.moduleLeftOfY_mk, assocBackInner_mk, assocBackInner_mk, Balanced.mk_smul]
    | add s s' hs hs' =>
        have hmk : Submodule.Quotient.mk (p := balancedRel K B C Z Y) (s + s')
            = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
        simp only [LinearMap.flip_apply] at hs hs' ⊢
        rw [hmk, smul_add, map_add, map_add, hs, hs']
  · intro c w x
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K B C Z Y) w
    induction s with
    | zero => simp
    | tmul z y =>
        show assocBackInner K A B C Y Z X x (c • Balanced.mk y z)
            = c • assocBackInner K A B C Y Z X x (Balanced.mk y z)
        rw [Balanced.smul_mk, assocBackInner_mk, assocBackInner_mk, Balanced.smul_mk]
    | add s s' hs hs' =>
        have hmk : Submodule.Quotient.mk (p := balancedRel K B C Z Y) (s + s')
            = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
        simp only [LinearMap.flip_apply] at hs hs' ⊢
        rw [hmk, smul_add, map_add, map_add, hs, hs', smul_add]


/-- Value guard for `assocBack`, `rfl`. -/
@[simp] theorem assocBack_mk (x : X) (w : Balanced K B C Z Y) :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    letI := Balanced.towerLeftOfY K A B C Y Z
    letI := Balanced.smulCommLeftOfY K A B C Y Z
    assocBack K A B C Y Z X (Balanced.mk (K := K) (A := A) (B := C) x w)
      = assocBackInner K A B C Y Z X x w := rfl

/-- **`Balanced.assoc` — the monoidality step**: `(X ⊗_A Y) ⊗_B Z ≅ X ⊗_A (Y ⊗_B Z)`, the
heterobasic associativity mathlib does not have (finding **S5-F10**, `DESIGN-NOTES` §67). -/
noncomputable def Balanced.assoc :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    letI := Balanced.towerLeftOfY K A B C Y Z
    letI := Balanced.smulCommLeftOfY K A B C Y Z
    Balanced K B C Z (Balanced K A B Y X) ≃ₗ[Cᵐᵒᵖ] Balanced K A C (Balanced K B C Z Y) X := by
  letI := Balanced.moduleLeftOfY K A B C Y Z
  letI := Balanced.towerLeftOfY K A B C Y Z
  letI := Balanced.smulCommLeftOfY K A B C Y Z
  refine LinearEquiv.ofLinear (assocFwd K A B C Y Z X) (assocBack K A B C Y Z X) ?_ ?_
  · refine Balanced.hom_ext fun x w => ?_
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K B C Z Y) w
    induction s with
    | zero =>
        have h0 : (Submodule.Quotient.mk (0 : Z ⊗[K] Y) : Balanced K B C Z Y) = 0 := rfl
        simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
        rw [h0, Balanced.mk_zero_right' (A' := A) (B' := C), map_zero, map_zero]
    | tmul z y =>
        show assocFwd K A B C Y Z X (assocBack K A B C Y Z X
            (Balanced.mk (K := K) (A := A) (B := C) x (Balanced.mk y z))) = _
        rw [assocBack_mk, assocBackInner_mk, assocFwd_mk]
        rfl
    | add s s' hs hs' =>
        have hmk : Submodule.Quotient.mk (p := balancedRel K B C Z Y) (s + s')
            = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
        simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq] at hs hs' ⊢
        rw [hmk, Balanced.mk_add_right, map_add, map_add, hs, hs', ← Balanced.mk_add_right]
  · refine Balanced.hom_ext fun w z => ?_
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K A B Y X) w
    induction s with
    | zero =>
        have h0 : (Submodule.Quotient.mk (0 : Y ⊗[K] X) : Balanced K A B Y X) = 0 := rfl
        simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
        rw [h0, Balanced.mk_zero_left' (A' := B) (B' := C), map_zero, map_zero]
    | tmul y x =>
        show assocBack K A B C Y Z X (assocFwd K A B C Y Z X
            (Balanced.mk (K := K) (A := B) (B := C) (Balanced.mk x y) z)) = _
        rw [assocFwd_mk, assocBack_mk, assocBackInner_mk]
        rfl
    | add s s' hs hs' =>
        have hmk : Submodule.Quotient.mk (p := balancedRel K A B Y X) (s + s')
            = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
        simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq] at hs hs' ⊢
        rw [hmk, Balanced.mk_add_left, map_add, map_add, hs, hs', ← Balanced.mk_add_left]

/-- **Value guard for `Balanced.assoc`, from birth** — its action on a generator, `rfl`. -/
@[simp] theorem Balanced.assoc_mk (x : X) (y : Y) (z : Z) :
    letI := Balanced.moduleLeftOfY K A B C Y Z
    letI := Balanced.towerLeftOfY K A B C Y Z
    letI := Balanced.smulCommLeftOfY K A B C Y Z
    Balanced.assoc K A B C Y Z X (Balanced.mk (Balanced.mk x y) z)
      = Balanced.mk (K := K) (A := A) (B := C) x (Balanced.mk y z) := rfl

end Assoc


/-! ### **`Balanced.baseFieldEquiv` — base-field invariance** (finding **S5-F10**, `§67.7`)

`Balanced K A B Y X ≅ Balanced N A B Y X` for a central tower `K → N → A`.

`RQ2-2.18-C3` needs it because **its two sides are built over different base fields**: the
base-changed side `Rep.tensor (S.baseChange N) k ℓ` is a `Balanced` over `N`, while
`repTensorBaseChangeAt` is one over `K`.  That is not an accident of the rendering — it is what the
row is about, `W'_k` living over an object of `S ⊗_K N` and `W_i` over `K`.

It is true for the same reason `Balanced` is balanced at all: the `A`-balancing generators already
contain `(n·y) ⊗ x − y ⊗ (x·n)` for every `n` in the image of `N` in `A`, and that is exactly the
relation collapsing `Y ⊗[K] X` onto `Y ⊗[N] X`.  So the two quotients coincide — and both inverse
laws come out `rfl` on generators, which is the sharpest possible statement of that.

**The standing assumptions are the point.**  `SMulCommClass N K Y` is what makes mathlib supply
`Module K (Balanced N A B Y X)` and `IsScalarTower K Bᵐᵒᵖ (Balanced N A B Y X)` — the two instances
`Balanced.lift`'s target requires.  Without it in scope both are reported absent, and that report is
an artefact of the probe's context, not a fact about the pin (`DESIGN-NOTES` §67.7's dated
correction; `CONVENTIONS.md` §6: *absence of an instance is not absence of the fact*).
-/

section BaseField


variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N]
variable {A : Type u} [Ring A] [Algebra K A] [Algebra N A] [IsScalarTower K N A]
variable {B : Type u} [Ring B] [Algebra K B] [Algebra N B] [IsScalarTower K N B]
variable {Y : Type u} [AddCommGroup Y] [Module K Y] [Module N Y] [Module A Y] [Module Bᵐᵒᵖ Y]
  [SMulCommClass K Bᵐᵒᵖ Y] [SMulCommClass N Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y]
  [IsScalarTower K A Y] [IsScalarTower N A Y] [IsScalarTower K Bᵐᵒᵖ Y] [IsScalarTower N Bᵐᵒᵖ Y]
  [IsScalarTower K N Y] [SMulCommClass K N Y] [SMulCommClass N K Y]
variable {X : Type u} [AddCommGroup X] [Module K X] [Module N X] [Module Aᵐᵒᵖ X]
  [IsScalarTower K Aᵐᵒᵖ X] [IsScalarTower N Aᵐᵒᵖ X] [IsScalarTower K N X]

variable (K N A B Y X)

/-- `x ⊗ y` over `K` maps to `x ⊗ y` over `N`. -/
noncomputable def baseFieldFwd : Balanced K A B Y X →ₗ[Bᵐᵒᵖ] Balanced N A B Y X := by
  refine Balanced.lift (A := A) (B := B)
    ({ toFun := fun y =>
        { toFun := fun x => Balanced.mk (K := N) (A := A) (B := B) x y
          map_add' := fun x x' => Balanced.mk_add_left _ _ _
          map_smul' := fun c x => by
            rw [RingHom.id_apply, smul_K_of_tower (C' := A) c x,
              smul_K_of_tower (C' := B) c (Balanced.mk (K := N) (A := A) (B := B) x y),
              Balanced.smul_mk,
              show (algebraMap K Aᵐᵒᵖ) c = MulOpposite.op ((algebraMap K A) c) from rfl,
              Balanced.mk_smul]
            congr 1
            rw [IsScalarTower.algebraMap_smul, ← smul_K_of_tower (C' := B) c y] }
       map_add' := fun y y' => by ext x; exact Balanced.mk_add_right _ _ _
       map_smul' := fun c y => by
         ext x
         simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
         rw [smul_K_of_tower (C' := B) c y,
           smul_K_of_tower (C' := B) c (Balanced.mk (K := N) (A := A) (B := B) x y),
           Balanced.smul_mk] })
    (fun a y x => (Balanced.mk_smul a x y).symm)
    (fun b y x => (Balanced.smul_mk b x y).symm)

/-- ...and back: `x ⊗ y` over `N` maps to `x ⊗ y` over `K`. -/
noncomputable def baseFieldBack : Balanced N A B Y X →ₗ[Bᵐᵒᵖ] Balanced K A B Y X := by
  refine Balanced.lift (A := A) (B := B)
    ({ toFun := fun y =>
        { toFun := fun x => Balanced.mk (K := K) (A := A) (B := B) x y
          map_add' := fun x x' => Balanced.mk_add_left _ _ _
          map_smul' := fun (c : N) x => by
            rw [RingHom.id_apply, smul_K_of_tower (C' := A) c x,
              smul_K_of_tower (C' := B) c (Balanced.mk (K := K) (A := A) (B := B) x y),
              Balanced.smul_mk,
              show (algebraMap N Aᵐᵒᵖ) c = MulOpposite.op ((algebraMap N A) c) from rfl,
              Balanced.mk_smul]
            congr 1
            rw [IsScalarTower.algebraMap_smul, ← smul_K_of_tower (C' := B) c y] }
       map_add' := fun y y' => by ext x; exact Balanced.mk_add_right _ _ _
       map_smul' := fun (c : N) y => by
         ext x
         simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
         rw [smul_K_of_tower (C' := B) c y,
           smul_K_of_tower (C' := B) c (Balanced.mk (K := K) (A := A) (B := B) x y),
           Balanced.smul_mk] })
    (fun a y x => (Balanced.mk_smul a x y).symm)
    (fun b y x => (Balanced.smul_mk b x y).symm)


/-- Value guards from birth, both `rfl`. -/
@[simp] theorem baseFieldFwd_mk (x : X) (y : Y) :
    baseFieldFwd K N A B Y X (Balanced.mk x y) = Balanced.mk (K := N) (A := A) (B := B) x y := rfl

@[simp] theorem baseFieldBack_mk (x : X) (y : Y) :
    baseFieldBack K N A B Y X (Balanced.mk x y) = Balanced.mk (K := K) (A := A) (B := B) x y := rfl

/-- **B6 — base-field invariance of `Balanced`.**  For a central tower `K → N → A` the balanced
product does not depend on which subfield it is built over: the `A`-balancing generators already
contain the relation that collapses `⊗[K]` onto `⊗[N]`. -/
noncomputable def Balanced.baseFieldEquiv :
    Balanced K A B Y X ≃ₗ[Bᵐᵒᵖ] Balanced N A B Y X := by
  refine LinearEquiv.ofLinear (baseFieldFwd K N A B Y X) (baseFieldBack K N A B Y X) ?_ ?_
  · exact Balanced.hom_ext fun x y => rfl
  · exact Balanced.hom_ext fun x y => rfl

/-- **Value guard for B6, from birth** — `rfl` on a generator. -/
@[simp] theorem Balanced.baseFieldEquiv_mk (x : X) (y : Y) :
    Balanced.baseFieldEquiv K N A B Y X (Balanced.mk x y)
      = Balanced.mk (K := N) (A := A) (B := B) x y := rfl

end BaseField


/-! ### Functoriality in the bimodule variable, the unit law, and finite products

The remaining general lemmas `RQ2-2.18-C3`'s fibre-summed identification needs, alongside
`Balanced.assoc` and `Balanced.baseFieldEquiv` (`DESIGN-NOTES` §67):

* **`Balanced.mapY` / `.congrY`** — `Balanced.map` varies the right-module slot `X`; nothing varied
  the **bimodule** slot `Y`, and the fibre-summed clause must, because the identification replaces
  one bimodule (`∏_a {}_{⟨i,a⟩}M'_ℓ`) by another (`{}_iM_j ⊗_{L_j} L'_ℓ`).
* **`Balanced.unitX`** — `A ⊗_A Y ≅ Y`, the algebra in the right-module slot.  With
  `Balanced.assoc` this is what cancels the `L'_k` the chain's first step leaves behind.
* **`piYFwd`** — a finite product of bimodules passes through the balanced product.  This is where
  the **fibre sum** of the repaired `C3` happens.

All species-free; they join the `MD-S5-01` upstream-candidate family (ledger `MD-S5-09`).
-/

section MapY


variable {K : Type u} [Field K]
variable {A : Type u} [Ring A] [Algebra K A]
variable {B : Type u} [Ring B] [Algebra K B]
variable {Y Y' : Type u} [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y]
  [SMulCommClass K Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y] [IsScalarTower K A Y] [IsScalarTower K Bᵐᵒᵖ Y]
variable [AddCommGroup Y'] [Module K Y'] [Module A Y'] [Module Bᵐᵒᵖ Y']
  [SMulCommClass K Bᵐᵒᵖ Y'] [SMulCommClass A Bᵐᵒᵖ Y'] [IsScalarTower K A Y']
  [IsScalarTower K Bᵐᵒᵖ Y']
variable {X : Type u} [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X]

variable (K A B X)

/-- **B2 — functoriality in the bimodule variable.**  An `(A,B)`-bimodule map `Y → Y'` induces
`X ⊗_A Y → X ⊗_A Y'`. -/
noncomputable def Balanced.mapY (φ : Y →ₗ[Bᵐᵒᵖ] Y')
    (hA : ∀ (a : A) (y : Y), φ (a • y) = a • φ y)
    (hK : ∀ (c : K) (y : Y), φ (c • y) = c • φ y) :
    Balanced K A B Y X →ₗ[Bᵐᵒᵖ] Balanced K A B Y' X :=
  Balanced.lift (A := A) (B := B)
    ({ toFun := fun y =>
        { toFun := fun x => Balanced.mk (K := K) (A := A) (B := B) x (φ y)
          map_add' := fun x x' => Balanced.mk_add_left _ _ _
          map_smul' := fun c x => by
            rw [RingHom.id_apply, Balanced.mk_smul_K_cross,
              smul_K_of_tower (C' := B) c (φ y), ← Balanced.smul_K_mk] }
       map_add' := fun y y' => by ext x; rw [map_add]; exact Balanced.mk_add_right _ _ _
       map_smul' := fun c y => by
         ext x
         simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
         rw [hK, smul_K_of_tower (C' := B) c (φ y), ← Balanced.smul_K_mk] })
    (fun a y x => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [hA, ← Balanced.mk_smul])
    (fun b y x => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [map_smul, ← Balanced.smul_mk])

@[simp] theorem Balanced.mapY_mk (φ : Y →ₗ[Bᵐᵒᵖ] Y')
    (hA : ∀ (a : A) (y : Y), φ (a • y) = a • φ y)
    (hK : ∀ (c : K) (y : Y), φ (c • y) = c • φ y) (x : X) (y : Y) :
    Balanced.mapY (K := K) (A := A) (B := B) (X := X) φ hA hK (Balanced.mk x y)
      = Balanced.mk (K := K) (A := A) (B := B) x (φ y) := rfl


/-- **B2, equivalence form** — a bimodule isomorphism `Y ≅ Y'` gives `X ⊗_A Y ≅ X ⊗_A Y'`. -/
noncomputable def Balanced.congrY (φ : Y ≃ₗ[Bᵐᵒᵖ] Y')
    (hA : ∀ (a : A) (y : Y), φ (a • y) = a • φ y)
    (hK : ∀ (c : K) (y : Y), φ (c • y) = c • φ y)
    (hA' : ∀ (a : A) (y : Y'), φ.symm (a • y) = a • φ.symm y)
    (hK' : ∀ (c : K) (y : Y'), φ.symm (c • y) = c • φ.symm y) :
    Balanced K A B Y X ≃ₗ[Bᵐᵒᵖ] Balanced K A B Y' X := by
  refine LinearEquiv.ofLinear
    (Balanced.mapY (K := K) (A := A) (B := B) (X := X) (φ : Y →ₗ[Bᵐᵒᵖ] Y') hA hK)
    (Balanced.mapY (K := K) (A := A) (B := B) (X := X) (φ.symm : Y' →ₗ[Bᵐᵒᵖ] Y) hA' hK') ?_ ?_
  · refine Balanced.hom_ext fun x y => ?_
    show Balanced.mapY (K := K) (A := A) (B := B) (X := X) _ hA hK (Balanced.mapY (K := K) (A := A) (B := B) (X := X) _ hA' hK' (Balanced.mk x y)) = _
    rw [Balanced.mapY_mk, Balanced.mapY_mk]
    simp
  · refine Balanced.hom_ext fun x y => ?_
    show Balanced.mapY (K := K) (A := A) (B := B) (X := X) _ hA' hK' (Balanced.mapY (K := K) (A := A) (B := B) (X := X) _ hA hK (Balanced.mk x y)) = _
    rw [Balanced.mapY_mk, Balanced.mapY_mk]
    simp

/-- **B5 — the unit law**: `A ⊗_A Y ≅ Y`, the algebra in the right-module slot. -/
noncomputable def Balanced.unitX : Balanced K A B Y A ≃ₗ[Bᵐᵒᵖ] Y := by
  refine LinearEquiv.ofLinear
    (Balanced.lift (A := A) (B := B)
      ({ toFun := fun y =>
          { toFun := fun a => a • y
            map_add' := fun a a' => add_smul a a' y
            map_smul' := fun c a => by rw [RingHom.id_apply, smul_assoc] }
         map_add' := fun y y' => by ext a; exact smul_add a y y'
         map_smul' := fun c y => by
           ext a
           simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk]
           rw [smul_comm] })
      (fun a y x => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        show x • (a • y) = (MulOpposite.op a • x) • y
        rw [← smul_assoc]
        rfl)
      (fun b y x => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        exact smul_comm x b y))
    ({ toFun := fun y => Balanced.mk (K := K) (A := A) (B := B) (1 : A) y
       map_add' := fun y y' => Balanced.mk_add_right _ _ _
       map_smul' := fun b y => by rw [RingHom.id_apply, Balanced.smul_mk] }) ?_ ?_
  · refine LinearMap.ext fun y => ?_
    show (1 : A) • y = y
    rw [one_smul]
  · refine Balanced.hom_ext fun a y => ?_
    show Balanced.mk (K := K) (A := A) (B := B) (1 : A) (a • y) = _
    rw [← Balanced.mk_smul]
    show Balanced.mk (MulOpposite.op a • (1 : A)) y = _
    rw [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, one_mul]
    rfl

end MapY

section PiY


variable {K : Type u} [Field K]
variable {A : Type u} [Ring A] [Algebra K A]
variable {B : Type u} [Ring B] [Algebra K B]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {Y : ι → Type u} [∀ a, AddCommGroup (Y a)] [∀ a, Module K (Y a)] [∀ a, Module A (Y a)]
  [∀ a, Module Bᵐᵒᵖ (Y a)] [∀ a, SMulCommClass K Bᵐᵒᵖ (Y a)] [∀ a, SMulCommClass A Bᵐᵒᵖ (Y a)]
  [∀ a, IsScalarTower K A (Y a)] [∀ a, IsScalarTower K Bᵐᵒᵖ (Y a)]
variable {X : Type u} [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X]

/-- **B3, forward**: `X ⊗_A (∏_a Y a) → ∏_a (X ⊗_A Y a)`. -/
noncomputable def piYFwd :
    Balanced K A B (∀ a, Y a) X →ₗ[Bᵐᵒᵖ] (∀ a, Balanced K A B (Y a) X) :=
  Balanced.lift (A := A) (B := B)
    ({ toFun := fun y =>
        { toFun := fun x a => Balanced.mk (K := K) (A := A) (B := B) x (y a)
          map_add' := fun x x' => by funext a; exact Balanced.mk_add_left _ _ _
          map_smul' := fun c x => by
            funext a
            simp only [RingHom.id_apply, Pi.smul_apply]
            rw [Balanced.mk_smul_K_cross, smul_K_of_tower (C' := B) c (y a),
              ← Balanced.smul_K_mk] }
       map_add' := fun y y' => by
         ext x a
         simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply]
         exact Balanced.mk_add_right _ _ _
       map_smul' := fun c y => by
         ext x a
         simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk,
           Pi.smul_apply]
         rw [smul_K_of_tower (C' := B) c (y a), ← Balanced.smul_K_mk] })
    (fun α y x => by
      funext a
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply]
      rw [← Balanced.mk_smul])
    (fun b y x => by
      funext a
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply]
      rw [← Balanced.smul_mk])

@[simp] theorem piYFwd_mk (x : X) (y : ∀ a, Y a) (a : ι) :
    piYFwd (K := K) (A := A) (B := B) (Y := Y) (X := X) (Balanced.mk x y) a
      = Balanced.mk (K := K) (A := A) (B := B) x (y a) := rfl


theorem single_smul_A (a : ι) (α : A) (y : Y a) :
    (LinearMap.single Bᵐᵒᵖ Y a) (α • y) = α • (LinearMap.single Bᵐᵒᵖ Y a) y := by
  funext b
  by_cases h : a = b
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem single_smul_K (a : ι) (c : K) (y : Y a) :
    (LinearMap.single Bᵐᵒᵖ Y a) (c • y) = c • (LinearMap.single Bᵐᵒᵖ Y a) y := by
  funext b
  by_cases h : a = b
  · subst h; simp
  · simp [Pi.single_apply, h]

/-- `x ⊗ −` as an additive map, so that it commutes with finite sums. -/
def Balanced.mkRightHom (x : X) {Y' : Type u} [AddCommGroup Y'] [Module K Y'] [Module A Y']
    [Module Bᵐᵒᵖ Y'] [SMulCommClass K Bᵐᵒᵖ Y'] [SMulCommClass A Bᵐᵒᵖ Y']
    [IsScalarTower K A Y'] [IsScalarTower K Bᵐᵒᵖ Y'] : Y' →+ Balanced K A B Y' X where
  toFun y := Balanced.mk (K := K) (A := A) (B := B) x y
  map_zero' := Balanced.mk_zero_right' (A' := A) (B' := B) x
  map_add' y y' := Balanced.mk_add_right _ _ _

/-- **B3, backward**: the sum of the summand inclusions. -/
noncomputable def piYBack :
    (∀ a, Balanced K A B (Y a) X) →ₗ[Bᵐᵒᵖ] Balanced K A B (∀ a, Y a) X :=
  ∑ a : ι, (Balanced.mapY (K := K) (A := A) (B := B) (X := X)
      (LinearMap.single Bᵐᵒᵖ Y a) (single_smul_A a) (single_smul_K a)).comp (LinearMap.proj a)


/-- The `a`-th summand lands in the `a`-th component. -/
theorem piYFwd_mapY_single_self (a : ι) (u : Balanced K A B (Y a) X) :
    piYFwd (K := K) (A := A) (B := B) (Y := Y) (X := X)
      (Balanced.mapY (K := K) (A := A) (B := B) (X := X)
        (LinearMap.single Bᵐᵒᵖ Y a) (single_smul_A a) (single_smul_K a) u) a = u := by
  have h : ((LinearMap.proj a).comp
        ((piYFwd (K := K) (A := A) (B := B) (Y := Y) (X := X)).comp
          (Balanced.mapY (K := K) (A := A) (B := B) (X := X)
            (LinearMap.single Bᵐᵒᵖ Y a) (single_smul_A a) (single_smul_K a))))
      = LinearMap.id := by
    refine Balanced.hom_ext fun x y => ?_
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.id_coe, id_eq]
    rw [Balanced.mapY_mk, piYFwd_mk]
    simp
  exact congrArg (fun f => f u) h

/-- …and nowhere else. -/
theorem piYFwd_mapY_single_ne (a b : ι) (hab : a ≠ b) (u : Balanced K A B (Y a) X) :
    piYFwd (K := K) (A := A) (B := B) (Y := Y) (X := X)
      (Balanced.mapY (K := K) (A := A) (B := B) (X := X)
        (LinearMap.single Bᵐᵒᵖ Y a) (single_smul_A a) (single_smul_K a) u) b = 0 := by
  have h : ((LinearMap.proj b).comp
        ((piYFwd (K := K) (A := A) (B := B) (Y := Y) (X := X)).comp
          (Balanced.mapY (K := K) (A := A) (B := B) (X := X)
            (LinearMap.single Bᵐᵒᵖ Y a) (single_smul_A a) (single_smul_K a))))
      = 0 := by
    refine Balanced.hom_ext fun x y => ?_
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.zero_apply]
    rw [Balanced.mapY_mk, piYFwd_mk]
    have hz : (LinearMap.single Bᵐᵒᵖ Y a) y b = 0 := by simp [Pi.single_apply, Ne.symm hab]
    rw [hz]
    exact Balanced.mk_zero_right' (A' := A) (B' := B) x
  exact congrArg (fun f => f u) h


/-- **B3 — a finite product of bimodules passes through the balanced product.**
`X ⊗_A (∏_a Y a) ≅ ∏_a (X ⊗_A Y a)`.  This is where the fibre sum of the repaired `RQ2-2.18-C3`
happens. -/
noncomputable def Balanced.piY :
    Balanced K A B (∀ a, Y a) X ≃ₗ[Bᵐᵒᵖ] (∀ a, Balanced K A B (Y a) X) := by
  refine LinearEquiv.ofLinear (piYFwd (K := K) (A := A) (B := B) (Y := Y) (X := X))
    (piYBack (K := K) (A := A) (B := B) (Y := Y) (X := X)) ?_ ?_
  · refine LinearMap.ext fun t => ?_
    funext b
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq, piYBack, LinearMap.coeFn_sum,
      Finset.sum_apply, map_sum]
    rw [Finset.sum_eq_single b]
    · exact piYFwd_mapY_single_self b (t b)
    · intro a _ hab
      exact piYFwd_mapY_single_ne a b hab (t a)
    · intro hb; exact absurd (Finset.mem_univ b) hb
  · refine Balanced.hom_ext fun x y => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq, piYBack, LinearMap.coeFn_sum,
      Finset.sum_apply]
    have hstep : ∀ a : ι, (Balanced.mapY (K := K) (A := A) (B := B) (X := X)
        (LinearMap.single Bᵐᵒᵖ Y a) (single_smul_A a) (single_smul_K a))
        ((LinearMap.proj (R := Bᵐᵒᵖ) (φ := fun c => Balanced K A B (Y c) X) a)
          (piYFwd (K := K) (A := A) (B := B) (Y := Y) (X := X) (Balanced.mk x y)))
        = Balanced.mkRightHom (K := K) (A := A) (B := B) (X := X) (Y' := ∀ c, Y c) x
            ((LinearMap.single Bᵐᵒᵖ Y a) (y a)) := by
      intro a
      simp only [LinearMap.proj_apply]
      rw [piYFwd_mk, Balanced.mapY_mk]
      rfl
    simp only [hstep]
    rw [← map_sum]
    have hsum : (∑ c : ι, (LinearMap.single Bᵐᵒᵖ Y c) (y c)) = y := by
      simpa using Finset.univ_sum_single y
    rw [hsum]
    rfl

/-- **Value guard for B3, from birth** — `rfl` on a generator. -/
@[simp] theorem Balanced.piY_mk (x : X) (y : ∀ a, Y a) (a : ι) :
    Balanced.piY (K := K) (A := A) (B := B) (Y := Y) (X := X) (Balanced.mk x y) a
      = Balanced.mk (K := K) (A := A) (B := B) x (y a) := rfl

end PiY

/-- **A right module over a commutative ring, read as a left one**, along `A ≃+* Aᵐᵒᵖ`.

`Balanced.equivTensor` needs a `Module A X` alongside `X`'s `Module Aᵐᵒᵖ X`, and for commutative
`A` this is it.  Its `hX` is then `rfl` (`smul_of_opposite`).

**Not an instance, and not even a section-local one — measured.**  As an ambient instance its head
is `Module ?A ?X` with *both* arguments variable, so instance search tries it against essentially
every module goal in scope; at `RQ2-2.20`'s heads that produced a `synthInstance` heartbeat timeout
and a spurious `failed to synthesize Module K L`, which is `CONVENTIONS.md` §3's timeout entry in a
new presentation: not a *wrong* competitor but a **combinatorial** one.  Consumers key it to a
specific carrier — the discipline `Species/Rep/Decomposition.lean`'s `moduleTwistBase_*` instances
already follow, and for the same reason.

@census none (helper, the `S5-F3` boundary) -/
@[reducible] noncomputable def moduleOfOpposite (A : Type u) [CommRing A] (X : Type u)
    [AddCommGroup X] [Module Aᵐᵒᵖ X] : Module A X :=
  Module.compHom X (RingEquiv.toOpposite A).toRingHom

/-- The left action of `moduleOfOpposite` is the right one, on the nose — the `hX` that
`Balanced.equivTensor` asks for.  @census none (helper) -/
theorem smul_of_opposite (A : Type u) [CommRing A] (X : Type u)
    [AddCommGroup X] [Module Aᵐᵒᵖ X] (a : A) (x : X) :
    (letI := moduleOfOpposite A X; a • x) = MulOpposite.op a • x := rfl

/-! ### Crossing the `S5-F3` boundary: `X ⊗_A Y` **is** mathlib's `Y ⊗[A] X`

`Balanced` is defined as a quotient of `Y ⊗[K] X` because that is what the standing assumptions
supply; mathlib's `Y ⊗[A] X` is the same object whenever `A` is commutative and `X`'s left and
right `A`-actions agree.  Every §2.6 decomposition row has a `Balanced` on the left of an
isomorphism and a mathlib `⊗` on the right, so the boundary is crossed once here and **named**,
rather than four times inside four proofs where it could not be audited.

**The compatibility is a hypothesis, not an instance** — `hX : a • x = op a • x`.  Deriving
`Module A X` from `Module Aᵐᵒᵖ X` by a global instance is the shape `CONVENTIONS.md` §3 forbids:
an ambient instance that can be silently re-derived and compete.  `Twist.rebase` and
`Balanced.map` already carry their compatibility as an explicit argument for the same reason, and
this follows them.

@census none (helpers, the `S5-F3` boundary)
-/

section Bridge
variable {K : Type u} [Field K]
variable {A : Type u} [CommRing A] [Algebra K A]
variable {B : Type u} [Ring B] [Algebra K B]
variable {Y : Type u} [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y]
  [SMulCommClass K Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y] [IsScalarTower K A Y]
  [IsScalarTower K Bᵐᵒᵖ Y]
variable {X : Type u} [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [Module A X]
  [IsScalarTower K Aᵐᵒᵖ X] [IsScalarTower K A X]

/-- forward: `Balanced K A B Y X → Y ⊗[A] X`. -/
noncomputable def toTensorA
    (hX : ∀ (a : A) (x : X), a • x = MulOpposite.op a • x) :
    Balanced K A B Y X →ₗ[Bᵐᵒᵖ] (Y ⊗[A] X) := by
  refine Balanced.lift (A := A) (B := B)
    ({ toFun := fun y =>
        { toFun := fun x => y ⊗ₜ[A] x
          map_add' := fun _ _ => TensorProduct.tmul_add _ _ _
          map_smul' := fun c x => by
            show y ⊗ₜ[A] (c • x) = c • (y ⊗ₜ[A] x)
            rw [← IsScalarTower.algebraMap_smul A c x,
              ← IsScalarTower.algebraMap_smul A c (y ⊗ₜ[A] x), TensorProduct.tmul_smul] }
       map_add' := fun _ _ => by ext x; exact TensorProduct.add_tmul _ _ _
       map_smul' := fun c y => by
         ext x
         show ((c • y) ⊗ₜ[A] x) = c • (y ⊗ₜ[A] x)
         rw [← IsScalarTower.algebraMap_smul A c y,
           ← IsScalarTower.algebraMap_smul A c (y ⊗ₜ[A] x), TensorProduct.smul_tmul'] } ) ?_ ?_
  · intro a y x
    show (a • y) ⊗ₜ[A] x = y ⊗ₜ[A] (MulOpposite.op a • x)
    rw [← hX, TensorProduct.smul_tmul]
  · intro b y x
    show (b • y) ⊗ₜ[A] x = b • (y ⊗ₜ[A] x)
    exact (TensorProduct.smul_tmul' b y x).symm


theorem Balanced.mk_zero_left (y : Y) :
    Balanced.mk (K := K) (A := A) (B := B) (0 : X) y = 0 := by
  show Submodule.Quotient.mk (M := Y ⊗[K] X) (y ⊗ₜ[K] (0 : X)) = 0
  rw [TensorProduct.tmul_zero]
  rfl

theorem Balanced.mk_zero_right (x : X) :
    Balanced.mk (K := K) (A := A) (B := B) x (0 : Y) = 0 := by
  show Submodule.Quotient.mk (M := Y ⊗[K] X) ((0 : Y) ⊗ₜ[K] x) = 0
  rw [TensorProduct.zero_tmul]
  rfl

/-- backward: `Y ⊗[A] X → Balanced K A B Y X`. -/
noncomputable def ofTensorA
    (hX : ∀ (a : A) (x : X), a • x = MulOpposite.op a • x) :
    (Y ⊗[A] X) →+ Balanced K A B Y X :=
  TensorProduct.liftAddHom
    ({ toFun := fun y =>
        { toFun := fun x => Balanced.mk (B := B) x y
          map_zero' := Balanced.mk_zero_left (B := B) y
          map_add' := fun x x' => Balanced.mk_add_left (B := B) x x' y }
       map_zero' := by
         ext x
         exact Balanced.mk_zero_right (K := K) (A := A) (B := B) x
       map_add' := fun y y' => by ext x; exact Balanced.mk_add_right (B := B) x y y' })
    (fun a y x => by
      show Balanced.mk (B := B) x (a • y) = Balanced.mk (B := B) (a • x) y
      rw [hX, Balanced.mk_smul])


/-- **`X ⊗_A Y` is mathlib's `Y ⊗[A] X`** — the S5-F3 boundary, crossed once and named. -/
noncomputable def Balanced.equivTensor
    (hX : ∀ (a : A) (x : X), a • x = MulOpposite.op a • x) :
    Balanced K A B Y X ≃ₗ[Bᵐᵒᵖ] (Y ⊗[A] X) := by
  refine AddEquiv.toLinearEquiv
    { toFun := toTensorA (B := B) hX
      invFun := ofTensorA (B := B) hX
      left_inv := ?_
      right_inv := ?_
      map_add' := map_add _ } (fun b t => (toTensorA (B := B) hX).map_smul b t)
  · intro t
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K A B Y X) t
    induction s with
    | zero => simp
    | tmul y x => rfl
    | add s s' hs hs' =>
        have hmk : Submodule.Quotient.mk (p := balancedRel K A B Y X) (s + s')
            = Submodule.Quotient.mk s + Submodule.Quotient.mk s' := rfl
        rw [hmk, map_add, map_add, hs, hs']
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul y x => rfl
    | add p q hp hq => rw [map_add, map_add, hp, hq]

@[simp] theorem Balanced.equivTensor_mk
    (hX : ∀ (a : A) (x : X), a • x = (MulOpposite.op a : Aᵐᵒᵖ) • x) (x : X) (y : Y) :
    Balanced.equivTensor (A := A) (B := B) hX (Balanced.mk (K := K) (A := A) (B := B) x y) = y ⊗ₜ[A] x := rfl

/-- **The `B`-linear variant** of `Balanced.equivTensor`, for commutative `B`.

**Why this must live here and not at the use site** (finding `S5-F7`, `DESIGN-NOTES` §52): the
seam is created by constructing the `≃ₗ[B]` *outside* the place its `Module` is introduced, so no
fix that stays outside can avoid crossing it.  Built here, `map_smul` is discharged at
construction against the very `Module` the `≃ₗ` carries.

The `Module B` on each side is an **instance binder** and its action is pinned by an accompanying
**value hypothesis** (`hL`, `hR`) rather than assumed to reduce — the value-guard rule
(`CONVENTIONS.md` §3) applied prospectively, at birth.  That pairing is what closes the seam: a
caller cannot supply a `Module` without also supplying the equation its `•` satisfies, so the
obligation and the caller's lemmas are about the same operation by construction.

@census none (helper, `S5-F7`) -/
noncomputable def Balanced.equivTensorL
    (hX : ∀ (a : A) (x : X), a • x = (MulOpposite.op a : Aᵐᵒᵖ) • x)
    [Module B (Balanced K A B Y X)] [Module B (Y ⊗[A] X)]
    (hL : ∀ (c : B) (z : Balanced K A B Y X), c • z = MulOpposite.op c • z)
    (hR : ∀ (c : B) (z : Y ⊗[A] X), c • z = MulOpposite.op c • z) :
    Balanced K A B Y X ≃ₗ[B] (Y ⊗[A] X) :=
  AddEquiv.toLinearEquiv (Balanced.equivTensor (B := B) hX).toAddEquiv (fun c x => by
    rw [hL, hR]
    exact (Balanced.equivTensor (B := B) hX).map_smul (MulOpposite.op c) x)

/-- **Value guard for `equivTensorL`, from birth** — its action on a generator, `rfl`.
@census none (guard, `CONVENTIONS.md` §3) -/
@[simp] theorem Balanced.equivTensorL_mk
    (hX : ∀ (a : A) (x : X), a • x = (MulOpposite.op a : Aᵐᵒᵖ) • x)
    [Module B (Balanced K A B Y X)] [Module B (Y ⊗[A] X)]
    (hL : ∀ (c : B) (z : Balanced K A B Y X), c • z = MulOpposite.op c • z)
    (hR : ∀ (c : B) (z : Y ⊗[A] X), c • z = MulOpposite.op c • z) (x : X) (y : Y) :
    Balanced.equivTensorL (A := A) (B := B) hX hL hR
        (Balanced.mk (K := K) (A := A) (B := B) x y) = y ⊗ₜ[A] x := rfl

@[simp] theorem Balanced.equivTensor_symm_tmul
    (hX : ∀ (a : A) (x : X), a • x = (MulOpposite.op a : Aᵐᵒᵖ) • x) (x : X) (y : Y) :
    (Balanced.equivTensor (A := A) (B := B) hX).symm (y ⊗ₜ[A] x) = Balanced.mk (K := K) (A := A) (B := B) x y := rfl
end Bridge

/-! ### General helpers for the fibre-summed `RQ2-2.18-C3` (finding **S5-F10**, `§67`)

Five species-free lemmas the fibre-summed identification consumes, kept here with the rest of the
`MD-S5-09` family rather than in `Species/Rep/BaseChange.lean`, because none of them mentions a
species: a scalar tower descends to a quotient module; a `K`-action factoring through `N` inherits
`N`'s commutation and tower facts; a ring equivalence of `B`-algebras respecting the two structure
maps is `Bᵐᵒᵖ`-linear (the shape every step of the chain arrives in); and an equivariance statement
about all of `X ⊗_A Y` may be checked on generators.
-/

theorem quotient_isScalarTower {R S M : Type u} [Ring R] [AddCommGroup M]
    [Module R M] [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    (P : Submodule R M) : IsScalarTower S R (M ⧸ P) :=
  ⟨fun s r x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective P x
    exact congrArg (Submodule.Quotient.mk (p := P)) (smul_assoc s r y)⟩

/-- A `K`-action factoring through `N` commutes with anything `N` commutes with. -/
theorem smulCommK_of_tower (K N : Type u) [Field K] [Field N] [Algebra K N]
    {M₁ : Type u} [AddCommGroup M₁] [Module K M₁] [Module N M₁] [IsScalarTower K N M₁]
    {R : Type u} [Monoid R] [DistribMulAction R M₁] [SMulCommClass N R M₁] :
    SMulCommClass K R M₁ :=
  ⟨fun c b m => by
    rw [← IsScalarTower.algebraMap_smul N c m, ← IsScalarTower.algebraMap_smul N c (b • m),
      smul_comm]⟩

/-- A tower through `N` composes with one over `N`. -/
theorem towerK_of_tower (K N : Type u) [Field K] [Field N] [Algebra K N]
    {M₁ : Type u} [AddCommGroup M₁] [Module K M₁] [Module N M₁] [IsScalarTower K N M₁]
    {R : Type u} [Semiring R] [SMul K R] [Algebra N R] [IsScalarTower K N R] [Module R M₁]
    [IsScalarTower N R M₁] : IsScalarTower K R M₁ :=
  ⟨fun c b m => by
    rw [← IsScalarTower.algebraMap_smul N c b, smul_assoc, IsScalarTower.algebraMap_smul N]⟩


noncomputable def ringEquivToOpLinear {B M₁ M₂ : Type u} [CommRing B] [Ring M₁] [Ring M₂]
    [Algebra B M₁] [Algebra B M₂] [Module Bᵐᵒᵖ M₁] [Module Bᵐᵒᵖ M₂]
    (h₁ : ∀ (c : B) (x : M₁), (MulOpposite.op c) • x = algebraMap B M₁ c * x)
    (h₂ : ∀ (c : B) (x : M₂), (MulOpposite.op c) • x = algebraMap B M₂ c * x)
    (e : M₁ ≃+* M₂) (he : ∀ c : B, e (algebraMap B M₁ c) = algebraMap B M₂ c) :
    M₁ ≃ₗ[Bᵐᵒᵖ] M₂ :=
  AddEquiv.toLinearEquiv e.toAddEquiv (fun c x => by
    show e (c • x) = c • e x
    rw [show c = MulOpposite.op c.unop from rfl, h₁, h₂, map_mul, he])

@[simp] theorem ringEquivToOpLinear_apply {B M₁ M₂ : Type u} [CommRing B] [Ring M₁] [Ring M₂]
    [Algebra B M₁] [Algebra B M₂] [Module Bᵐᵒᵖ M₁] [Module Bᵐᵒᵖ M₂]
    (h₁ : ∀ (c : B) (x : M₁), (MulOpposite.op c) • x = algebraMap B M₁ c * x)
    (h₂ : ∀ (c : B) (x : M₂), (MulOpposite.op c) • x = algebraMap B M₂ c * x)
    (e : M₁ ≃+* M₂) (he : ∀ c : B, e (algebraMap B M₁ c) = algebraMap B M₂ c) (x : M₁) :
    ringEquivToOpLinear h₁ h₂ e he x = e x := rfl

/-- An `A'`-equivariance statement about all of `X ⊗_A Y`, checked on generators. -/
theorem balanced_smul_ext {K : Type u} [Field K] {A B Y X : Type u} [Ring A] [Algebra K A]
    [Ring B] [Algebra K B] [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y]
    [SMulCommClass K Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y] [IsScalarTower K A Y]
    [IsScalarTower K Bᵐᵒᵖ Y] [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X]
    [IsScalarTower K Aᵐᵒᵖ X]
    {W : Type u} [AddCommGroup W] {A' : Type u}
    [DistribSMul A' (Balanced K A B Y X)] [DistribSMul A' W]
    (φ : Balanced K A B Y X →+ W) (α : A')
    (H : ∀ (x : X) (y : Y), φ (α • Balanced.mk x y) = α • φ (Balanced.mk x y))
    (t : Balanced K A B Y X) : φ (α • t) = α • φ t := by
  have h : φ.comp (DistribSMul.toAddMonoidHom (Balanced K A B Y X) α)
      = (DistribSMul.toAddMonoidHom W α).comp φ := Balanced.ext_forall H
  exact congrArg (fun f => f t) h


/-- Module-finiteness transfers between a ring and its opposite when the two actions agree. -/
theorem finite_of_op {R M : Type u} [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    (h : ∀ (r : R) (x : M), r • x = MulOpposite.op r • x) (hfin : Module.Finite Rᵐᵒᵖ M) :
    Module.Finite R M := by
  obtain ⟨s, hs⟩ := hfin.1
  refine ⟨⟨s, le_antisymm le_top ?_⟩⟩
  rintro x -
  have hx : x ∈ Submodule.span Rᵐᵒᵖ (↑s : Set M) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha =>
      rw [show c • a = c.unop • a from (h c.unop a).symm]
      exact Submodule.smul_mem _ _ ha

/-- …and back. -/
theorem finite_op_of {R M : Type u} [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    (h : ∀ (r : R) (x : M), r • x = MulOpposite.op r • x) (hfin : Module.Finite R M) :
    Module.Finite Rᵐᵒᵖ M := by
  obtain ⟨s, hs⟩ := hfin.1
  refine ⟨⟨s, le_antisymm le_top ?_⟩⟩
  rintro x -
  have hx : x ∈ Submodule.span R (↑s : Set M) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul c a _ ha =>
      rw [h c a]
      exact Submodule.smul_mem _ _ ha


end RationalQuivers
