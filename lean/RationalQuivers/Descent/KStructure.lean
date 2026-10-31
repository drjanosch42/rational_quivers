module

public import RationalQuivers.Descent.Semilinear
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

/-!
# Galois descent: `K`-structures on `L`-vector spaces

Formalizes §1.1 of `latex/rational_quivers.tex` (census `RQ2-1.16`, `RQ2-1.17`, `RQ2-1.18`).

## Main definitions / results
* `RationalQuivers.Descent.IsSemilinearAction` — a `Gal(L/K)`-action on an `L`-vector space whose
  every element acts `σ`-linearly (helper class; the semi-linearity half of a `K`-structure).
* `RationalQuivers.Descent.KStructure` — a **`K`-structure** on an `L`-vector space
  (`UNLABELED-kstructure`, census `RQ2-1.16`): semi-linear **and continuous**.
* `RationalQuivers.Descent.IsKRational` — **`K`-rational map** (`UNLABELED-krational-map`,
  census `RQ2-1.17`).
* `RationalQuivers.Descent.canonicalKStructure` — the canonical `K`-structure on `L ⊗[K] V`
  (`UNLABELED-canonical-kstructure`, census `RQ2-1.18`).

## Implementation notes
* **Shape of `KStructure` (design decision, S0).**  The source (after the D2 editorial correction)
  makes continuity *part of the definition of a `K`-structure*, so continuity is a field of
  `KStructure` rather than a separate `IsSmooth` predicate; the stage plan's row proposing a
  separate `Descent.KStructure.IsSmooth` predates that correction.  See
  `workflow/stages/S0/DESIGN-NOTES.md`.
* **Bridging, not forking (R2).**  The source's "group homomorphism `φ : Gal(L/K) → Aut_K(V)` with
  every `φ_σ` `σ`-linear" is expressed on top of mathlib's `DistribMulAction Gal(L/K) V`: the group
  homomorphism into `Aut_K(V)` is recovered as `KStructure.toAutHom`, and `Prop`-valued mixins
  carry the two extra axioms.  Continuity is carried in the **open-stabilizer** form demanded by
  clause `RQ2-1.16-C4`, and `continuousSMul` bridges it to mathlib's `ContinuousSMul` for the
  discrete topology (clause `RQ2-1.16-C3`) via `continuousSMul_iff_stabilizer_isOpen`.
  See `workflow/ledger/MATHLIB-DECISIONS.tsv` rows `MD-S0-02` … `MD-S0-05`.
* An `L`-vector space `V` is regarded as a `K`-vector space via `K → L`; following mathlib idiom
  this is carried as `[Module K V] [IsScalarTower K L V]` rather than by `Module.compHom`, to avoid
  scalar-action diamonds.
-/

universe u v w

open scoped TensorProduct

namespace RationalQuivers.Descent

section Semilinear

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable (V : Type v) [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
  [DistribMulAction Gal(L/K) V]

/-- Helper class (no census row of its own): the `Gal(L/K)`-action on the `L`-vector space `V`
acts by `σ`-linear maps, i.e. `σ • (a • v) = σ(a) • (σ • v)`.

This is the semi-linearity half of the source's notion of a `K`-structure (census `RQ2-1.16`,
clause `RQ2-1.16-C2`); it is split off so that the *continuity* half — the other clause of the same
definition — can be stated, and shown vacuous for finite `L/K` (clause `RQ2-1.16-C5`), on its own.

@census    none
-/
class IsSemilinearAction : Prop where
  /-- Every `σ ∈ Gal(L/K)` acts `σ`-linearly. -/
  smul_smul_semilinear : ∀ (σ : Gal(L/K)) (a : L) (v : V), σ • (a • v) = σ a • (σ • v)

variable {K L V}

omit [Module K V] [IsScalarTower K L V] in
/-- Helper (no census row): the defining semi-linearity identity, in `IsSemilinear` form. -/
theorem isSemilinear_smul [IsSemilinearAction K L V] (σ : Gal(L/K)) :
    IsSemilinear σ (fun v : V => σ • v) :=
  IsSemilinearAction.smul_smul_semilinear σ

variable (K L V)

/-- Helper instance (no census row): a semi-linear `Gal(L/K)`-action is `K`-linear, because
`σ ∈ Gal(L/K)` fixes `K` pointwise.  This is what makes `KStructure.toAutHom` land in `Aut_K(V)`
(clause `RQ2-1.16-C1`). -/
instance (priority := 100) IsSemilinearAction.toSMulCommClass [IsSemilinearAction K L V] :
    SMulCommClass Gal(L/K) K V where
  smul_comm σ c v :=
    calc σ • c • v
        = σ • ((algebraMap K L c) • v) := by rw [IsScalarTower.algebraMap_smul]
      _ = σ (algebraMap K L c) • (σ • v) := IsSemilinearAction.smul_smul_semilinear σ _ v
      _ = (algebraMap K L c) • (σ • v) := by rw [AlgEquiv.commutes]
      _ = c • σ • v := by rw [IsScalarTower.algebraMap_smul]

/-- **`K`-structure on an `L`-vector space** (`UNLABELED-kstructure`, §1.1 of the source).

A `K`-structure on an `L`-vector space `V` is a group homomorphism
`φ : Gal(L/K) → Aut_K(V)`, `σ ↦ φ_σ`, such that each `φ_σ` is `σ`-linear and such that the
resulting action `Gal(L/K) × V → V` is continuous, `V` being topologized discretely; explicitly,
every `v ∈ V` is fixed by `φ_σ` for all `σ` in an open subgroup of `Gal(L/K)`, and for finite
`L/K` the continuity condition is vacuous.

The action itself is carried by mathlib's `DistribMulAction Gal(L/K) V` (which *is* the datum of a
group homomorphism `Gal(L/K) → AddAut V`, `RQ2-1.16-C1`, identified with the collection
`(φ_σ)_σ`, `RQ2-1.16-C6`); this class adds the two defining axioms.  `Aut_K(V)`-valuedness
(`RQ2-1.16-C1`) is `KStructure.toAutHom`; `σ`-linearity (`RQ2-1.16-C2`) is the inherited field;
continuity (`RQ2-1.16-C3`) is `KStructure.continuousSMul`, carried in the open-stabilizer form
(`RQ2-1.16-C4`); vacuity for finite `L/K` (`RQ2-1.16-C5`) is
`KStructure.of_finiteDimensional`.

@census    RQ2-1.16
@source    def:kstructure
@clauses   RQ2-1.16-Hs1, RQ2-1.16-H1, RQ2-1.16-C1, RQ2-1.16-C2, RQ2-1.16-C3, RQ2-1.16-C4, RQ2-1.16-C5,
           RQ2-1.16-C6
@imports   none
@divergence generalized: stated without the §1.1 standing Galois hypothesis (clause
  `RQ2-1.16-Hs1`); paper's case recovered by specialization.  The class is stated for an arbitrary
  field extension `L/K`: `Gal(L/K)` carries mathlib's `krullTopology` for any extension, so
  "continuous action" and "open subgroup of `Gal(L/K)`" (clauses `C3`, `C4`) are meaningful without
  `IsGalois K L`, and the definition is simply the source's condition read over that topology.  The
  paper's `K`-structure is the special case `[IsGalois K L]`.  Clause `C5` is likewise proved in the
  more general form `[FiniteDimensional K L]` (`KStructure.of_finiteDimensional`).  Nothing is
  weakened: the CONCLUSION side is unchanged and the hypothesis side is strictly larger.

  Signature note (verified with `#check` on the elaborated constant, per `CONVENTIONS.md`'s
  instance-binder pruning rule): Lean PRUNES the unused binders `[Module K V]` and
  `[IsScalarTower K L V]` from this class, so `KStructure K L V` is stated over `[Module L V]`
  and `[DistribMulAction Gal(L/K) V]` alone.  This is faithful to clause `RQ2-1.16-H1`: the source
  says "every `L`-vector space `V` can be considered as a `K`-vector space via the embedding
  `K → L`", i.e. the `K`-structure of `V` is a canonical CONSTRUCTION, not an extra datum.  The
  `Aut_K(V)`-valuedness of clause `RQ2-1.16-C1` is stated where it belongs, on `toAutHom`, whose
  signature does carry `[Module K V] [IsScalarTower K L V]` (also verified by `#check`), and every
  object of `Descent.VecK` carries both as explicit structure fields.
-/
class KStructure : Prop extends IsSemilinearAction K L V where
  /-- Continuity of the action for the discrete topology on `V`, in the equivalent
  open-stabilizer form: every `v ∈ V` is fixed by an open subgroup of `Gal(L/K)`. -/
  isOpen_stabilizer : ∀ v : V, IsOpen (MulAction.stabilizer Gal(L/K) v : Set Gal(L/K))

/-- Clause `RQ2-1.16-C1`/`RQ2-1.16-C6`: a `K`-structure *is* a group homomorphism
`Gal(L/K) → Aut_K(V)`, `σ ↦ φ_σ`, identified with the collection `(φ_σ)_σ`.

@census    none
-/
def toAutHom [IsSemilinearAction K L V] : Gal(L/K) →* (V ≃ₗ[K] V) where
  toFun σ := DistribMulAction.toLinearEquiv K V σ
  map_one' := by ext v; exact one_smul _ v
  map_mul' σ τ := by ext v; exact mul_smul σ τ v

@[simp]
theorem toAutHom_apply [IsSemilinearAction K L V] (σ : Gal(L/K)) (v : V) :
    toAutHom K L V σ v = σ • v := rfl

omit [Module K V] [IsScalarTower K L V] in
/-- Clause `RQ2-1.16-C3`: for a `K`-structure the action `Gal(L/K) × V → V` is continuous when `V`
carries the discrete topology.  Bridges the open-stabilizer form of the axiom to mathlib's
`ContinuousSMul` via `continuousSMul_iff_stabilizer_isOpen`.

@census    none
-/
theorem KStructure.continuousSMul [KStructure K L V] [TopologicalSpace V] [DiscreteTopology V] :
    ContinuousSMul Gal(L/K) V :=
  continuousSMul_iff_stabilizer_isOpen.2 (KStructure.isOpen_stabilizer (K := K) (L := L) (V := V))

/-- Clause `RQ2-1.16-C5`: for a **finite** Galois extension `L/K` the continuity condition is
vacuous — every semi-linear action is a `K`-structure.  (`Gal(L/K)` is then discrete.)

@census    none
-/
instance (priority := 100) KStructure.of_finiteDimensional [FiniteDimensional K L]
    [IsSemilinearAction K L V] : KStructure K L V where
  isOpen_stabilizer _ := isOpen_discrete _

end Semilinear

section KRational

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable {V : Type v} [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
  [DistribMulAction Gal(L/K) V]
variable {W : Type w} [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W]
  [DistribMulAction Gal(L/K) W]

/-- **`K`-rational map** (`UNLABELED-krational-map`, §1.1 of the source).

A map `φ ∈ Hom_L(V,W)` between two `L`-vector spaces with `K`-structure is *`K`-rational* if it
commutes with the two given actions of `Gal(L/K)` on `V` and `W`.  `L`-linearity
(clause `RQ2-1.17-C1`) is carried by the type `V →ₗ[L] W`; commutation with the Galois actions
(clause `RQ2-1.17-C2`) is the body.

@census    RQ2-1.17
@source    def:krationalmap
@clauses   RQ2-1.17-H1, RQ2-1.17-C1, RQ2-1.17-C2
@imports   none
@divergence generalized: the predicate is stated for `L`-vector spaces carrying any
  `Gal(L/K)`-action, not only ones carrying a `K`-structure (clause `RQ2-1.17-H1`); the paper's case
  is the specialization `[KStructure K L V] [KStructure K L W]`, which is exactly how it is used —
  the morphisms of `Descent.VecK`, whose objects carry `KStructure` by construction.  Requiring
  `KStructure` here would add a hypothesis the CONCLUSION (`C1`, `C2`) does not use.  Nothing is
  weakened: the conclusion side is unchanged and the hypothesis side is strictly larger.  As for
  `KStructure`, Lean prunes the unused `[Module K V]`/`[IsScalarTower K L V]` binders from the
  elaborated signature (verified with `#check`); `L`-linearity, clause `RQ2-1.17-C1`, is carried by
  the argument's type `V →ₗ[L] W` and is unaffected.
-/
def IsKRational (φ : V →ₗ[L] W) : Prop :=
  ∀ (σ : Gal(L/K)) (v : V), φ (σ • v) = σ • φ v

variable {K L}

omit [Module K V] [IsScalarTower K L V] [Module K W] [IsScalarTower K L W] in
/-- Helper (no census row): the identity is `K`-rational. -/
theorem isKRational_id : IsKRational K L (LinearMap.id : V →ₗ[L] V) := fun _ _ => rfl

omit [Module K V] [IsScalarTower K L V] [Module K W] [IsScalarTower K L W] in
/-- Helper (no census row): `K`-rational maps are closed under composition. -/
theorem IsKRational.comp {X : Type*} [AddCommGroup X] [Module K X] [Module L X]
    [IsScalarTower K L X] [DistribMulAction Gal(L/K) X]
    {ψ : W →ₗ[L] X} {φ : V →ₗ[L] W} (hψ : IsKRational K L ψ) (hφ : IsKRational K L φ) :
    IsKRational K L (ψ ∘ₗ φ) := fun σ v => by
  simp only [LinearMap.coe_comp, Function.comp_apply, hφ σ v, hψ σ (φ v)]

end KRational

section CanonicalKStructure

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable (V : Type u) [AddCommGroup V] [Module K V]

/-- Helper (no census row): `1 ∈ Gal(L/K)` acts on `L ⊗[K] V` as the identity. -/
theorem galoisTensorMap_one :
    TensorProduct.map (1 : Gal(L/K)).toLinearMap (LinearMap.id : V →ₗ[K] V) = LinearMap.id := by
  refine TensorProduct.ext' fun a v => ?_
  simp [TensorProduct.map_tmul]

/-- Helper (no census row): the action of `Gal(L/K)` on `L ⊗[K] V` is multiplicative. -/
theorem galoisTensorMap_mul (σ τ : Gal(L/K)) :
    TensorProduct.map (σ * τ).toLinearMap (LinearMap.id : V →ₗ[K] V)
      = (TensorProduct.map σ.toLinearMap (LinearMap.id : V →ₗ[K] V)) ∘ₗ
        (TensorProduct.map τ.toLinearMap (LinearMap.id : V →ₗ[K] V)) := by
  refine TensorProduct.ext' fun a v => ?_
  simp [TensorProduct.map_tmul]

/-- The canonical `Gal(L/K)`-action on `L ⊗[K] V`, `σ • (α ⊗ v) = σ(α) ⊗ v` (helper; the data
underlying census `RQ2-1.18`).

@census    none
-/
instance galoisTensorAction : DistribMulAction Gal(L/K) (L ⊗[K] V) :=
  TensorProduct.leftDistribMulAction

/-- Helper (no census row): the action of `σ` on `L ⊗[K] V` is `σ ⊗ id`. -/
theorem galoisTensorAction_apply (σ : Gal(L/K)) (x : L ⊗[K] V) :
    σ • x = TensorProduct.map σ.toLinearMap (LinearMap.id : V →ₗ[K] V) x := by
  induction x with
  | tmul a v => rfl
  | add x y hx hy => rw [smul_add, map_add, hx, hy]

@[simp]
theorem galoisTensorAction_tmul (σ : Gal(L/K)) (a : L) (v : V) :
    σ • (a ⊗ₜ[K] v) = σ a ⊗ₜ[K] v := rfl

/-- Helper (no census row): the canonical action on `L ⊗[K] V` is semi-linear. -/
theorem galoisTensorAction_semilinear (σ : Gal(L/K)) (a : L) (x : L ⊗[K] V) :
    σ • (a • x) = σ a • (σ • x) := by
  simp only [galoisTensorAction_apply]
  induction x with
  | tmul b v =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.map_tmul,
        TensorProduct.map_tmul, TensorProduct.smul_tmul', smul_eq_mul]
      simp [map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- Helper (no census row): the canonical action on `L ⊗[K] V` is semi-linear — the
`σ`-linearity half of clause `RQ2-1.18-C1`. -/
instance galoisTensorAction_isSemilinear : IsSemilinearAction K L (L ⊗[K] V) where
  smul_smul_semilinear := galoisTensorAction_semilinear K L V

/-- Helper (no census row): every `x ∈ L ⊗[K] V` is fixed by an **open** subgroup of `Gal(L/K)`.
Proof by induction on `x`: a pure tensor `a ⊗ v` is fixed by the stabilizer of `a ∈ L`, open by
mathlib's `stabilizer_isOpen_of_isIntegral`; sums use the (finite) intersection of open subgroups.

@census    none
-/
theorem exists_openSubgroup_fixing [Algebra.IsIntegral K L] (x : L ⊗[K] V) :
    ∃ U : OpenSubgroup Gal(L/K),
      (U : Subgroup Gal(L/K)) ≤ MulAction.stabilizer Gal(L/K) x := by
  induction x with
  | tmul a v =>
      refine ⟨⟨MulAction.stabilizer Gal(L/K) a,
        stabilizer_isOpen_of_isIntegral (K := K) (L := L) a⟩, fun σ hσ => ?_⟩
      have hσa : σ a = a := hσ
      show σ • (a ⊗ₜ[K] v) = a ⊗ₜ[K] v
      rw [galoisTensorAction_tmul, hσa]
  | add x y hx hy =>
      obtain ⟨Ux, hUx⟩ := hx
      obtain ⟨Uy, hUy⟩ := hy
      refine ⟨Ux ⊓ Uy, fun σ hσ => ?_⟩
      have h1 : σ • x = x := hUx hσ.1
      have h2 : σ • y = y := hUy hσ.2
      show TensorProduct.map σ.toLinearMap (LinearMap.id : V →ₗ[K] V) (x + y) = x + y
      rw [map_add]
      rw [show TensorProduct.map σ.toLinearMap (LinearMap.id : V →ₗ[K] V) x = x from h1,
        show TensorProduct.map σ.toLinearMap (LinearMap.id : V →ₗ[K] V) y = y from h2]

/-- **The canonical `K`-structure on `L ⊗_K V`** (`UNLABELED-canonical-kstructure`, §1.1 of the
source).

If `V` is a `K`-vector space then `L ⊗_K V` carries a canonical `K`-structure, explicitly given by
`φ_σ (α ⊗ v) = σ(α) ⊗ v` for `σ ∈ Gal(L/K)`, `α ∈ L`, `v ∈ V` (clause `RQ2-1.18-C1`, whose explicit
formula is `galoisTensorAction_tmul`).  Canonicity (`RQ2-1.18-C2`) is naturality in `V`, i.e. the
functoriality recorded by `isKRational_baseChange` (`RQ2-1.18-C3`) and, in `Descent/Galois.lean`,
by `baseChangeFunctor`.

@census    RQ2-1.18
@source    prop:canonicalkstructure
@clauses   RQ2-1.18-Hs1, RQ2-1.18-H1, RQ2-1.18-H2, RQ2-1.18-C1, RQ2-1.18-C2, RQ2-1.18-C3
@imports   none
@divergence generalized: paper's standing Galois hypothesis weakened to Algebra.IsIntegral;
  paper's form recovered by instance search.  §1.1 of the source opens "Let `L/K` be a finite or
  infinite Galois extension", a subsection-level standing hypothesis that this statement inherits;
  the census records it explicitly only on `RQ2-1.13-H1` (SUPERSEDED 2026-08-29 by census r6 /
  `census-v1.3`, which added `RQ2-1.14-Hs1`, `RQ2-1.16-Hs1` and `RQ2-1.18-Hs1` recording exactly this
  standing hypothesis; `RQ2-1.18-Hs1` is cited in `@clauses` above.  The sentence is left standing
  because it is part of the coordinator's ruling as drafted; G4 verification finding C-1).  The
  continuity half of `RQ2-1.18-C1` is
  FALSE without it — for `K = ℚ`, `L = ℚ(t)`, `V = ℚ` the Krull topology on `Aut(ℚ(t)/ℚ)` is
  indiscrete (ℚ is algebraically closed in ℚ(t), so ℚ is the only finite-dimensional intermediate
  field), while the stabilizer of `t ⊗ 1` is the trivial subgroup, which is proper because
  `t ↦ 1/t` is a nontrivial ℚ-automorphism.  We therefore state it under `Algebra.IsIntegral K L`,
  the weakest sufficient hypothesis; `IsGalois K L ⇒ Algebra.IsIntegral K L` by instance search, so
  the paper's claim is the special case (`CONVENTIONS.md` §6 ladder step 2).  Approved by the
  coordinator; see `workflow/stages/S0/DESIGN-NOTES.md` §7.
-/
instance canonicalKStructure [Algebra.IsIntegral K L] : KStructure K L (L ⊗[K] V) where
  isOpen_stabilizer x := by
    obtain ⟨U, hU⟩ := exists_openSubgroup_fixing K L V x
    exact Subgroup.isOpen_of_openSubgroup _ hU

variable {V}
variable {W : Type u} [AddCommGroup W] [Module K W]

/-- Clause `RQ2-1.18-C3`: every `K`-linear map `φ : V → W` induces a `K`-rational map
`1 ⊗ φ : L ⊗ V → L ⊗ W`.

@census    none
-/
theorem isKRational_baseChange (φ : V →ₗ[K] W) :
    IsKRational K L (LinearMap.baseChange L φ) := by
  intro σ x
  show LinearMap.baseChange L φ (TensorProduct.map σ.toLinearMap LinearMap.id x)
      = TensorProduct.map σ.toLinearMap LinearMap.id (LinearMap.baseChange L φ x)
  induction x with
  | tmul a v =>
      simp only [TensorProduct.map_tmul, LinearMap.baseChange_tmul, LinearMap.id_coe, id_eq,
        AlgEquiv.toLinearMap_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

end CanonicalKStructure

section NonVacuity

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- **G5 non-vacuity** (`WORKFLOW.md` §4/G5): `L` itself, with `Gal(L/K)` acting tautologically
by field automorphisms, is a semi-linear `Gal(L/K)`-action on the `L`-vector space `L`.

@census    none
-/
instance isSemilinearAction_self : IsSemilinearAction K L L where
  smul_smul_semilinear σ a b := by
    simp only [smul_eq_mul, AlgEquiv.smul_def, map_mul]

/-- **G5 non-vacuity** (`WORKFLOW.md` §4/G5): the tautological action of `Gal(L/K)` on `L` is a
`K`-structure on the `L`-vector space `L`.  Continuity is mathlib's
`stabilizer_isOpen_of_isIntegral`.

What this witness does and does not establish (corrected 2026-08-29, G4 verification finding C-2):
it proves `KStructure` is **inhabited**, and `selfObj_nontrivial` proves the carrier is nontrivial.
It does **not** establish non-degeneracy of the *action*: nothing here rules out the all-trivial
interpretation, since `K = L` satisfies every witness in this file with `Gal(L/K)` trivial and
every `φ_σ = id`.  An earlier revision of this docstring asserted "for `L ≠ K` the action is
nontrivial too"; that is true but was never formalised, and the claim is withdrawn here rather than
left standing unproved.  Excluding the degenerate model is `Meta/Vacuity.lean`'s job (G3/G5, the
instrument owner's file); the probes it must carry are listed in `DESIGN-NOTES.md` §11.

@census    none
-/
instance kStructure_self [Algebra.IsIntegral K L] : KStructure K L L where
  isOpen_stabilizer x := stabilizer_isOpen_of_isIntegral (K := K) (L := L) x

/-- **G5 non-vacuity**: the carrier of `kStructure_self` is nontrivial.  (Carrier-level only —
free for any field; see the `kStructure_self` docstring and G4 finding C-2.) -/
example : Nontrivial L := inferInstance

/-- **G5 non-vacuity**: `L ⊗[K] V` really does carry a `K`-structure, for every `K`-vector
space `V` — the inhabitant announced for `canonicalKStructure`. -/
example [Algebra.IsIntegral K L] (V : Type u) [AddCommGroup V] [Module K V] :
    Nonempty (KStructure K L (L ⊗[K] V)) := ⟨inferInstance⟩

/-!
### Excluding the all-trivial interpretation (G4 finding **C-2**, `DESIGN-NOTES.md` §11)

The witnesses above are all satisfied by `K = L`, where `Gal(L/K)` is trivial and every `φ_σ` is
the identity.  The lemmas that follow close that hole: a general *moving-action* lemma, a
general criterion for `Gal(L/K)` to be non-trivial, and an **infinite** Galois model (probe 4 of
`DESIGN-NOTES.md` §11 — the sharpest gap, since infinite `L/K` is what clause `RQ2-1.13-C6` and
this whole layer are for).  The finite concrete model `ℂ/ℝ` and the fixed-point probes live in
`Descent/Galois.lean`, beside `selfObj` and `fixedPoints`.
-/

/-- **G5 non-vacuity, probe 2** (`DESIGN-NOTES.md` §11): if `Gal(L/K)` is non-trivial then its
tautological action on `L` genuinely **moves** a point.  This is the direct test against the
all-trivial interpretation, and it holds for *every* extension with a non-trivial Galois group,
finite or infinite.

The content is mathlib's `AlgEquiv.apply_faithfulSMul : FaithfulSMul (L ≃ₐ[K] L) L`: an algebra
automorphism fixing every point *is* the identity.

@census    none (G5 non-degeneracy witness)
-/
theorem exists_smul_ne_self [Nontrivial Gal(L/K)] : ∃ (σ : Gal(L/K)) (v : L), σ • v ≠ v := by
  obtain ⟨σ, hσ⟩ := exists_ne (1 : Gal(L/K))
  refine ⟨σ, ?_⟩
  by_contra hcon
  refine hσ (eq_of_smul_eq_smul (α := L) fun v => ?_)
  rw [one_smul]
  exact not_not.mp (not_exists.mp hcon v)

/-- **G5 non-vacuity**: an infinite Galois extension has a non-trivial Galois group.
(Contrapositive: if every automorphism were the identity then every element of `L` would be
`Gal(L/K)`-fixed, hence in `K` by mathlib's infinite Galois correspondence
`InfiniteGalois.mem_range_algebraMap_iff_fixed`, so `algebraMap K L` would be surjective and
`L/K` finite of degree one.)

Note that this is proved with **no finiteness hypothesis** — the infinite-Galois half of mathlib's
`FieldTheory/Galois/Infinite.lean` is what makes it available.

@census    none (G5 non-degeneracy witness)
-/
theorem nontrivial_gal_of_not_finiteDimensional [IsGalois K L]
    (h : ¬ FiniteDimensional K L) : Nontrivial Gal(L/K) := by
  by_contra hcon
  rw [not_nontrivial_iff_subsingleton] at hcon
  refine h (Module.Finite.of_surjective (Algebra.linearMap K L) fun x => ?_)
  have hfix : ∀ f : Gal(L/K), f x = x := fun f => by rw [Subsingleton.elim f 1]; rfl
  obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hfix
  exact ⟨y, hy⟩

/-- The prime field `𝔽₂`, base of the infinite Galois model below.

@census    none (G5 model)
-/
abbrev F2 : Type := ZMod 2

/-- An algebraic closure `𝔽̄₂` of `𝔽₂`.  With `F2` it is the **infinite** Galois extension that
probe 4 of `DESIGN-NOTES.md` §11 asks for.  A finite base field is used rather than `ℚ̄/ℚ` because
infinite-dimensionality is then a two-line argument (an algebraically closed field is infinite,
while a finite-dimensional module over a finite field is finite); over `ℚ` the same statement needs
a family of irreducible polynomials of unbounded degree.

@census    none (G5 model)
-/
abbrev F2Bar : Type := AlgebraicClosure F2

/-- `𝔽̄₂/𝔽₂` is Galois: normal because it is an algebraic closure (`IsAlgClosure.normal`) and
separable because `𝔽₂` is perfect (`PerfectField.ofFinite`, then
`Algebra.IsAlgebraic.isSeparable_of_perfectField`).  Left as a `theorem` rather than an `instance`:
in the spirit of `CONVENTIONS.md` §5 this file adds no global instance about mathlib's own types.
Use `haveI`.

@census    none (G5 model: infinite Galois extension, probe 4)
-/
theorem isGalois_algClosure_two : IsGalois F2 F2Bar := ⟨⟩

/-- `𝔽̄₂/𝔽₂` is **infinite**: an algebraically closed field is infinite, but a finite-dimensional
module over the finite field `𝔽₂` is finite.

@census    none (G5 model: probe 4, the infinity claim)
-/
theorem not_finiteDimensional_algClosure_two : ¬ FiniteDimensional F2 F2Bar := fun _ =>
  have : Finite F2Bar := Module.finite_of_finite F2
  not_finite F2Bar

/-- `Gal(𝔽̄₂/𝔽₂)` is non-trivial — the infinite model is not the degenerate one either.

@census    none (G5 model: probe 4 + probe 1)
-/
theorem nontrivial_gal_algClosure_two : Nontrivial Gal(F2Bar/F2) :=
  haveI := isGalois_algClosure_two
  nontrivial_gal_of_not_finiteDimensional F2 F2Bar not_finiteDimensional_algClosure_two

/-- **G5 non-vacuity, probe 4**: the infinite extension `𝔽̄₂/𝔽₂` carries a `K`-structure.  The
continuity field is discharged by `stabilizer_isOpen_of_isIntegral`, *not* by the finite-extension
shortcut: `krullTopology_discreteTopology_of_finiteDimensional`'s hypothesis is refuted here by
`not_finiteDimensional_algClosure_two`. -/
example : KStructure F2 F2Bar F2Bar := inferInstance

/-- **G5 non-vacuity, probe 4**: the canonical `K`-structure on `L ⊗_K V` exists over the infinite
extension too, for every `𝔽₂`-vector space `V`. -/
example (V : Type) [AddCommGroup V] [Module F2 V] :
    Nonempty (KStructure F2 F2Bar (F2Bar ⊗[F2] V)) := ⟨inferInstance⟩

/-- **G5 non-vacuity, probes 2 + 4**: the action of `Gal(𝔽̄₂/𝔽₂)` on `𝔽̄₂` genuinely moves a
point.  The all-trivial interpretation is excluded at an *infinite* extension. -/
example : ∃ (σ : Gal(F2Bar/F2)) (v : F2Bar), σ • v ≠ v :=
  haveI := nontrivial_gal_algClosure_two
  exists_smul_ne_self F2 F2Bar

end NonVacuity

end RationalQuivers.Descent
