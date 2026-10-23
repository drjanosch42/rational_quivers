import RationalQuivers.Descent.KStructure
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Galois descent: the Galois action on `Hom_L(V,W)`

Formalizes the `Hom`-paragraph of §1.1 of `latex/rational_quivers.tex` (census `RQ2-1.14`).

## Main definitions / results
* `RationalQuivers.Descent.homGaloisAction` — the action `φ^σ := σ ∘ φ ∘ σ⁻¹` of `Gal(L/K)` on
  `Hom_L(V,W)` (`UNLABELED-galois-action-on-hom`, census `RQ2-1.14`).
* `RationalQuivers.Descent.homGaloisAction_isOpen_stabilizer`,
  `RationalQuivers.Descent.homGaloisAction_continuousSMul` — the *conditional* continuity claim
  (clause `RQ2-1.14-C3`): it needs the actions on `V` and `W` to be continuous **and** `V` to be
  finite-dimensional over `L`.

## Implementation notes
The continuity claim of the source is explicitly conditional (clause `RQ2-1.14-H3`); the action
itself (`RQ2-1.14-C1`, `RQ2-1.14-C2`) is defined under semi-linearity alone, with no continuity and
no finiteness hypothesis, exactly as the source does.
-/

universe u v w

open scoped TensorProduct

namespace RationalQuivers.Descent

section HomAction

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable (V : Type v) [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
  [DistribMulAction Gal(L/K) V] [IsSemilinearAction K L V]
variable (W : Type w) [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W]
  [DistribMulAction Gal(L/K) W] [IsSemilinearAction K L W]

/-- Helper (no census row): `σ` applied to `σ⁻¹ a` is `a`. -/
private theorem apply_inv_apply (σ : Gal(L/K)) (a : L) : σ (σ⁻¹ a) = a := by
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

/-- Clause `RQ2-1.14-C1`: `φ^σ := σ ∘ φ ∘ σ⁻¹` is again `L`-linear.  This is the underlying map of
the action `homGaloisAction`.

@census    none
-/
def homGaloisMap (σ : Gal(L/K)) (φ : V →ₗ[L] W) : V →ₗ[L] W where
  toFun v := σ • φ (σ⁻¹ • v)
  map_add' v v' := by
    rw [smul_add, map_add, smul_add]
  map_smul' a v := by
    have h₁ : σ⁻¹ • (a • v) = (σ⁻¹ a) • (σ⁻¹ • v) :=
      IsSemilinearAction.smul_smul_semilinear (V := V) σ⁻¹ a v
    have h₂ : σ • ((σ⁻¹ a) • φ (σ⁻¹ • v)) = σ (σ⁻¹ a) • (σ • φ (σ⁻¹ • v)) :=
      IsSemilinearAction.smul_smul_semilinear (V := W) σ (σ⁻¹ a) _
    simp only [RingHom.id_apply, h₁, map_smul, h₂, apply_inv_apply]

omit [Module K V] [IsScalarTower K L V] [Module K W] [IsScalarTower K L W] in
@[simp]
theorem homGaloisMap_apply (σ : Gal(L/K)) (φ : V →ₗ[L] W) (v : V) :
    homGaloisMap K L V W σ φ v = σ • φ (σ⁻¹ • v) := rfl

omit [Module K V] [IsScalarTower K L V] [Module K W] [IsScalarTower K L W] in
/-- Helper (no census row): `φ^1 = φ`. -/
private theorem homGaloisMap_one (φ : V →ₗ[L] W) : homGaloisMap K L V W 1 φ = φ := by
  ext v; simp only [homGaloisMap_apply, inv_one, one_smul]

omit [Module K V] [IsScalarTower K L V] [Module K W] [IsScalarTower K L W] in
/-- Helper (no census row): `φ^(στ) = (φ^τ)^σ`. -/
private theorem homGaloisMap_mul (σ τ : Gal(L/K)) (φ : V →ₗ[L] W) :
    homGaloisMap K L V W (σ * τ) φ
      = homGaloisMap K L V W σ (homGaloisMap K L V W τ φ) := by
  ext v; simp only [homGaloisMap_apply, mul_smul, mul_inv_rev]

omit [Module K V] [IsScalarTower K L V] [Module K W] [IsScalarTower K L W] in
/-- Helper (no census row): `0^σ = 0`. -/
private theorem homGaloisMap_zero (σ : Gal(L/K)) :
    homGaloisMap K L V W σ (0 : V →ₗ[L] W) = 0 := by
  ext v; simp only [homGaloisMap_apply, LinearMap.zero_apply, smul_zero]

omit [Module K V] [IsScalarTower K L V] [Module K W] [IsScalarTower K L W] in
/-- Helper (no census row): `(φ + ψ)^σ = φ^σ + ψ^σ`. -/
private theorem homGaloisMap_add (σ : Gal(L/K)) (φ ψ : V →ₗ[L] W) :
    homGaloisMap K L V W σ (φ + ψ)
      = homGaloisMap K L V W σ φ + homGaloisMap K L V W σ ψ := by
  ext v; simp only [homGaloisMap_apply, LinearMap.add_apply, smul_add]

/-- **The `Gal(L/K)`-action on `Hom_L(V,W)`** (`UNLABELED-galois-action-on-hom`, §1.1 of the
source).

Let `V, W` be `L`-vector spaces, each endowed with a semi-linear action of `Gal(L/K)`
(clause `RQ2-1.14-H1`).  Then `Gal(L/K)` acts on the set of `L`-linear maps `Hom_L(V,W)` via
`φ^σ := σ ∘ φ ∘ σ⁻¹` for all `σ ∈ Gal(L/K)` and `φ ∈ Hom_L(V,W)` (clause `RQ2-1.14-H2`).

`φ^σ` is again `L`-linear (clause `RQ2-1.14-C1`, the map `homGaloisMap`), and this is an action
(clause `RQ2-1.14-C2`, the `MulAction` fields below).  Under the *additional* hypotheses that the
actions on `V` and `W` are continuous and that `V` is finite-dimensional over `L`
(clause `RQ2-1.14-H3`), the action is continuous for the discrete topology on `Hom_L(V,W)`
(clause `RQ2-1.14-C3`): see `homGaloisAction_isOpen_stabilizer` and
`homGaloisAction_continuousSMul`.  Asserting continuity unconditionally would be unfaithful.

@census    RQ2-1.14
@source    def:homgaloisaction
@clauses   RQ2-1.14-Hs1, RQ2-1.14-H1, RQ2-1.14-H2, RQ2-1.14-H3, RQ2-1.14-C1, RQ2-1.14-C2, RQ2-1.14-C3
@imports   none
@divergence generalized: stated without the §1.1 standing Galois hypothesis (clause
  `RQ2-1.14-Hs1`); paper's case recovered by specialization.  The action `φ^σ := σ ∘ φ ∘ σ⁻¹`
  (clauses `C1`, `C2`) needs only that `Gal(L/K)` acts semi-linearly on `V` and `W`, and the
  conditional continuity claim (`H3`, `C3`) needs only that the two actions are `KStructure`s —
  which already carries the open-stabilizer content over mathlib's `krullTopology`, defined for any
  extension `L/K`.  No `IsGalois K L` is therefore assumed; the paper's statement is the special
  case.  Nothing is weakened: the CONCLUSION side is unchanged and the hypothesis side is strictly
  larger.
-/
instance homGaloisAction : DistribMulAction Gal(L/K) (V →ₗ[L] W) where
  smul σ φ := homGaloisMap K L V W σ φ
  one_smul := homGaloisMap_one K L V W
  mul_smul := homGaloisMap_mul K L V W
  smul_zero := homGaloisMap_zero K L V W
  smul_add := homGaloisMap_add K L V W

omit [Module K V] [IsScalarTower K L V] [Module K W] [IsScalarTower K L W] in
@[simp]
theorem homGaloisAction_apply (σ : Gal(L/K)) (φ : V →ₗ[L] W) (v : V) :
    (σ • φ) v = σ • φ (σ⁻¹ • v) := rfl

end HomAction

section Continuity

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
variable (V : Type v) [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
  [DistribMulAction Gal(L/K) V] [KStructure K L V]
variable (W : Type w) [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W]
  [DistribMulAction Gal(L/K) W] [KStructure K L W]

set_option linter.unusedSectionVars false in
/-- Clause `RQ2-1.14-C3`, open-stabilizer form: if the actions on `V` and `W` are continuous
(i.e. are `K`-structures) and `V` is finite-dimensional over `L`, then every `φ ∈ Hom_L(V,W)` has
open stabilizer in `Gal(L/K)`.

@census    none
-/
theorem homGaloisAction_isOpen_stabilizer
    [FiniteDimensional L V] (φ : V →ₗ[L] W) :
    IsOpen (MulAction.stabilizer Gal(L/K) φ : Set Gal(L/K)) := by
  classical
  -- Choose a finite `L`-basis `b` of `V`.
  set ι := Module.Free.ChooseBasisIndex L V with hι
  set b : Module.Basis ι L V := Module.Free.chooseBasis L V with hb
  -- For each basis vector, the stabilizers of `b j` and of `φ (b j)` are open, by continuity of
  -- the two `K`-structures.
  let U : ι → OpenSubgroup Gal(L/K) := fun j =>
    ⟨MulAction.stabilizer Gal(L/K) (b j), KStructure.isOpen_stabilizer (K := K) (L := L) (b j)⟩ ⊓
    ⟨MulAction.stabilizer Gal(L/K) (φ (b j)),
      KStructure.isOpen_stabilizer (K := K) (L := L) (φ (b j))⟩
  -- Their (finite) intersection is an open subgroup contained in the stabilizer of `φ`.
  refine Subgroup.isOpen_of_openSubgroup _ (U := Finset.univ.inf U) ?_
  intro σ hσ
  have hσj : ∀ j : ι, σ ∈ U j := fun j =>
    (Finset.inf_le (Finset.mem_univ j) : Finset.univ.inf U ≤ U j) hσ
  have hb' : ∀ j : ι, σ • b j = b j := fun j => (hσj j).1
  have hφb : ∀ j : ι, σ • φ (b j) = φ (b j) := fun j => (hσj j).2
  have hinv : ∀ j : ι, σ⁻¹ • b j = b j := fun j => by
    conv_lhs => rw [← hb' j]
    rw [inv_smul_smul]
  refine (MulAction.mem_stabilizer_iff).2 (b.ext fun j => ?_)
  rw [homGaloisAction_apply, hinv j, hφb j]

set_option linter.unusedSectionVars false in
/-- Clause `RQ2-1.14-C3`: under the hypotheses of `RQ2-1.14-H3` the action of `Gal(L/K)` on
`Hom_L(V,W)` is continuous for the discrete topology on `Hom_L(V,W)`.

@census    none
-/
theorem homGaloisAction_continuousSMul
    [FiniteDimensional L V] [TopologicalSpace (V →ₗ[L] W)] [DiscreteTopology (V →ₗ[L] W)] :
    ContinuousSMul Gal(L/K) (V →ₗ[L] W) :=
  continuousSMul_iff_stabilizer_isOpen.2 (homGaloisAction_isOpen_stabilizer K L V W)

end Continuity

end RationalQuivers.Descent
