module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.CategoryTheory.Category.Quiv
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Topology.Algebra.MulAction

/-!
# Statement-surface definitions (Solution side)

Byte-identical copy of the definitions block of `Challenge.lean` (checked by
`scripts/check-statement-copy.sh`), compiled against the same Mathlib imports, so that its constants
coincide with the Challenge's constants (this is what Comparator compares).  Do not edit by hand.
-/
@[expose] public section

-- BEGIN STATEMENT DEFINITIONS (byte-identical in Challenge.lean and RQPalomar/Statement.lean)

/-! ## Galois twist on `L ⊗_K W` (from `RQStatement.Unipotent.Twist`) -/

section Twist
universe u v w
open scoped TensorProduct
namespace RQStatement.Unipotent
variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {WK : Type v} [AddCommGroup WK] [Module K WK]

/-- `σ ⊗ 1` on `L ⊗_K W_K`. -/
def galoisTwist (σ : Gal(L/K)) : (L ⊗[K] WK) →ₗ[K] (L ⊗[K] WK) :=
  TensorProduct.map σ.toLinearMap LinearMap.id

@[simp]
theorem galoisTwist_tmul (σ : Gal(L/K)) (a : L) (w : WK) :
    galoisTwist (WK := WK) σ (a ⊗ₜ[K] w) = σ a ⊗ₜ[K] w := rfl

@[simp]
theorem galoisTwist_one : galoisTwist (1 : Gal(L/K)) = (LinearMap.id : (L ⊗[K] WK) →ₗ[K] _) := by
  refine TensorProduct.ext' fun a w => ?_
  simp

theorem galoisTwist_mul (σ τ : Gal(L/K)) :
    galoisTwist (WK := WK) (σ * τ) = (galoisTwist σ).comp (galoisTwist τ) := by
  refine TensorProduct.ext' fun a w => ?_
  simp [galoisTwist_tmul]

theorem galoisTwist_inv_galoisTwist (σ : Gal(L/K)) (x : L ⊗[K] WK) :
    galoisTwist σ⁻¹ (galoisTwist σ x) = x := by
  have := congrArg (fun f => (f : (L ⊗[K] WK) →ₗ[K] _) x) (galoisTwist_mul (WK := WK) σ⁻¹ σ)
  rw [inv_mul_cancel] at this
  simpa using this.symm

theorem galoisTwist_galoisTwist_inv (σ : Gal(L/K)) (x : L ⊗[K] WK) :
    galoisTwist σ (galoisTwist σ⁻¹ x) = x := by
  have := congrArg (fun f => (f : (L ⊗[K] WK) →ₗ[K] _) x) (galoisTwist_mul (WK := WK) σ σ⁻¹)
  rw [mul_inv_cancel] at this
  simpa using this.symm

/-- `σ ⊗ 1` as an additive automorphism. -/
def galoisTwistEquiv (σ : Gal(L/K)) : (L ⊗[K] WK) ≃+ (L ⊗[K] WK) where
  toFun := galoisTwist σ
  invFun := galoisTwist σ⁻¹
  left_inv := galoisTwist_inv_galoisTwist σ
  right_inv := galoisTwist_galoisTwist_inv σ
  map_add' _ _ := map_add _ _ _

end RQStatement.Unipotent
end Twist

/-! ## `L_E = E(√-1)` and `χ_E` (from `RQStatement.HC.ImagUnit`) -/

section ImagUnitSec
namespace RQStatement.HC
open Polynomial

/-- `L_E`: a field generated over `E` by a root `i` of `X² + 1` (so `L_E = E` iff `√-1 ∈ E`). -/
structure ImagUnit (E : Type) [Field E] where
  /-- the field `L_E` -/
  L : Type
  [field : Field L]
  [algebra : Algebra E L]
  /-- the chosen `√-1 ∈ L_E` -/
  i : L
  i_mul_i : i * i = -1
  adjoin_eq_top : Algebra.adjoin E {i} = ⊤

attribute [instance] ImagUnit.field ImagUnit.algebra

namespace ImagUnit

variable {E : Type} [Field E] (D : ImagUnit E)

theorem isIntegral_i : IsIntegral E D.i :=
  ⟨X ^ 2 + 1, by
    have : (X ^ 2 + 1 : E[X]) = X ^ 2 + C 1 := by simp
    rw [this]; exact monic_X_pow_add_C 1 two_ne_zero, by simp [sq, D.i_mul_i]⟩

noncomputable def powerBasis : PowerBasis E D.L :=
  PowerBasis.ofAdjoinEqTop D.isIntegral_i D.adjoin_eq_top

instance finiteDimensional : FiniteDimensional E D.L := D.powerBasis.finite

theorem finrank_le_two : Module.finrank E D.L ≤ 2 := by
  rw [D.powerBasis.finrank]
  show (minpoly E D.i).natDegree ≤ 2
  have hq : (X ^ 2 + 1 : E[X]) = X ^ 2 + C 1 := by simp
  have hp : (X ^ 2 + 1 : E[X]) ≠ 0 := by
    rw [hq]; exact (monic_X_pow_add_C 1 two_ne_zero).ne_zero
  have hd : minpoly E D.i ∣ (X ^ 2 + 1 : E[X]) :=
    minpoly.dvd E D.i (by simp [sq, D.i_mul_i])
  calc (minpoly E D.i).natDegree ≤ (X ^ 2 + 1 : E[X]).natDegree :=
        natDegree_le_of_dvd hd hp
    _ = 2 := by
        have : (X ^ 2 + 1 : E[X]) = X ^ 2 + C 1 := by simp
        rw [this, natDegree_X_pow_add_C]

instance normal : Normal E D.L where
  splits' := by
    intro x
    obtain h | h := le_iff_lt_or_eq.mp ((minpoly.natDegree_le x).trans D.finrank_le_two)
    · exact Splits.of_natDegree_le_one <| natDegree_map_le.trans (Nat.lt_succ_iff.mp h)
    · exact Splits.of_natDegree_eq_two ((natDegree_map _).trans h)
        ((eval_map_algebraMap _ _).trans (minpoly.aeval E x))

section CharZero

variable [CharZero E]
set_option linter.unusedSectionVars false

/-- `L_E/E` is Galois. -/
instance isGalois : IsGalois E D.L := ⟨⟩

instance charZero : CharZero D.L :=
  charZero_of_injective_algebraMap (algebraMap E D.L).injective

theorem i_ne_zero : D.i ≠ 0 := by
  intro h; have := D.i_mul_i; rw [h, mul_zero] at this
  exact (neg_ne_zero.mpr (one_ne_zero (α := D.L))) this.symm

theorem i_ne_neg_i : D.i ≠ -D.i := by
  intro h
  have h2 : (2 : D.L) * D.i = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact two_ne_zero h'
  · exact D.i_ne_zero h'

theorem apply_i (σ : D.L ≃ₐ[E] D.L) : σ D.i = D.i ∨ σ D.i = -D.i := by
  have h : (σ D.i - D.i) * (σ D.i + D.i) = 0 := by
    have h1 : σ D.i * σ D.i = -1 := by rw [← map_mul, D.i_mul_i, map_neg, map_one]
    linear_combination h1 - D.i_mul_i
  rcases mul_eq_zero.mp h with h' | h'
  · left; exact sub_eq_zero.mp h'
  · right; exact eq_neg_of_add_eq_zero_left h'

/-- `χ_E : G_E → {±1}`, `σ(√-1) = χ_E(σ)√-1`. -/
noncomputable def chi (σ : D.L ≃ₐ[E] D.L) : ℤˣ := by
  classical exact if σ D.i = D.i then 1 else -1

theorem chi_eq_one_iff {σ : D.L ≃ₐ[E] D.L} : D.chi σ = 1 ↔ σ D.i = D.i := by
  unfold chi; split_ifs with h <;> simp [h]

theorem chi_eq_neg_one_iff {σ : D.L ≃ₐ[E] D.L} : D.chi σ = -1 ↔ σ D.i = -D.i := by
  unfold chi; split_ifs with h
  · simp only [h]; constructor
    · intro h'; exact absurd h' (by decide)
    · intro h'; exact absurd h' D.i_ne_neg_i
  · simpa using (D.apply_i σ).resolve_left h

theorem chi_cases (σ : D.L ≃ₐ[E] D.L) : D.chi σ = 1 ∨ D.chi σ = -1 := by
  rcases D.apply_i σ with h | h
  · exact Or.inl (D.chi_eq_one_iff.mpr h)
  · exact Or.inr (D.chi_eq_neg_one_iff.mpr h)

theorem chi_spec (σ : D.L ≃ₐ[E] D.L) : σ D.i = ((D.chi σ : ℤ) : D.L) * D.i := by
  rcases D.chi_cases σ with h | h
  · rw [D.chi_eq_one_iff.mp h, h]; simp
  · rw [D.chi_eq_neg_one_iff.mp h, h]; simp

theorem chi_one : D.chi 1 = 1 := D.chi_eq_one_iff.mpr rfl

theorem chi_mul (σ τ : D.L ≃ₐ[E] D.L) : D.chi (σ * τ) = D.chi σ * D.chi τ := by
  have key : (σ * τ) D.i = (((D.chi σ * D.chi τ : ℤˣ) : ℤ) : D.L) * D.i := by
    show σ (τ D.i) = _
    rw [D.chi_spec τ, map_mul, map_intCast, D.chi_spec σ]
    push_cast; ring
  rcases D.chi_cases σ with hσ | hσ <;> rcases D.chi_cases τ with hτ | hτ <;>
    rw [hσ, hτ] at key ⊢ <;> norm_num at key ⊢
  · exact D.chi_eq_one_iff.mpr key
  · exact D.chi_eq_neg_one_iff.mpr key
  · exact D.chi_eq_neg_one_iff.mpr key
  · exact D.chi_eq_one_iff.mpr key

/-- `χ_E : G_E →* ℤˣ`. -/
noncomputable def chiHom : (D.L ≃ₐ[E] D.L) →* ℤˣ where
  toFun := D.chi
  map_one' := D.chi_one
  map_mul' := D.chi_mul

end CharZero
end ImagUnit
end RQStatement.HC
end ImagUnitSec

/-! ## Weight data of an `𝔰𝔩₂`-module (from `RQStatement.HC.Sl2`, `HC.Graded`, `HC.Casimir`) -/

section Weights
universe u v
namespace RQStatement.HC

variable (E : Type u) [Field E] (M : Type v) [AddCommGroup M] [Module E M]

/-- A `ℤ`-graded `E`-module `M = ⨁ M_n` with an `𝔰𝔩₂`-triple `H, X, Y`: `H` acts on `M_n` by `n`,
`X : M_n → M_{n+2}`, `Y : M_n → M_{n-2}`, `[H,X] = 2X`, `[H,Y] = -2Y`, `[X,Y] = H`. -/
structure WeightData where
  comp : ℤ → Submodule E M
  isInternal : DirectSum.IsInternal comp
  H : Module.End E M
  X : Module.End E M
  Y : Module.End E M
  H_apply : ∀ (n : ℤ) (v : M), v ∈ comp n → H v = (n : E) • v
  X_mem : ∀ (n : ℤ) (v : M), v ∈ comp n → X v ∈ comp (n + 2)
  Y_mem : ∀ (n : ℤ) (v : M), v ∈ comp n → Y v ∈ comp (n - 2)
  lie_H_X : H * X - X * H = (2 : E) • X
  lie_H_Y : H * Y - Y * H = -((2 : E) • Y)
  lie_X_Y : X * Y - Y * X = H

variable {E M}

namespace WeightData

variable (W : WeightData E M)

/-- The Casimir `C = H² - 2H + 4XY + 1`. -/
def casimir : Module.End E M := W.H ^ 2 - 2 * W.H + 4 * (W.X * W.Y) + 1

end WeightData
end RQStatement.HC

namespace RQStatement.HC
variable {E : Type u} [Field E] {M : Type v} [AddCommGroup M] [Module E M]
namespace WeightData

/-- `M ≃ ⨁ M_n`. -/
noncomputable def decompEquiv (W : WeightData E M) :
    M ≃ₗ[E] DirectSum ℤ (fun n : ℤ => (W.comp n : Submodule E M)) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap W.comp) W.isInternal).symm

/-- The projection `M → M_n`. -/
noncomputable def proj (W : WeightData E M) (n : ℤ) : Module.End E M where
  toFun v := ((W.decompEquiv v n : W.comp n) : M)
  map_add' a b := by simp
  map_smul' c a := by simp [DirectSum.smul_apply]

/-- `N` is stable under `H`, `X`, `Y`. -/
def OpStable (W : WeightData E M) (N : Submodule E M) : Prop :=
  (∀ v ∈ N, W.H v ∈ N) ∧ (∀ v ∈ N, W.X v ∈ N) ∧ (∀ v ∈ N, W.Y v ∈ N)

/-- `N` is graded: it contains the homogeneous components of its elements. -/
def IsHomog (W : WeightData E M) (N : Submodule E M) : Prop :=
  ∀ (n : ℤ) (v : M), v ∈ N → W.proj n v ∈ N

end WeightData
end RQStatement.HC

namespace RQStatement.HC
variable {E : Type u} {M : Type v} [Field E] [Algebra ℚ E] [AddCommGroup M] [Module E M]

/-- Generalized infinitesimal character `λ = ℓ²`: `(C - λ)^m = 0` on `M` for some `m`. -/
def HasGeneralizedInfinitesimalCharacter (W : WeightData E M) (ℓ : ℕ) : Prop :=
  ∃ m : ℕ, (W.casimir - (algebraMap ℚ E ((ℓ : ℚ) ^ 2)) • (1 : Module.End E M)) ^ m = 0

end RQStatement.HC
end Weights

/-! ## `HC_λ(𝔤,K)_E` (from `RQStatement.HC.Category`) -/

section HCSec
universe u
namespace RQStatement.HC
open CategoryTheory
open scoped TensorProduct

section ObjOver
variable {E : Type u} [Field E] {V : Type u} [AddCommGroup V] [Module E V]

/-- The `(𝔤,K)`-submodule generated by `S`: the smallest graded, `H,X,Y`-stable submodule
containing `S`. -/
def gkSpanOver (W : WeightData E V) (S : Set V) : Submodule E V :=
  sInf {N | S ⊆ (N : Set V) ∧ W.OpStable N ∧ W.IsHomog N}

end ObjOver

section Descent
open RQStatement.Unipotent
set_option linter.dupNamespace false
variable {E : Type} [Field E] (D : ImagUnit E)

section GalAct
variable {Mq : Type} [AddCommGroup Mq] [Module E Mq] {Mi : Type} [AddCommGroup Mi] [Module D.L Mi]

/-- The `σ`-semilinear action `σ ⊗ 1` on `M_{L_E} ≅ L_E ⊗_E M_E`. -/
noncomputable def galActOf (b : (D.L ⊗[E] Mq) ≃ₗ[D.L] Mi) (σ : D.L ≃ₐ[E] D.L) : Mi ≃+ Mi :=
  (b.symm.toAddEquiv.trans (galoisTwistEquiv σ)).trans b.toAddEquiv

end GalAct

/-- Compatibility of `g = σ ⊗ 1` with the weight data, with sign `s = χ_E(σ)`:
`σ M_n = M_{sn}`, `σH = sHσ`; `σX = Xσ, σY = Yσ` if `s = 1`; `σX = Yσ, σY = Xσ` if `s = -1`. -/
structure GalCompat {Mi : Type} [AddCommGroup Mi] [Module D.L Mi] (W : WeightData D.L Mi)
    (g : Mi ≃+ Mi) (s : ℤˣ) : Prop where
  comp : ∀ (n : ℤ) (v : Mi), v ∈ W.comp n → g v ∈ W.comp ((s : ℤ) * n)
  H : ∀ v, g (W.H v) = (s : ℤ) • W.H (g v)
  X_one : s = 1 → ∀ v, g (W.X v) = W.X (g v)
  Y_one : s = 1 → ∀ v, g (W.Y v) = W.Y (g v)
  X_neg : s = -1 → ∀ v, g (W.X v) = W.Y (g v)
  Y_neg : s = -1 → ∀ v, g (W.Y v) = W.X (g v)

variable [CharZero E]

/-- An object of `HC_λ(𝔤,K)_E`, `λ = ℓ²` (descent presentation): an `E`-vector space `M_E`, its
base change `M_{L_E} = L_E ⊗_E M_E` with weight decomposition and `𝔰𝔩₂`-action, generalized
infinitesimal character `λ`, admissible, `M_n = 0` unless `n ≡ ℓ - 1 (mod 2)`, finitely generated,
and with the actions defined over `E` (every `σ ⊗ 1` is compatible with sign `χ_E(σ)`). -/
structure HC (ℓ : ℕ) (E : Type) [Field E] [CharZero E] (D : ImagUnit E) where
  /-- `M_E` -/
  form : Type
  [formAddCommGroup : AddCommGroup form]
  [formModule : Module E form]
  /-- `M_{L_E}` -/
  carrier : Type
  [addCommGroup : AddCommGroup carrier]
  [module : Module D.L carrier]
  /-- `M_{L_E} = L_E ⊗_E M_E` -/
  baseChange : (D.L ⊗[E] form) ≃ₗ[D.L] carrier
  /-- `M_{L_E}[χ_n]`, `H`, `X`, `Y` -/
  weight : WeightData D.L carrier
  /-- generalized infinitesimal character `λ = ℓ²` -/
  gic : HasGeneralizedInfinitesimalCharacter weight ℓ
  /-- the actions are defined over `E` -/
  galCompat : ∀ σ : D.L ≃ₐ[E] D.L, GalCompat D weight (galActOf D baseChange σ) (D.chi σ)
  /-- admissibility -/
  admissible : ∀ n : ℤ, FiniteDimensional D.L (weight.comp n)
  /-- the central character: `-1₂` acts by `(-1)^{ℓ-1}` -/
  centralCharacter : ∀ n : ℤ, (n - ((ℓ : ℤ) - 1)) % 2 ≠ 0 → weight.comp n = ⊥
  /-- finite generation as a `(𝔤,K)`-module -/
  fg : ∃ S : Finset carrier, gkSpanOver weight (↑S : Set carrier) = ⊤

attribute [instance] HC.formAddCommGroup HC.formModule HC.addCommGroup HC.module

namespace HC

variable {D} {ℓ : ℕ}

/-- The Galois action of `σ ∈ G_E` on `M_{L_E}`. -/
noncomputable abbrev galAct (A : HC ℓ E D) (σ : D.L ≃ₐ[E] D.L) : A.carrier ≃+ A.carrier :=
  galActOf D A.baseChange σ

/-- Morphisms: `L_E`-linear maps commuting with `H`, `X`, `Y`, the grading and every `σ ⊗ 1`
(equivalently: base changes of `E`-linear `(𝔤_E, K_E)`-maps of the forms). -/
structure Hom (A B : HC ℓ E D) where
  toLinearMap : A.carrier →ₗ[D.L] B.carrier
  map_H : ∀ v, toLinearMap (A.weight.H v) = B.weight.H (toLinearMap v)
  map_X : ∀ v, toLinearMap (A.weight.X v) = B.weight.X (toLinearMap v)
  map_Y : ∀ v, toLinearMap (A.weight.Y v) = B.weight.Y (toLinearMap v)
  map_comp : ∀ (n : ℤ) (v : A.carrier), v ∈ A.weight.comp n → toLinearMap v ∈ B.weight.comp n
  map_gal : ∀ σ v, toLinearMap (A.galAct σ v) = B.galAct σ (toLinearMap v)

@[ext] theorem Hom.ext' {A B : HC ℓ E D} {f g : Hom A B} (h : f.toLinearMap = g.toLinearMap) :
    f = g := by cases f; cases g; simp_all

/-- `HC_λ(𝔤,K)_E` is a category. -/
noncomputable instance instCategory : CategoryTheory.Category (HC ℓ E D) where
  Hom A B := Hom A B
  id A := ⟨LinearMap.id, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ h => h,
    fun _ _ => rfl⟩
  comp f g :=
    ⟨g.toLinearMap.comp f.toLinearMap,
      fun v => by simp [f.map_H, g.map_H],
      fun v => by simp [f.map_X, g.map_X],
      fun v => by simp [f.map_Y, g.map_Y],
      fun n v hv => g.map_comp n _ (f.map_comp n v hv),
      fun σ v => by simp [f.map_gal, g.map_gal]⟩
  id_comp _ := by apply Hom.ext'; rfl
  comp_id _ := by apply Hom.ext'; rfl
  assoc _ _ _ := by apply Hom.ext'; rfl

end HC
end Descent
end RQStatement.HC
end HCSec

/-! ## Quivers and rational quivers (from `RQStatement.Quiver.Basic`) -/

section QuiverSec
universe u
namespace RQStatement
open CategoryTheory

/-- A finite quiver `(V, E, s, t)`. -/
structure RQuiver : Type (u + 1) where
  V : Type u
  E : Type u
  source : E → V
  target : E → V
  finite_V : Finite V
  finite_E : Finite E

attribute [instance] RQuiver.finite_V RQuiver.finite_E

namespace RQuiver

/-- Quiver morphisms. -/
structure Hom (Γ Γ' : RQuiver.{u}) : Type u where
  onV : Γ.V → Γ'.V
  onE : Γ.E → Γ'.E
  onV_source : ∀ e, onV (Γ.source e) = Γ'.source (onE e)
  onV_target : ∀ e, onV (Γ.target e) = Γ'.target (onE e)

-- Stated by hand rather than by `@[ext]` on the structure: the generated proof uses a private
-- matcher whose name contains the module name, which Comparator would see as a different constant.
@[ext] theorem Hom.ext {Γ Γ' : RQuiver.{u}} {f g : Hom Γ Γ'} (onV : f.onV = g.onV)
    (onE : f.onE = g.onE) : f = g := by
  cases f; cases g; cases onV; cases onE; rfl

protected def Hom.id (Γ : RQuiver.{u}) : Hom Γ Γ where
  onV := _root_.id
  onE := _root_.id
  onV_source _ := rfl
  onV_target _ := rfl

protected def Hom.comp {Γ Γ' Γ'' : RQuiver.{u}} (f : Hom Γ Γ') (g : Hom Γ' Γ'') : Hom Γ Γ'' where
  onV := g.onV ∘ f.onV
  onE := g.onE ∘ f.onE
  onV_source e := by
    simp only [Function.comp_apply, f.onV_source e, g.onV_source (f.onE e)]
  onV_target e := by
    simp only [Function.comp_apply, f.onV_target e, g.onV_target (f.onE e)]

instance instCategory : Category.{u, u + 1} RQuiver.{u} where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The automorphism group of a quiver. -/
abbrev Aut (Γ : RQuiver.{u}) : Type u := CategoryTheory.Aut Γ

@[simps]
def Aut.toPermV (Γ : RQuiver.{u}) : Aut Γ →* Equiv.Perm Γ.V where
  toFun a :=
    { toFun := a.asIso.hom.onV
      invFun := a.asIso.inv.onV
      left_inv := fun v => congrFun (congrArg Hom.onV a.asIso.hom_inv_id) v
      right_inv := fun v => congrFun (congrArg Hom.onV a.asIso.inv_hom_id) v }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simps]
def Aut.toPermE (Γ : RQuiver.{u}) : Aut Γ →* Equiv.Perm Γ.E where
  toFun a :=
    { toFun := a.asIso.hom.onE
      invFun := a.asIso.inv.onE
      left_inv := fun e => congrFun (congrArg Hom.onE a.asIso.hom_inv_id) e
      right_inv := fun e => congrFun (congrArg Hom.onE a.asIso.inv_hom_id) e }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The arrows `a ⟶ b` are the edges from `a` to `b`. -/
instance instQuiverV (Γ : RQuiver.{u}) : _root_.Quiver Γ.V where
  Hom a b := {e : Γ.E // Γ.source e = a ∧ Γ.target e = b}

end RQuiver

/-- An action on a discrete set is continuous (open stabilizers). -/
def IsSmooth {G X : Type*} [Group G] [TopologicalSpace G] (ρ : G →* Equiv.Perm X) : Prop :=
  ∀ x : X, IsOpen {g : G | ρ g x = x}

namespace IsSmooth
variable {G X : Type*} [Group G] [TopologicalSpace G]

theorem of_discreteTopology [DiscreteTopology G] (ρ : G →* Equiv.Perm X) : IsSmooth ρ :=
  fun _ => isOpen_discrete _

end IsSmooth

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [galoisLK : IsGalois K L]

/-- A `K`-rational quiver w.r.t. the Galois extension `L/K`: a quiver with a continuous action of
`Gal(L/K)` by automorphisms. -/
structure RationalQuiver : Type (u + 1) where
  [galois : IsGalois K L]
  toRQuiver : RQuiver.{u}
  ρ : Gal(L/K) →* RQuiver.Aut toRQuiver
  smooth_V : IsSmooth ((RQuiver.Aut.toPermV toRQuiver).comp ρ)
  smooth_E : IsSmooth ((RQuiver.Aut.toPermE toRQuiver).comp ρ)

namespace RationalQuiver
variable {K L}

abbrev V (Γ : RationalQuiver K L) : Type u := Γ.toRQuiver.V

abbrev E (Γ : RationalQuiver K L) : Type u := Γ.toRQuiver.E

instance mulActionV (Γ : RationalQuiver K L) : MulAction Gal(L/K) Γ.V :=
  MulAction.compHom _ ((RQuiver.Aut.toPermV Γ.toRQuiver).comp Γ.ρ)

instance mulActionE (Γ : RationalQuiver K L) : MulAction Gal(L/K) Γ.E :=
  MulAction.compHom _ ((RQuiver.Aut.toPermE Γ.toRQuiver).comp Γ.ρ)

end RationalQuiver
end RQStatement
end QuiverSec

/-! ## The cyclic and the Gelfand quiver (from `RQStatement.Quiver.Models`, `Quiver.OfSign`) -/

section ModelsSec
namespace RQStatement
open CategoryTheory
namespace RQuiver

/-- The cyclic quiver: vertices `−` (0), `+` (1); arrows `a : − → +`, `b : + → −`. -/
@[reducible] def cyclic : RQuiver.{0} where
  V := Fin 2
  E := Fin 2
  source := ![0, 1]
  target := ![1, 0]
  finite_V := inferInstance
  finite_E := inferInstance

/-- The Gelfand quiver: vertices `−` (0), `⋆` (1), `+` (2); arrows `a₋ : − → ⋆` (0),
`b₋ : ⋆ → −` (1), `a₊ : + → ⋆` (2), `b₊ : ⋆ → +` (3). -/
@[reducible] def gelfand : RQuiver.{0} where
  V := Fin 3
  E := Fin 4
  source := ![0, 1, 2, 1]
  target := ![1, 0, 1, 2]
  finite_V := inferInstance
  finite_E := inferInstance

@[reducible] def gelfandVertexSwap : Equiv.Perm (Fin 3) where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv := by decide
  right_inv := by decide

@[reducible] def gelfandEdgeSwap : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- The `±`-swap of the Gelfand quiver. -/
@[reducible] def gelfandSwap : RQuiver.Aut gelfand := CategoryTheory.Aut.of
  { hom :=
      { onV := gelfandVertexSwap
        onE := gelfandEdgeSwap
        onV_source := by decide
        onV_target := by decide }
    inv :=
      { onV := gelfandVertexSwap
        onE := gelfandEdgeSwap
        onV_source := by decide
        onV_target := by decide }
    hom_inv_id := by
      refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)
    inv_hom_id := by
      refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide) }

theorem gelfandSwap_mul_self : gelfandSwap * gelfandSwap = 1 := by
  refine CategoryTheory.Aut.ext (CategoryTheory.Iso.ext ?_)
  refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)

def aMinus : @_root_.Quiver.Hom gelfand.V (instQuiverV gelfand) 0 1 := ⟨0, rfl, rfl⟩

def bMinus : @_root_.Quiver.Hom gelfand.V (instQuiverV gelfand) 1 0 := ⟨1, rfl, rfl⟩

def aPlus : @_root_.Quiver.Hom gelfand.V (instQuiverV gelfand) 2 1 := ⟨2, rfl, rfl⟩

def bPlus : @_root_.Quiver.Hom gelfand.V (instQuiverV gelfand) 1 2 := ⟨3, rfl, rfl⟩

/-- The loop `a₋ b₋` at `⋆` (through `−`). -/
def pathMinus : @_root_.Quiver.Path gelfand.V (instQuiverV gelfand) 1 1 :=
  letI := instQuiverV gelfand
  (_root_.Quiver.Path.nil.cons bMinus).cons aMinus

/-- The loop `a₊ b₊` at `⋆` (through `+`). -/
def pathPlus : @_root_.Quiver.Path gelfand.V (instQuiverV gelfand) 1 1 :=
  letI := instQuiverV gelfand
  (_root_.Quiver.Path.nil.cons bPlus).cons aPlus

/-- The `±`-swap of the cyclic quiver. -/
@[reducible] def cyclicSignSwap : RQuiver.Aut cyclic := CategoryTheory.Aut.of
  { hom := { onV := Equiv.swap 0 1, onE := Equiv.swap 0 1,
             onV_source := by decide, onV_target := by decide }
    inv := { onV := Equiv.swap 0 1, onE := Equiv.swap 0 1,
             onV_source := by decide, onV_target := by decide }
    hom_inv_id := by refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)
    inv_hom_id := by refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide) }

theorem cyclicSignSwap_mul_self : cyclicSignSwap * cyclicSignSwap = 1 := by
  refine CategoryTheory.Aut.ext (CategoryTheory.Iso.ext ?_)
  refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)

end RQuiver

/-- `u ↦ 1` if `u = 1`, `u ↦ a` if `u = -1`, for an involution `a`. -/
def MonoidHom.signToInvolution {H : Type*} [Group H] (a : H) (ha : a * a = 1) : ℤˣ →* H where
  toFun u := if u = 1 then 1 else a
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [ha]

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

namespace RationalQuiver

/-- The rational quiver on `Γ` on which `σ` acts trivially if `χ(σ) = 1` and by `a` if
`χ(σ) = -1`. -/
noncomputable def ofSign (Γ : RQuiver.{0}) (a : RQuiver.Aut Γ) (ha : a * a = 1)
    (χ : Gal(L/K) →* ℤˣ) : RationalQuiver K L where
  toRQuiver := Γ
  ρ := (MonoidHom.signToInvolution a ha).comp χ
  smooth_V := IsSmooth.of_discreteTopology _
  smooth_E := IsSmooth.of_discreteTopology _

noncomputable def gelfandOfSign (χ : Gal(L/K) →* ℤˣ) : RationalQuiver K L :=
  ofSign K L RQuiver.gelfand RQuiver.gelfandSwap RQuiver.gelfandSwap_mul_self χ

noncomputable def cyclicOfSign (χ : Gal(L/K) →* ℤˣ) : RationalQuiver K L :=
  ofSign K L RQuiver.cyclic RQuiver.cyclicSignSwap RQuiver.cyclicSignSwap_mul_self χ

end RationalQuiver
end RQStatement
end ModelsSec

/-! ## Representations of rational quivers (from `RQStatement.Quiver.Rep.*`) -/

section RepSec
universe u
namespace RQStatement
namespace RationalQuiver
open CategoryTheory
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- A representation of the `K`-rational quiver `Γ`: `L`-vector spaces `M(v)`, linear edge maps
`φ_e`, and `σ`-semilinear isomorphisms `φ_{v,σ} : M(v) → M(σv)` satisfying the cocycle condition,
continuity, and compatibility with the edge maps. -/
structure Rep (Γ : RationalQuiver K L) : Type (u + 1) where
  M : Γ.V → Type u
  [addCommGroup : ∀ v, AddCommGroup (M v)]
  [module : ∀ v, Module L (M v)]
  φ : ∀ (σ : Gal(L/K)) (v : Γ.V), M v ≃+ M (σ • v)
  semilinear : ∀ (σ : Gal(L/K)) (v : Γ.V) (a : L) (m : M v), φ σ v (a • m) = σ a • φ σ v m
  cocycle : ∀ (σ τ : Gal(L/K)) (v : Γ.V) (m : M v),
      (⟨σ • (τ • v), φ σ (τ • v) (φ τ v m)⟩ : (w : Γ.V) × M w) = ⟨(σ * τ) • v, φ (σ * τ) v m⟩
  smooth : ∀ x : (v : Γ.V) × M v,
      IsOpen {σ : Gal(L/K) | (⟨σ • x.1, φ σ x.1 x.2⟩ : (w : Γ.V) × M w) = x}
  φEdge : ∀ e : Γ.E, M (Γ.toRQuiver.source e) →ₗ[L] M (Γ.toRQuiver.target e)
  edge_equivariance : ∀ (σ : Gal(L/K)) (e : Γ.E) (m : M (Γ.toRQuiver.source e))
      (m' : M (Γ.toRQuiver.source (σ • e))),
      (⟨Γ.toRQuiver.source (σ • e), m'⟩ : (w : Γ.V) × M w)
          = ⟨σ • Γ.toRQuiver.source e, φ σ (Γ.toRQuiver.source e) m⟩ →
      (⟨Γ.toRQuiver.target (σ • e), φEdge (σ • e) m'⟩ : (w : Γ.V) × M w)
          = ⟨σ • Γ.toRQuiver.target e, φ σ (Γ.toRQuiver.target e) (φEdge e m)⟩

attribute [instance] Rep.addCommGroup Rep.module

/-- Transport along an equality of indices. -/
def famCast {V : Type u} (X : V → Type u) [∀ v, AddCommGroup (X v)] [∀ v, Module L (X v)]
    {v w : V} (h : v = w) : X v ≃ₗ[L] X w := by
  subst h; exact LinearEquiv.refl L (X v)

namespace Rep
variable {Γ : RationalQuiver K L}

/-- Morphisms: linear maps `ψ_v` commuting with the edge maps and with the `φ_{v,σ}`. -/
structure Hom {Γ : RationalQuiver K L} (M N : Rep Γ) : Type u where
  ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v
  edge : ∀ (e : Γ.E) (m : M.M (Γ.toRQuiver.source e)),
      ψ (Γ.toRQuiver.target e) (M.φEdge e m) = N.φEdge e (ψ (Γ.toRQuiver.source e) m)
  rational : ∀ (σ : Gal(L/K)) (v : Γ.V) (m : M.M v),
      ψ (σ • v) (M.φ σ v m) = N.φ σ v (ψ v m)

namespace Hom

-- By hand rather than `@[ext]` on the structure (private matcher; see `RQuiver.Hom.ext`).
@[ext] theorem ext {M N : Rep Γ} {f g : Hom M N} (ψ : f.ψ = g.ψ) : f = g := by
  cases f; cases g; cases ψ; rfl

protected def id (M : Rep Γ) : Hom M M where
  ψ _ := LinearMap.id
  edge _ _ := rfl
  rational _ _ _ := rfl

protected def comp {M N P : Rep Γ} (f : Hom M N) (g : Hom N P) : Hom M P where
  ψ v := g.ψ v ∘ₗ f.ψ v
  edge e m := by
    simp only [LinearMap.coe_comp, Function.comp_apply, f.edge e m, g.edge e (f.ψ _ m)]
  rational σ v m := by
    simp only [LinearMap.coe_comp, Function.comp_apply, f.rational σ v m,
      g.rational σ v (f.ψ v m)]

end Hom
end Rep

/-- Finite-dimensional representations. -/
structure FDRep (Γ : RationalQuiver K L) : Type (u + 1) extends Rep Γ where
  finiteDimensional : ∀ v : Γ.V, FiniteDimensional L (toRep.M v)

attribute [instance] FDRep.finiteDimensional

namespace FDRep

instance instCategory (Γ : RationalQuiver K L) : Category.{u, u + 1} (FDRep Γ) where
  Hom M N := Rep.Hom M.toRep N.toRep
  id M := Rep.Hom.id M.toRep
  comp f g := f.comp g
  id_comp _ := by apply Rep.Hom.ext; rfl
  comp_id _ := by apply Rep.Hom.ext; rfl
  assoc _ _ _ := by apply Rep.Hom.ext; rfl

end FDRep

def arrowCompose {Q : RQuiver.{u}} (X : Q.V → Type u) [∀ v, AddCommGroup (X v)]
    [∀ v, Module L (X v)] (f : ∀ e : Q.E, X (Q.source e) →ₗ[L] X (Q.target e))
    {a b : Q.V} (g : a ⟶ b) : X a →ₗ[L] X b :=
  (famCast X g.2.2).toLinearMap ∘ₗ f g.1 ∘ₗ (famCast X g.2.1).symm.toLinearMap

/-- The composite of the edge maps along a path. -/
def pathCompose {Q : RQuiver.{u}} (X : Q.V → Type u) [∀ v, AddCommGroup (X v)]
    [∀ v, Module L (X v)] (f : ∀ e : Q.E, X (Q.source e) →ₗ[L] X (Q.target e)) :
    ∀ {a b : Q.V}, Quiver.Path a b → (X a →ₗ[L] X b)
  | _, _, Quiver.Path.nil => LinearMap.id
  | _, _, Quiver.Path.cons p g => arrowCompose X f g ∘ₗ pathCompose X f p

namespace Rep
variable {Γ : RationalQuiver K L}

def pathMap (M : Rep Γ) {a b : Γ.V} (p : Quiver.Path a b) : M.M a →ₗ[L] M.M b :=
  pathCompose (Q := Γ.toRQuiver) M.M M.φEdge p

/-- Nilpotent: all paths of length `≥ n` act by `0`, for some `n`. -/
def IsNilpotent (M : Rep Γ) : Prop :=
  ∃ n : ℕ, ∀ (a b : Γ.V) (p : Quiver.Path a b), n ≤ p.length →
    pathCompose (Q := Γ.toRQuiver) M.M M.φEdge p = 0

end Rep
end RationalQuiver
end RQStatement
end RepSec

/-! ## The target `Rep^nil(Γ_E)` (from `RQStatement.Gelfand.Target`) -/

namespace RQStatement.Gelfand
open RQStatement.HC CategoryTheory
variable {E : Type} [Field E] [CharZero E]

/-- `Γ_E`: the cyclic quiver (`ℓ = 0`) resp. the Gelfand quiver (`ℓ ≥ 1`), on which `σ ∈ G_E`
acts trivially if `χ_E(σ) = 1` and by the `±`-swap if `χ_E(σ) = -1`. -/
noncomputable def GammaE (D : ImagUnit E) : ℕ → RationalQuiver E D.L
  | 0 => RationalQuiver.cyclicOfSign E D.L D.chiHom
  | _ + 1 => RationalQuiver.gelfandOfSign E D.L D.chiHom

variable (D : ImagUnit E)

/-- The relation `a₋b₋ = a₊b₊`. -/
def SatisfiesGelfandRelationE (M : RationalQuiver.Rep (RationalQuiver.gelfandOfSign E D.L D.chiHom)) :
    Prop :=
  M.pathMap (a := (1 : Fin 3)) (b := (1 : Fin 3)) RQuiver.pathMinus
    = M.pathMap (a := (1 : Fin 3)) (b := (1 : Fin 3)) RQuiver.pathPlus

/-- `Rep^nil(Γ_E)`: finite-dimensional nilpotent representations of `Γ_E`, satisfying
`a₋b₋ = a₊b₊` when `ℓ ≥ 1`. -/
def RepNilTarget : (ℓ : ℕ) → ObjectProperty (RationalQuiver.FDRep (GammaE D ℓ))
  | 0 => fun M => M.toRep.IsNilpotent
  | _ + 1 => fun M => M.toRep.IsNilpotent ∧ SatisfiesGelfandRelationE D M.toRep

end RQStatement.Gelfand

-- END STATEMENT DEFINITIONS
