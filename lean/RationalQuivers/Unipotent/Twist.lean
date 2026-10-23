import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import RationalQuivers.Unipotent.Nilpotent

/-!
# The `τ`-twist on `W_L = L ⊗_K W_K`

Support module for §4 of `latex/rational_quivers.tex` (stage **S6**).  It carries **no census
row**: it is the vocabulary in which §4's hypotheses are *stated*.

`prop:unipotentstabilization` equips `W_L = L ⊗_K W_K` with "the canonical semi-linear
`τ`-action" (clause `RQ2-4.01-H4`) and then writes `W_∓^τ` for the twist of a subspace and
`φ^τ = τ ∘ φ ∘ τ^{-1}` for the twist of a map (`census/NOTATION.md` §3: `α^σ = σ(α)`,
`φ^σ = σ ∘ φ ∘ σ^{-1}`).  This module is those three notions.

## Main definitions / results
* `RationalQuivers.Unipotent.galoisTwist` — the canonical semi-linear action
  `σ ⊗ id : L ⊗_K W_K → L ⊗_K W_K` (clause `RQ2-4.01-H4`).
* `RationalQuivers.Unipotent.twist` — `U^σ := σ(U)`, an `L`-subspace again.
* `RationalQuivers.Unipotent.twistConj` — `f ↦ f^σ = σ ∘ f ∘ σ^{-1}`, in the shape §4 uses it:
  it takes `f : U → V^σ` to `f^σ : U^σ → V` (using `V^{σσ} = V`).
* `RationalQuivers.Unipotent.semilinearConj` — conjugation of an `L`-linear endomorphism by an
  arbitrary semi-linear automorphism, the operation of clause `RQ2-4.05-C5`
  (`eq:semilinearconjugation`).
* `RationalQuivers.Unipotent.aut_mul_self` — in a quadratic Galois extension every element of
  `Gal(L/K)` is an involution; this is what makes `W^{ττ} = W` and hence lets `φ_-^τ ∘ φ_+` be an
  endomorphism of `W_+`, as `eq:nilpotency` requires.

## Implementation notes
The canonical action is *not* registered as a `DistribMulAction` instance here.  S0's
`Descent/KStructure.lean` already registers one for `L ⊗[K] V` (`galoisTensorAction`), and S6 is
by design independent of S0 (`workflow/PLAN.md` §S6: "no dependency on Stages 0–5 at all"), so
registering a second instance for the same type would create a competing instance in the audit
environment, which imports both.  Everything here is therefore a plain `def` applied explicitly.
See `workflow/stages/S6/DESIGN-NOTES.md` §2.
-/

universe u v w

open scoped TensorProduct

namespace RationalQuivers.Unipotent

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {WK : Type v} [AddCommGroup WK] [Module K WK]

/-! ## The canonical semi-linear action on `L ⊗_K W_K` -/

/-- The canonical semi-linear `σ`-action on `W_L = L ⊗_K W_K` (clause `RQ2-4.01-H4`):
`σ • (α ⊗ w) = σ(α) ⊗ w`.  It is `K`-linear and `σ`-semi-linear (`galoisTwist_smul`).

@census none
-/
def galoisTwist (σ : Gal(L/K)) : (L ⊗[K] WK) →ₗ[K] (L ⊗[K] WK) :=
  TensorProduct.map σ.toLinearMap LinearMap.id

@[simp]
theorem galoisTwist_tmul (σ : Gal(L/K)) (a : L) (w : WK) :
    galoisTwist (WK := WK) σ (a ⊗ₜ[K] w) = σ a ⊗ₜ[K] w := rfl

/-- The canonical action is `σ`-semi-linear: `σ(a · x) = σ(a) · σ(x)`. -/
theorem galoisTwist_smul (σ : Gal(L/K)) (a : L) (x : L ⊗[K] WK) :
    galoisTwist σ (a • x) = σ a • galoisTwist σ x := by
  induction x with
  | zero => simp
  | tmul b w =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, galoisTwist_tmul, galoisTwist_tmul,
        TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

@[simp]
theorem galoisTwist_one : galoisTwist (1 : Gal(L/K)) = (LinearMap.id : (L ⊗[K] WK) →ₗ[K] _) := by
  refine TensorProduct.ext' fun a w => ?_
  simp

theorem galoisTwist_mul (σ τ : Gal(L/K)) :
    galoisTwist (WK := WK) (σ * τ) = (galoisTwist σ).comp (galoisTwist τ) := by
  refine TensorProduct.ext' fun a w => ?_
  simp [galoisTwist_tmul]

/-- If `σ` is an involution of `L` then the canonical action is an involution of `W_L`. -/
theorem galoisTwist_galoisTwist {σ : Gal(L/K)} (hσ : σ * σ = 1) (x : L ⊗[K] WK) :
    galoisTwist σ (galoisTwist σ x) = x := by
  have := congrArg (fun f => (f : (L ⊗[K] WK) →ₗ[K] _) x) (galoisTwist_mul (WK := WK) σ σ)
  simp only [hσ, galoisTwist_one] at this
  simpa using this.symm

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

/-- An involution of `L` is its own inverse on scalars: `σ (σ c) = c`. -/
theorem aut_apply_aut {σ : Gal(L/K)} (hσ : σ * σ = 1) (c : L) : σ (σ c) = c := by
  have := congrArg (fun g => (g : Gal(L/K)) c) hσ
  simpa using this

/-- In a **quadratic** Galois extension every element of `Gal(L/K)` squares to the identity.

Clauses `RQ2-4.01-H1` (quadratic) and `RQ2-4.01-H3` (`τ` the non-trivial element) enter §4 only
through this fact and through the shape of `W_∓^τ`; note the conclusion needs no assumption
that `σ ≠ 1`.

@census none
-/
theorem aut_mul_self (hgal : IsGalois K L) (hquad : Module.finrank K L = 2) (σ : Gal(L/K)) :
    σ * σ = 1 := by
  letI := hgal
  haveI : FiniteDimensional K L := .of_finrank_eq_succ (n := 1) hquad
  have hcard : Nat.card Gal(L/K) = 2 := (IsGalois.card_aut_eq_finrank K L).trans hquad
  have h := pow_card_eq_one' (G := Gal(L/K)) (x := σ)
  rw [hcard, pow_two] at h
  exact h

/-! ## The twist of a subspace -/

/-- The twist `U^σ := σ(U)` of an `L`-subspace of `W_L` (the source's `W_∓^τ`,
clause `RQ2-4.01-H6`).  It is again an `L`-subspace because `σ` is semi-linear and surjective.

@census none
-/
def twist (σ : Gal(L/K)) (U : Submodule L (L ⊗[K] WK)) : Submodule L (L ⊗[K] WK) where
  carrier := galoisTwist σ '' U
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, U.add_mem hx hy, map_add _ _ _⟩
  zero_mem' := ⟨0, U.zero_mem, map_zero _⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    refine ⟨σ.symm c • x, U.smul_mem _ hx, ?_⟩
    rw [galoisTwist_smul]
    simp

theorem mem_twist {σ : Gal(L/K)} {U : Submodule L (L ⊗[K] WK)} {x : L ⊗[K] WK} :
    x ∈ twist σ U ↔ ∃ y ∈ U, galoisTwist σ y = x := Iff.rfl

theorem galoisTwist_mem_twist {σ : Gal(L/K)} {U : Submodule L (L ⊗[K] WK)} {x : L ⊗[K] WK}
    (hx : x ∈ U) : galoisTwist σ x ∈ twist σ U := ⟨x, hx, rfl⟩

theorem galoisTwist_mem_of_mem_twist {σ : Gal(L/K)} (hσ : σ * σ = 1)
    {U : Submodule L (L ⊗[K] WK)} {x : L ⊗[K] WK} (hx : x ∈ twist σ U) :
    galoisTwist σ x ∈ U := by
  obtain ⟨y, hy, rfl⟩ := hx
  rwa [galoisTwist_galoisTwist hσ]

/-- `(U^σ)^σ = U` for an involution `σ`. -/
theorem twist_twist {σ : Gal(L/K)} (hσ : σ * σ = 1) (U : Submodule L (L ⊗[K] WK)) :
    twist σ (twist σ U) = U := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact galoisTwist_mem_of_mem_twist hσ hy
  · intro hx
    exact ⟨galoisTwist σ x, galoisTwist_mem_twist hx, galoisTwist_galoisTwist hσ x⟩

@[simp]
theorem twist_top (σ : Gal(L/K)) : twist σ (⊤ : Submodule L (L ⊗[K] WK)) = ⊤ := by
  ext x
  exact ⟨fun _ => trivial, fun _ => ⟨galoisTwist σ⁻¹ x, trivial, galoisTwist_galoisTwist_inv σ x⟩⟩

/-! ## The twist of a map -/

/-- `Θ_σ` restricted to `U^σ → U`: the source's `σ^{-1} = σ` applied to a vector of `U^σ`.
It is additive and `σ`-semi-linear (`twistBack_add`, `twistBack_smul`).

@census none
-/
def twistBack {σ : Gal(L/K)} (hσ : σ * σ = 1) {U : Submodule L (L ⊗[K] WK)} (x : twist σ U) : U :=
  ⟨galoisTwist σ (x : L ⊗[K] WK), galoisTwist_mem_of_mem_twist hσ x.2⟩

@[simp]
theorem twistBack_coe {σ : Gal(L/K)} (hσ : σ * σ = 1) {U : Submodule L (L ⊗[K] WK)}
    (x : twist σ U) : ((twistBack hσ x : U) : L ⊗[K] WK) = galoisTwist σ (x : L ⊗[K] WK) := rfl

theorem twistBack_add {σ : Gal(L/K)} (hσ : σ * σ = 1) {U : Submodule L (L ⊗[K] WK)}
    (x y : twist σ U) : twistBack hσ (x + y) = twistBack hσ x + twistBack hσ y :=
  Subtype.ext (map_add _ _ _)

theorem twistBack_smul {σ : Gal(L/K)} (hσ : σ * σ = 1) {U : Submodule L (L ⊗[K] WK)}
    (c : L) (x : twist σ U) : twistBack hσ (c • x) = σ c • twistBack hσ x :=
  Subtype.ext (galoisTwist_smul _ _ _)

/-- The twist `f^σ = σ ∘ f ∘ σ^{-1}` of an `L`-linear map, in the shape §4 uses it: for
`f : U → V^σ` it is a map `U^σ → V`, using `(V^σ)^σ = V`.

With `f = φ_-` this is the source's `φ_-^τ : W_-^τ → W_+` of `eq:nilpotency`
(`census/NOTATION.md` §3: `φ^σ := σ ∘ φ ∘ σ^{-1}`).

@census none
-/
def twistConj {σ : Gal(L/K)} (hσ : σ * σ = 1) {U V : Submodule L (L ⊗[K] WK)}
    (f : U →ₗ[L] twist σ V) : twist σ U →ₗ[L] V where
  toFun x := twistBack hσ (f (twistBack hσ x))
  map_add' x y := by rw [twistBack_add, map_add, twistBack_add]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [twistBack_smul, map_smul, twistBack_smul, aut_apply_aut hσ]

@[simp]
theorem twistConj_apply {σ : Gal(L/K)} (hσ : σ * σ = 1) {U V : Submodule L (L ⊗[K] WK)}
    (f : U →ₗ[L] twist σ V) (x : twist σ U) :
    twistConj hσ f x = twistBack hσ (f (twistBack hσ x)) := rfl

/-- `Θ_σ` as a map `U → U^σ`: the inverse of `twistBack`.

@census none
-/
def twistFwd (σ : Gal(L/K)) {U : Submodule L (L ⊗[K] WK)} (x : U) : twist σ U :=
  ⟨galoisTwist σ (x : L ⊗[K] WK), galoisTwist_mem_twist x.2⟩

@[simp]
theorem twistFwd_coe (σ : Gal(L/K)) {U : Submodule L (L ⊗[K] WK)} (x : U) :
    ((twistFwd σ x : twist σ U) : L ⊗[K] WK) = galoisTwist σ (x : L ⊗[K] WK) := rfl

@[simp]
theorem twistBack_twistFwd {σ : Gal(L/K)} (hσ : σ * σ = 1) {U : Submodule L (L ⊗[K] WK)}
    (x : U) : twistBack hσ (twistFwd σ x) = x :=
  Subtype.ext (by simp [twistBack, galoisTwist_galoisTwist hσ])

@[simp]
theorem twistFwd_twistBack {σ : Gal(L/K)} (hσ : σ * σ = 1) {U : Submodule L (L ⊗[K] WK)}
    (x : twist σ U) : twistFwd σ (twistBack hσ x) = x :=
  Subtype.ext (by simp [twistBack, galoisTwist_galoisTwist hσ])

/-- The conjugation `g ↦ g^σ` in the *other* direction: from `V^σ → U` to `V → U^σ`.

Together with `twistConj` it says that conjugation by `σ` is a bijection between the two shapes
of map §4.1 uses, and it is what makes `twistConj` invertibility-preserving
(`twistConj_twistConjInv`).

@census none
-/
def twistConjInv {σ : Gal(L/K)} (hσ : σ * σ = 1) {U V : Submodule L (L ⊗[K] WK)}
    (g : twist σ V →ₗ[L] U) : V →ₗ[L] twist σ U where
  toFun y := twistFwd σ (g (twistFwd σ y))
  map_add' x y := by
    have h : twistFwd σ (x + y) = twistFwd σ x + twistFwd σ y := Subtype.ext (by simp)
    rw [h, map_add]
    exact Subtype.ext (by simp)
  map_smul' c x := by
    have h : twistFwd σ (c • x) = σ c • twistFwd σ x :=
      Subtype.ext (by simp [galoisTwist_smul])
    simp only [RingHom.id_apply, h, map_smul]
    exact Subtype.ext (by simp [galoisTwist_smul, aut_apply_aut hσ])

@[simp]
theorem twistConjInv_apply {σ : Gal(L/K)} (hσ : σ * σ = 1) {U V : Submodule L (L ⊗[K] WK)}
    (g : twist σ V →ₗ[L] U) (y : V) :
    twistConjInv hσ g y = twistFwd σ (g (twistFwd σ y)) := rfl

/-- Conjugating twice returns the map: `twistConj` and `twistConjInv` are mutually inverse. -/
@[simp]
theorem twistConj_twistConjInv {σ : Gal(L/K)} (hσ : σ * σ = 1)
    {U V : Submodule L (L ⊗[K] WK)} (g : twist σ V →ₗ[L] U) :
    twistConj hσ (twistConjInv hσ g) = g := by
  ext x
  simp [twistConj, twistConjInv]

@[simp]
theorem twistConjInv_twistConj {σ : Gal(L/K)} (hσ : σ * σ = 1)
    {U V : Submodule L (L ⊗[K] WK)} (f : U →ₗ[L] twist σ V) :
    twistConjInv hσ (twistConj hσ f) = f := by
  ext x
  simp [twistConj, twistConjInv]

/-! ### `twistConj` is additive and `σ`-semi-linear -/

theorem twistConj_add {σ : Gal(L/K)} (hσ : σ * σ = 1) {U V : Submodule L (L ⊗[K] WK)}
    (f g : U →ₗ[L] twist σ V) :
    twistConj hσ (f + g) = twistConj hσ f + twistConj hσ g := by
  ext x
  simp [twistConj, twistBack]

theorem twistConj_smul {σ : Gal(L/K)} (hσ : σ * σ = 1) {U V : Submodule L (L ⊗[K] WK)}
    (c : L) (f : U →ₗ[L] twist σ V) :
    twistConj hσ (c • f) = σ c • twistConj hσ f := by
  ext x
  simp [twistConj, twistBack, galoisTwist_smul]

theorem twistConj_zero {σ : Gal(L/K)} (hσ : σ * σ = 1) {U V : Submodule L (L ⊗[K] WK)} :
    twistConj hσ (0 : U →ₗ[L] twist σ V) = 0 := by
  ext x
  simp [twistConj, twistBack]

/-! ### Conjugation preserves composition and inverses -/

theorem twistConjInv_comp_twistConj {σ : Gal(L/K)} (hσ : σ * σ = 1)
    {U V : Submodule L (L ⊗[K] WK)} (f : U →ₗ[L] twist σ V) (g : twist σ V →ₗ[L] U)
    (h : g.comp f = LinearMap.id) :
    (twistConjInv hσ g).comp (twistConj hσ f) = LinearMap.id := by
  ext x
  have hx : g (f (twistBack hσ x)) = twistBack hσ x := by
    have := congrArg (fun m => (m : U →ₗ[L] U) (twistBack hσ x)) h
    simpa using this
  simp [twistConj, twistConjInv, hx]

theorem twistConj_comp_twistConjInv {σ : Gal(L/K)} (hσ : σ * σ = 1)
    {U V : Submodule L (L ⊗[K] WK)} (f : U →ₗ[L] twist σ V) (g : twist σ V →ₗ[L] U)
    (h : f.comp g = LinearMap.id) :
    (twistConj hσ f).comp (twistConjInv hσ g) = LinearMap.id := by
  ext x
  have hx : f (g (twistFwd σ x)) = twistFwd σ x := by
    have := congrArg (fun m => (m : twist σ V →ₗ[L] twist σ V) (twistFwd σ x)) h
    simpa using this
  simp [twistConj, twistConjInv, hx]

/-- **The conjugation-inverse exchange.**  `(f^σ)^{-1}` conjugated back is `f^{-1}`.

This is what makes the two components of `stabilizationSeq` the *same* recursion, and hence what
turns `cor:unipotentstabilization` into a statement about a single pair `(F, H)` of mutually
composable maps.

@census none
-/
theorem twistConj_linInv_twistConj {σ : Gal(L/K)} (hσ : σ * σ = 1)
    {U V : Submodule L (L ⊗[K] WK)} (f : U →ₗ[L] twist σ V) (hf : HasInverse f) :
    twistConj hσ (linInv (twistConj hσ f)) = linInv f := by
  obtain ⟨g, hgf, hfg⟩ := hf
  have h1 : linInv f = g := linInv_eq_of hgf hfg
  have h2 : linInv (twistConj hσ f) = twistConjInv hσ g :=
    linInv_eq_of (twistConjInv_comp_twistConj hσ f g hgf) (twistConj_comp_twistConjInv hσ f g hfg)
  rw [h1, h2, twistConj_twistConjInv]

/-- Conjugation preserves invertibility. -/
theorem HasInverse.twistConj {σ : Gal(L/K)} (hσ : σ * σ = 1)
    {U V : Submodule L (L ⊗[K] WK)} {f : U →ₗ[L] twist σ V} (hf : HasInverse f) :
    HasInverse (twistConj hσ f) := by
  obtain ⟨g, hgf, hfg⟩ := hf
  exact ⟨twistConjInv hσ g, twistConjInv_comp_twistConj hσ f g hgf,
    twistConj_comp_twistConjInv hσ f g hfg⟩

/-- Conjugation reflects invertibility. -/
theorem hasInverse_of_twistConj {σ : Gal(L/K)} (hσ : σ * σ = 1)
    {U V : Submodule L (L ⊗[K] WK)} {f : U →ₗ[L] twist σ V}
    (hf : HasInverse (twistConj hσ f)) : HasInverse f := by
  obtain ⟨g, hgf, hfg⟩ := hf
  refine ⟨twistConj hσ g, LinearMap.ext fun x => ?_, LinearMap.ext fun w => ?_⟩
  · have hx : g (twistBack hσ (f (twistBack hσ (twistFwd σ x)))) = twistFwd σ x :=
      comp_eq_id_apply hgf (twistFwd σ x)
    rw [twistBack_twistFwd hσ] at hx
    show twistBack hσ (g (twistBack hσ (f x))) = x
    rw [hx, twistBack_twistFwd hσ]
  · have hy : twistBack hσ (f (twistBack hσ (g (twistBack hσ w)))) = twistBack hσ w :=
      comp_eq_id_apply hfg (twistBack hσ w)
    show f (twistBack hσ (g (twistBack hσ w))) = w
    have := congrArg (fun z => twistFwd σ z) hy
    simpa [twistFwd_twistBack hσ] using this

/-- If `φ_+ ∘ φ_-^τ = 1` then `φ_+^τ ∘ φ_- = 1`: the two readings of `eq:conjugateinverse`
(one for each sign) are equivalent, because conjugation by `τ` exchanges them. -/
theorem twistConj_comp_eq_id {σ : Gal(L/K)} (hσ : σ * σ = 1)
    {U V : Submodule L (L ⊗[K] WK)} (F : U →ₗ[L] twist σ V) (G : V →ₗ[L] twist σ U)
    (h : F.comp (twistConj hσ G) = LinearMap.id) :
    (twistConj hσ F).comp G = LinearMap.id := by
  refine LinearMap.ext fun y => ?_
  have hy : F (twistConj hσ G (twistFwd σ y)) = twistFwd σ y :=
    comp_eq_id_apply h (twistFwd σ y)
  have hy' : F (twistBack hσ (G y)) = twistFwd σ y := by
    rw [show twistConj hσ G (twistFwd σ y) = twistBack hσ (G y) by
      show twistBack hσ (G (twistBack hσ (twistFwd σ y))) = twistBack hσ (G y)
      rw [twistBack_twistFwd hσ]] at hy
    exact hy
  show twistBack hσ (F (twistBack hσ (G y))) = y
  rw [hy', twistBack_twistFwd hσ]

/-! ## Conjugation by an arbitrary semi-linear automorphism -/

section SemilinearConj

variable {W : Type w} [AddCommGroup W] [Module L W]

/-- Conjugation `φ ↦ ψ ∘ φ ∘ ψ^{-1}` of an `L`-linear endomorphism by a `σ`-semi-linear additive
automorphism `ψ`; the result is again `L`-linear.  This is the operation of clause
`RQ2-4.05-C5` (`eq:semilinearconjugation`).

@census none
-/
def semilinearConj (σ : Gal(L/K)) (ψ : W ≃+ W)
    (hψ : ∀ (a : L) (x : W), ψ (a • x) = σ a • ψ x) (φ : Module.End L W) : Module.End L W where
  toFun x := ψ (φ (ψ.symm x))
  map_add' x y := by simp
  map_smul' c x := by
    have hsymm : ψ.symm (c • x) = σ.symm c • ψ.symm x := by
      apply ψ.injective
      rw [hψ]
      simp
    simp only [hsymm, map_smul, RingHom.id_apply, hψ]
    simp

@[simp]
theorem semilinearConj_apply (σ : Gal(L/K)) (ψ : W ≃+ W)
    (hψ : ∀ (a : L) (x : W), ψ (a • x) = σ a • ψ x) (φ : Module.End L W) (x : W) :
    semilinearConj σ ψ hψ φ x = ψ (φ (ψ.symm x)) := rfl

variable {σ : Gal(L/K)} {ψ : W ≃+ W} {hψ : ∀ (a : L) (x : W), ψ (a • x) = σ a • ψ x}

theorem semilinearConj_symm_smul (hψ' : ∀ (a : L) (x : W), ψ (a • x) = σ a • ψ x) (a : L)
    (x : W) : ψ.symm (a • x) = σ.symm a • ψ.symm x := by
  apply ψ.injective
  rw [hψ']
  simp

@[simp]
theorem semilinearConj_one : semilinearConj σ ψ hψ 1 = 1 := by
  ext x; simp

@[simp]
theorem semilinearConj_mul (a b : Module.End L W) :
    semilinearConj σ ψ hψ (a * b) = semilinearConj σ ψ hψ a * semilinearConj σ ψ hψ b := by
  ext x; simp

@[simp]
theorem semilinearConj_add (a b : Module.End L W) :
    semilinearConj σ ψ hψ (a + b) = semilinearConj σ ψ hψ a + semilinearConj σ ψ hψ b := by
  ext x; simp

@[simp]
theorem semilinearConj_sub (a b : Module.End L W) :
    semilinearConj σ ψ hψ (a - b) = semilinearConj σ ψ hψ a - semilinearConj σ ψ hψ b := by
  ext x; simp

theorem semilinearConj_pow (a : Module.End L W) (n : ℕ) :
    semilinearConj σ ψ hψ (a ^ n) = (semilinearConj σ ψ hψ a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, semilinearConj_mul, ih]

@[simp]
theorem semilinearConj_zero : semilinearConj σ ψ hψ 0 = 0 := by
  ext x; simp

theorem semilinearConj_smul (c : L) (a : Module.End L W) :
    semilinearConj σ ψ hψ (c • a) = σ c • semilinearConj σ ψ hψ a := by
  ext x
  simp only [semilinearConj_apply, LinearMap.smul_apply, hψ]

/-- Conjugation preserves nilpotency (with the same exponent). -/
theorem semilinearConj_isNilpotent {a : Module.End L W} (h : IsNilpotent a) :
    IsNilpotent (semilinearConj σ ψ hψ a) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [← semilinearConj_pow, hn, semilinearConj_zero]⟩

/-- Conjugation preserves units. -/
theorem semilinearConj_isUnit {a : Module.End L W} (h : IsUnit a) :
    IsUnit (semilinearConj σ ψ hψ a) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨⟨semilinearConj σ ψ hψ (u : Module.End L W),
    semilinearConj σ ψ hψ ((u⁻¹ : (Module.End L W)ˣ) : Module.End L W), ?_, ?_⟩, rfl⟩
  · rw [← semilinearConj_mul, u.mul_inv, semilinearConj_one]
  · rw [← semilinearConj_mul, u.inv_mul, semilinearConj_one]

/-- Conjugation commutes with `Ring.inverse` on units. -/
theorem semilinearConj_inverse {a : Module.End L W} (h : IsUnit a) :
    semilinearConj σ ψ hψ (Ring.inverse a) = Ring.inverse (semilinearConj σ ψ hψ a) := by
  have h1 : a * Ring.inverse a = 1 := Ring.mul_inverse_cancel a h
  have h2 : Ring.inverse a * a = 1 := Ring.inverse_mul_cancel a h
  have hu : IsUnit (semilinearConj σ ψ hψ a) := semilinearConj_isUnit h
  have e1 : semilinearConj σ ψ hψ a * semilinearConj σ ψ hψ (Ring.inverse a) = 1 := by
    rw [← semilinearConj_mul, h1, semilinearConj_one]
  calc semilinearConj σ ψ hψ (Ring.inverse a)
      = Ring.inverse (semilinearConj σ ψ hψ a) *
          (semilinearConj σ ψ hψ a * semilinearConj σ ψ hψ (Ring.inverse a)) := by
        rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
    _ = Ring.inverse (semilinearConj σ ψ hψ a) := by rw [e1, mul_one]

/-- A field automorphism fixes `½`. -/
theorem aut_half (h2 : (2 : L) ≠ 0) (σ : Gal(L/K)) : σ (half h2) = half h2 := by
  rw [half_eq, map_inv₀, map_ofNat]

end SemilinearConj

/-- The canonical semi-linear action of `σ` on `W_L = L ⊗_K W_K`, packaged as an additive
automorphism, so that it can be fed to `semilinearConj`.  This is the `ψ` of
`eq:squarerootgaloisequivariance` (clause `RQ2-4.09-C2`).

@census none
-/
def galoisTwistEquiv (σ : Gal(L/K)) : (L ⊗[K] WK) ≃+ (L ⊗[K] WK) where
  toFun := galoisTwist σ
  invFun := galoisTwist σ⁻¹
  left_inv := galoisTwist_inv_galoisTwist σ
  right_inv := galoisTwist_galoisTwist_inv σ
  map_add' _ _ := map_add _ _ _

@[simp]
theorem galoisTwistEquiv_apply (σ : Gal(L/K)) (x : L ⊗[K] WK) :
    galoisTwistEquiv σ x = galoisTwist σ x := rfl

theorem galoisTwistEquiv_smul (σ : Gal(L/K)) (a : L) (x : L ⊗[K] WK) :
    galoisTwistEquiv σ (a • x) = σ a • galoisTwistEquiv σ x := galoisTwist_smul σ a x

end RationalQuivers.Unipotent
