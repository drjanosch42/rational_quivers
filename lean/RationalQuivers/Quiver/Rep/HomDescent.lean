import RationalQuivers.Quiver.Rep.TowerDescent
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Base change for `Hom`: Hom-descent for rational quiver representations

Formalizes §1.4 of `latex/rational_quivers.tex`, Proposition `prop:homdescent`
(census `RQ2-1.12`).

## Main definitions / results
* `RationalQuivers.RationalQuiver.Rep.classicalHom` — `W := Hom_Γ(M,N)`, the `L`-vector space of
  homomorphisms of the underlying **classical** quiver representations.
* `RationalQuivers.RationalQuiver.Rep.homGaloisMap` — the semi-linear `Gal(L/K)`-action
  `(ψ^σ)_v := φ^N_{σ⁻¹v,σ} ∘ ψ_{σ⁻¹v} ∘ (φ^M_{σ⁻¹v,σ})⁻¹` of the source's proof.
* `RationalQuivers.RationalQuiver.Rep.homVecK` — `W` as an object of S0's `Descent.VecK K L`,
  i.e. an `L`-vector space with a `K`-structure.  Its continuity field is clause `RQ2-1.12-H4`.
* `RationalQuivers.RationalQuiver.Rep.homModule` — `Hom_{Γ_K}(M_K,N_K) = W^{Gal(L/K)}`, a
  `K`-vector space, together with `Rep.homEquiv` identifying it with `Rep.Hom` (census `RQ2-1.09`).
* `RationalQuivers.RationalQuiver.Rep.hom_baseChange_iso` — **Proposition `prop:homdescent`**
  (census `RQ2-1.12`).

## Implementation notes

**The source's proof, and the shape it dictates.**  The source first treats `E' = L`: it puts the
semi-linear action `ψ ↦ ψ^σ` on `W = Hom_Γ(M,N)`, checks that it is continuous (using
finite-dimensionality of `M_K`, `N_K` and continuity of their actions — clause `RQ2-1.12-H4`),
identifies `Hom_{Γ_K}(M_K,N_K) = W^{Gal(L/K)}`, and invokes Galois descent
(`thm:galoisdescent`, census `RQ2-1.13`) for the canonical map `L ⊗_K W^G → W`.  The general
intermediate `E'` follows because `Hom_{Γ_{E'}}(M_{E'},N_{E'}) = W^{Gal(L/E')}` and descent applies
again over `E'`.  We therefore package `W` as an object of S0's `Descent.VecK K L` — the category
`thm:galoisdescent` is *about* — so that S0's `descentCounit_bijective` is directly available;
`Descent.fixedPoints K L (homVecK M N)` is then literally `W^{Gal(L/K)}` as a `K`-vector space.

**Where the `K`-vector space structure on `W` comes from.**  `W` is an `L`-vector space; its
`K`-structure is `Module.compHom` along `K → L`, supplied as the `isModuleK` **field** of the
`Descent.VecK` object, never as a global instance (S0, `Descent/KStructure.lean` implementation
notes: carrying it as a field is what avoids scalar-action diamonds).  This is why `Rep` itself
needs no `Module K` field: the paper's `M(v)` really are only `L`-vector spaces
(clause `RQ2-1.08-C1`), and nothing here asks them to be more.

**`Hom_{Γ_K}` is `Rep.Hom`.**  `homModule` is defined as the fixed-point space `W^{Gal(L/K)}`;
`Rep.mem_homModule_iff` and `Rep.homEquiv` prove that this is exactly the set of homomorphisms of
`def:rationalrepresentationhom` (census `RQ2-1.09`), which is what makes the left-hand side of
`prop:homdescent` the paper's `Hom_{Γ_K}(M_K,N_K)` and not a differently-defined space.
-/

universe u

namespace RationalQuivers

namespace RationalQuiver

open CategoryTheory
open scoped TensorProduct

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

namespace Rep

variable {Γ : RationalQuiver K L}

/-- `W := Hom_Γ(M,N)`, the `L`-vector space of homomorphisms of the underlying **classical**
quiver representations of `M` and `N` over `L`: families `(ψ_v : M(v) → N(v))_v` of `L`-linear
maps with `ψ_{t(e)} ∘ φ^M_e = φ^N_e ∘ ψ_{s(e)}` for every edge `e`.

@census none (helper: the space `W` of the source's proof of `prop:homdescent`)
-/
def classicalHom (M N : Rep Γ) : Submodule L (∀ v : Γ.V, M.M v →ₗ[L] N.M v) where
  carrier := {ψ | ∀ (e : Γ.E) (m : M.M (Γ.toRQuiver.source e)),
      ψ (Γ.toRQuiver.target e) (M.φEdge e m) = N.φEdge e (ψ (Γ.toRQuiver.source e) m)}
  add_mem' {ψ χ} hψ hχ e m := by
    simp only [Pi.add_apply, LinearMap.add_apply, hψ e m, hχ e m, map_add]
  zero_mem' e m := by simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero]
  smul_mem' a ψ hψ e m := by
    simp only [Pi.smul_apply, LinearMap.smul_apply, hψ e m, map_smul]

/-- Membership in `W = Hom_Γ(M,N)` unfolded.  @census none (helper) -/
@[simp]
theorem mem_classicalHom {M N : Rep Γ} {ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v} :
    ψ ∈ classicalHom M N ↔ ∀ (e : Γ.E) (m : M.M (Γ.toRQuiver.source e)),
      ψ (Γ.toRQuiver.target e) (M.φEdge e m) = N.φEdge e (ψ (Γ.toRQuiver.source e) m) :=
  Iff.rfl

/-! ### The semi-linear `Gal(L/K)`-action on `W` -/

/-- The underlying function of the semi-linear action of the source's proof of
`prop:homdescent`,

`(ψ^σ)_v := φ^N_{σ⁻¹v,σ} ∘ ψ_{σ⁻¹v} ∘ (φ^M_{σ⁻¹v,σ})⁻¹`.

The inverse `(φ^M_{σ⁻¹v,σ})⁻¹ : M(v) → M(σ⁻¹v)` is written here as `φ^M_{v,σ⁻¹}`, which is the
same map: `φ^M_{σ⁻¹v,σ} ∘ φ^M_{v,σ⁻¹} = φ^M_{v,σσ⁻¹} = φ^M_{v,1} = id` by the cocycle condition
(`Rep.φ'_inv`).  Writing it that way keeps the definition free of `AddEquiv.symm`.

@census none (helper)
-/
def homGaloisFun (M N : Rep Γ) (σ : Gal(L/K)) (ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v) (v : Γ.V) :
    M.M v → N.M v :=
  fun m => N.φ' σ (smul_inv_smul σ v) (ψ (σ⁻¹ • v) (M.φ σ⁻¹ v m))

/-- `ψ^σ` computed through any presentation of the vertex `σ⁻¹ v`.  Every later computation goes
through this, so that no `subst` bookkeeping is needed twice.

@census none (helper)
-/
theorem homGaloisFun_eq (M N : Rep Γ) (σ : Gal(L/K)) (ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v)
    {v w : Γ.V} (h : σ • w = v) (h' : σ⁻¹ • v = w) (m : M.M v) :
    homGaloisFun M N σ ψ v m = N.φ' σ h (ψ w (M.φ' σ⁻¹ h' m)) := by
  subst h'; rfl

/-- `ψ^σ` is additive: every map in the composite is.

@census none (helper)
-/
theorem homGaloisFun_map_add (M N : Rep Γ) (σ : Gal(L/K))
    (ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v) (v : Γ.V) (m m' : M.M v) :
    homGaloisFun M N σ ψ v (m + m') = homGaloisFun M N σ ψ v m + homGaloisFun M N σ ψ v m' := by
  simp only [homGaloisFun, map_add]

/-- `ψ^σ` is `L`-**linear**: the `σ⁻¹`-semi-linearity of `φ^M_{v,σ⁻¹}` and the
`σ`-semi-linearity of `φ^N_{σ⁻¹v,σ}` cancel.  This is the computation the source spells out in
the proof of `prop:homdescent`.

@census none (helper)
-/
theorem homGaloisFun_map_smul (M N : Rep Γ) (σ : Gal(L/K))
    (ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v) (v : Γ.V) (a : L) (m : M.M v) :
    homGaloisFun M N σ ψ v (a • m) = a • homGaloisFun M N σ ψ v m := by
  show N.φ' σ (smul_inv_smul σ v) (ψ (σ⁻¹ • v) (M.φ σ⁻¹ v (a • m)))
      = a • N.φ' σ (smul_inv_smul σ v) (ψ (σ⁻¹ • v) (M.φ σ⁻¹ v m))
  rw [M.semilinear σ⁻¹ v a m, map_smul, N.φ'_smul, apply_inv_apply]

/-- `(ψ^σ)_v : M(v) → N(v)` as an `L`-linear map.

@census none (helper)
-/
def homGaloisMap (M N : Rep Γ) (σ : Gal(L/K)) (ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v) (v : Γ.V) :
    M.M v →ₗ[L] N.M v where
  toFun := homGaloisFun M N σ ψ v
  map_add' := homGaloisFun_map_add M N σ ψ v
  map_smul' a m := homGaloisFun_map_smul M N σ ψ v a m

/-- The defining edge condition of `W`, transported to named endpoints.

@census none (helper)
-/
theorem φEdge'_of_mem {M N : Rep Γ} {ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v}
    (hψ : ψ ∈ classicalHom M N) (f : Γ.E) {a b : Γ.V}
    (ha : Γ.toRQuiver.source f = a) (hb : Γ.toRQuiver.target f = b) (x : M.M a) :
    ψ b (M.φEdge' f ha hb x) = N.φEdge' f ha hb (ψ a x) := by
  subst ha; subst hb; exact hψ f x

/-- `ψ^σ` again respects the edge relations, i.e. `W` is stable under the action.  This is the
step the source records as "one can verify that `ψ^σ` respects the edge relations".

@census none (helper)
-/
theorem homGaloisMap_mem (M N : Rep Γ) (σ : Gal(L/K))
    {ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v} (hψ : ψ ∈ classicalHom M N) :
    (fun v => homGaloisMap M N σ ψ v) ∈ classicalHom M N := by
  haveI := Γ.galois
  intro e m
  have hs : Γ.toRQuiver.source (σ⁻¹ • e) = σ⁻¹ • Γ.toRQuiver.source e := Γ.source_smul σ⁻¹ e
  have ht : Γ.toRQuiver.target (σ⁻¹ • e) = σ⁻¹ • Γ.toRQuiver.target e := Γ.target_smul σ⁻¹ e
  -- (1) push `φ^M_{·,σ⁻¹}` through `M`'s edge map
  have step1 : M.φEdge' (σ⁻¹ • e) hs ht (M.φ σ⁻¹ (Γ.toRQuiver.source e) m)
      = M.φ σ⁻¹ (Γ.toRQuiver.target e) (M.φEdge e m) :=
    M.φEdge'_φ' σ⁻¹ rfl rfl rfl hs ht rfl rfl m
  -- (2) `ψ` commutes with the edge map of the edge `σ⁻¹ e`
  have step2 := φEdge'_of_mem hψ (σ⁻¹ • e) hs ht (M.φ σ⁻¹ (Γ.toRQuiver.source e) m)
  -- (3) push `φ^N_{·,σ}` back through `N`'s edge map
  have step3 := N.φEdge'_φ' σ (smul_inv_smul σ e) hs ht rfl rfl
    (smul_inv_smul σ (Γ.toRQuiver.source e)) (smul_inv_smul σ (Γ.toRQuiver.target e))
    (ψ (σ⁻¹ • Γ.toRQuiver.source e) (M.φ σ⁻¹ (Γ.toRQuiver.source e) m))
  show homGaloisFun M N σ ψ (Γ.toRQuiver.target e) (M.φEdge e m)
      = N.φEdge e (homGaloisFun M N σ ψ (Γ.toRQuiver.source e) m)
  show N.φ' σ (smul_inv_smul σ (Γ.toRQuiver.target e))
        (ψ (σ⁻¹ • Γ.toRQuiver.target e)
          (M.φ σ⁻¹ (Γ.toRQuiver.target e) (M.φEdge e m)))
      = N.φEdge e (N.φ' σ (smul_inv_smul σ (Γ.toRQuiver.source e))
          (ψ (σ⁻¹ • Γ.toRQuiver.source e) (M.φ σ⁻¹ (Γ.toRQuiver.source e) m)))
  rw [← step1, step2, ← step3]
  rfl

/-- The action `ψ ↦ ψ^σ` of `Gal(L/K)` on `W = Hom_Γ(M,N)`.

@census none (helper)
-/
instance homSMul (M N : Rep Γ) : SMul Gal(L/K) (classicalHom M N) where
  smul σ ψ := ⟨fun v => homGaloisMap M N σ ψ.1 v, homGaloisMap_mem M N σ ψ.2⟩

/-- The Galois action on `W`, in components.  @census none (helper) -/
@[simp]
theorem homSMul_coe (M N : Rep Γ) (σ : Gal(L/K)) (ψ : classicalHom M N) (v : Γ.V) :
    ((σ • ψ : classicalHom M N) : ∀ v : Γ.V, M.M v →ₗ[L] N.M v) v
      = homGaloisMap M N σ (ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v) v := rfl

/-- Two elements of `W` agree as soon as all their components do.  @census none (helper) -/
theorem classicalHom_ext {M N : Rep Γ} {ψ χ : classicalHom M N}
    (h : ∀ (v : Γ.V) (m : M.M v),
      (ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v) v m = (χ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v) v m) :
    ψ = χ :=
  Subtype.ext (funext fun v => LinearMap.ext (h v))

/-- `ψ^1 = ψ`.  @census none (helper) -/
theorem homSMul_one (M N : Rep Γ) (ψ : classicalHom M N) : (1 : Gal(L/K)) • ψ = ψ := by
  refine classicalHom_ext fun v m => ?_
  have h1 : (1 : Gal(L/K)) • v = v := one_smul _ v
  have h1' : (1 : Gal(L/K))⁻¹ • v = v := by rw [inv_one, one_smul]
  show homGaloisFun M N 1 _ v m = _
  rw [homGaloisFun_eq M N 1 _ h1 h1' m,
    M.φ'_congr (inv_one (G := Gal(L/K))) h1' h1 m, M.φ'_one, N.φ'_one]
  simp only [eqCast_natural]
  exact M.eqCast_rfl v m ▸ (N.eqCast_rfl v _)

/-- `ψ^{στ} = (ψ^τ)^σ`, from the cocycle condition `eq:semi-linearactiononrep`.

@census none (helper)
-/
theorem homSMul_mul (M N : Rep Γ) (σ τ : Gal(L/K)) (ψ : classicalHom M N) :
    (σ * τ) • ψ = σ • (τ • ψ) := by
  refine classicalHom_ext fun v m => ?_
  set u : Γ.V := (σ * τ)⁻¹ • v with hu
  have hτu : τ • u = τ • u := rfl
  have h₁ : σ • (τ • u) = v := by
    rw [← mul_smul, hu, smul_inv_smul]
  have h₁' : σ⁻¹ • v = τ • u := by rw [← h₁, inv_smul_smul]
  have h₂' : τ⁻¹ • (τ • u) = u := inv_smul_smul τ u
  have h₃ : (σ * τ) • u = v := by rw [hu, smul_inv_smul]
  have h₄ : (τ⁻¹ * σ⁻¹) • v = u := by rw [mul_smul, h₁', h₂']
  have h₅ : (σ * τ)⁻¹ • v = u := rfl
  show homGaloisFun M N (σ * τ) _ v m = homGaloisFun M N σ _ v m
  rw [homGaloisFun_eq M N (σ * τ) _ h₃ h₅ m, homGaloisFun_eq M N σ _ h₁ h₁' m]
  show _ = N.φ' σ h₁ (homGaloisFun M N τ _ (τ • u) (M.φ' σ⁻¹ h₁' m))
  rw [homGaloisFun_eq M N τ _ hτu h₂' (M.φ' σ⁻¹ h₁' m),
    N.φ'_comp σ τ hτu h₁ h₃, M.φ'_comp τ⁻¹ σ⁻¹ h₁' h₂' h₄,
    M.φ'_congr (mul_inv_rev σ τ).symm h₄ h₅ m]

/-- `0^σ = 0`.  @census none (helper) -/
theorem homSMul_zero (M N : Rep Γ) (σ : Gal(L/K)) :
    σ • (0 : classicalHom M N) = 0 := by
  refine classicalHom_ext fun v m => ?_
  show homGaloisFun M N σ _ v m = _
  simp [homGaloisFun]

/-- `(ψ + χ)^σ = ψ^σ + χ^σ`.  @census none (helper) -/
theorem homSMul_add (M N : Rep Γ) (σ : Gal(L/K)) (ψ χ : classicalHom M N) :
    σ • (ψ + χ) = σ • ψ + σ • χ := by
  refine classicalHom_ext fun v m => ?_
  show homGaloisFun M N σ _ v m = homGaloisFun M N σ _ v m + homGaloisFun M N σ _ v m
  simp only [homGaloisFun, Submodule.coe_add, Pi.add_apply, LinearMap.add_apply, map_add]

/-- `Gal(L/K)` acts on `W = Hom_Γ(M,N)` by additive automorphisms.

@census none (helper)
-/
instance homGaloisAction (M N : Rep Γ) : DistribMulAction Gal(L/K) (classicalHom M N) where
  one_smul := homSMul_one M N
  mul_smul := homSMul_mul M N
  smul_zero := homSMul_zero M N
  smul_add := homSMul_add M N

/-- The action of `Gal(L/K)` on `W` is **semi-linear**: `(a ψ)^σ = σ(a) ψ^σ`.

@census none (helper)
-/
theorem homIsSemilinearAction (M N : Rep Γ) :
    Descent.IsSemilinearAction K L (classicalHom M N) where
  smul_smul_semilinear σ a ψ := by
    refine classicalHom_ext fun v m => ?_
    show homGaloisFun M N σ _ v m = _
    show N.φ' σ (smul_inv_smul σ v) ((a • (ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v)) (σ⁻¹ • v)
        (M.φ σ⁻¹ v m)) = _
    rw [Pi.smul_apply, LinearMap.smul_apply, N.φ'_smul]
    rfl

/-- **Clause `RQ2-1.12-H4`**: the semi-linear `Gal(L/K)`-action on `W = Hom_Γ(M,N)` is
**continuous** for the discrete topology on `W`, i.e. `W` carries a `K`-structure.

The source verifies exactly this, and names finite-dimensionality of `M_K` and `N_K` and the
continuity of their actions as what it needs: `ψ` is determined by its values on finitely many
basis vectors, and all vertices, vectors and coefficients involved are fixed by a common open
subgroup of `Gal(L/K)`, so the stabilizer of `ψ` is open.  This is what licenses the appeal to
Galois descent.

The open subgroup is the (finite) intersection, over the finitely many vertices `v` and the
finitely many vectors `b` of a chosen `L`-basis of `M(v)`, of the stabilizers of the points
`(v,b)` of `⊔_v M(v)` and `(v, ψ_v b)` of `⊔_v N(v)` — each open by clause `RQ2-1.08-C6` for `M`
resp. `N`.  Note that S0's `homGaloisAction_isOpen_stabilizer` cannot be reused: it assumes a
`Gal(L/K)`-action on each of the two spaces separately, whereas here `Gal(L/K)` acts only on the
disjoint unions, not on an individual `M(v)`.

@census none (helper: clause `RQ2-1.12-H4`)
-/
theorem homKStructure (M N : FDRep Γ) :
    letI := homIsSemilinearAction M.toRep N.toRep
    Descent.KStructure K L (classicalHom M.toRep N.toRep) := by
  classical
  letI := homIsSemilinearAction M.toRep N.toRep
  refine { __ := homIsSemilinearAction M.toRep N.toRep, isOpen_stabilizer := fun ψ => ?_ }
  haveI : Fintype Γ.V := Fintype.ofFinite _
  set f : ∀ v : Γ.V, M.toRep.M v →ₗ[L] N.toRep.M v :=
    (ψ : ∀ v : Γ.V, M.toRep.M v →ₗ[L] N.toRep.M v) with hf
  set b : ∀ v : Γ.V, Module.Basis (Module.Free.ChooseBasisIndex L (M.toRep.M v)) L
      (M.toRep.M v) := fun v => Module.Free.chooseBasis L (M.toRep.M v) with hb
  set U : ((v : Γ.V) × Module.Free.ChooseBasisIndex L (M.toRep.M v)) →
      OpenSubgroup Gal(L/K) := fun j =>
    ⟨MulAction.stabilizer Gal(L/K) (M.toRep.tot j.1 (b j.1 j.2)),
      M.toRep.isOpen_stabilizer_total _⟩ ⊓
    ⟨MulAction.stabilizer Gal(L/K) (N.toRep.tot j.1 (f j.1 (b j.1 j.2))),
      N.toRep.isOpen_stabilizer_total _⟩ with hU
  refine Subgroup.isOpen_of_openSubgroup _ (U := Finset.univ.inf U) ?_
  intro σ hσ
  refine (MulAction.mem_stabilizer_iff).2 (Subtype.ext (funext fun v => (b v).ext fun i => ?_))
  have hj : σ ∈ U ⟨v, i⟩ :=
    (Finset.inf_le (Finset.mem_univ (⟨v, i⟩ :
      (v : Γ.V) × Module.Free.ChooseBasisIndex L (M.toRep.M v))) :
      Finset.univ.inf U ≤ U ⟨v, i⟩) hσ
  have hM1 : M.toRep.tot (σ • v) (M.toRep.φ σ v (b v i)) = M.toRep.tot v (b v i) := hj.1
  have hN1 : N.toRep.tot (σ • v) (N.toRep.φ σ v (f v (b v i)))
      = N.toRep.tot v (f v (b v i)) := hj.2
  have hv : σ • v = v := congrArg (fun x : M.toRep.Total => x.1) hM1
  have hv' : σ⁻¹ • v = v := inv_smul_eq_iff.2 hv.symm
  have hMb : M.toRep.φ' σ hv (b v i) = b v i := (M.toRep.tot_eq_iff hv _ _).1 hM1
  have hNb : N.toRep.φ' σ hv (f v (b v i)) = f v (b v i) := (N.toRep.tot_eq_iff hv _ _).1 hN1
  have hinv : M.toRep.φ' σ⁻¹ hv' (b v i) = b v i := by
    conv_lhs => rw [← hMb]
    exact M.toRep.φ'_inv σ hv hv' (b v i)
  show homGaloisFun M.toRep N.toRep σ f v (b v i) = f v (b v i)
  rw [homGaloisFun_eq M.toRep N.toRep σ f hv hv' (b v i), hinv, hNb]

/-- `W = Hom_Γ(M,N)` as an object of S0's category `Descent.VecK K L` of `L`-vector spaces with a
`K`-structure — the category `thm:galoisdescent` (census `RQ2-1.13`) is about.  The `K`-vector
space structure on `W` is `Module.compHom` along `K → L`, carried as a field.

@census none (helper)
-/
def homVecK (M N : FDRep Γ) : Descent.VecK K L :=
  letI : Module K (classicalHom M.toRep N.toRep) := Module.compHom _ (algebraMap K L)
  letI : IsScalarTower K L (classicalHom M.toRep N.toRep) := ⟨fun c a x => by
    show ((c • a) • x : classicalHom M.toRep N.toRep) = algebraMap K L c • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩
  { carrier := classicalHom M.toRep N.toRep
    isKStructure := homKStructure M N }

/-- `Hom_{Γ_K}(M_K,N_K) = W^{Gal(L/K)}`, the `K`-vector space of `K`-rational homomorphisms, as
the fixed-point space of S0's `Descent.fixedPoints`.

@census none (helper: the left-hand side of `RQ2-1.12-C1`)
-/
@[reducible]
def homModule (M N : FDRep Γ) : Submodule K (homVecK M N).carrier :=
  Descent.fixedPoints K L (homVecK M N)

/-- The underlying family `(ψ_v)_v` of `L`-linear maps of an element of `W = Hom_Γ(M,N)`.

@census none (helper)
-/
@[reducible]
def homFam (M N : FDRep Γ) (ψ : (homVecK M N).carrier) :
    ∀ v : Γ.V, M.toRep.M v →ₗ[L] N.toRep.M v :=
  Subtype.val (p := fun χ => χ ∈ classicalHom M.toRep N.toRep) ψ

/-- The rationality condition of `def:rationalrepresentationhom`, transported to a named target
vertex.

@census none (helper)
-/
theorem rational_φ' {M N : Rep Γ} {ψ : ∀ v : Γ.V, M.M v →ₗ[L] N.M v}
    (hr : ∀ (σ : Gal(L/K)) (v : Γ.V) (m : M.M v), ψ (σ • v) (M.φ σ v m) = N.φ σ v (ψ v m))
    (σ : Gal(L/K)) {v w : Γ.V} (h : σ • v = w) (m : M.M v) :
    ψ w (M.φ' σ h m) = N.φ' σ h (ψ v m) := by
  subst h; exact hr σ v m

/-- **The identification the source makes**: a classical homomorphism `ψ` is `Gal(L/K)`-invariant
for the action `ψ ↦ ψ^σ` **iff** it satisfies the rationality condition
`eq:koecheractiononrephom` of `def:rationalrepresentationhom` (census `RQ2-1.09`).  This is what
makes `homModule` the paper's `Hom_{Γ_K}(M_K,N_K)`.

@census none (helper)
-/
theorem mem_homModule_iff (M N : FDRep Γ) (ψ : (homVecK M N).carrier) :
    ψ ∈ homModule M N ↔
      ∀ (σ : Gal(L/K)) (v : Γ.V) (m : M.toRep.M v),
        homFam M N ψ (σ • v) (M.toRep.φ σ v m) = N.toRep.φ σ v (homFam M N ψ v m) := by
  rw [homModule, Descent.mem_fixedPoints]
  constructor
  · intro h σ v m
    have key : homGaloisFun M.toRep N.toRep σ (homFam M N ψ) (σ • v) (M.toRep.φ σ v m)
        = homFam M N ψ (σ • v) (M.toRep.φ σ v m) :=
      congrArg (fun χ : (homVecK M N).carrier =>
        homFam M N χ (σ • v) (M.toRep.φ σ v m)) (h σ)
    rw [homGaloisFun_eq M.toRep N.toRep σ (homFam M N ψ)
      (rfl : σ • v = σ • v) (inv_smul_smul σ v) (M.toRep.φ σ v m),
      show M.toRep.φ' σ⁻¹ (inv_smul_smul σ v) (M.toRep.φ σ v m) = m from
        M.toRep.φ'_inv σ rfl (inv_smul_smul σ v) m] at key
    exact key.symm
  · intro hr σ
    refine classicalHom_ext fun v m => ?_
    show homGaloisFun M.toRep N.toRep σ (homFam M N ψ) v m = homFam M N ψ v m
    rw [homGaloisFun_eq M.toRep N.toRep σ (homFam M N ψ) (smul_inv_smul σ v) rfl m,
      ← rational_φ' hr σ (smul_inv_smul σ v) (M.toRep.φ' σ⁻¹ rfl m),
      M.toRep.φ'_inv' σ (rfl : σ⁻¹ • v = σ⁻¹ • v) (smul_inv_smul σ v) m]

/-- `Hom_{Γ_K}(M_K,N_K)` in the sense of `def:rationalrepresentationhom` (census `RQ2-1.09`) is the
`K`-vector space `homModule`.

@census none (helper)
-/
def homEquiv (M N : FDRep Γ) : Rep.Hom M.toRep N.toRep ≃ homModule M N where
  toFun f := ⟨⟨f.ψ, f.edge⟩, (mem_homModule_iff M N ⟨f.ψ, f.edge⟩).2 f.rational⟩
  invFun ψ := ⟨homFam M N ψ.1, ψ.1.2, (mem_homModule_iff M N ψ.1).1 ψ.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### Consequences of Galois descent for the fixed-point space -/

/-- `W = Hom_Γ(M,N)` is a finite-dimensional `L`-vector space: `V` is finite and every `M(v)`,
`N(v)` is finite-dimensional (clause `RQ2-1.10-C1`).

@census none (helper: clause `RQ2-1.12-C3`)
-/
instance finiteDimensional_classicalHom (M N : FDRep Γ) :
    FiniteDimensional L (classicalHom M.toRep N.toRep) := by
  haveI : Fintype Γ.V := Fintype.ofFinite _
  infer_instance

/-! ### `prop:homdescent` -/

variable [IsGalois K L]

/-- Clause `RQ2-1.12-C3`, source side: `Hom_{Γ_K}(M_K,N_K)` is a **finite-dimensional** `K`-vector
space.

@census none (helper: clause `RQ2-1.12-C3`)
-/
theorem finiteDimensional_homModule (M N : FDRep Γ) :
    FiniteDimensional K (homModule M N) := by
  haveI : FiniteDimensional L (homVecK M N).carrier := finiteDimensional_classicalHom M N
  exact Descent.finiteDimensional_fixedPoints K (homVecK M N)

/-- Clause `RQ2-1.12-C3`, target side: `Hom_{Γ_{E'}}(M_{E'},N_{E'})` is a finite-dimensional
`E'`-vector space.

@census none (helper: clause `RQ2-1.12-C3`)
-/
theorem finiteDimensional_homModule_baseChange (M N : FDRep Γ)
    (E' : IntermediateField K L) [FiniteDimensional K E'] :
    FiniteDimensional E' (homModule (M.baseChange E') (N.baseChange E')) := by
  haveI := ((RationalQuiver.baseChange K L E').obj Γ).galois
  haveI : FiniteDimensional L (homVecK (M.baseChange E') (N.baseChange E')).carrier :=
    finiteDimensional_classicalHom _ _
  exact Descent.finiteDimensional_fixedPoints (E' : Type u)
    (homVecK (M.baseChange E') (N.baseChange E'))

/-- **The Hom-space of the base change is the base restriction of the Hom-space.**  `W` does not
change under base change — only the group acting on it does, from `Gal(L/K)` to `Gal(L/E')` — so
`Hom_Γ(M_{E'},N_{E'})` *is* `Hom_Γ(M,N)` with its base restricted (`VecK.restrictBase`).

This is what lets `prop:homdescent` be exactly the generic descent step
`Descent.tower_fixedPoints_iso`, with no `Hom`-specific argument left in it.

@census none (helper)
-/
theorem homVecK_baseChange (M N : FDRep Γ) (E' : IntermediateField K L)
    [FiniteDimensional K E'] :
    homVecK (M.baseChange E') (N.baseChange E') = (homVecK M N).restrictBase E' := rfl

/-- **Proposition** (`prop:homdescent`, §1.4 of the source).

Let `Γ_K` be a quiver with a `K`-rational structure (clause `RQ2-1.12-H1`).  For `K`-rational
representations `M_K` and `N_K` of `Γ_K` (clause `RQ2-1.12-H2`) and **any** intermediate field
`L/E'/K` with `E'/K` finite (clauses `RQ2-1.12-H3`, `RQ2-1.12-H5`) — not only `E' = L` — there is a
canonical isomorphism

`E' ⊗_K Hom_{Γ_K}(M_K,N_K) ≅ Hom_{Γ_{E'}}(M_{E'},N_{E'})`

of finite-dimensional `E'`-vector spaces (clauses `RQ2-1.12-C1`, `RQ2-1.12-C2`, `RQ2-1.12-C3`).
*Canonical* (clause `RQ2-1.12-C2`) is pinned by the second conjunct: the isomorphism is the map
induced by `α ⊗ ψ ↦ α ψ`, stated as an identity of the underlying families of `L`-linear maps.

@census    RQ2-1.12
@source    prop:homdescent
@clauses   RQ2-1.12-H1, RQ2-1.12-H2, RQ2-1.12-H3, RQ2-1.12-H4, RQ2-1.12-H5, RQ2-1.12-C1, RQ2-1.12-C2,
           RQ2-1.12-C3
@imports   none
@divergence JUSTIFIED_REFORMULATION (verifier-agreed, `stages/S2/VERIFICATION.md` V-2).
`Hom_{Γ_K}(M_K,N_K)` is `homModule`, the fixed-point space `W^{Gal(L/K)}`;
`Rep.homEquiv` proves this is the paper's `Rep.Hom` (census `RQ2-1.09`), so the left-hand side is
the paper's.  `E'/K` finite (clause `RQ2-1.12-H5`) is carried as `[FiniteDimensional K E']`, as the
source states it since census r5 and as `Γ_{E'}` (S1's `RationalQuiver.baseChange`, `RQ2-1.05-H2`)
requires.  The quantifier is over **every** intermediate `E'`, not only `E' = L`
(clause `RQ2-1.12-H3`).  `E'`-linearity and finite-dimensionality of both sides
(clause `RQ2-1.12-C3`) are the `≃ₗ[E']` and the two `FiniteDimensional` lemmas
`finiteDimensional_homModule` / `finiteDimensional_homModule_baseChange`.

**Added hypothesis, disclosed** (`VERIFICATION.md` V-4).  `M` and `N` are taken to be objects of
`Rep(Γ_K)`, i.e. `FDRep Γ`, whereas clause `RQ2-1.12-H2` says only "`M_K` and `N_K` are
`K`-rational representations of `Γ_K`": **finite-dimensionality is an added hypothesis**.  It is
the source's own reading and it is not optional: clause `RQ2-1.12-H4` records that the source
verifies the continuity of the action on `W` *from* finite-dimensionality of `M_K`, `N_K`, clause
`RQ2-1.12-C3` asserts a conclusion about **finite-dimensional** `E'`-vector spaces which is false
without it, and `prop:homdescent` is stated after the definition of `Rep(Γ_K)`, whose objects are
finite-dimensional by clause `RQ2-1.10-C1`.
-/
theorem hom_baseChange_iso (M N : FDRep Γ) (E' : IntermediateField K L)
    [FiniteDimensional K E'] :
    ∃ f : (E' ⊗[K] homModule M N)
        ≃ₗ[E'] homModule (M.baseChange E') (N.baseChange E'),
      ∀ (a : E') (ψ : homModule M N),
        homFam (M.baseChange E') (N.baseChange E') (f (a ⊗ₜ[K] ψ))
          = (a : L) • homFam M N ψ := by
  haveI : FiniteDimensional L (homVecK M N).carrier := finiteDimensional_classicalHom M N
  obtain ⟨f, hf⟩ := Descent.tower_fixedPoints_iso (homVecK M N) E'
  exact ⟨f, fun a ψ => congrArg Subtype.val (hf a ψ)⟩


end Rep

end RationalQuiver

end RationalQuivers
