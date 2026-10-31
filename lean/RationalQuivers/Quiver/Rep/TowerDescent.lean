module

public import RationalQuivers.Quiver.Rep.BaseChange
public import RationalQuivers.Descent.Galois
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

/-!
# Galois descent along a tower `K ⊆ E' ⊆ L`

Supporting material for §1.3–§1.4 of `latex/rational_quivers.tex`: the step both
`unlabeled:1` (census `RQ2-1.11`) and `prop:homdescent` (census `RQ2-1.12`) reduce to, isolated once
so that neither has to repeat it.

## Main definitions / results
* `RationalQuivers.Descent.VecK.restrictBase` — an `L`-vector space with a `K`-structure, read as
  one with an `E'`-structure by restricting the `Gal(L/K)`-action along `Gal(L/E') ↪ Gal(L/K)`.
  This is `def:quiverbasechange`'s device (S1's `RationalQuiver.baseChange`) at the level of
  vector spaces.
* `RationalQuivers.Descent.tower_fixedPoints_iso` — **the descent step**: for `E'/K` finite,
  `E' ⊗_K V^{Gal(L/K)} ≅ V^{Gal(L/E')}` canonically, by `α ⊗ v ↦ α v`.

## Implementation notes

**Where this belongs.**  `VecK` and `fixedPoints` are S0's (`Descent/Galois.lean`), and both
declarations here are about them and mention nothing of §1.2–§1.4; they belong **upstream in
`Descent/`**.  They are written in an S2 module because S0 is frozen and S2 may not modify it
(stage brief; `WORKFLOW.md` R11).  Reported to the coordinator for relocation at the next S0
revision — nothing in either statement depends on `Quiver/`.

**The proof of `tower_fixedPoints_iso`**, which is the source's "the general case … follows … again
by Galois descent":

* the canonical map `g : E' ⊗_K V^{G_K} → V^{G_{E'}}`, `α ⊗ v ↦ α v`, is mathlib's
  `LinearMap.liftBaseChange`;
* `g`, followed by the inclusion into `V`, **equals** the composite
  `E' ⊗_K V^{G_K} → L ⊗_K V^{G_K} → V` of `LinearMap.rTensor` along `E' ↪ L` (injective because a
  `K`-vector space is flat) with S0's `descentCounit` (injective by `descentCounit_bijective`),
  so `g` is injective;
* `finrank_{E'} (E' ⊗_K V^{G_K}) = finrank_K V^{G_K} = finrank_L V = finrank_{E'} V^{G_{E'}}`,
  the outer two equalities being Galois descent over `K` and over `E'` (`finrank_fixedPoints`);
* an injective map between `E'`-spaces of equal finite dimension is onto.

So Galois descent is applied once over each base, and the passage between them is a dimension
count rather than faithfully-flat descent.  Faithful flatness would also serve; this route uses
only what the census clauses already assert.
-/

universe u

namespace RationalQuivers

namespace Descent

open scoped TensorProduct

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-! ### Restricting the base of a `K`-structure -/

section RestrictBase

variable [IsGalois K L] (X : VecK K L) (E' : IntermediateField K L) [FiniteDimensional K E']

/-- The `E'`-vector space structure on `X`, along `E' → L`.  A `local instance` only, so that
`VecK.restrictBase` below can be assembled; it is never global.

@census none (helper)
-/
@[reducible] def restrictBaseModule : Module (E' : Type u) X.carrier :=
  Module.compHom _ (algebraMap (E' : Type u) L)

attribute [local instance] restrictBaseModule

/-- `K ⊆ E' ⊆ L` acts compatibly on `X`.  @census none (helper) -/
theorem restrictBaseTower : IsScalarTower (E' : Type u) L X.carrier :=
  ⟨fun c a x => by
    show (c • a) • x = algebraMap (E' : Type u) L c • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩

attribute [local instance] restrictBaseTower

/-- The `Gal(L/E')`-action on `X` obtained by restricting the `Gal(L/K)`-action.

@census none (helper)
-/
@[reducible] def restrictBaseAction : DistribMulAction Gal(L/(E' : Type u)) X.carrier :=
  DistribMulAction.compHom X.carrier (galRestrict K L E')

attribute [local instance] restrictBaseAction

/-- The restricted action is again a `K`-structure — semi-linear because the original one is, and
continuous because `galRestrict` is continuous (S1's `continuous_galRestrict`, which is where
`E'/K` finite is used).

@census none (helper)
-/
theorem restrictBaseKStructure : KStructure (E' : Type u) L X.carrier :=
  { smul_smul_semilinear := fun τ a v =>
      IsSemilinearAction.smul_smul_semilinear (V := X.carrier) (galRestrict K L E' τ) a v
    isOpen_stabilizer := fun v =>
      (KStructure.isOpen_stabilizer (K := K) (L := L) (V := X.carrier) v).preimage
        (continuous_galRestrict K L E') }

attribute [local instance] restrictBaseKStructure

/-- An `L`-vector space with a `K`-structure, read as one with an `E'`-structure for an
intermediate field `L/E'/K` with `E'/K` finite: same space, same semi-linear maps, with the action
restricted along `Gal(L/E') ↪ Gal(L/K)` (`galRestrict`).

This is exactly what S1's `RationalQuiver.baseChange` does to a rational quiver
(`def:quiverbasechange`: `Γ_{E'} = E' ⊗_K Γ_K := (Γ, ρ|_{Gal(L/E')})`), and what
`Rep.baseChange` does to a representation.

@census none (helper for `RQ2-1.11`, `RQ2-1.12`; belongs upstream in `Descent/` — see the module
notes)
-/
def VecK.restrictBase : VecK (E' : Type u) L where
  carrier := X.carrier
  isAddCommGroup := X.isAddCommGroup
  isModuleK := restrictBaseModule X E'
  isModuleL := X.isModuleL
  isScalarTower := restrictBaseTower X E'
  galoisAction := restrictBaseAction X E'
  isKStructure := restrictBaseKStructure X E'

end RestrictBase

/-- The base-restricted space is the same space.  @census none (helper) -/
@[simp]
theorem VecK.restrictBase_carrier [IsGalois K L] (X : VecK K L) (E' : IntermediateField K L)
    [FiniteDimensional K E'] : (X.restrictBase E').carrier = X.carrier := rfl

/-! ### Dimensions of the fixed-point space -/

/-- Galois descent (`thm:galoisdescent`, census `RQ2-1.13`) computes the `F`-dimension of the
fixed-point space as the `L`-dimension of the whole space.

@census none (helper: clause `RQ2-1.12-C3`)
-/
theorem finrank_fixedPoints (F : Type u) [Field F] [Algebra F L] [IsGalois F L]
    (X : Descent.VecK F L) :
    Module.finrank F (Descent.fixedPoints F L X) = Module.finrank L X.carrier := by
  have e := LinearEquiv.ofBijective (Descent.descentCounit F L X)
    (Descent.descentCounit_bijective F L X)
  rw [← e.finrank_eq, Module.finrank_baseChange]

/-- Galois descent also transports finite-dimensionality from `L` down to `F`.

@census none (helper: clause `RQ2-1.12-C3`)
-/
theorem finiteDimensional_fixedPoints (F : Type u) [Field F] [Algebra F L] [IsGalois F L]
    (X : Descent.VecK F L) [FiniteDimensional L X.carrier] :
    FiniteDimensional F (Descent.fixedPoints F L X) := by
  have e := LinearEquiv.ofBijective (Descent.descentCounit F L X)
    (Descent.descentCounit_bijective F L X)
  have h1 : Module.rank L (L ⊗[F] (Descent.fixedPoints F L X)) = Module.rank L X.carrier :=
    e.rank_eq
  rw [Module.rank_baseChange] at h1
  have h2 : Module.rank L X.carrier < Cardinal.aleph0 := Module.rank_lt_aleph0_iff.2 inferInstance
  rw [← h1] at h2
  exact Module.rank_lt_aleph0_iff.1 (by simpa using h2)

/-! ### The descent step -/

/-- **Galois descent along a tower.**  Let `L/K` be Galois, `V` an `L`-vector space with a
`K`-structure whose underlying `L`-space is finite-dimensional, and `L/E'/K` an intermediate field
with `E'/K` finite.  Then the canonical map

`E' ⊗_K V^{Gal(L/K)} → V^{Gal(L/E')}`,  `α ⊗ v ↦ α v`

is an isomorphism of `E'`-vector spaces.

This is the step `prop:homdescent` calls "again by Galois descent", and the same step discharges
clause `RQ2-1.11-C1`'s `M_{E'} = E' ⊗_K M_K`.

@census none (helper for `RQ2-1.11-C1` and `RQ2-1.12`; belongs upstream in `Descent/`)
-/
theorem tower_fixedPoints_iso [IsGalois K L] (X : VecK K L) [FiniteDimensional L X.carrier]
    (E' : IntermediateField K L) [FiniteDimensional K E'] :
    ∃ f : (E' ⊗[K] fixedPoints K L X)
        ≃ₗ[E'] fixedPoints (E' : Type u) L (X.restrictBase E'),
      ∀ (a : E') (m : fixedPoints K L X),
        ((f (a ⊗ₜ[K] m) : (X.restrictBase E').carrier)) = (a : L) • (m : X.carrier) := by
  classical
  letI : Module K (fixedPoints (E' : Type u) L (X.restrictBase E')) :=
    Module.compHom _ (algebraMap K (E' : Type u))
  haveI : IsScalarTower K (E' : Type u) (fixedPoints (E' : Type u) L (X.restrictBase E')) :=
    ⟨fun c a x => by
      show (c • a) • x = algebraMap K (E' : Type u) c • (a • x)
      rw [Algebra.smul_def, mul_smul]⟩
  -- a `Gal(L/K)`-invariant vector is a fortiori `Gal(L/E')`-invariant
  have hmem : ∀ m : fixedPoints K L X,
      (m : X.carrier) ∈ fixedPoints (E' : Type u) L (X.restrictBase E') := by
    intro m
    refine (mem_fixedPoints _ _).2 fun τ => ?_
    exact ((mem_fixedPoints K L).1 m.2) (galRestrict K L E' τ)
  set g₀ : fixedPoints K L X →ₗ[K] fixedPoints (E' : Type u) L (X.restrictBase E') :=
    { toFun := fun m => ⟨(m : X.carrier), hmem m⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun c m => by
        refine Subtype.ext ?_
        show ((c • m : fixedPoints K L X) : X.carrier)
            = algebraMap (E' : Type u) L (algebraMap K (E' : Type u) c) • (m : X.carrier)
        rw [Submodule.coe_smul, ← IsScalarTower.algebraMap_apply K (E' : Type u) L c,
          IsScalarTower.algebraMap_smul] } with hg₀
  have hg₀coe : ∀ m : fixedPoints K L X,
      ((g₀ m : fixedPoints (E' : Type u) L (X.restrictBase E')) :
        (X.restrictBase E').carrier) = (m : X.carrier) := fun _ => rfl
  set g : (E' ⊗[K] fixedPoints K L X)
      →ₗ[E'] fixedPoints (E' : Type u) L (X.restrictBase E') :=
    LinearMap.liftBaseChange (E' : Type u) g₀ with hg
  set q : (E' ⊗[K] fixedPoints K L X) →ₗ[K] L ⊗[K] (fixedPoints K L X) :=
    LinearMap.rTensor _ (E'.val.toLinearMap) with hq
  have hqinj : Function.Injective q := by
    rw [hq]
    exact Module.Flat.rTensor_preserves_injective_linearMap _ (fun x y h => Subtype.ext h)
  have hrinj : Function.Injective (descentCounit K L X) := (descentCounit_bijective K L X).1
  have hfactor : ∀ z : E' ⊗[K] fixedPoints K L X,
      ((g z : fixedPoints (E' : Type u) L (X.restrictBase E')) :
        (X.restrictBase E').carrier) = descentCounit K L X (q z) := by
    intro z
    induction z with
    | tmul a m =>
        rw [hg, LinearMap.liftBaseChange_tmul, hq, LinearMap.rTensor_tmul]
        show ((a • g₀ m : fixedPoints (E' : Type u) L (X.restrictBase E')) :
            (X.restrictBase E').carrier) = descentCounit K L X ((a : L) ⊗ₜ[K] m)
        rw [descentCounit_tmul, Submodule.coe_smul, hg₀coe]
        rfl
    | add z w hz hw => simp only [map_add, Submodule.coe_add, hz, hw]; rfl
  have hginj : Function.Injective g := by
    intro z w hzw
    refine hqinj (hrinj ?_)
    rw [← hfactor z, ← hfactor w, hzw]
  haveI : FiniteDimensional K (fixedPoints K L X) := finiteDimensional_fixedPoints K X
  haveI : FiniteDimensional L (X.restrictBase E').carrier :=
    inferInstanceAs (FiniteDimensional L X.carrier)
  haveI : FiniteDimensional (E' : Type u)
      (fixedPoints (E' : Type u) L (X.restrictBase E')) :=
    finiteDimensional_fixedPoints (E' : Type u) (X.restrictBase E')
  haveI : FiniteDimensional (E' : Type u) (E' ⊗[K] fixedPoints K L X) := inferInstance
  have hdim : Module.finrank (E' : Type u) (E' ⊗[K] fixedPoints K L X)
      = Module.finrank (E' : Type u) (fixedPoints (E' : Type u) L (X.restrictBase E')) := by
    rw [Module.finrank_baseChange, finrank_fixedPoints K X,
      finrank_fixedPoints (E' : Type u) (X.restrictBase E')]
    rfl
  refine ⟨LinearMap.linearEquivOfInjective g hginj hdim, fun a m => ?_⟩
  rw [LinearMap.linearEquivOfInjective_apply hginj hdim, hg, LinearMap.liftBaseChange_tmul]
  show ((a • g₀ m : fixedPoints (E' : Type u) L (X.restrictBase E')) :
    (X.restrictBase E').carrier) = _
  rw [Submodule.coe_smul, hg₀coe]
  rfl

end Descent

/-! ### The `K`-form of a representation, and clause `RQ2-1.11-C1` -/

namespace RationalQuiver

open scoped TensorProduct

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

namespace Rep

variable {Γ : RationalQuiver K L}

/-- The underlying function of the semi-linear `Gal(L/K)`-action on `∏_{v ∈ V} M(v)`:
`(σ · x)_w := φ_{σ⁻¹ w, σ}(x_{σ⁻¹ w})`.  This is the action of
`def:rationalrepresentations`(ii) read on the product rather than on the disjoint union; `V` is
finite, so the product is the direct sum `⊕_v M(v)`.

@census none (helper: clause `RQ2-1.11-C1`)
-/
def totSMulFun (M : Rep Γ) (σ : Gal(L/K)) (x : ∀ v : Γ.V, M.M v) (w : Γ.V) : M.M w :=
  M.φ' σ (smul_inv_smul σ w) (x (σ⁻¹ • w))

/-- `σ · x` computed through any presentation of `σ⁻¹ w`.  @census none (helper) -/
theorem totSMulFun_eq (M : Rep Γ) (σ : Gal(L/K)) (x : ∀ v : Γ.V, M.M v) {w u : Γ.V}
    (h : σ • u = w) (h' : σ⁻¹ • w = u) : totSMulFun M σ x w = M.φ' σ h (x u) := by
  subst h'; rfl

/-- The action of `Gal(L/K)` on `⊕_v M(v)`.  @census none (helper) -/
instance totSMul (M : Rep Γ) : SMul Gal(L/K) (∀ v : Γ.V, M.M v) where
  smul σ x := totSMulFun M σ x

@[simp]
theorem totSMul_apply (M : Rep Γ) (σ : Gal(L/K)) (x : ∀ v : Γ.V, M.M v) (w : Γ.V) :
    (σ • x) w = totSMulFun M σ x w := rfl

/-- `1 · x = x`.  @census none (helper) -/
theorem totSMul_one (M : Rep Γ) (x : ∀ v : Γ.V, M.M v) : (1 : Gal(L/K)) • x = x := by
  funext w
  have h1 : (1 : Gal(L/K)) • w = w := one_smul _ w
  have h1' : (1 : Gal(L/K))⁻¹ • w = w := by rw [inv_one, one_smul]
  rw [totSMul_apply, totSMulFun_eq M 1 x h1 h1', M.φ'_one]
  exact M.eqCast_rfl w (x w)

/-- `(στ) · x = σ · (τ · x)`, from the cocycle condition.  @census none (helper) -/
theorem totSMul_mul (M : Rep Γ) (σ τ : Gal(L/K)) (x : ∀ v : Γ.V, M.M v) :
    (σ * τ) • x = σ • (τ • x) := by
  funext w
  set u : Γ.V := (σ * τ)⁻¹ • w with hu
  have h₃ : (σ * τ) • u = w := by rw [hu, smul_inv_smul]
  have h₅ : (σ * τ)⁻¹ • w = u := rfl
  have h₁ : σ • (τ • u) = w := by rw [← mul_smul]; exact h₃
  have h₁' : σ⁻¹ • w = τ • u := by rw [← h₁, inv_smul_smul]
  have h₂' : τ⁻¹ • (τ • u) = u := inv_smul_smul τ u
  rw [totSMul_apply, totSMul_apply, totSMulFun_eq M (σ * τ) x h₃ h₅,
    totSMulFun_eq M σ (τ • x) h₁ h₁', totSMul_apply,
    totSMulFun_eq M τ x (rfl : τ • u = τ • u) h₂', M.φ'_comp σ τ rfl h₁ h₃]

/-- `Gal(L/K)` acts on `⊕_v M(v)` by additive automorphisms.  @census none (helper) -/
instance totAction (M : Rep Γ) : DistribMulAction Gal(L/K) (∀ v : Γ.V, M.M v) where
  one_smul := totSMul_one M
  mul_smul := totSMul_mul M
  smul_zero σ := by
    funext w; simp only [totSMul_apply, totSMulFun, Pi.zero_apply, map_zero]
  smul_add σ x y := by
    funext w; simp only [totSMul_apply, totSMulFun, Pi.add_apply, map_add]

/-- The action on `⊕_v M(v)` is semi-linear.  @census none (helper) -/
theorem totIsSemilinearAction (M : Rep Γ) :
    Descent.IsSemilinearAction K L (∀ v : Γ.V, M.M v) where
  smul_smul_semilinear σ a x := by
    funext w
    simp only [totSMul_apply, totSMulFun, Pi.smul_apply, M.φ'_smul]

/-- The action on `⊕_v M(v)` is continuous: `x` has open stabilizer, namely the (finite)
intersection over the finitely many vertices `v` of the stabilizers of the points `(v, x_v)` of
`⊔_v M(v)` — each open by clause `RQ2-1.08-C6`.

@census none (helper: clause `RQ2-1.11-C1`)
-/
theorem totKStructure (M : Rep Γ) :
    letI := totIsSemilinearAction M
    Descent.KStructure K L (∀ v : Γ.V, M.M v) := by
  classical
  letI := totIsSemilinearAction M
  refine { __ := totIsSemilinearAction M, isOpen_stabilizer := fun x => ?_ }
  haveI : Fintype Γ.V := Fintype.ofFinite _
  set U : Γ.V → OpenSubgroup Gal(L/K) := fun v =>
    ⟨MulAction.stabilizer Gal(L/K) (M.tot v (x v)), M.isOpen_stabilizer_total _⟩ with hU
  refine Subgroup.isOpen_of_openSubgroup _ (U := Finset.univ.inf U) ?_
  intro σ hσ
  refine (MulAction.mem_stabilizer_iff).2 (funext fun w => ?_)
  have hj : σ ∈ U w := (Finset.inf_le (Finset.mem_univ w) : Finset.univ.inf U ≤ U w) hσ
  have h1 : M.tot (σ • w) (M.φ σ w (x w)) = M.tot w (x w) := hj
  have hv : σ • w = w := congrArg (fun y : M.Total => y.1) h1
  have hv' : σ⁻¹ • w = w := inv_smul_eq_iff.2 hv.symm
  have hxw : M.φ' σ hv (x w) = x w := (M.tot_eq_iff hv _ _).1 h1
  rw [totSMul_apply, totSMulFun_eq M σ x hv hv', hxw]

/-- **The `K`-form of a representation.**  `⊕_{v ∈ V} M(v)` with the semi-linear `Gal(L/K)`-action
of `def:rationalrepresentations`(ii), as an object of S0's `Descent.VecK K L`.  By Galois descent
(`thm:galoisdescent`, census `RQ2-1.13`) its fixed-point space
`Descent.fixedPoints K L (totVecK M)` **is** the `K`-vector space `M_K` the source writes, and
`L ⊗_K M_K ≅ ⊕_v M(v)` is `Descent.descentCounit`.

@census none (helper: the `M_K` of clause `RQ2-1.11-C1`)
-/
def totVecK (M : Rep Γ) : Descent.VecK K L :=
  letI : Module K (∀ v : Γ.V, M.M v) := Module.compHom _ (algebraMap K L)
  letI : IsScalarTower K L (∀ v : Γ.V, M.M v) := ⟨fun c a x => by
    show ((c • a) • x : ∀ v : Γ.V, M.M v) = algebraMap K L c • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩
  { carrier := ∀ v : Γ.V, M.M v
    isKStructure := totKStructure M }

/-- **Base change does not move `⊕_v M(v)`; it only shrinks the group.**  `M_{E'}`'s underlying
`L`-space, action and edge maps are `M`'s, with `Gal(L/K)` replaced by `Gal(L/E')` — so the
`E'`-structure of `M_{E'}` is literally the base restriction of the `K`-structure of `M`.

@census none (helper: clause `RQ2-1.11-C1`)
-/
theorem totVecK_baseChange (M : Rep Γ) (E' : IntermediateField K L) [IsGalois K L]
    [FiniteDimensional K E'] :
    totVecK (M.baseChange E') = (totVecK M).restrictBase E' := rfl

/-- **Clause `RQ2-1.11-C1`, pinned**: `M_{E'} = E' ⊗_K M_K`.

The base change of `M` along `L/E'/K` has, as its `E'`-form, exactly `E' ⊗_K` (the `K`-form of
`M`), canonically — the isomorphism is induced by `α ⊗ m ↦ α m`.  The source writes
`M_{E'} := E' ⊗_K M_K` and then equips it with a representation structure; `Rep.baseChange`
constructs the representation directly, by restricting the Galois action (which is what
`def:quiverbasechange` does for the quiver, and what the source's own one-line proof appeals to),
and **this lemma is the proof that the two descriptions agree** — the `RQ2-1.11` analogue of
`Rep.mem_homModule_iff` for `RQ2-1.12` (`stages/S2/VERIFICATION.md` V-3).

@census    none (auxiliary; discharges clause `RQ2-1.11-C1`)
@source    UNLABELED-basechange-representations
@clauses   RQ2-1.11-C1
@imports   none
@divergence JUSTIFIED_REFORMULATION (`stages/S2/G4-VERIFICATION.md` C-3).  Two points, both of
the shape the coordinator adjudicated for this stage in `VERIFICATION.md` V-2 and V-4.
(i) **Added hypothesis.**  The lemma is stated for `M : FDRep Γ`, i.e. for a **finite-dimensional**
representation, whereas clause `RQ2-1.11-C1` carries no finite-dimensionality: the descent step
`Descent.tower_fixedPoints_iso` needs `⊕_v M(v)` to be finite-dimensional over `L`, and clause
`RQ2-1.10-C1` supplies exactly that for the objects of `Rep(Γ_K)`, which is what `RQ2-1.11` is about.
(ii) **Reformulation.**  `M_K` is realized as `(⊕_v M(v))^{Gal(L/K)}`, the fixed-point space of the
Galois module underlying `M`.  The source writes `M_K` and never defines it; by `thm:galoisdescent`
(census `RQ2-1.13`) it can only be this space, and `Descent.descentCounit` is the isomorphism
`L ⊗_K M_K ≅ ⊕_v M(v)` that says so.  See ledger `DEF-S2-08`.
Note the scope of what is pinned (`G4-VERIFICATION.md` O-1): this is the **underlying Galois
module**, up to canonical isomorphism.  Clause `RQ2-1.11-C1`'s other half — that `M_{E'}` *carries
a natural structure of representation* of `Γ_{E'}` — is discharged **by construction**, by
`Rep.baseChange`, which is what the source's own one-line proof does.
-/
theorem baseChange_form_iso [IsGalois K L] (M : FDRep Γ) (E' : IntermediateField K L)
    [FiniteDimensional K E'] :
    ∃ f : (E' ⊗[K] Descent.fixedPoints K L (totVecK M.toRep))
        ≃ₗ[E'] Descent.fixedPoints (E' : Type u) L (totVecK (M.toRep.baseChange E')),
      ∀ (a : E') (m : Descent.fixedPoints K L (totVecK M.toRep)),
        (((f (a ⊗ₜ[K] m) : (totVecK (M.toRep.baseChange E')).carrier)) :
            ∀ v : Γ.V, M.toRep.M v)
          = (a : L) • (((m : (totVecK M.toRep).carrier)) : ∀ v : Γ.V, M.toRep.M v) := by
  haveI : Fintype Γ.V := Fintype.ofFinite _
  haveI : FiniteDimensional L (totVecK M.toRep).carrier :=
    inferInstanceAs (FiniteDimensional L (∀ v : Γ.V, M.toRep.M v))
  obtain ⟨f, hf⟩ := Descent.tower_fixedPoints_iso (totVecK M.toRep) E'
  exact ⟨f, hf⟩

end Rep

end RationalQuiver

end RationalQuivers
