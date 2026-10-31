module

public import RationalQuivers.Descent.KStructure
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

/-!
# Galois descent for vector spaces

Formalizes Theorem `thm:galoisdescent` of §1.1 of `latex/rational_quivers.tex`
(census `RQ2-1.13`).

## Main definitions / results
* `RationalQuivers.Descent.VecK` — the category of `L`-vector spaces with a `K`-structure and
  `K`-rational maps (the *target* of the descent equivalence; clauses `RQ2-1.13-C3`, `RQ2-1.13-C4`).
* `RationalQuivers.Descent.fixedPoints` — `V^{Gal(L/K)} = {v | ∀ σ, φ_σ v = v}` as a
  `K`-subspace, and `RationalQuivers.Descent.fixedPointsFunctor`, the quasi-inverse functor
  (clause `RQ2-1.13-C5`).
* `RationalQuivers.Descent.baseChangeFunctor` — `V ↦ (L ⊗_K V, (φ_σ)_σ)` (clause `RQ2-1.13-C1`).
* `RationalQuivers.Descent.galoisDescent` — **Theorem (Galois descent)**, census `RQ2-1.13`.

## Implementation notes
* **No finiteness anywhere (clause `RQ2-1.13-C7`).**  `ModuleCat.{u} K` is the category of *all*
  `K`-modules with carrier in `Type u`; `VecK K L` is the category of *all* `L`-vector spaces with
  a `K`-structure.  Neither side carries a `FiniteDimensional` hypothesis, and neither does
  `galoisDescent`.
* **Finite *and* infinite `L/K` (clauses `RQ2-1.13-H1`, `RQ2-1.13-C6`).**  The hypothesis is
  mathlib's `IsGalois K L` (`Normal` + `Algebra.IsSeparable`), which carries **no** finiteness
  assumption; `Gal(L/K)` carries mathlib's `krullTopology`, which is discrete exactly when `L/K`
  is finite.
* **Continuity (clause `RQ2-1.13-H2`).**  Continuity of the semi-linear action is part of
  `KStructure` (census `RQ2-1.16`) and hence of every object of `VecK K L`, exactly as in the
  source after the D2 editorial correction.
* The equivalence is stated as the existence of a `CategoryTheory.Equivalence` whose `functor` is
  *literally* `baseChangeFunctor` and whose `inverse` is *literally* `fixedPointsFunctor`, so that
  clauses `RQ2-1.13-C1`, `RQ2-1.13-C2` and `RQ2-1.13-C5` are all pinned by the statement and not only
  by its proof.
-/

universe u

open scoped TensorProduct
open CategoryTheory

namespace RationalQuivers.Descent

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- An object of the category of `L`-vector spaces with a `K`-structure: an `L`-vector space `V`
(regarded as a `K`-vector space via `K → L`) together with a `K`-structure `(φ_σ)_σ` on it —
a semi-linear, **continuous** `Gal(L/K)`-action (census `RQ2-1.16`).

This is the target category of `thm:galoisdescent` (clause `RQ2-1.13-C3`); its morphisms are the
`K`-rational maps (clause `RQ2-1.13-C4`), see the `Category` instance below.

@census    none
-/
structure VecK : Type (u + 1) where
  /-- The underlying `L`-vector space. -/
  carrier : Type u
  [isAddCommGroup : AddCommGroup carrier]
  [isModuleK : Module K carrier]
  [isModuleL : Module L carrier]
  [isScalarTower : IsScalarTower K L carrier]
  [galoisAction : DistribMulAction Gal(L/K) carrier]
  [isKStructure : KStructure K L carrier]

attribute [instance] VecK.isAddCommGroup VecK.isModuleK VecK.isModuleL VecK.isScalarTower
  VecK.galoisAction VecK.isKStructure

namespace VecK

instance : CoeSort (VecK K L) (Type u) := ⟨VecK.carrier⟩

/-- Morphisms of `VecK K L` are exactly the `K`-rational maps: `L`-linear maps commuting with the
two `Gal(L/K)`-actions (clause `RQ2-1.13-C4`, census `RQ2-1.17`).

@census    none
-/
instance category : Category.{u} (VecK K L) where
  Hom X Y := {f : X.carrier →ₗ[L] Y.carrier // IsKRational K L f}
  id _ := ⟨LinearMap.id, isKRational_id⟩
  comp f g := ⟨g.1 ∘ₗ f.1, g.2.comp f.2⟩
  id_comp _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  comp_id _ := Subtype.ext (LinearMap.ext fun _ => rfl)
  assoc _ _ _ := Subtype.ext (LinearMap.ext fun _ => rfl)

@[simp]
theorem id_val (X : VecK K L) : (𝟙 X : X ⟶ X).1 = LinearMap.id := rfl

@[simp]
theorem comp_val {X Y Z : VecK K L} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).1 = g.1 ∘ₗ f.1 := rfl

end VecK

/-- **The fixed-point space** `V^{Gal(L/K)} = {v ∈ V | ∀ σ, φ_σ(v) = v}` of an `L`-vector space
with a `K`-structure, as a `K`-subspace (clause `RQ2-1.13-C5`).

@census    none
-/
def fixedPoints (X : VecK K L) : Submodule K X.carrier where
  carrier := {v : X.carrier | ∀ σ : Gal(L/K), σ • v = v}
  add_mem' {v w} hv hw σ := by rw [smul_add, hv σ, hw σ]
  zero_mem' σ := smul_zero σ
  smul_mem' c v hv σ := by rw [smul_comm σ c v, hv σ]

@[simp]
theorem mem_fixedPoints {X : VecK K L} {v : X.carrier} :
    v ∈ fixedPoints K L X ↔ ∀ σ : Gal(L/K), σ • v = v := Iff.rfl

/-- Helper (no census row): a `K`-rational map restricts to the fixed-point subspaces. -/
def fixedPointsMap {X Y : VecK K L} (f : X ⟶ Y) :
    (fixedPoints K L X) →ₗ[K] (fixedPoints K L Y) :=
  (LinearMap.restrictScalars K f.1).restrict fun v hv σ => by
    show σ • f.1 v = f.1 v
    rw [← f.2 σ v, hv σ]

@[simp]
theorem fixedPointsMap_coe {X Y : VecK K L} (f : X ⟶ Y) (v : fixedPoints K L X) :
    (fixedPointsMap K L f v : Y.carrier) = f.1 (v : X.carrier) := rfl

/-- **The fixed-point functor** `(V,(φ_σ)_σ) ↦ V^{Gal(L/K)}`, the quasi-inverse of
`thm:galoisdescent` (clause `RQ2-1.13-C5`).

@census    none
-/
def fixedPointsFunctor : VecK K L ⥤ ModuleCat.{u} K where
  obj X := ModuleCat.of K (fixedPoints K L X)
  map f := ModuleCat.ofHom (fixedPointsMap K L f)
  map_id X := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun v => Subtype.ext rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun v => Subtype.ext rfl

/-- **The base-change functor** `V ↦ (L ⊗_K V, (φ_σ)_σ)` of `thm:galoisdescent`
(clause `RQ2-1.13-C1`), with the canonical `K`-structure of census `RQ2-1.18` on `L ⊗_K V` and
`1 ⊗ φ` on morphisms.

@census    none
-/
def baseChangeFunctor [Algebra.IsIntegral K L] : ModuleCat.{u} K ⥤ VecK K L where
  obj M := { carrier := L ⊗[K] M }
  map f := ⟨LinearMap.baseChange L f.hom, isKRational_baseChange K L f.hom⟩
  map_id M := Subtype.ext (by simp [LinearMap.baseChange_id])
  map_comp f g := Subtype.ext (by
    simpa using LinearMap.baseChange_comp (A := L) f.hom g.hom)

/-- Helper (no census row): `1 ⊗ v` is `Gal(L/K)`-fixed in `L ⊗[K] M`. -/
theorem one_tmul_mem_fixedPoints {M : Type u} [AddCommGroup M] [Module K M] (v : M)
    (σ : Gal(L/K)) : σ • ((1 : L) ⊗ₜ[K] v) = (1 : L) ⊗ₜ[K] v := by
  rw [galoisTensorAction_tmul, map_one]

/-- Helper (no census row): the canonical map `V → (L ⊗_K V)^{Gal(L/K)}`, `v ↦ 1 ⊗ v`, i.e. the
unit of the descent adjunction. -/
def descentUnit [Algebra.IsIntegral K L] (M : ModuleCat.{u} K) :
    M →ₗ[K] fixedPoints K L ((baseChangeFunctor K L).obj M) where
  toFun v := ⟨(1 : L) ⊗ₜ[K] (v : M), fun σ => one_tmul_mem_fixedPoints K L (M := M) v σ⟩
  map_add' _ _ := Subtype.ext (TensorProduct.tmul_add _ _ _)
  map_smul' c v := Subtype.ext (TensorProduct.tmul_smul c (1 : L) (v : M))

/-- Helper (no census row): the canonical map `L ⊗_K V^{Gal(L/K)} → V`, `α ⊗ v ↦ α · v`, i.e. the
counit of the descent adjunction.  Clause `RQ2-1.24-C3` is the assertion that *without* continuity
this map may fail to be an isomorphism. -/
def descentCounit (X : VecK K L) :
    L ⊗[K] (fixedPoints K L X) →ₗ[L] X.carrier :=
  LinearMap.liftBaseChange L ((fixedPoints K L X).subtype.restrictScalars K)

@[simp]
theorem descentCounit_tmul (X : VecK K L) (a : L) (v : fixedPoints K L X) :
    descentCounit K L X (a ⊗ₜ[K] v) = a • (v : X.carrier) := rfl

/-- Helper (no census row): the `Gal(L/K)`-action moves base-changed basis coordinates by `σ`.
If `b` is a `K`-basis of `M`, then `b.baseChange L` is an `L`-basis of `L ⊗[K] M` consisting of
`Gal(L/K)`-fixed vectors `1 ⊗ b i`, so the coordinates of `σ • x` are the `σ`-images of those
of `x`. -/
private theorem baseChange_repr_smul {ι : Type u} (M : Type u) [AddCommGroup M] [Module K M]
    (b : Module.Basis ι K M) (σ : Gal(L/K)) (x : L ⊗[K] M) (i : ι) :
    (b.baseChange L).repr (σ • x) i = σ ((b.baseChange L).repr x i) := by
  have key : ∀ y : L ⊗[K] M,
      (b.baseChange L).repr
          (TensorProduct.map σ.toLinearMap (LinearMap.id : M →ₗ[K] M) y) i
        = σ ((b.baseChange L).repr y i) := by
    intro y
    induction y with
    | tmul a m =>
        rw [TensorProduct.map_tmul]
        simp only [Module.Basis.baseChange_repr_tmul, LinearMap.id_coe, id_eq,
          AlgEquiv.toLinearMap_apply, Algebra.smul_def, map_mul, AlgEquiv.commutes]
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  exact key x

/-- Helper (no census row): `v ↦ 1 ⊗ v` is injective on any `K`-vector space. -/
private theorem one_tmul_injective {N : Type u} [AddCommGroup N] [Module K N] {v w : N}
    (h : (1 : L) ⊗ₜ[K] v = (1 : L) ⊗ₜ[K] w) : v = w := by
  classical
  set b : Module.Basis (Module.Free.ChooseBasisIndex K N) K N :=
    Module.Free.chooseBasis K N with hbdef
  refine b.repr.injective (Finsupp.ext fun i => (algebraMap K L).injective ?_)
  have h1 : (b.baseChange L).repr ((1 : L) ⊗ₜ[K] v) i
      = (b.baseChange L).repr ((1 : L) ⊗ₜ[K] w) i := by rw [h]
  simpa only [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one] using h1

/-- Helper (no census row): every `Gal(L/K)`-fixed element of `L ⊗[K] N` is of the form `1 ⊗ v`.
This is the surjectivity half of the descent unit; it uses `L^{Gal(L/K)} = K`, i.e. mathlib's
`InfiniteGalois.mem_range_algebraMap_iff_fixed`, which holds for infinite `L/K` as well. -/
private theorem exists_one_tmul_of_fixed [IsGalois K L] {N : Type u} [AddCommGroup N]
    [Module K N] (x : L ⊗[K] N) (hx : ∀ σ : Gal(L/K), σ • x = x) :
    ∃ v : N, (1 : L) ⊗ₜ[K] v = x := by
  classical
  set b : Module.Basis (Module.Free.ChooseBasisIndex K N) K N :=
    Module.Free.chooseBasis K N with hbdef
  set B := b.baseChange L with hBdef
  have hfix : ∀ i, ∀ σ : Gal(L/K), σ (B.repr x i) = B.repr x i := by
    intro i σ
    rw [hBdef, ← baseChange_repr_smul K L N b σ x i, hx σ]
  have hrange : ∀ i, ∃ c : K, algebraMap K L c = B.repr x i := fun i =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed (B.repr x i)).2 (hfix i)
  set g : L → K := fun a => if h : ∃ c : K, algebraMap K L c = a then h.choose else 0 with hgdef
  have hgspec : ∀ a : L, (∃ c : K, algebraMap K L c = a) → algebraMap K L (g a) = a := by
    intro a h
    rw [hgdef]
    simp only [dif_pos h]
    exact h.choose_spec
  have hg0 : g 0 = 0 :=
    (algebraMap K L).injective ((hgspec 0 ⟨0, map_zero _⟩).trans (map_zero _).symm)
  refine ⟨b.repr.symm (Finsupp.mapRange g hg0 (B.repr x)), B.repr.injective (Finsupp.ext ?_)⟩
  intro i
  rw [hBdef, Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one,
    LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply, hgspec _ (hrange i)]

/-- Helper (no census row): the unit `V → (L ⊗_K V)^{Gal(L/K)}` is bijective.  This is the
"faithfully flat" half of `thm:galoisdescent`; no finiteness hypothesis (clause `RQ2-1.13-C7`).

@census    none
-/
theorem descentUnit_bijective [IsGalois K L] (M : ModuleCat.{u} K) :
    Function.Bijective (descentUnit K L M) := by
  constructor
  · intro v w h
    exact one_tmul_injective K L (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    obtain ⟨v, hv⟩ := exists_one_tmul_of_fixed K L (N := (M : Type u)) x hx
    exact ⟨v, Subtype.ext hv⟩

section Speiser

/-- Helper (no census row): an open subgroup of `Gal(L/K)` contains the fixing subgroup of a
**finite normal** subextension.  This is mathlib's `krullTopology_mem_nhds_one_iff_of_normal`. -/
private theorem exists_finite_normal_fixingSubgroup_le [Normal K L]
    {H : Subgroup Gal(L/K)} (hH : IsOpen (H : Set Gal(L/K))) :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧ Normal K E ∧
      (E.fixingSubgroup : Set Gal(L/K)) ⊆ (H : Set Gal(L/K)) :=
  (krullTopology_mem_nhds_one_iff_of_normal K L _).1 (hH.mem_nhds (one_mem H))

/-- Helper (no census row): the counit `L ⊗_K V^{Gal(L/K)} → V` is `K`-rational. -/
private theorem isKRational_descentCounit [Algebra.IsIntegral K L] (X : VecK K L)
    (σ : Gal(L/K)) (u : L ⊗[K] (fixedPoints K L X)) :
    descentCounit K L X (σ • u) = σ • descentCounit K L X u := by
  have key : ∀ v : L ⊗[K] (fixedPoints K L X),
      descentCounit K L X (TensorProduct.map σ.toLinearMap
          (LinearMap.id : (fixedPoints K L X) →ₗ[K] (fixedPoints K L X)) v)
        = σ • descentCounit K L X v := by
    intro v
    induction v with
    | tmul a w =>
        rw [TensorProduct.map_tmul]
        simp only [LinearMap.id_coe, id_eq, AlgEquiv.toLinearMap_apply, descentCounit_tmul]
        rw [IsSemilinearAction.smul_smul_semilinear σ a (w : X.carrier), w.2 σ]
    | add v w hv hw => simp only [map_add, hv, hw, smul_add]
  exact key u

/-- Helper (no census row) — **Speiser's lemma**, in the form used by `thm:galoisdescent`.

Every `Gal(L/K)`-stable `L`-subspace `p` of an `L`-vector space with a `K`-structure is spanned,
over `L`, by its `Gal(L/K)`-FIXED vectors.

The proof is the classical averaging argument, run against a separating functional.  If `x ∈ p`
were outside the span `S` of the fixed vectors of `p`, pick `f : V →ₗ[L] L` with `S ≤ ker f` and
`f x ≠ 0`.  Continuity of the `K`-structure (clause `RQ2-1.13-H2`) makes the stabilizer of `x` open,
so it contains `Gal(L/E)` for a FINITE NORMAL subextension `E/K`; averaging over the finite group
`Gal(E/K)` gives, for each `a ∈ E`, a fixed vector `T a := Σ_q q(a) · (s q • x) ∈ p`, whence
`Σ_q q(a) · f (s q • x) = 0` for every `a ∈ E`.  Dedekind–Artin independence of characters
(mathlib's `linearIndependent_monoidHom`) forces every `f (s q • x)` to vanish; taking `q = 1`
contradicts `f x ≠ 0`.

This is the only place where continuity is used, and census `RQ2-1.24` records that it cannot be
dropped.
-/
private theorem mem_span_fixed_of_stable [IsGalois K L] (X : VecK K L)
    (p : Submodule L X.carrier)
    (hp : ∀ (σ : Gal(L/K)) (v : X.carrier), v ∈ p → σ • v ∈ p)
    (x : X.carrier) (hx : x ∈ p) :
    x ∈ Submodule.span L {v : X.carrier | v ∈ p ∧ ∀ σ : Gal(L/K), σ • v = v} := by
  classical
  by_contra hxs
  obtain ⟨f, hfx, hfker⟩ := Submodule.exists_le_ker_of_notMem hxs
  obtain ⟨E, hfd, hnorm, hle⟩ :=
    exists_finite_normal_fixingSubgroup_le (K := K) (L := L)
      (KStructure.isOpen_stabilizer (K := K) (L := L) x)
  haveI := hfd
  haveI := hnorm
  -- the restriction homomorphism onto the finite Galois group `Gal(E/K)`, and a set-theoretic
  -- section of it
  set π : Gal(L/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom ↥E with hπ
  have hπsurj : Function.Surjective π := AlgEquiv.restrictNormalHom_surjective (F := K) L
  set s : Gal(E/K) → Gal(L/K) := Function.surjInv hπsurj with hsdef
  have hs : ∀ q, π (s q) = q := fun q => Function.surjInv_eq hπsurj q
  -- `σ • x` depends only on `π σ`
  have hwd : ∀ σ τ : Gal(L/K), π σ = π τ → σ • x = τ • x := by
    intro σ τ hστ
    have hmem : σ⁻¹ * τ ∈ E.fixingSubgroup := by
      have : (σ⁻¹ * τ) ∈ π.ker := by
        simp [MonoidHom.mem_ker, hστ]
      rwa [IntermediateField.restrictNormalHom_ker] at this
    have : (σ⁻¹ * τ) • x = x := hle hmem
    calc σ • x = σ • ((σ⁻¹ * τ) • x) := by rw [this]
      _ = τ • x := by rw [← mul_smul, mul_inv_cancel_left]
  -- the averaged vectors `T a = Σ_q q(a) · (s q • x)`
  set T : ↥E → X.carrier :=
    fun a => ∑ q : Gal(E/K), algebraMap ↥E L (q a) • (s q • x) with hT
  have hTfix : ∀ (a : ↥E) (τ : Gal(L/K)), τ • T a = T a := by
    intro a τ
    have step : τ • T a
        = ∑ q : Gal(E/K),
            algebraMap ↥E L ((π τ * q) a) • (s (π τ * q) • x) := by
      rw [hT, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have h1 : τ (algebraMap ↥E L (q a))
          = algebraMap ↥E L ((π τ * q) a) := by
        rw [AlgEquiv.mul_apply]
        exact (AlgEquiv.restrictNormal_commutes τ ↥E (q a)).symm
      have h2 : τ • (s q • x) = s (π τ * q) • x := by
        rw [← mul_smul]
        exact hwd _ _ (by rw [map_mul, hs, hs])
      rw [IsSemilinearAction.smul_smul_semilinear, h1, h2]
    rw [step, hT]
    exact Equiv.sum_comp (Equiv.mulLeft (π τ))
      (fun q => algebraMap ↥E L (q a) • (s q • x))
  have hTp : ∀ a : ↥E, T a ∈ p := by
    intro a
    rw [hT]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (hp _ _ hx)
  have hfT : ∀ a : ↥E, f (T a) = 0 := by
    intro a
    exact hfker (Submodule.subset_span ⟨hTp a, fun τ => hTfix a τ⟩)
  -- expand `f (T a)` and apply Dedekind's independence of characters
  set c : Gal(E/K) → L := fun q => f (s q • x) with hc
  have hchar : ∀ a : ↥E,
      ∑ q : Gal(E/K), c q • (algebraMap ↥E L (q a)) = 0 := by
    intro a
    have := hfT a
    rw [hT, map_sum] at this
    simp only [map_smul, smul_eq_mul, hc] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  set χ : Gal(E/K) → (↥E →* L) := fun q =>
    ((algebraMap ↥E L : ↥E →+* L) :
        ↥E →* L).comp
      ((q : ↥E →ₐ[K] ↥E) :
        ↥E →+* ↥E) with hχ
  have hχinj : Function.Injective χ := by
    intro q q' hqq'
    have h : ∀ a : ↥E, q a = q' a := by
      intro a
      exact (algebraMap ↥E L).injective (DFunLike.congr_fun hqq' a)
    exact AlgEquiv.ext h
  have hLI : LinearIndependent L (fun q : Gal(E/K) => (χ q : ↥E → L)) :=
    (linearIndependent_monoidHom ↥E L).comp χ hχinj
  have hχapp : ∀ (q : Gal(E/K)) (y : ↥E), χ q y = algebraMap ↥E L (q y) := fun _ _ => rfl
  have hc0 : ∀ q : Gal(E/K), c q = 0 := by
    refine Fintype.linearIndependent_iff.1 hLI c (funext fun a => ?_)
    simpa [hχapp] using hchar a
  have hs1 : s 1 • x = x := by
    have : π (s 1) = π 1 := by rw [hs, map_one]
    simpa using hwd (s 1) 1 this
  exact hfx (by rw [← hs1]; exact hc0 1)

/-- Helper (no census row): the counit `L ⊗_K V^{Gal(L/K)} → V` is bijective.  This is the
descent half of `thm:galoisdescent` (Speiser's lemma); it is exactly here that continuity of the
`K`-structure is used (clause `RQ2-1.13-H2`, sharpness recorded in census `RQ2-1.24`).  No
finiteness hypothesis (clause `RQ2-1.13-C7`).

@census    none
-/
theorem descentCounit_bijective [IsGalois K L] (X : VecK K L) :
    Function.Bijective (descentCounit K L X) := by
  have hfix : ∀ v : X.carrier,
      (v ∈ (⊤ : Submodule L X.carrier) ∧ ∀ σ : Gal(L/K), σ • v = v)
        ↔ v ∈ fixedPoints K L X := by
    intro v; exact ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩
  constructor
  · -- injectivity: the kernel is a `Gal(L/K)`-stable subspace of `L ⊗_K V^{Gal}`, hence spanned
    -- by its fixed vectors, and those are the `1 ⊗ w` with `w = 0`.
    rw [← LinearMap.ker_eq_bot]
    refine le_antisymm (fun u hu => ?_) bot_le
    have hstable : ∀ (σ : Gal(L/K)) (v : L ⊗[K] (fixedPoints K L X)),
        v ∈ LinearMap.ker (descentCounit K L X) →
          σ • v ∈ LinearMap.ker (descentCounit K L X) := by
      intro σ v hv
      simp only [LinearMap.mem_ker] at hv ⊢
      rw [isKRational_descentCounit K L X σ v, hv, smul_zero]
    have hspan := mem_span_fixed_of_stable K L
      ((baseChangeFunctor K L).obj (ModuleCat.of K (fixedPoints K L X)))
      (LinearMap.ker (descentCounit K L X)) hstable u hu
    have hzero : {v : L ⊗[K] (fixedPoints K L X) |
        v ∈ LinearMap.ker (descentCounit K L X) ∧ ∀ σ : Gal(L/K), σ • v = v}
        ⊆ ((⊥ : Submodule L (L ⊗[K] (fixedPoints K L X))) : Set _) := by
      rintro v ⟨hv1, hv2⟩
      obtain ⟨w, rfl⟩ := exists_one_tmul_of_fixed K L v hv2
      have hw : (w : X.carrier) = 0 := by
        have := (LinearMap.mem_ker).1 hv1
        rwa [descentCounit_tmul, one_smul] at this
      have : w = 0 := Subtype.ext hw
      simp [this]
    have : u ∈ (⊥ : Submodule L (L ⊗[K] (fixedPoints K L X))) :=
      Submodule.span_le.2 hzero hspan
    exact this
  · -- surjectivity: the range is the `L`-span of the fixed vectors, which is everything
    intro y
    have hy : y ∈ Submodule.span L {v : X.carrier |
        v ∈ (⊤ : Submodule L X.carrier) ∧ ∀ σ : Gal(L/K), σ • v = v} :=
      mem_span_fixed_of_stable K L X ⊤ (fun _ _ _ => trivial) y trivial
    have hset : {v : X.carrier | v ∈ (⊤ : Submodule L X.carrier) ∧ ∀ σ : Gal(L/K), σ • v = v}
        = (LinearMap.range ((fixedPoints K L X).subtype.restrictScalars K) : Set X.carrier) := by
      ext v
      simp [fixedPoints]
    rw [hset, ← LinearMap.range_liftBaseChange L] at hy
    exact hy

/-- Helper (no census row): a morphism of `VecK K L` whose underlying `L`-linear map is bijective
is an isomorphism (the inverse map is automatically `K`-rational). -/
private noncomputable def VecK.isoOfBijective {X Y : VecK K L} (f : X ⟶ Y)
    (hf : Function.Bijective f.1) : X ≅ Y where
  hom := f
  inv := ⟨(LinearEquiv.ofBijective f.1 hf).symm, by
    intro σ y
    show (LinearEquiv.ofBijective f.1 hf).symm (σ • y)
        = σ • (LinearEquiv.ofBijective f.1 hf).symm y
    rw [LinearEquiv.symm_apply_eq]
    show σ • y = f.1 (σ • (LinearEquiv.ofBijective f.1 hf).symm y)
    rw [f.2 σ]
    show σ • y = σ • (LinearEquiv.ofBijective f.1 hf) ((LinearEquiv.ofBijective f.1 hf).symm y)
    rw [LinearEquiv.apply_symm_apply]⟩
  hom_inv_id := Subtype.ext (LinearMap.ext fun v =>
    (LinearEquiv.ofBijective f.1 hf).symm_apply_apply v)
  inv_hom_id := Subtype.ext (LinearMap.ext fun v =>
    (LinearEquiv.ofBijective f.1 hf).apply_symm_apply v)

/-- Helper (no census row): naturality of the descent unit `v ↦ 1 ⊗ v`. -/
private theorem descentUnit_naturality [Algebra.IsIntegral K L] {M N : ModuleCat.{u} K}
    (φ : M ⟶ N) (v : M) :
    fixedPointsMap K L ((baseChangeFunctor K L).map φ) (descentUnit K L M v)
      = descentUnit K L N (φ.hom v) :=
  Subtype.ext (LinearMap.baseChange_tmul _ _ _)

/-- Helper (no census row): naturality of the descent counit `α ⊗ v ↦ α · v`. -/
private theorem descentCounit_naturality [Algebra.IsIntegral K L] {X Y : VecK K L} (f : X ⟶ Y)
    (u : L ⊗[K] (fixedPoints K L X)) :
    f.1 (descentCounit K L X u)
      = descentCounit K L Y (LinearMap.baseChange L (fixedPointsMap K L f) u) := by
  induction u with
  | tmul a w =>
      rw [LinearMap.baseChange_tmul, descentCounit_tmul, descentCounit_tmul, fixedPointsMap_coe,
        map_smul]
  | add u v hu hv => simp only [map_add, hu, hv]

/-- Helper (no census row): the descent **unit** `V ≅ (L ⊗_K V)^{Gal(L/K)}`, natural in `V`. -/
private noncomputable def descentUnitIso [IsGalois K L] :
    𝟭 (ModuleCat.{u} K) ≅ baseChangeFunctor K L ⋙ fixedPointsFunctor K L :=
  NatIso.ofComponents
    (fun M => (LinearEquiv.ofBijective (descentUnit K L M)
      (descentUnit_bijective K L M)).toModuleIso)
    (fun φ => by
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun v => (descentUnit_naturality K L φ v).symm)

/-- Helper (no census row): the descent **counit** `L ⊗_K V^{Gal(L/K)} ≅ V`, natural in `V`. -/
private noncomputable def descentCounitIso [IsGalois K L] :
    fixedPointsFunctor K L ⋙ baseChangeFunctor K L ≅ 𝟭 (VecK K L) :=
  NatIso.ofComponents
    (fun X => VecK.isoOfBijective K L
      (⟨descentCounit K L X, isKRational_descentCounit K L X⟩ :
        (fixedPointsFunctor K L ⋙ baseChangeFunctor K L).obj X ⟶ X)
      (descentCounit_bijective K L X))
    (fun f => Subtype.ext (LinearMap.ext fun u =>
      (descentCounit_naturality K L f u).symm))

end Speiser

/-- **Theorem (Galois descent)** (`thm:galoisdescent`, §1.1 of the source).

Let `L/K` be a finite or infinite Galois extension (clauses `RQ2-1.13-H1`, `RQ2-1.13-C6`).  The
category `Vec_K` of **all** `K`-vector spaces is equivalent (clause `RQ2-1.13-C2`), via the functor
`V ↦ (L ⊗_K V, (φ_σ)_σ)` (clause `RQ2-1.13-C1`), to the category of **all** `L`-vector spaces with
a `K`-structure — the defining semi-linear action of `Gal(L/K)` being continuous, as required by
the definition of a `K`-structure (clauses `RQ2-1.13-H2`, `RQ2-1.13-C3`) — and `K`-rational maps as
morphisms (clause `RQ2-1.13-C4`).  A quasi-inverse functor is given by
`(V,(φ_σ)_σ) ↦ V^{Gal(L/K)} = {v | ∀ σ, φ_σ(v) = v}` (clause `RQ2-1.13-C5`).

There is **no finite-dimensionality hypothesis on either side** (clause `RQ2-1.13-C7`):
`ModuleCat.{u} K` and `VecK K L` range over all `K`-vector spaces resp. all `L`-vector spaces
with a `K`-structure.

@census    RQ2-1.13
@source    thm:galoisdescent
@clauses   RQ2-1.13-H1, RQ2-1.13-H2, RQ2-1.13-C1, RQ2-1.13-C2, RQ2-1.13-C3, RQ2-1.13-C4, RQ2-1.13-C5, RQ2-1.13-C6, RQ2-1.13-C7
@imports   none
@divergence none
-/
theorem galoisDescent [IsGalois K L] :
    ∃ e : ModuleCat.{u} K ≌ VecK K L,
      e.functor = baseChangeFunctor K L ∧ e.inverse = fixedPointsFunctor K L :=
  ⟨CategoryTheory.Equivalence.mk (baseChangeFunctor K L) (fixedPointsFunctor K L)
      (descentUnitIso K L) (descentCounitIso K L), rfl, rfl⟩

section NonVacuity

/-- **G5 non-vacuity** (`WORKFLOW.md` §4/G5): `L` itself, with its tautological `K`-structure
(`kStructure_self`), is an object of `VecK K L`.  It is *non-degenerate*: its carrier is
nontrivial (see `selfObj_nontrivial`), so `VecK K L` is not the category with only a zero object.

@census    none
-/
def selfObj [Algebra.IsIntegral K L] : VecK K L := { carrier := L }

/-- **G5 non-vacuity**: the witness `selfObj` is not the zero object. -/
theorem selfObj_nontrivial [Algebra.IsIntegral K L] : Nontrivial (selfObj K L).carrier :=
  inferInstanceAs (Nontrivial L)

/-- **G5 non-vacuity**: the base-change functor produces objects of `VecK K L` — in particular
`L ⊗_K K ≅ L` is in its image, so the source category of `galoisDescent` is not empty either. -/
example [Algebra.IsIntegral K L] : Nonempty (VecK K L) :=
  ⟨(baseChangeFunctor K L).obj (ModuleCat.of K K)⟩

/-!
### Non-degeneracy: the descent equivalence is not the identity in disguise

`DESIGN-NOTES.md` §11 probes 2–4 (G4 finding **C-2**).  `KStructure.lean` supplies the general
moving-action lemma `exists_smul_ne_self`, the criterion `nontrivial_gal_of_not_finiteDimensional`
and the infinite model `𝔽̄₂/𝔽₂`; here they are turned into statements about `selfObj` and
`fixedPoints`, and instantiated at two concrete extensions — the quadratic `ℂ/ℝ` and the infinite
`𝔽̄₂/𝔽₂`.
-/

/-- **G5 non-vacuity, probe 2**: on the tautological object `selfObj K L` the `Gal(L/K)`-action
genuinely moves a vector, as soon as the Galois group is non-trivial.

@census    none (G5 non-degeneracy witness)
-/
theorem exists_smul_ne_self_selfObj [Algebra.IsIntegral K L] [Nontrivial Gal(L/K)] :
    ∃ (σ : Gal(L/K)) (v : (selfObj K L).carrier), σ • v ≠ v :=
  exists_smul_ne_self K L

/-- **G5 non-vacuity, probe 3**: the fixed-point space of `selfObj K L` is a **proper** subspace,
`L^{Gal(L/K)} ≠ L`.  Hence `fixedPointsFunctor` is not the identity functor in disguise and the
descent equivalence of `galoisDescent` genuinely changes the object.

@census    none (G5 non-degeneracy witness)
-/
theorem fixedPoints_selfObj_ne_top [Algebra.IsIntegral K L] [Nontrivial Gal(L/K)] :
    fixedPoints K L (selfObj K L) ≠ ⊤ := by
  intro htop
  obtain ⟨σ, v, hv⟩ := exists_smul_ne_self_selfObj K L
  exact hv (((mem_fixedPoints K L).mp (htop ▸ Submodule.mem_top)) σ)

end NonVacuity

section ConcreteModels

/-- `ℂ/ℝ` is Galois (`IsAlgClosure.isGalois`, `CharZero ℝ`).  Deliberately **not** an instance —
in the spirit of `CONVENTIONS.md` §5 this file adds no global instance about mathlib's own types;
use `haveI`.
Duplicated, by design, in `Quiver/Models.lean` — `Quiver/` is a *higher* layer than `Descent/` and
must not be imported here, and `CONVENTIONS.md` §1 requires the two stages' module sets to be
disjoint.

@census    none (G5 concrete model)
-/
theorem isGalois_real_complex : IsGalois ℝ ℂ :=
  haveI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  inferInstance

/-- `Gal(ℂ/ℝ)` is non-trivial: it has exactly two elements, `1` and complex conjugation
(`IsGalois.card_aut_eq_finrank` with `Complex.finrank_real_complex`).

@census    none (G5 concrete model: probe 1 of `DESIGN-NOTES.md` §11)
-/
theorem nontrivial_gal_complex_real : Nontrivial Gal(ℂ/ℝ) := by
  haveI := isGalois_real_complex
  have h : Nat.card Gal(ℂ/ℝ) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]
  obtain ⟨z, hz, -⟩ := (Nat.card_eq_two_iff' (1 : Gal(ℂ/ℝ))).mp h
  exact ⟨z, 1, hz⟩

/-- **G5 non-vacuity, probe 2 at a concrete extension**: complex conjugation moves a complex
number.  Every witness in this file is now realised at an `L/K` with `K ≠ L`. -/
example : ∃ (σ : Gal(ℂ/ℝ)) (v : (selfObj ℝ ℂ).carrier), σ • v ≠ v :=
  haveI := nontrivial_gal_complex_real
  exists_smul_ne_self_selfObj ℝ ℂ

/-- **G5 non-vacuity, probe 3 at a concrete extension**: `ℂ^{Gal(ℂ/ℝ)}` is a proper subspace of
`ℂ`.  (It *is* `ℝ`; only properness — which is what probe 3 asks — is proved.) -/
example : fixedPoints ℝ ℂ (selfObj ℝ ℂ) ≠ ⊤ :=
  haveI := nontrivial_gal_complex_real
  fixedPoints_selfObj_ne_top ℝ ℂ

/-- **G5 non-vacuity, probe 4**: the infinite Galois extension `𝔽̄₂/𝔽₂` supplies an object of
`VecK`.  Clause `RQ2-1.13-C6`'s infinite branch now has a model. -/
noncomputable example : VecK F2 F2Bar := selfObj F2 F2Bar

/-- **G5 non-vacuity, probes 3 + 4**: at the infinite extension the fixed-point space is proper
too.  (It *is* `𝔽₂`; again only properness is proved.) -/
example : fixedPoints F2 F2Bar (selfObj F2 F2Bar) ≠ ⊤ :=
  haveI := nontrivial_gal_algClosure_two
  fixedPoints_selfObj_ne_top F2 F2Bar

end ConcreteModels

end RationalQuivers.Descent
