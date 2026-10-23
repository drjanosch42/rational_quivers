import RationalQuivers.Quiver.Rep.Nilpotent
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Quiver-side base change for an arbitrary extension

Stage **S10**, prerequisite **(iii)** of census row `RQ-5.08` (`rmk:generalbases`); coordinator
rulings `R-S10-3` (the `qBC_*` binder reshape) and `R-S10-8` (module set).

S2's `Quiver/Rep/BaseChange.lean` is the `RQ2-1.11` base change: it moves along an intermediate
field `L/E'/K` of **one** Galois extension, and is `rfl`-cheap because base change there *is*
restriction of the Galois action — the `L`-spaces `M(v)` do not change.  `RQ-5.08-C4` needs
something different: the splitting field itself moves (`E(√-1) → E''(√-1)`), so the spaces really
are tensored up.

## What is built here

`Rep.toSplit`: base change onto a **split** target.  For `M` a `K`-rational representation of `Γ`
with splitting field `L`, and any extension `L → K''`, the family `K'' ⊗_L M(v)` with the
base-changed edge maps and the trivial `Gal(K''/K'')`-action is a `K''`-rational representation of
`splitOf K'' Γ.toRQuiver`.  One construction covers **two** of `RQ-5.08-C4`'s three shapes:

* `ss` (`√-1 ∈ E`, `√-1 ∈ E''`) at `L = K = E`, `K'' = E''`;
* `ns` (`√-1 ∉ E`, `√-1 ∈ E''`) at `L = E(√-1)`, `K'' = E''` — the descent datum of the
  `E`-rational representation is *forgotten*, which is exactly right because the target is split.

Nilpotency survives (`Rep.toSplit_isNilpotent`), because `pathCompose` depends only on the
classical quiver, the family and the edge maps (`pathCompose_baseChange`), and
finite-dimensionality survives by `Module.Finite.base_change`.  `RepNil.toSplitFunctor` is the
resulting functor on `Rep^nil`.

## What is NOT built here

The **`nn`** shape — `Rep^nil(Γ_E) ⥤ Rep^nil(Γ_{E''})` with *both* fields non-split — is not
constructed.  It is the one shape where the semi-linear structure maps must be carried, not
forgotten: `φ''_{v,σ}(a ⊗ m) = σ(a) ⊗ φ_{v,θσ}(m)` for the induced
`θ : Gal(E''(√-1)/E'') → Gal(E(√-1)/E)`, a semi-linear map on a tensor product.  `RQ-5.08`'s
`C4a` states its existence as a conclusion; the construction is owed.  See
`workflow/stages/S10/DESIGN-NOTES.md` §3 and `RESULTS.md` for the measurement.

## Main definitions / results

* `RationalQuivers.RationalQuiver.splitOf` — the split rational quiver on a classical quiver;
  `Gelfand.gelfandSplit` and `Gelfand.cyclicSplit` are instances of it, definitionally.
* `arrowCompose_baseChange`, `pathCompose_baseChange` — path composites commute with base change.
* `Rep.toSplit`, `Rep.Hom.toSplit`, `Rep.toSplit_isNilpotent`, `FDRep.toSplit`.
* `RepNil.toSplitFunctor` — the functor `Rep^nil(Γ) ⥤ Rep^nil(split_{K''} Γ)`.
-/

universe u

namespace RationalQuivers

namespace RationalQuiver

open CategoryTheory
open scoped TensorProduct

/-! ## The split rational quiver on a classical quiver -/

/-- The trivial action is smooth.  @census none (helper) -/
theorem isSmooth_one {G X : Type u} [Group G] [TopologicalSpace G] :
    IsSmooth (1 : G →* Equiv.Perm X) := fun x => by simp

/-- The **split** `K`-rational quiver on a classical quiver `Γ`: `Γ` with the trivial
`Gal(K/K)`-action.  `Gelfand.gelfandSplit E` and `Gelfand.cyclicSplit E` are this at
`Γ = RQuiver.gelfand` resp. `RQuiver.cyclic`, definitionally.

@census none (helper) -/
def splitOf (K : Type u) [Field K] (Γ : RQuiver.{u}) : RationalQuiver K K :=
  ofAction K K Γ 1 1 (fun _ _ => rfl) (fun _ _ => rfl) isSmooth_one isSmooth_one

variable {K : Type u} [Field K] {Γ : RQuiver.{u}}

@[simp] theorem splitOf_toRQuiver : (splitOf K Γ).toRQuiver = Γ := rfl

@[simp] theorem splitOf_smul_V (σ : Gal(K/K)) (v : (splitOf K Γ).V) : σ • v = v := rfl

@[simp] theorem splitOf_smul_E (σ : Gal(K/K)) (e : (splitOf K Γ).E) : σ • e = e := rfl

/-- `Gal(K/K)` acts trivially on `K`.  @census none (helper) -/
theorem galSelf_apply' (σ : Gal(K/K)) (a : K) : σ a = a := by simpa using σ.commutes a

/-! ## Base change of path composites -/

/-- **Arrow composites commute with base change.**  @census none (helper) -/
theorem arrowCompose_baseChange {L L'' : Type u} [Field L] [Field L''] [Algebra L L'']
    {Q : RQuiver.{u}} (X : Q.V → Type u) [∀ v, AddCommGroup (X v)] [∀ v, Module L (X v)]
    (f : ∀ e : Q.E, X (Q.source e) →ₗ[L] X (Q.target e)) {a b : Q.V} (g : a ⟶ b) :
    arrowCompose (L := L'') (fun v => L'' ⊗[L] X v)
        (fun e => LinearMap.baseChange L'' (f e)) g
      = LinearMap.baseChange L'' (arrowCompose X f g) := by
  obtain ⟨e, h1, h2⟩ := g
  cases h1
  cases h2
  rfl

/-- **Path composites commute with base change.**  This is what makes nilpotency survive base
change: `pathCompose` depends only on the classical quiver, the family and the edge maps.

@census none (helper) -/
theorem pathCompose_baseChange {L L'' : Type u} [Field L] [Field L''] [Algebra L L'']
    {Q : RQuiver.{u}} (X : Q.V → Type u) [∀ v, AddCommGroup (X v)] [∀ v, Module L (X v)]
    (f : ∀ e : Q.E, X (Q.source e) →ₗ[L] X (Q.target e)) {a b : Q.V} (p : Quiver.Path a b) :
    pathCompose (L := L'') (fun v => L'' ⊗[L] X v)
        (fun e => LinearMap.baseChange L'' (f e)) p
      = LinearMap.baseChange L'' (pathCompose X f p) := by
  induction p with
  | nil => simp
  | cons p g ih =>
      rw [pathCompose_cons, pathCompose_cons, ih, arrowCompose_baseChange,
        ← LinearMap.baseChange_comp]

/-! ## Base change onto a split target -/

namespace Rep

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {Γ : RationalQuiver K L}
variable (K'' : Type u) [Field K''] [Algebra L K'']

/-- **Base change onto a split target.**  For a `K`-rational representation `M` of `Γ` with
splitting field `L`, and any field extension `L → K''`, the family `K'' ⊗_L M(v)` with the
base-changed edge maps and the **trivial** `Gal(K''/K'')`-action is a `K''`-rational representation
of the split quiver on `Γ`'s underlying classical quiver.

This is the shape both the `ss` and the `ns` case of `RQ-5.08-C4` need: `ss` at `L = K = E`,
`K'' = E''`; `ns` at `L = E(√-1)`, `K'' = E''` with `√-1 ∈ E''`, where the descent datum of the
`E`-rational representation is forgotten because the target is split.

@census none (helper; `RQ-5.08-C4`'s quiver-side arrow, split target) -/
def toSplit (M : Rep Γ) : Rep (splitOf K'' Γ.toRQuiver) where
  M v := K'' ⊗[L] M.M v
  φ _ _ := AddEquiv.refl _
  semilinear σ v a m := by
    show a • ((AddEquiv.refl (K'' ⊗[L] M.M v)) m) = σ a • _
    rw [galSelf_apply' σ a]
    rfl
  cocycle _ _ _ _ := rfl
  smooth _ := isOpen_discrete _
  φEdge e := LinearMap.baseChange K'' (M.φEdge e)
  edge_equivariance σ e m m' h := by
    have hm : m' = m := by
      simp only [splitOf_smul_E, splitOf_smul_V, Sigma.mk.injEq, heq_eq_eq, true_and] at h
      exact h
    subst hm
    rfl

/-- Base change onto a split target, on morphisms.  @census none (helper) -/
def Hom.toSplit {M N : Rep Γ} (f : Rep.Hom M N) :
    Rep.Hom (M.toSplit K'') (N.toSplit K'') where
  ψ v := LinearMap.baseChange K'' (f.ψ v)
  edge e m := by
    have h : (f.ψ (Γ.toRQuiver.target e)) ∘ₗ M.φEdge e
        = N.φEdge e ∘ₗ (f.ψ (Γ.toRQuiver.source e)) := LinearMap.ext (f.edge e)
    have h2 := congrArg (LinearMap.baseChange K'') h
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h2
    exact congrArg (fun g : (K'' ⊗[L] M.M (Γ.toRQuiver.source e)) →ₗ[K'']
      (K'' ⊗[L] N.M (Γ.toRQuiver.target e)) => g m) h2
  rational _ _ _ := rfl

/-- Path composites of the split base change.  @census none (helper) -/
theorem pathMap_toSplit (M : Rep Γ) {a b : Γ.V} (p : Quiver.Path a b) :
    (M.toSplit K'').pathMap p = LinearMap.baseChange K'' (M.pathMap p) :=
  pathCompose_baseChange (L'' := K'') M.M M.φEdge p

/-- **Any relation between path composites survives base change onto a split target.**  This is
what carries `ex:gelfand`'s relation `a₋b₋ = a₊b₊` along `RQ-5.08-C4`'s quiver-side arrows, and so
what lets `C4b`'s squares be stated between the **relation-carrying** categories `RQ-5.02`/`RQ-5.05`
actually prove equivalences onto.

@census none (helper; `RQ-5.08-C4`) -/
theorem toSplit_pathMap_congr (M : Rep Γ) {a b : Γ.V} (p q : Quiver.Path a b)
    (h : M.pathMap p = M.pathMap q) :
    (M.toSplit K'').pathMap p = (M.toSplit K'').pathMap q := by
  rw [pathMap_toSplit, pathMap_toSplit, h]

/-- **Nilpotency survives base change onto a split target.**  @census none (helper) -/
theorem toSplit_isNilpotent {M : Rep Γ} (h : M.IsNilpotent) : (M.toSplit K'').IsNilpotent := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, fun a b p hp => ?_⟩
  have h1 : (M.toSplit K'').pathMap p = LinearMap.baseChange K'' (M.pathMap p) :=
    pathMap_toSplit K'' M p
  have h2 : M.pathMap p = 0 := hn a b p hp
  show (M.toSplit K'').pathMap p = 0
  rw [h1, h2]
  exact LinearMap.baseChange_zero

end Rep

namespace FDRep

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {Γ : RationalQuiver K L}
variable (K'' : Type u) [Field K''] [Algebra L K'']

/-- Base change onto a split target preserves finite-dimensionality.  @census none (helper) -/
def toSplit (M : FDRep Γ) : FDRep (splitOf K'' Γ.toRQuiver) where
  toRep := M.toRep.toSplit K''
  finiteDimensional v := by
    haveI := M.finiteDimensional v
    exact Module.Finite.base_change L K'' (M.toRep.M v)

end FDRep

namespace RepNil

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {Γ : RationalQuiver K L}
variable (K'' : Type u) [Field K''] [Algebra L K'']

/-- **The quiver-side base-change functor onto a split target**, `M ↦ K'' ⊗_L M`, for an
**arbitrary** extension `L → K''`.  Constructed, not assumed: `RQ-5.08-C4a`'s quiver-side arrow in
the `ss` and `ns` shapes.

@census none (helper; `RQ-5.08-C4`) -/
def toSplitFunctor :
    (RepNil Γ).FullSubcategory ⥤ (RepNil (splitOf K'' Γ.toRQuiver)).FullSubcategory where
  obj M := ⟨(M.obj.toSplit K'' : FDRep (splitOf K'' Γ.toRQuiver)),
    Rep.toSplit_isNilpotent K'' M.property⟩
  map f := ⟨Rep.Hom.toSplit K'' f.hom⟩
  map_id _ := by
    apply CategoryTheory.ObjectProperty.hom_ext
    apply Rep.Hom.ext
    funext v
    show LinearMap.baseChange K'' LinearMap.id = _
    rw [LinearMap.baseChange_id]
    rfl
  map_comp _ _ := by
    apply CategoryTheory.ObjectProperty.hom_ext
    apply Rep.Hom.ext
    funext v
    show LinearMap.baseChange K'' (_ ∘ₗ _) = _
    rw [LinearMap.baseChange_comp]
    rfl

end RepNil

end RationalQuiver

end RationalQuivers
