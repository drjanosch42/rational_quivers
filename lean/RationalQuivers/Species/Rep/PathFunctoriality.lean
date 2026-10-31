module

public import RationalQuivers.Species.Rep.Relations
public import RationalQuivers.Species.BaseChange

@[expose] public section

/-!
# Functoriality of length-two path bimodules (stage T6, T4-B)

Path bimodules `{}_{i_0}M_p` (`def:speciesrelations`, clause `RQ2-2.36-C1`, `Species/Rep/Relations.lean`) are functorial
in two ways:
* along a **morphism** of étale `K`-species `f : S ⟶ T` (`RQ2-2.04`; index map backwards, algebra maps forwards), and
* along **base change** `S ↦ S ⊗_K N` (`def:basechangeforspecies`, `RQ2-2.05`).

Both are cases of one datum, `EtaleSpecies.PathDatum S T`, a map of étale species over a field map `K → N`. Such a datum
induces `x ⊗ y ↦ onM x ⊗ onM y` on length-two path bimodules (`PathDatum.pathMap`). That map is semilinear over `K → N`.

* **B1**: `EtaleSpecies.pathMapHom f idx : {}M_{f^*idx}(S) →ₗ[K] {}M_idx(T)`, with `pathMapHom_id`, `pathMapHom_comp`.
* **B2**: `EtaleSpecies.pathBaseChange S N idx : N ⊗_K {}M_{π∘idx}(S) →ₗ[N] {}M_idx(S ⊗_K N)`, `n ⊗ (x ⊗ y) ↦ n·(ιx ⊗ ιy)`.

Only length two (`pathBimod … 1`) is built. It is the length at which the relations of `ex:gelfandspeciesrelation` live
(`GelfandRelation.RGelfand` is `⊥` at every other length). Consumer: `Gelfand/Species/RelationBaseChange.lean`
(`RQ2-5.16-C4`).

@census none (module; stage T6, AUTHOR-QUEUE T4-B, authorization 2026-10-18 part C)
-/

universe u

namespace RationalQuivers

open scoped TensorProduct
open CategoryTheory

namespace EtaleSpecies

variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N]

/-- A map of étale species over the field map `K → N`: an index map `T.I → S.I` and ring maps on vertex fields and
edge algebras, compatible with both structure maps and with `K → N`. A morphism of étale `K`-species
(`PathDatum.ofHom`) and the base-change map `S → S ⊗_K N` (`PathDatum.baseChange`) are instances.

@census none (helper; T4-B) -/
structure PathDatum (S : EtaleSpecies.{u} K) (T : EtaleSpecies.{u} N) : Type u where
  /-- the index map, backwards -/
  onI : T.I → S.I
  /-- the vertex maps -/
  onL : ∀ t, S.L (onI t) →+* T.L t
  /-- the edge maps -/
  onM : ∀ s t, S.M (onI s) (onI t) →+* T.M s t
  /-- compatibility with the left structure maps -/
  compat_left : ∀ s t (a : S.L (onI s)), onM s t (S.left _ _ a) = T.left s t (onL s a)
  /-- compatibility with the right structure maps -/
  compat_right : ∀ s t (a : S.L (onI t)), onM s t (S.right _ _ a) = T.right s t (onL t a)
  /-- compatibility with `K → N` -/
  onM_algebraMap : ∀ s t (c : K),
    onM s t (algebraMap K (S.M (onI s) (onI t)) c) = algebraMap N (T.M s t) (algebraMap K N c)

/-- The length-two path bimodule `{}_{i_0}M_{i_1} ⊗_{L_{i_1}} {}_{i_1}M_{i_2}` of an étale species, with the instances of
`EtaleSpecies`; it is `(pathBimod S.toSpecies idx 1).carrier` by `rfl` (`pathBimod_one_eq`).  @census none (helper) -/
abbrev P2 (S : EtaleSpecies.{u} K) (i0 i1 i2 : S.I) : Type u :=
  Balanced K (S.L i1) (S.L i2) (S.M i1 i2) (S.M i0 i1)

set_option backward.isDefEq.respectTransparency.types false in
/-- `P2` is the path bimodule of `def:speciesrelations` at the path `(idx 0, idx 1, idx 2)`.  @census none (helper) -/
theorem pathBimod_one_eq (S : EtaleSpecies.{u} K) (idx : ℕ → S.I) :
    (Species.pathBimod S.toSpecies idx 1).carrier = P2 S (idx 0) (idx 1) (idx 2) := rfl

/-- A `N`-module as a `K`-module through `K → N` (local; used only to build maps).  @census none (helper) -/
@[reducible] noncomputable def moduleKOf (W : Type u) [AddCommGroup W] [Module N W] : Module K W :=
  Module.compHom W (algebraMap K N)

namespace PathDatum

variable {S : EtaleSpecies.{u} K} {T : EtaleSpecies.{u} N} (F : PathDatum S T)

/-- `onM` is semilinear over `K → N`.  @census none (helper) -/
theorem onM_smul (s t) (c : K) (m : S.M (F.onI s) (F.onI t)) :
    F.onM s t (c • m) = algebraMap K N c • F.onM s t m := by
  rw [Algebra.smul_def, map_mul, F.onM_algebraMap, ← Algebra.smul_def]

/-- `onM` carries the right action of `L_{ι t}` to the right action of `L'_t` through `onL`.  @census none (helper) -/
theorem onM_op_smul (s t) (a : S.L (F.onI t)) (m : S.M (F.onI s) (F.onI t)) :
    F.onM s t (MulOpposite.op a • m) = MulOpposite.op (F.onL t a) • F.onM s t m := by
  rw [smul_right_def, smul_right_def, map_mul, F.compat_right]; rfl

/-- `onM` carries the left action of `L_{ι s}` to the left action of `L'_s` through `onL`.  @census none (helper) -/
theorem onM_smul_left (s t) (a : S.L (F.onI s)) (m : S.M (F.onI s) (F.onI t)) :
    F.onM s t (a • m) = F.onL s a • F.onM s t m := by
  rw [smul_left_def, smul_left_def, map_mul, F.compat_left]

section PathMap

variable (i0 i1 i2 : T.I)

/-- The `K`-bilinear map `(y, x) ↦ onM x ⊗ onM y` behind `pathMap`.  @census none (helper) -/
noncomputable def pathBil :
    letI := moduleKOf (K := K) (N := N) (P2 T i0 i1 i2)
    S.M (F.onI i1) (F.onI i2) →ₗ[K] S.M (F.onI i0) (F.onI i1) →ₗ[K] P2 T i0 i1 i2 :=
  letI := moduleKOf (K := K) (N := N) (P2 T i0 i1 i2)
  LinearMap.mk₂ K
    (fun y x => (Balanced.mk (K := N) (A := T.L i1) (B := T.L i2)
      (F.onM i0 i1 x) (F.onM i1 i2 y) : P2 T i0 i1 i2))
    (fun y y' x => by rw [map_add]; exact Balanced.mk_add_right _ _ _)
    (fun c y x => by
      show _ = (algebraMap K N c • (Balanced.mk (K := N) (A := T.L i1) (B := T.L i2) _ _ : P2 T i0 i1 i2))
      rw [F.onM_smul]
      rfl)
    (fun y x x' => by rw [map_add]; exact Balanced.mk_add_left _ _ _)
    (fun c y x => by
      show _ = (algebraMap K N c • (Balanced.mk (K := N) (A := T.L i1) (B := T.L i2) _ _ : P2 T i0 i1 i2))
      rw [F.onM_smul, Balanced.mk_smul_K_cross]
      rfl)

/-- **The map induced by `F` on the length-two path bimodule**, `x ⊗ y ↦ onM x ⊗ onM y`, semilinear over `K → N`:
`{}M_{(ι i₀, ι i₁, ι i₂)}(S) → {}M_{(i₀, i₁, i₂)}(T)`. It is well defined because `onM` intertwines the two
`L_{ι i₁}`-actions through `onL` (`compat_left`/`compat_right`).  @census none (helper; T4-B) -/
noncomputable def pathMap :
    P2 S (F.onI i0) (F.onI i1) (F.onI i2) →ₛₗ[algebraMap K N] P2 T i0 i1 i2 :=
  letI := moduleKOf (K := K) (N := N) (P2 T i0 i1 i2)
  let g := Balanced.liftK (A := S.L (F.onI i1)) (B := S.L (F.onI i2)) (F.pathBil i0 i1 i2)
    (fun a y x => by
      show Balanced.mk (K := N) (A := T.L i1) (B := T.L i2) (F.onM i0 i1 x) (F.onM i1 i2 (a • y)) =
        Balanced.mk (F.onM i0 i1 (MulOpposite.op a • x)) (F.onM i1 i2 y)
      rw [F.onM_op_smul, F.onM_smul_left, Balanced.mk_smul])
  { toFun := g
    map_add' := g.map_add
    map_smul' := g.map_smul }

/-- `pathMap` on pure tensors (`rfl`).  @census none (value guard) -/
@[simp] theorem pathMap_mk (x : S.M (F.onI i0) (F.onI i1)) (y : S.M (F.onI i1) (F.onI i2)) :
    F.pathMap i0 i1 i2 (Balanced.mk x y) =
      Balanced.mk (K := N) (A := T.L i1) (B := T.L i2) (F.onM i0 i1 x) (F.onM i1 i2 y) := rfl

/-- The `N`-linear extension `N ⊗_K {}M(S) → {}M(T)`, `n ⊗ z ↦ n · pathMap z`.  @census none (helper; T4-B) -/
noncomputable def pathLift :
    N ⊗[K] P2 S (F.onI i0) (F.onI i1) (F.onI i2) →ₗ[N] P2 T i0 i1 i2 :=
  letI := moduleKOf (K := K) (N := N) (P2 T i0 i1 i2)
  haveI : IsScalarTower K N (P2 T i0 i1 i2) :=
    ⟨fun c n w => by
      show (c • n) • w = algebraMap K N c • n • w
      rw [Algebra.smul_def, mul_smul]⟩
  LinearMap.liftBaseChange N
    { toFun := F.pathMap i0 i1 i2
      map_add' := map_add _
      map_smul' := (F.pathMap i0 i1 i2).map_smulₛₗ }

/-- `pathLift` on pure tensors.  @census none (value guard) -/
@[simp] theorem pathLift_tmul (n : N) (z : P2 S (F.onI i0) (F.onI i1) (F.onI i2)) :
    F.pathLift i0 i1 i2 (n ⊗ₜ z) = n • F.pathMap i0 i1 i2 z := by
  simp [pathLift, LinearMap.liftBaseChange_tmul]

end PathMap

end PathDatum

/-! ### B1: morphisms of étale species -/

section Hom

variable {S T U : EtaleSpecies.{u} K}

/-- A morphism of étale `K`-species (`RQ2-2.04`) as a `PathDatum` over `K → K`.  @census none (helper; T4-B) -/
def PathDatum.ofHom (f : S ⟶ T) : PathDatum S T where
  onI := f.onI
  onL t := (f.onL t).toRingHom
  onM s t := (f.onM s t).toRingHom
  compat_left s t a := AlgHom.congr_fun (f.compat_left s t) a
  compat_right s t a := AlgHom.congr_fun (f.compat_right s t) a
  onM_algebraMap s t c := (f.onM s t).commutes c

/-- **B1.** The `K`-linear map induced by a morphism `f : S ⟶ T` of étale `K`-species on length-two path bimodules,
`{}M_{(f i₀, f i₁, f i₂)}(S) → {}M_{(i₀, i₁, i₂)}(T)`, `x ⊗ y ↦ f(x) ⊗ f(y)`.
@census none (helper; T4-B, plan piece B1) -/
noncomputable def pathMapHom (f : S ⟶ T) (i0 i1 i2 : T.I) :
    P2 S (f.onI i0) (f.onI i1) (f.onI i2) →ₗ[K] P2 T i0 i1 i2 where
  toFun := (PathDatum.ofHom f).pathMap i0 i1 i2
  map_add' := map_add _
  map_smul' := ((PathDatum.ofHom f).pathMap i0 i1 i2).map_smulₛₗ

/-- B1 on pure tensors (`rfl`).  @census none (value guard) -/
@[simp] theorem pathMapHom_mk (f : S ⟶ T) (i0 i1 i2 : T.I) (x : S.M (f.onI i0) (f.onI i1))
    (y : S.M (f.onI i1) (f.onI i2)) :
    pathMapHom f i0 i1 i2 (Balanced.mk x y) =
      Balanced.mk (K := K) (A := T.L i1) (B := T.L i2) (f.onM i0 i1 x) (f.onM i1 i2 y) := rfl

/-- B1 is functorial: the identity induces the identity.  @census none (helper; T4-B) -/
theorem pathMapHom_id (i0 i1 i2 : S.I) : pathMapHom (𝟙 S) i0 i1 i2 = LinearMap.id :=
  Balanced.hom_extK fun _ _ => rfl

/-- B1 is functorial: `(f ≫ g)_* = g_* ∘ f_*`.  @census none (helper; T4-B) -/
theorem pathMapHom_comp (f : S ⟶ T) (g : T ⟶ U) (i0 i1 i2 : U.I) :
    pathMapHom (f ≫ g) i0 i1 i2 =
      (pathMapHom g i0 i1 i2).comp (pathMapHom f (g.onI i0) (g.onI i1) (g.onI i2)) :=
  Balanced.hom_extK fun _ _ => rfl

end Hom

namespace PathDatum

/-! ### B2: base change -/

section BaseChange

variable (S : EtaleSpecies.{u} K) (N)

/-- `L_{π k} → L'_k`, `a ↦ pr_k(1 ⊗ a)`.  @census none (helper; T4-B) -/
noncomputable def bcOnL (k : S.baseChangeIndex N) : S.L (S.fibreMap N k) →+* S.baseChangeField N k :=
  (S.baseChangeProj N k).toRingHom.comp
    (Algebra.TensorProduct.includeRight : S.L (S.fibreMap N k) →ₐ[K] N ⊗[K] S.L (S.fibreMap N k)).toRingHom

/-- `{}_{π k}M_{π l} → {}_kM'_l`, `m ↦ 1 ⊗ ((1 ⊗ m) ⊗ 1)`.  @census none (helper; T4-B) -/
noncomputable def bcOnM (k l : S.baseChangeIndex N) :
    S.M (S.fibreMap N k) (S.fibreMap N l) →+* (S.baseChangeEdge N k l).carrier :=
  letI := S.algRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerRightEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N l
  letI := S.towerVertexField N l
  letI := S.algLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.towerLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.smulCommEdge N (S.fibreMap N k) (S.fibreMap N l)
  letI := S.algVertexField N k
  letI := S.towerVertexField N k
  ((Algebra.TensorProduct.includeRight :
      ((S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l))
        →ₐ[S.vertexAlg N (S.fibreMap N k)] (S.baseChangeField N k) ⊗[S.vertexAlg N (S.fibreMap N k)]
          ((S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) ⊗[S.vertexAlg N (S.fibreMap N l)]
            (S.baseChangeField N l))).toRingHom.comp
    (Algebra.TensorProduct.includeLeft :
      S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l) →ₐ[S.vertexAlg N (S.fibreMap N k)]
        (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) ⊗[S.vertexAlg N (S.fibreMap N l)]
          (S.baseChangeField N l)).toRingHom).comp
    (Algebra.TensorProduct.includeRight :
      S.M (S.fibreMap N k) (S.fibreMap N l) →ₐ[K] N ⊗[K] S.M (S.fibreMap N k) (S.fibreMap N l)).toRingHom

/-- The base-change map `S → S ⊗_K N` as a `PathDatum` over `K → N` (`def:basechangeforspecies`, `RQ2-2.05`).
@census none (helper; T4-B) -/
noncomputable def baseChange : PathDatum S (S.baseChange N) where
  onI := S.fibreMap N
  onL := bcOnL N S
  onM := bcOnM N S
  compat_left k l a := by
    letI := S.algRightEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.towerRightEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.towerVertexField N l
    letI := S.algLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.towerLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.smulCommEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.algVertexField N k
    letI := S.towerVertexField N k
    change (1 : S.baseChangeField N k) ⊗ₜ[S.vertexAlg N (S.fibreMap N k)]
        ((((1 : N) ⊗ₜ[K] S.left _ _ a : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))) ⊗ₜ[S.vertexAlg N (S.fibreMap N l)]
          (1 : S.baseChangeField N l)) =
      (algebraMap (S.vertexAlg N (S.fibreMap N k)) (S.baseChangeField N k) ((1 : N) ⊗ₜ[K] a)) ⊗ₜ[S.vertexAlg N (S.fibreMap N k)]
        (1 : (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l))
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, Algebra.TensorProduct.algebraMap_apply]
    rfl
  compat_right k l a := by
    letI := S.algRightEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.towerRightEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.towerVertexField N l
    letI := S.algLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.towerLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.smulCommEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.algVertexField N k
    letI := S.towerVertexField N k
    change (1 : S.baseChangeField N k) ⊗ₜ[S.vertexAlg N (S.fibreMap N k)]
        ((((1 : N) ⊗ₜ[K] S.right _ _ a : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l))) ⊗ₜ[S.vertexAlg N (S.fibreMap N l)]
          (1 : S.baseChangeField N l)) =
      (1 : S.baseChangeField N k) ⊗ₜ[S.vertexAlg N (S.fibreMap N k)]
        ((1 : S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) ⊗ₜ[S.vertexAlg N (S.fibreMap N l)]
          (algebraMap (S.vertexAlg N (S.fibreMap N l)) (S.baseChangeField N l) ((1 : N) ⊗ₜ[K] a)))
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rfl
  onM_algebraMap k l c := by
    letI := S.algRightEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.towerRightEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.algVertexField N l
    letI := S.towerVertexField N l
    letI := S.algLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.towerLeftEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.smulCommEdge N (S.fibreMap N k) (S.fibreMap N l)
    letI := S.algVertexField N k
    letI := S.towerVertexField N k
    have h1 : ((1 : N) ⊗ₜ[K] algebraMap K (S.M (S.fibreMap N k) (S.fibreMap N l)) c) =
        algebraMap N (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) (algebraMap K N c) := by
      rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self_apply]
    change (AlgHom.restrictScalars N (Algebra.TensorProduct.includeRight :
        ((S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) ⊗[S.vertexAlg N (S.fibreMap N l)] (S.baseChangeField N l))
          →ₐ[S.vertexAlg N (S.fibreMap N k)] (S.baseChangeField N k) ⊗[S.vertexAlg N (S.fibreMap N k)]
            ((S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) ⊗[S.vertexAlg N (S.fibreMap N l)]
              (S.baseChangeField N l))))
      ((AlgHom.restrictScalars N (Algebra.TensorProduct.includeLeft :
        S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l) →ₐ[S.vertexAlg N (S.fibreMap N k)]
          (S.edgeAlg N (S.fibreMap N k) (S.fibreMap N l)) ⊗[S.vertexAlg N (S.fibreMap N l)]
            (S.baseChangeField N l)))
        ((1 : N) ⊗ₜ[K] algebraMap K (S.M (S.fibreMap N k) (S.fibreMap N l)) c)) = _
    rw [h1, AlgHom.commutes, AlgHom.commutes]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **B2.** The canonical `N`-linear map from the base change of a length-two path bimodule of `S` to the path bimodule
of `S ⊗_K N` over a lift of the path: `N ⊗_K {}M_{(π k₀, π k₁, π k₂)}(S) → {}M_{(k₀, k₁, k₂)}(S ⊗_K N)`,
`n ⊗ (x ⊗ y) ↦ n · (ι x ⊗ ι y)` with `ι m = 1 ⊗ ((1 ⊗ m) ⊗ 1)`. This is what "`R ⊗_K N`" means inside the path
bimodule of `S ⊗_K N`.  @census none (helper; T4-B, plan piece B2) -/
noncomputable def pathBaseChange (k0 k1 k2 : S.baseChangeIndex N) :
    N ⊗[K] P2 S (S.fibreMap N k0) (S.fibreMap N k1) (S.fibreMap N k2) →ₗ[N] P2 (S.baseChange N) k0 k1 k2 :=
  (baseChange N S).pathLift k0 k1 k2

set_option backward.isDefEq.respectTransparency.types false in
/-- B2 on pure tensors.  @census none (value guard) -/
@[simp] theorem pathBaseChange_tmul_mk (k0 k1 k2 : S.baseChangeIndex N) (n : N)
    (x : S.M (S.fibreMap N k0) (S.fibreMap N k1)) (y : S.M (S.fibreMap N k1) (S.fibreMap N k2)) :
    pathBaseChange N S k0 k1 k2 (n ⊗ₜ Balanced.mk x y) =
      n • Balanced.mk (K := N) (A := (S.baseChange N).L k1) (B := (S.baseChange N).L k2)
        ((baseChange N S).onM k0 k1 x) ((baseChange N S).onM k1 k2 y) :=
  (baseChange N S).pathLift_tmul k0 k1 k2 n _

end BaseChange


end PathDatum

end EtaleSpecies

end RationalQuivers
