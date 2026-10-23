import RationalQuivers.Gelfand.Target
import RationalQuivers.HC.Sl2
import RationalQuivers.Species.Rep.BaseChangeGeneral
import RationalQuivers.Quiver.Inflation

/-!
# `Γ_E = E ⊗_ℚ Γ_ℚ` for every `E` (tex §5, opening: `lem:GammaEbasechange`, stage T4)

Formalizes `lem:GammaEbasechange` (census `RQ2-5.11`): for every field `E` of characteristic `0`,
`Γ_E ≅ E ⊗_ℚ Γ_ℚ`, the base change of `def:quiverbasechangegeneral`,
`E ⊗_ℚ Γ_ℚ := Γ_E(S(Γ_ℚ) ⊗_ℚ E)`.

## The proof

The base change is defined through the étale species, so the proof runs through species base change
and the anti-equivalence of `thm:KrationalquiveretaleKspeciesantiequivalence`. The field `E` need not
lie in any Galois extension of `ℚ` with respect to which `Γ_ℚ` is regarded, so
`lem:quiverbasechangecompat` does not apply. Fix the `ℚ`-embedding `ι : ℚ[√-1] → L_E`, `√-1 ↦ √-1`,
and the restriction `r : G_E → Gal(ℚ[√-1]/ℚ)` with `σ ∘ ι = ι ∘ r(σ)`.

1. `L_E` splits `S(Γ_ℚ) ⊗_ℚ E` (`isSplitBy_baseChange_of_emb`): the splitting fields of `S(Γ_ℚ)` lie
   in `ℚ[√-1]`, which embeds into `L_E`.
2. Species base change, quiver side (T0's `bcToVertex`, `bcToEdge`, stated for an arbitrary
   extension `N/K`): `V(Γ_E(S ⊗_ℚ E)) ≃ ⨆_i Hom_ℚ(L_i, L_E)`, and likewise for edges.
3. Every `ℚ`-embedding of a vertex or edge field into `L_E` factors through `ι`, because those fields
   are split by `ℚ[√-1]` (`postV_bijective`, `postE_bijective`). Hence `⨆_i Hom_ℚ(L_i, L_E) ≃
   ⨆_i Hom_ℚ(L_i, ℚ[√-1])`, which is `Γ_ℚ(S(Γ_ℚ))`.
4. The unit `Γ_ℚ ≅ Γ_ℚ(S(Γ_ℚ))` of the anti-equivalence.

Steps 2 to 4 carry the `G_E`-action, `σ ∈ G_E` acting through `r(σ)` (`pullbackIso`). The quiver
obtained this way, `Γ_ℚ` with `G_E` acting through `r`, **is** `Γ_E` (`pullback_GammaE`): `r(σ)` is
the swap exactly when `χ_E(σ) = -1`. The argument is uniform in `E` and `ℓ`: no case distinction
between `√-1 ∈ E` and `√-1 ∉ E` is needed.

@census none (module; claimant of `RQ2-5.11` below)
-/

namespace RationalQuivers

open CategoryTheory Polynomial
open scoped TensorProduct

/-! ## Post-composition with an embedding of splitting fields -/

namespace EtaleSpecies

section Post

variable {K L L' : Type} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

/-- An algebra map out of an integral `K`-algebra whose minimal polynomials split in `L` factors
through any `K`-embedding `ι : L → L'`.  @census none (helper) -/
theorem exists_factor_of_splits (ι : L →ₐ[K] L') {A : Type} [CommRing A] [Algebra K A]
    [Algebra.IsIntegral K A]
    (hspl : ∀ x : A, (Polynomial.map (algebraMap K L) (minpoly K x)).Splits)
    (τ : A →ₐ[K] L') : ∃ τ' : A →ₐ[K] L, ι.comp τ' = τ := by
  have hmem : ∀ x : A, τ x ∈ ι.range := by
    intro x
    have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    have hne : (minpoly K x).map (algebraMap K L) ≠ 0 :=
      Polynomial.map_ne_zero (minpoly.ne_zero hint)
    have hroot : (((minpoly K x).map (algebraMap K L)).map (ι : L →+* L')).IsRoot (τ x) := by
      rw [Polynomial.map_map, ι.comp_algebraMap, Polynomial.IsRoot, Polynomial.eval_map_algebraMap,
        Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    obtain ⟨y, hy⟩ := (hspl x).mem_range_of_isRoot hne hroot
    exact ⟨y, hy⟩
  let e := AlgEquiv.ofInjective ι ι.injective
  refine ⟨e.symm.toAlgHom.comp (τ.codRestrict ι.range hmem), AlgHom.ext fun x => ?_⟩
  show ι (e.symm ⟨τ x, hmem x⟩) = τ x
  have := AlgEquiv.ofInjective_apply ι ι.injective (e.symm ⟨τ x, hmem x⟩)
  rw [AlgEquiv.apply_symm_apply] at this
  exact this.symm

variable (S : EtaleSpecies K) (ι : L →ₐ[K] L')

/-- Post-composition with `ι` on the vertices of `Γ_K(S)`.  @census none (helper) -/
def postV : S.vertexSet L → S.vertexSet L' := fun v => ⟨v.1, ι.comp v.2⟩

/-- Post-composition with `ι` on the edges of `Γ_K(S)`.  @census none (helper) -/
noncomputable def postE : S.edgeSet L → S.edgeSet L' := fun e => ⟨e.1, ι.comp e.2⟩

theorem postV_source (e : S.edgeSet L) :
    postV S ι (S.edgeSource L e) = S.edgeSource L' (postE S ι e) := rfl

theorem postV_target (e : S.edgeSet L) :
    postV S ι (S.edgeTarget L e) = S.edgeTarget L' (postE S ι e) := rfl

theorem postV_injective : Function.Injective (postV S ι) := by
  rintro ⟨i, τ⟩ ⟨j, τ'⟩ h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
  have h3 : ι.comp τ = ι.comp τ' := eq_of_heq h2
  have : τ = τ' := AlgHom.ext fun x => ι.injective (congrArg (fun f => f x) h3)
  rw [this]

theorem postE_injective : Function.Injective (postE S ι) := by
  rintro ⟨i, τ⟩ ⟨j, τ'⟩ h
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
  have h3 : ι.comp τ = ι.comp τ' := eq_of_heq h2
  have : τ = τ' := AlgHom.ext fun x => ι.injective (congrArg (fun f => f x) h3)
  rw [this]

/-- If `L` splits `S` (`IsSplitBy`), every `K`-embedding of a vertex field into `L'` factors through
`ι`: post-composition is surjective on vertices.  @census none (helper) -/
theorem postV_surjective [IsGalois K L] [FiniteDimensional K L] (hS : S.IsSplitBy L) :
    Function.Surjective (postV S ι) := by
  rintro ⟨i, τ⟩
  obtain ⟨τ', hτ'⟩ := exists_factor_of_splits ι (hS.splits_L i) τ
  exact ⟨⟨i, τ'⟩, by rw [postV, hτ']⟩

/-- Likewise on edges: the residue fields `L_ε` are quotients of the edge algebras, which `L`
splits.  @census none (helper) -/
theorem postE_surjective [IsGalois K L] [FiniteDimensional K L] (hS : S.IsSplitBy L) :
    Function.Surjective (postE S ι) := by
  rintro ⟨c, τ⟩
  have hspl : ∀ x : S.residueField c,
      (Polynomial.map (algebraMap K L) (minpoly K x)).Splits := by
    intro x
    obtain ⟨m, rfl⟩ := S.residueMap_surjective c x
    exact SplitAlg.splits_of_algHom (S.residueMap c) m (Algebra.IsIntegral.isIntegral m)
      (hS.splits_M c.1.1 c.1.2 m)
  obtain ⟨τ', hτ'⟩ := exists_factor_of_splits ι hspl τ
  exact ⟨⟨c, τ'⟩, by rw [postE, hτ']⟩

end Post

/-! ## The base change is split by `L'` -/

section Split

variable {K : Type} [Field K] (S : EtaleSpecies K)
variable {L : Type} [Field L] [Algebra K L]
variable (F : Type) [Field F] [Algebra K F] [Algebra F L] [IsScalarTower K F L]

/-- (Copied from T0's `baseChange_splits_L` with the hypothesis weakened from `IsSplitBy` to the
splitting condition on the vertex fields, so that `L/K` need not be Galois: here `L = L_E` over
`K = ℚ`.)  @census none (helper) -/
theorem baseChange_splits_L' [Normal F L] [FiniteDimensional F L]
    (hL : ∀ (i : S.I) (x : S.L i), (Polynomial.map (algebraMap K L) (minpoly K x)).Splits)
    (p : S.baseChangeIndex F) (x : S.baseChangeField F p) :
    (Polynomial.map (algebraMap F L) (minpoly F x)).Splits := by
  haveI : Module.Finite F (F ⊗[K] S.L p.1) :=
    Algebra.FormallyUnramified.finite_of_free F (F ⊗[K] S.L p.1)
  haveI : Algebra.IsIntegral F (F ⊗[K] S.L p.1) := Algebra.IsIntegral.of_finite F _
  obtain ⟨y, rfl⟩ := S.baseChangeProj_surjective F p x
  exact SplitAlg.splits_of_algHom (S.baseChangeProj F p) y (Algebra.IsIntegral.isIntegral y)
    (SplitAlg.tensor_splits (hL p.1) y)

/-- (Copied from T0's `baseChange_splits_M` with the hypothesis weakened from `IsSplitBy` to the two
splitting conditions, `L/K` need not be Galois.) Each edge algebra `{}_kM'_ℓ` of the base-changed species is split by `L`. It is
`L'_k ⊗_{A_i} ((F ⊗_K {}_iM_j) ⊗_{A_j} L'_ℓ)`, so `splits_of_two_gens` applies twice, over the
three algebras `L'_k`, `F ⊗_K {}_iM_j`, `L'_ℓ`, each of which is already known to be split.

@census none (helper for `RQ2-2.08`)
-/
theorem baseChange_splits_M' [Normal F L] [FiniteDimensional F L]
    (hL : ∀ (i : S.I) (x : S.L i), (Polynomial.map (algebraMap K L) (minpoly K x)).Splits)
    (hM : ∀ (i j : S.I) (x : S.M i j), (Polynomial.map (algebraMap K L) (minpoly K x)).Splits)
    (k l : S.baseChangeIndex F) (x : (S.baseChange F).M k l) :
    (Polynomial.map (algebraMap F L) (minpoly F x)).Splits := by
  letI := S.algRightEdge F (S.fibreMap F k) (S.fibreMap F l)
  letI := S.towerRightEdge F (S.fibreMap F k) (S.fibreMap F l)
  letI := S.algVertexField F l
  letI := S.towerVertexField F l
  letI := S.algLeftEdge F (S.fibreMap F k) (S.fibreMap F l)
  letI := S.towerLeftEdge F (S.fibreMap F k) (S.fibreMap F l)
  letI := S.smulCommEdge F (S.fibreMap F k) (S.fibreMap F l)
  letI := S.algVertexField F k
  letI := S.towerVertexField F k
  letI Inner : Type := (S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l))
    ⊗[S.vertexAlg F (S.fibreMap F l)] (S.baseChangeField F l)
  haveI hEk : Algebra.Etale F (S.baseChangeField F k) := S.etale_baseChangeField F k
  haveI hEl : Algebra.Etale F (S.baseChangeField F l) := S.etale_baseChangeField F l
  haveI : Algebra.Etale (S.vertexAlg F (S.fibreMap F l)) (S.baseChangeField F l) :=
    Algebra.Etale.of_restrictScalars F _ _
  haveI hEdge : Algebra.Etale F (S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) :=
    Algebra.Etale.baseChange K (S.M (S.fibreMap F k) (S.fibreMap F l)) F
  haveI : Algebra.Etale (S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) Inner :=
    Algebra.Etale.baseChange _ _ _
  haveI hEInner : Algebra.Etale F Inner :=
    Algebra.Etale.comp F (S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) Inner
  haveI : Module.Finite F (S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) :=
    Algebra.FormallyUnramified.finite_of_free F _
  haveI : Module.Finite F (S.baseChangeField F l) := Algebra.FormallyUnramified.finite_of_free F _
  haveI : Module.Finite F (S.baseChangeField F k) := Algebra.FormallyUnramified.finite_of_free F _
  haveI : Module.Finite F Inner := Algebra.FormallyUnramified.finite_of_free F _
  have hEdgeSplits : ∀ z : S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l),
      (Polynomial.map (algebraMap F L) (minpoly F z)).Splits :=
    SplitAlg.tensor_splits (hM (S.fibreMap F k) (S.fibreMap F l))
  have hInner : ∀ z : Inner, (Polynomial.map (algebraMap F L) (minpoly F z)).Splits := by
    refine SplitAlg.splits_of_two_gens
      (AlgHom.restrictScalars F (Algebra.TensorProduct.includeLeft
        (R := S.vertexAlg F (S.fibreMap F l)) (S := S.vertexAlg F (S.fibreMap F l))
        (A := S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) (B := S.baseChangeField F l)))
      (AlgHom.restrictScalars F (Algebra.TensorProduct.includeRight
        (R := S.vertexAlg F (S.fibreMap F l))
        (A := S.edgeAlg F (S.fibreMap F k) (S.fibreMap F l)) (B := S.baseChangeField F l)))
      ?_ (Algebra.IsIntegral.of_finite F _) (Algebra.IsIntegral.of_finite F _)
      hEdgeSplits (S.baseChange_splits_L' F hL l)
    exact SplitAlg.tensor_subalgebra_eq_top _ (fun a => Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩))
      (fun b => Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩))
  set fOut : (S.baseChangeField F k) →ₐ[F]
      ((S.baseChangeField F k) ⊗[S.vertexAlg F (S.fibreMap F k)] Inner) :=
    AlgHom.restrictScalars F (Algebra.TensorProduct.includeLeft
      (S := S.vertexAlg F (S.fibreMap F k)))
  set gOut : Inner →ₐ[F]
      ((S.baseChangeField F k) ⊗[S.vertexAlg F (S.fibreMap F k)] Inner) :=
    AlgHom.restrictScalars F Algebra.TensorProduct.includeRight
  have hfOut : ∀ a, fOut a = a ⊗ₜ[S.vertexAlg F (S.fibreMap F k)] (1 : Inner) := fun _ => rfl
  have hgOut : ∀ b, gOut b = (1 : S.baseChangeField F k) ⊗ₜ[S.vertexAlg F (S.fibreMap F k)] b :=
    fun _ => rfl
  haveI hEcar : Algebra.Etale F
      ((S.baseChangeField F k) ⊗[S.vertexAlg F (S.fibreMap F k)] Inner) :=
    S.baseChangeEdge_etale F k l
  show (Polynomial.map (algebraMap F L)
    (minpoly F (x : (S.baseChangeField F k) ⊗[S.vertexAlg F (S.fibreMap F k)] Inner))).Splits
  refine SplitAlg.splits_of_two_gens (A := S.baseChangeField F k) (B := Inner)
    (C := (S.baseChangeField F k) ⊗[S.vertexAlg F (S.fibreMap F k)] Inner) fOut gOut
    ?_ (Algebra.IsIntegral.of_finite F _) (Algebra.IsIntegral.of_finite F _)
    (S.baseChange_splits_L' F hL k) hInner x
  exact SplitAlg.tensor_subalgebra_eq_top _
    (fun a => Algebra.subset_adjoin (Or.inl ⟨a, hfOut a⟩))
    (fun b => Algebra.subset_adjoin (Or.inr ⟨b, hgOut b⟩))

end Split

section SplitEmb

variable {K L L' : Type} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [IsGalois K L] [FiniteDimensional K L]
variable (S : EtaleSpecies K) (ι : L →ₐ[K] L')

omit [IsGalois K L] [FiniteDimensional K L] in
include ι in
/-- **Step 1.** If `L` splits `S` and `ι : L → L'` is a `K`-embedding into a finite Galois
extension `L'/N`, then `L'` splits `S ⊗_K N`.  @census none (helper) -/
theorem isSplitBy_baseChange_of_emb (hS : S.IsSplitBy L) (N : Type) [Field N] [Algebra K N]
    [Algebra N L'] [IsScalarTower K N L'] [IsGalois N L'] [FiniteDimensional N L'] :
    (S.baseChange N).IsSplitBy L' := by
  haveI : Normal N L' := IsGalois.to_normal
  have hmap : ∀ {A : Type} [CommRing A] [Algebra K A] (x : A),
      (Polynomial.map (algebraMap K L) (minpoly K x)).Splits →
        (Polynomial.map (algebraMap K L') (minpoly K x)).Splits := by
    intro A _ _ x h
    rw [← ι.comp_algebraMap, ← Polynomial.map_map]
    exact h.map (ι : L →+* L')
  have hL : ∀ (i : S.I) (x : S.L i), (Polynomial.map (algebraMap K L') (minpoly K x)).Splits :=
    fun i x => hmap x (hS.splits_L i x)
  have hM : ∀ (i j : S.I) (x : S.M i j), (Polynomial.map (algebraMap K L') (minpoly K x)).Splits :=
    fun i j x => hmap x (hS.splits_M i j x)
  exact { galois := inferInstance
          findim := inferInstance
          splits_L := fun p x => S.baseChange_splits_L' N hL p x
          splits_M := fun k l x => S.baseChange_splits_M' N hL hM k l x }

end SplitEmb

end EtaleSpecies

/-! ## The pulled-back quiver and the comparison isomorphism -/

namespace RationalQuiver

section Pullback

variable {K L N L' : Type} [Field K] [Field L] [Field N] [Field L'] [Algebra K L] [Algebra K N]
  [Algebra N L'] [Algebra K L'] [IsScalarTower K N L'] [IsGalois N L'] [FiniteDimensional N L']

/-- `Γ` regarded as an `N`-rational quiver with respect to `L'/N`, `σ ∈ Gal(L'/N)` acting through
`r(σ) ∈ Gal(L/K)`.  @census none (helper) -/
noncomputable def pullback (r : Gal(L'/N) →* Gal(L/K)) (Γ : RationalQuiver K L) :
    RationalQuiver N L' where
  toRQuiver := Γ.toRQuiver
  ρ := Γ.ρ.comp r
  smooth_V := IsSmooth.of_discreteTopology _
  smooth_E := IsSmooth.of_discreteTopology _

end Pullback

end RationalQuiver

namespace EtaleSpecies

section Equivariance

variable {K L' N : Type} [Field K] [Field L'] [Field N] [Algebra K N] [Algebra N L'] [Algebra K L']
  [IsScalarTower K N L'] (S : EtaleSpecies K)

/-- `σ ∈ Gal(L'/N)` acting on `⨆_i Hom_K(L_i, L')` by post-composition.  @census none (helper) -/
def galPostV (σ : Gal(L'/N)) : S.vertexSet L' → S.vertexSet L' :=
  fun v => ⟨v.1, ((σ : L' ≃ₐ[N] L').toAlgHom.restrictScalars K).comp v.2⟩

/-- The same on edges.  @census none (helper) -/
noncomputable def galPostE (σ : Gal(L'/N)) : S.edgeSet L' → S.edgeSet L' :=
  fun e => ⟨e.1, ((σ : L' ≃ₐ[N] L').toAlgHom.restrictScalars K).comp e.2⟩

/-- T0's vertex comparison commutes with `Gal(L'/N)`, for any `N` (not only an intermediate
field).  @census none (helper) -/
theorem bcToVertex_smul (σ : Gal(L'/N)) (v : (S.baseChange N).vertexSet L') :
    bcToVertex S N (σ • v) = galPostV S σ (bcToVertex S N v) := rfl

/-- T0's edge comparison commutes with `Gal(L'/N)`.  @census none (helper) -/
theorem bcToEdge_smul (σ : Gal(L'/N)) (e : (S.baseChange N).edgeSet L') :
    bcToEdge S N (σ • e) = galPostE S σ (bcToEdge S N e) := by
  refine edgeSet_ext_of_val (MaximalSpectrum.ext ?_) (fun x => rfl)
  ext y
  show σ (bcEdgeHom e.1 e.2 y) = 0 ↔ bcEdgeHom e.1 e.2 y = 0
  exact map_eq_zero_iff _ (σ : L' ≃ₐ[N] L').injective

end Equivariance

end EtaleSpecies

/-! ## Steps 2–4: `Γ_N(S(Γ) ⊗_K N) ≅ ι^*Γ` -/

namespace RationalQuiver

section PullbackIso

set_option linter.unusedSectionVars false

variable {K L N L' : Type} [Field K] [Field L] [Field N] [Field L'] [Algebra K L] [Algebra K N]
  [Algebra N L'] [Algebra K L'] [IsScalarTower K N L'] [IsGalois N L'] [FiniteDimensional N L']
  [IsGalois K L] [FiniteDimensional K L]
variable (Γ : RationalQuiver K L) (ι : L →ₐ[K] L') (r : Gal(L'/N) →* Gal(L/K))
  (hr : ∀ (σ : Gal(L'/N)) (x : L), σ (ι x) = ι (r σ x))

/-- Steps 3 and 4 on vertices: `V(Γ) ≃ ⨆_i Hom_K(L_i, L')`, the unit followed by post-composition
with `ι`.  @census none (helper) -/
noncomputable def unitPostV : Γ.V ≃ Γ.toSpecies.vertexSet L' :=
  Equiv.ofBijective (EtaleSpecies.postV Γ.toSpecies ι ∘ Γ.unitOnV)
    ⟨(EtaleSpecies.postV_injective _ ι).comp Γ.unitOnV_bijective.1,
      (EtaleSpecies.postV_surjective _ ι Γ.toSpecies_isSplitBy).comp Γ.unitOnV_bijective.2⟩

/-- The same on edges.  @census none (helper) -/
noncomputable def unitPostE : Γ.E ≃ Γ.toSpecies.edgeSet L' :=
  Equiv.ofBijective (EtaleSpecies.postE Γ.toSpecies ι ∘ Γ.unitOnE)
    ⟨(EtaleSpecies.postE_injective _ ι).comp Γ.unitOnE_bijective.1,
      (EtaleSpecies.postE_surjective _ ι Γ.toSpecies_isSplitBy).comp Γ.unitOnE_bijective.2⟩

theorem unitPostV_source (x : Γ.E) :
    unitPostV Γ ι (Γ.toRQuiver.source x) = Γ.toSpecies.edgeSource L' (unitPostE Γ ι x) := by
  show EtaleSpecies.postV _ ι (Γ.unitOnV _) = _
  rw [Γ.unitOnV_source]
  rfl

theorem unitPostV_target (x : Γ.E) :
    unitPostV Γ ι (Γ.toRQuiver.target x) = Γ.toSpecies.edgeTarget L' (unitPostE Γ ι x) := by
  show EtaleSpecies.postV _ ι (Γ.unitOnV _) = _
  rw [Γ.unitOnV_target]
  rfl

include hr in
theorem unitPostV_smul (σ : Gal(L'/N)) (x : Γ.V) :
    unitPostV Γ ι (r σ • x) = EtaleSpecies.galPostV Γ.toSpecies σ (unitPostV Γ ι x) := by
  show EtaleSpecies.postV _ ι (Γ.unitOnV _) = _
  rw [Γ.unitOnV_equivariant]
  exact congrArg (Sigma.mk _) (AlgHom.ext fun a => (hr σ _).symm)

include hr in
theorem unitPostE_smul (σ : Gal(L'/N)) (x : Γ.E) :
    unitPostE Γ ι (r σ • x) = EtaleSpecies.galPostE Γ.toSpecies σ (unitPostE Γ ι x) := by
  show EtaleSpecies.postE _ ι (Γ.unitOnE _) = _
  rw [Γ.unitOnE_equivariant]
  exact congrArg (Sigma.mk _) (AlgHom.ext fun a => (hr σ _).symm)

/-- **The comparison morphism** `Γ_N(S(Γ) ⊗_K N) ⟶ ι^*Γ`: T0's species base-change comparison
(`bcToVertex`, `bcToEdge`), then post-composition with `ι` and the unit of the anti-equivalence,
inverted.  @census none (helper) -/
noncomputable def pullbackHom (hY : (Γ.toSpecies.baseChange N).IsSplitBy L') :
    (Γ.toSpecies.baseChange N).toRationalQuiver L' hY ⟶ pullback r Γ where
  toRQuiverHom :=
    { onV := (unitPostV Γ ι).symm ∘ EtaleSpecies.bcToVertex Γ.toSpecies N
      onE := (unitPostE Γ ι).symm ∘ EtaleSpecies.bcToEdge Γ.toSpecies N
      onV_source := fun e => (unitPostV Γ ι).injective (by
        show unitPostV Γ ι ((unitPostV Γ ι).symm (EtaleSpecies.bcToVertex Γ.toSpecies N
            ((Γ.toSpecies.baseChange N).edgeSource L' e)))
          = unitPostV Γ ι (Γ.toRQuiver.source ((unitPostE Γ ι).symm
            (EtaleSpecies.bcToEdge Γ.toSpecies N e)))
        rw [Equiv.apply_symm_apply, unitPostV_source, Equiv.apply_symm_apply]
        exact EtaleSpecies.bcToVertex_source Γ.toSpecies N e)
      onV_target := fun e => (unitPostV Γ ι).injective (by
        show unitPostV Γ ι ((unitPostV Γ ι).symm (EtaleSpecies.bcToVertex Γ.toSpecies N
            ((Γ.toSpecies.baseChange N).edgeTarget L' e)))
          = unitPostV Γ ι (Γ.toRQuiver.target ((unitPostE Γ ι).symm
            (EtaleSpecies.bcToEdge Γ.toSpecies N e)))
        rw [Equiv.apply_symm_apply, unitPostV_target, Equiv.apply_symm_apply]
        exact EtaleSpecies.bcToVertex_target Γ.toSpecies N e) }
  equivariant_V := fun σ v => (unitPostV Γ ι).injective (by
    show unitPostV Γ ι ((unitPostV Γ ι).symm (EtaleSpecies.bcToVertex Γ.toSpecies N (σ • v)))
      = unitPostV Γ ι (r σ • (unitPostV Γ ι).symm (EtaleSpecies.bcToVertex Γ.toSpecies N v))
    rw [unitPostV_smul Γ ι r hr, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact EtaleSpecies.bcToVertex_smul Γ.toSpecies σ v)
  equivariant_E := fun σ e => (unitPostE Γ ι).injective (by
    show unitPostE Γ ι ((unitPostE Γ ι).symm (EtaleSpecies.bcToEdge Γ.toSpecies N (σ • e)))
      = unitPostE Γ ι (r σ • (unitPostE Γ ι).symm (EtaleSpecies.bcToEdge Γ.toSpecies N e))
    rw [unitPostE_smul Γ ι r hr, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact EtaleSpecies.bcToEdge_smul Γ.toSpecies σ e)

/-- **`Γ_N(S(Γ) ⊗_K N) ≅ ι^*Γ`**: the comparison morphism is an isomorphism (all three steps are
bijections).  @census none (helper) -/
noncomputable def pullbackIso (hY : (Γ.toSpecies.baseChange N).IsSplitBy L') :
    (Γ.toSpecies.baseChange N).toRationalQuiver L' hY ≅ pullback r Γ :=
  haveI : IsIso (pullbackHom Γ ι r hr hY) :=
    isIso_of_bijective _
      ((unitPostV Γ ι).symm.bijective.comp (EtaleSpecies.bcToVertex_bijective Γ.toSpecies N))
      ((unitPostE Γ ι).symm.bijective.comp
        ⟨EtaleSpecies.bcToEdge_injective Γ.toSpecies N, EtaleSpecies.bcToEdge_surjective Γ.toSpecies N⟩)
  asIso (pullbackHom Γ ι r hr hY)

end PullbackIso

end RationalQuiver

/-! ## `lem:GammaEbasechange` -/


namespace Gelfand

open RationalQuivers.HC

section GammaE

variable {E : Type} [Field E] [CharZero E] (D : ImagUnit E)

/-- `L_ℚ` carries two `ℚ`-algebra structures (`ImagUnit.qi.algebra` and mathlib's `algebraRat`);
`χ`, `Γ_ℚ` and `ImagUnit.qi.powerBasis` use the first, so it is pinned here.  @census none (helper) -/
noncomputable local instance (priority := high) instAlgebraQi : Algebra ℚ ImagUnit.qi.L := ImagUnit.qi.algebra

/-- `L_ℚ/ℚ` is Galois and finite (T1's derived instances).  @census none (helper) -/
local instance instIsGaloisQi' : IsGalois ℚ ImagUnit.qi.L := ImagUnit.isGalois _

local instance instFiniteDimensionalQi' : FiniteDimensional ℚ ImagUnit.qi.L :=
  ImagUnit.finiteDimensional _

/-- `√-1 ∉ ℚ`.  @census none (helper) -/
theorem qi_not_sqrt' : ¬ ∃ a : ℚ, a * a = -1 :=
  fun ⟨a, ha⟩ => by nlinarith [mul_self_nonneg a]

/-- **`ι : ℚ[√-1] → L_E`**, the `ℚ`-embedding `√-1 ↦ √-1`.  @census none (helper) -/
noncomputable def qiEmb : ImagUnit.qi.L →ₐ[ℚ] D.L :=
  ImagUnit.qi.powerBasis.lift D.i (by
    rw [show ImagUnit.qi.powerBasis.gen = ImagUnit.qi.i from rfl,
      ImagUnit.qi.minpoly_i_of_not_sqrt qi_not_sqrt']
    simp [sq, D.i_mul_i])

theorem qiEmb_i : qiEmb D ImagUnit.qi.i = D.i :=
  ImagUnit.qi.powerBasis.lift_gen _ _

/-- The non-trivial element of `Gal(ℚ[√-1]/ℚ)`.  @census none (helper) -/
noncomputable def cQi : Gal(ImagUnit.qi.L/ℚ) :=
  (ImagUnit.qi.exists_chi_neg_one_iff.mpr qi_not_sqrt').choose

theorem chi_cQi : ImagUnit.qi.chi cQi = -1 :=
  (ImagUnit.qi.exists_chi_neg_one_iff.mpr qi_not_sqrt').choose_spec

/-- **`r : G_E → Gal(ℚ[√-1]/ℚ)`**, `σ ↦` the element with the same sign `χ`.  @census none (helper) -/
noncomputable def resQi : Gal(D.L/E) →* Gal(ImagUnit.qi.L/ℚ) where
  toFun σ := if D.chi σ = 1 then 1 else cQi
  map_one' := by rw [if_pos D.chi_one]
  map_mul' σ τ := by
    apply ImagUnit.qi.chi_injective
    have key : ∀ ρ : Gal(D.L/E), ImagUnit.qi.chi (if D.chi ρ = 1 then 1 else cQi) = D.chi ρ := by
      intro ρ
      rcases D.chi_cases ρ with h | h
      · rw [if_pos h, ImagUnit.qi.chi_one, h]
      · rw [if_neg (by rw [h]; decide), chi_cQi, h]
    rw [key, ImagUnit.qi.chi_mul, key, key, D.chi_mul]

theorem chi_resQi (σ : Gal(D.L/E)) : ImagUnit.qi.chi (resQi D σ) = D.chi σ := by
  show ImagUnit.qi.chi (if D.chi σ = 1 then 1 else cQi) = D.chi σ
  rcases D.chi_cases σ with h | h
  · rw [if_pos h, ImagUnit.qi.chi_one, h]
  · rw [if_neg (by rw [h]; decide), chi_cQi, h]

/-- **`σ ∘ ι = ι ∘ r(σ)`** on `ℚ[√-1]`: both send `√-1` to `χ_E(σ)·√-1`.  @census none (helper) -/
theorem qiEmb_res (σ : Gal(D.L/E)) (x : ImagUnit.qi.L) :
    σ (qiEmb D x) = qiEmb D (resQi D σ x) := by
  have h := AlgHom.ext_of_adjoin_eq_top (R := ℚ) ImagUnit.qi.adjoin_eq_top
    (φ₁ := ((σ : D.L ≃ₐ[E] D.L).toAlgHom.restrictScalars ℚ).comp (qiEmb D))
    (φ₂ := (qiEmb D).comp (resQi D σ : ImagUnit.qi.L ≃ₐ[ℚ] ImagUnit.qi.L).toAlgHom) (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      show σ (qiEmb D ImagUnit.qi.i) = qiEmb D (resQi D σ ImagUnit.qi.i)
      rw [qiEmb_i]
      rcases D.chi_cases σ with hσ | hσ
      · have h1 : ImagUnit.qi.chi (resQi D σ) = 1 := (chi_resQi D σ).trans hσ
        rw [D.chi_eq_one_iff.mp hσ, ImagUnit.qi.chi_eq_one_iff.mp h1, qiEmb_i]
      · have h1 : ImagUnit.qi.chi (resQi D σ) = -1 := (chi_resQi D σ).trans hσ
        rw [D.chi_eq_neg_one_iff.mp hσ, ImagUnit.qi.chi_eq_neg_one_iff.mp h1, map_neg, qiEmb_i])
  exact congrArg (fun f => f x) h

/-- **`Γ_E` is `Γ_ℚ` with `G_E` acting through `r`.**  @census none (helper) -/
theorem pullback_GammaE (ℓ : ℕ) :
    RationalQuiver.pullback (resQi D) (GammaE ImagUnit.qi ℓ) = GammaE D ℓ := by
  have hχ : ImagUnit.qi.chiHom.comp (resQi D) = D.chiHom :=
    MonoidHom.ext fun σ => by
      rw [MonoidHom.comp_apply, ImagUnit.chiHom_apply, ImagUnit.chiHom_apply, chi_resQi]
  cases ℓ with
  | zero =>
    show RationalQuiver.pullback (resQi D) (RationalQuiver.cyclicOfSign ℚ _ ImagUnit.qi.chiHom)
      = RationalQuiver.cyclicOfSign E D.L D.chiHom
    unfold RationalQuiver.pullback RationalQuiver.cyclicOfSign RationalQuiver.ofSign
    simp only [MonoidHom.comp_assoc, hχ]
  | succ k =>
    show RationalQuiver.pullback (resQi D) (RationalQuiver.gelfandOfSign ℚ _ ImagUnit.qi.chiHom)
      = RationalQuiver.gelfandOfSign E D.L D.chiHom
    unfold RationalQuiver.pullback RationalQuiver.gelfandOfSign RationalQuiver.ofSign
    simp only [MonoidHom.comp_assoc, hχ]

/-- **Step 1** at `Γ_ℚ`: `L_E` splits `S(Γ_ℚ) ⊗_ℚ E`.  @census none (helper) -/
theorem GammaE_isSplitBy (ℓ : ℕ) :
    ((GammaE ImagUnit.qi ℓ).toSpecies.baseChange E).IsSplitBy D.L :=
  EtaleSpecies.isSplitBy_baseChange_of_emb _ (qiEmb D) (GammaE ImagUnit.qi ℓ).toSpecies_isSplitBy E

/-- **Lemma** (`lem:GammaEbasechange`).  Let `E` be a field of characteristic `0`.  Then
`Γ_E ≅ E ⊗_ℚ Γ_ℚ`, the base change of `def:quiverbasechangegeneral`, taken with the splitting field
`L_E` of `S(Γ_ℚ) ⊗_ℚ E` (`GammaE_isSplitBy`).

*Proof* (module docstring).  `E ⊗_ℚ Γ_ℚ = Γ_E(S(Γ_ℚ) ⊗_ℚ E)`; species base change, quiver side
(`bcToVertex`, `bcToEdge`), identifies its vertices and edges with the `ℚ`-embeddings of the vertex
and edge fields of `S(Γ_ℚ)` into `L_E`; these factor through `ι : ℚ[√-1] → L_E`; and the unit of the
anti-equivalence identifies the result with `Γ_ℚ`, on which `σ ∈ G_E` acts through `r(σ)`: this is
`Γ_E` (`pullback_GammaE`).

@census    RQ2-5.11
@source    lem:GammaEbasechange
@clauses   RQ2-5.11-H1, RQ2-5.11-C1, RQ2-5.11-H2, RQ2-5.11-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (splitting field as an argument; data).  As for
`def:quiverbasechangegeneral` (`RQ2-2.39`), the base change is built over an explicit splitting field,
here `L_E` itself; the isomorphism is given as data, an isomorphism in the category of `E`-rational
quivers with respect to `L_E/E` (`C1`).  `H1`: every characteristic-zero field `E : Type` (universe
`0`), with its `L_E` (`D : ImagUnit E`).  `Γ_ℚ` is `GammaE ImagUnit.qi ℓ`, the quiver of `ex:gelfand`
resp. `ex:cyclic` (`Rational.GammaE_qi_of_pos`, `Rational.GammaE_qi_zero`).  `H2`/`C2` (finite `E'` inside
a Galois `L`): `GammaE_baseChange_finite`, the general base change of `Γ_ℚ` over `L` **is**
`def:quiverbasechange` of `Γ_ℚ` inflated to `L` (`lem:quiverbasechangecompat`).
-/
noncomputable def GammaE_eq_baseChange (ℓ : ℕ) :
    GammaE D ℓ ≅ (GammaE ImagUnit.qi ℓ).baseChangeGeneral E D.L (GammaE_isSplitBy D ℓ) :=
  eqToIso (pullback_GammaE D ℓ).symm ≪≫
    (RationalQuiver.pullbackIso (GammaE ImagUnit.qi ℓ) (qiEmb D) (resQi D) (qiEmb_res D)
      (GammaE_isSplitBy D ℓ)).symm

end GammaE

/-! ## `RQ2-5.11-C2`: finite `E` inside a Galois `L` -/

section Finite

noncomputable local instance (priority := high) instAlgebraQiF : Algebra ℚ ImagUnit.qi.L :=
  ImagUnit.qi.algebra
local instance instIsGaloisQiF : IsGalois ℚ ImagUnit.qi.L := ImagUnit.isGalois _
local instance instFiniteDimensionalQiF : FiniteDimensional ℚ ImagUnit.qi.L :=
  ImagUnit.finiteDimensional _

variable (L : Type) [Field L] [Algebra ℚ L] [IsGalois ℚ L] [FiniteDimensional ℚ L]
  [Algebra ImagUnit.qi.L L] [IsScalarTower ℚ ImagUnit.qi.L L]
  (E' : IntermediateField ℚ L) [FiniteDimensional ℚ E']

omit [FiniteDimensional ℚ E'] in
/-- For `E'/ℚ` finite inside a Galois `L ⊇ ℚ[√-1]`, `L` splits `S(Γ_ℚ) ⊗_ℚ E'`.  @census none (helper) -/
theorem GammaE_isSplitBy_finite (ℓ : ℕ) :
    ((GammaE ImagUnit.qi ℓ).toSpecies.baseChange E').IsSplitBy L := by
  haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois ℚ E' L
  exact EtaleSpecies.isSplitBy_baseChange_of_emb _ (IsScalarTower.toAlgHom ℚ ImagUnit.qi.L L)
    (GammaE ImagUnit.qi ℓ).toSpecies_isSplitBy E'

/-- **`RQ2-5.11-C2`** (`H2`: `E'/ℚ` finite, inside a Galois `L/ℚ` with `√-1 ∈ L`, with respect to which
`Γ_ℚ` is regarded, `rmk:finitequotient`).  The base change of `def:quiverbasechangegeneral`, taken
with the splitting field `L`, **is** the base change of `def:quiverbasechange` of `Γ_ℚ` regarded with
respect to `L` (its inflation): the same comparison as for `GammaE_eq_baseChange`, with `ι : ℚ[√-1] ⊆ L`
and `r` the restriction `Gal(L/E') → Gal(L/ℚ) → Gal(ℚ[√-1]/ℚ)`; this is `lem:quiverbasechangecompat`
(`RQ2-2.40`) at `Γ_ℚ`.  @census none (helper; clauses `RQ2-5.11-H2`, `RQ2-5.11-C2`) -/
noncomputable def GammaE_baseChange_finite (ℓ : ℕ) :
    (GammaE ImagUnit.qi ℓ).baseChangeGeneral E' L (GammaE_isSplitBy_finite L E' ℓ) ≅
      (RationalQuiver.baseChange ℚ L E').obj ((GammaE ImagUnit.qi ℓ).inflate (M := L)) :=
  haveI : IsGalois E' L := IsGalois.tower_top_of_isGalois ℚ E' L
  RationalQuiver.pullbackIso (GammaE ImagUnit.qi ℓ) (IsScalarTower.toAlgHom ℚ ImagUnit.qi.L L)
    ((galInflate ℚ ImagUnit.qi.L L).comp (galRestrict ℚ L E'))
    (fun σ x => (AlgEquiv.restrictNormal_commutes (galRestrict ℚ L E' σ) ImagUnit.qi.L x).symm)
    (GammaE_isSplitBy_finite L E' ℓ)

end Finite

end Gelfand

end RationalQuivers
