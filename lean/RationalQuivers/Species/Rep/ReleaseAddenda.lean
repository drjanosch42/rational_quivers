import RationalQuivers.Species.Rep.Equivalence
import RationalQuivers.Species.Rep.GelfandRelation

/-!
# §2 release addenda (final-release WP-16a)

New, gate-neutral clause witnesses for §2 (stage S5) rows whose bound claimant is weaker than the
corrected (census r18/r19) text.  Nothing here changes an existing declaration.

* `RationalQuivers.RationalQuiver.hFunctor_map_formula` — `RQ2-2.28` / `RQ2-2.28-C5`: for
  `v = σ v_i`, the identification `M(v) = W_i ⊗_{L_i,σ} L` (`hIdent`), its independence of `σ`
  modulo `G_{v_i}`, and `H` on morphisms is `ψ_i ⊗ 1_L` under it.
* `RationalQuivers.RationalQuiver.hFunctor_indep_KStructure` — `RQ2-2.28`: different choices of the
  `K`-structures `W_{i,K}` (and of the edge choice) give naturally isomorphic functors.
* `RationalQuivers.GelfandRelation.satisfies_RGelfand_iff_rational` — `RQ2-2.37-C4`: `F(M)`
  satisfies `R_Gelfand` iff `X = Y` on `W_⋆` iff `X` commutes with `φ_{⋆,c}` (`ℚ`-rationality).
-/

universe u

namespace RationalQuivers

open MulAction CategoryTheory

open scoped TensorProduct DirectSum

namespace RationalQuiver

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {Γ : RationalQuiver K L}

section HMorphisms

variable (WK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit), Submodule K (V.W i))
  (hWK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
    IsKRationalStructure V i (WK V i))
  (ch : ∀ (k l : Γ.VertexOrbit) (ε : Γ.EdgeOrbit k l), Γ.EdgeChoice ε)

open scoped Classical in
/-- **The identification `M(v) = W_i ⊗_{L_i,σ} L` for `v = σ v_i`** (`RQ2-2.28-C5`).  Written in
mathlib's factor order `L ⊗_{L_i} W_i`: the canonical `M(v_i) = W_{i,K} ⊗_K L = W_i ⊗_{L_i} L`
(`hObjEquivBaseChange`, clause `RQ2-2.27-C4`) followed by `φ_{v_i,σ} : M(v_i) → M(σ v_i)`.  It is
`σ`-semilinear in the `L` factor (`hIdent_smul`), which is what the twisted `⊗_{L_i,σ}` records.
@census none (helper for `RQ2-2.28-C5`) -/
noncomputable def hIdent (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit) (σ : Gal(L/K))
    {v : Γ.V} (hσ : σ • Γ.vertexRep i = v) (x : L ⊗[Γ.toSpecies.L i] V.W i) :
    ((hFunctor WK hWK ch).obj V).toRep.M v :=
  ((hFunctor WK hWK ch).obj V).toRep.φ' σ hσ
    (hObjCast V (WK V) (Γ.vertexClass_vertexRep i).symm
      (hObjEquivBaseChange V (WK V) i (hWK V i) x))

omit [IsGalois K L] in
/-- A morphism of `Rep(Γ_K)` commutes with transport along an equality of vertices.
@census none (helper) -/
theorem hom_eqCast {M N : Rep Γ} (f : Rep.Hom M N) {v w : Γ.V} (h : v = w) (m : M.M v) :
    f.ψ w (M.eqCast h m) = N.eqCast h (f.ψ v m) := by
  subst h; rfl

open scoped Classical in
/-- **`RQ2-2.28` (statement) and `RQ2-2.28-C5`, corrected text** — `H` on morphisms, and the
identification it is read through.  For every vertex orbit `i`, every `σ ∈ G` and `v = σ v_i`:

* `hIdent : L ⊗_{L_i} W_i → M(v)` (the source's `M(v) = W_{i,K} ⊗_K L = W_i ⊗_{L_i,σ} L`) is a
  **bijection**, **`σ`-semilinear** in the `L` factor;
* it is **independent of `σ` modulo `G_{v_i}`**: for `g ∈ G_{v_i}`, the identification for `σg`
  is the one for `σ` precomposed with `g` on the `L` factor (`a ⊗ w ↦ g(a) ⊗ w`, `L_i`-linear
  because `g` fixes `L_i`);
* `φ_{v,τ}` becomes `w ⊗ a ↦ w ⊗ τ a` (on `M(v) = W_{i,K} ⊗_K L`, for `τ ∈ G_v`);
* **`H` on morphisms is `ψ_i ⊗ 1_L`**: `(H ψ)_v (ι_σ(a ⊗ w)) = ι_σ(a ⊗ ψ_i(w))`;
* and `H` is a functor (`map_id`, `map_comp`).

Strengthens `RationalQuivers.RationalQuiver.H_cocycle` (whose `C5` conjunct is `∃ H` with only
`map_id`/`map_comp`, `H.map` unconstrained) for rows `RQ2-2.28` and `RQ2-2.28-C5` (final-release
WP-16a, MISMATCH-TRIAGE #5/#6).

@census    none (auxiliary; clause witness for `RQ2-2.28-C5`)
@source    UNLABELED-H-cocycle
@clauses   RQ2-2.28-C5
@imports   none
@divergence JUSTIFIED_REFORMULATION (factor order and the twist, disclosed).  The source writes
`W_i ⊗_{L_i,σ} L`; the tree writes `L ⊗_{L_i} W_i` and records the twist `σ` as the
`σ`-semilinearity of the identification `hIdent` (second conjunct) rather than as a second module
structure on `L`.  The two are the same identification: `ι_σ(a ⊗ w) = φ_{v_i,σ}(w ⊗ a)`. -/
theorem hFunctor_map_formula :
    (∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit) (σ : Gal(L/K)) {v : Γ.V}
        (hσ : σ • Γ.vertexRep i = v),
        Function.Bijective (hIdent WK hWK ch V i σ hσ) ∧
        (∀ (b : L) (x : L ⊗[Γ.toSpecies.L i] V.W i),
          hIdent WK hWK ch V i σ hσ (b • x) = σ b • hIdent WK hWK ch V i σ hσ x) ∧
        (∀ (g : Gal(L/K)) (hg : g • Γ.vertexRep i = Γ.vertexRep i)
            (hσg : (σ * g) • Γ.vertexRep i = v) (x : L ⊗[Γ.toSpecies.L i] V.W i),
          hIdent WK hWK ch V i (σ * g) hσg x
            = hIdent WK hWK ch V i σ hσ (LinearMap.rTensor (V.W i) (galLinearVOF i g hg) x))) ∧
      (∀ (V : EtaleSpecies.Rep Γ.toSpecies) (v : Γ.V) (τ : Gal(L/K)) (hτ : τ • v = v)
          (a : L) (w : ↥(WK V (Γ.vertexClass v))),
        ((hFunctor WK hWK ch).obj V).toRep.φ' τ hτ (a ⊗ₜ[K] w) = (τ a) ⊗ₜ[K] w) ∧
      (∀ (U V : EtaleSpecies.Rep Γ.toSpecies) (ψ : U ⟶ V) (i : Γ.VertexOrbit) (σ : Gal(L/K))
          {v : Γ.V} (hσ : σ • Γ.vertexRep i = v) (a : L) (w : U.W i),
        ((hFunctor WK hWK ch).map ψ).ψ v (hIdent WK hWK ch U i σ hσ (a ⊗ₜ w))
          = hIdent WK hWK ch V i σ hσ (a ⊗ₜ ψ.ψ i w)) ∧
      ((∀ V : EtaleSpecies.Rep Γ.toSpecies,
          (hFunctor WK hWK ch).map (𝟙 V) = 𝟙 ((hFunctor WK hWK ch).obj V)) ∧
        ∀ (U V W : EtaleSpecies.Rep Γ.toSpecies) (φ : U ⟶ V) (χ : V ⟶ W),
          (hFunctor WK hWK ch).map (φ ≫ χ)
            = (hFunctor WK hWK ch).map φ ≫ (hFunctor WK hWK ch).map χ) := by
  refine ⟨fun V i σ v hσ => ⟨?_, ?_, ?_⟩, fun V v τ hτ a w => ?_, fun U V ψ i σ v hσ a w => ?_,
    fun V => (hFunctor WK hWK ch).map_id V,
    fun U V W φ χ => (hFunctor WK hWK ch).map_comp φ χ⟩
  · -- a composite of three bijections
    exact ((((hFunctor WK hWK ch).obj V).toRep.φ' σ hσ).bijective.comp
      (hObjCast V (WK V) (Γ.vertexClass_vertexRep i).symm).bijective).comp
      (hObjEquivBaseChange V (WK V) i (hWK V i)).bijective
  · intro b x
    simp only [hIdent, LinearEquiv.map_smul, hObjCast_smul, Rep.φ'_apply]
    erw [Rep.semilinear]
    rw [LinearEquiv.map_smul]
  · intro g hg hσg x
    simp only [hIdent]
    rw [← Rep.φ'_comp _ σ g hg hσ hσg, hObjEquivBaseChange_gal V (WK V) i (hWK V i) g hg x]
    congr 1
    erw [hObjRep_phi'_apply]
    exact hPhi_hObjCast V (WK V) _ g _
  · exact hObjRep_phi'_tmul WK hWK ch V v τ hτ a w
  · -- `H ψ` commutes with `φ_{v_i,σ}` (the `rational` field) and is `ψ_i ⊗ 1` at `v_i`
    have hv : ∀ (a' : L) (w' : U.W i),
        ((hFunctor WK hWK ch).map ψ).ψ (Γ.vertexRep i)
            (hObjCast U (WK U) (Γ.vertexClass_vertexRep i).symm
              (hObjEquivBaseChange U (WK U) i (hWK U i) (a' ⊗ₜ w')))
          = hObjCast V (WK V) (Γ.vertexClass_vertexRep i).symm
              (hObjEquivBaseChange V (WK V) i (hWK V i) (a' ⊗ₜ ψ.ψ i w')) := by
      intro a' w'
      have h1 : ∀ (X : EtaleSpecies.Rep Γ.toSpecies) (x : X.W i),
          (a' ⊗ₜ[Γ.toSpecies.L i] x : L ⊗[Γ.toSpecies.L i] X.W i)
            = a' • ((1 : L) ⊗ₜ[Γ.toSpecies.L i] x) := by
        intro X x
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1 U, h1 V, LinearEquiv.map_smul, LinearEquiv.map_smul, hObjCast_smul, hObjCast_smul]
      erw [LinearMap.map_smul]
      rw [← kFormIncl_eq, ← kFormIncl_eq]
      congr 1
      exact hMapPsi_kFormIncl (WK U) (WK V) (hWK U) (hWK V) ψ i w'
    simp only [hIdent, Rep.φ'_apply]
    rw [hom_eqCast, ((hFunctor WK hWK ch).map ψ).rational, hv]

end HMorphisms

open scoped Classical in
/-- **`RQ2-2.28` (statement), last sentence** — *"different choices of the `K`-structures
`W_{i,K}` give naturally isomorphic functors"*: for any two families of `K`-rational structures
(and any two edge choices), the two functors `H` are naturally isomorphic.  Both are inverses of
the same equivalence functor `F` (`species_equivalence_at_tree_functors`, Theorem B at the tree's
functors), and inverses of equivalences with equal functors are isomorphic.

Strengthens `RationalQuivers.RationalQuiver.H_cocycle` (no independence statement) for row
`RQ2-2.28` (final-release WP-16a, MISMATCH-TRIAGE #5).

@census    none (auxiliary; clause witness for `RQ2-2.28` statement and `RQ2-2.28-C5`)
@source    UNLABELED-H-cocycle
@clauses   RQ2-2.28-C5
@imports   none
@divergence none -/
theorem hFunctor_indep_KStructure
    (WK WK' : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit), Submodule K (V.W i))
    (hWK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
      IsKRationalStructure V i (WK V i))
    (hWK' : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
      IsKRationalStructure V i (WK' V i))
    (ch ch' : ∀ (i j : Γ.VertexOrbit) (ε : Γ.EdgeOrbit i j), Γ.EdgeChoice ε) :
    Nonempty (hFunctor WK hWK ch ≅ hFunctor WK' hWK' ch') := by
  obtain ⟨e, he1, he2⟩ := species_equivalence_at_tree_functors Γ WK hWK ch
  obtain ⟨e', he1', he2'⟩ := species_equivalence_at_tree_functors Γ WK' hWK' ch'
  exact ⟨eqToIso he2.symm ≪≫
    Iso.isoInverseOfIsoFunctor (eqToIso (he1.trans he1'.symm)) ≪≫ eqToIso he2'⟩

end RationalQuiver

namespace GelfandRelation

open RationalQuiver RQuiver MulAction Examples GelfandDescent Species
open scoped Classical

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
  (h : Nat.card Gal(L/K) = 2)

/-- **`RQ2-2.37-C4`, corrected text** — `R_Gelfand` is the descent of the `G`-stable relation set:
with `X := φ_{a₋} ∘ φ_{b₋}` and `Y := φ_{a₊} ∘ φ_{b₊}` on `M(⋆)`,

* `F(M)` satisfies `R_Gelfand` **iff `X = Y` on `W_⋆`** (the `G_⋆`-invariants, `toStar`);
* `F(M)` satisfies `R_Gelfand` **iff `X` commutes with `φ_{⋆,c}`**, i.e. is `ℚ`-rational (in
  general: defined over `K`) by Galois descent;
* and equivariance gives only the conjugacy `φ_{⋆,c} ∘ X = Y ∘ φ_{⋆,c}`.

The "genuine condition" half of the clause (a nilpotent `M` refuting it) is `RGelfand_genuine`.

Strengthens `RationalQuivers.GelfandRelation.satisfies_RGelfand_iff_pair` (⇔ both quiver
relations, the retired reading) for row `RQ2-2.37-C4` (final-release WP-16a, MISMATCH-TRIAGE #7).

@census    none (auxiliary; clause witness for `RQ2-2.37-C4`)
@source    ex:gelfandspeciesrelation
@clauses   RQ2-2.37-C4
@imports   none
@divergence none -/
theorem satisfies_RGelfand_iff_rational (M : FDRep (GΓ K L h)) {c : Gal(L/K)} (hc : c ≠ 1)
    {α : L} (hα : c α = -α) (hα0 : α ≠ 0) :
    (Species.Satisfies (SG K L h) ((FFunctor (GΓ K L h)).obj M) (RGelfand K L h α) ↔
        ∀ w : ((FFunctor (GΓ K L h)).obj M).W (nStar K L h),
          M.toRep.pathMap (gelfandPathMinus K L h) (toStar K L h M w)
            = M.toRep.pathMap (gelfandPathPlus K L h) (toStar K L h M w)) ∧
      (Species.Satisfies (SG K L h) ((FFunctor (GΓ K L h)).obj M) (RGelfand K L h α) ↔
        ∀ m : M.toRep.M (gelfandStar K L h),
          M.toRep.φ' c (gelfand_smul_star K L h hc) (M.toRep.pathMap (gelfandPathMinus K L h) m)
            = M.toRep.pathMap (gelfandPathMinus K L h)
                (M.toRep.φ' c (gelfand_smul_star K L h hc) m)) ∧
      (∀ m : M.toRep.M (gelfandStar K L h),
        M.toRep.φ' c (gelfand_smul_star K L h hc) (M.toRep.pathMap (gelfandPathMinus K L h) m)
          = M.toRep.pathMap (gelfandPathPlus K L h)
              (M.toRep.φ' c (gelfand_smul_star K L h hc) m)) := by
  refine ⟨⟨fun hsat w => ?_, fun key => ?_⟩, ?_, fun m => gelfand_relation_conjugate K L h hc _ m⟩
  · have hrel := (satisfies_RGelfand_iff_relation K L h M hc hα hα0).mp hsat
    exact LinearMap.congr_fun hrel _
  · -- `W_⋆` spans `M(⋆)` (`vertexDescentEquiv`, the source's `eq:WitoMvi`)
    refine (satisfies_RGelfand_iff_relation K L h M hc hα hα0).mpr ?_
    refine LinearMap.ext fun x => ?_
    obtain ⟨t, rfl⟩ := (vertexDescentEquiv M.toRep (gelfandStar K L h)).surjective x
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a m =>
        rw [vertexDescentEquiv_tmul, map_smul, map_smul]
        congr 1
        have hm : M.toRep.eqCast (vertexRep_star K L h).symm (m : M.toRep.M _)
            ∈ M.toRep.vertexFixed ((GΓ K L h).vertexRep (nStar K L h)) :=
          mem_vertexFixed_eqCast M.toRep _ m.2
        have := key ⟨_, hm⟩
        unfold toStar at this
        rwa [show wv M (nStar K L h) ⟨_, hm⟩ = M.toRep.eqCast (vertexRep_star K L h).symm m
          from rfl, M.toRep.eqCast_symm_apply] at this
    | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]
  · rw [satisfies_RGelfand_iff_relation K L h M hc hα hα0]
    exact (gelfand_relation_iff_transpose K L h hc M.toRep).2

end GelfandRelation

end RationalQuivers
