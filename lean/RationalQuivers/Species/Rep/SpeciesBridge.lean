module

public import RationalQuivers.Species.Rep.Equivalence
public import RationalQuivers.Quiver.Rep.Nilpotent
public import Mathlib.LinearAlgebra.Dual.Lemmas

@[expose] public section

/-!
# Engine `E7` — the nilpotency bridge between `Rep^nil(Γ_K)` and `Rep^nil(S(Γ_K))`

Stage S8, `@census none (helper)` throughout.  Design notes `stages/S8/DESIGN-NOTES.md` §19.
*(2026-10-21, O-V2-6: "throughout" has not held since `FObj_isNilpotent_iff` became the claimant of
`cor:nilpotentrelations` (`R-FR-5`, 2026-10-02; census `RQ2-2.38` on the v2 line, stage T0); every
other declaration here is a helper.)*
-/

universe u u₁ u₂ v₁ v₂

namespace RationalQuivers

namespace RationalQuiver

open CategoryTheory MulAction

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {Γ : RationalQuiver K L}

/-- The generating set of the `N`-th reach: the values `φ'_σ(pathMap p y)` for a path `p` of
length `N` ending at a vertex `b` with `σ • b = v`.

@census none (helper; engine `E7`) -/
def ReachSet (M : Rep Γ) (N : ℕ) (v : Γ.V) : Set (M.M v) :=
  {x | ∃ (σ : Gal(L/K)) (a : Γ.V) (b : Γ.V) (h : σ • b = v) (p : Quiver.Path a b),
      p.length = N ∧ ∃ y : M.M a, x = M.φ' σ h (M.pathMap p y)}

/-- The `N`-th **reach** of a representation at a vertex `v`: the `L`-submodule of `M(v)` spanned
by the images of `φ'_σ ∘ (path composite of length N)`.

@census none (helper; engine `E7`) -/
def Reach (M : Rep Γ) (N : ℕ) (v : Γ.V) : Submodule L (M.M v) :=
  Submodule.span L (ReachSet M N v)

omit [IsGalois K L] in
/-- The generators of `Reach`.  @census none (helper) -/
theorem mem_Reach (M : Rep Γ) {N : ℕ} {v : Γ.V} (σ : Gal(L/K)) {a b : Γ.V} (h : σ • b = v)
    (p : Quiver.Path a b) (hp : p.length = N) (y : M.M a) :
    M.φ' σ h (M.pathMap p y) ∈ Reach M N v :=
  Submodule.subset_span ⟨σ, a, b, h, p, hp, y, rfl⟩

omit [IsGalois K L] in
/-- The elimination principle for `Reach`.  @census none (helper) -/
theorem Reach_le (M : Rep Γ) {N : ℕ} {v : Γ.V} (T : Submodule L (M.M v))
    (H : ∀ (σ : Gal(L/K)) (a b : Γ.V) (h : σ • b = v) (p : Quiver.Path a b), p.length = N →
      ∀ y : M.M a, M.φ' σ h (M.pathMap p y) ∈ T) :
    Reach M N v ≤ T := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨σ, a, b, h, p, hp, y, rfl⟩
  exact H σ a b h p hp y

omit [IsGalois K L] in
/-- The zeroth reach is everything.  @census none (helper) -/
theorem Reach_zero (M : Rep Γ) (v : Γ.V) : Reach M 0 v = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have h1 : (1 : Gal(L/K)) • v = v := one_smul _ v
  have hx : M.φ' (1 : Gal(L/K)) h1 (M.pathMap (Quiver.Path.nil : Quiver.Path v v) x) = x := by
    rw [M.pathMap_nil]
    show M.φ' (1 : Gal(L/K)) h1 x = x
    rw [M.φ'_one]
    rfl
  exact hx ▸ mem_Reach M (1 : Gal(L/K)) h1 Quiver.Path.nil rfl x

/-- The `σ`-semilinear pullback of a submodule along `φ'_σ`.  @census none (helper) -/
def phiPull (M : Rep Γ) (σ : Gal(L/K)) {v w : Γ.V} (h : σ • v = w)
    (T : Submodule L (M.M w)) : Submodule L (M.M v) where
  carrier := {x | M.φ' σ h x ∈ T}
  add_mem' hx hy := by simpa only [Set.mem_setOf_eq, map_add] using T.add_mem hx hy
  zero_mem' := by simpa only [Set.mem_setOf_eq, map_zero] using T.zero_mem
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, M.φ'_smul]
    exact T.smul_mem _ hx

omit [IsGalois K L] in
/-- **Step 1 of `E7`**: the reach is stable under the semi-linear structure maps.
@census none (helper) -/
theorem Reach_phi (M : Rep Γ) (N : ℕ) (τ : Gal(L/K)) {v w : Γ.V} (hτ : τ • v = w)
    {x : M.M v} (hx : x ∈ Reach M N v) : M.φ' τ hτ x ∈ Reach M N w := by
  refine Reach_le M (phiPull M τ hτ (Reach M N w)) ?_ hx
  intro σ a b h p _ y
  show M.φ' τ hτ (M.φ' σ h (M.pathMap p y)) ∈ Reach M N w
  have hmul : (τ * σ) • b = w := by rw [mul_smul, h, hτ]
  rw [M.φ'_comp τ σ h hτ hmul]
  exact mem_Reach M (τ * σ) hmul p ‹p.length = N› y

/-- **Step 2 of `E7`**: an edge map raises the reach by one.  @census none (helper) -/
theorem Reach_edge (M : Rep Γ) (N : ℕ) (e : Γ.E) {x : M.M (Γ.toRQuiver.source e)}
    (hx : x ∈ Reach M N (Γ.toRQuiver.source e)) :
    M.φEdge e x ∈ Reach M (N + 1) (Γ.toRQuiver.target e) := by
  refine Reach_le M (Submodule.comap (M.φEdge e)
    (Reach M (N + 1) (Γ.toRQuiver.target e))) ?_ hx
  intro σ a b h p hp y
  suffices hgoal : M.φEdge e (M.φ' σ h (M.pathMap p y))
      ∈ Reach M (N + 1) (Γ.toRQuiver.target e) from hgoal
  -- the `σ`-translate of `e` back onto the path's endpoint
  have ha : Γ.toRQuiver.source (σ⁻¹ • e) = b := by
    rw [Γ.source_smul, ← h, inv_smul_smul]
  have hb : Γ.toRQuiver.target (σ⁻¹ • e) = σ⁻¹ • Γ.toRQuiver.target e := Γ.target_smul _ _
  have h₂ : σ • (σ⁻¹ • Γ.toRQuiver.target e) = Γ.toRQuiver.target e := smul_inv_smul _ _
  have key := M.φEdge'_φ' σ (smul_inv_smul σ e) ha hb (rfl : Γ.toRQuiver.source e = _)
    (rfl : Γ.toRQuiver.target e = _) h h₂ (M.pathMap p y)
  rw [show M.φEdge e (M.φ' σ h (M.pathMap p y))
      = M.φEdge' e rfl rfl (M.φ' σ h (M.pathMap p y)) from rfl, key]
  have harr : M.φEdge' (σ⁻¹ • e) ha hb (M.pathMap p y)
      = M.pathMap (p.cons (⟨σ⁻¹ • e, ha, hb⟩ : b ⟶ σ⁻¹ • Γ.toRQuiver.target e)) y := by
    rw [M.pathMap_cons]
    rfl
  rw [harr]
  exact mem_Reach M σ h₂ _ (by simpa using hp) y

omit [IsGalois K L] in
/-- **Step 3 of `E7`**: past the nilpotency bound the reach is zero.  @census none (helper) -/
theorem Reach_eq_bot (M : Rep Γ) {n N : ℕ}
    (hn : ∀ (a b : Γ.V) (p : Quiver.Path a b), n ≤ p.length →
      pathCompose (Q := Γ.toRQuiver) M.M M.φEdge p = 0)
    (hN : n ≤ N) (v : Γ.V) : Reach M N v = ⊥ := by
  refine le_bot_iff.1 (Reach_le M ⊥ ?_)
  intro σ a b h p hp y
  have hz : M.pathMap p y = 0 := by
    have := hn a b p (hp ▸ hN)
    rw [show M.pathMap p = pathCompose (Q := Γ.toRQuiver) M.M M.φEdge p from rfl, this]
    rfl
  rw [hz, map_zero]
  exact Submodule.zero_mem _

/-! ### `E7` step 4 — the descended structure maps move one step along the filtration -/

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Step 4 of `E7`**: the Galois descent `f_{ij}` of `Φ_{ij}` (`RQ2-2.24`) raises the reach by
exactly one.  This is `IsEdgeDescent`'s first conjunct read as a filtration statement:
`f_{ij}(w ⊗ m) = Σ_{ε,η} c_{ε,η} · φ'(φ_{e_ε}(φ'(w)))` (`phiTotal_e0_generator`), and each summand
is one edge map of `Γ` dressed with Galois transports on both sides.

@census none (helper; engine `E7`) -/
theorem isEdgeDescent_mem_Reach (M : Rep Γ) {i j : Γ.VertexOrbit} (N : ℕ)
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
    (hf : IsEdgeDescent M ch e₀ f)
    (u : ↥(M.vertexFixed (Γ.vertexRep i))) (mm : Γ.toSpecies.M i j)
    (hu : (u : M.M (Γ.vertexRep i)) ∈ Reach M N (Γ.vertexRep i)) :
    ((f (Balanced.mk u mm) : M.M (Γ.vertexRep j))) ∈ Reach M (N + 1) (Γ.vertexRep j) := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε)) :=
    fun ε => @Fintype.ofFinite _ (finite_cosetIndex (ch ε))
  have hval : ((f (Balanced.mk u mm) : M.M (Γ.vertexRep j)))
      = phiTotal M ch (e₀ (Balanced.mk (Balanced.mk u mm) (1 : L))) := by
    have h := hf.2 (phiTotal M ch) (phiTotal_single M ch) (Balanced.mk u mm) 1
    rw [one_smul] at h
    exact h.symm
  rw [hval, phiTotal_e0_generator M ch e₀ hf.1 u mm 1]
  refine Submodule.sum_mem _ fun ε _ => Submodule.sum_mem _ fun η _ =>
    Submodule.smul_mem _ _ ?_
  rw [show phiComp M (ch ε) η u
      = M.φ' (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((ch ε).cosetTarget η)
          (M.φEdge' (Γ.edgeRep ε) rfl rfl
            (M.φ' (ch ε).σ (ch ε).sourceVertex (u : M.M (Γ.vertexRep i)))) from rfl]
  refine Reach_phi M (N + 1) _ ((ch ε).cosetTarget η) ?_
  exact Reach_edge M N (Γ.edgeRep ε) (Reach_phi M N _ (ch ε).sourceVertex hu)

/-! ### `E7` step 5 — the forward direction of the bridge -/

open scoped Classical in
/-- **Step 5 of `E7`**: the species-side path composite of `F(M)` at length `N` lands in the `N`-th
reach of `M`.  @census none (helper; engine `E7`) -/
theorem FObj_pathApply_mem_Reach (M : FDRep Γ) (idx : ℕ → Γ.VertexOrbit)
    (mm : ∀ k, Γ.toSpecies.toSpecies.M (idx k) (idx (k + 1)))
    (w : ((FFunctor Γ).obj M).W (idx 0)) (N : ℕ) :
    (((FFunctor Γ).obj M).pathApply idx mm N w :
        ↥(M.toRep.vertexFixed (Γ.vertexRep (idx N)))).val
      ∈ Reach M.toRep N (Γ.vertexRep (idx N)) := by
  induction N with
  | zero =>
      rw [Reach_zero]
      exact Submodule.mem_top
  | succ N ih =>
      exact isEdgeDescent_mem_Reach M.toRep N _ _ (edgeDescentOf M.toRep (idx N) (idx (N + 1)))
        (isEdgeDescent_edgeDescentOf M.toRep (idx N) (idx (N + 1))) _ (mm N) ih

open scoped Classical in
/-- **`E7`, the forward direction**: `F = FFunctor Γ` **preserves** nilpotency, with the same
bound.  @census none (helper; engine `E7`) -/
theorem FObj_isNilpotent (M : FDRep Γ) (h : M.toRep.IsNilpotent) :
    ((FFunctor Γ).obj M).IsNilpotent := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, fun idx mm N hN w => ?_⟩
  have hmem := FObj_pathApply_mem_Reach M idx mm w N
  rw [Reach_eq_bot M.toRep hn hN (Γ.vertexRep (idx N)), Submodule.mem_bot] at hmem
  exact Subtype.ext hmem

/-! ### `E7` step 6 — the choosing lemma

`DESIGN-NOTES` §12.5(b) records the converse of `E7` as blocked on the ability to *choose* an
`m ∈ {}_iM_j` realising a given edge.  The obstruction is exactly this: `f_{ij}(w ⊗ m)` is the
**whole** double sum `Σ_{ε,η} (ητ_ε⁻¹)(m_ε) · phiComp M (ch ε) η w`, and a single `(ε,η)` term has
to be extracted from it.  Extraction over `ε` is free, because `{}_iM_j = ∏_ε L(e_ε)`
(`RationalQuiver.edgeAlgebra`); extraction over `η` is Dedekind's independence of characters, and
that is what this section proves.
-/

section Choosing

variable {i j : Γ.VertexOrbit}

/-- The coefficient family of `phiTotal_e0_generator` at `a = 1`: `x ↦ ((η τ_ε⁻¹)(x))_η`, a
`K`-linear map `L(e_ε) → (G_{v_j}/G_{τ_ε⁻¹e_ε} → L)`.

@census none (helper; engine `E7`) -/
noncomputable def cosetEval {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    (x : Γ.edgeOrbitField ε) : EdgeChoice.CosetIndex Γ ch → L :=
  fun η => (EdgeChoice.rep Γ ch η * ch.τ⁻¹) (x : L)

/-- **Distinct cosets give distinct embeddings `L(e_ε) → L`.**  This is the Galois correspondence
at the *edge* stabilizer — `smul_eq_of_stabField_apply_eq`, S5's `RQ2-2.13-C4` helper — combined
with the definition of `CosetIndex` as `G_{v_j}/G_{τ_ε⁻¹e_ε}`.

@census none (helper; engine `E7`) -/
theorem cosetEval_index_injective {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    {η η' : EdgeChoice.CosetIndex Γ ch}
    (h : ∀ x : Γ.edgeOrbitField ε, cosetEval ch x η = cosetEval ch x η') : η = η' := by
  have hsm : (EdgeChoice.rep Γ ch η * ch.τ⁻¹) • Γ.edgeRep ε
      = (EdgeChoice.rep Γ ch η' * ch.τ⁻¹) • Γ.edgeRep ε :=
    smul_eq_of_stabField_apply_eq (Γ.isOpen_stabilizer_E _) (fun α => h α)
  -- `y := τ (rep η')⁻¹ (rep η) τ⁻¹` stabilises `e_ε`
  have hy : (ch.τ * (EdgeChoice.rep Γ ch η')⁻¹ * EdgeChoice.rep Γ ch η * ch.τ⁻¹)
      ∈ stabilizer Gal(L/K) (Γ.edgeRep ε) := by
    rw [mem_stabilizer_iff]
    calc (ch.τ * (EdgeChoice.rep Γ ch η')⁻¹ * EdgeChoice.rep Γ ch η * ch.τ⁻¹) • Γ.edgeRep ε
        = (ch.τ * (EdgeChoice.rep Γ ch η')⁻¹) •
            ((EdgeChoice.rep Γ ch η * ch.τ⁻¹) • Γ.edgeRep ε) := by
          rw [← mul_smul]; congr 1
      _ = (ch.τ * (EdgeChoice.rep Γ ch η')⁻¹) •
            ((EdgeChoice.rep Γ ch η' * ch.τ⁻¹) • Γ.edgeRep ε) := by rw [hsm]
      _ = Γ.edgeRep ε := by rw [← mul_smul, show ch.τ * (EdgeChoice.rep Γ ch η')⁻¹ *
            (EdgeChoice.rep Γ ch η' * ch.τ⁻¹) = 1 by group, one_smul]
  have hconj := stabilizer_conj (X := Γ.E) ch.τ⁻¹ _ (Γ.edgeRep ε) hy
  have hmem : (EdgeChoice.rep Γ ch η')⁻¹ * EdgeChoice.rep Γ ch η
      ∈ stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε) := by
    have hEq : ch.τ⁻¹ * (ch.τ * (EdgeChoice.rep Γ ch η')⁻¹ * EdgeChoice.rep Γ ch η * ch.τ⁻¹)
        * ch.τ⁻¹⁻¹ = (EdgeChoice.rep Γ ch η')⁻¹ * EdgeChoice.rep Γ ch η := by group
    rwa [hEq] at hconj
  -- conclude in the coset space
  have hout : ∀ κ : EdgeChoice.CosetIndex Γ ch,
      (Quotient.mk _ (Quotient.out κ : stabilizer Gal(L/K) (Γ.vertexRep j)) :
        EdgeChoice.CosetIndex Γ ch) = κ := fun κ => κ.out_eq
  have hmem2 : (((Quotient.out η : stabilizer Gal(L/K) (Γ.vertexRep j))⁻¹ *
      (Quotient.out η' : stabilizer Gal(L/K) (Γ.vertexRep j)) : _) : Gal(L/K))
      ∈ stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε) := by
    have hinv := Subgroup.inv_mem _ hmem
    rw [mul_inv_rev, inv_inv] at hinv
    exact hinv
  rw [← hout η, ← hout η']
  refine (QuotientGroup.eq (s := (stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε)).subgroupOf
    (stabilizer Gal(L/K) (Γ.vertexRep j)))).2 ?_
  rw [Subgroup.mem_subgroupOf]
  exact hmem2

/-- **The choosing lemma.**  The coefficient families `cosetEval ch x`, `x ∈ L(e_ε)`, span
`G_{v_j}/G_{τ_ε⁻¹e_ε} → L` over `L`.  This is Dedekind's independence of characters
(`linearIndependent_monoidHom`) read as a spanning statement, through the duality of a
finite-dimensional space.

@census none (helper; engine `E7`) -/
theorem span_cosetEval_eq_top {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε) :
    Submodule.span L (Set.range (cosetEval ch)) = ⊤ := by
  classical
  letI : Fintype (EdgeChoice.CosetIndex Γ ch) :=
    @Fintype.ofFinite _ (finite_cosetIndex (Γ := Γ) ch)
  by_contra hne
  obtain ⟨f, hf0, hfker⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (p := Submodule.span L (Set.range (cosetEval ch)))
    (lt_top_iff_ne_top.2 hne) inferInstance
  set c : EdgeChoice.CosetIndex Γ ch → L :=
    fun η => f (Pi.single η (1 : L)) with hc
  -- `f` is `v ↦ Σ_η v η * c η`
  have hfv : ∀ v : EdgeChoice.CosetIndex Γ ch → L, f v = ∑ η, v η * c η := by
    intro v
    have hv : v = ∑ η, v η • Pi.single η (1 : L) := by
      funext η
      rw [Finset.sum_apply, Finset.sum_eq_single η]
      · simp
      · intro η' _ hne'
        simp [Ne.symm hne']
      · intro hcon; exact absurd (Finset.mem_univ η) hcon
    conv_lhs => rw [hv]
    rw [map_sum]
    exact Finset.sum_congr rfl fun η _ => by rw [map_smul]; rfl
  -- `f` kills every generator
  have hzero : ∀ x : Γ.edgeOrbitField ε, ∑ η, cosetEval ch x η * c η = 0 := by
    intro x
    rw [← hfv]
    have : f (cosetEval ch x) ∈ (Submodule.span L (Set.range (cosetEval ch))).map f :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, rfl⟩)
    rw [hfker, Submodule.mem_bot] at this
    exact this
  -- Dedekind
  set χ : EdgeChoice.CosetIndex Γ ch → (↥(Γ.edgeOrbitField ε) →* L) := fun η =>
    { toFun := fun x => (EdgeChoice.rep Γ ch η * ch.τ⁻¹) (x : L)
      map_one' := by simp
      map_mul' := fun x y => by
        show (EdgeChoice.rep Γ ch η * ch.τ⁻¹) ((x * y : ↥(Γ.edgeOrbitField ε)) : L) = _
        push_cast
        rw [map_mul] } with hχ
  have hχinj : Function.Injective χ := by
    intro η η' hηη'
    exact cosetEval_index_injective ch fun x => DFunLike.congr_fun hηη' x
  have hLI : LinearIndependent L
      (fun η : EdgeChoice.CosetIndex Γ ch => (χ η : ↥(Γ.edgeOrbitField ε) → L)) :=
    (linearIndependent_monoidHom ↥(Γ.edgeOrbitField ε) L).comp χ hχinj
  have hc0 : ∀ η, c η = 0 := by
    refine Fintype.linearIndependent_iff.1 hLI c (funext fun x => ?_)
    have := hzero x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun η _ => mul_comm _ _
  exact hf0 (LinearMap.ext fun v => by rw [hfv v]; simp [hc0])

end Choosing

/-! ### `E7` step 7 — the species-side reach, and what nilpotency says about it

`Species.Rep.IsNilpotent` is a statement about *chains* `i₀ → i₁ → …`; the converse of the bridge
needs it as a statement about *submodules*, so that an induction along a path of `Γ` can carry it.
`WReach` is that form, and `WReach_eq_bot` is the translation.  The translation is proved with the
chain PREPENDED rather than appended, which is what makes it free of dependent transport: with
`idx' = i :: idx` one has `idx' (k+1) = idx k` **definitionally**.
-/

namespace Species

open RationalQuivers.Species

variable {K' : Type u} [Field K'] {S : Species K'}

/-- The `N`-th reach of a species representation: the additive subgroup of `W_j` generated by the
values of `N`-fold composites of structure maps.  @census none (helper; engine `E7`) -/
def WReach (V : Species.Rep S) : ℕ → (j : S.I) → AddSubgroup (V.W j)
  | 0, _ => ⊤
  | (N + 1), j => ⨆ i : S.I, AddSubgroup.closure
      {x | ∃ (u : V.W i), u ∈ WReach V N i ∧ ∃ m : S.M i j, x = V.f i j (Balanced.mk u m)}

/-- `pathApply` is additive in its starting vector.  @census none (helper) -/
theorem pathApply_add (V : Species.Rep S) (idx : ℕ → S.I)
    (m : ∀ k, S.M (idx k) (idx (k + 1))) (N : ℕ) (w w' : V.W (idx 0)) :
    V.pathApply idx m N (w + w') = V.pathApply idx m N w + V.pathApply idx m N w' := by
  induction N with
  | zero => rfl
  | succ N ih =>
      show V.f _ _ (Balanced.mk (V.pathApply idx m N (w + w')) (m N))
        = V.f _ _ (Balanced.mk (V.pathApply idx m N w) (m N))
          + V.f _ _ (Balanced.mk (V.pathApply idx m N w') (m N))
      rw [ih, Balanced.mk_add_left, map_add]

/-- `pathApply` kills `0`.  @census none (helper) -/
theorem pathApply_zero (V : Species.Rep S) (idx : ℕ → S.I)
    (m : ∀ k, S.M (idx k) (idx (k + 1))) (N : ℕ) :
    V.pathApply idx m N (0 : V.W (idx 0)) = 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      show V.f _ _ (Balanced.mk (V.pathApply idx m N 0) (m N)) = 0
      rw [ih, Balanced.mk_zero_left', map_zero]

/-- `pathApply` commutes with negation.  @census none (helper) -/
theorem pathApply_neg (V : Species.Rep S) (idx : ℕ → S.I)
    (m : ∀ k, S.M (idx k) (idx (k + 1))) (N : ℕ) (w : V.W (idx 0)) :
    V.pathApply idx m N (-w) = -V.pathApply idx m N w := by
  have h := pathApply_add V idx m N w (-w)
  rw [add_neg_cancel, pathApply_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The starting vectors annihilated by a fixed chain form an additive subgroup.
@census none (helper) -/
def pathApplyKer (V : Species.Rep S) (idx : ℕ → S.I)
    (m : ∀ k, S.M (idx k) (idx (k + 1))) (N : ℕ) : AddSubgroup (V.W (idx 0)) where
  carrier := {w | V.pathApply idx m N w = 0}
  add_mem' hw hw' := by
    simp only [Set.mem_setOf_eq] at *
    rw [pathApply_add, hw, hw', add_zero]
  zero_mem' := pathApply_zero V idx m N
  neg_mem' hw := by
    simp only [Set.mem_setOf_eq] at *
    rw [pathApply_neg, hw, neg_zero]

/-- The chain `i :: idx`.  `(i :: idx) (k+1) = idx k` definitionally.  @census none (helper) -/
def consIdx (i : S.I) (idx : ℕ → S.I) : ℕ → S.I
  | 0 => i
  | (k + 1) => idx k

/-- Prepending one structure map to a chain shifts `pathApply` by one.
@census none (helper) -/
theorem pathApply_consIdx (V : Species.Rep S) {i : S.I} (idx : ℕ → S.I)
    (m : ∀ k, S.M (idx k) (idx (k + 1))) (m₀ : S.M i (idx 0)) (v : V.W i) (N : ℕ) :
    V.pathApply (consIdx i idx)
        (fun k => Nat.rec (motive := fun k => S.M (consIdx i idx k) (consIdx i idx (k + 1)))
          m₀ (fun k _ => m k) k) (N + 1) v
      = V.pathApply idx m N (V.f i (idx 0) (Balanced.mk v m₀)) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      show V.f _ _ (Balanced.mk (V.pathApply (consIdx i idx)
            (fun k => Nat.rec (motive := fun k =>
              S.M (consIdx i idx k) (consIdx i idx (k + 1))) m₀ (fun k _ => m k) k) (N + 1) v)
            (m N))
        = V.f _ _ (Balanced.mk
            (V.pathApply idx m N (V.f i (idx 0) (Balanced.mk v m₀))) (m N))
      rw [ih]
      rfl

/-- **The translation.**  If `V` is nilpotent with bound `n`, then every chain of length `K`
annihilates the `N`-th reach as soon as `n ≤ N + K`.  @census none (helper; engine `E7`) -/
theorem pathApply_reach_eq_zero (V : Species.Rep S) {n : ℕ}
    (hn : ∀ (idx : ℕ → S.I) (m : ∀ k, S.M (idx k) (idx (k + 1))) (N : ℕ), n ≤ N →
      ∀ w : V.W (idx 0), V.pathApply idx m N w = 0) :
    ∀ (N : ℕ) (idx : ℕ → S.I) (m : ∀ k, S.M (idx k) (idx (k + 1))) (K : ℕ), n ≤ N + K →
      ∀ u : V.W (idx 0), u ∈ WReach V N (idx 0) → V.pathApply idx m K u = 0 := by
  intro N
  induction N with
  | zero => intro idx m K hK u _; exact hn idx m K (by omega) u
  | succ N ih =>
      intro idx m K hK u hu
      have hgen : ∀ i : S.I,
          AddSubgroup.closure
            {x | ∃ (v : V.W i), v ∈ WReach V N i ∧ ∃ mm : S.M i (idx 0),
              x = V.f i (idx 0) (Balanced.mk v mm)} ≤ pathApplyKer V idx m K := by
        intro i
        refine AddSubgroup.closure_le _ |>.2 ?_
        rintro x ⟨v, hv, mm, rfl⟩
        show V.pathApply idx m K (V.f i (idx 0) (Balanced.mk v mm)) = 0
        rw [← pathApply_consIdx V idx m mm v K]
        exact ih (consIdx i idx) _ (K + 1) (by omega) v hv
      have : WReach V (N + 1) (idx 0) ≤ pathApplyKer V idx m K := iSup_le hgen
      exact this hu

/-- Past the nilpotency bound the species-side reach is trivial.  @census none (helper) -/
theorem exists_WReach_eq_bot (V : Species.Rep S) (h : V.IsNilpotent) :
    ∃ n : ℕ, ∀ N : ℕ, n ≤ N → ∀ j : S.I, WReach V N j = ⊥ := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, fun N hN j => le_bot_iff.1 fun u hu => ?_⟩
  exact pathApply_reach_eq_zero V (fun idx m N' hN' w => hn idx m N' hN' w) N
    (fun _ => j) (fun _ => 0) 0 (by omega) u hu

end Species

/-! ### `E7` step 8 — one `(ε,η)` term, recovered from the descent -/

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Step 8 of `E7`**: each single `(ε,η)` term `phiComp M (ch ε) η u` lies in the `L`-span of the
values `f_{ij}(u ⊗ m)`.  This is the choosing lemma cashed in: `Pi.single` isolates the edge orbit
`ε`, and `span_cosetEval_eq_top` isolates the coset `η`.

@census none (helper; engine `E7`) -/
theorem phiComp_mem_descentSpan (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.vertexFixed (Γ.vertexRep j)))
    (hf : IsEdgeDescent M ch e₀ f)
    (u : ↥(M.vertexFixed (Γ.vertexRep i))) (ε : Γ.EdgeOrbit i j)
    (η : EdgeChoice.CosetIndex Γ (ch ε)) :
    phiComp M (ch ε) η u ∈ Submodule.span L
      (Set.range (fun m : Γ.toSpecies.M i j =>
        ((f (Balanced.mk u m) : M.M (Γ.vertexRep j))))) := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε' : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (ch ε')) :=
    fun ε' => @Fintype.ofFinite _ (finite_cosetIndex (ch ε'))
  -- the `L`-linear map `v ↦ Σ_η v η • phiComp M (ch ε) η u`
  set Θ : (EdgeChoice.CosetIndex Γ (ch ε) → L) →ₗ[L] M.M (Γ.vertexRep j) :=
    ∑ η' : EdgeChoice.CosetIndex Γ (ch ε),
      LinearMap.smulRight (LinearMap.proj η') (phiComp M (ch ε) η' u) with hΘ
  have hΘapp : ∀ v : EdgeChoice.CosetIndex Γ (ch ε) → L,
      Θ v = ∑ η' : EdgeChoice.CosetIndex Γ (ch ε), v η' • phiComp M (ch ε) η' u := by
    intro v
    rw [hΘ, LinearMap.sum_apply]
    rfl
  -- the value of `f` on the generator `m = Pi.single ε x`
  have hval : ∀ x : Γ.edgeOrbitField ε,
      ((f (Balanced.mk u (Pi.single ε x : ∀ ε' : Γ.EdgeOrbit i j, Γ.edgeOrbitField ε'))
          : M.M (Γ.vertexRep j)))
        = Θ (cosetEval (ch ε) x) := by
    intro x
    have hd := hf.2 (phiTotal M ch) (phiTotal_single M ch)
      (Balanced.mk u (Pi.single ε x : ∀ ε' : Γ.EdgeOrbit i j, Γ.edgeOrbitField ε')) 1
    rw [one_smul] at hd
    rw [← hd, phiTotal_e0_generator M ch e₀ hf.1 u _ 1, hΘapp]
    rw [Finset.sum_eq_single ε]
    · refine Finset.sum_congr rfl fun η' _ => ?_
      rw [one_mul, Pi.single_eq_same]
      rfl
    · intro ε' _ hne
      refine Finset.sum_eq_zero fun η' _ => ?_
      rw [Pi.single_eq_of_ne hne]
      show (1 * (EdgeChoice.rep Γ (ch ε') η' * (ch ε').τ⁻¹) ((0 : Γ.edgeOrbitField ε') : L))
        • phiComp M (ch ε') η' u = 0
      rw [ZeroMemClass.coe_zero, map_zero, mul_zero, zero_smul]
    · intro hcon; exact absurd (Finset.mem_univ ε) hcon
  -- transport the spanning statement through `Θ`
  have hmapped : Submodule.map Θ (Submodule.span L (Set.range (cosetEval (ch ε))))
      = Submodule.span L (Θ '' Set.range (cosetEval (ch ε))) := Submodule.map_span _ _
  have hsub : Θ '' Set.range (cosetEval (ch ε))
      ⊆ Set.range (fun m : Γ.toSpecies.M i j =>
        ((f (Balanced.mk u m) : M.M (Γ.vertexRep j)))) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(Pi.single ε x : ∀ ε' : Γ.EdgeOrbit i j, Γ.edgeOrbitField ε'), hval x⟩
  have hmem : Θ (Pi.single η (1 : L)) ∈ Submodule.map Θ
      (Submodule.span L (Set.range (cosetEval (ch ε)))) := by
    rw [span_cosetEval_eq_top]
    exact Submodule.mem_map_of_mem Submodule.mem_top
  rw [hmapped] at hmem
  have hone : Θ (Pi.single η (1 : L)) = phiComp M (ch ε) η u := by
    rw [hΘapp, Finset.sum_eq_single η]
    · rw [Pi.single_eq_same, one_smul]
    · intro η' _ hne
      rw [Pi.single_eq_of_ne hne, zero_smul]
    · intro hcon; exact absurd (Finset.mem_univ η) hcon
  rw [hone] at hmem
  exact Submodule.span_mono hsub hmem

/-! ### `E7` step 9 — the transported species reach on the quiver side -/

open scoped Classical in
/-- `TSpan M N v` — the `L`-span, inside `M(v)`, of the Galois transports of the `N`-th species
reach of `F(M)`.  This is the filtration the CONVERSE induction runs on.

@census none (helper; engine `E7`) -/
noncomputable def TSpan (M : FDRep Γ) (N : ℕ) (v : Γ.V) : Submodule L (M.toRep.M v) :=
  Submodule.span L {x | ∃ (i : Γ.VertexOrbit) (τ : Gal(L/K)) (hτ : τ • Γ.vertexRep i = v)
    (u : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
      u ∈ Species.WReach ((FFunctor Γ).obj M) N i ∧
        x = M.toRep.φ' τ hτ (u : M.toRep.M (Γ.vertexRep i))}

open scoped Classical in
/-- The generators of `TSpan`.  @census none (helper) -/
theorem mem_TSpan (M : FDRep Γ) {N : ℕ} {v : Γ.V} (i : Γ.VertexOrbit) (τ : Gal(L/K))
    (hτ : τ • Γ.vertexRep i = v) (u : ↥(M.toRep.vertexFixed (Γ.vertexRep i)))
    (hu : u ∈ Species.WReach ((FFunctor Γ).obj M) N i) :
    M.toRep.φ' τ hτ (u : M.toRep.M (Γ.vertexRep i)) ∈ TSpan M N v :=
  Submodule.subset_span ⟨i, τ, hτ, u, hu, rfl⟩

open scoped Classical in
/-- The elimination principle for `TSpan`.  @census none (helper) -/
theorem TSpan_le (M : FDRep Γ) {N : ℕ} {v : Γ.V} (T : Submodule L (M.toRep.M v))
    (H : ∀ (i : Γ.VertexOrbit) (τ : Gal(L/K)) (hτ : τ • Γ.vertexRep i = v)
      (u : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
      u ∈ Species.WReach ((FFunctor Γ).obj M) N i →
        M.toRep.φ' τ hτ (u : M.toRep.M (Γ.vertexRep i)) ∈ T) :
    TSpan M N v ≤ T := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, τ, hτ, u, hu, rfl⟩
  exact H i τ hτ u hu

open scoped Classical in
/-- `TSpan` is stable under the semi-linear structure maps.  @census none (helper) -/
theorem TSpan_phi (M : FDRep Γ) (N : ℕ) {v w : Γ.V} (g : Gal(L/K)) (hg : g • v = w)
    {x : M.toRep.M v} (hx : x ∈ TSpan M N v) : M.toRep.φ' g hg x ∈ TSpan M N w := by
  refine TSpan_le M (phiPull M.toRep g hg (TSpan M N w)) ?_ hx
  intro i τ hτ u hu
  show M.toRep.φ' g hg (M.toRep.φ' τ hτ _) ∈ TSpan M N w
  have hmul : (g * τ) • Γ.vertexRep i = w := by rw [mul_smul, hτ, hg]
  rw [M.toRep.φ'_comp g τ hτ hg hmul]
  exact mem_TSpan M i (g * τ) hmul u hu

open scoped Classical in
/-- Past the species-side nilpotency bound, `TSpan` is zero.  @census none (helper) -/
theorem TSpan_eq_bot (M : FDRep Γ) {N : ℕ}
    (hbot : ∀ i : Γ.VertexOrbit, Species.WReach ((FFunctor Γ).obj M) N i = ⊥) (v : Γ.V) :
    TSpan M N v = ⊥ := by
  refine le_bot_iff.1 (TSpan_le M ⊥ ?_)
  intro i τ hτ u hu
  rw [hbot i] at hu
  have hu0 : u = 0 := AddSubgroup.mem_bot.mp hu
  have : (u : M.toRep.M (Γ.vertexRep i)) = 0 := by rw [hu0]; rfl
  rw [this, map_zero]
  exact Submodule.zero_mem _

open scoped Classical in
/-- `TSpan M 0 v = ⊤`: Galois descent (`vertexDescentEquiv`, `RQ2-1.13` at `L/L(v_i)`) says `W_i`
spans `M(v_i)` over `L`, and `φ'` carries that to every vertex of the orbit.
@census none (helper) -/
theorem TSpan_zero (M : FDRep Γ) (v : Γ.V) : TSpan M 0 v = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  obtain ⟨i, τ, rfl⟩ : ∃ (i : Γ.VertexOrbit) (τ : Gal(L/K)), τ • Γ.vertexRep i = v :=
    ⟨Γ.vertexClass v,
      (mem_orbit_iff.mp (Quotient.exact (Γ.vertexClass_vertexRep (Γ.vertexClass v)).symm)).choose,
      (mem_orbit_iff.mp (Quotient.exact (Γ.vertexClass_vertexRep (Γ.vertexClass v)).symm)).choose_spec⟩
  have hτ' : τ⁻¹ • (τ • Γ.vertexRep i) = Γ.vertexRep i := inv_smul_smul τ _
  obtain ⟨z, hz⟩ := (vertexDescentEquiv M.toRep (Γ.vertexRep i)).surjective
    (M.toRep.φ' τ⁻¹ hτ' x)
  rw [← M.toRep.φ'_inv' τ hτ' rfl x, ← hz]
  clear hz
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | tmul a m =>
      rw [vertexDescentEquiv_tmul, M.toRep.φ'_smul]
      exact Submodule.smul_mem _ _ (mem_TSpan M i τ rfl m (by trivial))
  | add p q hp hq => rw [map_add, map_add]; exact Submodule.add_mem _ hp hq

/-! ### `E7` step 10 — an edge map raises the transported reach by one -/

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Step 10 of `E7`**, the converse's engine: an edge map of `Γ` raises `TSpan` by exactly one.

The route is the one `DESIGN-NOTES` §12.5(b) says the tree could not take: pull the edge back to
the orbit representative (`φEdge'_φ'`, twice), recognise the resulting composite as `phiComp`
(`Rep.φ'_vertexFixed_congr` absorbs the difference between the two group elements carrying `v_i`
to `s(e_ε)`), and then use step 8 to write that single `(ε,η)` term as an `L`-combination of
values `f_{ij}(u ⊗ m)` — which is exactly one further step of the species reach.

@census none (helper; engine `E7`) -/
theorem TSpan_edge (M : FDRep Γ) (N : ℕ) (e : Γ.E)
    {x : M.toRep.M (Γ.toRQuiver.source e)} (hx : x ∈ TSpan M N (Γ.toRQuiver.source e)) :
    M.toRep.φEdge e x ∈ TSpan M (N + 1) (Γ.toRQuiver.target e) := by
  classical
  refine TSpan_le M (Submodule.comap (M.toRep.φEdge e)
    (TSpan M (N + 1) (Γ.toRQuiver.target e))) ?_ hx
  intro i τ hτ u hu
  suffices hgoal : M.toRep.φEdge e (M.toRep.φ' τ hτ (u : M.toRep.M (Γ.vertexRep i)))
      ∈ TSpan M (N + 1) (Γ.toRQuiver.target e) from hgoal
  -- (1) pull the edge back along `τ`
  have ha : Γ.toRQuiver.source (τ⁻¹ • e) = Γ.vertexRep i := by
    rw [Γ.source_smul, ← hτ, inv_smul_smul]
  have hb : Γ.toRQuiver.target (τ⁻¹ • e) = τ⁻¹ • Γ.toRQuiver.target e := Γ.target_smul _ _
  have h₂ : τ • (τ⁻¹ • Γ.toRQuiver.target e) = Γ.toRQuiver.target e := smul_inv_smul _ _
  have key1 := M.toRep.φEdge'_φ' τ (smul_inv_smul τ e) ha hb
    (rfl : Γ.toRQuiver.source e = _) (rfl : Γ.toRQuiver.target e = _) hτ h₂
    (u : M.toRep.M (Γ.vertexRep i))
  -- (2) the edge orbit of the pulled-back edge
  set j : Γ.VertexOrbit := Γ.vertexClass (Γ.toRQuiver.target (τ⁻¹ • e)) with hj
  have hmem : (τ⁻¹ • e) ∈ Γ.edgeSet i j := ⟨by rw [ha]; exact Γ.vertexClass_vertexRep i, rfl⟩
  obtain ⟨ε, g, hg⟩ : ∃ (ε : Γ.EdgeOrbit i j) (g : Gal(L/K)), g • Γ.edgeRep ε = τ⁻¹ • e := by
    letI : Setoid ↥(Γ.edgeSet i j) := orbitRel Gal(L/K) (Γ.edgeSet i j)
    refine ⟨Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet i j)) ⟨τ⁻¹ • e, hmem⟩, ?_⟩
    have h0 := Quotient.exact (Quotient.out_eq
      (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet i j)) (⟨τ⁻¹ • e, hmem⟩ : Γ.edgeSet i j)))
    obtain ⟨g, hgg⟩ := mem_orbit_iff.mp (Setoid.symm h0)
    refine ⟨g, ?_⟩
    show g • ((Quotient.out (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet i j))
      ⟨τ⁻¹ • e, hmem⟩) : Γ.edgeSet i j) : Γ.E) = τ⁻¹ • e
    rw [← Γ.coe_smul_edgeSet g _, hgg]
  set ch : ∀ ε' : Γ.EdgeOrbit i j, Γ.EdgeChoice ε' := fun ε' => EdgeChoice.choose Γ ε' with hch
  have h₁ : g • Γ.toRQuiver.source (Γ.edgeRep ε) = Γ.vertexRep i := by
    rw [← Γ.source_smul, hg, ha]
  have h₂g : g • Γ.toRQuiver.target (Γ.edgeRep ε) = τ⁻¹ • Γ.toRQuiver.target e := by
    rw [← Γ.target_smul, hg, hb]
  -- (3) `φ'_g ∘ φ'_{σ_ε}` is the identity on `W_i`
  have hys : (g * (ch ε).σ) • Γ.vertexRep i = Γ.vertexRep i := by
    rw [mul_smul, (ch ε).sourceVertex, h₁]
  have hcomp : M.toRep.φ' g h₁
      (M.toRep.φ' (ch ε).σ (ch ε).sourceVertex (u : M.toRep.M (Γ.vertexRep i)))
        = (u : M.toRep.M (Γ.vertexRep i)) := by
    rw [M.toRep.φ'_comp g (ch ε).σ (ch ε).sourceVertex h₁ hys,
      M.toRep.φ'_vertexFixed_congr u (g * (ch ε).σ) 1 hys (one_smul _ _), M.toRep.φ'_one]
    rfl
  have key2 := M.toRep.φEdge'_φ' g hg (rfl : Γ.toRQuiver.source (Γ.edgeRep ε) = _)
    (rfl : Γ.toRQuiver.target (Γ.edgeRep ε) = _) ha hb h₁ h₂g
    (M.toRep.φ' (ch ε).σ (ch ε).sourceVertex (u : M.toRep.M (Γ.vertexRep i)))
  rw [hcomp] at key2
  -- (4) recognise `phiComp` at an arbitrary coset
  set η : EdgeChoice.CosetIndex Γ (ch ε) :=
    Quotient.mk _ (1 : stabilizer Gal(L/K) (Γ.vertexRep j)) with hη
  have hrho : ((EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹))⁻¹ • Γ.vertexRep j
      = Γ.toRQuiver.target (Γ.edgeRep ε) := by
    rw [← (ch ε).cosetTarget η, inv_smul_smul]
  have hinner : M.toRep.φEdge' (Γ.edgeRep ε) rfl rfl
      (M.toRep.φ' (ch ε).σ (ch ε).sourceVertex (u : M.toRep.M (Γ.vertexRep i)))
      = M.toRep.φ' (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)⁻¹ hrho
          (phiComp M.toRep (ch ε) η u) :=
    (M.toRep.φ'_inv (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹) ((ch ε).cosetTarget η) hrho _).symm
  -- (5) assemble the transport
  have hfin : (τ * (g * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)⁻¹)) • Γ.vertexRep j
      = Γ.toRQuiver.target e := by
    rw [mul_smul, mul_smul, hrho, h₂g, h₂]
  have hgr : (g * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)⁻¹) • Γ.vertexRep j
      = τ⁻¹ • Γ.toRQuiver.target e := by rw [mul_smul, hrho, h₂g]
  have hval : M.toRep.φEdge e (M.toRep.φ' τ hτ (u : M.toRep.M (Γ.vertexRep i)))
      = M.toRep.φ' (τ * (g * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)⁻¹)) hfin
          (phiComp M.toRep (ch ε) η u) := by
    show M.toRep.φEdge' e rfl rfl (M.toRep.φ' τ hτ (u : M.toRep.M (Γ.vertexRep i))) = _
    rw [key1, key2, hinner,
      M.toRep.φ'_comp g (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)⁻¹ hrho h₂g hgr,
      M.toRep.φ'_comp τ (g * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)⁻¹) hgr h₂ hfin]
  rw [hval]
  -- (6) the choosing lemma, and one further species step
  have hspan := phiComp_mem_descentSpan M.toRep ch
    (phi_descends M.toRep ch).choose_spec.2.2.choose (edgeDescentOf M.toRep i j)
    (isEdgeDescent_edgeDescentOf M.toRep i j) u ε η
  refine (Submodule.span_le.2 ?_ : Submodule.span L
    (Set.range (fun m : Γ.toSpecies.M i j =>
      ((edgeDescentOf M.toRep i j (Balanced.mk u m) : M.toRep.M (Γ.vertexRep j)))))
      ≤ phiPull M.toRep (τ * (g * (EdgeChoice.rep Γ (ch ε) η * (ch ε).τ⁻¹)⁻¹)) hfin
        (TSpan M (N + 1) (Γ.toRQuiver.target e))) hspan
  rintro _ ⟨m, rfl⟩
  refine mem_TSpan M j _ hfin (edgeDescentOf M.toRep i j (Balanced.mk u m)) ?_
  refine (le_iSup (fun i' : Γ.VertexOrbit => AddSubgroup.closure
    {y | ∃ (u' : ((FFunctor Γ).obj M).W i'),
      u' ∈ Species.WReach ((FFunctor Γ).obj M) N i' ∧ ∃ mm : Γ.toSpecies.toSpecies.M i' j,
        y = ((FFunctor Γ).obj M).f i' j (Balanced.mk u' mm)}) i) ?_
  exact AddSubgroup.subset_closure ⟨u, hu, m, rfl⟩

/-! ### `E7` step 11 — the converse, and the bridge -/

open scoped Classical in
/-- Every path composite of `Γ` of length `N` lands in `TSpan M N`.  @census none (helper) -/
theorem pathMap_mem_TSpan (M : FDRep Γ) {a b : Γ.V} (p : Quiver.Path a b)
    (x : M.toRep.M a) : M.toRep.pathMap p x ∈ TSpan M p.length b := by
  induction p with
  | nil =>
      rw [M.toRep.pathMap_nil]
      rw [show (Quiver.Path.nil : Quiver.Path a a).length = 0 from rfl, TSpan_zero]
      exact Submodule.mem_top
  | cons p g ih =>
      obtain ⟨e, hs, ht⟩ := g
      subst hs
      subst ht
      rw [M.toRep.pathMap_cons]
      exact TSpan_edge M p.length e ih

open scoped Classical in
/-- **`E7`, the converse direction**: `F = FFunctor Γ` **reflects** nilpotency.
@census none (helper; engine `E7`) -/
theorem FObj_isNilpotent_converse (M : FDRep Γ)
    (h : ((FFunctor Γ).obj M).IsNilpotent) : M.toRep.IsNilpotent := by
  obtain ⟨n, hn⟩ := Species.exists_WReach_eq_bot ((FFunctor Γ).obj M) h
  refine ⟨n, fun a b p hp => LinearMap.ext fun x => ?_⟩
  have hmem := pathMap_mem_TSpan M p x
  rw [TSpan_eq_bot M (hn p.length hp) b, Submodule.mem_bot] at hmem
  exact hmem

open scoped Classical in
/-- **`E7`, the bridge**: `F` preserves AND reflects nilpotency.  This is the first conjunct of
census clauses `RQ-5.06-H3` and `RQ-5.09-H3` (v1 census ids; on the v2 line the claimants of
`RQ2-5.06`, `RQ2-5.09` and `RQ2-5.16` use it, in `Gelfand/Species/Rational.lean` and
`Gelfand/Species/Equivalence.lean`).

It is also the claimant of `cor:nilpotentrelations` (census `RQ2-2.38`, reassigned from S5 to S8 by
coordinator ruling `R-FR-5`, 2026-10-02), bound by a docstring-only `R-PROC-4` amendment of frozen
S8; until then it read `@census none (helper; engine E7)`.

@census    RQ2-2.38
@source    cor:nilpotentrelations
@clauses   RQ2-2.38-H1, RQ2-2.38-C1, RQ2-2.38-C2, RQ2-2.38-H2, RQ2-2.38-C3
@imports   none
@divergence `H1`/`C1`: for every finite Galois `L/K`, every `K`-rational quiver `Γ` and every
`M : FDRep Γ`, `M` is nilpotent iff `F(M)` is; `C1`'s rider "with the same bound `n`" is not
carried (each side's `IsNilpotent` is its own existential). `C2` (the restriction to an equivalence
`Rep^nil(Γ_K) ≌ Rep^nil(S(Γ_K))`) is not a separate declaration: it is derived from this theorem,
the same-module `FFunctor_isEquivalence` and `liftFullSubEquivalence`, the shape v1's
`Gelfand/Corollaries.lean` used and v2's `Gelfand/Species/Equivalence.lean` and
`Gelfand/Species/Rational.lean` use. `H2`/`C3` (the Gelfand relation) are discharged along
`RQ2-5.06`'s route: the relation half is S5's `GelfandRelation.satisfies_RGelfand_iff_relation`
(through `GelfandRelation.repNilRel_RGelfand_iff`), the composite equivalence is
`Gelfand.Species.species_equivalence_intrinsic` (`Gelfand/Species/Rational.lean`; in v1,
`Gelfand.species_equivalence_intrinsic` in `Gelfand/Corollaries.lean`, deleted at WP-13).
Partial, disclosed; no statement is moved by this amendment. -/
theorem FObj_isNilpotent_iff (M : FDRep Γ) :
    M.toRep.IsNilpotent ↔ ((FFunctor Γ).obj M).IsNilpotent :=
  ⟨FObj_isNilpotent M, FObj_isNilpotent_converse M⟩

/-! ### `E7` step 12 — nilpotency is an isomorphism invariant on the species side -/

namespace Species

variable {K'' : Type u} [Field K''] {S : Species K''}

/-- A morphism of species representations intertwines `pathApply`.  @census none (helper) -/
theorem pathApply_hom {V V' : Species.Rep S} (a : Species.Rep.Hom V V') (idx : ℕ → S.I)
    (m : ∀ k, S.M (idx k) (idx (k + 1))) (N : ℕ) (w : V.W (idx 0)) :
    V'.pathApply idx m N (a.ψ (idx 0) w) = a.ψ (idx N) (V.pathApply idx m N w) := by
  induction N with
  | zero => rfl
  | succ N ih =>
      show V'.f _ _ (Balanced.mk (V'.pathApply idx m N (a.ψ (idx 0) w)) (m N))
        = a.ψ (idx (N + 1)) (V.f _ _ (Balanced.mk (V.pathApply idx m N w) (m N)))
      rw [ih, Species.Rep.Hom.comm_mk]

/-- Nilpotency of a species representation is invariant under isomorphism.
@census none (helper) -/
theorem isNilpotent_of_iso {V V' : Species.Rep S} (φ : V ≅ V') (h : V.IsNilpotent) :
    V'.IsNilpotent := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, fun idx m N hN w => ?_⟩
  have hid : ∀ (i : S.I) (y : V'.W i), (φ.hom).ψ i ((φ.inv).ψ i y) = y := by
    intro i y
    exact congrArg (fun t : V' ⟶ V' => t.ψ i y) φ.inv_hom_id
  rw [← hid (idx 0) w, pathApply_hom, hn idx m N hN, map_zero]

end Species

/-! ### `E7` step 13 — `F` is an equivalence, and equivalences restrict to full subcategories -/

open scoped Classical in
/-- `FFunctor Γ` is an equivalence: `species_equivalence_tree` (S5, unconditional) pins S5's
Theorem B to exactly this functor.  @census none (helper) -/
theorem FFunctor_isEquivalence (Γ : RationalQuiver K L) :
    (FFunctor Γ).IsEquivalence := by
  obtain ⟨WK, hWK, e, hF, _⟩ := species_equivalence_tree Γ
  rw [← hF]
  infer_instance

/-- **Restricting an equivalence to full subcategories.**  If `F` is fully faithful, carries `P`
into `Q`, and every `Q`-object is isomorphic to `F` of a `P`-object, then
`ObjectProperty.lift Q (P.ι ⋙ F)` is an equivalence — and its `functor` field IS that lift on the
nose, which is what the pinned `e.functor = …` of `RQ-5.06`/`RQ-5.09` needs.

@census none (helper) -/
noncomputable def liftFullSubEquivalence {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) [F.Full] [F.Faithful]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hQ : ∀ Y : Q.FullSubcategory, ∃ X : C, P X ∧ Nonempty (F.obj X ≅ Y.obj)) :
    P.FullSubcategory ≌ Q.FullSubcategory :=
  letI : (Q.lift (P.ι ⋙ F) hF).EssSurj := ⟨fun Y => by
    obtain ⟨X, hX, ⟨iso⟩⟩ := hQ Y
    exact ⟨⟨X, hX⟩, ⟨Q.ι.preimageIso iso⟩⟩⟩
  letI : (Q.lift (P.ι ⋙ F) hF).IsEquivalence :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  (Q.lift (P.ι ⋙ F) hF).asEquivalence

theorem liftFullSubEquivalence_functor {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) [F.Full] [F.Faithful]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hQ : ∀ Y : Q.FullSubcategory, ∃ X : C, P X ∧ Nonempty (F.obj X ≅ Y.obj)) :
    (liftFullSubEquivalence F P Q hF hQ).functor = Q.lift (P.ι ⋙ F) hF := rfl

end RationalQuiver

end RationalQuivers
