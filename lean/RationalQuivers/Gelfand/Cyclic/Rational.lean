import RationalQuivers.Gelfand.EssSurj.NaturalIso
import RationalQuivers.Gelfand.Split.Cyclic
import RationalQuivers.Species.Examples

/-!
# the case `ℓ = 0`: the rational structure (§5.3, Steps C-1, C-2, C-4)

Engine (suffix `S` where a v2 name was freed): `cyclicQ`, `E_Cyc_rep`, `ObjSpecC`, `phiCyc_eq_conj`,
`E_Cyc_spec`; since the v2 amendment T3-a1 (route fix F-B11) the engine's `φ^{(∞)}_±` at `ℓ = 0` is the
identity by definition (`limAtC`), as in the tex, with no stabilization run.  Native: `φ_{±,σ} := σ` (`E_Cyc_φ`, `eq:varphicyclic`, no stabilization), the cocycle
`c² = 1` (`cyc_cocycle`), Koecher `cX = Yc` (`cyc_equiv`), `𝔼_E(M)` (`E_Cyc_repZ`) and the functor
`E_ECyc`.

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Cyclic.lean (§Target … §CycNilpotent2)` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.Cyclic.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

*(2026-10-21, O-V2-6 round 2.)*  `limPlus_eq_of_one`, which a carried docstring below places in
v1's `Gelfand/Stabilization.lean` (deleted at WP-13, `ae9eda9`), is
`RationalStructure.limPlus_eq_of_one` in `Gelfand/RationalStructure/Stabilization.lean`.

@census none (module)
-/

namespace RationalQuivers.Gelfand.Cyclic

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {Dq : SqrtNegOneExt E}
open scoped TensorProduct Classical

variable {Mi : Type} [AddCommGroup Mi] [Module Dq.carrier Mi]

/-! ### The target -/

section Target

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)

/-- `Γ_E` for the **cyclic** quiver of `ex:cyclic`: `RQuiver.cyclic` with the non-trivial
`Gal(D.carrier/E)`-involution (S8's `Γ_ℚ` at `E = ℚ`).  The general-`E` analogue of `RQ-5.07`'s and
`RQ-5.09`'s target.  *(Corrected 2026-10-02, docstring-only, `V1-09`: the copied text named `Γ_ℚ`.)*

@census none (auxiliary; the target quiver of `RQ-5.07-C2`) -/
noncomputable def cyclicQ : RationalQuiver E Dq.carrier :=
  RationalQuiver.cyclicOfCardTwo E Dq.carrier hcard

/-- The vertices of the cyclic quiver: `−`(=0), `+`(=1).  @census none (helper) -/
abbrev vtxC (v : Fin 2) : (cyclicQ hcard).V := v

/-- The edges of the cyclic quiver: `a : − → +`(=0), `b : + → −`(=1).  @census none (helper) -/
abbrev edgeC (e : Fin 2) : (cyclicQ hcard).E := e

theorem cyclicQ_rho_apply {z : Dq.carrier ≃ₐ[E] Dq.carrier} (hz : z ≠ 1) :
    (cyclicQ hcard).ρ z = RQuiver.cyclicSwap := by
  have hr : (cyclicQ hcard).ρ z = if z = 1 then 1 else RQuiver.cyclicSwap := rfl
  rw [hr, if_neg hz]

/-- `c` acts on the vertices of the cyclic quiver by the swap.  @census none (helper) -/
theorem cyclicQ_smul_vertex (v : Fin 2) :
    Dq.conj • vtxC hcard v = vtxC hcard (RQuiver.twoLoopsSwapPerm v) := by
  show (RQuiver.Aut.toPermV _ ((cyclicQ hcard).ρ Dq.conj)) v = _
  rw [cyclicQ_rho_apply hcard Gelfand.RationalStructure.galConj_ne_one]; rfl

/-- `c` acts on the edges of the cyclic quiver by the swap.  @census none (helper) -/
theorem cyclicQ_smul_edge (e : Fin 2) :
    Dq.conj • edgeC hcard e = edgeC hcard (RQuiver.twoLoopsSwapPerm e) := by
  show (RQuiver.Aut.toPermE _ ((cyclicQ hcard).ρ Dq.conj)) e = _
  rw [cyclicQ_rho_apply hcard Gelfand.RationalStructure.galConj_ne_one]; rfl

/-- `σ • v` on the cyclic quiver, computed.  @census none (helper) -/
theorem cyclicQ_smul_eq (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : Fin 2) :
    σ • vtxC hcard v = vtxC hcard (if σ = 1 then v else RQuiver.twoLoopsSwapPerm v) := by
  by_cases hσ : σ = 1
  · subst hσ; simp [vtxC]
  · rw [if_neg hσ, Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ, cyclicQ_smul_vertex]

/-- `Rep^nil` of the cyclic quiver: the full subcategory of finite-dimensional nilpotent
representations (no relation).  @census none (auxiliary; the target category of `RQ-5.07-C2`) -/
noncomputable abbrev RepNilCycQ : Type 1 := (RationalQuiver.RepNil (cyclicQ hcard)).FullSubcategory

end Target

/-- **`RQ-5.07-H3`** — at `ℓ = 0` the case "`⋆`" is **obsolete**: the two components the `(⋆)` case
would act on, `M_{-(ℓ-1)} = M_{1}` and `M_{ℓ-1} = M_{-1}`, are the *same two* components as the
`(±)` case's `M_{ℓ+1} = M_1` and `M_{-(ℓ+1)} = M_{-1}`. There is nothing left for a third vertex,
which is why the target is the two-vertex cyclic quiver.

@census    none (auxiliary; discharges census clause `RQ-5.07-H3`)
@source    thm:cyclicEEQQequivalence
(clauses of the frozen original:)   RQ-5.07-H3
@imports   none
@divergence none -/
theorem star_case_obsolete (Q : Split.QiSetup Dq.carrier 0 Mi) :
    Q.comp (-(((0 : ℕ) : ℤ) - 1)) = Q.comp (((0 : ℕ) : ℤ) + 1) ∧
      Q.comp (((0 : ℕ) : ℤ) - 1) = Q.comp (-(((0 : ℕ) : ℤ) + 1)) := by
  constructor <;> norm_num

/-! ### The data of `𝔼_ℚ(M)` at `ℓ = 0` -/

section Data

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)
variable (A : HCEObj 0 E Dq)


/-- The vertex family `M(−) = M_{-1}`, `M(+) = M_1`.  @census none (helper) -/
abbrev V2 (v : Fin 2) : Type := ↥(A.setup.weight.comp (cycIdx v))

/-- The edge maps: `a ↦ X : M_{-1} → M_1`, `b ↦ Y : M_1 → M_{-1}`.  @census none (helper) -/
noncomputable def E_Cyc_edge :
    ∀ e : Fin 2, V2 A (RQuiver.cyclic.source e) →ₗ[Dq.carrier] V2 A (RQuiver.cyclic.target e)
  | 0 => A.setup.weight.X.restrict fun _ hv => by
      have h := A.setup.weight.X_mem _ _ hv
      exact (show (cycIdx (RQuiver.cyclic.source 0) + 2 : ℤ) = cycIdx (RQuiver.cyclic.target 0)
        by decide) ▸ h
  | 1 => A.setup.weight.Y.restrict fun _ hv => by
      have h := A.setup.weight.Y_mem _ _ hv
      exact (show (cycIdx (RQuiver.cyclic.source 1) - 2 : ℤ) = cycIdx (RQuiver.cyclic.target 1)
        by decide) ▸ h

/-- The edge maps as endomorphisms of the carrier.  @census none (helper) -/
noncomputable def edgeOpC (e : Fin 2) : Module.End Dq.carrier A.carrier :=
  ![A.setup.weight.X, A.setup.weight.Y] e

theorem E_Cyc_edge_val : ∀ (e : Fin 2) (m : V2 A (RQuiver.cyclic.source e)),
    ((E_Cyc_edge A e m : V2 A (RQuiver.cyclic.target e)) : A.carrier) = edgeOpC A e (m : A.carrier)
  | 0, _ => rfl
  | 1, _ => rfl

/-- The maps `φ^{(∞)}_v` at the two vertices at `ℓ = 0`: **the identity** of `M(−) = M_{-1}` resp.
`M(+) = M_1` (the tex: "at `ℓ = 0` no unipotent stabilization is required … `eq:varphiplus` and
`eq:varphiminus` hold with `φ^{(∞)}_±` replaced by the identity"), extended to the carrier by the
weight projection, since `phiCyc` is total on `A.carrier`.  On the vertex component it is the
identity (`phiCyc_eq_conj`).

v2 R-PROC-4 amendment T3-a1, route fix **F-B11** (TW-4, C-1; WP-16 triage verdict FIX-LEAN): before,
this was the limit of the `(∓)` unipotent stabilization runs at `ℓ = 0`
(`![(inputMinus A.setup).limPlus, (inputPlus A.setup).limPlus]`), proved equal to the identity
afterwards (`limPlus_inputMinus_zero`, `limPlus_inputPlus_zero`, kept off-path).  Type unchanged.
@census none (helper) -/
noncomputable def limAtC (v : Fin 2) : Module.End Dq.carrier A.carrier :=
  ![A.setup.weight.proj (-1), A.setup.weight.proj 1] v

theorem limAtC_mem : ∀ (v : Fin 2) (m : A.carrier),
    limAtC A v m ∈ A.setup.weight.comp (-(cycIdx (RQuiver.twoLoopsSwapPerm v)))
  | 0, m => by
      have h : (-(cycIdx (RQuiver.twoLoopsSwapPerm 0)) : ℤ) = -1 := by decide
      rw [h]; exact A.setup.weight.proj_mem (-1) m
  | 1, m => by
      have h : (-(cycIdx (RQuiver.twoLoopsSwapPerm 1)) : ℤ) = 1 := by decide
      rw [h]; exact A.setup.weight.proj_mem 1 m

/-- `φ_{v,c} := c ∘ φ^{(∞)}_v` at `ℓ = 0`, with `φ^{(∞)}_v` the identity of `M(v)` (`limAtC`): on the
vertex component `φ_{v,c} = c`, i.e. `eq:varphicyclic`, by definition (`phiCyc_eq_conj`).
@census none (helper)
@clauses   RQ2-5.24-S-TW4 -/
noncomputable def phiCyc (v : Fin 2) (m : A.carrier) : A.carrier :=
  A.setup.conj (limAtC A v m)

theorem phiCyc_mem (v : Fin 2) (m : A.carrier) :
    phiCyc A v m ∈ A.setup.weight.comp (cycIdx (RQuiver.twoLoopsSwapPerm v)) := by
  have h := A.setup.conj_comp _ _ (limAtC_mem A v m)
  rwa [neg_neg] at h

theorem phiCyc_add (v : Fin 2) (m m' : A.carrier) :
    phiCyc A v (m + m') = phiCyc A v m + phiCyc A v m' := by simp only [phiCyc, map_add]

theorem phiCyc_smul (v : Fin 2) (a : Dq.carrier) (m : A.carrier) :
    phiCyc A v (a • m) = Dq.conj a • phiCyc A v m := by
  simp only [phiCyc, map_smul, A.setup.conj_smul]

/-- The propositions `𝔼_ℚ(M)` needs at `ℓ = 0`: the cocycle condition, the equivariance for the
two edges, and nilpotency.  @census none (auxiliary; the bundle `E_CycFunctor` consumes) -/
structure ObjSpecC : Prop where
  cocycle : ∀ (v : Fin 2) (m : A.carrier), m ∈ A.setup.weight.comp (cycIdx v) →
    phiCyc A (RQuiver.twoLoopsSwapPerm v) (phiCyc A v m) = m
  equiv : ∀ (e : Fin 2) (m : A.carrier), m ∈ A.setup.weight.comp (cycIdx (RQuiver.cyclic.source e)) →
    edgeOpC A (RQuiver.twoLoopsSwapPerm e) (phiCyc A (RQuiver.cyclic.source e) m)
      = phiCyc A (RQuiver.cyclic.target e) (edgeOpC A e m)
  nilpotent : ∃ n : ℕ, ∀ (a b : (cyclicQ hcard).V) (p : Quiver.Path a b), n ≤ p.length →
    RationalQuiver.pathCompose (Q := (cyclicQ hcard).toRQuiver) (V2 A) (E_Cyc_edge A) p = 0

/-- Functoriality of the limits at `ℓ = 0`.  @census none (auxiliary) -/
def HomSpecC {A B : HCEObj 0 E Dq} (f : A ⟶ B) : Prop :=
  ∀ (v : Fin 2) (m : A.carrier), f.toLinearMap (limAtC A v m) = limAtC B v (f.toLinearMap m)

/-- The joint specification of `𝔼_ℚ` at `ℓ = 0`.  @census none (auxiliary) -/
def E_CycSpec : Prop :=
  (∀ A : HCEObj 0 E Dq, ObjSpecC hcard A) ∧ (∀ (A B : HCEObj 0 E Dq) (f : A ⟶ B), HomSpecC f)

/-- The Galois action on the carrier at a vertex.  @census none (helper) -/
noncomputable def galActC (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : Fin 2) (m : A.carrier) :
    A.carrier :=
  if σ = 1 then m else phiCyc A v m

theorem galActC_one (v : Fin 2) (m : A.carrier) : galActC A 1 v m = m := by simp [galActC]

theorem galActC_of_ne {σ : Dq.carrier ≃ₐ[E] Dq.carrier} (hσ : σ ≠ 1) (v : Fin 2)
    (m : A.carrier) : galActC A σ v m = phiCyc A v m := by simp [galActC, hσ]

theorem galActC_mem (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : Fin 2) (m : A.carrier)
    (hm : m ∈ A.setup.weight.comp (cycIdx v)) :
    galActC A σ v m ∈ A.setup.weight.comp (cycIdx (σ • vtxC hcard v)) := by
  rw [cyclicQ_smul_eq]
  by_cases hσ : σ = 1
  · subst hσ; rw [galActC_one, if_pos rfl]; exact hm
  · rw [galActC_of_ne A hσ, if_neg hσ]; exact phiCyc_mem A v m

theorem twoLoopsSwapPerm_swap (v : Fin 2) :
    RQuiver.twoLoopsSwapPerm (RQuiver.twoLoopsSwapPerm v) = v := by
  fin_cases v <;> rfl

/-- `φ_{v,σ} : M(v) ≃+ M(σ • v)` at `ℓ = 0`.  @census none (helper) -/
noncomputable def E_Cyc_φS (h : ObjSpecC hcard A) (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : Fin 2) :
    V2 A v ≃+ V2 A (σ • vtxC hcard v) where
  toFun m := ⟨galActC A σ v m, galActC_mem hcard A σ v m m.2⟩
  invFun m := ⟨galActC A σ (if σ = 1 then v else RQuiver.twoLoopsSwapPerm v) m, by
    obtain ⟨m, hm⟩ := m
    rw [cyclicQ_smul_eq] at hm
    by_cases hσ : σ = 1
    · subst hσ; rw [galActC_one]; simpa using hm
    · rw [galActC_of_ne A hσ, if_neg hσ]
      have := phiCyc_mem A (RQuiver.twoLoopsSwapPerm v) m
      rwa [twoLoopsSwapPerm_swap] at this⟩
  left_inv m := by
    refine Subtype.ext ?_
    show galActC A σ _ (galActC A σ v m) = m
    by_cases hσ : σ = 1
    · subst hσ; rw [galActC_one, galActC_one]
    · rw [galActC_of_ne A hσ, galActC_of_ne A hσ, if_neg hσ]
      exact h.cocycle v m m.2
  right_inv m := by
    obtain ⟨m, hm⟩ := m
    refine Subtype.ext ?_
    show galActC A σ v (galActC A σ _ m) = m
    by_cases hσ : σ = 1
    · subst hσ; rw [galActC_one, galActC_one]
    · rw [galActC_of_ne A hσ, galActC_of_ne A hσ, if_neg hσ]
      rw [cyclicQ_smul_eq, if_neg hσ] at hm
      have := h.cocycle (RQuiver.twoLoopsSwapPerm v) m hm
      rwa [twoLoopsSwapPerm_swap] at this
  map_add' m m' := by
    refine Subtype.ext ?_
    show galActC A σ v (m + m') = galActC A σ v m + galActC A σ v m'
    by_cases hσ : σ = 1
    · subst hσ; simp [galActC_one]
    · simp only [galActC_of_ne A hσ, phiCyc_add]

theorem sigma_ext_valC {v w : (cyclicQ hcard).V} (hvw : v = w) (m : V2 A v) (n : V2 A w)
    (h : (m : A.carrier) = (n : A.carrier)) :
    (⟨v, m⟩ : (u : (cyclicQ hcard).V) × V2 A u) = ⟨w, n⟩ := by
  subst hvw
  exact congrArg _ (Subtype.ext h)

/-- **`𝔼_ℚ(M)` as a rational representation of the cyclic quiver** (`RQ-5.07-C1`, given
`ObjSpecC`).

@census    none (auxiliary; the object map of `𝔼_ℚ` at `ℓ = 0`, clause `RQ-5.07-C1`)
@source    thm:cyclicEEQQequivalence
(clauses of the frozen original:)   RQ-5.07-C1
@imports   none
@divergence none -/
noncomputable def E_Cyc_rep (h : ObjSpecC hcard A) : RationalQuiver.Rep (cyclicQ hcard) :=
  RationalQuiver.Rep.ofFiniteDimensional (Γ := cyclicQ hcard) (V2 A)
    (fun σ v => E_Cyc_φS hcard A h σ v)
    (fun σ v a m => by
      refine Subtype.ext ?_
      show galActC A σ v (a • m) = σ a • galActC A σ v m
      by_cases hσ : σ = 1
      · subst hσ; simp [galActC_one]
      · rw [galActC_of_ne A hσ, galActC_of_ne A hσ, phiCyc_smul, Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ])
    (fun σ τ v m => by
      refine sigma_ext_valC hcard A (mul_smul σ τ (vtxC hcard v)).symm _ _ ?_
      show galActC A σ _ (galActC A τ v m) = galActC A (σ * τ) v m
      by_cases hσ : σ = 1
      · subst hσ; rw [galActC_one, one_mul]
      · by_cases hτ : τ = 1
        · subst hτ; rw [galActC_one, mul_one]; simp [galActC]
        · have hστ : σ * τ = 1 := by
            rw [Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ, Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hτ, Gelfand.RationalStructure.galConj_mul_self]
          rw [hστ, galActC_one, galActC_of_ne A hσ, galActC_of_ne A hτ]
          have hv : τ • vtxC hcard v = vtxC hcard (RQuiver.twoLoopsSwapPerm v) := by
            rw [cyclicQ_smul_eq, if_neg hτ]
          show phiCyc A (τ • vtxC hcard v) (phiCyc A v m) = m
          rw [hv]
          exact h.cocycle v m m.2)
    (fun e => E_Cyc_edge A e)
    (fun σ e m m' hmm' => by
      have hsrc := (cyclicQ hcard).source_smul σ e
      have htgt := (cyclicQ hcard).target_smul σ e
      have hm' : (m' : A.carrier) = galActC A σ (RQuiver.cyclic.source e) m := by
        have h2 := (Sigma.mk.inj_iff.mp hmm').2
        exact (Subtype.heq_iff_coe_eq (fun x => by rw [hsrc])).mp h2
      refine sigma_ext_valC hcard A htgt _ _ ?_
      refine (E_Cyc_edge_val A (σ • e) m').trans ?_
      refine Eq.trans ?_ (congrArg (galActC A σ _) (E_Cyc_edge_val A e m)).symm
      rw [hm']
      by_cases hσ : σ = 1
      · subst hσ
        rw [galActC_one, galActC_one, one_smul]
      · rw [galActC_of_ne A hσ, galActC_of_ne A hσ, Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ,
          cyclicQ_smul_edge hcard e]
        exact h.equiv e m m.2)

/-- `𝔼_ℚ(M)` at `ℓ = 0` as an object of `Rep^nil` of the cyclic quiver.  @census none (helper) -/
noncomputable def E_Cyc_obj (h : ObjSpecC hcard A) : RepNilCycQ hcard :=
  ⟨⟨E_Cyc_rep hcard A h, fun _ => A.admissible _⟩, h.nilpotent⟩

end Data

/-! ### The functor and the theorem -/

section Functor

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)

/-- The vertex components of `𝔼_ℚ(f)` at `ℓ = 0`.  @census none (helper) -/
noncomputable def E_Cyc_map_ψ {A B : HCEObj 0 E Dq} (f : A ⟶ B) (v : Fin 2) :
    V2 A v →ₗ[Dq.carrier] V2 B v :=
  f.toLinearMap.restrict fun _ hv => f.map_comp _ _ hv

theorem E_Cyc_map_edge {A B : HCEObj 0 E Dq} (f : A ⟶ B) :
    ∀ (e : Fin 2) (m : V2 A (RQuiver.cyclic.source e)),
      E_Cyc_map_ψ f (RQuiver.cyclic.target e) (E_Cyc_edge A e m)
        = E_Cyc_edge B e (E_Cyc_map_ψ f (RQuiver.cyclic.source e) m)
  | 0, m => Subtype.ext (f.map_X _)
  | 1, m => Subtype.ext (f.map_Y _)

/-- `𝔼_ℚ(f)` at `ℓ = 0`.  @census none (helper) -/
noncomputable def E_Cyc_hom {A B : HCEObj 0 E Dq} (hA : ObjSpecC hcard A) (hB : ObjSpecC hcard B)
    (f : A ⟶ B) (hf : HomSpecC f) :
    RationalQuiver.Rep.Hom (E_Cyc_rep hcard A hA) (E_Cyc_rep hcard B hB) where
  ψ v := E_Cyc_map_ψ f v
  edge e m := E_Cyc_map_edge f e m
  rational σ v m := by
    obtain ⟨m, hm⟩ := m
    refine Subtype.ext ?_
    show f.toLinearMap (galActC A σ v m) = galActC B σ v (f.toLinearMap m)
    by_cases hσ : σ = 1
    · subst hσ; rw [galActC_one, galActC_one]
    · rw [galActC_of_ne A hσ, galActC_of_ne B hσ]
      show f.toLinearMap (A.setup.conj (limAtC A v m)) = B.setup.conj (limAtC B v (f.toLinearMap m))
      rw [f.map_conj, hf v m]

/-- **`𝔼_ℚ` as a functor at `ℓ = 0`**, `HC_0(𝔤,K)_ℚ ⥤ Rep^nil(cyclic_ℚ)`, given its specification.

@census    none (auxiliary; the functor of `RQ-5.07`)
@source    thm:cyclicEEQQequivalence
@imports   none
@divergence none -/
noncomputable def E_CycFunctor (h : E_CycSpec hcard) : HCEObj 0 E Dq ⥤ RepNilCycQ hcard where
  obj A := E_Cyc_obj hcard A (h.1 A)
  map f := ⟨E_Cyc_hom hcard (h.1 _) (h.1 _) f (h.2 _ _ f)⟩
  map_id A := by
    apply ObjectProperty.hom_ext
    exact RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)


/-! ### `E_CycSpec`, at `ℓ = 0`: `φ_{v,c} = c`

*(v2 R-PROC-4 amendment T3-a1, route fix F-B11.)*  Since the amendment `limAtC` is the identity of
the vertex components by definition, so `φ_{v,c} = c` (`phiCyc_eq_conj`) and `HomSpecC`
(`cyc_homSpec`) no longer pass through the stabilization runs.  The lemmas of this section on the
`(±)` runs at `ℓ = 0` (`tMinus_zero`, `limPlus_inputPlus_zero`, `limPlus_inputMinus_zero`) are kept,
off the route of `E_CycSpec`.  The note below describes the earlier route.

The source's "at `ℓ = 0` the case `(⋆)` is obsolete and one obtains analogously" is, on the
`(±)` runs, the statement that they stabilize at step 0: `T_± = 𝟏` because the Casimir product
`∏_{j=0}^{ℓ-2}` defining them is EMPTY at `ℓ = 0` and `γ_⋆(0) = 0! = 1`, so both maps of
`inputPlus`/`inputMinus` are `𝟏` and `Gelfand/Stabilization.lean`'s `limPlus_eq_of_one` applies.
Hence `φ_{v,c} = c ∘ φ^{(∞)}_v = c` on the two vertex components, and `ObjSpecC`'s cocycle and
equivariance conditions are exactly `c² = 𝟏` (`conj_involutive`) and `cX = Yc`, `cY = Xc`
(`conj_X`, `conj_Y`) — three fields of S7's `RationalSetup`, with no `ℓ = 0` engine of their own.
`stages/S8/DESIGN-NOTES.md` §20.2. -/

section CycSpec

variable {Mq : Type} [AddCommGroup Mq] [Module E Mq]

/-- **`T_- = 𝟏` at `ℓ = 0`** — the Casimir product is empty and `γ_⋆(0) = 0! = 1`.
@census none (helper) -/
theorem tMinus_zero (Q : Split.QiSetup Dq.carrier 0 Mi) : Split.tMinus Q = 1 := by
  show ((4 : Dq.carrier) ^ (0 - 1) * Split.gammaStarF Dq.carrier 0 ^ 2)⁻¹
    • casimirFactorProd Q.weight.casimir ((0 : ℤ) - 2) (0 - 1) = 1
  rw [Split.gammaStarF_eq]
  norm_num [casimirFactorProd]

/-- `φ^{(∞)}_+ = 𝟏` on `M_1` at `ℓ = 0`.  @census none (helper) -/
theorem limPlus_inputPlus_zero (S : RationalSetupOver 0 E Dq Mq Mi) (m : Mi)
    (hm : m ∈ S.weight.comp 1) : (Gelfand.RationalStructure.inputPlus S).limPlus m = m := by
  refine Gelfand.RationalStructure.limPlus_eq_of_one (Gelfand.RationalStructure.inputPlus S) rfl (tMinus_zero S.toQiSetup) ?_ ?_ m ?_
  · intro v hv
    show (1 : Module.End Dq.carrier Mi) v ∈ S.weight.comp (-(-(((0 : ℕ) : ℤ) + 1)))
    rw [neg_neg]; exact hv
  · intro v hv
    show (1 : Module.End Dq.carrier Mi) v ∈ S.weight.comp (-(((0 : ℕ) : ℤ) + 1))
    exact hv
  · show m ∈ S.weight.comp (((0 : ℕ) : ℤ) + 1)
    norm_num
    exact hm

/-- `φ^{(∞)}_- = 𝟏` on `M_{-1}` at `ℓ = 0`.  @census none (helper) -/
theorem limPlus_inputMinus_zero (S : RationalSetupOver 0 E Dq Mq Mi) (m : Mi)
    (hm : m ∈ S.weight.comp (-1)) : (Gelfand.RationalStructure.inputMinus S).limPlus m = m := by
  refine Gelfand.RationalStructure.limPlus_eq_of_one (Gelfand.RationalStructure.inputMinus S) (tMinus_zero S.toQiSetup) rfl ?_ ?_ m ?_
  · intro v hv
    show (1 : Module.End Dq.carrier Mi) v ∈ S.weight.comp (-(((0 : ℕ) : ℤ) + 1))
    exact hv
  · intro v hv
    show (1 : Module.End Dq.carrier Mi) v ∈ S.weight.comp (-(-(((0 : ℕ) : ℤ) + 1)))
    rw [neg_neg]; exact hv
  · show m ∈ S.weight.comp (-(((0 : ℕ) : ℤ) + 1))
    norm_num
    exact hm

end CycSpec

section CycSpec2


/-- **At `ℓ = 0`, `φ_{v,c} = c`** on the two vertex components.  @census none (helper) -/
theorem phiCyc_eq_conj (A : HCEObj 0 E Dq) : ∀ (v : Fin 2) (m : A.carrier),
    m ∈ A.setup.weight.comp (cycIdx v) → phiCyc A v m = A.setup.conj m
  | 0, m, hm => by
      show A.setup.conj (A.setup.weight.proj (-1) m) = _
      rw [A.setup.weight.proj_of_mem_same (n := -1) hm]
  | 1, m, hm => by
      show A.setup.conj (A.setup.weight.proj 1 m) = _
      rw [A.setup.weight.proj_of_mem_same (n := 1) hm]

/-- **`ObjSpecC`'s cocycle condition at `ℓ = 0`** — `c² = 𝟏`.  @census none (helper) -/
theorem cyc_cocycleS (A : HCEObj 0 E Dq) : ∀ (v : Fin 2) (m : A.carrier),
    m ∈ A.setup.weight.comp (cycIdx v) →
      phiCyc A (RQuiver.twoLoopsSwapPerm v) (phiCyc A v m) = m := by
  intro v m hm
  have h1 : phiCyc A v m = A.setup.conj m := phiCyc_eq_conj A v m hm
  have h2 : phiCyc A v m ∈ A.setup.weight.comp (cycIdx (RQuiver.twoLoopsSwapPerm v)) :=
    phiCyc_mem A v m
  rw [phiCyc_eq_conj A _ _ h2, h1]
  exact A.setup.conj_involutive m

/-- **`ObjSpecC`'s equivariance condition at `ℓ = 0`** — `cX = Yc` and `cY = Xc`.
@census none (helper) -/
theorem cyc_equivS (A : HCEObj 0 E Dq) : ∀ (e : Fin 2) (m : A.carrier),
    m ∈ A.setup.weight.comp (cycIdx (RQuiver.cyclic.source e)) →
      edgeOpC A (RQuiver.twoLoopsSwapPerm e) (phiCyc A (RQuiver.cyclic.source e) m)
        = phiCyc A (RQuiver.cyclic.target e) (edgeOpC A e m) := by
  intro e m hm
  fin_cases e
  · have hX : A.setup.weight.X m ∈ A.setup.weight.comp (cycIdx 1) := by
      have h := A.setup.weight.X_mem (-1) m (by simpa [cycIdx] using hm)
      simpa [cycIdx] using h
    show A.setup.weight.Y (phiCyc A 0 m) = phiCyc A 1 (A.setup.weight.X m)
    rw [phiCyc_eq_conj A 0 m (by simpa [cycIdx] using hm), phiCyc_eq_conj A 1 _ hX]
    exact (A.setup.conj_X m).symm
  · have hY : A.setup.weight.Y m ∈ A.setup.weight.comp (cycIdx 0) := by
      have h := A.setup.weight.Y_mem 1 m (by simpa [cycIdx] using hm)
      simpa [cycIdx] using h
    show A.setup.weight.X (phiCyc A 1 m) = phiCyc A 0 (A.setup.weight.Y m)
    rw [phiCyc_eq_conj A 1 m (by simpa [cycIdx] using hm), phiCyc_eq_conj A 0 _ hY]
    exact (A.setup.conj_Y m).symm

/-- **`HomSpecC` at `ℓ = 0`** — both limits are the weight projections onto their component
(`limAtC`), so functoriality is `WeightData.proj_comm_of_map` (route fix F-B11, T3-a1).
@census none (helper) -/
theorem cyc_homSpec {A B : HCEObj 0 E Dq} (f : A ⟶ B) : HomSpecC f := by
  intro v m
  fin_cases v
  · show f.toLinearMap (A.setup.weight.proj (-1) m) = B.setup.weight.proj (-1) (f.toLinearMap m)
    exact (HC.WeightData.proj_comm_of_map A.setup.weight B.setup.weight f.toLinearMap
      (fun n v hv => f.map_comp n v hv) _ m).symm
  · show f.toLinearMap (A.setup.weight.proj 1 m) = B.setup.weight.proj 1 (f.toLinearMap m)
    exact (HC.WeightData.proj_comm_of_map A.setup.weight B.setup.weight f.toLinearMap
      (fun n v hv => f.map_comp n v hv) _ m).symm

end CycSpec2


/-! ### `ObjSpecC`'s nilpotency at `ℓ = 0`

The loop at the `+` vertex is `X ∘ Y` on `M_1`, and `prop:XY_C_relation` at `n = 1` reads
`4·X(Yv) = Cv − (1−1)²·v = Cv`.  At `λ = ℓ² = 0` the Casimir itself is nilpotent (the generalized
infinitesimal character), so the loop is nilpotent, and every path of length `2m + 1` factors
through `m` copies of it — the cyclic quiver's analogue of `qiLoop_pathMap_peel`, and simpler
because the quiver has exactly one edge in and one edge out at each vertex.
`stages/S8/DESIGN-NOTES.md` §20.3. -/

section CycNilpotent

variable (A : HCEObj 0 E Dq)

/-- `C` maps `M_1` into itself.  @census none (helper) -/
theorem cyc_casimir_mapsTo : ∀ v ∈ A.setup.weight.comp (cycIdx 1),
    (A.setup.weight.casimir - ((((0 : ℕ)) : Dq.carrier) ^ 2)
      • (1 : Module.End Dq.carrier A.carrier)) v ∈ A.setup.weight.comp (cycIdx 1) :=
  fun v hv => Split.casimir_sub_sq_mem A.setup.toQiSetup _ hv

/-- The loop at the `+` vertex of the cyclic quiver: `X ∘ Y` on `M_1`.  @census none (helper) -/
noncomputable def cycLoop : Module.End Dq.carrier (V2 A 1) :=
  (E_Cyc_edge A 0).comp (E_Cyc_edge A 1)

/-- **`4·(X∘Y) = C` on `M_1`** at `ℓ = 0` — `prop:XY_C_relation` at `n = 1`.
@census none (helper) -/
theorem four_smul_cycLoop :
    (4 : Dq.carrier) • cycLoop A
      = (A.setup.weight.casimir - ((((0 : ℕ)) : Dq.carrier) ^ 2)
          • (1 : Module.End Dq.carrier A.carrier)).restrict (cyc_casimir_mapsTo A) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨v, hv⟩ := x
  show (4 : Dq.carrier) • A.setup.weight.X (A.setup.weight.Y v)
    = A.setup.weight.casimir v - ((((0 : ℕ)) : Dq.carrier) ^ 2) • v
  have h := Split.four_X_Y_apply A.setup.toQiSetup (cycIdx 1) v hv
  have hc : (((cycIdx 1 : ℤ) : Dq.carrier) - 1) ^ 2 = ((((0 : ℕ)) : Dq.carrier) ^ 2) := by
    norm_num [cycIdx]
  rwa [hc] at h

/-- The loop is nilpotent: at `λ = 0` the Casimir is.  @census none (helper) -/
theorem cycLoop_pow_eq_zero : ∃ m : ℕ, (cycLoop A) ^ m = 0 := by
  obtain ⟨m, hm⟩ := Module.End.isNilpotent.restrict (cyc_casimir_mapsTo A)
    A.setup.toQiSetup.gic_nilpotent
  refine ⟨m, ?_⟩
  have h4 : ((4 : Dq.carrier) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have heq : (4 : Dq.carrier) ^ m • (cycLoop A) ^ m
      = (4 : Dq.carrier) ^ m • (0 : Module.End Dq.carrier (V2 A 1)) := by
    rw [smul_zero, ← smul_pow, four_smul_cycLoop]
    exact hm
  exact smul_right_injective _ h4 heq

end CycNilpotent

section CycNilpotent2

/-- An edge landing away from `+` starts at `+`.  @census none (helper) -/
theorem cyc_edge_dichotomy {x y : (cyclicQ hcard).V} (g : x ⟶ y) (hy : y ≠ vtxC hcard 1) :
    x = vtxC hcard 1 := by
  obtain ⟨k, hs, ht⟩ :=
    (g : {e : Fin 2 // RQuiver.cyclic.source e = x ∧ RQuiver.cyclic.target e = y})
  obtain ⟨kv, hkv⟩ := k
  interval_cases kv <;> first
    | exact absurd ht.symm hy
    | exact hs.symm

/-- No self-loop at `+`.  @census none (helper) -/
theorem cyc_no_selfloop {x : (cyclicQ hcard).V} (g : x ⟶ vtxC hcard 1) : x ≠ vtxC hcard 1 := by
  obtain ⟨k, hs, ht⟩ :=
    (g : {e : Fin 2 // RQuiver.cyclic.source e = x ∧ RQuiver.cyclic.target e = vtxC hcard 1})
  have hkey : ∀ e : Fin 2, RQuiver.cyclic.target e = (1 : Fin 2) →
      RQuiver.cyclic.source e ≠ (1 : Fin 2) := by decide
  rw [← hs]
  exact hkey k ht

variable (A : HCEObj 0 E Dq)

/-- The path composite of the `ℓ = 0` edge family.  @census none (helper) -/
noncomputable abbrev cycPath {a b : (cyclicQ hcard).V} (p : Quiver.Path a b) :
    V2 A a →ₗ[Dq.carrier] V2 A b :=
  RationalQuiver.pathCompose (Q := (cyclicQ hcard).toRQuiver) (V2 A) (E_Cyc_edge A) p

/-- A length-two window based at `+` is the loop.  @census none (helper) -/
theorem cycLoop_arrow_comp {w : (cyclicQ hcard).V}
    (g1 : (vtxC hcard 1) ⟶ w) (g2 : w ⟶ (vtxC hcard 1)) :
    RationalQuiver.arrowCompose (Q := (cyclicQ hcard).toRQuiver) (V2 A) (E_Cyc_edge A) g2 ∘ₗ
        RationalQuiver.arrowCompose (Q := (cyclicQ hcard).toRQuiver) (V2 A) (E_Cyc_edge A) g1
      = cycLoop A := by
  obtain ⟨k1, hs1, ht1⟩ :=
    (g1 : {e : Fin 2 // RQuiver.cyclic.source e = (1 : Fin 2) ∧ RQuiver.cyclic.target e = w})
  obtain ⟨k2, hs2, ht2⟩ :=
    (g2 : {e : Fin 2 // RQuiver.cyclic.source e = w ∧ RQuiver.cyclic.target e = (1 : Fin 2)})
  have hkey : ∀ e1 e2 : Fin 2, RQuiver.cyclic.source e1 = (1 : Fin 2) →
      RQuiver.cyclic.target e2 = (1 : Fin 2) →
      RQuiver.cyclic.target e1 = RQuiver.cyclic.source e2 → e1 = 1 ∧ e2 = 0 := by decide
  obtain ⟨rfl, rfl⟩ := hkey k1 k2 hs1 ht2 (ht1.trans hs2.symm)
  subst ht1
  rfl

/-- Peeling `2k` `+`-based windows off the end of a path landing at `+`.  @census none (helper) -/
theorem cycLoop_path_peel :
    ∀ (k : ℕ) (a : (cyclicQ hcard).V) (p : Quiver.Path a (vtxC hcard 1)),
      2 * k ≤ p.length →
      ∃ q : Quiver.Path a (vtxC hcard 1), q.length = p.length - 2 * k ∧
        ∀ v, cycPath hcard A p v = ((cycLoop A) ^ k) (cycPath hcard A q v) := by
  intro k
  induction k with
  | zero => intro a p _; exact ⟨p, by simp, fun v => by simp⟩
  | succ k ih =>
    intro a p hp
    cases p with
    | nil => simp [Quiver.Path.length] at hp
    | cons q1 g_last =>
      rename_i X
      have hXne : X ≠ vtxC hcard 1 := cyc_no_selfloop hcard g_last
      have hp1 : 2 * k + 1 ≤ q1.length := by
        simp only [Quiver.Path.length] at hp; omega
      cases q1 with
      | nil => simp at hp1
      | cons q2 g_prev =>
        rename_i Y
        have hY : Y = vtxC hcard 1 := cyc_edge_dichotomy hcard g_prev hXne
        subst hY
        have hp2 : 2 * k ≤ q2.length := by
          simp only [Quiver.Path.length] at hp1; omega
        obtain ⟨q, hqlen, hqeq⟩ := ih _ q2 hp2
        refine ⟨q, by simp only [Quiver.Path.length] at hqlen ⊢; omega, fun v => ?_⟩
        have hloop := cycLoop_arrow_comp hcard A g_prev g_last
        have hloop_apply : ∀ u : V2 A 1,
            RationalQuiver.arrowCompose (Q := (cyclicQ hcard).toRQuiver) (V2 A) (E_Cyc_edge A)
                g_last (RationalQuiver.arrowCompose (Q := (cyclicQ hcard).toRQuiver) (V2 A)
                  (E_Cyc_edge A) g_prev u)
              = cycLoop A u := fun u => by
          have h := LinearMap.congr_fun hloop u
          rwa [LinearMap.comp_apply] at h
        have step1 : cycPath hcard A ((q2.cons g_prev).cons g_last) v
            = RationalQuiver.arrowCompose (Q := (cyclicQ hcard).toRQuiver) (V2 A) (E_Cyc_edge A)
                g_last (RationalQuiver.arrowCompose (Q := (cyclicQ hcard).toRQuiver) (V2 A)
                  (E_Cyc_edge A) g_prev (cycPath hcard A q2 v)) := by
          show RationalQuiver.pathCompose _ _ ((q2.cons g_prev).cons g_last) v = _
          rw [RationalQuiver.pathCompose_cons, RationalQuiver.pathCompose_cons,
            LinearMap.comp_apply, LinearMap.comp_apply]
        have hpow_apply : ∀ z : V2 A 1,
            (((cycLoop A) ^ (k + 1)) z) = cycLoop A (((cycLoop A) ^ k) z) := by
          intro z
          rw [pow_succ', Module.End.mul_apply]
        rw [step1, hqeq, hloop_apply]
        exact (hpow_apply (cycPath hcard A q v)).symm

/-- **`ObjSpecC`'s nilpotency at `ℓ = 0`.**  @census none (helper) -/
theorem cyc_nilpotentS : ∃ n : ℕ, ∀ (a b : (cyclicQ hcard).V) (p : Quiver.Path a b), n ≤ p.length →
    RationalQuiver.pathCompose (Q := (cyclicQ hcard).toRQuiver) (V2 A) (E_Cyc_edge A) p = 0 := by
  obtain ⟨m, hm⟩ := cycLoop_pow_eq_zero A
  refine ⟨2 * m + 1, fun a b p hp => LinearMap.ext fun v => ?_⟩
  show cycPath hcard A p v = 0
  by_cases hb : b = vtxC hcard 1
  · subst hb
    obtain ⟨q, _, hq⟩ := cycLoop_path_peel hcard A m _ p (by omega)
    have hzero : ∀ z : V2 A 1, (0 : Module.End Dq.carrier (V2 A 1)) z = 0 := fun _ => rfl
    rw [hq, hm]
    exact hzero _
  · cases p with
    | nil => simp [Quiver.Path.length] at hp
    | cons q1 g_last =>
      rename_i c
      have hc : c = vtxC hcard 1 := cyc_edge_dichotomy hcard g_last hb
      subst hc
      have hp1 : 2 * m ≤ q1.length := by
        simp only [Quiver.Path.length] at hp; omega
      obtain ⟨q, _, hq⟩ := cycLoop_path_peel hcard A m _ q1 hp1
      have hzero : ∀ z : V2 A 1, (0 : Module.End Dq.carrier (V2 A 1)) z = 0 := fun _ => rfl
      show RationalQuiver.pathCompose _ _ (q1.cons g_last) v = 0
      rw [RationalQuiver.pathCompose_cons, LinearMap.comp_apply]
      show RationalQuiver.arrowCompose (Q := (cyclicQ hcard).toRQuiver) (V2 A) (E_Cyc_edge A)
        g_last (cycPath hcard A q1 v) = 0
      rw [hq, hm, hzero]
      exact map_zero _

end CycNilpotent2

/-- **`RQ-5.07-C1`, the specification** — `𝔼_ℚ` is well defined at `ℓ = 0`: the cocycle condition,
the edge equivariance and nilpotency at every object, and functoriality of the (trivial) limits at
every morphism.  @census none (auxiliary; `E_CycFunctor`'s hypothesis) -/
theorem E_Cyc_spec : E_CycSpec hcard :=
  ⟨fun A => ⟨cyc_cocycleS A, cyc_equivS A, cyc_nilpotentS hcard A⟩, fun _ _ f => cyc_homSpec f⟩

end Functor


/-! ## The native `𝔼_E` on `HC ℓ E D` (stage T3) -/

section NativeHC

set_option linter.unusedSectionVars false

variable {D : ImagUnit E}

/-! ## `ℓ = 0`: the cyclic quiver -/

section CyclicZ

variable (D) in
/-- The vertices of `Γ_E`, `ℓ = 0`.  @census none (helper) -/
abbrev vtxZ (v : Fin 2) : (RationalQuiver.cyclicOfSign E D.L D.chiHom).V := v

variable (D) in
/-- The edges of `Γ_E`, `ℓ = 0`.  @census none (helper) -/
abbrev edgeZ (e : Fin 2) : (RationalQuiver.cyclicOfSign E D.L D.chiHom).E := e

/-- `σ • v` on `Γ_E`, `ℓ = 0`, as an index.  @census none (helper) -/
noncomputable def galVtxZ (σ : D.L ≃ₐ[E] D.L) (v : Fin 2) : Fin 2 :=
  if D.chi σ = 1 then v else RQuiver.twoLoopsSwapPerm v

theorem vtxZ_smul (σ : D.L ≃ₐ[E] D.L) (v : Fin 2) : σ • vtxZ D v = vtxZ D (galVtxZ σ v) := by
  show (RQuiver.Aut.toPermV _ ((RationalQuiver.cyclicOfSign E D.L D.chiHom).ρ σ)) v = _
  rw [show (RationalQuiver.cyclicOfSign E D.L D.chiHom).ρ σ
      = if D.chiHom σ = 1 then 1 else RQuiver.cyclicSignSwap from rfl, ImagUnit.chiHom_apply]
  unfold galVtxZ
  split_ifs
  · rfl
  · fin_cases v <;> rfl

theorem edgeZ_smul (σ : D.L ≃ₐ[E] D.L) (e : Fin 2) :
    (σ • edgeZ D e : Fin 2) = if D.chi σ = 1 then e else RQuiver.twoLoopsSwapPerm e := by
  show (RQuiver.Aut.toPermE _ ((RationalQuiver.cyclicOfSign E D.L D.chiHom).ρ σ)) e = _
  rw [show (RationalQuiver.cyclicOfSign E D.L D.chiHom).ρ σ
      = if D.chiHom σ = 1 then 1 else RQuiver.cyclicSignSwap from rfl, ImagUnit.chiHom_apply]
  split_ifs
  · rfl
  · fin_cases e <;> rfl

variable (A : HC 0 E D)

/-- The vertex spaces `M(−) = M_{-1}`, `M(+) = M_1`.  @census none (helper) -/
abbrev V2Z (v : Fin 2) : Type := ↥(A.weight.comp (cycIdx v))

/-- **Step C-1** (`eq:varphicyclic`): `φ_{v,σ} := σ` on `M_{∓1}` (for `σ = 1` the identity).
@census none (helper)
@clauses   RQ2-5.13-S-C1 -/
noncomputable def E_Cyc_φ (σ : D.L ≃ₐ[E] D.L) (m : A.carrier) : A.carrier := A.galAct σ m

theorem E_Cyc_φZ_mem (σ : D.L ≃ₐ[E] D.L) (v : Fin 2) (m : A.carrier)
    (hm : m ∈ A.weight.comp (cycIdx v)) :
    E_Cyc_φ A σ m ∈ A.weight.comp (cycIdx (galVtxZ σ v)) := by
  unfold galVtxZ E_Cyc_φ
  rcases D.chi_cases σ with hσ | hσ
  · rw [if_pos hσ, HC.galAct_of_chi_one _ hσ]; exact hm
  · rw [if_neg (by rw [hσ]; decide)]
    have := (A.compat_neg hσ).1 _ m hm
    fin_cases v <;> exact this

theorem twoLoopsSwapPerm_swap' (v : Fin 2) :
    RQuiver.twoLoopsSwapPerm (RQuiver.twoLoopsSwapPerm v) = v := by
  fin_cases v <;> rfl

theorem galVtxZ_galVtxZ (σ : D.L ≃ₐ[E] D.L) (v : Fin 2) : galVtxZ σ (galVtxZ σ v) = v := by
  unfold galVtxZ; split_ifs
  · rfl
  · exact twoLoopsSwapPerm_swap' v

/-- `φ_{v,σ} : M(v) ≃+ M(σ • v)`, `ℓ = 0`.  @census none (helper) -/
noncomputable def E_Cyc_φEquivZ (σ : D.L ≃ₐ[E] D.L) (v : Fin 2) :
    V2Z A v ≃+ V2Z A (σ • vtxZ D v) where
  toFun m := ⟨E_Cyc_φ A σ m, by rw [vtxZ_smul]; exact E_Cyc_φZ_mem A σ v m m.2⟩
  invFun m := ⟨E_Cyc_φ A σ m, by
    obtain ⟨m, hm⟩ := m
    rw [vtxZ_smul] at hm
    have := E_Cyc_φZ_mem A σ _ m hm
    rwa [galVtxZ_galVtxZ] at this⟩
  left_inv m := Subtype.ext (A.galAct_galAct σ m.1)
  right_inv m := Subtype.ext (A.galAct_galAct σ m.1)
  map_add' m m' := Subtype.ext (map_add (A.galAct σ) m.1 m'.1)

/-- The edge maps as endomorphisms of the carrier.  @census none (helper) -/
noncomputable def edgeOpZ (e : Fin 2) : Module.End D.L A.carrier := ![A.weight.X, A.weight.Y] e

theorem edgeZ_val : ∀ (e : Fin 2) (m : V2Z A (RQuiver.cyclic.source e)),
    ((Split.E_CycSplit_edge A.toF e m : V2Z A (RQuiver.cyclic.target e)) : A.carrier)
      = edgeOpZ A e (m : A.carrier)
  | 0, _ => rfl
  | 1, _ => rfl

theorem gelSigma_ext_valZ {v w : (RationalQuiver.cyclicOfSign E D.L D.chiHom).V} (hvw : v = w)
    (m : V2Z A v) (n : V2Z A w) (h : (m : A.carrier) = (n : A.carrier)) :
    (⟨v, m⟩ : (u : (RationalQuiver.cyclicOfSign E D.L D.chiHom).V) × V2Z A u) = ⟨w, n⟩ := by
  subst hvw
  exact congrArg _ (Subtype.ext h)

/-- **Step C-4**, cocycle: `c² = 1`.  @census none (helper) -/
theorem cyc_cocycle (σ τ : D.L ≃ₐ[E] D.L) (m : A.carrier) :
    E_Cyc_φ A σ (E_Cyc_φ A τ m) = E_Cyc_φ A (σ * τ) m := by
  unfold E_Cyc_φ
  rcases D.chi_cases σ with hσ | hσ
  · rw [HC.galAct_of_chi_one _ hσ, D.eq_one_of_chi_one hσ, one_mul]
  · rcases D.chi_cases τ with hτ | hτ
    · rw [HC.galAct_of_chi_one _ hτ, D.eq_one_of_chi_one hτ, mul_one]
    · obtain rfl := D.eq_of_chi_neg_one hτ hσ
      rw [D.mul_self, HC.galAct_of_chi_one _ D.chi_one, A.galAct_galAct]

/-- **Step C-4**, Koecher: `cX = Yc`, `cY = Xc`.  @census none (helper)
@clauses   RQ2-5.13-S-C4 -/
theorem cyc_equiv (σ : D.L ≃ₐ[E] D.L) (e : Fin 2) (m : A.carrier) :
    edgeOpZ A (σ • edgeZ D e) (E_Cyc_φ A σ m) = E_Cyc_φ A σ (edgeOpZ A e m) := by
  unfold E_Cyc_φ
  rw [edgeZ_smul]
  rcases D.chi_cases σ with hσ | hσ
  · rw [if_pos hσ, HC.galAct_of_chi_one _ hσ, HC.galAct_of_chi_one _ hσ]
  · rw [if_neg (by rw [hσ]; decide)]
    fin_cases e
    · exact ((A.compat_neg hσ).2.1 m).symm
    · exact ((A.compat_neg hσ).2.2.1 m).symm

/-- **`𝔼_E(M)`, `ℓ = 0`**.  @census none (helper) -/
noncomputable def E_Cyc_repZ : RationalQuiver.Rep (RationalQuiver.cyclicOfSign E D.L D.chiHom) :=
  RationalQuiver.Rep.ofFiniteDimensional (Γ := RationalQuiver.cyclicOfSign E D.L D.chiHom)
    (V2Z A)
    (fun σ v => E_Cyc_φEquivZ A σ v)
    (fun σ v a m => Subtype.ext (galActOf_smul _ σ a m.1))
    (fun σ τ v m => gelSigma_ext_valZ A (mul_smul σ τ (vtxZ D v)).symm _ _ (cyc_cocycle A σ τ m.1))
    (fun e => Split.E_CycSplit_edge A.toF e)
    (fun σ e m m' hmm' => by
      have hsrc := (RationalQuiver.cyclicOfSign E D.L D.chiHom).source_smul σ e
      have htgt := (RationalQuiver.cyclicOfSign E D.L D.chiHom).target_smul σ e
      have hm' : (m' : A.carrier) = E_Cyc_φ A σ m := by
        have h2 := (Sigma.mk.inj_iff.mp hmm').2
        exact (Subtype.heq_iff_coe_eq (fun x => by rw [hsrc])).mp h2
      refine gelSigma_ext_valZ A htgt _ _ ?_
      refine (edgeZ_val A (σ • edgeZ D e) m').trans ?_
      refine Eq.trans ?_ (congrArg (E_Cyc_φ A σ) (edgeZ_val A e m)).symm
      rw [hm']
      exact cyc_equiv A σ e m.1)

/-- **Step C-4**, nilpotence: the paths of the cyclic quiver alternate between `X` and `Y`, and
`XY`, `YX` are nilpotent on `M_{∓1}` (`Split.E_CycSplit_isNilpotent`; the representation has the
vertex spaces and edges of `𝔼_{L_E}(M_{L_E})`).  @census none (helper; Step C-4) -/
theorem cyc_nilpotent : (E_Cyc_repZ A).IsNilpotent := Split.E_CycSplit_isNilpotent A.toF

/-- `𝔼_E(M)`, `ℓ = 0`, in `Rep^nil(Γ_E)`: nilpotent (Step C-4).  @census none (helper) -/
noncomputable def E_Cyc_objZ : (RepNilTarget D 0).FullSubcategory :=
  ⟨⟨E_Cyc_repZ A, fun _ => A.admissible _⟩, cyc_nilpotent A⟩

end CyclicZ



/-- `𝔼_E(f)`, `ℓ = 0`.  @census none (helper) -/
noncomputable def E_Cyc_homZ {A B : HC 0 E D} (f : A ⟶ B) :
    RationalQuiver.Rep.Hom (E_Cyc_repZ A) (E_Cyc_repZ B) where
  ψ v := Split.E_CycSplit_map_ψ (HC.Hom.toF f) v
  edge e m := Split.E_CycSplit_map_edge (HC.Hom.toF f) e m
  rational σ v m := Subtype.ext ((f : HC.Hom A B).map_gal σ m.1)

/-- **`𝔼_E`, `ℓ = 0`**.  @census none (helper) -/
noncomputable def E_ECyc : HC 0 E D ⥤ (RepNilTarget D 0).FullSubcategory where
  obj A := E_Cyc_objZ A
  map f := ⟨E_Cyc_homZ f⟩
  map_id A := by
    apply ObjectProperty.hom_ext
    exact RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)

end NativeHC

end RationalQuivers.Gelfand.Cyclic
