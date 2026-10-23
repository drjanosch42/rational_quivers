import RationalQuivers.Gelfand.RationalStructure.Phi

/-!
# well-definedness of `𝔼_E` (§5.3, Steps O-13, O-14)

Engine: `𝔼_E(M)` as a representation in the engine presentation (`E_Q_rep`) and the clauses
`E_E_cocycle` (`φ₊φ₋ = 1`, `φ⋆φ⋆ = 1`), `E_E_limitDiagram`, `E_E_rationalStructure` (Koecher),
`E_E_wellDefined`.  Native: `𝔼_E(M)` as an object of `Rep^nil(Γ_E)` (`E_E_rep`, `E_E_obj`), its
well-definedness read from the engine's `ObjSpec` through the bridge at `σ = c`.

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Equivalence.lean (§Rep, §Clauses)` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.Equivalence.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

@census none (module)
-/

namespace RationalQuivers.Gelfand.Equivalence

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {Dq : SqrtNegOneExt E}
open scoped TensorProduct Classical

variable {ℓ : ℕ}

/-! ### `𝔼_ℚ(M)` as a representation of `Γ_ℚ` -/

section Rep

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)
variable (hℓ : 1 ≤ ℓ) (A : HCEObj ℓ E Dq)

/-- The action of `σ ∈ Gal(ℚ[√-1]/ℚ)` on the carrier at the vertex `v`: the identity for `σ = 1`,
`φ_{v,c}` otherwise.  @census none (helper) -/
noncomputable def galAct (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : Fin 3) (m : A.carrier) :
    A.carrier :=
  if σ = 1 then m else Gelfand.RationalStructure.phiC hℓ A v m

theorem galAct_one (v : Fin 3) (m : A.carrier) : galAct hℓ A 1 v m = m := by
  simp [galAct]

theorem galAct_of_ne {σ : Dq.carrier ≃ₐ[E] Dq.carrier} (hσ : σ ≠ 1) (v : Fin 3)
    (m : A.carrier) : galAct hℓ A σ v m = Gelfand.RationalStructure.phiC hℓ A v m := by
  simp [galAct, hσ]

/-- `σ • v` on `Γ_ℚ`, computed: `v` for `σ = 1`, the swap otherwise.  @census none (helper) -/
theorem gelfandQ_smul_eq (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : Fin 3) :
    σ • Gelfand.RationalStructure.vtxQ hcard v = Gelfand.RationalStructure.vtxQ hcard (if σ = 1 then v else RQuiver.gelfandVertexSwap v) := by
  by_cases hσ : σ = 1
  · subst hσ; simp [Gelfand.RationalStructure.vtxQ]
  · rw [if_neg hσ, Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ, Gelfand.RationalStructure.gelfandQ_smul_vertex]

theorem galAct_mem (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : Fin 3) (m : A.carrier)
    (hm : m ∈ A.setup.weight.comp (vtxIdx ℓ v)) :
    galAct hℓ A σ v m ∈ A.setup.weight.comp (vtxIdx ℓ (σ • Gelfand.RationalStructure.vtxQ hcard v)) := by
  rw [gelfandQ_smul_eq]
  by_cases hσ : σ = 1
  · subst hσ; rw [galAct_one, if_pos rfl]; exact hm
  · rw [galAct_of_ne hℓ A hσ, if_neg hσ]; exact Gelfand.RationalStructure.phiC_mem hℓ A v m

/-- `φ_{v,σ} : M(v) ≃+ M(σ • v)`, given the cocycle condition.  @census none (helper) -/
noncomputable def E_Q_φ (h : Gelfand.RationalStructure.ObjSpec hcard hℓ A) (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : Fin 3) :
    Split.V3 A.qi v ≃+ Split.V3 A.qi (σ • Gelfand.RationalStructure.vtxQ hcard v) where
  toFun m := ⟨galAct hℓ A σ v m, galAct_mem hcard hℓ A σ v m m.2⟩
  invFun m := ⟨galAct hℓ A σ (if σ = 1 then v else RQuiver.gelfandVertexSwap v) m, by
    obtain ⟨m, hm⟩ := m
    rw [gelfandQ_smul_eq] at hm
    by_cases hσ : σ = 1
    · subst hσ
      rw [galAct_one]
      simpa using hm
    · rw [galAct_of_ne hℓ A hσ, if_neg hσ]
      have := Gelfand.RationalStructure.phiC_mem hℓ A (RQuiver.gelfandVertexSwap v) m
      have hsw : RQuiver.gelfandVertexSwap (RQuiver.gelfandVertexSwap v) = v := by
        fin_cases v <;> rfl
      rwa [hsw] at this⟩
  left_inv m := by
    refine Subtype.ext ?_
    show galAct hℓ A σ _ (galAct hℓ A σ v m) = m
    by_cases hσ : σ = 1
    · subst hσ; rw [galAct_one, galAct_one]
    · rw [galAct_of_ne hℓ A hσ, galAct_of_ne hℓ A hσ, if_neg hσ]
      exact h.cocycle v m m.2
  right_inv m := by
    obtain ⟨m, hm⟩ := m
    refine Subtype.ext ?_
    show galAct hℓ A σ v (galAct hℓ A σ _ m) = m
    by_cases hσ : σ = 1
    · subst hσ; rw [galAct_one, galAct_one]
    · rw [galAct_of_ne hℓ A hσ, galAct_of_ne hℓ A hσ, if_neg hσ]
      rw [gelfandQ_smul_eq, if_neg hσ] at hm
      have hsw : RQuiver.gelfandVertexSwap (RQuiver.gelfandVertexSwap v) = v := by
        fin_cases v <;> rfl
      have := h.cocycle (RQuiver.gelfandVertexSwap v) m hm
      rwa [hsw] at this
  map_add' m m' := by
    refine Subtype.ext ?_
    show galAct hℓ A σ v (m + m') = galAct hℓ A σ v m + galAct hℓ A σ v m'
    by_cases hσ : σ = 1
    · subst hσ; simp [galAct_one]
    · simp only [galAct_of_ne hℓ A hσ, Gelfand.RationalStructure.phiC_add]

theorem E_Q_φ_val (h : Gelfand.RationalStructure.ObjSpec hcard hℓ A) (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : Fin 3)
    (m : Split.V3 A.qi v) : ((E_Q_φ hcard hℓ A h σ v m : Split.V3 A.qi _) : A.carrier) = galAct hℓ A σ v m :=
  rfl

/-- The `Fin 3`-indexed elements of the disjoint union `⊔_v M(v)`, compared through their carrier
values: two elements at propositionally equal vertices are equal iff their underlying vectors are.
@census none (helper) -/
theorem sigma_ext_val {v w : (Gelfand.RationalStructure.gelfandQ hcard).V} (hvw : v = w) (m : Split.V3 A.qi v) (n : Split.V3 A.qi w)
    (h : (m : A.carrier) = (n : A.carrier)) :
    (⟨v, m⟩ : (u : (Gelfand.RationalStructure.gelfandQ hcard).V) × Split.V3 A.qi u) = ⟨w, n⟩ := by
  subst hvw
  exact congrArg _ (Subtype.ext h)

/-- **`𝔼_ℚ(M)` as a rational representation of `Γ_ℚ`** — the object `(𝔼_{ℚ[√-1]}(M), φ_•)` of
`thm:EEQQequivalence`, given the propositions of `ObjSpec` (`C1`, `C2`, `C4`, `RQ-5.01-C7`/`C8`):
the vertex family `V3` of `𝔼_{ℚ[√-1]}(M)`, its four edge maps, and the semi-linear structure
`φ_{v,c} = c ∘ φ^{(∞)}_v`.

@census    none (auxiliary; the object map of `𝔼_ℚ`, clause `RQ-5.05-C1`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C1
@imports   none
@divergence none -/
noncomputable def E_Q_rep (h : Gelfand.RationalStructure.ObjSpec hcard hℓ A) : RationalQuiver.Rep (Gelfand.RationalStructure.gelfandQ hcard) :=
  RationalQuiver.Rep.ofFiniteDimensional (Γ := Gelfand.RationalStructure.gelfandQ hcard) (Split.V3 A.qi)
    (fun σ v => E_Q_φ hcard hℓ A h σ v)
    (fun σ v a m => by
      refine Subtype.ext ?_
      show galAct hℓ A σ v (a • m) = σ a • galAct hℓ A σ v m
      by_cases hσ : σ = 1
      · subst hσ; simp [galAct_one]
      · rw [galAct_of_ne hℓ A hσ, galAct_of_ne hℓ A hσ, Gelfand.RationalStructure.phiC_smul,
          Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ])
    (fun σ τ v m => by
      refine sigma_ext_val hcard A (mul_smul σ τ (Gelfand.RationalStructure.vtxQ hcard v)).symm _ _ ?_
      show galAct hℓ A σ _ (galAct hℓ A τ v m) = galAct hℓ A (σ * τ) v m
      by_cases hσ : σ = 1
      · subst hσ; rw [galAct_one, one_mul]
      · by_cases hτ : τ = 1
        · subst hτ; rw [galAct_one, mul_one]; simp [galAct]
        · have hστ : σ * τ = 1 := by
            rw [Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ, Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hτ, Gelfand.RationalStructure.galConj_mul_self]
          rw [hστ, galAct_one, galAct_of_ne hℓ A hσ, galAct_of_ne hℓ A hτ]
          have hm := m.2
          have hv : τ • Gelfand.RationalStructure.vtxQ hcard v = Gelfand.RationalStructure.vtxQ hcard (RQuiver.gelfandVertexSwap v) := by
            rw [gelfandQ_smul_eq, if_neg hτ]
          show Gelfand.RationalStructure.phiC hℓ A (τ • Gelfand.RationalStructure.vtxQ hcard v) (Gelfand.RationalStructure.phiC hℓ A v m) = m
          rw [hv]
          exact h.cocycle v m hm)
    (fun e => Split.E_F_edge A.qi (A.qi.starInverses hℓ) hℓ e)
    (fun σ e m m' hmm' => by
      have hsrc := (Gelfand.RationalStructure.gelfandQ hcard).source_smul σ e
      have htgt := (Gelfand.RationalStructure.gelfandQ hcard).target_smul σ e
      have hm' : (m' : A.carrier) = galAct hℓ A σ (RQuiver.gelfand.source e) m := by
        have h2 := (Sigma.mk.inj_iff.mp hmm').2
        exact (Subtype.heq_iff_coe_eq (fun x => by rw [hsrc])).mp h2
      refine sigma_ext_val hcard A htgt _ _ ?_
      refine (Gelfand.RationalStructure.E_Qi_edge_val hℓ A (σ • e) m').trans ?_
      refine Eq.trans ?_ (congrArg (galAct hℓ A σ _) (Gelfand.RationalStructure.E_Qi_edge_val hℓ A e m)).symm
      rw [hm']
      by_cases hσ : σ = 1
      · subst hσ
        rw [galAct_one, galAct_one, one_smul]
      · rw [galAct_of_ne hℓ A hσ, galAct_of_ne hℓ A hσ, Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ,
          Gelfand.RationalStructure.gelfandQ_smul_edge hcard e]
        exact h.equiv e m m.2)

@[simp] theorem E_Q_rep_M (h : Gelfand.RationalStructure.ObjSpec hcard hℓ A) : (E_Q_rep hcard hℓ A h).M = Split.V3 A.qi := rfl

theorem E_Q_rep_φEdge (h : Gelfand.RationalStructure.ObjSpec hcard hℓ A) (e : Fin 4) :
    (E_Q_rep hcard hℓ A h).φEdge e = Split.E_F_edge A.qi (A.qi.starInverses hℓ) hℓ e := rfl

theorem E_Q_rep_φ (h : Gelfand.RationalStructure.ObjSpec hcard hℓ A) (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : Fin 3) :
    (E_Q_rep hcard hℓ A h).φ σ v = E_Q_φ hcard hℓ A h σ v := rfl

/-- `𝔼_ℚ(M)` is finite-dimensional (admissibility).  @census none (helper) -/
noncomputable def E_Q_fdrep (h : Gelfand.RationalStructure.ObjSpec hcard hℓ A) : RationalQuiver.FDRep (Gelfand.RationalStructure.gelfandQ hcard) where
  toRep := E_Q_rep hcard hℓ A h
  finiteDimensional v := A.admissible _

/-- `𝔼_ℚ(M)` is an object of `Rep^nil(Γ_ℚ)`: nilpotent, with the relation.  @census none (helper) -/
noncomputable def E_Q_obj (h : Gelfand.RationalStructure.ObjSpec hcard hℓ A) : Gelfand.RationalStructure.RepNilQ hcard :=
  ⟨E_Q_fdrep hcard hℓ A h, h.nilpotent, h.relation⟩

end Rep

/-! ### `C2`–`C5`: the rational structure and functoriality -/

section Clauses

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)
variable (hℓ : 1 ≤ ℓ) (A : HCEObj ℓ E Dq)

/-- **`RQ-5.05-C2`** — the cocycle condition `eq:semi-linearactiononrep`:
`φ₊φ₋ = 𝟏_{M(−)}`, `φ₋φ₊ = 𝟏_{M(+)}`, `φ_⋆φ_⋆ = 𝟏_{M(⋆)}`, where `φ_• = c ∘ φ^{(∞)}_•` are the
**defined** limits (repair `V-S8-3`: the former statement ranged over unpinned sequences and was
refuted in-tree).  The source derives it from `eq:conjugateinversepm` and `eq:conjugateinversestar`
(`RQ-5.04-C9`, `C10`) together with `c² = 𝟏`.

@census    none (auxiliary; discharges census clause `RQ-5.05-C2`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C2
@imports   none
@divergence none -/
theorem E_E_cocycle :
    ∀ (v : Fin 3) (m : A.carrier), m ∈ A.setup.weight.comp (vtxIdx ℓ v) →
      Gelfand.RationalStructure.phiC hℓ A (RQuiver.gelfandVertexSwap v) (Gelfand.RationalStructure.phiC hℓ A v m) = m := by
  -- `eq:conjugateinversepm` (`RQ-5.04-C9`) at the two `±` vertices, `eq:conjugateinversestar`
  -- (`RQ-5.04-C10`) at `⋆`: the cocycle condition IS those identities, since `φ_{v,c} = c φ^{(∞)}_v`
  -- and `c(±) = ∓`, `c(⋆) = ⋆`.
  obtain ⟨-, -, hC9, hC10, -⟩ := Gelfand.RationalStructure.varphi_spec A.setup hℓ
  intro v
  fin_cases v
  · exact fun m hm => hC9.2 m hm
  · exact fun m hm => hC10.1 m hm
  · exact fun m hm => hC9.1 m hm

/-- **`RQ-5.05-C3`** — `eq:limitdiagram` commutes: `eq:normalizedcomparison` with the three
verticals replaced by the limits `φ^{(∞)}_-`, `φ^{(∞)}_⋆`, `φ^{(∞)}_+`.  The source proves it "by
induction, as in the case of the first iteration `eq:firstiteration`".

@census    none (auxiliary; discharges census clause `RQ-5.05-C3`)
@source    eq:limitdiagram
(clauses of the frozen original:)   RQ-5.05-C3
@imports   none
@divergence none
@clauses   RQ2-5.12-S-O14 -/
theorem E_E_limitDiagram :
    (∀ v ∈ A.setup.weight.comp (-((ℓ : ℤ) + 1)),
        (Gelfand.RationalStructure.inputStar A.setup hℓ).limPlus (A.setup.weight.X v)
          = (A.qi.starInverses hℓ).yStarInv (A.setup.weight.X ((Gelfand.RationalStructure.inputMinus A.setup).limPlus v))) ∧
    (∀ v ∈ A.setup.weight.comp (-((ℓ : ℤ) - 1)),
        (Gelfand.RationalStructure.inputPlus A.setup).limPlus (A.setup.weight.X (Split.xStar A.qi v))
          = A.setup.weight.X ((Gelfand.RationalStructure.inputStar A.setup hℓ).limPlus v)) ∧
    (∀ v ∈ A.setup.weight.comp (-((ℓ : ℤ) - 1)),
        (Gelfand.RationalStructure.inputMinus A.setup).limPlus (A.setup.weight.Y v)
          = A.setup.weight.Y (Split.yStar A.qi ((Gelfand.RationalStructure.inputStar A.setup hℓ).limPlus v))) ∧
    (∀ v ∈ A.setup.weight.comp ((ℓ : ℤ) + 1),
        (Gelfand.RationalStructure.inputStar A.setup hℓ).limPlus ((A.qi.starInverses hℓ).xStarInv (A.setup.weight.Y v))
          = A.setup.weight.Y ((Gelfand.RationalStructure.inputPlus A.setup).limPlus v)) :=
  -- `limit_diagram` (`Gelfand/RationalStructure/Stabilization.lean`; v1's
  -- `Gelfand/Stabilization.lean`, deleted at WP-13; 2026-10-21 note, O-V2-6 round 2): the
  -- induction the source asks for, run on
  -- `DiagSq` (the four squares for an arbitrary triple of verticals) and evaluated past both
  -- nilpotency exponents.  The type ascription is what carries `A.setup.toQiSetup` to `A.qi`
  -- (`CONVENTIONS.md` §3, the defeq-but-not-`rw`-able projection chain).
  Gelfand.RationalStructure.limit_diagram A.setup (A.qi.starInverses hℓ) hℓ

/-- **`RQ-5.05-C4`** — `φ_•` satisfies `eq:koecheractiononrep` and therefore defines a
`ℚ`-rational structure on `𝔼_{ℚ[√-1]}(M)` in the sense of `def:rationalrepresentations`: for each
of the **four** edges `e`, `φ_{c·e} ∘ φ_{s(e),c} = φ_{t(e),c} ∘ φ_e` (repair `V-S8-3`: all four
equivariances, about the defined `φ_•`).  With `C2` this is exactly `ObjSpec`'s content, i.e. `C1`.

@census    none (auxiliary; discharges census clause `RQ-5.05-C4`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C4
@imports   none
@divergence none -/
theorem E_E_rationalStructure :
    ∀ (e : Fin 4) (m : A.carrier), m ∈ A.setup.weight.comp (vtxIdx ℓ (RQuiver.gelfand.source e)) →
      Gelfand.RationalStructure.edgeOp hℓ A (RQuiver.gelfandEdgeSwap e) (Gelfand.RationalStructure.phiC hℓ A (RQuiver.gelfand.source e) m)
        = Gelfand.RationalStructure.phiC hℓ A (RQuiver.gelfand.target e) (Gelfand.RationalStructure.edgeOp hℓ A e m) := by
  -- `eq:koecheractiononrep` is `eq:limitdiagram` (`C3`) read through `c`: each of the four
  -- equivariances is one square of the limit diagram composed with `cX = Yc`, `cY = Xc`,
  -- `cY⋆ = X⋆c`, `cY⋆⁻¹ = X⋆⁻¹c`.  `a₋ ← ` square 1, `b₋ ← ` square 3, `a₊ ← ` square 4,
  -- `b₊ ← ` square 2.
  obtain ⟨h1, h2, h3, h4⟩ := E_E_limitDiagram hℓ A
  have hcy : ∀ w, A.setup.conj (Split.yStar A.qi w) = Split.xStar A.qi (A.setup.conj w) :=
    Gelfand.RationalStructure.conj_yStar A.setup hℓ
  have hcyi : ∀ w ∈ A.setup.weight.comp (-((ℓ : ℤ) - 1)),
      A.setup.conj ((A.qi.starInverses hℓ).yStarInv w)
        = (A.qi.starInverses hℓ).xStarInv (A.setup.conj w) :=
    fun w hw => Gelfand.RationalStructure.conj_yStarInv A.setup (A.qi.starInverses hℓ) hℓ hw
  intro e
  fin_cases e
  · -- `a₋`: `X⋆⁻¹ Y φ_{-,c} = φ_{⋆,c} X` on `M_{-(ℓ+1)}`
    intro m hm
    have hM : (Gelfand.RationalStructure.inputMinus A.setup).limPlus m ∈ A.setup.weight.comp (-((ℓ : ℤ) + 1)) :=
      (Gelfand.RationalStructure.inputMinus A.setup).limPlus_mem m
    have hXM : A.setup.weight.X ((Gelfand.RationalStructure.inputMinus A.setup).limPlus m)
        ∈ A.setup.weight.comp (-((ℓ : ℤ) - 1)) :=
      Split.x_mem (Q := A.setup.toQiSetup) (m := -((ℓ : ℤ) + 1)) (by ring) hM
    show (A.qi.starInverses hℓ).xStarInv
        (A.setup.weight.Y (A.setup.conj ((Gelfand.RationalStructure.inputMinus A.setup).limPlus m)))
      = A.setup.conj ((Gelfand.RationalStructure.inputStar A.setup hℓ).limPlus (A.setup.weight.X m))
    rw [h1 m hm, hcyi _ hXM, A.setup.conj_X]
  · -- `b₋`: `X X⋆ φ_{⋆,c} = φ_{-,c} Y` on `M_{-(ℓ-1)}`
    intro m hm
    show A.setup.weight.X (Split.xStar A.qi (A.setup.conj ((Gelfand.RationalStructure.inputStar A.setup hℓ).limPlus m)))
      = A.setup.conj ((Gelfand.RationalStructure.inputMinus A.setup).limPlus (A.setup.weight.Y m))
    rw [h3 m hm, A.setup.conj_Y, hcy]
  · -- `a₊`: `X φ_{+,c} = φ_{⋆,c} X⋆⁻¹ Y` on `M_{ℓ+1}`
    intro m hm
    show A.setup.weight.X (A.setup.conj ((Gelfand.RationalStructure.inputPlus A.setup).limPlus m))
      = A.setup.conj ((Gelfand.RationalStructure.inputStar A.setup hℓ).limPlus
          ((A.qi.starInverses hℓ).xStarInv (A.setup.weight.Y m)))
    rw [h4 m hm, A.setup.conj_Y]
  · -- `b₊`: `Y φ_{⋆,c} = φ_{+,c} X X⋆` on `M_{-(ℓ-1)}`
    intro m hm
    show A.setup.weight.Y (A.setup.conj ((Gelfand.RationalStructure.inputStar A.setup hℓ).limPlus m))
      = A.setup.conj ((Gelfand.RationalStructure.inputPlus A.setup).limPlus (A.setup.weight.X (Split.xStar A.qi m)))
    rw [h2 m hm, A.setup.conj_X]

/-- **`RQ-5.05-C1`** — `𝔼_ℚ` is **well defined**: every object of `HC_λ(𝔤,K)_ℚ` satisfies the
specification that makes `(𝔼_{ℚ[√-1]}(M), φ_•)` an object of `Rep^nil(Γ_ℚ)` — the cocycle
condition (`C2`), the equivariance (`C4`), nilpotency and the relation (`RQ-5.01-C7`, `C8`).

@census    none (auxiliary; discharges census clause `RQ-5.05-C1`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C1
@imports   none
@divergence none -/
theorem E_E_wellDefined : Gelfand.RationalStructure.ObjSpec hcard hℓ A :=
  -- `C2` and `C4`; nilpotency and the relation are `RQ-5.01`'s, transported by type ascription
  -- (`(gelfandQ hcard).toRQuiver` and `(gelfandSplit ℚ[√-1]).toRQuiver` are both `RQuiver.gelfand`).
  ⟨E_E_cocycle hℓ A, E_E_rationalStructure hℓ A,
    Split.E_F_isNilpotent A.qi (A.qi.starInverses hℓ) hℓ,
    Split.E_F_rep_relation A.qi (A.qi.starInverses hℓ) hℓ⟩


end Clauses


/-! ## The native `𝔼_E` on `HC ℓ E D` (stage T3) -/

section NativeHC

set_option linter.unusedSectionVars false

variable {D : ImagUnit E}

/-! ### The target: `σ • v` on `Γ_E` -/

variable (D) in
/-- The vertices of `Γ_E` (`ℓ ≥ 1`) by index.  @census none (helper) -/
abbrev vtxE (v : Fin 3) : (RationalQuiver.gelfandOfSign E D.L D.chiHom).V := v

variable (D) in
/-- The edges of `Γ_E` (`ℓ ≥ 1`) by index.  @census none (helper) -/
abbrev edgeE (e : Fin 4) : (RationalQuiver.gelfandOfSign E D.L D.chiHom).E := e

theorem gammaE_smul_vertex (σ : D.L ≃ₐ[E] D.L) (v : Fin 3) :
    (σ • vtxE D v : Fin 3)
      = if D.chi σ = 1 then v else RQuiver.gelfandVertexSwap v := by
  show (RQuiver.Aut.toPermV _ ((RationalQuiver.gelfandOfSign E D.L D.chiHom).ρ σ)) v = _
  rw [show (RationalQuiver.gelfandOfSign E D.L D.chiHom).ρ σ
      = if D.chiHom σ = 1 then 1 else RQuiver.gelfandSwap from rfl, ImagUnit.chiHom_apply]
  split_ifs <;> rfl

theorem gammaE_smul_edge (σ : D.L ≃ₐ[E] D.L) (e : Fin 4) :
    (σ • edgeE D e : Fin 4)
      = if D.chi σ = 1 then e else RQuiver.gelfandEdgeSwap e := by
  show (RQuiver.Aut.toPermE _ ((RationalQuiver.gelfandOfSign E D.L D.chiHom).ρ σ)) e = _
  rw [show (RationalQuiver.gelfandOfSign E D.L D.chiHom).ρ σ
      = if D.chiHom σ = 1 then 1 else RQuiver.gelfandSwap from rfl, ImagUnit.chiHom_apply]
  split_ifs <;> rfl


/-! ### `𝔼_E(M)` for `ℓ ≥ 1`: the object -/

/-- `M_{L_E}` as an object of `HC_λ(𝔤,K)_{L_E}` (forgetting the descent datum).  @census none (helper) -/
@[reducible] noncomputable def _root_.RationalQuivers.HC.HC.toF (A : HC ℓ E D) : Split.HCFObj D.L ℓ where
  carrier := A.carrier
  weight := A.weight
  gic := A.gic
  admissible := A.admissible
  centralCharacter := A.centralCharacter
  fg := A.fg

/-- A morphism of `HC ℓ E D` as a morphism over `L_E`.  @census none (helper) -/
noncomputable def _root_.RationalQuivers.HC.HC.Hom.toF {A B : HC ℓ E D} (f : A ⟶ B) : A.toF ⟶ B.toF :=
  ⟨(f : HC.Hom A B).toLinearMap, (f : HC.Hom A B).map_H, (f : HC.Hom A B).map_X,
    (f : HC.Hom A B).map_Y, (f : HC.Hom A B).map_comp⟩

variable (D) in
/-- `Rep^nil(Γ_E)`, `ℓ ≥ 1`: nilpotent, with the relation.  `RepNilTarget D (k + 1)` unfolds to it.
@census none (helper) -/
def RepNilGel : ObjectProperty (RationalQuiver.FDRep (RationalQuiver.gelfandOfSign E D.L D.chiHom)) :=
  fun M => M.toRep.IsNilpotent ∧ SatisfiesGelfandRelationE D M.toRep

theorem repNilTarget_succ (k : ℕ) : RepNilTarget D (k + 1) = RepNilGel D := rfl

section Rep

variable (hℓ : 1 ≤ ℓ) (A : HC ℓ E D)

/-- `σ • v` on `Γ_E`, as a vertex index.  @census none (helper) -/
noncomputable def galVtx (σ : D.L ≃ₐ[E] D.L) (v : Fin 3) : Fin 3 :=
  if D.chi σ = 1 then v else RQuiver.gelfandVertexSwap v

theorem gelfandVertexSwap_swap (v : Fin 3) :
    RQuiver.gelfandVertexSwap (RQuiver.gelfandVertexSwap v) = v := by
  fin_cases v <;> rfl

/-- The bridged object at `c` satisfies the engine's `ObjSpec` (Step O-14).  @census none (helper) -/
theorem objSpec (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) :
    Gelfand.RationalStructure.ObjSpec (D.sqrtExt h).card_gal hℓ (A.toHCEObj h) :=
  E_E_wellDefined _ hℓ _

theorem E_E_φ_mem (σ : D.L ≃ₐ[E] D.L) (v : Fin 3) (m : A.carrier)
    (hm : m ∈ A.weight.comp (vtxIdx ℓ v)) :
    Gelfand.RationalStructure.E_E_φ hℓ A σ v m ∈ A.weight.comp (vtxIdx ℓ (galVtx σ v)) := by
  unfold galVtx
  rcases D.chi_cases σ with hσ | hσ
  · rw [if_pos hσ, Gelfand.RationalStructure.E_E_φ_of_one hℓ A hσ]; exact hm
  · rw [if_neg (by rw [hσ]; decide), Gelfand.RationalStructure.E_E_φ_eq_phiC hℓ A hσ]
    exact Gelfand.RationalStructure.phiC_mem hℓ (A.toHCEObj ⟨σ, hσ⟩) v m

/-- The cocycle condition on values (Step O-14, `eq:semi-linearactiononrep`).  @census none (helper) -/
theorem E_E_φ_cocycle (σ : D.L ≃ₐ[E] D.L) (v : Fin 3) (m : A.carrier)
    (hm : m ∈ A.weight.comp (vtxIdx ℓ v)) :
    Gelfand.RationalStructure.E_E_φ hℓ A σ (galVtx σ v) (Gelfand.RationalStructure.E_E_φ hℓ A σ v m) = m := by
  unfold galVtx
  rcases D.chi_cases σ with hσ | hσ
  · rw [if_pos hσ, Gelfand.RationalStructure.E_E_φ_of_one hℓ A hσ, Gelfand.RationalStructure.E_E_φ_of_one hℓ A hσ]
  · rw [if_neg (by rw [hσ]; decide), Gelfand.RationalStructure.E_E_φ_eq_phiC hℓ A hσ, Gelfand.RationalStructure.E_E_φ_eq_phiC hℓ A hσ]
    exact (objSpec hℓ A ⟨σ, hσ⟩).cocycle v m hm

theorem vtxE_smul (σ : D.L ≃ₐ[E] D.L) (v : Fin 3) : σ • vtxE D v = vtxE D (galVtx σ v) :=
  gammaE_smul_vertex σ v

/-- `φ_{v,σ} : M(v) ≃+ M(σ • v)`.  @census none (helper) -/
noncomputable def E_E_φEquiv (σ : D.L ≃ₐ[E] D.L) (v : Fin 3) :
    Split.V3 A.qi v ≃+ Split.V3 A.qi (σ • vtxE D v) where
  toFun m := ⟨Gelfand.RationalStructure.E_E_φ hℓ A σ v m, by rw [vtxE_smul]; exact E_E_φ_mem hℓ A σ v m m.2⟩
  invFun m := ⟨Gelfand.RationalStructure.E_E_φ hℓ A σ (galVtx σ v) m, by
    obtain ⟨m, hm⟩ := m
    rw [vtxE_smul] at hm
    have := E_E_φ_mem hℓ A σ _ m hm
    unfold galVtx at this ⊢
    split_ifs at this ⊢ with hσ
    · exact this
    · rwa [gelfandVertexSwap_swap] at this⟩
  left_inv m := Subtype.ext (E_E_φ_cocycle hℓ A σ v m m.2)
  right_inv m := by
    obtain ⟨m, hm⟩ := m
    refine Subtype.ext ?_
    rw [vtxE_smul] at hm
    show Gelfand.RationalStructure.E_E_φ hℓ A σ v (Gelfand.RationalStructure.E_E_φ hℓ A σ (galVtx σ v) m) = m
    have := E_E_φ_cocycle hℓ A σ (galVtx σ v) m hm
    have hv : galVtx σ (galVtx σ v) = v := by
      unfold galVtx; split_ifs
      · rfl
      · exact gelfandVertexSwap_swap v
    rwa [hv] at this
  map_add' m m' := by
    refine Subtype.ext ?_
    show Gelfand.RationalStructure.E_E_φ hℓ A σ v (m + m') = Gelfand.RationalStructure.E_E_φ hℓ A σ v m + Gelfand.RationalStructure.E_E_φ hℓ A σ v m'
    rcases D.chi_cases σ with hσ | hσ
    · simp only [Gelfand.RationalStructure.E_E_φ_of_one hℓ A hσ]
    · simp only [Gelfand.RationalStructure.E_E_φ_of_neg hℓ A hσ, map_add]

theorem gelSigma_ext_val {v w : (RationalQuiver.gelfandOfSign E D.L D.chiHom).V} (hvw : v = w)
    (m : Split.V3 A.qi v) (n : Split.V3 A.qi w) (h : (m : A.carrier) = (n : A.carrier)) :
    (⟨v, m⟩ : (u : (RationalQuiver.gelfandOfSign E D.L D.chiHom).V) × Split.V3 A.qi u) = ⟨w, n⟩ := by
  subst hvw
  exact congrArg _ (Subtype.ext h)

/-- The four edge maps of `𝔼_{L_E}(M_{L_E})` as endomorphisms of the carrier.  @census none (helper) -/
noncomputable def edgeOpE (e : Fin 4) : Module.End D.L A.carrier :=
  ![A.weight.X, A.weight.Y, (A.qi.starInverses hℓ).xStarInv ∘ₗ A.weight.Y,
    A.weight.X ∘ₗ Split.xStar A.qi] e

theorem edgeE_val : ∀ (e : Fin 4) (m : Split.V3 A.qi (RQuiver.gelfand.source e)),
    ((Split.E_F_edge A.qi (A.qi.starInverses hℓ) hℓ e m : Split.V3 A.qi (RQuiver.gelfand.target e))
      : A.carrier) = edgeOpE hℓ A e (m : A.carrier)
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- **`𝔼_E(M)`, `ℓ ≥ 1`**: `𝔼_{L_E}(M_{L_E})` with `φ_{•,σ}`.  @census none (helper) -/
noncomputable def E_E_rep : RationalQuiver.Rep (RationalQuiver.gelfandOfSign E D.L D.chiHom) :=
  RationalQuiver.Rep.ofFiniteDimensional (Γ := RationalQuiver.gelfandOfSign E D.L D.chiHom)
    (Split.V3 A.qi)
    (fun σ v => E_E_φEquiv hℓ A σ v)
    (fun σ v a m => by
      refine Subtype.ext ?_
      show Gelfand.RationalStructure.E_E_φ hℓ A σ v (a • m) = σ a • Gelfand.RationalStructure.E_E_φ hℓ A σ v m
      rcases D.chi_cases σ with hσ | hσ
      · rw [Gelfand.RationalStructure.E_E_φ_of_one hℓ A hσ, Gelfand.RationalStructure.E_E_φ_of_one hℓ A hσ, D.eq_one_of_chi_one hσ]; rfl
      · rw [Gelfand.RationalStructure.E_E_φ_of_neg hℓ A hσ, Gelfand.RationalStructure.E_E_φ_of_neg hℓ A hσ, map_smul, galActOf_smul])
    (fun σ τ v m => by
      refine gelSigma_ext_val A (mul_smul σ τ (vtxE D v)).symm _ _ ?_
      show Gelfand.RationalStructure.E_E_φ hℓ A σ _ (Gelfand.RationalStructure.E_E_φ hℓ A τ v m) = Gelfand.RationalStructure.E_E_φ hℓ A (σ * τ) v m
      rcases D.chi_cases σ with hσ | hσ
      · rw [Gelfand.RationalStructure.E_E_φ_of_one hℓ A hσ, D.eq_one_of_chi_one hσ, one_mul]
      · rcases D.chi_cases τ with hτ | hτ
        · rw [Gelfand.RationalStructure.E_E_φ_of_one hℓ A hτ, D.eq_one_of_chi_one hτ, mul_one, one_smul]
        · obtain rfl := D.eq_of_chi_neg_one hτ hσ
          rw [D.mul_self, Gelfand.RationalStructure.E_E_φ_of_one hℓ A D.chi_one, vtxE_smul]
          exact E_E_φ_cocycle hℓ A τ v m m.2)
    (fun e => Split.E_F_edge A.qi (A.qi.starInverses hℓ) hℓ e)
    (fun σ e m m' hmm' => by
      have hsrc := (RationalQuiver.gelfandOfSign E D.L D.chiHom).source_smul σ e
      have htgt := (RationalQuiver.gelfandOfSign E D.L D.chiHom).target_smul σ e
      have hm' : (m' : A.carrier) = Gelfand.RationalStructure.E_E_φ hℓ A σ (RQuiver.gelfand.source e) m := by
        have h2 := (Sigma.mk.inj_iff.mp hmm').2
        exact (Subtype.heq_iff_coe_eq (fun x => by rw [hsrc])).mp h2
      refine gelSigma_ext_val A htgt _ _ ?_
      refine (edgeE_val hℓ A (σ • edgeE D e) m').trans ?_
      refine Eq.trans ?_ (congrArg (Gelfand.RationalStructure.E_E_φ hℓ A σ _) (edgeE_val hℓ A e m)).symm
      rw [hm']
      rcases D.chi_cases σ with hσ | hσ
      · rw [Gelfand.RationalStructure.E_E_φ_of_one hℓ A hσ, Gelfand.RationalStructure.E_E_φ_of_one hℓ A hσ, D.eq_one_of_chi_one hσ, one_smul]
      · rw [Gelfand.RationalStructure.E_E_φ_eq_phiC hℓ A hσ, Gelfand.RationalStructure.E_E_φ_eq_phiC hℓ A hσ, gammaE_smul_edge,
          if_neg (by rw [hσ]; decide)]
        exact (objSpec hℓ A ⟨σ, hσ⟩).equiv e (m : A.carrier) m.2)

/-- `𝔼_E(M)` is finite-dimensional.  @census none (helper) -/
noncomputable def E_E_fdrep : RationalQuiver.FDRep (RationalQuiver.gelfandOfSign E D.L D.chiHom) where
  toRep := E_E_rep hℓ A
  finiteDimensional _ := A.admissible _

/-- `𝔼_E(M)` in `Rep^nil(Γ_E)`: nilpotent (`RQ2-5.01-C8`) and with the relation (`C7`).
@census none (helper) -/
noncomputable def E_E_obj : (RepNilGel D).FullSubcategory :=
  ⟨E_E_fdrep hℓ A, Split.E_F_isNilpotent A.qi (A.qi.starInverses hℓ) hℓ,
    Split.E_F_rep_relation A.qi (A.qi.starInverses hℓ) hℓ⟩


end Rep

end NativeHC

end RationalQuivers.Gelfand.Equivalence
