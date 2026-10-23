import RationalQuivers.Gelfand.RationalStructure.Stabilization
import RationalQuivers.Gelfand.Target
import RationalQuivers.Quiver.Rep.Category
import RationalQuivers.Species.Rep.Gelfand

/-!
# `eq:varphiplus`, `eq:varphiminus`, `eq:varphistar` (§5.2, Steps O-9, O-12)

The data of `𝔼_E(M)`: the target `Γ` in the engine's presentation (`gelfandQ`, `RepNilQ`, `toSplitW`),
the limits `φ^{(∞)}_v` (`limAt`), `φ_{v,c} = c ∘ φ^{(∞)}_v` (`phiC`) and the specification `ObjSpec`.
On `HC ℓ E D` (native): the three situations of Step O-9 (`stabInput`), `φ^{(∞)}` (`limAtHC`) and
**Step O-12**, `φ_{v,σ}` by dispatch on `χ_E(σ)` (`E_E_φ`: `1` if `χ σ = 1`, `σ ∘ φ^{(∞)}_v` if
`χ σ = -1`).

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Equivalence.lean (§Target, §Data)` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.RationalStructure.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

*(2026-10-21, O-V2-6 round 2.)*  Two carried docstrings below point to S8's
`Gelfand/Construction.lean` (deleted at WP-13, `ae9eda9`) and to S8's `E_Qi_rep`.  The split
Gelfand quiver with its relation, and the representation `E_F_rep`, are in
`Gelfand/Split/Construction.lean` (stage T2).

@census none (module)
-/

namespace RationalQuivers.Gelfand.RationalStructure

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {Dq : SqrtNegOneExt E}
open scoped TensorProduct Classical

variable {ℓ : ℕ}


/-! ### `Γ_ℚ` and `Rep^nil(Γ_ℚ)` -/

section Target

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)

/-- `Γ_E`, the **`E`-rational** Gelfand quiver of `ex:gelfand` over `E`: `RQuiver.gelfand` with the
non-trivial `Gal(D.carrier/E)`-involution (S8's `Γ_ℚ` at `E = ℚ`).  The general-`E` analogue of
`RQ-5.05`'s and `RQ-5.06`'s target, as distinct from `Gelfand.gelfandSplit`, the split target over
`D.carrier`.  *(Corrected 2026-10-02, docstring-only, `V1-09`: the copied text named `Γ_ℚ`.)*

@census none (auxiliary; the target quiver of `RQ-5.05-C26`) -/
noncomputable def gelfandQ : RationalQuiver E Dq.carrier :=
  RationalQuiver.gelfandOfCardTwo E Dq.carrier hcard

/-- The vertices of `Γ_ℚ` by index: `−`(=0), `⋆`(=1), `+`(=2).  @census none (helper) -/
abbrev vtxQ (v : Fin 3) : (gelfandQ hcard).V := v

/-- The vertex `⋆` of `ex:gelfand`, read on `Γ_ℚ`.  @census none (helper) -/
abbrev vtxStarQ : (gelfandQ hcard).V := vtxQ hcard 1

/-- `c ≠ 1` in `Gal(ℚ[√-1]/ℚ)`: it moves `√-1`.  @census none (helper) -/
theorem galConj_ne_one : Dq.conj ≠ 1 := Dq.conj_ne_one

/-- In the order-two Galois group, every element other than `1` is `c`.  @census none (helper) -/
theorem eq_galConj_of_ne_one (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)
    {σ : Dq.carrier ≃ₐ[E] Dq.carrier} (hσ : σ ≠ 1) : σ = Dq.conj := by
  obtain ⟨w, -, hu⟩ := (Nat.card_eq_two_iff' (1 : Dq.carrier ≃ₐ[E] Dq.carrier)).mp hcard
  rw [hu σ hσ, ← hu Dq.conj galConj_ne_one]

/-- `c` acts on the vertices of `Γ_ℚ` by the `±`-swap.  @census none (helper) -/
theorem gelfandQ_smul_vertex (v : Fin 3) :
    Dq.conj • vtxQ hcard v = vtxQ hcard (RQuiver.gelfandVertexSwap v) :=
  Examples.gelfand_smul_vertex E Dq.carrier hcard galConj_ne_one v

/-- The edges of `Γ_ℚ` by index.  @census none (helper) -/
abbrev edgeQ (e : Fin 4) : (gelfandQ hcard).E := e

/-- `c` acts on the edges of `Γ_ℚ` by the `±`-swap.  @census none (helper) -/
theorem gelfandQ_smul_edge (e : Fin 4) :
    Dq.conj • edgeQ hcard e = edgeQ hcard (RQuiver.gelfandEdgeSwap e) :=
  Examples.gelfand_smul_edge E Dq.carrier hcard galConj_ne_one e

/-- **`Rep^nil(Γ_ℚ)` with `ex:gelfand`'s relation**: the full subcategory of `Rep(Γ_ℚ)` of
finite-dimensional nilpotent representations satisfying `a₋b₋ = a₊b₊` (S5's
`Examples.SatisfiesGelfandRelation`).  See `Gelfand/Construction.lean`, "The split Gelfand quiver
…, with its relation", for why the relation is part of the target.

@census none (auxiliary; the target category of `RQ-5.05-C26`) -/
def RepNilRelQ : ObjectProperty (RationalQuiver.FDRep (gelfandQ hcard)) :=
  fun M => M.toRep.IsNilpotent ∧ Examples.SatisfiesGelfandRelation E Dq.carrier hcard M.toRep

/-- `Rep^nil(Γ_ℚ)`, as a category.  @census none (auxiliary) -/
noncomputable abbrev RepNilQ : Type 1 := (RepNilRelQ hcard).FullSubcategory

/-- **The underlying split representation** of `V` (route (α)): the same vertex spaces and edge
maps, with the trivial `Gal(L/L)`-structure.  Its vertex spaces and edges are *definitionally*
those of `V`, so the `c`-free core read at `toSplitW V` is the non-split engine's.
@census none (spike; route (α)) -/
noncomputable def toSplitRep (V : RepNilQ hcard) : RationalQuiver.FDRep (gelfandSplit Dq.carrier) where
  toRep := RationalQuiver.Rep.ofFiniteDimensional (Γ := gelfandSplit Dq.carrier)
    (fun v => V.obj.toRep.M v) (fun _ _ => AddEquiv.refl _)
    (fun σ v a m => by rw [galSelf_apply]; rfl) (fun _ _ _ _ => rfl)
    (fun e => V.obj.toRep.φEdge e) (fun _ _ _ _ h => by cases h; rfl)
  finiteDimensional v := V.obj.finiteDimensional v

/-- `toSplitRep V` is nilpotent and satisfies the relation.  @census none (spike; route (α)) -/
noncomputable abbrev toSplitW (V : RepNilQ hcard) : (RepNilRelSplit Dq.carrier).FullSubcategory :=
  ⟨toSplitRep hcard V, V.property.1, V.property.2⟩

end Target

/-! ### The data of `𝔼_ℚ(M)`: `𝔼_{ℚ[√-1]}(M)` and `φ_• = c ∘ φ^{(∞)}_•` -/

section Data

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)
variable (hℓ : 1 ≤ ℓ) (A : HCEObj ℓ E Dq)

/-- The weight datum of `M_{ℚ[√-1]}` as a `QiSetup`.  @census none (helper) -/
@[reducible] noncomputable def _root_.RationalQuivers.Gelfand.HCEObj.qi : Split.QiSetup Dq.carrier ℓ A.carrier := A.toF.setup

/-- The limit `φ^{(∞)}_v` attached to a vertex: the `(−)`-run at `−`, the `(⋆)`-run at `⋆`, the
`(+)`-run at `+` (`eq:varphiminus`, `eq:varphistar`, `eq:varphiplus`).  @census none (helper) -/
noncomputable def limAt (v : Fin 3) : Module.End Dq.carrier A.carrier :=
  ![(inputMinus A.setup).limPlus, (inputStar A.setup hℓ).limPlus, (inputPlus A.setup).limPlus] v

/-- `φ^{(∞)}_v` sends `M(v)` into `c(M(c·v))`.  @census none (helper) -/
theorem limAt_mem : ∀ (v : Fin 3) (m : A.carrier),
    limAt hℓ A v m ∈ A.setup.weight.comp (-(vtxIdx ℓ (RQuiver.gelfandVertexSwap v)))
  | 0, m => (inputMinus A.setup).limPlus_mem m
  | 1, m => by
    have h := (inputStar A.setup hℓ).limPlus_mem m
    rwa [show -(inputStar A.setup hℓ).idxMinus = -(vtxIdx ℓ (RQuiver.gelfandVertexSwap 1)) from
      rfl] at h
  | 2, m => (inputPlus A.setup).limPlus_mem m

/-- **The rational structure** `φ_{v,c} := c ∘ φ^{(∞)}_v : M(v) → M(c·v)` on the carrier
(`eq:varphiplus`, `eq:varphiminus`, `eq:varphistar`).  @census none (helper) -/
noncomputable def phiC (v : Fin 3) (m : A.carrier) : A.carrier :=
  A.setup.conj (limAt hℓ A v m)

theorem phiC_mem (v : Fin 3) (m : A.carrier) :
    phiC hℓ A v m ∈ A.setup.weight.comp (vtxIdx ℓ (RQuiver.gelfandVertexSwap v)) := by
  have h := A.setup.conj_comp _ _ (limAt_mem hℓ A v m)
  rwa [neg_neg] at h

theorem phiC_add (v : Fin 3) (m m' : A.carrier) :
    phiC hℓ A v (m + m') = phiC hℓ A v m + phiC hℓ A v m' := by
  simp only [phiC, map_add]

theorem phiC_smul (v : Fin 3) (a : Dq.carrier) (m : A.carrier) :
    phiC hℓ A v (a • m) = Dq.conj a • phiC hℓ A v m := by
  simp only [phiC, map_smul, A.setup.conj_smul]

/-- The four edge maps of `𝔼_{ℚ[√-1]}(M)` as endomorphisms of the carrier:
`a₋ ↦ X`, `b₋ ↦ Y`, `a₊ ↦ X⋆⁻¹Y`, `b₊ ↦ XX⋆`.  @census none (helper) -/
noncomputable def edgeOp (e : Fin 4) : Module.End Dq.carrier A.carrier :=
  ![A.setup.weight.X, A.setup.weight.Y,
    (A.qi.starInverses hℓ).xStarInv ∘ₗ A.setup.weight.Y,
    A.setup.weight.X ∘ₗ Split.xStar A.qi] e

/-- The edge maps of `E_Qi_rep`, on underlying elements, are `edgeOp`.  @census none (helper) -/
theorem E_Qi_edge_val : ∀ (e : Fin 4) (m : Split.V3 A.qi (RQuiver.gelfand.source e)),
    ((Split.E_F_edge A.qi (A.qi.starInverses hℓ) hℓ e m : Split.V3 A.qi (RQuiver.gelfand.target e))
      : A.carrier) = edgeOp hℓ A e (m : A.carrier)
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

/-- **The propositions `𝔼_ℚ(M)` needs to be an object** — `C1`'s "well-defined":
* `cocycle`: `eq:semi-linearactiononrep` (`C2`) — `φ_{c·v,c} ∘ φ_{v,c} = 𝟏` on `M(v)`;
* `equiv`: `eq:koecheractiononrep` (`C4`) — `φ_{c·e} ∘ φ_{s(e),c} = φ_{t(e),c} ∘ φ_e` for the four
  edges;
* `nilpotent`, `relation`: `𝔼_{ℚ[√-1]}(M)` is nilpotent (`RQ-5.01-C8`) and satisfies the relation
  (`RQ-5.01-C7`), in the raw path-composite form both `RepNilRelSplit` and `RepNilRelQ` unfold to.

@census none (auxiliary; the bundle `E_QFunctor` consumes) -/
structure ObjSpec : Prop where
  cocycle : ∀ (v : Fin 3) (m : A.carrier), m ∈ A.setup.weight.comp (vtxIdx ℓ v) →
    phiC hℓ A (RQuiver.gelfandVertexSwap v) (phiC hℓ A v m) = m
  equiv : ∀ (e : Fin 4) (m : A.carrier), m ∈ A.setup.weight.comp (vtxIdx ℓ (RQuiver.gelfand.source e)) →
    edgeOp hℓ A (RQuiver.gelfandEdgeSwap e) (phiC hℓ A (RQuiver.gelfand.source e) m)
      = phiC hℓ A (RQuiver.gelfand.target e) (edgeOp hℓ A e m)
  nilpotent : ∃ n : ℕ, ∀ (a b : (gelfandQ hcard).V) (p : Quiver.Path a b), n ≤ p.length →
    RationalQuiver.pathCompose (Q := (gelfandQ hcard).toRQuiver) (Split.V3 A.qi)
      (Split.E_F_edge A.qi (A.qi.starInverses hℓ) hℓ) p = 0
  relation : RationalQuiver.pathCompose (Q := (gelfandQ hcard).toRQuiver) (Split.V3 A.qi)
      (Split.E_F_edge A.qi (A.qi.starInverses hℓ) hℓ) (Examples.gelfandPathMinus E Dq.carrier hcard)
    = RationalQuiver.pathCompose (Q := (gelfandQ hcard).toRQuiver) (Split.V3 A.qi)
      (Split.E_F_edge A.qi (A.qi.starInverses hℓ) hℓ) (Examples.gelfandPathPlus E Dq.carrier hcard)

end Data

/-- **Functoriality of the limits** (`C5`): a morphism of `HC_λ(𝔤,K)_ℚ` commutes with the three
unipotent stabilizations.  @census none (auxiliary; the bundle `E_QFunctor` consumes on morphisms) -/
def HomSpec (hℓ : 1 ≤ ℓ) {A B : HCEObj ℓ E Dq} (f : A ⟶ B) : Prop :=
  ∀ (v : Fin 3) (m : A.carrier), f.toLinearMap (limAt hℓ A v m) = limAt hℓ B v (f.toLinearMap m)

/-- The joint specification of `𝔼_ℚ`: `ObjSpec` at every object and `HomSpec` at every morphism.
@census none (auxiliary) -/
def E_QSpec (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2) (hℓ : 1 ≤ ℓ) : Prop :=
  (∀ A : HCEObj ℓ E Dq, ObjSpec hcard hℓ A) ∧ (∀ (A B : HCEObj ℓ E Dq) (f : A ⟶ B), HomSpec hℓ f)



/-! ## The native `𝔼_E` on `HC ℓ E D` (stage T3) -/

section NativeHC

set_option linter.unusedSectionVars false

variable {D : ImagUnit E}

/-- The `σ`-free weight datum of `M_{L_E}`.  @census none (helper) -/
abbrev _root_.RationalQuivers.HC.HC.qi (A : HC ℓ E D) : Split.QiSetup D.L ℓ A.carrier :=
  ⟨A.weight, A.gic⟩



/-- **Step O-9**: the three situations `(−)`, `(⋆)`, `(+)` of `prop:unipotentstabilization` for
`L_E/E`, `τ = c`, `W_K = M_E`.  @census none (helper) -/
noncomputable def stabInput (A : HC ℓ E D) (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) (hℓ : 1 ≤ ℓ) :
    Fin 3 → StabInput (A.setup h) :=
  ![inputMinus (A.setup h), inputStar (A.setup h) hℓ, inputPlus (A.setup h)]

/-- `φ^{(∞)}_v`.  @census none (helper) -/
noncomputable def limAtHC (A : HC ℓ E D) (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) (hℓ : 1 ≤ ℓ)
    (v : Fin 3) : Module.End D.L A.carrier :=
  (stabInput A h hℓ v).limPlus

theorem limAtHC_eq (A : HC ℓ E D) (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) (hℓ : 1 ≤ ℓ)
    (v : Fin 3) : limAtHC A h hℓ v = limAt hℓ (A.toHCEObj h) v := by
  fin_cases v <;> rfl

/-- **Step O-12**: `φ_{v,σ}` by dispatch on `χ_E(σ)`.  @census none (helper)
@clauses   RQ2-5.04-S-O12 -/
noncomputable def E_E_φ (hℓ : 1 ≤ ℓ) (A : HC ℓ E D) (σ : D.L ≃ₐ[E] D.L) (v : Fin 3)
    (m : A.carrier) : A.carrier :=
  if hσ : D.chi σ = -1 then A.galAct σ (limAtHC A ⟨σ, hσ⟩ hℓ v m) else m

variable (hℓ : 1 ≤ ℓ) (A : HC ℓ E D)

theorem E_E_φ_of_neg {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = -1) (v : Fin 3) (m : A.carrier) :
    E_E_φ hℓ A σ v m = A.galAct σ (limAtHC A ⟨σ, hσ⟩ hℓ v m) := by
  simp [E_E_φ, hσ]

theorem E_E_φ_of_one {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = 1) (v : Fin 3) (m : A.carrier) :
    E_E_φ hℓ A σ v m = m := by
  have : D.chi σ ≠ -1 := by rw [hσ]; decide
  simp [E_E_φ, this]

/-- `φ_{v,c}` is the relocated engine's `phiC` on the bridged object.  @census none (helper) -/
theorem E_E_φ_eq_phiC {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = -1) (v : Fin 3) (m : A.carrier) :
    E_E_φ hℓ A σ v m = phiC hℓ (A.toHCEObj ⟨σ, hσ⟩) v m := by
  rw [E_E_φ_of_neg hℓ A hσ, limAtHC_eq]
  show _ = (A.setup ⟨σ, hσ⟩).conj _
  rw [A.setup_conj _ hσ]
  rfl


/-- The bridge's setup of `B.toHC` is `B`'s.  @census none (helper) -/
theorem setup_toHC {hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1} (B : HCEObj ℓ E (D.sqrtExt hc)) :
    B.toHC.setup hc = B.setup := by
  obtain ⟨form, carrier, ⟨bc, w, gic, conj, cs, ci, cb, cc, cX, cY, cH⟩, adm, cc', fg⟩ := B
  have hconj : galActOf D bc (D.sqrtExt hc).conj = conj := by
    ext v
    exact HCEObj.galActOf_conj (⟨form, carrier, ⟨bc, w, gic, conj, cs, ci, cb, cc, cX, cY, cH⟩,
      adm, cc', fg⟩ : HCEObj ℓ E (D.sqrtExt hc)) v
  simp only [HC.setup, HCEObj.toHC, RationalSetupOver.mk.injEq, hconj, true_and]

theorem phiC_toHC {hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1} (B : HCEObj ℓ E (D.sqrtExt hc))
    (v : Fin 3) (m : B.carrier) : phiC hℓ (B.toHC.toHCEObj hc) v m = phiC hℓ B v m := by
  show (B.toHC.setup hc).conj (![(inputMinus (B.toHC.setup hc)).limPlus,
      (inputStar (B.toHC.setup hc) hℓ).limPlus, (inputPlus (B.toHC.setup hc)).limPlus] v m)
    = B.setup.conj (![(inputMinus B.setup).limPlus, (inputStar B.setup hℓ).limPlus,
      (inputPlus B.setup).limPlus] v m)
  rw [setup_toHC]
  rfl


end NativeHC

end RationalQuivers.Gelfand.RationalStructure
