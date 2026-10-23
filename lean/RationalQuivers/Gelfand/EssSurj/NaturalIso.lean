import RationalQuivers.Gelfand.EssSurj.Descent

/-!
# essential surjectivity, the natural isomorphism (§5.3, Steps O-20 … O-24)

`γ̃ = 2^{ℓ-1}(ℓ-1)!` and `X⋆` as a polynomial in `n⋆` (C17, read from T2's `Split.xStar_eq_poly` /
star chain), `C18`–`C24` (`limStarV_eq_one` = `eq:phistaridentity`, `limPM_conj_inverse` =
`eq:pmsquarerootsinverses`, `s_± = (φ^{(∞)}_±)^{1/2}`, `t = X⋆^{1/2}`), the comparison `natPsi` and
`essSurj_naturalIsomorphism`.  Native: the re-indexing of `Rep^nil(Γ_E)` along T1's
`gelfandOfSign = gelfandOfCardTwo` (`toCardTwo`) and `E_E_essSurj` (split case: T2's `Split.essSurj`,
Step O-7h; non-split: the construction above).

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Equivalence.lean (§PinnedComposites … §E3, `essSurj_operators` … §E8, §Main)` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.EssSurj.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

*(2026-10-21, O-V2-6 round 2.)*  Carried docstrings below name, in the present tense, S8's
`E_Qi_edge`, S8's `Gelfand/Category.lean` with `HCQObj` and S7's `RationalSetup`, and
"the frozen claimant of `RQ-5.05`" (v1's `Gelfand.E_Q_equivalence`).  All of them were deleted
with the v1 Q-chain at WP-13 (`ae9eda9`, `9c6b193`).  The v2 forms are:
* `Split.E_F_edge` (`Gelfand/Split/Construction.lean`) and `RationalStructure.E_Qi_edge_val`;
* `HCEObj` over `RationalSetupOver`;
* `RQ2-5.05`'s claimant `Gelfand.Rational.E_Q_equivalence` (`Gelfand/Rational.lean`).

@census none (module)
-/

namespace RationalQuivers.Gelfand.EssSurj

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {Dq : SqrtNegOneExt E}
open scoped TensorProduct Classical

variable {ℓ : ℕ}

section EssSurj

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2) (hℓ : 1 ≤ ℓ)

/-! #### Reading a composite of the pinned formulas -/

section PinnedComposites

variable {V : Gelfand.RationalStructure.RepNilQ hcard} (D : EssSurjData hcard hℓ V)
variable {W₁ W₂ : Type} [AddCommGroup W₁] [Module Dq.carrier W₁]
  [AddCommGroup W₂] [Module Dq.carrier W₂] {p q : ℤ}

/-- **`4XY` from the pins.**  If `Y` carries `M_p` to `M_q` as `g` and `X` carries `M_q` back to
`M_p` as `f` — the shape of every `X_*`/`Y_*` field of `EssSurjData` — then `4XY` on `M_p` is
`4(f∘g)` read through `e₁`.  @census none (helper) -/
theorem pin_compose
    (e₁ : D.setup.weight.comp p ≃ₗ[Dq.carrier] W₁)
    (e₂ : D.setup.weight.comp q ≃ₗ[Dq.carrier] W₂)
    (g : W₁ →ₗ[Dq.carrier] W₂) (f : W₂ →ₗ[Dq.carrier] W₁)
    (hY : ∀ v (hv : v ∈ D.setup.weight.comp p),
      D.setup.weight.Y v = ((e₂.symm (g (e₁ ⟨v, hv⟩)) : D.setup.weight.comp q) : D.carrier))
    (hX : ∀ w (hw : w ∈ D.setup.weight.comp q),
      D.setup.weight.X w = ((e₁.symm (f (e₂ ⟨w, hw⟩)) : D.setup.weight.comp p) : D.carrier))
    (h : Module.End Dq.carrier W₁) (hh : h = (4 : Dq.carrier) • (f ∘ₗ g))
    (v : D.carrier) (hv : v ∈ D.setup.weight.comp p) :
    (4 : Dq.carrier) • D.setup.weight.X (D.setup.weight.Y v)
      = ((e₁.symm (h (e₁ ⟨v, hv⟩)) : D.setup.weight.comp p) : D.carrier) := by
  have hYm : D.setup.weight.Y v ∈ D.setup.weight.comp q := by
    rw [hY v hv]; exact Submodule.coe_mem _
  have hsub : (⟨D.setup.weight.Y v, hYm⟩ : D.setup.weight.comp q) = e₂.symm (g (e₁ ⟨v, hv⟩)) :=
    Subtype.ext (hY v hv)
  rw [hX _ hYm, hsub, LinearEquiv.apply_symm_apply, hh]
  simp

/-- **`4YX` from the pins**, the companion of `pin_compose` on the other component.
@census none (helper) -/
theorem pin_compose'
    (e₁ : D.setup.weight.comp p ≃ₗ[Dq.carrier] W₁)
    (e₂ : D.setup.weight.comp q ≃ₗ[Dq.carrier] W₂)
    (g : W₁ →ₗ[Dq.carrier] W₂) (f : W₂ →ₗ[Dq.carrier] W₁)
    (hY : ∀ v (hv : v ∈ D.setup.weight.comp p),
      D.setup.weight.Y v = ((e₂.symm (g (e₁ ⟨v, hv⟩)) : D.setup.weight.comp q) : D.carrier))
    (hX : ∀ w (hw : w ∈ D.setup.weight.comp q),
      D.setup.weight.X w = ((e₁.symm (f (e₂ ⟨w, hw⟩)) : D.setup.weight.comp p) : D.carrier))
    (h : Module.End Dq.carrier W₂) (hh : h = (4 : Dq.carrier) • (g ∘ₗ f))
    (w : D.carrier) (hw : w ∈ D.setup.weight.comp q) :
    (4 : Dq.carrier) • D.setup.weight.Y (D.setup.weight.X w)
      = ((e₂.symm (h (e₂ ⟨w, hw⟩)) : D.setup.weight.comp q) : D.carrier) := by
  have hXm : D.setup.weight.X w ∈ D.setup.weight.comp p := by
    rw [hX w hw]; exact Submodule.coe_mem _
  have hsub : (⟨D.setup.weight.X w, hXm⟩ : D.setup.weight.comp p) = e₁.symm (f (e₂ ⟨w, hw⟩)) :=
    Subtype.ext (hX w hw)
  rw [hY _ hXm, hsub, LinearEquiv.apply_symm_apply, hh]
  simp

end PinnedComposites

/-! #### `C17`/`C18` — the middle-range chain, and `X⋆` as a product of `ξ`'s

The pins `X_star`/`Y_star` read `2X|_{M_{j-1}} = ξ^{(j)}_{⋆,+}` and `2Y|_{M_{j+1}} = ξ^{(j)}_{⋆,-}`
for `-ℓ < j < ℓ`.  Running the chain `ℓ-1` steps **up** from `M_{-(ℓ-1)}` and `ℓ-1` steps **down**
from `M_{ℓ-1}` produces the *same* product `∏_{k=1}^{ℓ-1}(φ_⋆^{1/2} + (2k-ℓ)·𝟏)`: this is `C17`'s
first display, and `C18`'s `X⋆ = Y⋆` falls out of it rather than out of a separate argument. -/

section StarChain

variable {V : Gelfand.RationalStructure.RepNilQ hcard}

end StarChain

section StarChainData

variable {hcard hℓ} {V : Gelfand.RationalStructure.RepNilQ hcard} (D : EssSurjData hcard hℓ V)

namespace EssSurjData

end EssSurjData

end StarChainData

section StarChain2

variable {V : Gelfand.RationalStructure.RepNilQ hcard}

/-! #### The two left-hand edges intertwine the `⋆`- and `−`-vertex operators

`n_⋆ = φ_{a₋}φ_{b₋}` and `n_- = φ_{b₋}φ_{a₋}` are the two length-two loops through the same pair of
edges, so `φ_{a₋} n_- = n_⋆ φ_{a₋}` and `n_- φ_{b₋} = φ_{b₋} n_⋆` by associativity alone.  Every
operator built from `n_•` by scalars and `def:squareroots` therefore intertwines as well — the
square root by `sqrtOfScalarPlusNilpotent_natural` — which is clause **(e)** of
`prop:unipotentsquareroots` since the author's ruling of 2026-09-11 (census `RQ-4.05-C7`).  Until
that ruling this was what `RQ-5.05-C25`'s **corrected** left-hand squares asserted (`AN-41`, ruling
`R-S8-17`); `C25` is retired in the amended source, and these two intertwining facts are kept as
the compiled record of it (`stages/S8/DESIGN-NOTES.md` §13).

`edgeAm`/`edgeBm` are `Vedge … 0`/`Vedge … 1` with their endpoints normalised to `Fin 3`
literals: the raw maps have type `VM (Γ.source e) → VM (Γ.target e)`, whose indices are
`Matrix.cons` applications that `rw` will not see through. -/

/-- `c`-conjugation at the vertex `⋆`, with its codomain normalised to the literal `1`: the raw
`conjBy … (Vphi hcard V 1)` lands in `End (VM (toSplitW hcard V) (gelfandVertexSwap 1))`, whose index `rw`
will not see through.  @census none (helper) -/
noncomputable def conjStar (V : Gelfand.RationalStructure.RepNilQ hcard) (φ : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1)) :
    Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :=
  conjBy Dq.conj (Vphi hcard V 1) (Vphi_smul hcard V 1) φ

theorem conjStar_one (V : Gelfand.RationalStructure.RepNilQ hcard) : conjStar hcard V 1 = 1 :=
  conjBy_one Dq.conj (Vphi hcard V 1) (Vphi_smul hcard V 1)

theorem conjStar_mul (V : Gelfand.RationalStructure.RepNilQ hcard) (a b : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1)) :
    conjStar hcard V (a * b) = conjStar hcard V a * conjStar hcard V b :=
  conjBy_mul Dq.conj (Vphi hcard V 1) (Vphi_smul hcard V 1) a b

theorem conjStar_smul (V : Gelfand.RationalStructure.RepNilQ hcard) (c : Dq.carrier)
    (a : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1)) :
    conjStar hcard V (c • a) = Dq.conj c • conjStar hcard V a :=
  conjBy_smul Dq.conj (Vphi hcard V 1) (Vphi_smul hcard V 1) c a

theorem conjStar_xiOp (V : Gelfand.RationalStructure.RepNilQ hcard) (s j : ℤ) :
    conjStar hcard V (Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 s j) = Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 s j :=
  conjBy_xiOp hcard hℓ V 1 s j

theorem conjStar_xiProd (V : Gelfand.RationalStructure.RepNilQ hcard) (i : ℕ) :
    conjStar hcard V (Split.xiProd hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 i) = Split.xiProd hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 i := by
  induction i with
  | zero => rw [Split.xiProd_zero]; exact conjStar_one hcard V
  | succ i ih => rw [Split.xiProd_succ, conjStar_mul, conjStar_xiOp, ih]

/-- `c` fixes `X⋆`: it is a polynomial in `φ_⋆^{1/2}` with rational coefficients and `c` fixes
both.  This was `C25`'s rational-structure conjunct until the author's ruling of 2026-09-11
retired that clause; it is now consumed by `C18` (`essSurj_C18_xStar`) and, through
`conjStar_sqrt_xStar`, by `C24`'s `⋆`-vertex conjugation.  @census none (helper) -/
theorem conjStar_xStarAt (V : Gelfand.RationalStructure.RepNilQ hcard) :
    conjStar hcard V (Split.xStarAt hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1) = Split.xStarAt hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 := by
  have hc : Dq.conj (((Split.gammaStarF Dq.carrier ℓ) * (2 : Dq.carrier) ^ (ℓ - 1))⁻¹)
      = ((Split.gammaStarF Dq.carrier ℓ) * (2 : Dq.carrier) ^ (ℓ - 1))⁻¹ := by
    rw [map_inv₀, map_mul, GF.conj_gammaStarF, map_pow, map_ofNat]
  show conjStar hcard V (((Split.gammaStarF Dq.carrier ℓ) * (2 : Dq.carrier) ^ (ℓ - 1))⁻¹
      • Split.xiProd hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 (ℓ - 1)) = _
  rw [conjStar_smul, hc, conjStar_xiProd]
  rfl

/-- A `c`-invariant operator at `⋆` commutes with `φ_{⋆,c}`.  @census none (helper) -/
theorem Vphi_comm_of_conjStar (V : Gelfand.RationalStructure.RepNilQ hcard) {φ : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1)}
    (h : conjStar hcard V φ = φ) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Vphi hcard V 1 (φ x) = φ (Vphi hcard V 1 x) := by
  have hx := DFunLike.congr_fun h (Vphi hcard V 1 x)
  calc Vphi hcard V 1 (φ x)
      = Vphi hcard V 1 (φ ((Vphi hcard V 1).symm (Vphi hcard V 1 x))) := by
        rw [AddEquiv.symm_apply_apply]
    _ = conjStar hcard V φ (Vphi hcard V 1 x) := rfl
    _ = φ (Vphi hcard V 1 x) := hx

end StarChain2

section StarChainData2

variable {hcard hℓ} {V : Gelfand.RationalStructure.RepNilQ hcard} (D : EssSurjData hcard hℓ V)

namespace EssSurjData

end EssSurjData

end StarChainData2

/-- **`RQ-5.05-C18`, the two conjuncts about `X_⋆`**: `X_⋆ = Y_⋆` and `X_⋆^c = X_⋆`.  (The third
conjunct, `φ^{(∞),c}_⋆ = φ^{(∞)}_⋆`, was proved at shift 8 as `EssSurjData.limStarV_conj`,
consumed directly at the `C18` assembly site below — corrected 2026-09-05, G7 integration,
V-S8G4-2(a): this docstring's "blocked on engine `E3`" was stale.)  @census none (helper) -/
theorem essSurj_C18_xStar (V : Gelfand.RationalStructure.RepNilQ hcard) (D : EssSurjData hcard hℓ V) :
    D.xStarV = D.yStarV ∧
      (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1,
        Vphi hcard V 1 (D.xStarV ((Vphi hcard V 1).symm x)) = D.xStarV x) := by
  refine ⟨D.xStarV_eq_yStarV, fun x => ?_⟩
  rw [D.xStarV_eq]
  exact DFunLike.congr_fun (conjStar_xStarAt hcard hℓ V) x

/-! ### `RQ-5.05-C25` — RETIRED IN THE SOURCE, 2026-09-11

Until the paper author's ruling of 2026-09-11 the source's `thm:EEQQequivalence` closed with the
sentence *"the `ℚ`-rational quiver representations appearing in `eq:limitsquarerootdiagram0` and
`eq:limitsquarerootdiagram1` are isomorphic over `ℚ` via the isomorphism
`({\bf1}_{V(+)}, X_\star, {\bf1}_{V(-)})`"*, which on its two **left-hand** edges read
`X⋆ φ_{a₋} = φ_{a₋}` and `φ_{b₋} X⋆ = φ_{b₋}` — false whenever `ñ_⋆ ≠ 0` (`AN-41`). This tree
rendered it with the corrected third component `X⋆^{(−)} := xStarAt … 0` under coordinator ruling
`R-S8-17`, as a theorem `EssSurjData.essSurj_C25`.

The author ruled **Option B**: the sentence is **DELETED**, not corrected, and the single triple
`(s₊, t, s₋)` of `essSurj_C24` is what the proof concludes with. Census revision r14
(tag `census-v1.11`) records `RQ-5.05-C25` as `RETIRED BY SOURCE EDIT r14 (2026-09-11)` with its
content absorbed into `RQ-5.05-C24`, so **the tree carries no `C25` rendering**: `essSurj_C25` was
removed in the same round, and `essSurj_naturalIsomorphism`'s ninth conjunct with it. The two
naturality facts that repair drew on — `edgeAm_xStarAt` and `edgeBm_xStarAt`, that `φ_{a₋}` and
`φ_{b₋}` intertwine `X⋆^{(−)}` with `X⋆` — are kept above: they are true, compiled, and are the
`xStarAt` instance of the naturality clause (e) the same ruling added to
`prop:unipotentsquareroots` (`RQ-4.05-C7`, `sqrt_natural`). -/


end EssSurj

section EssSurj

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2) (hℓ : 1 ≤ ℓ)

section E3

variable {hcard hℓ}

namespace EssSurjData

variable {V : Gelfand.RationalStructure.RepNilQ hcard} (D : EssSurjData hcard hℓ V)

/-- `W_{-(ℓ-1)} ≃ V(⋆)`.  @census none (helper: `E3`) -/
noncomputable def thStar : Gelfand.RationalStructure.Wc D.setup (-((ℓ : ℤ) - 1)) ≃ₗ[Dq.carrier] Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1 :=
  Gelfand.RationalStructure.readVia D.setup D.toStarLo

/-- `W_{ℓ+1} ≃ V(+)`.  @census none (helper: `E3`) -/
noncomputable def thPlus : Gelfand.RationalStructure.Wc D.setup ((ℓ : ℤ) + 1) ≃ₗ[Dq.carrier] Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2 :=
  Gelfand.RationalStructure.readVia D.setup D.toPlus

/-- `W_{-(ℓ+1)} ≃ V(−)`.  @census none (helper: `E3`) -/
noncomputable def thMinus : Gelfand.RationalStructure.Wc D.setup (-((ℓ : ℤ) + 1)) ≃ₗ[Dq.carrier] Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0 :=
  Gelfand.RationalStructure.readVia D.setup D.toMinus

/-- The `(⋆)` run's identification `M_{-(ℓ-1)}^τ = M_{ℓ-1} ≅ V(⋆) ≅ M_{-(ℓ-1)}` — the one
`eq:limitsquarerootdiagram0` uses.  It exists although `W_-^τ ≠ W_+`, which is why `E3` reaches
the `(⋆)` run.  @census none (helper: `E3`) -/
noncomputable def eStar :
    twist Dq.conj (Gelfand.RationalStructure.Wc D.setup (-((ℓ : ℤ) - 1))) ≃ₗ[Dq.carrier] Gelfand.RationalStructure.Wc D.setup (-((ℓ : ℤ) - 1)) :=
  Gelfand.RationalStructure.identVia D.setup (neg_neg _) D.toStarLo D.toStarHi

/-- The `(+)` run's identification; here `W_-^τ = W_+` already, so this is S6's `ofEq hWp`.
@census none (helper: `E3`) -/
noncomputable def ePlus :
    twist Dq.conj (Gelfand.RationalStructure.Wc D.setup (-((ℓ : ℤ) + 1))) ≃ₗ[Dq.carrier] Gelfand.RationalStructure.Wc D.setup ((ℓ : ℤ) + 1) :=
  Gelfand.RationalStructure.identVia D.setup (neg_neg _) D.toPlus D.toPlus

/-- The `(−)` run's identification.  @census none (helper: `E3`) -/
noncomputable def eMinus :
    twist Dq.conj (Gelfand.RationalStructure.Wc D.setup ((ℓ : ℤ) + 1)) ≃ₗ[Dq.carrier] Gelfand.RationalStructure.Wc D.setup (-((ℓ : ℤ) + 1)) :=
  Gelfand.RationalStructure.identVia D.setup rfl D.toMinus D.toMinus

/-- `P₀` of the `(⋆)` run is `X⋆` read on `V(⋆)`.  @census none (helper: `E3`) -/
theorem eStar_phpT :
    asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).phpT) = Gelfand.RationalStructure.endConjOf D.thStar D.xStarV := by
  refine LinearMap.ext fun z => ?_
  have hz : ((D.toStarLo.symm (D.thStar z) : D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier)
      ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) := (D.toStarLo.symm (D.thStar z)).2
  have key := Gelfand.RationalStructure.toEnd_read D.setup (neg_neg _) D.toStarLo D.toStarHi
    ((Gelfand.RationalStructure.inputStar D.setup hℓ).phpT) (D.thStar z)
    ⟨Split.xStar D.setup.toQiSetup ((D.toStarLo.symm (D.thStar z) :
        D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier),
      Split.xStar_mem (Q := D.setup.toQiSetup) (by ring) hℓ hz⟩
    (((Gelfand.RationalStructure.inputStar D.setup hℓ).seqPlus_zero_apply _ hz).symm)
  show _ = D.thStar.symm (D.xStarV (D.thStar z))
  rw [show D.xStarV (D.thStar z) = D.toStarHi ⟨Split.xStar D.setup.toQiSetup
      ((D.toStarLo.symm (D.thStar z) : D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier),
      Split.xStar_mem (Q := D.setup.toQiSetup) (by ring) hℓ hz⟩ from rfl, key]
  show _ = D.thStar.symm (D.thStar (asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).phpT)
      (D.thStar.symm (D.thStar z))))
  rw [D.thStar.symm_apply_apply, D.thStar.symm_apply_apply]

/-- `Q₀` of the `(⋆)` run is `Y⋆` read on `V(⋆)` — `X⋆^c = Y⋆` (`RQ-5.04-C3`, `conj_symmetry`)
seen through the identification.  @census none (helper: `E3`) -/
theorem eStar_phmT :
    asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).phmT)
      = Gelfand.RationalStructure.endConjOf D.thStar D.yStarV := by
  refine LinearMap.ext fun z => ?_
  have hz : ((D.toStarHi.symm (D.thStar z) : D.setup.weight.comp ((ℓ : ℤ) - 1)) : D.carrier)
      ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) := (D.toStarHi.symm (D.thStar z)).2
  have hcz : D.setup.conj ((D.toStarHi.symm (D.thStar z) :
      D.setup.weight.comp ((ℓ : ℤ) - 1)) : D.carrier)
      ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) := D.setup.conj_comp _ _ hz
  have h0 : Gelfand.RationalStructure.toEnd D.setup ((Gelfand.RationalStructure.inputStar D.setup hℓ).phmT)
      (D.setup.conj ((D.toStarHi.symm (D.thStar z) :
        D.setup.weight.comp ((ℓ : ℤ) - 1)) : D.carrier))
      = Split.xStar D.setup.toQiSetup (D.setup.conj ((D.toStarHi.symm (D.thStar z) :
        D.setup.weight.comp ((ℓ : ℤ) - 1)) : D.carrier)) :=
    (Gelfand.RationalStructure.inputStar D.setup hℓ).seqMinus_zero_apply _ hcz
  have hy : ((⟨Split.yStar D.setup.toQiSetup ((D.toStarHi.symm (D.thStar z) :
        D.setup.weight.comp ((ℓ : ℤ) - 1)) : D.carrier),
      Split.yStar_mem (Q := D.setup.toQiSetup) (by ring) hℓ hz⟩ :
        D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier)
      = D.setup.conj (Gelfand.RationalStructure.toEnd D.setup ((Gelfand.RationalStructure.inputStar D.setup hℓ).phmT)
          (D.setup.conj ((D.toStarHi.symm (D.thStar z) :
            D.setup.weight.comp ((ℓ : ℤ) - 1)) : D.carrier))) := by
    rw [h0]
    exact ((Gelfand.RationalStructure.conj_symmetry D.setup hℓ).2 _).symm
  have key := Gelfand.RationalStructure.asEndConjVia_read D.setup (neg_neg _) D.toStarLo D.toStarHi
    ((Gelfand.RationalStructure.inputStar D.setup hℓ).phmT) (D.thStar z) _ hy
  show _ = D.thStar.symm (D.yStarV (D.thStar z))
  rw [show D.yStarV (D.thStar z) = D.toStarLo ⟨Split.yStar D.setup.toQiSetup
      ((D.toStarHi.symm (D.thStar z) : D.setup.weight.comp ((ℓ : ℤ) - 1)) : D.carrier),
      Split.yStar_mem (Q := D.setup.toQiSetup) (by ring) hℓ hz⟩ from rfl, ← key]
  show _ = D.thStar.symm (D.thStar (asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.eStar
      ((Gelfand.RationalStructure.inputStar D.setup hℓ).phmT) (D.thStar.symm (D.thStar z))))
  rw [D.thStar.symm_apply_apply, D.thStar.symm_apply_apply]

/-- **`E3` at the `(⋆)` run** (`stages/S8/DESIGN-NOTES.md` §13.4, obstacle (a) discharged):
`φ^{(∞)}_⋆ = 𝟏` on `V(⋆)`.

The `(⋆)` run is exactly the one S6's `stabilizationSeq_addendum` cannot see (`W_+ = W_- =
M_{-(ℓ-1)}`, `W_-^τ = M_{ℓ-1}`), and it is also the one where the conclusion is sharpest, because
there `P₀ = Q₀`: `P₀` is `X⋆` and `Q₀` is `Y⋆` read on `V(⋆)` (`eStar_phpT`, `eStar_phmT`), and
`X⋆ = Y⋆` is `RQ-5.05-C18` (`xStarV_eq_yStarV`).  Hence every iterate has `P_k = Q_k`
(`asEndVia_eq_asEndConjVia`), and `eq:conjugateinverse` at the limit — S6's
`stabilizationSeq_conjugate_inverse` through `stab_limit_spec` — reads `(φ^{(∞)}_⋆)² = 𝟏`.  With
`φ^{(∞)}_⋆ = 𝟏 + nilpotent` from `E3` (whose `k = 0` input is `X⋆ = 𝟏 + ñ⋆`,
`xStarAt_eq_one_add`), the uniqueness statement of `prop:unipotentsquareroots`
(`Unipotent.sqrt_unique`), applied to `φ = 𝟏`, gives `φ^{(∞)}_⋆ = 𝟏^{1/2} = 𝟏` (the tex's
argument; v2 R-PROC-4 amendment T3-a1, route fix F-B4 / O-21, WP-16 triage verdict FIX-LEAN —
the earlier route closed with `eq_one_of_sq_eq_one_of_unipotent`, which is kept off-path).

@census none (helper: `E3`; the content of census clause `RQ-5.05-C19`)
@clauses   RQ2-5.12-S-O21 -/
theorem limStarV_eq_one : D.limStarV = 1 := by
  have hL : (2 : Dq.carrier) ≠ 0 := two_ne_zero_of_base (K := E) two_ne_zero
  obtain ⟨hpS, hmS, nS, hnilS, hnS⟩ := Gelfand.RationalStructure.stab_prereq D.setup hℓ (Gelfand.RationalStructure.inputStar D.setup hℓ) (by simp)
  obtain ⟨eS, hconstS, hlimS, hciS1, hciS2, hinvS1, hinvS2⟩ :=
    Gelfand.RationalStructure.stab_limit_spec (Gelfand.RationalStructure.inputStar D.setup hℓ) hpS hmS hnilS hnS
  have h0 : asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).phpT)
      = asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).phmT) := by
    rw [D.eStar_phpT, D.eStar_phmT, D.xStarV_eq_yStarV]
  obtain ⟨n', hn', -, heq⟩ := Split.xStarAt_eq_one_add hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1
  have hup : ∃ mp, IsNilpotent mp ∧
      asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).phpT) = 1 + mp := by
    refine ⟨Gelfand.RationalStructure.endConjOf D.thStar n', Gelfand.RationalStructure.isNilpotent_of_conj D.thStar.symm (fun _ => rfl) hn', ?_⟩
    rw [D.eStar_phpT, D.xStarV_eq, heq, Gelfand.RationalStructure.endConjOf_add, Gelfand.RationalStructure.endConjOf_one]
  have huq : ∃ mq, IsNilpotent mq ∧
      asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).phmT) = 1 + mq := by
    rw [← h0]; exact hup
  have hcomm : Commute (asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).phpT))
      (asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).phmT)) := by
    rw [← h0]
  obtain ⟨-, ⟨mp, hmp, hP⟩, -⟩ := stabilizationSeq_addendum_via two_ne_zero Gelfand.RationalStructure.galConj_mul_self
    D.eStar _ _ hcomm hup huq eS
  have heqk := asEndVia_eq_asEndConjVia two_ne_zero Gelfand.RationalStructure.galConj_mul_self D.eStar _ _
    hcomm hup huq h0 eS
  have hPQ : asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).limT.1)
      = asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).limT.2) := by
    rw [hlimS]; exact heqk
  have hQP : asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).limT.2)
      * asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).limT.1) = 1 := by
    rw [asEndConjVia_comp_asEndVia]; exact hciS1
  have hPlim : asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).limT.1) = 1 + mp := by
    rw [hlimS]; exact hP
  -- `P_∞ * P_∞ = 𝟏`, from `Q_∞ * P_∞ = 𝟏` and `P_∞ = Q_∞`
  have hAA : asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).limT.1)
      * asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).limT.1) = 1 := by
    have h := hQP
    rw [← hPQ] at h
    exact h
  -- `φ^{(∞)}_⋆` read through `V(⋆) ≃ W_{-(ℓ-1)}` is `P_∞`
  have hrd : ∀ x, D.limStarV x = D.thStar (asEndVia D.eStar
      ((Gelfand.RationalStructure.inputStar D.setup hℓ).limT.1) (D.thStar.symm x)) := by
    intro x
    have hmem : (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus ((D.toStarLo.symm x :
        D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier) ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) := by
      have h := (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus_mem ((D.toStarLo.symm x :
        D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier)
      rwa [show -(Gelfand.RationalStructure.inputStar D.setup hℓ).idxMinus = (ℓ : ℤ) - 1 by simp [Gelfand.RationalStructure.inputStar]] at h
    have key := Gelfand.RationalStructure.toEnd_read D.setup (neg_neg _) D.toStarLo D.toStarHi
      ((Gelfand.RationalStructure.inputStar D.setup hℓ).limT.1) x ⟨_, hmem⟩ rfl
    rw [show D.limStarV x = D.toStarHi ⟨_, hmem⟩ from rfl, key]
    rfl
  -- (b) of `prop:unipotentsquareroots`: `φ^{(∞)}_⋆ = 𝟏 + nilpotent`
  have hm' : IsNilpotent (Gelfand.RationalStructure.endConjOf D.thStar.symm mp) :=
    Gelfand.RationalStructure.isNilpotent_of_conj D.thStar (fun _ => rfl) hmp
  have hU : D.limStarV = 1 + Gelfand.RationalStructure.endConjOf D.thStar.symm mp := by
    refine LinearMap.ext fun x => ?_
    rw [hrd, hPlim]
    simp
  -- (a): `(φ^{(∞)}_⋆)² = 𝟏`
  have hsq : D.limStarV ^ 2 = 1 := by
    refine LinearMap.ext fun x => ?_
    have hAA' : ∀ y, asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).limT.1)
        (asEndVia D.eStar ((Gelfand.RationalStructure.inputStar D.setup hℓ).limT.1) y) = y :=
      fun y => by simpa using LinearMap.congr_fun hAA y
    show D.limStarV (D.limStarV x) = x
    rw [hrd, hrd, D.thStar.symm_apply_apply, hAA', D.thStar.apply_symm_apply]
  -- uniqueness of unipotent square roots, applied to `φ = 𝟏`: `φ^{(∞)}_⋆ = 𝟏^{1/2} = 𝟏`
  exact (Unipotent.sqrt_unique hL 1 D.limStarV _ hm' hU hsq).trans
    (Unipotent.sqrt_unique hL 1 1 0 IsNilpotent.zero (add_zero 1).symm (one_pow 2)).symm

/-- `P₀` of the `(+)` run is `𝟏` — its `φ_+` is `𝟏` (`casePlus`).  @census none (helper: `E3`) -/
theorem ePlus_phpT : asEndVia D.ePlus ((Gelfand.RationalStructure.inputPlus D.setup).phpT) = 1 := by
  refine LinearMap.ext fun z => ?_
  have hz : D.setup.baseChange (z : Dq.carrier ⊗[E] D.form)
      ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := z.2
  have key := Gelfand.RationalStructure.toEnd_read_apply D.setup (neg_neg _) D.toPlus D.toPlus
    ((Gelfand.RationalStructure.inputPlus D.setup).phpT) z (Gelfand.RationalStructure.wcEquivComp D.setup ((ℓ : ℤ) + 1) z)
    (((Gelfand.RationalStructure.inputPlus D.setup).seqPlus_zero_apply _ hz).symm)
  exact ((Gelfand.RationalStructure.readVia D.setup D.toPlus).injective key).symm

/-- `Q₀` of the `(−)` run is `𝟏` — its `φ_-` is `𝟏` (`caseMinus`).  @census none (helper: `E3`) -/
theorem eMinus_phmT :
    asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.eMinus ((Gelfand.RationalStructure.inputMinus D.setup).phmT) = 1 := by
  refine LinearMap.ext fun z => ?_
  set u : D.carrier := ((D.toMinus.symm (Gelfand.RationalStructure.readVia D.setup D.toMinus z) :
    D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier) with hudef
  have hz : u ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) :=
    (D.toMinus.symm (Gelfand.RationalStructure.readVia D.setup D.toMinus z)).2
  have hcz : D.setup.conj u ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := by
    have h := D.setup.conj_comp _ _ hz
    rwa [neg_neg] at h
  have h0 : Gelfand.RationalStructure.toEnd D.setup ((Gelfand.RationalStructure.inputMinus D.setup).phmT) (D.setup.conj u) = D.setup.conj u :=
    (Gelfand.RationalStructure.inputMinus D.setup).seqMinus_zero_apply _ hcz
  have hy : ((D.toMinus.symm (Gelfand.RationalStructure.readVia D.setup D.toMinus z) :
        D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier)
      = D.setup.conj (Gelfand.RationalStructure.toEnd D.setup ((Gelfand.RationalStructure.inputMinus D.setup).phmT) (D.setup.conj u)) := by
    rw [h0, Gelfand.RationalStructure.conj_conj]
  have key := Gelfand.RationalStructure.asEndConjVia_read_apply D.setup rfl D.toMinus D.toMinus
    ((Gelfand.RationalStructure.inputMinus D.setup).phmT) z _ hy
  rw [LinearEquiv.apply_symm_apply] at key
  exact (Gelfand.RationalStructure.readVia D.setup D.toMinus).injective key

/-- **`E3` at the `(+)` run** — `φ^{(∞)}_+ − 𝟏` is nilpotent on `V(+)` (census clause
`RQ-5.05-C21`, first conjunct).  Here `W_-^τ = W_+` already holds, so this is S6's addendum read
through the bridge; the generalised engine is used uniformly for all three runs.
@census none (helper: `E3`) -/
theorem limPlusV_unipotent : IsNilpotent (D.limPlusV - 1) := by
  obtain ⟨hpP, hmP, nP, hnilP, hnP⟩ := Gelfand.RationalStructure.stab_prereq D.setup hℓ (Gelfand.RationalStructure.inputPlus D.setup) (by simp)
  obtain ⟨eP, hconstP, hlimP, -, -, -, -⟩ := Gelfand.RationalStructure.stab_limit_spec (Gelfand.RationalStructure.inputPlus D.setup) hpP hmP hnilP hnP
  have hup : ∃ mp, IsNilpotent mp ∧ asEndVia D.ePlus ((Gelfand.RationalStructure.inputPlus D.setup).phpT) = 1 + mp :=
    ⟨0, IsNilpotent.zero, by rw [D.ePlus_phpT, add_zero]⟩
  have huq : ∃ mq, IsNilpotent mq ∧
      asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.ePlus ((Gelfand.RationalStructure.inputPlus D.setup).phmT) = 1 + mq := by
    refine ⟨nP, hnilP, ?_⟩
    calc asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.ePlus ((Gelfand.RationalStructure.inputPlus D.setup).phmT)
        = asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.ePlus ((Gelfand.RationalStructure.inputPlus D.setup).phmT)
            * asEndVia D.ePlus ((Gelfand.RationalStructure.inputPlus D.setup).phpT) := by rw [D.ePlus_phpT, mul_one]
      _ = (twistConj Gelfand.RationalStructure.galConj_mul_self ((Gelfand.RationalStructure.inputPlus D.setup).phmT)).comp
            ((Gelfand.RationalStructure.inputPlus D.setup).phpT) :=
          asEndConjVia_comp_asEndVia Gelfand.RationalStructure.galConj_mul_self D.ePlus _ _
      _ = 1 + nP := hnP
  have hcomm : Commute (asEndVia D.ePlus ((Gelfand.RationalStructure.inputPlus D.setup).phpT))
      (asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.ePlus ((Gelfand.RationalStructure.inputPlus D.setup).phmT)) := by
    rw [D.ePlus_phpT]; exact Commute.one_left _
  obtain ⟨-, ⟨mp, hmp, hP⟩, -⟩ := stabilizationSeq_addendum_via two_ne_zero Gelfand.RationalStructure.galConj_mul_self
    D.ePlus _ _ hcomm hup huq eP
  have hPlim : asEndVia D.ePlus ((Gelfand.RationalStructure.inputPlus D.setup).limT.1) = 1 + mp := by
    rw [hlimP]; exact hP
  have hval : D.limPlusV = 1 + Gelfand.RationalStructure.endConjOf D.thPlus.symm mp := by
    refine LinearMap.ext fun x => ?_
    have hmem : (Gelfand.RationalStructure.inputPlus D.setup).limPlus ((D.toPlus.symm x :
        D.setup.weight.comp ((ℓ : ℤ) + 1)) : D.carrier)
        ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := by
      have h := (Gelfand.RationalStructure.inputPlus D.setup).limPlus_mem ((D.toPlus.symm x :
        D.setup.weight.comp ((ℓ : ℤ) + 1)) : D.carrier)
      rwa [show -(Gelfand.RationalStructure.inputPlus D.setup).idxMinus = (ℓ : ℤ) + 1 by simp [Gelfand.RationalStructure.inputPlus]] at h
    have key := Gelfand.RationalStructure.toEnd_read D.setup (neg_neg _) D.toPlus D.toPlus
      ((Gelfand.RationalStructure.inputPlus D.setup).limT.1) x ⟨_, hmem⟩ rfl
    rw [show D.limPlusV x = D.toPlus ⟨_, hmem⟩ from rfl, key]
    show D.thPlus (asEndVia D.ePlus ((Gelfand.RationalStructure.inputPlus D.setup).limT.1) (D.thPlus.symm x)) = _
    rw [hPlim]
    show D.thPlus (D.thPlus.symm x + mp (D.thPlus.symm x)) = x + _
    rw [map_add, D.thPlus.apply_symm_apply]
    simp
  rw [hval, add_sub_cancel_left]
  exact Gelfand.RationalStructure.isNilpotent_of_conj D.thPlus (fun _ => by simp) hmp

/-- **`E3` at the `(−)` run** — `φ^{(∞)}_- − 𝟏` is nilpotent on `V(−)` (census clause
`RQ-5.05-C21`, second conjunct).  @census none (helper: `E3`) -/
theorem limMinusV_unipotent : IsNilpotent (D.limMinusV - 1) := by
  obtain ⟨hpM, hmM, nM, hnilM, hnM⟩ := Gelfand.RationalStructure.stab_prereq D.setup hℓ (Gelfand.RationalStructure.inputMinus D.setup) (by simp)
  obtain ⟨eM, hconstM, hlimM, -, -, -, -⟩ :=
    Gelfand.RationalStructure.stab_limit_spec (Gelfand.RationalStructure.inputMinus D.setup) hpM hmM hnilM hnM
  have hup : ∃ mp, IsNilpotent mp ∧ asEndVia D.eMinus ((Gelfand.RationalStructure.inputMinus D.setup).phpT) = 1 + mp := by
    refine ⟨nM, hnilM, ?_⟩
    calc asEndVia D.eMinus ((Gelfand.RationalStructure.inputMinus D.setup).phpT)
        = asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.eMinus ((Gelfand.RationalStructure.inputMinus D.setup).phmT)
            * asEndVia D.eMinus ((Gelfand.RationalStructure.inputMinus D.setup).phpT) := by rw [D.eMinus_phmT, one_mul]
      _ = (twistConj Gelfand.RationalStructure.galConj_mul_self ((Gelfand.RationalStructure.inputMinus D.setup).phmT)).comp
            ((Gelfand.RationalStructure.inputMinus D.setup).phpT) :=
          asEndConjVia_comp_asEndVia Gelfand.RationalStructure.galConj_mul_self D.eMinus _ _
      _ = 1 + nM := hnM
  have huq : ∃ mq, IsNilpotent mq ∧
      asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.eMinus ((Gelfand.RationalStructure.inputMinus D.setup).phmT) = 1 + mq :=
    ⟨0, IsNilpotent.zero, by rw [D.eMinus_phmT, add_zero]⟩
  have hcomm : Commute (asEndVia D.eMinus ((Gelfand.RationalStructure.inputMinus D.setup).phpT))
      (asEndConjVia Gelfand.RationalStructure.galConj_mul_self D.eMinus ((Gelfand.RationalStructure.inputMinus D.setup).phmT)) := by
    rw [D.eMinus_phmT]; exact Commute.one_right _
  obtain ⟨-, ⟨mp, hmp, hP⟩, -⟩ := stabilizationSeq_addendum_via two_ne_zero Gelfand.RationalStructure.galConj_mul_self
    D.eMinus _ _ hcomm hup huq eM
  have hPlim : asEndVia D.eMinus ((Gelfand.RationalStructure.inputMinus D.setup).limT.1) = 1 + mp := by
    rw [hlimM]; exact hP
  have hval : D.limMinusV = 1 + Gelfand.RationalStructure.endConjOf D.thMinus.symm mp := by
    refine LinearMap.ext fun x => ?_
    have hmem : (Gelfand.RationalStructure.inputMinus D.setup).limPlus ((D.toMinus.symm x :
        D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier)
        ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) :=
      (Gelfand.RationalStructure.inputMinus D.setup).limPlus_mem ((D.toMinus.symm x :
        D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier)
    have key := Gelfand.RationalStructure.toEnd_read D.setup rfl D.toMinus D.toMinus
      ((Gelfand.RationalStructure.inputMinus D.setup).limT.1) x ⟨_, hmem⟩ rfl
    rw [show D.limMinusV x = D.toMinus ⟨_, hmem⟩ from rfl, key]
    show D.thMinus (asEndVia D.eMinus ((Gelfand.RationalStructure.inputMinus D.setup).limT.1) (D.thMinus.symm x)) = _
    rw [hPlim]
    show D.thMinus (D.thMinus.symm x + mp (D.thMinus.symm x)) = x + _
    rw [map_add, D.thMinus.apply_symm_apply]
    simp
  rw [hval, add_sub_cancel_left]
  exact Gelfand.RationalStructure.isNilpotent_of_conj D.thMinus (fun _ => by simp) hmp

/-- **`RQ-5.05-C18`, third conjunct** — `φ^{(∞),c}_⋆ = φ^{(∞)}_⋆`.  Immediate from
`limStarV_eq_one`: the identity is `c`-invariant.  @census none (helper) -/
theorem limStarV_conj (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Vphi hcard V 1 (D.limStarV ((Vphi hcard V 1).symm x)) = D.limStarV x := by
  rw [D.limStarV_eq_one]
  show Vphi hcard V 1 ((Vphi hcard V 1).symm x) = x
  exact (Vphi hcard V 1).apply_symm_apply x

/-- **`RQ-5.05-C19`** (`eq:phistaridentity`) — `(φ^{(∞)}_⋆)² = 𝟏`, `φ^{(∞)}_⋆ − 𝟏` nilpotent,
`φ^{(∞)}_⋆ = 𝟏`.  @census none (helper) -/
theorem essSurj_C19 :
    D.limStarV * D.limStarV = 1 ∧ IsNilpotent (D.limStarV - 1) ∧ D.limStarV = 1 := by
  refine ⟨by rw [D.limStarV_eq_one, one_mul], ?_, D.limStarV_eq_one⟩
  rw [D.limStarV_eq_one, sub_self]
  exact IsNilpotent.zero

/-- **`RQ-5.05-C20`** (`eq:starsquarerootsinverses`) — `(φ^{(∞)}_⋆)^{1/2} = 𝟏`, and the rational
structure `𝔼_ℚ(M)` induces on `V(⋆)` is the given `φ_⋆`.  @census none (helper) -/
theorem essSurj_C20 :
    Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limStarV = 1 ∧
      ∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1, D.phiV 1 x = Vphi hcard V 1 x := by
  have h2 : (2 : Dq.carrier) ≠ 0 := two_ne_zero_of_base (K := E) two_ne_zero
  refine ⟨?_, fun x => ?_⟩
  · rw [D.limStarV_eq_one]
    exact (Unipotent.sqrt_unique h2 1 1 0 IsNilpotent.zero (add_zero 1).symm (one_pow 2)).symm
  · have hmem : (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus ((D.toStarLo.symm x :
        D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier)
        ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) := by
      have h := (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus_mem ((D.toStarLo.symm x :
        D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier)
      rwa [show -(Gelfand.RationalStructure.inputStar D.setup hℓ).idxMinus = (ℓ : ℤ) - 1 by simp [Gelfand.RationalStructure.inputStar]] at h
    have hlim : (⟨_, hmem⟩ : D.setup.weight.comp ((ℓ : ℤ) - 1)) = D.toStarHi.symm x := by
      refine D.toStarHi.injective ?_
      rw [LinearEquiv.apply_symm_apply]
      exact (DFunLike.congr_fun D.limStarV_eq_one x : D.limStarV x = x)
    have hconj := D.conj_star ((ℓ : ℤ) - 1) (by omega) le_rfl (by omega)
      ((D.toStarHi.symm x : D.setup.weight.comp ((ℓ : ℤ) - 1)) : D.carrier) (D.toStarHi.symm x).2
    show D.toStarLo ⟨D.setup.conj ((Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus _), _⟩ = _
    refine Eq.trans (congrArg D.toStarLo (Subtype.ext ?_)) (D.toStarLo.apply_symm_apply _)
    show D.setup.conj ((Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus _)
        = ((D.toStarLo.symm (Vphi hcard V 1 x) : D.setup.weight.comp (-((ℓ : ℤ) - 1)))
            : D.carrier)
    rw [show (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus ((D.toStarLo.symm x :
        D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier)
      = ((D.toStarHi.symm x : D.setup.weight.comp ((ℓ : ℤ) - 1)) : D.carrier) from
      congrArg Subtype.val hlim, hconj]
    congr 2
    exact congrArg (fun y => Vphi hcard V 1 y) (D.toStarHi.apply_symm_apply x)

/-- **`RQ-5.05-C21`** — `φ^{(∞)}_± − 𝟏` nilpotent, and the unipotent square roots
`(φ^{(∞)}_±)^{1/2}` exist with the properties of `prop:unipotentsquareroots`.
@census none (helper) -/
theorem essSurj_C21 :
    IsNilpotent (D.limPlusV - 1) ∧ IsNilpotent (D.limMinusV - 1) ∧
      (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV) ^ 2 = D.limPlusV ∧
      IsNilpotent (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV - 1) ∧
      (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV) ^ 2 = D.limMinusV ∧
      IsNilpotent (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV - 1) := by
  have h2 : (2 : Dq.carrier) ≠ 0 := two_ne_zero_of_base (K := E) two_ne_zero
  obtain ⟨-, hnP, hsqP⟩ := Unipotent.sqrt_spec h2 D.limPlusV (D.limPlusV - 1)
    D.limPlusV_unipotent (by abel)
  obtain ⟨-, hnM, hsqM⟩ := Unipotent.sqrt_spec h2 D.limMinusV (D.limMinusV - 1)
    D.limMinusV_unipotent (by abel)
  exact ⟨D.limPlusV_unipotent, D.limMinusV_unipotent, hsqP, hnP, hsqM, hnM⟩

/-- **`eq:limitdiagram`'s `a₋` square, read on `V(•)`** — `X⋆ ∘ φ_{a₋} = φ_{a₋} ∘ φ^{(∞)}_-`.

The compiled probe of finding `F-S8-G4-1` / author item `AN-42`
(`stages/S8/DESIGN-NOTES.md` §14), and — since the author's Option-B ruling of 2026-09-11 — the
identity the amended source's own `a₋` square states.  `eq:limitdiagram`'s bottom row has
`Y⋆^{-1}X` where its top row has `X`, because its two middle objects are `M_{-(ℓ-1)}` and
`M_{ℓ-1}`; read on `V(•)` that `Y⋆^{-1}` is the `X⋆` below.  Until that ruling
`eq:limitsquarerootdiagram0`/`1` put the SAME row top and bottom and `𝟏_{V(⋆)}` on the middle
vertical, dropping exactly this `X⋆` — the same conflation of `M_{∓(ℓ-1)}` that `AN-41` booked at
the now-retired `C25`.

@census none (helper; the `F-S8-G4-1` probe) -/
theorem limitDiag_edgeAm (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) :
    D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (D.limMinusV x) := by
  -- memberships
  have hXmem : ∀ (w : D.carrier), w ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) →
      D.setup.weight.X w ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) := by
    intro w hw
    rw [D.X_bdry_minus w hw]
    exact Submodule.coe_mem _
  have hAmem : ∀ u : D.carrier,
      (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) := by
    intro u
    have h := (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus_mem u
    rwa [show -(Gelfand.RationalStructure.inputStar D.setup hℓ).idxMinus = (ℓ : ℤ) - 1 by simp [Gelfand.RationalStructure.inputStar]] at h
  -- readings
  have hXread : ∀ (w : D.carrier) (hw : w ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1))),
      D.toStarLo ⟨D.setup.weight.X w, hXmem w hw⟩ = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (D.toMinus ⟨w, hw⟩) :=
    fun w hw => Eq.trans (congrArg D.toStarLo (Subtype.ext (D.X_bdry_minus w hw)))
      (D.toStarLo.apply_symm_apply _)
  have hlimStar : ∀ (u : D.carrier) (hu : u ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1))),
      D.toStarHi ⟨(Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u, hAmem u⟩
        = D.limStarV (D.toStarLo ⟨u, hu⟩) := by
    intro u hu
    show _ = D.toStarHi _
    refine congrArg D.toStarHi (Subtype.ext ?_)
    show (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u
        = (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus
          ((D.toStarLo.symm (D.toStarLo ⟨u, hu⟩) : D.setup.weight.comp (-((ℓ : ℤ) - 1)))
            : D.carrier)
    rw [LinearEquiv.symm_apply_apply]
  have hyStarV : ∀ (u : D.carrier) (hu : u ∈ D.setup.weight.comp ((ℓ : ℤ) - 1))
      (hy : Split.yStar D.setup.toQiSetup u ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1))),
      D.yStarV (D.toStarHi ⟨u, hu⟩) = D.toStarLo ⟨Split.yStar D.setup.toQiSetup u, hy⟩ := by
    intro u hu hy
    show D.toStarLo _ = _
    refine congrArg D.toStarLo (Subtype.ext ?_)
    show Split.yStar D.setup.toQiSetup
        ((D.toStarHi.symm (D.toStarHi ⟨u, hu⟩) : D.setup.weight.comp ((ℓ : ℤ) - 1)) : D.carrier)
          = _
    rw [LinearEquiv.symm_apply_apply]
  -- the square
  set v : D.carrier := ((D.toMinus.symm x : D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier)
    with hvdef
  have hvm : v ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) := (D.toMinus.symm x).2
  have hvx : D.toMinus ⟨v, hvm⟩ = x := D.toMinus.apply_symm_apply x
  have hNm : (Gelfand.RationalStructure.inputMinus D.setup).limPlus v ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) :=
    (Gelfand.RationalStructure.inputMinus D.setup).limPlus_mem v
  have hNx : D.toMinus ⟨(Gelfand.RationalStructure.inputMinus D.setup).limPlus v, hNm⟩ = D.limMinusV x := rfl
  obtain ⟨hsq1, -, -, -⟩ := Gelfand.RationalStructure.limit_diagram D.setup (D.setup.toQiSetup.starInverses hℓ) hℓ
  have hkey := hsq1 v hvm
  have hXv : D.setup.weight.X v ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) := hXmem v hvm
  have hXNv : D.setup.weight.X ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v)
      ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) := hXmem _ hNm
  have hYm : (D.setup.toQiSetup.starInverses hℓ).yStarInv
      (D.setup.weight.X ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v))
      ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) :=
    Split.StarInverses.yStarInv_mem (D.setup.toQiSetup.starInverses hℓ) hXNv
  have hZ : Split.yStar D.setup.toQiSetup ((D.setup.toQiSetup.starInverses hℓ).yStarInv
      (D.setup.weight.X ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v)))
      ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) :=
    Split.yStar_mem (Q := D.setup.toQiSetup) (by ring) hℓ hYm
  -- LHS
  have hL : D.toStarHi ⟨(Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus (D.setup.weight.X v), hAmem _⟩
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x := by
    rw [hlimStar _ hXv, hXread v hvm, hvx, D.limStarV_eq_one]
    rfl
  -- RHS
  have hRR : D.yStarV (D.toStarHi ⟨(D.setup.toQiSetup.starInverses hℓ).yStarInv
        (D.setup.weight.X ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v)), hYm⟩)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (D.limMinusV x) := by
    rw [hyStarV _ hYm hZ]
    rw [show (⟨Split.yStar D.setup.toQiSetup ((D.setup.toQiSetup.starInverses hℓ).yStarInv
        (D.setup.weight.X ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v))), hZ⟩ :
          D.setup.weight.comp (-((ℓ : ℤ) - 1)))
        = ⟨D.setup.weight.X ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v), hXNv⟩ from
      Subtype.ext (Split.yStar_yStarInv D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) _ hXNv),
      hXread _ hNm, hNx]
  -- combine
  have hsubtype : (⟨(Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus (D.setup.weight.X v), hAmem _⟩ :
      D.setup.weight.comp ((ℓ : ℤ) - 1))
      = ⟨(D.setup.toQiSetup.starInverses hℓ).yStarInv
          (D.setup.weight.X ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v)), hYm⟩ := Subtype.ext hkey
  rw [D.xStarV_eq_yStarV, ← hL, hsubtype, hRR]

/-- `φ^{(∞)}_+` read on `V(+)` from a component element.  @census none (helper) -/
theorem toPlus_limPlus (v : D.carrier) (hv : v ∈ D.setup.weight.comp ((ℓ : ℤ) + 1))
    (hw : (Gelfand.RationalStructure.inputPlus D.setup).limPlus v ∈ D.setup.weight.comp ((ℓ : ℤ) + 1)) :
    D.toPlus ⟨(Gelfand.RationalStructure.inputPlus D.setup).limPlus v, hw⟩ = D.limPlusV (D.toPlus ⟨v, hv⟩) := by
  show _ = D.toPlus _
  refine congrArg D.toPlus (Subtype.ext ?_)
  show (Gelfand.RationalStructure.inputPlus D.setup).limPlus v
      = (Gelfand.RationalStructure.inputPlus D.setup).limPlus
        ((D.toPlus.symm (D.toPlus ⟨v, hv⟩) : D.setup.weight.comp ((ℓ : ℤ) + 1)) : D.carrier)
  rw [LinearEquiv.symm_apply_apply]

/-- `φ^{(∞)}_-` read on `V(−)` from a component element.  @census none (helper) -/
theorem toMinus_limMinus (v : D.carrier) (hv : v ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)))
    (hw : (Gelfand.RationalStructure.inputMinus D.setup).limPlus v ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1))) :
    D.toMinus ⟨(Gelfand.RationalStructure.inputMinus D.setup).limPlus v, hw⟩ = D.limMinusV (D.toMinus ⟨v, hv⟩) := by
  show _ = D.toMinus _
  refine congrArg D.toMinus (Subtype.ext ?_)
  show (Gelfand.RationalStructure.inputMinus D.setup).limPlus v
      = (Gelfand.RationalStructure.inputMinus D.setup).limPlus
        ((D.toMinus.symm (D.toMinus ⟨v, hv⟩) : D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier)
  rw [LinearEquiv.symm_apply_apply]

/-- `c|_{M_{ℓ+1}} = φ_{+,c}` (the `conj_plus` pin), read on `V(•)`.  @census none (helper) -/
theorem toMinus_conj (w : D.carrier) (hw : w ∈ D.setup.weight.comp ((ℓ : ℤ) + 1))
    (hc : D.setup.conj w ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1))) :
    D.toMinus ⟨D.setup.conj w, hc⟩ = Vphi hcard V 2 (D.toPlus ⟨w, hw⟩) :=
  Eq.trans (congrArg D.toMinus
      (Subtype.ext (D.conj_plus ((ℓ : ℤ) + 1) le_rfl (by omega) w hw)))
    (D.toMinus.apply_symm_apply _)

/-- `c|_{M_{-(ℓ+1)}} = φ_{-,c}`, read on `V(•)`; the `conj_minus` pin through the involution.
@census none (helper) -/
theorem toPlus_conj (u : D.carrier) (hu : u ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)))
    (hc : D.setup.conj u ∈ D.setup.weight.comp ((ℓ : ℤ) + 1)) :
    D.toPlus ⟨D.setup.conj u, hc⟩ = Vphi hcard V 0 (D.toMinus ⟨u, hu⟩) := by
  have hcc : D.setup.conj (D.setup.conj u) = u := Gelfand.RationalStructure.conj_conj D.setup u
  have h := D.toMinus_conj (D.setup.conj u) hc (by rw [hcc]; exact hu)
  have h2 : D.toMinus ⟨u, hu⟩ = Vphi hcard V 2 (D.toPlus ⟨D.setup.conj u, hc⟩) := by
    rw [← h]
    exact congrArg D.toMinus (Subtype.ext hcc.symm)
  rw [h2, Vphi_swap_plus]

/-- **`eq:conjugateinversepm` (`RQ-5.04-C9`) read on `V(±)`.**  @census none (helper)
@clauses   RQ2-5.12-S-O22 -/
theorem limPM_conj_inverse :
    (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2, Vphi hcard V 0 (D.limMinusV (Vphi hcard V 2 (D.limPlusV x))) = x) ∧
      (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0,
        Vphi hcard V 2 (D.limPlusV (Vphi hcard V 0 (D.limMinusV x))) = x) := by
  obtain ⟨-, -, ⟨hC9a, hC9b⟩, -, -⟩ := Gelfand.RationalStructure.varphi_spec D.setup hℓ
  have hPmem : ∀ v : D.carrier,
      (Gelfand.RationalStructure.inputPlus D.setup).limPlus v ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := by
    intro v
    have h := (Gelfand.RationalStructure.inputPlus D.setup).limPlus_mem v
    rwa [show -(Gelfand.RationalStructure.inputPlus D.setup).idxMinus = (ℓ : ℤ) + 1 by simp [Gelfand.RationalStructure.inputPlus]] at h
  have hMmem : ∀ v : D.carrier,
      (Gelfand.RationalStructure.inputMinus D.setup).limPlus v ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) :=
    fun v => (Gelfand.RationalStructure.inputMinus D.setup).limPlus_mem v
  constructor
  · intro x
    set v : D.carrier := ((D.toPlus.symm x : D.setup.weight.comp ((ℓ : ℤ) + 1)) : D.carrier)
      with hvdef
    have hv : v ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := (D.toPlus.symm x).2
    have hvx : D.toPlus ⟨v, hv⟩ = x := D.toPlus.apply_symm_apply x
    have hcP : D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus v)
        ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) := D.setup.conj_comp _ _ (hPmem v)
    have hcM : D.setup.conj ((Gelfand.RationalStructure.inputMinus D.setup).limPlus
        (D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus v)))
        ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := by
      have h := D.setup.conj_comp _ _ (hMmem (D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus v)))
      rwa [neg_neg] at h
    have hfin : D.toPlus ⟨D.setup.conj ((Gelfand.RationalStructure.inputMinus D.setup).limPlus
        (D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus v))), hcM⟩ = x := by
      rw [show (⟨D.setup.conj ((Gelfand.RationalStructure.inputMinus D.setup).limPlus
          (D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus v))), hcM⟩ :
            D.setup.weight.comp ((ℓ : ℤ) + 1)) = ⟨v, hv⟩ from
        Subtype.ext (hC9a v hv)]
      exact hvx
    have hchain : D.toPlus ⟨D.setup.conj ((Gelfand.RationalStructure.inputMinus D.setup).limPlus
        (D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus v))), hcM⟩
        = Vphi hcard V 0 (D.limMinusV (Vphi hcard V 2 (D.limPlusV x))) := by
      rw [D.toPlus_conj _ (hMmem _) hcM, D.toMinus_limMinus _ hcP (hMmem _),
        D.toMinus_conj _ (hPmem v) hcP, D.toPlus_limPlus v hv (hPmem v), hvx]
    exact hchain.symm.trans hfin
  · intro x
    set v : D.carrier := ((D.toMinus.symm x : D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier)
      with hvdef
    have hv : v ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) := (D.toMinus.symm x).2
    have hvx : D.toMinus ⟨v, hv⟩ = x := D.toMinus.apply_symm_apply x
    have hcM : D.setup.conj ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v)
        ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := by
      have h := D.setup.conj_comp _ _ (hMmem v)
      rwa [neg_neg] at h
    have hcP : D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus
        (D.setup.conj ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v)))
        ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) :=
      D.setup.conj_comp _ _ (hPmem _)
    have hfin : D.toMinus ⟨D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus
        (D.setup.conj ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v))), hcP⟩ = x := by
      rw [show (⟨D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus
          (D.setup.conj ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v))), hcP⟩ :
            D.setup.weight.comp (-((ℓ : ℤ) + 1))) = ⟨v, hv⟩ from
        Subtype.ext (hC9b v hv)]
      exact hvx
    have hchain : D.toMinus ⟨D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus
        (D.setup.conj ((Gelfand.RationalStructure.inputMinus D.setup).limPlus v))), hcP⟩
        = Vphi hcard V 2 (D.limPlusV (Vphi hcard V 0 (D.limMinusV x))) := by
      rw [D.toMinus_conj _ (hPmem _) hcP, D.toPlus_limPlus _ hcM (hPmem _),
        D.toPlus_conj _ (hMmem v) hcM, D.toMinus_limMinus v hv (hMmem v), hvx]
    exact hchain.symm.trans hfin

/-- The `c`-conjugate of `φ^{(∞)}_+` is `(φ^{(∞)}_-)^{-1}` — `eq:conjugateinversepm` read in
`End(V(−))`.  @census none (helper) -/
theorem cjPlus_limPlusV : cjPlus hcard V D.limPlusV = Ring.inverse D.limMinusV := by
  obtain ⟨hc1, hc2⟩ := D.limPM_conj_inverse
  have hL : D.limMinusV * cjPlus hcard V D.limPlusV = 1 := by
    refine LinearMap.ext fun y => ?_
    show D.limMinusV (cjPlus hcard V D.limPlusV y) = y
    rw [cjPlus_apply]
    have h' := congrArg (fun z => Vphi hcard V 2 z) (hc1 (Vphi hcard V 0 y))
    simp only [Vphi_swap_minus] at h'
    exact h'
  have hR : cjPlus hcard V D.limPlusV * D.limMinusV = 1 := by
    refine LinearMap.ext fun y => ?_
    show cjPlus hcard V D.limPlusV (D.limMinusV y) = y
    rw [cjPlus_apply]
    exact hc2 y
  exact (Ring.inverse_unit (⟨D.limMinusV, cjPlus hcard V D.limPlusV, hL, hR⟩ :
    (Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0))ˣ)).symm

/-- The `c`-conjugate of `φ^{(∞)}_-` is `(φ^{(∞)}_+)^{-1}`.  @census none (helper) -/
theorem cjMinus_limMinusV : cjMinus hcard V D.limMinusV = Ring.inverse D.limPlusV := by
  obtain ⟨hc1, hc2⟩ := D.limPM_conj_inverse
  have hL : D.limPlusV * cjMinus hcard V D.limMinusV = 1 := by
    refine LinearMap.ext fun y => ?_
    show D.limPlusV (cjMinus hcard V D.limMinusV y) = y
    rw [cjMinus_apply]
    have h' := congrArg (fun z => Vphi hcard V 0 z) (hc2 (Vphi hcard V 2 y))
    simp only [Vphi_swap_plus] at h'
    exact h'
  have hR : cjMinus hcard V D.limMinusV * D.limPlusV = 1 := by
    refine LinearMap.ext fun y => ?_
    show cjMinus hcard V D.limMinusV (D.limPlusV y) = y
    rw [cjMinus_apply]
    exact hc1 y
  exact (Ring.inverse_unit (⟨D.limPlusV, cjMinus hcard V D.limMinusV, hL, hR⟩ :
    (Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2))ˣ)).symm

/-- **`RQ-5.05-C22`** (`eq:pmsquarerootsinverses`) —
`φ_± ∘ (φ^{(∞)}_±)^{1/2} = ((φ^{(∞)}_∓)^{1/2})^{-1} ∘ φ_±`, **which is what the display prints**
since the author's ruling of 2026-09-11 on `AN-35`…`AN-42` (`AN-40`: the trailing `φ_±` became
`φ_∓`).  Until then the display was ill-typed and this was the index-corrected reading `AN-40`
recorded — the gloss the source printed below it.

Route: the `c`-conjugate of `(φ^{(∞)}_+)^{1/2}` is a **unipotent square root** of the `c`-conjugate
of `φ^{(∞)}_+`, which is `(φ^{(∞)}_-)^{-1}` (`cjPlus_limPlusV`, i.e. `eq:conjugateinversepm`); by
`sqrt_unique` it therefore **is** `((φ^{(∞)}_-)^{-1})^{1/2}`, and by `sqrt_inv` that is
`((φ^{(∞)}_-)^{1/2})^{-1}`.  @census none (helper) -/
theorem essSurj_C22 :
    (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2,
        Vphi hcard V 2 (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV x)
          = linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV)
              (Vphi hcard V 2 x)) ∧
      (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0,
        Vphi hcard V 0 (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV x)
          = linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV)
              (Vphi hcard V 0 x)) := by
  have h2 : (2 : Dq.carrier) ≠ 0 := two_ne_zero_of_base (K := E) two_ne_zero
  obtain ⟨-, hnP, hsqP⟩ := Unipotent.sqrt_spec h2 D.limPlusV (D.limPlusV - 1)
    D.limPlusV_unipotent (by abel)
  obtain ⟨-, hnM, hsqM⟩ := Unipotent.sqrt_spec h2 D.limMinusV (D.limMinusV - 1)
    D.limMinusV_unipotent (by abel)
  have hTP : cjPlus hcard V (Unipotent.sqrt h2 D.limPlusV)
      = Ring.inverse (Unipotent.sqrt h2 D.limMinusV) := by
    have hTsq : (cjPlus hcard V (Unipotent.sqrt h2 D.limPlusV)) ^ 2
        = Ring.inverse D.limMinusV := by
      rw [← cjPlus_pow, hsqP, D.cjPlus_limPlusV]
    have hTnil : IsNilpotent (cjPlus hcard V (Unipotent.sqrt h2 D.limPlusV) - 1) := by
      rw [← cjPlus_one hcard V, ← cjPlus_sub]
      exact cjPlus_isNilpotent hcard V hnP
    have h1 := Unipotent.sqrt_unique h2 (Ring.inverse D.limMinusV)
      (cjPlus hcard V (Unipotent.sqrt h2 D.limPlusV))
      (cjPlus hcard V (Unipotent.sqrt h2 D.limPlusV) - 1) hTnil (by abel) hTsq
    have h3 := Unipotent.sqrt_inv h2 D.limMinusV (D.limMinusV - 1) D.limMinusV_unipotent (by abel)
    rw [h1, ← h3]
  have hTM : cjMinus hcard V (Unipotent.sqrt h2 D.limMinusV)
      = Ring.inverse (Unipotent.sqrt h2 D.limPlusV) := by
    have hTsq : (cjMinus hcard V (Unipotent.sqrt h2 D.limMinusV)) ^ 2
        = Ring.inverse D.limPlusV := by
      rw [← cjMinus_pow, hsqM, D.cjMinus_limMinusV]
    have hTnil : IsNilpotent (cjMinus hcard V (Unipotent.sqrt h2 D.limMinusV) - 1) := by
      rw [← cjMinus_one hcard V, ← cjMinus_sub]
      exact cjMinus_isNilpotent hcard V hnM
    have h1 := Unipotent.sqrt_unique h2 (Ring.inverse D.limPlusV)
      (cjMinus hcard V (Unipotent.sqrt h2 D.limMinusV))
      (cjMinus hcard V (Unipotent.sqrt h2 D.limMinusV) - 1) hTnil (by abel) hTsq
    have h3 := Unipotent.sqrt_inv h2 D.limPlusV (D.limPlusV - 1) D.limPlusV_unipotent (by abel)
    rw [h1, ← h3]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have hval : cjPlus hcard V (Unipotent.sqrt h2 D.limPlusV) (Vphi hcard V 2 x)
        = Vphi hcard V 2 (Unipotent.sqrt h2 D.limPlusV x) := by
      rw [cjPlus_apply, Vphi_swap_plus]
    rw [← hval, hTP, ring_inverse_eq_linInv]
  · have hval : cjMinus hcard V (Unipotent.sqrt h2 D.limMinusV) (Vphi hcard V 0 x)
        = Vphi hcard V 0 (Unipotent.sqrt h2 D.limMinusV x) := by
      rw [cjMinus_apply, Vphi_swap_minus]
    rw [← hval, hTM, ring_inverse_eq_linInv]

/-- `X⋆` is unipotent on `V(⋆)` (`RQ-5.05-C17`, second display, with `γ̃' = 1`).
@census none (helper) -/
theorem xStarV_unipotent : IsNilpotent (D.xStarV - 1) := by
  obtain ⟨n', hn', -, heq⟩ := Split.xStarAt_eq_one_add hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1
  rw [D.xStarV_eq, heq, add_sub_cancel_left]
  exact hn'

/-- **The square-root diagram's `a₋` square, as it actually is** — the middle vertical is
`(X⋆)^{1/2}`, **not** the `𝟏_{V(⋆)}` the source printed until 2026-09-11.  `sqrt_natural` applied
to `limitDiag_edgeAm`; the amended source's diagram prints exactly this square.
@census none (helper; the `F-S8-G4-1` probe) -/
theorem limitSqrtDiag_edgeAm (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) :
    Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV x)
      = Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.xStarV
          (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x) :=
  sqrt_natural (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV_unipotent
    D.xStarV_unipotent (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0) (fun y => (D.limitDiag_edgeAm y).symm) x

/-- **`eq:limitdiagram`'s `b₊` square, read on `V(•)`** — `φ^{(∞)}_+ ∘ φ_{b₊} ∘ X⋆ = φ_{b₊}`.

Together with `limitDiag_edgeAm` this shows that **no single endomorphism of `V(⋆)` can be the
middle vertical** of a square-root diagram on `V(•)`: the `a₋` square forces `(X⋆)^{1/2}` and the
`b₊` square forces `(X⋆)^{-1/2}`.  The two agree only when `X⋆ = 𝟏`.  Part of the `F-S8-G4-1`
probe.  @census none (helper) -/
theorem limitDiag_edgeBp (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    D.limPlusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV x)) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 x := by
  have hXmem : ∀ (w : D.carrier), w ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) →
      D.setup.weight.X w ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := by
    intro w hw
    rw [D.X_bdry_plus w hw]
    exact Submodule.coe_mem _
  have hXread : ∀ (w : D.carrier) (hw : w ∈ D.setup.weight.comp ((ℓ : ℤ) - 1)),
      D.toPlus ⟨D.setup.weight.X w, hXmem w hw⟩ = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.toStarHi ⟨w, hw⟩) :=
    fun w hw => Eq.trans (congrArg D.toPlus (Subtype.ext (D.X_bdry_plus w hw)))
      (D.toPlus.apply_symm_apply _)
  have hAmem : ∀ u : D.carrier,
      (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) := by
    intro u
    have h := (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus_mem u
    rwa [show -(Gelfand.RationalStructure.inputStar D.setup hℓ).idxMinus = (ℓ : ℤ) - 1 by simp [Gelfand.RationalStructure.inputStar]] at h
  have hlimStar : ∀ (u : D.carrier) (hu : u ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1))),
      D.toStarHi ⟨(Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u, hAmem u⟩
        = D.limStarV (D.toStarLo ⟨u, hu⟩) := by
    intro u hu
    show _ = D.toStarHi _
    refine congrArg D.toStarHi (Subtype.ext ?_)
    show (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u
        = (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus
          ((D.toStarLo.symm (D.toStarLo ⟨u, hu⟩) : D.setup.weight.comp (-((ℓ : ℤ) - 1)))
            : D.carrier)
    rw [LinearEquiv.symm_apply_apply]
  set v : D.carrier := ((D.toStarLo.symm x : D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier)
    with hvdef
  have hvm : v ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) := (D.toStarLo.symm x).2
  have hvx : D.toStarLo ⟨v, hvm⟩ = x := D.toStarLo.apply_symm_apply x
  have hsm : Split.xStar D.setup.toQiSetup v ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) :=
    Split.xStar_mem (Q := D.setup.toQiSetup) (by ring) hℓ hvm
  have hsx : D.toStarHi ⟨Split.xStar D.setup.toQiSetup v, hsm⟩ = D.xStarV x := rfl
  obtain ⟨-, hsq2, -, -⟩ := Gelfand.RationalStructure.limit_diagram D.setup (D.setup.toQiSetup.starInverses hℓ) hℓ
  have hkey := hsq2 v hvm
  have hPmem : ∀ u : D.carrier,
      (Gelfand.RationalStructure.inputPlus D.setup).limPlus u ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := by
    intro u
    have h := (Gelfand.RationalStructure.inputPlus D.setup).limPlus_mem u
    rwa [show -(Gelfand.RationalStructure.inputPlus D.setup).idxMinus = (ℓ : ℤ) + 1 by simp [Gelfand.RationalStructure.inputPlus]] at h
  have hL : D.toPlus ⟨(Gelfand.RationalStructure.inputPlus D.setup).limPlus
      (D.setup.weight.X (Split.xStar D.setup.toQiSetup v)), hPmem _⟩
      = D.limPlusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV x)) := by
    rw [D.toPlus_limPlus _ (hXmem _ hsm) (hPmem _), hXread _ hsm, hsx]
  have hR : D.toPlus ⟨D.setup.weight.X ((Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus v),
      hXmem _ (hAmem v)⟩ = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 x := by
    rw [hXread _ (hAmem v), hlimStar v hvm, hvx, D.limStarV_eq_one]
    rfl
  rw [← hL, ← hR]
  exact congrArg D.toPlus (Subtype.ext hkey)

/-- **`F-S8-G4-1`, the refutation of what the source printed until 2026-09-11** (`AN-42`;
`stages/S8/DESIGN-NOTES.md` §14).  Kept, dated and past-tensed: the hypothesis `h` is census clause
`RQ-5.05-C23`'s first conjunct **as the source printed it before the author's Option-B ruling of
2026-09-11** — `eq:limitsquarerootdiagram0`'s `a₋` square with `𝟏_{V(⋆)}` on the middle vertical,
i.e. `φ_{a₋} ∘ (φ^{(∞)}_-)^{1/2} = φ_{a₋}` — and the conclusion is **`AN-41`'s false identity**
`X⋆ ∘ φ_{a₋} = φ_{a₋}`, which fails whenever `ñ⋆ ≠ 0` (`RQ-5.05-C17`: `X⋆ = 𝟏 + ñ⋆`).  So the
then-printed `C23` was false, by exactly the conflation of `M_{-(ℓ-1)}` with `M_{ℓ-1}` that `AN-41`
booked at the now-retired `C25`; and so was `C24`, whose first block repeated the same four
equations.  The amended source prints the `a₋` square with `t = X⋆^{1/2}` on the middle vertical
(`essSurj_C23`), so this theorem is now a record, not a live divergence.

@census none (helper; the `F-S8-G4-1` probe) -/
theorem C23_printed_forces_AN41
    (h : ∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0, Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0
        (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV x)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) :
    D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x := by
  have h2 : (2 : Dq.carrier) ≠ 0 := two_ne_zero_of_base (K := E) two_ne_zero
  have hs : ∀ y : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0,
      Unipotent.sqrt h2 D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 y) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 y := by
    intro y
    rw [← D.limitSqrtDiag_edgeAm y]
    exact h y
  obtain ⟨-, -, hsq⟩ := Unipotent.sqrt_spec h2 D.xStarV (D.xStarV - 1) D.xStarV_unipotent
    (by abel)
  calc D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x)
      = (Unipotent.sqrt h2 D.xStarV ^ 2) (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x) := by rw [hsq]
    _ = Unipotent.sqrt h2 D.xStarV (Unipotent.sqrt h2 D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x)) := by
        rw [sq, Module.End.mul_apply]
    _ = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x := by rw [hs x, hs x]

/-- **`F-S8-G4-1`, the refutation at the other end** — likewise a dated record of what the source
printed until 2026-09-11.  `C24`'s then-printed fourth edge equation —
`(φ^{(∞)}_+)^{1/2} ∘ φ_{b₊} = φ_{b₊}`, i.e. `eq:limitsquarerootdiagram1`'s `b₊` square with
`𝟏_{V(⋆)}` on the middle vertical — implies `φ_{b₊} ∘ X⋆ = φ_{b₊}`, the mirror of `AN-41`'s false
identity at the `+` end.  With `C23_printed_forces_AN41` this pinned the defect from both sides:
for a diagram whose two rows are ONE representation the `a₋` square wants `(X⋆)^{1/2}` on the
middle vertical and the `b₊` square wants `(X⋆)^{-1/2}`, so **no single endomorphism of `V(⋆)` was
the middle vertical** unless `X⋆ = 𝟏`.  The amended source's one diagram has two DIFFERENT rows —
`𝔼_{ℚ[√-1]}(M)` over `V` — which is exactly what lets the single `t = X⋆^{1/2}` serve all four
squares.  @census none (helper; the `F-S8-G4-1` probe) -/
theorem C24_printed_forces_trivial_xStar
    (h : ∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1, Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero)
        D.limPlusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 x) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 x := by
  have h2 : (2 : Dq.carrier) ≠ 0 := two_ne_zero_of_base (K := E) two_ne_zero
  obtain ⟨-, -, hsq⟩ := Unipotent.sqrt_spec h2 D.limPlusV (D.limPlusV - 1)
    D.limPlusV_unipotent (by abel)
  have hlim : ∀ y : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1, D.limPlusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 y) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 y := by
    intro y
    calc D.limPlusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 y)
        = (Unipotent.sqrt h2 D.limPlusV ^ 2) (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 y) := by rw [hsq]
      _ = Unipotent.sqrt h2 D.limPlusV (Unipotent.sqrt h2 D.limPlusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 y)) := by
          rw [sq, Module.End.mul_apply]
      _ = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 y := by rw [h y, h y]
  rw [← D.limitDiag_edgeBp x, hlim]


end EssSurjData

/-! #### `RQ-5.05-C23`/`C24` — from `R-S8-23` to the author's Option-B ruling of 2026-09-11

`F-S8-G4-1` / `AN-42` (DESIGN-NOTES §14.3, §14.9) measured that `eq:limitsquarerootdiagram0` and
`eq:limitsquarerootdiagram1` were **false as printed**: their middle vertical `𝟏_{V(⋆)}` was forced
to be `(X⋆)^{1/2}` by the two left-hand squares and `(X⋆)^{-1/2}` by the two right-hand ones.
Coordinator ruling **`R-S8-23`** (2026-09-04) directed that the two diagrams be rendered with
exactly that data — printed rows kept, no conjunct dropped — with the conjugation conclusion §5.3
consumes as a further named conjunct of `C24`.  **On 2026-09-11 the paper author ruled Option B
instead**: ONE diagram, top row `𝔼_{ℚ[√-1]}(M)`, bottom row `V`, middle vertical `X⋆^{1/2}`, and
the final `(𝟏_{V(+)}, X⋆, 𝟏_{V(−)})` sentence deleted.  `essSurj_C23`/`essSurj_C24` render that,
`essSurj_C25` was retired with the sentence, and the Option-A squares below
(`sqrtDiag0_edgeBp`/`sqrtDiag0_edgeAp`) are kept as true helper identities and as the record of
what `R-S8-23` had directed.

The four squares of `eq:limitdiagram`, read on `V(•)` through `D`'s identifications, are
`limitDiag_edgeAm`, `limitDiag_edgeBm`, `limitDiag_edgeBp`, `limitDiag_edgeAp`; each is an
intertwining relation between two unipotent operators, and `sqrt_natural` turns it into the
corresponding square of the square-root diagram. -/

/-- `f (f⁻¹ y) = y` for a unit endomorphism.  @census none (helper) -/
theorem end_inverse_apply {W : Type} [AddCommGroup W] [Module Dq.carrier W]
    {f : Module.End Dq.carrier W} (hf : IsUnit f) (y : W) :
    f (Ring.inverse f y) = y := by
  rw [← Module.End.mul_apply, Ring.mul_inverse_cancel f hf]
  rfl

/-- `f⁻¹ (f y) = y` for a unit endomorphism.  @census none (helper) -/
theorem inverse_end_apply {W : Type} [AddCommGroup W] [Module Dq.carrier W]
    {f : Module.End Dq.carrier W} (hf : IsUnit f) (y : W) :
    Ring.inverse f (f y) = y := by
  rw [← Module.End.mul_apply, Ring.inverse_mul_cancel f hf]
  rfl

/-- `φ ∘ (φ^{1/2})^{-1} = φ^{1/2}` for a unipotent `φ`.  @census none (helper) -/
theorem unipotent_sqrt_inv_cancel {W : Type} [AddCommGroup W] [Module Dq.carrier W]
    (h2 : (2 : Dq.carrier) ≠ 0) {φ : Module.End Dq.carrier W} (hφ : IsNilpotent (φ - 1))
    (y : W) :
    φ (Ring.inverse (Unipotent.sqrt h2 φ) y) = Unipotent.sqrt h2 φ y := by
  obtain ⟨hu, -, hsq⟩ := Unipotent.sqrt_spec h2 φ (φ - 1) hφ (by abel)
  have hpt : ∀ z, φ z = Unipotent.sqrt h2 φ (Unipotent.sqrt h2 φ z) := fun z => by
    rw [← Module.End.mul_apply, ← sq, hsq]
  rw [hpt (Ring.inverse (Unipotent.sqrt h2 φ) y), end_inverse_apply hu]

namespace EssSurjData

variable {V : Gelfand.RationalStructure.RepNilQ hcard} (D : EssSurjData hcard hℓ V)

/-- **`eq:limitdiagram`'s `b₋` square, read on `V(•)`** — `φ^{(∞)}_- ∘ φ_{b₋} = φ_{b₋} ∘ X⋆`.

The third conjunct of `DiagSq`, `N ∘ Y = Y ∘ Y⋆ ∘ A`, read through `toStarLo` on the source and
`toMinus` on the target, with `A = φ^{(∞)}_⋆ = 𝟏` (`limStarV_eq_one`) and `Y⋆ = X⋆`
(`xStarV_eq_yStarV`).  @census none (helper) -/
theorem limitDiag_edgeBm (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    D.limMinusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (D.xStarV x) := by
  have hYmem : ∀ (w : D.carrier), w ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) →
      D.setup.weight.Y w ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) := by
    intro w hw
    rw [D.Y_bdry_minus w hw]
    exact Submodule.coe_mem _
  have hYread : ∀ (w : D.carrier) (hw : w ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1))),
      D.toMinus ⟨D.setup.weight.Y w, hYmem w hw⟩ = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (D.toStarLo ⟨w, hw⟩) :=
    fun w hw => Eq.trans (congrArg D.toMinus (Subtype.ext (D.Y_bdry_minus w hw)))
      (D.toMinus.apply_symm_apply _)
  have hAmem : ∀ u : D.carrier,
      (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) := by
    intro u
    have h := (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus_mem u
    rwa [show -(Gelfand.RationalStructure.inputStar D.setup hℓ).idxMinus = (ℓ : ℤ) - 1 by simp [Gelfand.RationalStructure.inputStar]] at h
  have hlimStar : ∀ (u : D.carrier) (hu : u ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1))),
      D.toStarHi ⟨(Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u, hAmem u⟩
        = D.limStarV (D.toStarLo ⟨u, hu⟩) := by
    intro u hu
    show _ = D.toStarHi _
    refine congrArg D.toStarHi (Subtype.ext ?_)
    show (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u
        = (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus
          ((D.toStarLo.symm (D.toStarLo ⟨u, hu⟩) : D.setup.weight.comp (-((ℓ : ℤ) - 1)))
            : D.carrier)
    rw [LinearEquiv.symm_apply_apply]
  have hyStarV : ∀ (u : D.carrier) (hu : u ∈ D.setup.weight.comp ((ℓ : ℤ) - 1))
      (hy : Split.yStar D.setup.toQiSetup u ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1))),
      D.yStarV (D.toStarHi ⟨u, hu⟩) = D.toStarLo ⟨Split.yStar D.setup.toQiSetup u, hy⟩ := by
    intro u hu hy
    show D.toStarLo _ = _
    refine congrArg D.toStarLo (Subtype.ext ?_)
    show Split.yStar D.setup.toQiSetup
        ((D.toStarHi.symm (D.toStarHi ⟨u, hu⟩) : D.setup.weight.comp ((ℓ : ℤ) - 1)) : D.carrier)
          = _
    rw [LinearEquiv.symm_apply_apply]
  set v : D.carrier := ((D.toStarLo.symm x : D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier)
  have hvm : v ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) := (D.toStarLo.symm x).2
  have hvx : D.toStarLo ⟨v, hvm⟩ = x := D.toStarLo.apply_symm_apply x
  have hNmem : ∀ u : D.carrier,
      (Gelfand.RationalStructure.inputMinus D.setup).limPlus u ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) :=
    fun u => (Gelfand.RationalStructure.inputMinus D.setup).limPlus_mem u
  have hz : Split.yStar D.setup.toQiSetup ((Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus v)
      ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) :=
    Split.yStar_mem (Q := D.setup.toQiSetup) (by ring) hℓ (hAmem v)
  obtain ⟨-, -, hsq3, -⟩ := Gelfand.RationalStructure.limit_diagram D.setup (D.setup.toQiSetup.starInverses hℓ) hℓ
  have hkey := hsq3 v hvm
  have hL : D.toMinus ⟨(Gelfand.RationalStructure.inputMinus D.setup).limPlus (D.setup.weight.Y v), hNmem _⟩
      = D.limMinusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 x) := by
    rw [D.toMinus_limMinus _ (hYmem v hvm) (hNmem _), hYread v hvm, hvx]
  have hR : D.toMinus ⟨D.setup.weight.Y (Split.yStar D.setup.toQiSetup
        ((Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus v)), hYmem _ hz⟩
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (D.xStarV x) := by
    rw [hYread _ hz, ← hyStarV _ (hAmem v) hz, hlimStar v hvm, hvx, D.limStarV_eq_one,
      D.xStarV_eq_yStarV]
    rfl
  rw [← hL, ← hR]
  exact congrArg D.toMinus (Subtype.ext hkey)

/-- **`eq:limitdiagram`'s `a₊` square, read on `V(•)`** — `X⋆ ∘ φ_{a₊} ∘ φ^{(∞)}_+ = φ_{a₊}`.

The fourth conjunct of `DiagSq`, `A ∘ X⋆^{-1} ∘ Y = Y ∘ P`, read through `toPlus` on the source and
`toStarHi` on the target, with `A = φ^{(∞)}_⋆ = 𝟏` (`limStarV_eq_one`).
@census none (helper) -/
theorem limitDiag_edgeAp (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :
    D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (D.limPlusV x)) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x := by
  have hYmem : ∀ (w : D.carrier), w ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) →
      D.setup.weight.Y w ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) := by
    intro w hw
    rw [D.Y_bdry_plus w hw]
    exact Submodule.coe_mem _
  have hYread : ∀ (w : D.carrier) (hw : w ∈ D.setup.weight.comp ((ℓ : ℤ) + 1)),
      D.toStarHi ⟨D.setup.weight.Y w, hYmem w hw⟩ = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (D.toPlus ⟨w, hw⟩) :=
    fun w hw => Eq.trans (congrArg D.toStarHi (Subtype.ext (D.Y_bdry_plus w hw)))
      (D.toStarHi.apply_symm_apply _)
  have hAmem : ∀ u : D.carrier,
      (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) := by
    intro u
    have h := (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus_mem u
    rwa [show -(Gelfand.RationalStructure.inputStar D.setup hℓ).idxMinus = (ℓ : ℤ) - 1 by simp [Gelfand.RationalStructure.inputStar]] at h
  have hlimStar : ∀ (u : D.carrier) (hu : u ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1))),
      D.toStarHi ⟨(Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u, hAmem u⟩
        = D.limStarV (D.toStarLo ⟨u, hu⟩) := by
    intro u hu
    show _ = D.toStarHi _
    refine congrArg D.toStarHi (Subtype.ext ?_)
    show (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus u
        = (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus
          ((D.toStarLo.symm (D.toStarLo ⟨u, hu⟩) : D.setup.weight.comp (-((ℓ : ℤ) - 1)))
            : D.carrier)
    rw [LinearEquiv.symm_apply_apply]
  have hxStarV : ∀ (u : D.carrier) (hu : u ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)))
      (hx : Split.xStar D.setup.toQiSetup u ∈ D.setup.weight.comp ((ℓ : ℤ) - 1)),
      D.xStarV (D.toStarLo ⟨u, hu⟩) = D.toStarHi ⟨Split.xStar D.setup.toQiSetup u, hx⟩ := by
    intro u hu hx
    show D.toStarHi _ = _
    refine congrArg D.toStarHi (Subtype.ext ?_)
    show Split.xStar D.setup.toQiSetup
        ((D.toStarLo.symm (D.toStarLo ⟨u, hu⟩) : D.setup.weight.comp (-((ℓ : ℤ) - 1)))
          : D.carrier) = _
    rw [LinearEquiv.symm_apply_apply]
  set v : D.carrier := ((D.toPlus.symm x : D.setup.weight.comp ((ℓ : ℤ) + 1)) : D.carrier)
  have hvm : v ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := (D.toPlus.symm x).2
  have hvx : D.toPlus ⟨v, hvm⟩ = x := D.toPlus.apply_symm_apply x
  have hYv : D.setup.weight.Y v ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) := hYmem v hvm
  have hzm : (D.setup.toQiSetup.starInverses hℓ).xStarInv (D.setup.weight.Y v)
      ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) :=
    Split.StarInverses.xStarInv_mem (D.setup.toQiSetup.starInverses hℓ) hYv
  have hPmem : ∀ u : D.carrier,
      (Gelfand.RationalStructure.inputPlus D.setup).limPlus u ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := by
    intro u
    have h := (Gelfand.RationalStructure.inputPlus D.setup).limPlus_mem u
    rwa [show -(Gelfand.RationalStructure.inputPlus D.setup).idxMinus = (ℓ : ℤ) + 1 by simp [Gelfand.RationalStructure.inputPlus]] at h
  have hxx : Split.xStar D.setup.toQiSetup
      ((D.setup.toQiSetup.starInverses hℓ).xStarInv (D.setup.weight.Y v))
      = D.setup.weight.Y v :=
    Split.xStar_xStarInv D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) _ hYv
  have hx' : Split.xStar D.setup.toQiSetup
      ((D.setup.toQiSetup.starInverses hℓ).xStarInv (D.setup.weight.Y v))
      ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) := by rw [hxx]; exact hYv
  obtain ⟨-, -, -, hsq4⟩ := Gelfand.RationalStructure.limit_diagram D.setup (D.setup.toQiSetup.starInverses hℓ) hℓ
  have hkey := hsq4 v hvm
  have hR : D.toStarHi ⟨D.setup.weight.Y ((Gelfand.RationalStructure.inputPlus D.setup).limPlus v), hYmem _ (hPmem v)⟩
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (D.limPlusV x) := by
    rw [hYread _ (hPmem v), D.toPlus_limPlus v hvm (hPmem v), hvx]
  have hL : D.xStarV (D.toStarLo ⟨(D.setup.toQiSetup.starInverses hℓ).xStarInv
        (D.setup.weight.Y v), hzm⟩) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x := by
    rw [hxStarV _ hzm hx',
      congrArg D.toStarHi (Subtype.ext hxx :
        (⟨_, hx'⟩ : D.setup.weight.comp ((ℓ : ℤ) - 1)) = ⟨D.setup.weight.Y v, hYv⟩),
      hYread v hvm, hvx]
  have hsub : (⟨D.setup.weight.Y ((Gelfand.RationalStructure.inputPlus D.setup).limPlus v), hYmem _ (hPmem v)⟩ :
      D.setup.weight.comp ((ℓ : ℤ) - 1))
      = ⟨(Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus
          ((D.setup.toQiSetup.starInverses hℓ).xStarInv (D.setup.weight.Y v)),
        hAmem ((D.setup.toQiSetup.starInverses hℓ).xStarInv (D.setup.weight.Y v))⟩ :=
    Subtype.ext hkey.symm
  calc D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (D.limPlusV x))
      = D.xStarV (D.toStarHi ⟨D.setup.weight.Y ((Gelfand.RationalStructure.inputPlus D.setup).limPlus v),
          hYmem _ (hPmem v)⟩) := by rw [hR]
    _ = D.xStarV (D.toStarHi ⟨(Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus
          ((D.setup.toQiSetup.starInverses hℓ).xStarInv (D.setup.weight.Y v)), hAmem _⟩) := by
        rw [hsub]
    _ = D.xStarV (D.toStarLo ⟨(D.setup.toQiSetup.starInverses hℓ).xStarInv
          (D.setup.weight.Y v), hzm⟩) := by rw [hlimStar _ hzm, D.limStarV_eq_one]; rfl
    _ = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x := hL


/-- `X⋆` is a unit on `V(⋆)` (`RQ-5.05-C17`).  @census none (helper) -/
theorem xStarV_isUnit : IsUnit D.xStarV := isUnit_of_sub_one_isNilpotent D.xStarV_unipotent

/-- `φ^{(∞)}_+` is a unit on `V(+)`.  @census none (helper) -/
theorem limPlusV_isUnit : IsUnit D.limPlusV := isUnit_of_sub_one_isNilpotent D.limPlusV_unipotent

/-- `φ^{(∞)}_-` is a unit on `V(−)`.  @census none (helper) -/
theorem limMinusV_isUnit : IsUnit D.limMinusV :=
  isUnit_of_sub_one_isNilpotent D.limMinusV_unipotent

/-- `eq:limitdiagram`'s `b₊` square as an intertwining relation for `φ_{b₊}`:
`φ_{b₊} ∘ X⋆ = (φ^{(∞)}_+)^{-1} ∘ φ_{b₊}`.  @census none (helper) -/
theorem limitDiag_edgeBp' (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV x) = Ring.inverse D.limPlusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 x) := by
  rw [← D.limitDiag_edgeBp x, inverse_end_apply D.limPlusV_isUnit]

/-- `eq:limitdiagram`'s `a₊` square as an intertwining relation for `φ_{a₊}`:
`φ_{a₊} ∘ φ^{(∞)}_+ = (X⋆)^{-1} ∘ φ_{a₊}`.  @census none (helper) -/
theorem limitDiag_edgeAp' (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :
    Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (D.limPlusV x) = Ring.inverse D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x) := by
  rw [← D.limitDiag_edgeAp x, inverse_end_apply D.xStarV_isUnit]

/-- `(X⋆)^{1/2}` is a unit.  @census none (helper) -/
theorem sqrtXStarV_isUnit (h2 : (2 : Dq.carrier) ≠ 0) :
    IsUnit (Unipotent.sqrt h2 D.xStarV) :=
  (Unipotent.sqrt_spec h2 D.xStarV (D.xStarV - 1) D.xStarV_unipotent (by abel)).1

/-- `X⋆ = ((X⋆)^{1/2})²`, pointwise.  @census none (helper) -/
theorem xStarV_eq_sqrt_sqrt (h2 : (2 : Dq.carrier) ≠ 0) (y : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    D.xStarV y = Unipotent.sqrt h2 D.xStarV (Unipotent.sqrt h2 D.xStarV y) := by
  obtain ⟨-, -, hsq⟩ := Unipotent.sqrt_spec h2 D.xStarV (D.xStarV - 1) D.xStarV_unipotent
    (by abel)
  rw [← Module.End.mul_apply, ← sq, hsq]

/-- `(X⋆)^{-1/2} ∘ X⋆ = (X⋆)^{1/2}`.  @census none (helper) -/
theorem sqrtXStarV_inv_xStarV (h2 : (2 : Dq.carrier) ≠ 0) (y : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Ring.inverse (Unipotent.sqrt h2 D.xStarV) (D.xStarV y) = Unipotent.sqrt h2 D.xStarV y := by
  rw [D.xStarV_eq_sqrt_sqrt h2 y, inverse_end_apply (D.sqrtXStarV_isUnit h2)]

/-- `X⋆ ∘ (X⋆)^{-1/2} = (X⋆)^{1/2}`.  @census none (helper) -/
theorem xStarV_sqrtXStarV_inv (h2 : (2 : Dq.carrier) ≠ 0) (y : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    D.xStarV (Ring.inverse (Unipotent.sqrt h2 D.xStarV) y) = Unipotent.sqrt h2 D.xStarV y := by
  rw [D.xStarV_eq_sqrt_sqrt h2 (Ring.inverse (Unipotent.sqrt h2 D.xStarV) y),
    end_inverse_apply (D.sqrtXStarV_isUnit h2)]

/-- `(X⋆)^{-1}` and `(X⋆)^{-1/2}` commute.  @census none (helper) -/
theorem xStarV_inv_comm_sqrt_inv (h2 : (2 : Dq.carrier) ≠ 0) (y : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Ring.inverse D.xStarV (Ring.inverse (Unipotent.sqrt h2 D.xStarV) y)
      = Ring.inverse (Unipotent.sqrt h2 D.xStarV) (Ring.inverse D.xStarV y) := by
  have hcom : Commute (Unipotent.sqrt h2 D.xStarV) D.xStarV :=
    Unipotent.sqrt_commute h2 D.xStarV (D.xStarV - 1) D.xStarV_unipotent (by abel)
      D.xStarV D.xStarV_isUnit (Commute.refl _)
  have h1 : Commute (Ring.inverse (Unipotent.sqrt h2 D.xStarV)) D.xStarV :=
    Commute.inverse_left (D.sqrtXStarV_isUnit h2) hcom
  have hcc : Commute (Ring.inverse D.xStarV) (Ring.inverse (Unipotent.sqrt h2 D.xStarV)) :=
    Commute.inverse_left D.xStarV_isUnit h1.symm
  rw [← Module.End.mul_apply, hcc.eq, Module.End.mul_apply]

/-! ##### The four squares of `R-S8-23`'s Option-A square-root diagrams

Read as diagrams whose two rows are ONE representation — which is how the source printed
`eq:limitsquarerootdiagram0`/`1` until the author's ruling of 2026-09-11 — the middle vertical is
`(X⋆)^{1/2}` on the two left-hand squares and `(X⋆)^{-1/2}` on the two right-hand ones, never
`𝟏_{V(⋆)}` unless `X⋆ = 𝟏` (`F-S8-G4-1`, ruling `R-S8-23`).  All four remain true and two of
them, `sqrtDiag_edgeAm` and `sqrtDiag_edgeBm`, are the amended source's own `a₋`/`b₋` squares; the
amended `b₊`/`a₊` squares are `sqrtDiagEV_edgeBp`/`sqrtDiagEV_edgeAp` below. -/

/-- **The `a₋` square of `eq:limitsquarerootdiagram0`**, as the amended source prints it: the
middle vertical is `(X⋆)^{1/2}`.  Until the author's Option-B ruling of 2026-09-11 (`AN-42`,
applied at `388f0f8`) the source printed TWO square-root diagrams and this was the `a₋` square of
both; the second, then labelled `eq:limitsquarerootdiagram1`, was deleted, so this docstring no
longer names it.  `sqrt_natural` on `limitDiag_edgeAm`.  Re-tensed 2026-09-12, the amendment's
close-out round (`V-ERR-6`).  @census none (helper) -/
theorem sqrtDiag_edgeAm (h2 : (2 : Dq.carrier) ≠ 0) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) :
    Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (Unipotent.sqrt h2 D.limMinusV x)
      = Unipotent.sqrt h2 D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x) :=
  sqrt_natural h2 D.limMinusV_unipotent D.xStarV_unipotent (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0)
    (fun y => (D.limitDiag_edgeAm y).symm) x

/-- **The `b₋` square of `eq:limitsquarerootdiagram0`**, as the amended source prints it: the
middle vertical is `(X⋆)^{1/2}`.  As with `sqrtDiag_edgeAm`, the second diagram this docstring used
to name alongside it — `eq:limitsquarerootdiagram1` — was deleted by the author's Option-B ruling of
2026-09-11 (`AN-42`).  `sqrt_natural` on `limitDiag_edgeBm`.  Re-tensed 2026-09-12, the amendment's
close-out round (`V-ERR-6`).  @census none (helper) -/
theorem sqrtDiag_edgeBm (h2 : (2 : Dq.carrier) ≠ 0) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Unipotent.sqrt h2 D.limMinusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 x)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (Unipotent.sqrt h2 D.xStarV x) :=
  (sqrt_natural h2 D.xStarV_unipotent D.limMinusV_unipotent (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1)
    (fun y => (D.limitDiag_edgeBm y).symm) x).symm

/-- **The `b₊` square of the SECOND square-root diagram the source printed until 2026-09-11**, in
the Option-A reading ruling `R-S8-23` directed: the middle vertical is `(X⋆)^{-1/2}`.  That diagram,
then labelled `eq:limitsquarerootdiagram1`, was DELETED by the author's Option-B ruling of
2026-09-11 (`AN-42`); the amended source's `b₊` square is `sqrtDiagEV_edgeBp` below.  The identity
itself is true and is used, which is why it is kept — see the section header above.
`sqrt_natural` on `limitDiag_edgeBp'`, then `sqrt_inv`.  Re-tensed 2026-09-12, the amendment's
close-out round (`V-ERR-6`).  @census none (helper) -/
theorem sqrtDiag_edgeBp (h2 : (2 : Dq.carrier) ≠ 0) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Unipotent.sqrt h2 D.limPlusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 x)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (linInv (Unipotent.sqrt h2 D.xStarV) x) := by
  have hsu : IsUnit (Unipotent.sqrt h2 D.limPlusV) :=
    (Unipotent.sqrt_spec h2 D.limPlusV (D.limPlusV - 1) D.limPlusV_unipotent (by abel)).1
  have hinv := Unipotent.sqrt_inv h2 D.limPlusV (D.limPlusV - 1) D.limPlusV_unipotent (by abel)
  have key := sqrt_natural h2 D.xStarV_unipotent
    (isNilpotent_inverse_sub_one D.limPlusV_unipotent) (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3)
    (fun y => D.limitDiag_edgeBp' y) (Ring.inverse (Unipotent.sqrt h2 D.xStarV) x)
  rw [end_inverse_apply (D.sqrtXStarV_isUnit h2), ← hinv] at key
  have goal' : Unipotent.sqrt h2 D.limPlusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 x)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (Ring.inverse (Unipotent.sqrt h2 D.xStarV) x) :=
    Eq.trans (congrArg (fun z => Unipotent.sqrt h2 D.limPlusV z) key)
      (end_inverse_apply hsu _)
  rw [← ring_inverse_eq_linInv]
  exact goal'

/-- **The `a₊` square of the SECOND square-root diagram the source printed until 2026-09-11**, in
ruling `R-S8-23`'s Option-A reading: the middle vertical is `(X⋆)^{-1/2}`.  That diagram, then
labelled `eq:limitsquarerootdiagram1`, was DELETED by the author's Option-B ruling of 2026-09-11
(`AN-42`); the amended source's `a₊` square is `sqrtDiagEV_edgeAp` below.  The identity itself is
true and is used.  `sqrt_natural` on `limitDiag_edgeAp'`, then `sqrt_inv`.  Re-tensed 2026-09-12,
the amendment's close-out round (`V-ERR-6`).  @census none (helper) -/
theorem sqrtDiag_edgeAp (h2 : (2 : Dq.carrier) ≠ 0) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :
    Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (Unipotent.sqrt h2 D.limPlusV x)
      = linInv (Unipotent.sqrt h2 D.xStarV) (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x) := by
  have hnat := sqrt_natural h2 D.limPlusV_unipotent
    (isNilpotent_inverse_sub_one D.xStarV_unipotent) (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2)
    (fun y => D.limitDiag_edgeAp' y) x
  rw [← ring_inverse_eq_linInv,
    Unipotent.sqrt_inv h2 D.xStarV (D.xStarV - 1) D.xStarV_unipotent (by abel)]
  exact hnat

/-- **The `b₊` square of `R-S8-23`'s Option-A FIRST diagram** — what the source printed as
`eq:limitsquarerootdiagram0` until the author's ruling of 2026-09-11 — whose edge is `φ_{b₊}X⋆`:
the middle vertical was `(X⋆)^{-1/2}` here too, and both sides are `φ_{b₊}((X⋆)^{1/2}·)`.  Kept as
a true helper identity, per the section header above; the AMENDED `eq:limitsquarerootdiagram0`'s
`b₊` square is `sqrtDiagEV_edgeBp` below, whose middle vertical is `t = (X⋆)^{1/2}`.  Re-tensed
2026-09-12, the amendment's close-out round (`V-ERR-6`).  @census none (helper) -/
theorem sqrtDiag0_edgeBp (h2 : (2 : Dq.carrier) ≠ 0) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Unipotent.sqrt h2 D.limPlusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV x))
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV (linInv (Unipotent.sqrt h2 D.xStarV) x)) := by
  rw [D.sqrtDiag_edgeBp h2 (D.xStarV x), ← ring_inverse_eq_linInv, D.sqrtXStarV_inv_xStarV h2,
    D.xStarV_sqrtXStarV_inv h2]

/-- **The `a₊` square of `R-S8-23`'s Option-A FIRST diagram** — what the source printed as
`eq:limitsquarerootdiagram0` until the author's ruling of 2026-09-11 — whose edge is
`X⋆^{-1}φ_{a₊}`.  Kept as a true helper identity; the AMENDED diagram's `a₊` square is
`sqrtDiagEV_edgeAp` below.  Re-tensed 2026-09-12, the amendment's close-out round (`V-ERR-6`).
@census none (helper) -/
theorem sqrtDiag0_edgeAp (h2 : (2 : Dq.carrier) ≠ 0) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :
    linInv D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (Unipotent.sqrt h2 D.limPlusV x))
      = linInv (Unipotent.sqrt h2 D.xStarV) (linInv D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x)) := by
  rw [D.sqrtDiag_edgeAp h2 x, ← ring_inverse_eq_linInv, ← ring_inverse_eq_linInv,
    D.xStarV_inv_comm_sqrt_inv h2]

/-! ##### The ONE square-root diagram of the amended source: `𝔼_{ℚ[√-1]}(M)` over `V`

Until the author's ruling of 2026-09-11 the source printed **two** square-root diagrams, each with
the same row top and bottom and `𝟏_{V(⋆)}` on the middle vertical; that was `AN-42`, and the four
squares above are the Option-A repair the coordinator had ruled for the tree (`R-S8-23`).  The
author ruled **Option B**: one diagram, whose **top** row is `𝔼_{ℚ[√-1]}(M)`
`(φ_{a₋}, φ_{b₋}, φ_{b₊}X⋆, X⋆⁻¹φ_{a₊})`, whose **bottom** row is `V`
`(φ_{a₋}, φ_{b₋}, φ_{b₊}, φ_{a₊})`, and whose verticals are `(s₋, t, s₊)`.  All four squares then
commute with the **same** middle vertical `t = X⋆^{1/2}`.  The `a₋` and `b₋` squares are
`sqrtDiag_edgeAm`/`sqrtDiag_edgeBm` unchanged; the two right-hand ones are the two theorems below,
and they are where `t X⋆⁻¹ = t⁻¹ = X⋆⁻¹ t` is used. -/

/-- `(X⋆)^{1/2} ∘ (X⋆)^{-1} = (X⋆)^{-1/2}`.  The mirror of `sqrtXStarV_inv_xStarV`, and the
identity the two right-hand squares of the amended source's diagram use.
@census none (helper) -/
theorem sqrtXStarV_xStarV_inv (h2 : (2 : Dq.carrier) ≠ 0) (y : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Unipotent.sqrt h2 D.xStarV (Ring.inverse D.xStarV y)
      = Ring.inverse (Unipotent.sqrt h2 D.xStarV) y := by
  have hkey : D.xStarV (Ring.inverse (Unipotent.sqrt h2 D.xStarV)
      (Ring.inverse (Unipotent.sqrt h2 D.xStarV) y)) = y := by
    rw [D.xStarV_eq_sqrt_sqrt h2, end_inverse_apply (D.sqrtXStarV_isUnit h2),
      end_inverse_apply (D.sqrtXStarV_isUnit h2)]
  have hinv : Ring.inverse D.xStarV y
      = Ring.inverse (Unipotent.sqrt h2 D.xStarV)
          (Ring.inverse (Unipotent.sqrt h2 D.xStarV) y) := by
    conv_lhs => rw [← hkey]
    rw [inverse_end_apply D.xStarV_isUnit]
  rw [hinv, end_inverse_apply (D.sqrtXStarV_isUnit h2)]

/-- **The `b₊` square of the amended source's ONE diagram**: top edge `φ_{b₊}X⋆`, bottom edge
`φ_{b₊}`, verticals `t` and `s₊`.  `s₊ ∘ (φ_{b₊}X⋆) = φ_{b₊} ∘ t`, via
`sqrtDiag_edgeBp` and `(X⋆)^{-1/2} ∘ X⋆ = (X⋆)^{1/2}`.  @census none (helper) -/
theorem sqrtDiagEV_edgeBp (h2 : (2 : Dq.carrier) ≠ 0) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Unipotent.sqrt h2 D.limPlusV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV x))
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (Unipotent.sqrt h2 D.xStarV x) := by
  rw [D.sqrtDiag_edgeBp h2 (D.xStarV x), ← ring_inverse_eq_linInv,
    D.sqrtXStarV_inv_xStarV h2]

/-- **The `a₊` square of the amended source's ONE diagram**: top edge `X⋆⁻¹φ_{a₊}`, bottom edge
`φ_{a₊}`, verticals `s₊` and `t`.  `t ∘ (X⋆⁻¹φ_{a₊}) = φ_{a₊} ∘ s₊`, via `sqrtDiag_edgeAp`
and `(X⋆)^{1/2} ∘ (X⋆)^{-1} = (X⋆)^{-1/2}`.  @census none (helper) -/
theorem sqrtDiagEV_edgeAp (h2 : (2 : Dq.carrier) ≠ 0) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :
    Unipotent.sqrt h2 D.xStarV (linInv D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x))
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (Unipotent.sqrt h2 D.limPlusV x) := by
  rw [D.sqrtDiag_edgeAp h2 x, ← ring_inverse_eq_linInv, ← ring_inverse_eq_linInv,
    D.sqrtXStarV_xStarV_inv h2]

/-! ##### The rational structure of the constructed module, read on `V(±)` -/

/-- `φ^M_{+,c} = φ_{+,c} ∘ φ^{(∞)}_+` on `V(+)` — the `+`-vertex reading of `eq:varphiplus`.
@census none (helper) -/
theorem phiV_plus (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :
    D.phiV 2 x = Vphi hcard V 2 (D.limPlusV x) := by
  have hvm : ((D.toPlus.symm x : D.setup.weight.comp ((ℓ : ℤ) + 1)) : D.carrier)
      ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := (D.toPlus.symm x).2
  have hPm : (Gelfand.RationalStructure.inputPlus D.setup).limPlus
      ((D.toPlus.symm x : D.setup.weight.comp ((ℓ : ℤ) + 1)) : D.carrier)
      ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := (Gelfand.RationalStructure.inputPlus D.setup).limPlus_mem _
  have hc : D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus
      ((D.toPlus.symm x : D.setup.weight.comp ((ℓ : ℤ) + 1)) : D.carrier))
      ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) := D.setup.conj_comp _ _ hPm
  have hsub : (⟨((D.toPlus.symm x : D.setup.weight.comp ((ℓ : ℤ) + 1)) : D.carrier), hvm⟩ :
      D.setup.weight.comp ((ℓ : ℤ) + 1)) = D.toPlus.symm x := rfl
  show D.toMinus ⟨D.setup.conj ((Gelfand.RationalStructure.inputPlus D.setup).limPlus _), hc⟩ = _
  rw [D.toMinus_conj _ hPm hc, D.toPlus_limPlus _ hvm hPm, hsub, D.toPlus.apply_symm_apply]

/-- `φ^M_{-,c} = φ_{-,c} ∘ φ^{(∞)}_-` on `V(−)` — the `−`-vertex reading of `eq:varphiminus`.
@census none (helper) -/
theorem phiV_minus (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) :
    D.phiV 0 x = Vphi hcard V 0 (D.limMinusV x) := by
  have hvm : ((D.toMinus.symm x : D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier)
      ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) := (D.toMinus.symm x).2
  have hPm : (Gelfand.RationalStructure.inputMinus D.setup).limPlus
      ((D.toMinus.symm x : D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier)
      ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1)) := (Gelfand.RationalStructure.inputMinus D.setup).limPlus_mem _
  have hc : D.setup.conj ((Gelfand.RationalStructure.inputMinus D.setup).limPlus
      ((D.toMinus.symm x : D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier))
      ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := by
    have h := D.setup.conj_comp _ _ hPm
    rwa [neg_neg] at h
  have hsub : (⟨((D.toMinus.symm x : D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier), hvm⟩ :
      D.setup.weight.comp (-((ℓ : ℤ) + 1))) = D.toMinus.symm x := rfl
  show D.toPlus ⟨D.setup.conj ((Gelfand.RationalStructure.inputMinus D.setup).limPlus _), hc⟩ = _
  rw [D.toPlus_conj _ hPm hc, D.toMinus_limMinus _ hvm hPm, hsub, D.toMinus.apply_symm_apply]


/-! ##### `c`-invariance of `(X⋆)^{1/2}`, needed at the `⋆` vertex of the amended `C24`

The amended `C24`'s `⋆`-vertex conjugation conjunct `t ∘ φ^M_⋆ ∘ t⁻¹ = φ_⋆` needs `t^c = t`, which
the source states as `X⋆^c = Y⋆ = X⋆` plus `eq:squarerootgaloisequivariance`.  The three theorems
below are the `h₂`-parameterized companions of engine `E8`'s `conjStar_sub'`,
`conjStar_sqrt_xStarV` and `Vphi_sqrt_xStarV`, stated here because `C24` consumes them at this
earlier point in the file; `E8`'s own copies (at `qiTwo`) are unchanged. -/

/-- `c`-conjugation at `⋆` is additive on differences.  @census none (helper) -/
theorem conjStar_sub (a b : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1)) :
    conjStar hcard V (a - b) = conjStar hcard V a - conjStar hcard V b := by
  ext x
  simp [conjStar, conjBy]

/-- `c` fixes `(X⋆)^{1/2}` — `X⋆^c = X⋆` (`C18`) transported across the square root by
`sqrt_unique`.  @census none (helper) -/
theorem conjStar_sqrt_xStar (h2 : (2 : Dq.carrier) ≠ 0) :
    conjStar hcard V (Unipotent.sqrt h2 D.xStarV) = Unipotent.sqrt h2 D.xStarV := by
  obtain ⟨-, hnil, hsq⟩ := Unipotent.sqrt_spec h2 D.xStarV (D.xStarV - 1)
    D.xStarV_unipotent (by abel)
  refine Unipotent.sqrt_unique h2 D.xStarV
    (conjStar hcard V (Unipotent.sqrt h2 D.xStarV))
    (conjStar hcard V (Unipotent.sqrt h2 D.xStarV - 1))
    (conjBy_isNilpotent Dq.conj (Vphi hcard V 1) (Vphi_smul hcard V 1) hnil) ?_ ?_
  · rw [conjStar_sub, conjStar_one]
    abel
  · rw [sq, ← conjStar_mul, ← sq, hsq, D.xStarV_eq, conjStar_xStarAt]

/-- `φ_{⋆,c}` commutes with `(X⋆)^{1/2}`.  @census none (helper) -/
theorem Vphi_comm_sqrt_xStar (h2 : (2 : Dq.carrier) ≠ 0) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Vphi hcard V 1 (Unipotent.sqrt h2 D.xStarV x)
      = Unipotent.sqrt h2 D.xStarV (Vphi hcard V 1 x) :=
  Vphi_comm_of_conjStar hcard V (D.conjStar_sqrt_xStar h2) x

/-- **`RQ-5.05-C23`, as the author's Option-B ruling of 2026-09-11 states it** (`AN-42`; census
revision r14, tag `census-v1.11`).

The amended source prints **one** square-root diagram, `eq:limitsquarerootdiagram0`: its **top**
row is `𝔼_{ℚ[√-1]}(M)`, i.e. `(φ_{a₋}, φ_{b₋}, φ_{b₊}X⋆, X⋆⁻¹φ_{a₊})`, its **bottom** row is `V`,
i.e. `(φ_{a₋}, φ_{b₋}, φ_{b₊}, φ_{a₊})`, and its verticals are `(s₋, t, s₊)` with
`s_± := (φ^{(∞)}_±)^{1/2}` and `t := X⋆^{1/2}`.  All four squares commute, with the **same** middle
vertical `t`; the two right-hand ones use `t X⋆⁻¹ = t⁻¹ = X⋆⁻¹ t`
(`sqrtDiagEV_edgeBp`, `sqrtDiagEV_edgeAp`).

Until that ruling the source printed two diagrams, each with the same row top and bottom and
`𝟏_{V(⋆)}` on the middle vertical, and this clause was rendered in the Option-A form coordinator
ruling `R-S8-23` directed — the split middle vertical `(X⋆)^{±1/2}` plus a "commutes iff" conjunct.
The author ruled Option B instead, so the tree is brought off `R-S8-23` and onto the source; the
two refutation probes `C23_printed_forces_AN41` and `C24_printed_forces_trivial_xStar` are kept,
as the record of what the source said before 2026-09-11.
@census none (helper) -/
theorem essSurj_C23 :
    (let sPlus := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV
     let sMinus := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV
     let tStar := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.xStarV
     -- the `a₋` square: `t ∘ φ_{a₋} = φ_{a₋} ∘ s₋`
     (∀ x, tStar (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (sMinus x)) ∧
     -- the `b₋` square: `s₋ ∘ φ_{b₋} = φ_{b₋} ∘ t`
     (∀ x, sMinus (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (tStar x)) ∧
     -- the `b₊` square: `s₊ ∘ (φ_{b₊}X⋆) = φ_{b₊} ∘ t`
     (∀ x, sPlus (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV x)) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (tStar x)) ∧
     -- the `a₊` square: `t ∘ (X⋆⁻¹φ_{a₊}) = φ_{a₊} ∘ s₊`
     (∀ x, tStar (linInv D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x)) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (sPlus x))) :=
  ⟨fun x => (D.sqrtDiag_edgeAm (two_ne_zero_of_base (K := E) two_ne_zero) x).symm,
    fun x => D.sqrtDiag_edgeBm (two_ne_zero_of_base (K := E) two_ne_zero) x,
    fun x => D.sqrtDiagEV_edgeBp (two_ne_zero_of_base (K := E) two_ne_zero) x,
    fun x => D.sqrtDiagEV_edgeAp (two_ne_zero_of_base (K := E) two_ne_zero) x⟩

/-- **`RQ-5.05-C24`, as the author's Option-B ruling of 2026-09-11 states it** (`AN-41`/`AN-42`;
census revision r14, tag `census-v1.11`).  It also carries what `RQ-5.05-C25` used to claim: that
clause is **retired in the source** — the final `(𝟏_{V(+)}, X⋆, 𝟏_{V(−)})` sentence is deleted, not
corrected — and its content is absorbed here.

Two named parts.  (a) The triple `(s₊, t, s₋)` is a `ℚ[√-1]`-linear **isomorphism of quiver
representations** `𝔼_{ℚ[√-1]}(M) → V`: all three components are units, and the four squares of
`essSurj_C23` are its four edge conditions.  (b) It is an isomorphism of `ℚ`-**rational**
representations: it conjugates the rational structure `𝔼_ℚ(M)` induces into the given `φ_•` at
**all three** vertices — at `±` by `eq:pmsquarerootsinverses` (`essSurj_C22`), and at `⋆` because
`φ^{(∞)}_⋆ = 𝟏` (`eq:phistaridentity`, `essSurj_C20`) and `X⋆^c = Y⋆ = X⋆`, whence `t^c = t`
(`Vphi_comm_sqrt_xStar`) and `t φ_⋆ t⁻¹ = φ_⋆`.  Hence `𝔼_ℚ(M, φ_•^M) ≅ (V, φ_•)`.

Until 2026-09-11 the `⋆` component of (b) was the printed `𝟏_{V(⋆)}`, which made this conjunct
read `φ^M_⋆ = φ_⋆` on the nose; the amended source's `t` is what makes the single triple an
isomorphism of `ℚ`-rational representations, which is the statement the proof needs and which the
two printed triples one paragraph apart did not state.
@census none (helper)
@clauses   RQ2-5.12-S-O24 -/
theorem essSurj_C24 :
    (let sPlus := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV
     let sMinus := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV
     let tStar := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.xStarV
     -- (a) an isomorphism of quiver representations `𝔼_{ℚ[√-1]}(M) → V`
     (IsUnit sPlus ∧ IsUnit sMinus ∧ IsUnit tStar ∧
       (∀ x, tStar (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (sMinus x)) ∧
       (∀ x, sMinus (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (tStar x)) ∧
       (∀ x, sPlus (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV x)) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (tStar x)) ∧
       (∀ x, tStar (linInv D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x)) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (sPlus x))) ∧
     -- (b) and of `ℚ`-rational representations, at all THREE vertices
     (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2, sMinus (D.phiV 2 (linInv sPlus x)) = Vphi hcard V 2 x) ∧
     (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0, sPlus (D.phiV 0 (linInv sMinus x)) = Vphi hcard V 0 x) ∧
     (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1, tStar (D.phiV 1 (linInv tStar x)) = Vphi hcard V 1 x)) := by
  obtain ⟨hPu, -, -⟩ := Unipotent.sqrt_spec (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV (D.limPlusV - 1)
    D.limPlusV_unipotent (by abel)
  obtain ⟨hMu, -, -⟩ := Unipotent.sqrt_spec (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV (D.limMinusV - 1)
    D.limMinusV_unipotent (by abel)
  obtain ⟨hC22p, hC22m⟩ := D.essSurj_C22
  obtain ⟨hd1, hd2, hd3, hd4⟩ := D.essSurj_C23
  refine ⟨⟨hPu, hMu, D.sqrtXStarV_isUnit (two_ne_zero_of_base (K := E) two_ne_zero),
      hd1, hd2, hd3, hd4⟩,
    fun x => ?_, fun x => ?_, fun x => ?_⟩
  · calc Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV
          (D.phiV 2 (linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV) x))
        = Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV (Vphi hcard V 2
            (D.limPlusV (linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV) x))) := by rw [D.phiV_plus]
      _ = Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV
            (Vphi hcard V 2 (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV x)) := by
          rw [← ring_inverse_eq_linInv, unipotent_sqrt_inv_cancel (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV_unipotent]
      _ = Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV
            (linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV) (Vphi hcard V 2 x)) := by rw [hC22p x]
      _ = Vphi hcard V 2 x := by rw [← ring_inverse_eq_linInv, end_inverse_apply hMu]
  · calc Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV
          (D.phiV 0 (linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV) x))
        = Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV (Vphi hcard V 0
            (D.limMinusV (linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV) x))) := by rw [D.phiV_minus]
      _ = Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV
            (Vphi hcard V 0 (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV x)) := by
          rw [← ring_inverse_eq_linInv, unipotent_sqrt_inv_cancel (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV_unipotent]
      _ = Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV
            (linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV) (Vphi hcard V 0 x)) := by rw [hC22m x]
      _ = Vphi hcard V 0 x := by rw [← ring_inverse_eq_linInv, end_inverse_apply hPu]
  · calc Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.xStarV
          (D.phiV 1 (linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.xStarV) x))
        = Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.xStarV
            (Vphi hcard V 1 (linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.xStarV) x)) := by
          rw [D.essSurj_C20.2]
      _ = Vphi hcard V 1 (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.xStarV
            (linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.xStarV) x)) := by
          rw [D.Vphi_comm_sqrt_xStar (two_ne_zero_of_base (K := E) two_ne_zero)]
      _ = Vphi hcard V 1 x := by
          rw [← ring_inverse_eq_linInv,
            end_inverse_apply (D.sqrtXStarV_isUnit (two_ne_zero_of_base (K := E) two_ne_zero))]

end EssSurjData

end E3

end EssSurj

section EssSurj

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2) (hℓ : 1 ≤ ℓ)

/-- **`RQ-5.05-C10`, `C11`, `C12`, `C14`** — the identities of the construction.

`C10`: by the relation, `n_⋆` and `φ_⋆` are independent of the sign — `φ_{a₋}φ_{b₋} = φ_{a₊}φ_{b₊}`.
`C11`: `ξ^{(j)}_{•,+} ∘ ξ^{(j)}_{•,-} = φ_• − j²·𝟏` (from `(φ_•^{1/2})² = φ_•`, which needs `φ_•`'s
`ℓ²·𝟏 + nilpotent` shape — `phi_scalar_add_nilpotent`, the fact that replaced `HYP-07`).
`C12`: `φ_{•,c} ∘ ξ^{(j)}_{•,±} ∘ φ_{•,c}^{-1} = ξ^{(j)}_{c•,±}` (`eq:semilinearconjugation`,
`RQ-4.05-C5`), with `φ_{•,c}^{-1} = φ_{c•,c}` by the cocycle condition.
`C14`: `eq:4XY2`, `eq:4YX2` for **all** `j ≡ ℓ (mod 2)`, boundary cases included, read on the
construction's components: `4XY|_{M_{j+1}} = φ_• − j²·𝟏` and `4YX|_{M_{j-1}} = φ_• − j²·𝟏` with `•`
the vertex of the component; `eq:Xconjugation`/`eq:Yconjugation` are the `conj_X`/`conj_Y` fields
of the constructed `RationalSetup` (`essSurj_exists`).

@census    none (auxiliary; discharges census clauses `RQ-5.05-C10`, `RQ-5.05-C11`, `RQ-5.05-C12`, `RQ-5.05-C14`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C10, RQ-5.05-C11, RQ-5.05-C12, RQ-5.05-C14
@imports   none
@divergence `C14`'s two identities are read on `M_{j+1}` (for `4XY`) and `M_{j-1}` (for `4YX`) — the
components the two composites actually act on, given `X`/`Y` shift the grading by `±1` — silently
correcting `eq:4XY2`/`eq:4YX2` as printed, which write the identity factors as `1_{M_{j-1}}` and
`1_{M_{j+1}}` respectively (swapped against the composite each multiplies). This is the transcription
error the `fccad35` repair fixed (`V-S8-D1-4`(a), 2026-09-03); no `AN` item is proposed since the
index-corrected reading is forced by the composites' own domains/codomains, not a choice. -/
theorem essSurj_operators (V : Gelfand.RationalStructure.RepNilQ hcard) (D : EssSurjData hcard hℓ V) :
    -- `C10`
    (Split.nOp (Gelfand.RationalStructure.toSplitW hcard V) 1 = Split.nStarPlus (Gelfand.RationalStructure.toSplitW hcard V) ∧
      Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 = ((ℓ : Dq.carrier) ^ 2) • 1 + (4 : Dq.carrier) • Split.nStarPlus (Gelfand.RationalStructure.toSplitW hcard V)) ∧
    -- `C11`
    (∀ (v : Fin 3) (j : ℤ),
      Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) v 1 j * Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) v (-1) j
        = Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) v - ((j : Dq.carrier) ^ 2) • 1) ∧
    -- `C12`
    (∀ (v : Fin 3) (s j : ℤ) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) (RQuiver.gelfandVertexSwap v)),
      Vphi hcard V v (Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) v s j ((Vphi hcard V v).symm x))
        = Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) (RQuiver.gelfandVertexSwap v) s j x) ∧
    -- `C14`, `eq:4XY2` / `eq:4YX2` on the three ranges and at the two boundaries
    ((∀ (j : ℤ) (_hj : (ℓ : ℤ) < j) (_hp : (j - (ℓ : ℤ)) % 2 = 0),
        (∀ v (hv : v ∈ D.setup.weight.comp (j + 1)),
          (4 : Dq.carrier) • D.setup.weight.X (D.setup.weight.Y v)
            = (D.isoPlus (j + 1) (by omega) (by omega)).symm
                ((Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 2 - ((j : Dq.carrier) ^ 2) • 1)
                  (D.isoPlus (j + 1) (by omega) (by omega) ⟨v, hv⟩))) ∧
        (∀ v (hv : v ∈ D.setup.weight.comp (j - 1)),
          (4 : Dq.carrier) • D.setup.weight.Y (D.setup.weight.X v)
            = (D.isoPlus (j - 1) (by omega) (by omega)).symm
                ((Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 2 - ((j : Dq.carrier) ^ 2) • 1)
                  (D.isoPlus (j - 1) (by omega) (by omega) ⟨v, hv⟩)))) ∧
      (∀ (j : ℤ) (_hj : -(ℓ : ℤ) < j) (_hj' : j < (ℓ : ℤ)) (_hp : (j - (ℓ : ℤ)) % 2 = 0),
        (∀ v (hv : v ∈ D.setup.weight.comp (j + 1)),
          (4 : Dq.carrier) • D.setup.weight.X (D.setup.weight.Y v)
            = (D.isoStar (j + 1) (by omega) (by omega) (by omega)).symm
                ((Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 - ((j : Dq.carrier) ^ 2) • 1)
                  (D.isoStar (j + 1) (by omega) (by omega) (by omega) ⟨v, hv⟩))) ∧
        (∀ v (hv : v ∈ D.setup.weight.comp (j - 1)),
          (4 : Dq.carrier) • D.setup.weight.Y (D.setup.weight.X v)
            = (D.isoStar (j - 1) (by omega) (by omega) (by omega)).symm
                ((Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 - ((j : Dq.carrier) ^ 2) • 1)
                  (D.isoStar (j - 1) (by omega) (by omega) (by omega) ⟨v, hv⟩)))) ∧
      (∀ (j : ℤ) (_hj : j < -(ℓ : ℤ)) (_hp : (j - (ℓ : ℤ)) % 2 = 0),
        (∀ v (hv : v ∈ D.setup.weight.comp (j + 1)),
          (4 : Dq.carrier) • D.setup.weight.X (D.setup.weight.Y v)
            = (D.isoMinus (j + 1) (by omega) (by omega)).symm
                ((Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 0 - ((j : Dq.carrier) ^ 2) • 1)
                  (D.isoMinus (j + 1) (by omega) (by omega) ⟨v, hv⟩))) ∧
        (∀ v (hv : v ∈ D.setup.weight.comp (j - 1)),
          (4 : Dq.carrier) • D.setup.weight.Y (D.setup.weight.X v)
            = (D.isoMinus (j - 1) (by omega) (by omega)).symm
                ((Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 0 - ((j : Dq.carrier) ^ 2) • 1)
                  (D.isoMinus (j - 1) (by omega) (by omega) ⟨v, hv⟩)))) ∧
      -- `j = ℓ`: `4XY|_{M_{ℓ+1}} = φ_+ − ℓ²`, `4YX|_{M_{ℓ-1}} = φ_⋆ − ℓ²`
      ((∀ v (hv : v ∈ D.setup.weight.comp ((ℓ : ℤ) + 1)),
          (4 : Dq.carrier) • D.setup.weight.X (D.setup.weight.Y v)
            = D.toPlus.symm ((Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 2 - ((ℓ : Dq.carrier) ^ 2) • 1) (D.toPlus ⟨v, hv⟩))) ∧
        (∀ v (hv : v ∈ D.setup.weight.comp ((ℓ : ℤ) - 1)),
          (4 : Dq.carrier) • D.setup.weight.Y (D.setup.weight.X v)
            = D.toStarHi.symm ((Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 - ((ℓ : Dq.carrier) ^ 2) • 1)
                (D.toStarHi ⟨v, hv⟩)))) ∧
      -- `j = -ℓ`: `4XY|_{M_{-(ℓ-1)}} = φ_⋆ − ℓ²`, `4YX|_{M_{-(ℓ+1)}} = φ_- − ℓ²`
      ((∀ v (hv : v ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1))),
          (4 : Dq.carrier) • D.setup.weight.X (D.setup.weight.Y v)
            = D.toStarLo.symm ((Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 - ((ℓ : Dq.carrier) ^ 2) • 1)
                (D.toStarLo ⟨v, hv⟩))) ∧
        (∀ v (hv : v ∈ D.setup.weight.comp (-((ℓ : ℤ) + 1))),
          (4 : Dq.carrier) • D.setup.weight.Y (D.setup.weight.X v)
            = D.toMinus.symm ((Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 0 - ((ℓ : Dq.carrier) ^ 2) • 1)
                (D.toMinus ⟨v, hv⟩)))))
    := by
  have hxi := Split.xi_mul_xi hℓ (Gelfand.RationalStructure.toSplitW hcard V)
  refine ⟨⟨Split.nOp_star_eq_nStarPlus (Gelfand.RationalStructure.toSplitW hcard V), ?_⟩, fun v j => (hxi v j).1,
    fun v s j x => LinearMap.congr_fun (conjBy_xiOp hcard hℓ V v s j) x, ?_, ?_, ?_, ?_, ?_⟩
  · -- `C10`, second conjunct: `φ_⋆ = ℓ²·𝟏 + 4·φ_{a₊}φ_{b₊}`
    show ((ℓ : Dq.carrier) ^ 2) • 1 + (4 : Dq.carrier) • Split.nOp (Gelfand.RationalStructure.toSplitW hcard V) 1 = _
    rw [Split.nOp_star_eq_nStarPlus]
  · -- `C14`, the range `ℓ < j`
    intro j hj hp
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact pin_compose hcard hℓ D (D.isoPlus (j + 1) (by omega) (by omega))
        (D.isoPlus (j - 1) (by omega) (by omega))
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 2 (-1) j)
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 2 1 j)
        (fun w hw => D.Y_plus j hj hp w hw) (fun w hw => D.X_plus j hj hp w hw)
        (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 2 - ((j : Dq.carrier) ^ 2) • 1)
        ((Split.four_smul_half_comp _ _).trans (hxi 2 j).1).symm v hv
    · exact pin_compose' hcard hℓ D (D.isoPlus (j + 1) (by omega) (by omega))
        (D.isoPlus (j - 1) (by omega) (by omega))
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 2 (-1) j)
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 2 1 j)
        (fun w hw => D.Y_plus j hj hp w hw) (fun w hw => D.X_plus j hj hp w hw)
        (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 2 - ((j : Dq.carrier) ^ 2) • 1)
        ((Split.four_smul_half_comp _ _).trans (hxi 2 j).2).symm v hv
  · -- `C14`, the range `-ℓ < j < ℓ`
    intro j hj hj' hp
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact pin_compose hcard hℓ D (D.isoStar (j + 1) (by omega) (by omega) (by omega))
        (D.isoStar (j - 1) (by omega) (by omega) (by omega))
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 (-1) j)
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 1 j)
        (fun w hw => D.Y_star j hj hj' hp w hw) (fun w hw => D.X_star j hj hj' hp w hw)
        (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 - ((j : Dq.carrier) ^ 2) • 1)
        ((Split.four_smul_half_comp _ _).trans (hxi 1 j).1).symm v hv
    · exact pin_compose' hcard hℓ D (D.isoStar (j + 1) (by omega) (by omega) (by omega))
        (D.isoStar (j - 1) (by omega) (by omega) (by omega))
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 (-1) j)
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 1 j)
        (fun w hw => D.Y_star j hj hj' hp w hw) (fun w hw => D.X_star j hj hj' hp w hw)
        (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 - ((j : Dq.carrier) ^ 2) • 1)
        ((Split.four_smul_half_comp _ _).trans (hxi 1 j).2).symm v hv
  · -- `C14`, the range `j < -ℓ`
    intro j hj hp
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact pin_compose hcard hℓ D (D.isoMinus (j + 1) (by omega) (by omega))
        (D.isoMinus (j - 1) (by omega) (by omega))
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 0 (-1) j)
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 0 1 j)
        (fun w hw => D.Y_minus j hj hp w hw) (fun w hw => D.X_minus j hj hp w hw)
        (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 0 - ((j : Dq.carrier) ^ 2) • 1)
        ((Split.four_smul_half_comp _ _).trans (hxi 0 j).1).symm v hv
    · exact pin_compose' hcard hℓ D (D.isoMinus (j + 1) (by omega) (by omega))
        (D.isoMinus (j - 1) (by omega) (by omega))
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 0 (-1) j)
        (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) 0 1 j)
        (fun w hw => D.Y_minus j hj hp w hw) (fun w hw => D.X_minus j hj hp w hw)
        (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 0 - ((j : Dq.carrier) ^ 2) • 1)
        ((Split.four_smul_half_comp _ _).trans (hxi 0 j).2).symm v hv
  · -- `C14`, the boundary `j = ℓ`
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact pin_compose hcard hℓ D D.toPlus D.toStarHi (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2) (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3)
        (fun w hw => D.Y_bdry_plus w hw) (fun w hw => D.X_bdry_plus w hw)
        (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 2 - ((ℓ : Dq.carrier) ^ 2) • 1) (Split.phiOp_sub_ell (Gelfand.RationalStructure.toSplitW hcard V) 2) v hv
    · exact pin_compose' hcard hℓ D D.toPlus D.toStarHi (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2) (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3)
        (fun w hw => D.Y_bdry_plus w hw) (fun w hw => D.X_bdry_plus w hw)
        (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 - ((ℓ : Dq.carrier) ^ 2) • 1)
        (by rw [Split.phiOp_sub_ell, Split.nOp_star_eq_nStarPlus]; rfl) v hv
  · -- `C14`, the boundary `j = -ℓ`
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact pin_compose hcard hℓ D D.toStarLo D.toMinus (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1) (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0)
        (fun w hw => D.Y_bdry_minus w hw) (fun w hw => D.X_bdry_minus w hw)
        (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 1 - ((ℓ : Dq.carrier) ^ 2) • 1) (Split.phiOp_sub_ell (Gelfand.RationalStructure.toSplitW hcard V) 1) v hv
    · exact pin_compose' hcard hℓ D D.toStarLo D.toMinus (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1) (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0)
        (fun w hw => D.Y_bdry_minus w hw) (fun w hw => D.X_bdry_minus w hw)
        (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 0 - ((ℓ : Dq.carrier) ^ 2) • 1) (Split.phiOp_sub_ell (Gelfand.RationalStructure.toSplitW hcard V) 0) v hv

/-- **`RQ-5.05-C17`–`C25`** — the natural isomorphism `𝔼_ℚ(M, φ_•^M) ≅ (V, φ_•)`, for the
constructed `M` of any `D : EssSurjData V`, everything read on `V(•)` through `D`'s
identifications.

`C17`: `2^{ℓ-1}X^{ℓ-1}|_{M_{-(ℓ-1)}} = γ̃·𝟏 + ñ` with `0 < γ̃ ∈ ℚ^×`, `ñ` nilpotent commuting with
`φ_⋆`; hence `X⋆ = γ̃'(𝟏 + ñ_⋆)`, `γ̃' ∈ ℚ^×`.
`C18`: `X⋆ = Y⋆` on `V(⋆)`; hence `X⋆^c = X⋆` and `φ^{(∞),c}_⋆ = φ^{(∞)}_⋆`.
`C19` (`eq:phistaridentity`): `(φ^{(∞)}_⋆)² = 𝟏`, `φ^{(∞)}_⋆ − 𝟏` nilpotent, `φ^{(∞)}_⋆ = 𝟏`.
`C20` (`eq:starsquarerootsinverses`): `(φ^{(∞)}_⋆)^{1/2} = 𝟏`, and the rational structure induced on
`V(⋆)` by `𝔼_ℚ(M)` is the given `φ_⋆`.
`C21`: `φ^{(∞)}_± − 𝟏` nilpotent, and the unipotent square roots `(φ^{(∞)}_±)^{1/2}` exist
(`prop:unipotentsquareroots`: their squares are `φ^{(∞)}_±` and they are `𝟏 + nilpotent`).
`C22` (`eq:pmsquarerootsinverses`): `φ_± ∘ (φ^{(∞)}_±)^{1/2} = ((φ^{(∞)}_∓)^{1/2})^{-1} ∘ φ_±`.
`C23` (`eq:limitsquarerootdiagram0`): the amended source's **one** square-root diagram — top row
`𝔼_{ℚ[√-1]}(M)` `(φ_{a₋}, φ_{b₋}, φ_{b₊}X⋆, X⋆⁻¹φ_{a₊})`, bottom row `V`
`(φ_{a₋}, φ_{b₋}, φ_{b₊}, φ_{a₊})`, verticals `(s₋, t, s₊)` with `s_± = (φ^{(∞)}_±)^{1/2}` and
`t = X⋆^{1/2}` — commutes, all four squares, with the same middle vertical `t` (`essSurj_C23`).
`C24`: the triple `(s₊, t, s₋)` is a `ℚ[√-1]`-linear isomorphism of quiver representations
`𝔼_{ℚ[√-1]}(M) → V` and an isomorphism of `ℚ`-**rational** representations
`𝔼_ℚ(M) → (V, φ_•)`, conjugating the constructed rational structure into the given `φ_•` at all
three vertices (`essSurj_C24`).
`C25`: **retired in the source.** Under the author's Option-B ruling of 2026-09-11 the final
`(𝟏_{V(+)}, X⋆, 𝟏_{V(−)})` sentence is **deleted**, not corrected; the census records the row as
`RETIRED BY SOURCE EDIT r14` with its content absorbed into `C24`, and the tree carries no
separate `C25` rendering. The clause id is kept in `@clauses` because the row still exists and
`C24` above is what now discharges it.

**The three disclosures this declaration used to carry RETIRED on 2026-09-11.** Until the paper
author's ruling of that date (`workflow/reports/AUTHOR-QUEUE.md`, the `AUTHOR RULING, 2026-09-11`
block; `latex/rational_quivers.tex` blob `5d6c52f → af777c9`) this declaration disclosed a
`JUSTIFIED_REFORMULATION` in three items, and every one of them is now a statement the source
itself prints:

* **`AN-40`.** `eq:pmsquarerootsinverses` was printed as
  `φ_∓ ∘ (φ^{(∞)}_∓)^{1/2} = ((φ^{(∞)}_±)^{1/2})^{-1} ∘ φ_±`, which did not type-check (its left
  side was a map `V(∓) → V(±)` and its right side applied an endomorphism of `V(±)` to
  `φ_±(V(±)) ⊆ V(∓)`); the tree rendered the gloss printed below it instead. The source now prints
  that gloss in the display — the trailing `φ_±` became `φ_∓` — so `C22` agrees with it verbatim.
  The companion `(φ^{(∞),c}_∓)^{1/2}` slip six lines below is gone with the display it lived in.
* **`AN-41`.** The final sentence claimed `(𝟏_{V(+)}, X⋆, 𝟏_{V(−)})` was an isomorphism, which on
  its two left-hand edges read `X⋆ φ_{a₋} = φ_{a₋}` and `φ_{b₋} X⋆ = φ_{b₋}` — false whenever
  `ñ_⋆ ≠ 0`. The tree rendered a corrected third component `X⋆^{(−)}` (`R-S8-17`). The sentence is
  **deleted** in the amended source, so there is nothing left to correct: `essSurj_C25` was
  retired with it, and `C24`'s single triple is what the proof now concludes with.
* **`AN-42`.** `eq:limitsquarerootdiagram0`/`1` were printed with the same row top and bottom and
  `𝟏_{V(⋆)}` on the middle vertical, correct only when `X⋆ = 𝟏`. The tree rendered the Option-A
  repair coordinator ruling `R-S8-23` directed — the split middle vertical `(X⋆)^{±1/2}` and a
  "commutes iff" conjunct. The author ruled **Option B**: one diagram, `𝔼_{ℚ[√-1]}(M)` over `V`,
  middle vertical `X⋆^{1/2}`. `C23`/`C24` are re-stated accordingly and the tree is off `R-S8-23`.

What the source said before that ruling is kept, compiled and dated, in the two refutation probes
`EssSurjData.C23_printed_forces_AN41` and `EssSurjData.C24_printed_forces_trivial_xStar`, and in
the Option-A squares `sqrtDiag0_edgeBp`/`sqrtDiag0_edgeAp`, which remain true as helper identities.

@census    none (auxiliary; discharges census clauses `RQ-5.05-C17` … `RQ-5.05-C25`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C17, RQ-5.05-C18, RQ-5.05-C19, RQ-5.05-C20, RQ-5.05-C21, RQ-5.05-C22, RQ-5.05-C23, RQ-5.05-C24, RQ-5.05-C25
@imports   none
@divergence none -/
theorem essSurj_naturalIsomorphism (V : Gelfand.RationalStructure.RepNilQ hcard) (D : EssSurjData hcard hℓ V) :
    -- `C17`
    ((∃ (γ : ℚ) (n : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1)), 0 < γ ∧ IsNilpotent n ∧
        Commute n (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) 1) ∧
        D.transport D.toStarLo D.toStarHi ((2 : Dq.carrier) ^ (ℓ - 1) • D.setup.weight.X ^ (ℓ - 1))
            (fun v hv => Submodule.smul_mem _ _ (Split.xpow_maps D.setup.toQiSetup hℓ v hv))
          = (algebraMap ℚ Dq.carrier γ) • 1 + n) ∧
      (∃ (γ' : ℚ) (n : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1)), γ' ≠ 0 ∧ IsNilpotent n ∧
        D.xStarV = (algebraMap ℚ Dq.carrier γ') • (1 + n))) ∧
    -- `C18`
    (D.xStarV = D.yStarV ∧
      (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1, Vphi hcard V 1 (D.xStarV ((Vphi hcard V 1).symm x)) = D.xStarV x) ∧
      (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1, Vphi hcard V 1 (D.limStarV ((Vphi hcard V 1).symm x)) = D.limStarV x)) ∧
    -- `C19` = `eq:phistaridentity`
    (D.limStarV * D.limStarV = 1 ∧ IsNilpotent (D.limStarV - 1) ∧ D.limStarV = 1) ∧
    -- `C20` = `eq:starsquarerootsinverses`, and the induced structure on `V(⋆)` is `φ_⋆`
    (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limStarV = 1 ∧
      ∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1, D.phiV 1 x = Vphi hcard V 1 x) ∧
    -- `C21`
    (IsNilpotent (D.limPlusV - 1) ∧ IsNilpotent (D.limMinusV - 1) ∧
      (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV) ^ 2 = D.limPlusV ∧
      IsNilpotent (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV - 1) ∧
      (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV) ^ 2 = D.limMinusV ∧
      IsNilpotent (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV - 1)) ∧
    -- `C22` = `eq:pmsquarerootsinverses`
    ((∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2,
        Vphi hcard V 2 (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV x)
          = linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV)
              (Vphi hcard V 2 x)) ∧
      (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0,
        Vphi hcard V 0 (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV x)
          = linInv (Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV)
              (Vphi hcard V 0 x))) ∧
    -- `C23`: the amended source's ONE square-root diagram — top row `𝔼_{ℚ[√-1]}(M)`, bottom row
    -- `V`, verticals `(s₋, t, s₊)` — commutes, all four squares with the SAME middle vertical
    -- `t = X⋆^{1/2}` (`AN-42`, the author's Option-B ruling of 2026-09-11; `essSurj_C23`).
    (let sPlus := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV
     let sMinus := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV
     let tStar := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.xStarV
     (∀ x, tStar (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (sMinus x)) ∧
     (∀ x, sMinus (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (tStar x)) ∧
     (∀ x, sPlus (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV x)) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (tStar x)) ∧
     (∀ x, tStar (linInv D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x)) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (sPlus x))) ∧
    -- `C24` (carrying the retired `C25`): `(s₊, t, s₋)` is an isomorphism of quiver
    -- representations `𝔼_{ℚ[√-1]}(M) → V` and of `ℚ`-rational representations
    -- `𝔼_ℚ(M) → (V, φ_•)`, compatible at all THREE vertices (`essSurj_C24`).
    (let sPlus := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limPlusV
     let sMinus := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.limMinusV
     let tStar := Unipotent.sqrt (two_ne_zero_of_base (K := E) two_ne_zero) D.xStarV
     (IsUnit sPlus ∧ IsUnit sMinus ∧ IsUnit tStar ∧
       (∀ x, tStar (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (sMinus x)) ∧
       (∀ x, sMinus (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 x) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (tStar x)) ∧
       (∀ x, sPlus (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV x)) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (tStar x)) ∧
       (∀ x, tStar (linInv D.xStarV (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x)) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (sPlus x))) ∧
     (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2, sMinus (D.phiV 2 (linInv sPlus x)) = Vphi hcard V 2 x) ∧
     (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0, sPlus (D.phiV 0 (linInv sMinus x)) = Vphi hcard V 0 x) ∧
     (∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1, tStar (D.phiV 1 (linInv tStar x)) = Vphi hcard V 1 x)) :=
  ⟨Split.essSurj_C17 hℓ (Gelfand.RationalStructure.toSplitW hcard V) D.toSplitEssSurjData,
    ⟨(essSurj_C18_xStar (V := V) (D := D)).1, (essSurj_C18_xStar (V := V) (D := D)).2,
      fun x => D.limStarV_conj x⟩,
    D.essSurj_C19, D.essSurj_C20, D.essSurj_C21, D.essSurj_C22, D.essSurj_C23, D.essSurj_C24⟩


/-! ### Engine `E8` — the four edges of `𝔼_ℚ(M_D)`, read on `V`

`essSurj_exists` produces the module and `essSurj_naturalIsomorphism` the identities its
comparison triple satisfies.  What is still missing between them and `Functor.EssSurj` is the
DICTIONARY: what the four edge maps of `𝔼_ℚ(M_D)` — `a₋ ↦ X`, `b₋ ↦ Y`, `a₊ ↦ X⋆⁻¹Y`,
`b₊ ↦ XX⋆` (`E_Qi_edge`) — are when read on `V(•)` through `C9`'s identifications.

The answer, and it is exactly what the pins were for: `a₋` and `b₋` are `φ_{a₋}` and `φ_{b₋}` on
the nose, while `a₊` and `b₊` are `φ_{a₊}` and `φ_{b₊}` **twisted by `X⋆`** — `a₊` post-composed
with `X⋆` and `b₊` pre-composed with it.  That twist is the whole reason the comparison triple
carries `(X⋆)^{1/2}` at the `⋆` vertex and not `𝟏` — `AN-42`, and since the author's Option-B
ruling of 2026-09-11 it is what the source's own one diagram prints.
-/

section E8


namespace EssSurjData

variable {hcard hℓ} {V : Gelfand.RationalStructure.RepNilQ hcard} (D : EssSurjData hcard hℓ V)

/-- `X⋆` read at the low `⋆` component.  @census none (helper; engine `E8`) -/
theorem toStarHi_xStar (z : D.setup.weight.comp (-((ℓ : ℤ) - 1)))
    (hxz : Split.xStar D.setup.toQiSetup (z : D.carrier) ∈ D.setup.weight.comp ((ℓ : ℤ) - 1)) :
    D.toStarHi ⟨Split.xStar D.setup.toQiSetup (z : D.carrier), hxz⟩ = D.xStarV (D.toStarLo z) := by
  exact (Split.xStarV_toStarLo D.toSplitEssSurjData z).symm

/-- `X⋆` transports `M_{-(ℓ-1)}` onto `M_{ℓ-1}`: reading `X⋆⁻¹w` at the low `⋆` component and
applying `X⋆V` gives `w` read at the high one.  @census none (helper; engine `E8`) -/
theorem xStarV_toStarLo (z : D.setup.weight.comp (-((ℓ : ℤ) - 1)))
    (w : D.carrier) (hw : w ∈ D.setup.weight.comp ((ℓ : ℤ) - 1))
    (hz : Split.xStar D.setup.toQiSetup (z : D.carrier) = w) :
    D.xStarV (D.toStarLo z) = D.toStarHi ⟨w, hw⟩ := by
  subst hz
  exact (D.toStarHi_xStar z hw).symm

/-- `a₋`: `X|_{M(-)} = φ_{a₋}` on the nose (pin `X_bdry_minus`).
@census none (helper; engine `E8`) -/
theorem edgeRead_aMinus (m : Split.V3 D.setup.toQiSetup 0) :
    D.toStarLo (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 0 m)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (D.toMinus m) := by
  have h : (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 0 m)
      = D.toStarLo.symm (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (D.toMinus m)) :=
    Subtype.ext (D.X_bdry_minus m.1 m.2)
  rw [h, LinearEquiv.apply_symm_apply]

/-- `b₋`: `Y|_{M(⋆)} = φ_{b₋}` on the nose (pin `Y_bdry_minus`).
@census none (helper; engine `E8`) -/
theorem edgeRead_bMinus (m : Split.V3 D.setup.toQiSetup 1) :
    D.toMinus (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 1 m)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (D.toStarLo m) := by
  have h : (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 1 m)
      = D.toMinus.symm (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (D.toStarLo m)) :=
    Subtype.ext (D.Y_bdry_minus m.1 m.2)
  rw [h, LinearEquiv.apply_symm_apply]

/-- `b₊`: `X X⋆|_{M(⋆)} = φ_{b₊} ∘ X⋆` (pin `X_bdry_plus`).
@census none (helper; engine `E8`) -/
theorem edgeRead_bPlus (m : Split.V3 D.setup.toQiSetup (RQuiver.gelfand.source 3)) :
    D.toPlus (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 3 m)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV (D.toStarLo m)) := by
  have hm2 : (m : D.carrier) ∈ D.setup.weight.comp (-((ℓ : ℤ) - 1)) := m.2
  have hmem : Split.xStar D.setup.toQiSetup m.1 ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) :=
    Split.xStar_mem (Q := D.setup.toQiSetup) (by ring) hℓ hm2
  have hstar := D.toStarHi_xStar m hmem
  have h : (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 3 m)
      = D.toPlus.symm (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (D.xStarV (D.toStarLo m))) := by
    refine Subtype.ext ?_
    rw [← hstar]
    exact D.X_bdry_plus (Split.xStar D.setup.toQiSetup m.1) hmem
  rw [h, LinearEquiv.apply_symm_apply]

/-- `a₊`: `X⋆ ∘ (X⋆⁻¹ Y)|_{M(+)} = φ_{a₊}` (pin `Y_bdry_plus` and `xStar_xStarInv`).
@census none (helper; engine `E8`) -/
theorem edgeRead_aPlus (m : Split.V3 D.setup.toQiSetup (RQuiver.gelfand.source 2)) :
    D.xStarV (D.toStarLo (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 2 m))
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (D.toPlus m) := by
  have hm2 : (m : D.carrier) ∈ D.setup.weight.comp ((ℓ : ℤ) + 1) := m.2
  have hy : D.setup.weight.Y m.1 ∈ D.setup.weight.comp ((ℓ : ℤ) - 1) :=
    Split.y_mem (Q := D.setup.toQiSetup) (m := (ℓ : ℤ) + 1) (by ring) hm2
  refine Eq.trans (D.xStarV_toStarLo
    (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 2 m)
    (D.setup.weight.Y m.1) hy
    (Split.xStar_xStarInv D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) _ hy)) ?_
  have h : (⟨D.setup.weight.Y m.1, hy⟩ : D.setup.weight.comp ((ℓ : ℤ) - 1))
      = D.toStarHi.symm (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (D.toPlus m)) :=
    Subtype.ext (D.Y_bdry_plus m.1 hm2)
  rw [h, LinearEquiv.apply_symm_apply]

end EssSurjData

/-! #### The comparison triple as a map of representations -/

/-- `2 ≠ 0` in `ℚ[√-1]`, named so that every square root below is taken with the SAME proof term
and `rw` matches.  @census none (helper; engine `E8`) -/
theorem qiTwo : (2 : Dq.carrier) ≠ 0 := two_ne_zero_of_base (K := E) two_ne_zero

namespace EssSurjData

variable {hcard hℓ} {V : Gelfand.RationalStructure.RepNilQ hcard} (D : EssSurjData hcard hℓ V)

/-- **The comparison triple**, `C9`'s identifications followed by `((φ^{(∞)}_-)^{1/2}, (X⋆)^{1/2},
(φ^{(∞)}_+)^{1/2})` — the vertex components of the candidate isomorphism `𝔼_ℚ(M_D) → V`.
@census none (helper; engine `E8`)
@clauses   RQ2-5.12-S-O23 -/
noncomputable def natPsi : ∀ v : Fin 3, Split.V3 D.setup.toQiSetup v →ₗ[Dq.carrier] Split.VM (Gelfand.RationalStructure.toSplitW hcard V) v
  | 0 => (Unipotent.sqrt qiTwo D.limMinusV).comp D.toMinus.toLinearMap
  | 1 => (Unipotent.sqrt qiTwo D.xStarV).comp D.toStarLo.toLinearMap
  | 2 => (Unipotent.sqrt qiTwo D.limPlusV).comp D.toPlus.toLinearMap

/-- The inverse triple.  @census none (helper; engine `E8`) -/
noncomputable def natPsiInv : ∀ v : Fin 3, Split.VM (Gelfand.RationalStructure.toSplitW hcard V) v →ₗ[Dq.carrier] Split.V3 D.setup.toQiSetup v
  | 0 => D.toMinus.symm.toLinearMap.comp (linInv (Unipotent.sqrt qiTwo D.limMinusV))
  | 1 => D.toStarLo.symm.toLinearMap.comp (linInv (Unipotent.sqrt qiTwo D.xStarV))
  | 2 => D.toPlus.symm.toLinearMap.comp (linInv (Unipotent.sqrt qiTwo D.limPlusV))

/-- @census none (helper; engine `E8`) -/
theorem sqrtLimPlusV_isUnit : IsUnit (Unipotent.sqrt qiTwo D.limPlusV) :=
  (Unipotent.sqrt_spec qiTwo D.limPlusV (D.limPlusV - 1) D.limPlusV_unipotent (by abel)).1

/-- @census none (helper; engine `E8`) -/
theorem sqrtLimMinusV_isUnit : IsUnit (Unipotent.sqrt qiTwo D.limMinusV) :=
  (Unipotent.sqrt_spec qiTwo D.limMinusV (D.limMinusV - 1) D.limMinusV_unipotent (by abel)).1

/-- `a₋` intertwines.  @census none (helper; engine `E8`) -/
theorem natPsi_edge0 (m : Split.V3 D.setup.toQiSetup (RQuiver.gelfand.source 0)) :
    natPsi D 1 (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 0 m)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (natPsi D 0 m) := by
  show Unipotent.sqrt qiTwo D.xStarV
      (D.toStarLo (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 0 m))
    = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (Unipotent.sqrt qiTwo D.limMinusV (D.toMinus m))
  rw [D.edgeRead_aMinus m, D.sqrtDiag_edgeAm qiTwo]

/-- `b₋` intertwines.  @census none (helper; engine `E8`) -/
theorem natPsi_edge1 (m : Split.V3 D.setup.toQiSetup (RQuiver.gelfand.source 1)) :
    natPsi D 0 (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 1 m)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (natPsi D 1 m) := by
  show Unipotent.sqrt qiTwo D.limMinusV
      (D.toMinus (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 1 m))
    = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (Unipotent.sqrt qiTwo D.xStarV (D.toStarLo m))
  rw [D.edgeRead_bMinus m, D.sqrtDiag_edgeBm qiTwo]

/-- `a₊` intertwines.  @census none (helper; engine `E8`) -/
theorem natPsi_edge2 (m : Split.V3 D.setup.toQiSetup (RQuiver.gelfand.source 2)) :
    natPsi D 1 (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 2 m)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (natPsi D 2 m) := by
  show Unipotent.sqrt qiTwo D.xStarV
      (D.toStarLo (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 2 m))
    = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (Unipotent.sqrt qiTwo D.limPlusV (D.toPlus m))
  rw [D.sqrtDiag_edgeAp qiTwo, ← D.edgeRead_aPlus m, ← ring_inverse_eq_linInv,
    D.sqrtXStarV_inv_xStarV qiTwo]

/-- `b₊` intertwines.  @census none (helper; engine `E8`) -/
theorem natPsi_edge3 (m : Split.V3 D.setup.toQiSetup (RQuiver.gelfand.source 3)) :
    natPsi D 2 (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 3 m)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (natPsi D 1 m) := by
  show Unipotent.sqrt qiTwo D.limPlusV
      (D.toPlus (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ 3 m))
    = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (Unipotent.sqrt qiTwo D.xStarV (D.toStarLo m))
  rw [D.edgeRead_bPlus m, D.sqrtDiag0_edgeBp qiTwo, ← ring_inverse_eq_linInv,
    D.xStarV_sqrtXStarV_inv qiTwo]

/-! #### `E8`'s `rational` field, part 1: the `⋆` vertex commutes with `(X⋆)^{1/2}`

`C24`(b) at `⋆` says `D.phiV 1 = Vphi 1` on the nose, so the `rational` field at `⋆` reduces to
the statement that the comparison map's `⋆` component `(X⋆)^{1/2}` COMMUTES with `φ_{⋆,c}`.  That
is `c`-invariance of the square root, and `Vphi_comm_of_conjStar` turns it into
`conjStar ((X⋆)^{1/2}) = (X⋆)^{1/2}`, which `sqrt_unique` gives from three facts about
`conjStar`: it is multiplicative, it fixes `1`, and it fixes `X⋆` (`conjStar_xStarAt`).
`DESIGN-NOTES.md` §17.4(c), obstacle 1 — closed WITHOUT `conjBy_sqrtOfScalarPlusNilpotent`, whose
`γ = 1` specialisation is what would not normalise. -/

/-- `c`-conjugation at `⋆` is additive on differences.  @census none (helper; engine `E8`) -/
theorem conjStar_sub' (a b : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1)) :
    conjStar hcard V (a - b) = conjStar hcard V a - conjStar hcard V b := by
  ext x
  simp [conjStar, conjBy]

/-- `X⋆ − 𝟏` is nilpotent, at the constructed datum.  @census none (helper; engine `E8`) -/
theorem xStarV_sub_one_isNilpotent : IsNilpotent (D.xStarV - 1) := by
  obtain ⟨n, hn, -, heq⟩ := Split.xStarAt_eq_one_add hℓ (Gelfand.RationalStructure.toSplitW hcard V) 1
  rw [D.xStarV_eq, heq]
  simpa using hn

/-- **`DESIGN-NOTES.md` §17.4(c), obstacle 1.**  `c` fixes `(X⋆)^{1/2}`.
@census none (helper; engine `E8`) -/
theorem conjStar_sqrt_xStarV :
    conjStar hcard V (Unipotent.sqrt qiTwo D.xStarV) = Unipotent.sqrt qiTwo D.xStarV := by
  obtain ⟨-, hnil, hsq⟩ := Unipotent.sqrt_spec qiTwo D.xStarV (D.xStarV - 1)
    D.xStarV_sub_one_isNilpotent (by abel)
  refine Unipotent.sqrt_unique qiTwo D.xStarV
    (conjStar hcard V (Unipotent.sqrt qiTwo D.xStarV))
    (conjStar hcard V (Unipotent.sqrt qiTwo D.xStarV - 1))
    (conjBy_isNilpotent Dq.conj (Vphi hcard V 1) (Vphi_smul hcard V 1) hnil) ?_ ?_
  · rw [conjStar_sub', conjStar_one]
    abel
  · rw [sq, ← conjStar_mul, ← sq, hsq, D.xStarV_eq, conjStar_xStarAt]

/-- `φ_{⋆,c}` commutes with `(X⋆)^{1/2}` — the `⋆` half of the `rational` field.
@census none (helper; engine `E8`) -/
theorem Vphi_sqrt_xStarV (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Vphi hcard V 1 (Unipotent.sqrt qiTwo D.xStarV x)
      = Unipotent.sqrt qiTwo D.xStarV (Vphi hcard V 1 x) :=
  Vphi_comm_of_conjStar hcard V D.conjStar_sqrt_xStarV x

end EssSurjData

/-! #### `E8`'s `rational` field, part 2: the comparison map is a morphism, and an isomorphism

`DESIGN-NOTES.md` §17.4(c)'s recipe, executed.  Three layers.

1. **The transport layer.**  `rational_of_phi'` says that the `Rep.Hom` field
   `ψ_{σ v} ∘ φ^M_{v,σ} = φ^N_{v,σ} ∘ ψ_v` follows from the same identity read at ANY named target
   vertex `w` with a proof `σ • v = w`; `subst` on that proof is what turns the un-reducible
   `σ • v` into `2`, `1` or `0`.  `repEqCast_val`/`repPhi'_val` give the carrier VALUE of the
   transported structure map — the "state the value lemma with the transported element explicit"
   device of §17.4(c), obstacle 2.
2. **The three vertices.**  `phiV_zero_val`/`phiV_one_val`/`phiV_two_val` compare the two subtypes
   by `Subtype.ext` on values rather than by rewriting inside `⟨_, _⟩` — the second half of
   obstacle 2's fix, since `phiV`'s own membership proof mentions the term being rewritten.  With
   them, `natPsi_rational_conj` is `C24`(b) at each vertex, plus `Vphi_sqrt_xStarV` at `⋆`.
3. **The isomorphism.**  `natPsi` and `natPsiInv` are mutually inverse (the three square roots are
   units, the three identifications are `LinearEquiv`s), so `repHomInv` produces the inverse
   morphism and `natIsoFD` the isomorphism of `Rep(Γ_ℚ)`; `ObjectProperty.isoMk` lifts it to the
   full subcategory `Rep^nil(Γ_ℚ)`. -/

section E8Rational

variable {hcard hℓ}

/-- Transport in `𝔼_ℚ(M)` is the identity on carrier values.  @census none (helper; engine `E8`) -/
theorem repEqCast_val {A : HCEObj ℓ E Dq} (hA : Gelfand.RationalStructure.ObjSpec hcard hℓ A) {v w : (Gelfand.RationalStructure.gelfandQ hcard).V}
    (h : v = w) (m : Split.V3 A.qi v) :
    (((Gelfand.Equivalence.E_Q_rep hcard hℓ A hA).eqCast h m : Split.V3 A.qi w)).1 = m.1 := by
  subst h; rfl

/-- The transported `c`-structure of `𝔼_ℚ(M)`, on carrier values: it is `φ_{v,c}`.
@census none (helper; engine `E8`) -/
theorem repPhi'_val {A : HCEObj ℓ E Dq} (hA : Gelfand.RationalStructure.ObjSpec hcard hℓ A) {v w : (Gelfand.RationalStructure.gelfandQ hcard).V}
    (h : Dq.conj • v = w) (m : Split.V3 A.qi v) :
    (((Gelfand.Equivalence.E_Q_rep hcard hℓ A hA).φ' Dq.conj h m : Split.V3 A.qi w)).1 = Gelfand.RationalStructure.phiC hℓ A v m.1 := by
  rw [RationalQuiver.Rep.φ'_apply, repEqCast_val hA h]
  show Gelfand.Equivalence.galAct hℓ A Dq.conj v m.1 = _
  rw [Gelfand.Equivalence.galAct_of_ne hℓ A Gelfand.RationalStructure.galConj_ne_one]

/-- **`Rep.Hom`'s `rational` field, read at a NAMED target vertex.**  `Rep.Hom` states it at the
un-reducible `σ • v`; every proof of it is by cases on `v`, which needs `σ • v` replaced by a
literal.  `subst` on `hvw` does exactly that, and `Rep.φ'_rfl` closes the residue.
@census none (helper; engine `E8`) -/
theorem rational_of_phi' {M N : RationalQuiver.Rep (Gelfand.RationalStructure.gelfandQ hcard)}
    (psi : ∀ v : (Gelfand.RationalStructure.gelfandQ hcard).V, M.M v →ₗ[Dq.carrier] N.M v)
    {σ : Dq.carrier ≃ₐ[E] Dq.carrier} {v w : (Gelfand.RationalStructure.gelfandQ hcard).V} (hvw : σ • v = w)
    (m : M.M v) (H : psi w (M.φ' σ hvw m) = N.φ' σ hvw (psi v m)) :
    psi (σ • v) (M.φ σ v m) = N.φ σ v (psi v m) := by
  subst hvw; exact H

/-- **A `Rep.Hom` whose vertex components are invertible has an inverse `Rep.Hom`**: the inverse's
`edge` and `rational` fields are the originals' applied to the preimages.
@census none (helper; engine `E8`) -/
def repHomInv {M N : RationalQuiver.Rep (Gelfand.RationalStructure.gelfandQ hcard)}
    (f : RationalQuiver.Rep.Hom M N)
    (g : ∀ v : (Gelfand.RationalStructure.gelfandQ hcard).V, N.M v →ₗ[Dq.carrier] M.M v)
    (hgf : ∀ v x, g v (f.ψ v x) = x) (hfg : ∀ v y, f.ψ v (g v y) = y) :
    RationalQuiver.Rep.Hom N M where
  ψ := g
  edge e m := by
    have h := f.edge e (g _ m)
    rw [hfg] at h
    rw [← h, hgf]
  rational σ v m := by
    have h := f.rational σ v (g v m)
    rw [hfg] at h
    rw [← h, hgf]

namespace EssSurjData

variable {V : Gelfand.RationalStructure.RepNilQ hcard} (D : EssSurjData hcard hℓ V)

/-- `φ^M_{-,c}` read on `V(−)`, with the argument presented as `D.toMinus m`.
@census none (helper; engine `E8`) -/
theorem phiV_zero_val (m : D.setup.weight.comp (-((ℓ : ℤ) + 1))) :
    D.phiV 0 (D.toMinus m)
      = D.toPlus ⟨Gelfand.RationalStructure.phiC hℓ D.toHCQObj 0 (m : D.carrier), Gelfand.RationalStructure.phiC_mem hℓ D.toHCQObj 0 _⟩ := by
  show D.toPlus ⟨Gelfand.RationalStructure.phiC hℓ D.toHCQObj 0
      ((D.toMinus.symm (D.toMinus m) : D.setup.weight.comp (-((ℓ : ℤ) + 1))) : D.carrier), _⟩ = _
  exact congrArg D.toPlus (Subtype.ext (congrArg
    (fun z : D.setup.weight.comp (-((ℓ : ℤ) + 1)) => Gelfand.RationalStructure.phiC hℓ D.toHCQObj 0 (z : D.carrier))
    (D.toMinus.symm_apply_apply m)))

/-- `φ^M_{+,c}` read on `V(+)`.  @census none (helper; engine `E8`) -/
theorem phiV_two_val (m : D.setup.weight.comp ((ℓ : ℤ) + 1)) :
    D.phiV 2 (D.toPlus m)
      = D.toMinus ⟨Gelfand.RationalStructure.phiC hℓ D.toHCQObj 2 (m : D.carrier), Gelfand.RationalStructure.phiC_mem hℓ D.toHCQObj 2 _⟩ := by
  show D.toMinus ⟨Gelfand.RationalStructure.phiC hℓ D.toHCQObj 2
      ((D.toPlus.symm (D.toPlus m) : D.setup.weight.comp ((ℓ : ℤ) + 1)) : D.carrier), _⟩ = _
  exact congrArg D.toMinus (Subtype.ext (congrArg
    (fun z : D.setup.weight.comp ((ℓ : ℤ) + 1) => Gelfand.RationalStructure.phiC hℓ D.toHCQObj 2 (z : D.carrier))
    (D.toPlus.symm_apply_apply m)))

/-- `φ^M_{⋆,c}` read on `V(⋆)`.  @census none (helper; engine `E8`) -/
theorem phiV_one_val (m : D.setup.weight.comp (-((ℓ : ℤ) - 1))) :
    D.phiV 1 (D.toStarLo m)
      = D.toStarLo ⟨Gelfand.RationalStructure.phiC hℓ D.toHCQObj 1 (m : D.carrier), Gelfand.RationalStructure.phiC_mem hℓ D.toHCQObj 1 _⟩ := by
  show D.toStarLo ⟨Gelfand.RationalStructure.phiC hℓ D.toHCQObj 1
      ((D.toStarLo.symm (D.toStarLo m) : D.setup.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier), _⟩ = _
  exact congrArg D.toStarLo (Subtype.ext (congrArg
    (fun z : D.setup.weight.comp (-((ℓ : ℤ) - 1)) => Gelfand.RationalStructure.phiC hℓ D.toHCQObj 1 (z : D.carrier))
    (D.toStarLo.symm_apply_apply m)))

/-- **`DESIGN-NOTES.md` §17.4(c), obstacle 2 — closed.**  The comparison triple intertwines the
two `c`-structures, at each of the three vertices: at `±` by `C24`(b)'s two conjugation conjuncts
(the `linInv` cancels because `(φ^{(∞)}_∓)^{1/2}` is a unit), at `⋆` by `C24`(b)'s third conjunct
together with `Vphi_sqrt_xStarV` (obstacle 1).  @census none (helper; engine `E8`) -/
theorem natPsi_rational_conj (hA : Gelfand.RationalStructure.ObjSpec hcard hℓ D.toHCQObj) (v : Fin 3)
    (m : Split.V3 D.toHCQObj.qi v) :
    natPsi D (RQuiver.gelfandVertexSwap v)
        ((Gelfand.Equivalence.E_Q_rep hcard hℓ D.toHCQObj hA).φ' Dq.conj (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard v) m)
      = Vphi hcard V v (natPsi D v m) := by
  fin_cases v
  · have hb : D.toPlus ((Gelfand.Equivalence.E_Q_rep hcard hℓ D.toHCQObj hA).φ' Dq.conj
        (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 0) m) = D.phiV 0 (D.toMinus m) := by
      rw [D.phiV_zero_val m]
      exact congrArg D.toPlus (Subtype.ext (repPhi'_val hA _ m))
    have hC24 : ∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0,
        Unipotent.sqrt qiTwo D.limPlusV (D.phiV 0 (linInv (Unipotent.sqrt qiTwo D.limMinusV) x))
          = Vphi hcard V 0 x := D.essSurj_C24.2.2.1
    have hC := hC24 (Unipotent.sqrt qiTwo D.limMinusV (D.toMinus m))
    rw [← ring_inverse_eq_linInv, inverse_end_apply D.sqrtLimMinusV_isUnit] at hC
    show Unipotent.sqrt qiTwo D.limPlusV (D.toPlus ((Gelfand.Equivalence.E_Q_rep hcard hℓ D.toHCQObj hA).φ' Dq.conj
        (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 0) m))
      = Vphi hcard V 0 (Unipotent.sqrt qiTwo D.limMinusV (D.toMinus m))
    rw [hb]
    exact hC
  · have hb : D.toStarLo ((Gelfand.Equivalence.E_Q_rep hcard hℓ D.toHCQObj hA).φ' Dq.conj
        (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 1) m) = D.phiV 1 (D.toStarLo m) := by
      rw [D.phiV_one_val m]
      exact congrArg D.toStarLo (Subtype.ext (repPhi'_val hA _ m))
    -- `C20`'s second conjunct, not `C24`'s: under the author's Option-B ruling of 2026-09-11
    -- `C24`'s `⋆` conjunct is the conjugation `t φ^M_⋆ t⁻¹ = φ_⋆`, and the on-the-nose equality
    -- this step needs is `essSurj_C20.2` (`eq:starsquarerootsinverses`), where it always lived.
    have hC20 : ∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1, D.phiV 1 x = Vphi hcard V 1 x := D.essSurj_C20.2
    show Unipotent.sqrt qiTwo D.xStarV (D.toStarLo ((Gelfand.Equivalence.E_Q_rep hcard hℓ D.toHCQObj hA).φ' Dq.conj
        (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 1) m))
      = Vphi hcard V 1 (Unipotent.sqrt qiTwo D.xStarV (D.toStarLo m))
    rw [hb, hC20, D.Vphi_sqrt_xStarV]
  · have hb : D.toMinus ((Gelfand.Equivalence.E_Q_rep hcard hℓ D.toHCQObj hA).φ' Dq.conj
        (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 2) m) = D.phiV 2 (D.toPlus m) := by
      rw [D.phiV_two_val m]
      exact congrArg D.toMinus (Subtype.ext (repPhi'_val hA _ m))
    have hC24 : ∀ x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2,
        Unipotent.sqrt qiTwo D.limMinusV (D.phiV 2 (linInv (Unipotent.sqrt qiTwo D.limPlusV) x))
          = Vphi hcard V 2 x := D.essSurj_C24.2.1
    have hC := hC24 (Unipotent.sqrt qiTwo D.limPlusV (D.toPlus m))
    rw [← ring_inverse_eq_linInv, inverse_end_apply D.sqrtLimPlusV_isUnit] at hC
    show Unipotent.sqrt qiTwo D.limMinusV (D.toMinus ((Gelfand.Equivalence.E_Q_rep hcard hℓ D.toHCQObj hA).φ' Dq.conj
        (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 2) m))
      = Vphi hcard V 2 (Unipotent.sqrt qiTwo D.limPlusV (D.toPlus m))
    rw [hb]
    exact hC

/-- `natPsiInv` is a left inverse of `natPsi`.  @census none (helper; engine `E8`) -/
theorem natPsiInv_natPsi : ∀ (v : Fin 3) (x : Split.V3 D.setup.toQiSetup v),
    natPsiInv D v (natPsi D v x) = x
  | 0, x => by
    show D.toMinus.symm (linInv (Unipotent.sqrt qiTwo D.limMinusV)
      (Unipotent.sqrt qiTwo D.limMinusV (D.toMinus x))) = x
    rw [← ring_inverse_eq_linInv, inverse_end_apply D.sqrtLimMinusV_isUnit,
      D.toMinus.symm_apply_apply]
  | 1, x => by
    show D.toStarLo.symm (linInv (Unipotent.sqrt qiTwo D.xStarV)
      (Unipotent.sqrt qiTwo D.xStarV (D.toStarLo x))) = x
    rw [← ring_inverse_eq_linInv, inverse_end_apply (D.sqrtXStarV_isUnit qiTwo),
      D.toStarLo.symm_apply_apply]
  | 2, x => by
    show D.toPlus.symm (linInv (Unipotent.sqrt qiTwo D.limPlusV)
      (Unipotent.sqrt qiTwo D.limPlusV (D.toPlus x))) = x
    rw [← ring_inverse_eq_linInv, inverse_end_apply D.sqrtLimPlusV_isUnit,
      D.toPlus.symm_apply_apply]

/-- `natPsiInv` is a right inverse of `natPsi`.  @census none (helper; engine `E8`) -/
theorem natPsi_natPsiInv : ∀ (v : Fin 3) (y : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) v),
    natPsi D v (natPsiInv D v y) = y
  | 0, y => by
    show Unipotent.sqrt qiTwo D.limMinusV (D.toMinus (D.toMinus.symm
      (linInv (Unipotent.sqrt qiTwo D.limMinusV) y))) = y
    rw [D.toMinus.apply_symm_apply, ← ring_inverse_eq_linInv,
      end_inverse_apply D.sqrtLimMinusV_isUnit]
  | 1, y => by
    show Unipotent.sqrt qiTwo D.xStarV (D.toStarLo (D.toStarLo.symm
      (linInv (Unipotent.sqrt qiTwo D.xStarV) y))) = y
    rw [D.toStarLo.apply_symm_apply, ← ring_inverse_eq_linInv,
      end_inverse_apply (D.sqrtXStarV_isUnit qiTwo)]
  | 2, y => by
    show Unipotent.sqrt qiTwo D.limPlusV (D.toPlus (D.toPlus.symm
      (linInv (Unipotent.sqrt qiTwo D.limPlusV) y))) = y
    rw [D.toPlus.apply_symm_apply, ← ring_inverse_eq_linInv,
      end_inverse_apply D.sqrtLimPlusV_isUnit]

/-- The four intertwining conditions of `natPsi`, collected as one statement over the edge index.
@census none (helper; engine `E8`) -/
theorem natPsi_edge_all : ∀ (e : Fin 4) (m : Split.V3 D.setup.toQiSetup (RQuiver.gelfand.source e)),
    natPsi D (RQuiver.gelfand.target e)
        (Split.E_F_edge D.setup.toQiSetup (D.setup.toQiSetup.starInverses hℓ) hℓ e m)
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) e (natPsi D (RQuiver.gelfand.source e) m)
  | 0, m => D.natPsi_edge0 m
  | 1, m => D.natPsi_edge1 m
  | 2, m => D.natPsi_edge2 m
  | 3, m => D.natPsi_edge3 m

/-- **The comparison triple as a morphism of rational representations** `𝔼_ℚ(M_D) → V`.
@census none (helper; engine `E8`) -/
noncomputable def natHom (hA : Gelfand.RationalStructure.ObjSpec hcard hℓ D.toHCQObj) :
    RationalQuiver.Rep.Hom (Gelfand.Equivalence.E_Q_rep hcard hℓ D.toHCQObj hA) V.obj.toRep where
  ψ := natPsi D
  edge e m := D.natPsi_edge_all e m
  rational σ v m := by
    by_cases hσ : σ = 1
    · subst hσ
      refine rational_of_phi' (natPsi D) (one_smul _ v) m ?_
      rw [RationalQuiver.Rep.φ'_one, RationalQuiver.Rep.φ'_one]
      exact RationalQuiver.Rep.eqCast_natural (fun u => natPsi D u) _ m
    · have hg := Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ
      subst hg
      exact rational_of_phi' (natPsi D) (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard v) m
        (D.natPsi_rational_conj hA v m)

/-- The inverse morphism.  @census none (helper; engine `E8`) -/
noncomputable def natHomInv (hA : Gelfand.RationalStructure.ObjSpec hcard hℓ D.toHCQObj) :
    RationalQuiver.Rep.Hom V.obj.toRep (Gelfand.Equivalence.E_Q_rep hcard hℓ D.toHCQObj hA) :=
  repHomInv (D.natHom hA) (fun v => natPsiInv D v)
    (fun v x => D.natPsiInv_natPsi v x) (fun v y => D.natPsi_natPsiInv v y)

/-- **`𝔼_ℚ(M_D) ≅ V` in `Rep(Γ_ℚ)`.**  @census none (helper; engine `E8`) -/
noncomputable def natIsoFD (hA : Gelfand.RationalStructure.ObjSpec hcard hℓ D.toHCQObj) :
    Gelfand.Equivalence.E_Q_fdrep hcard hℓ D.toHCQObj hA ≅ V.obj where
  hom := D.natHom hA
  inv := D.natHomInv hA
  hom_inv_id := RationalQuiver.Rep.Hom.ext
    (funext fun v => LinearMap.ext fun x => D.natPsiInv_natPsi v x)
  inv_hom_id := RationalQuiver.Rep.Hom.ext
    (funext fun v => LinearMap.ext fun y => D.natPsi_natPsiInv v y)

/-- **`𝔼_ℚ(M_D) ≅ V` in `Rep^nil(Γ_ℚ)`.**  @census none (helper; engine `E8`) -/
noncomputable def natIsoObj (hA : Gelfand.RationalStructure.ObjSpec hcard hℓ D.toHCQObj) :
    Gelfand.Equivalence.E_Q_obj hcard hℓ D.toHCQObj hA ≅ V :=
  ObjectProperty.isoMk (Gelfand.RationalStructure.RepNilRelQ hcard) (D.natIsoFD hA)

end EssSurjData

end E8Rational

end E8

/-- **`RQ-5.05-C26`, essential surjectivity** — engine `E8`, closed.  Every nilpotent
`ℚ`-rational representation `V` of `Γ_ℚ` satisfying the relation is isomorphic to `𝔼_ℚ(M)` for the
Harish-Chandra module `M = M_D` that `essSurj_exists` constructs, the isomorphism being the
comparison triple `((φ^{(∞)}_-)^{1/2}, (X⋆)^{1/2}, (φ^{(∞)}_+)^{1/2})` of `C23`/`C24` composed with
`C9`'s identifications.

@census none (auxiliary; the essential-surjectivity half of census clause `RQ-5.05-C26`)
@source thm:EEQQequivalence
(clauses of the frozen original:) RQ-5.05-C26
@imports none
@divergence none -/
theorem E_Q_essSurj (h : Gelfand.RationalStructure.E_QSpec hcard hℓ) : (Gelfand.Equivalence.E_QFunctor hcard hℓ h).EssSurj where
  mem_essImage W := by
    obtain ⟨D⟩ := essSurj_exists hcard hℓ W
    exact ⟨D.toHCQObj, ⟨D.natIsoObj (h.1 _)⟩⟩


end EssSurj

/-! ### The theorem -/

section Main


/-- **`RQ-5.05`** (`thm:EEQQequivalence`) — **Main Theorem C**.

For `ℓ ≥ 1`, the assignment `𝔼_ℚ : M_ℚ ↦ (𝔼_{ℚ[√-1]}(M_{ℚ[√-1]}), φ_•)` from `HC_λ(𝔤,K)_ℚ` to the
category `Rep^nil(Γ_ℚ)` of `ℚ`-rational finite-dimensional nilpotent representations of the
`ℚ`-rational Gelfand quiver is **well defined** (`C1`: its specification `E_QSpec` holds, so
`E_QFunctor` is a functor) and an **equivalence of categories** (`C8`, `C26`): there is an
equivalence whose functor **is** `𝔼_ℚ`, on the nose — the pin S5's `RQ-2.29` uses for `FFunctor`.

@census none (WP-8c field-generic copy; the frozen claimant of RQ-5.05 is unchanged)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-H1, RQ-5.05-H2, RQ-5.05-H3, RQ-5.05-C8, RQ-5.05-C26
@imports   none
@divergence JUSTIFIED_REFORMULATION (the concrete category, ruling `R-S8-6`).  The source category
is the concrete `HC_λ(𝔤,K)_ℚ` of `Gelfand/Category.lean` — S7's `RationalSetup` (the `ℚ`-form with
its base change, components, triple, character and conjugation, i.e. §3.4's standing setup) with
admissibility, finite generation and the central character — whose objects carry their weight
decomposition and whose morphisms are the `(𝔤,K)`-maps; the `Realization` hypothesis and the
opaque `HCInterface` of `fccad35` are gone (verifier `V-S8-8`).  The presentation of the
`ℚ`-objects through their `ℚ[√-1]`-forms with descent datum is the one §3.4 itself adopts and is
equivalent to the category of `ℚ`-forms by `thm:galoisdescent` (`RQ-1.16`); disclosed on
`HCQObj`.  The target carries `ex:gelfand`'s relation (`RepNilRelQ`), which "representation of
the Gelfand quiver" includes.  The three arithmetic facts about `ℚ[√-1]/ℚ` this statement used to
carry as binders — `IsGalois ℚ ℚ[√-1]`, `FiniteDimensional ℚ ℚ[√-1]` and
`hcard : #Gal(ℚ[√-1]/ℚ) = 2` — are **proved in-tree** (`Gelfand/GaloisFacts.lean`:
`Qi.instIsGalois`, `Qi.instFiniteDimensional`, `Dq.card_gal`) and are no longer hypotheses of this
theorem; commission `C-M2-1` against M2 primary-audit finding `F-M2-02`,
`stages/S8/DESIGN-NOTES.md` §25 (renumbered on merge into `main` from this commission's own
working §24, which collided with M2 process repair round 1's own §24, `F-M2-07`, landed the same
day — `m2-merge-resolver`; superseding §3.2's pre-`C-M2-1` measurement). -/
theorem E_Q_equivalence (hℓ : 1 ≤ ℓ) :
    ∃ (h : Gelfand.RationalStructure.E_QSpec Dq.card_gal hℓ) (e : HCEObj ℓ E Dq ≌ Gelfand.RationalStructure.RepNilQ Dq.card_gal),
      e.functor = Gelfand.Equivalence.E_QFunctor Dq.card_gal hℓ h := by
  refine ⟨Gelfand.Equivalence.E_Q_spec Dq.card_gal hℓ, ?_⟩
  haveI := Gelfand.Equivalence.E_Q_full Dq.card_gal hℓ (Gelfand.Equivalence.E_Q_spec Dq.card_gal hℓ)
  haveI := Gelfand.Equivalence.E_Q_faithful Dq.card_gal hℓ (Gelfand.Equivalence.E_Q_spec Dq.card_gal hℓ)
  haveI := E_Q_essSurj Dq.card_gal hℓ (Gelfand.Equivalence.E_Q_spec Dq.card_gal hℓ)
  haveI : (Gelfand.Equivalence.E_QFunctor Dq.card_gal hℓ (Gelfand.Equivalence.E_Q_spec Dq.card_gal hℓ)).IsEquivalence := { }
  exact ⟨(Gelfand.Equivalence.E_QFunctor Dq.card_gal hℓ (Gelfand.Equivalence.E_Q_spec Dq.card_gal hℓ)).asEquivalence, rfl⟩

end Main


/-! ## The native `𝔼_E` on `HC ℓ E D` (stage T3) -/

section NativeHC

set_option linter.unusedSectionVars false

variable {D : ImagUnit E}

/-! ### Two representations of the same quiver with different (equal-valued) rational structures -/

section Reindex

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

/-- `Γ` with its rational structure replaced by `ρ'`.  @census none (helper) -/
def _root_.RationalQuivers.RationalQuiver.withρ (Γ : RationalQuiver K L)
    (ρ' : Gal(L/K) →* RQuiver.Aut Γ.toRQuiver) : RationalQuiver K L where
  toRQuiver := Γ.toRQuiver
  ρ := ρ'
  smooth_V := IsSmooth.of_discreteTopology _
  smooth_E := IsSmooth.of_discreteTopology _

variable {Γ : RationalQuiver K L} {ρ' : Gal(L/K) →* RQuiver.Aut Γ.toRQuiver}

omit [IsGalois K L] [FiniteDimensional K L] in
/-- Sigma-equality after a transport.  @census none (helper) -/
theorem sigma_eqCast (M : RationalQuiver.Rep Γ) {v w : Γ.V} (h : v = w) (x : M.M v) :
    (⟨w, M.eqCast h x⟩ : (u : Γ.V) × M.M u) = ⟨v, x⟩ := by
  subst h; rfl

omit [FiniteDimensional K L] in
/-- `φ` commutes with transport, as sigma-equality.  @census none (helper) -/
theorem sigma_φ_eqCast (M : RationalQuiver.Rep Γ) (σ : Gal(L/K)) {v w : Γ.V} (h : v = w)
    (x : M.M v) :
    (⟨σ • w, M.φ σ w (M.eqCast h x)⟩ : (u : Γ.V) × M.M u) = ⟨σ • v, M.φ σ v x⟩ := by
  subst h; rfl

omit [FiniteDimensional K L] in
/-- A family of linear maps commutes with transport.  @census none (helper) -/
theorem eqCast_natural' {M N : RationalQuiver.Rep Γ} (ψ : ∀ v, M.M v →ₗ[L] N.M v) {v w : Γ.V}
    (h : v = w) (x : M.M v) : ψ w (M.eqCast h x) = N.eqCast h (ψ v x) := by
  subst h; rfl

omit [FiniteDimensional K L] in
/-- `Rep.Hom`'s `rational` field at `σ = 1`, for any family of linear maps.  @census none (helper) -/
theorem rational_one {M N : RationalQuiver.Rep Γ} (ψ : ∀ v, M.M v →ₗ[L] N.M v) (v : Γ.V)
    (m : M.M v) : ψ ((1 : Gal(L/K)) • v) (M.φ 1 v m) = N.φ 1 v (ψ v m) := by
  have h0 : (1 : Gal(L/K)) • v = v := one_smul _ v
  have eM : M.eqCast h0.symm m = M.φ 1 v m :=
    (M.sigma_mk_eq_iff h0.symm m (M.φ 1 v m)).1 (M.smul_one_total ⟨v, m⟩).symm
  have eN : N.eqCast h0.symm (ψ v m) = N.φ 1 v (ψ v m) :=
    (N.sigma_mk_eq_iff h0.symm (ψ v m) (N.φ 1 v (ψ v m))).1 (N.smul_one_total ⟨v, ψ v m⟩).symm
  rw [← eM, ← eN, eqCast_natural']

omit [FiniteDimensional K L] in
/-- `Rep.Hom`'s `rational` field read at a named target vertex.  @census none (helper) -/
theorem rational_of_φ' {M N : RationalQuiver.Rep Γ} (ψ : ∀ v, M.M v →ₗ[L] N.M v)
    {σ : Gal(L/K)} {v w : Γ.V} (hvw : σ • v = w) (m : M.M v)
    (H : ψ w (M.φ' σ hvw m) = N.φ' σ hvw (ψ v m)) :
    ψ (σ • v) (M.φ σ v m) = N.φ σ v (ψ v m) := by
  subst hvw; exact H

variable (ρ') in
/-- A vertex of `Γ` as a vertex of `Γ.withρ ρ'`.  @census none (helper) -/
abbrev wV (v : Γ.V) : (Γ.withρ ρ').V := v

variable (ρ') in
/-- An edge of `Γ` as an edge of `Γ.withρ ρ'`.  @census none (helper) -/
abbrev wE (e : Γ.E) : (Γ.withρ ρ').E := e

variable (ρ') in
/-- An edge of `Γ.withρ ρ'` as an edge of `Γ`.  @census none (helper) -/
abbrev uE (e : (Γ.withρ ρ').E) : Γ.E := e

variable (hV : ∀ (σ : Gal(L/K)) (v : Γ.V), σ • v = (σ • wV ρ' v : (Γ.withρ ρ').V))
  (hE : ∀ (σ : Gal(L/K)) (e : Γ.E), σ • e = (σ • wE ρ' e : (Γ.withρ ρ').E))
include hV hE

/-- **Re-indexing**: a representation of `Γ`, read as a representation of `Γ.withρ ρ'` for a `ρ'`
acting by the same permutations: the same spaces and edges, `φ` transported.  @census none (helper) -/
noncomputable def _root_.RationalQuivers.RationalQuiver.Rep.reρ (M : RationalQuiver.Rep Γ) :
    RationalQuiver.Rep (Γ.withρ ρ') :=
  RationalQuiver.Rep.ofFiniteDimensional (Γ := Γ.withρ ρ') M.M
    (fun σ v => (M.φ σ v).trans (M.eqCast (hV σ v)).toAddEquiv)
    (fun σ v a m => by
      show M.eqCast (hV σ v) (M.φ σ v (a • m)) = σ a • M.eqCast (hV σ v) (M.φ σ v m)
      rw [M.semilinear, map_smul])
    (fun σ τ v m =>
      (sigma_eqCast M _ _).trans ((sigma_φ_eqCast M σ _ _).trans
        ((M.cocycle σ τ v m).trans (sigma_eqCast M _ _).symm)))
    M.φEdge
    (fun σ e m m' hmm' => by
      have hEe : (σ • uE ρ' e : Γ.E) = (σ • e : (Γ.withρ ρ').E) := hE σ e
      revert m' hmm'
      generalize (σ • e : (Γ.withρ ρ').E) = e' at hEe ⊢
      subst hEe
      intro m' hmm'
      have key := M.edge_equivariance σ e m m' (hmm'.trans (sigma_eqCast M _ _))
      exact key.trans (sigma_eqCast M _ _).symm)

theorem reρ_M (M : RationalQuiver.Rep Γ) : (M.reρ hV hE).M = M.M := rfl

theorem reρ_φ_val (M : RationalQuiver.Rep Γ) (σ : Gal(L/K)) (v : Γ.V) (m : M.M v) :
    (M.reρ hV hE).φ σ v m = M.eqCast (hV σ v) (M.φ σ v m) := rfl

end Reindex

/-! ### An isomorphism from invertible components -/

section IsoMk

variable {K L : Type} [Field K] [Field L] [Algebra K L] {Γ : RationalQuiver K L}

/-- A morphism of representations with invertible components is an isomorphism of `FDRep`s.
@census none (helper) -/
noncomputable def fdRepIsoOfComponents {M N : RationalQuiver.FDRep Γ}
    (f : RationalQuiver.Rep.Hom M.toRep N.toRep) (g : ∀ v, N.toRep.M v →ₗ[L] M.toRep.M v)
    (hgf : ∀ v x, g v (f.ψ v x) = x) (hfg : ∀ v y, f.ψ v (g v y) = y) : M ≅ N where
  hom := f
  inv :=
    { ψ := g
      edge := fun e m => by
        have h := f.edge e (g _ m)
        rw [hfg] at h
        rw [← h, hgf]
      rational := fun σ v m => by
        have h := f.rational σ v (g v m)
        rw [hfg] at h
        rw [← h, hgf] }
  hom_inv_id := RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun x => hgf v x)
  inv_hom_id := RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun y => hfg v y)

end IsoMk

/-! ### `Γ_E` vs `gelfandOfCardTwo` for `√-1 ∉ E` -/

section CardTwo

variable (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1)

/-- A vertex index of `gelfandOfCardTwo`.  @census none (helper) -/
abbrev vtxCT (v : Fin 3) : (RationalQuiver.gelfandOfCardTwo E D.L (D.sqrtExt hc).card_gal).V := v

/-- An edge index of `gelfandOfCardTwo`.  @census none (helper) -/
abbrev edgeCT (e : Fin 4) : (RationalQuiver.gelfandOfCardTwo E D.L (D.sqrtExt hc).card_gal).E := e

theorem gammaE_smul_vertex_cardTwo (σ : D.L ≃ₐ[E] D.L) (v : Fin 3) :
    (σ • Gelfand.Equivalence.vtxE D v : Fin 3) = (σ • vtxCT hc v : Fin 3) := by
  rw [Gelfand.Equivalence.gammaE_smul_vertex]
  by_cases hσ : σ = 1
  · subst hσ; rw [if_pos D.chi_one]; exact (one_smul (D.L ≃ₐ[E] D.L) (vtxCT hc v)).symm
  · rw [if_neg (by rw [D.chi_eq_one_iff]; exact fun h => hσ (D.ext_i (by rw [h]; rfl)))]
    exact (Examples.gelfand_smul_vertex E D.L (D.sqrtExt hc).card_gal hσ v).symm

theorem gammaE_smul_edge_cardTwo (σ : D.L ≃ₐ[E] D.L) (e : Fin 4) :
    (σ • Gelfand.Equivalence.edgeE D e : Fin 4) = (σ • edgeCT hc e : Fin 4) := by
  rw [Gelfand.Equivalence.gammaE_smul_edge]
  by_cases hσ : σ = 1
  · subst hσ; rw [if_pos D.chi_one]; exact (one_smul (D.L ≃ₐ[E] D.L) (edgeCT hc e)).symm
  · rw [if_neg (by rw [D.chi_eq_one_iff]; exact fun h => hσ (D.ext_i (by rw [h]; rfl)))]
    exact (Examples.gelfand_smul_edge E D.L (D.sqrtExt hc).card_gal hσ e).symm

/-- `V ∈ Rep^nil(Γ_E)` read in the engine's presentation `Rep^nil(gelfandOfCardTwo)` (T1's
`ImagUnit.gelfandOfSign_eq_gelfandOfCardTwo`, on representations): same spaces and edges, `φ`
re-indexed.  @census none (helper) -/
noncomputable def toCardTwo (V : (Gelfand.Equivalence.RepNilGel D).FullSubcategory) :
    Gelfand.RationalStructure.RepNilQ (Dq := D.sqrtExt hc) (D.sqrtExt hc).card_gal :=
  ⟨⟨V.obj.toRep.reρ (Γ := RationalQuiver.gelfandOfSign E D.L D.chiHom) (ρ' := (RationalQuiver.gelfandOfCardTwo E D.L (D.sqrtExt hc).card_gal).ρ)
      (gammaE_smul_vertex_cardTwo hc) (gammaE_smul_edge_cardTwo hc),
    V.obj.finiteDimensional⟩, V.property.1, V.property.2⟩

end CardTwo


end NativeHC


/-! ## The native `𝔼_E` on `HC ℓ E D` (stage T3) -/

section NativeHC

set_option linter.unusedSectionVars false

variable {D : ImagUnit E} (hℓ : 1 ≤ ℓ)


theorem E_E_rep_eqCast_val (A : HC ℓ E D) {v w : (RationalQuiver.gelfandOfSign E D.L D.chiHom).V}
    (h : v = w) (m : Split.V3 A.qi v) : (((Gelfand.Equivalence.E_E_rep hℓ A).eqCast h m : Split.V3 A.qi w)).1 = m.1 := by
  subst h; rfl

omit [CharZero E] in
theorem eqCast_eqCast {Γ : RationalQuiver E D.L} (M : RationalQuiver.Rep Γ) {u v w : Γ.V}
    (h₁ : u = v) (h₂ : v = w) (x : M.M u) : M.eqCast h₂ (M.eqCast h₁ x) = M.eqCast (h₁.trans h₂) x := by
  subst h₁; subst h₂; rfl


/-- **Essential surjectivity, `√-1 ∉ E`** (Steps O-18b … O-24): for `V ∈ Rep^nil(Γ_E)` the
construction `M` of the relocated engine (with `c := φ_c^M`) satisfies `𝔼_E(M_E) ≅ V`, the iso being
`(s_−, t, s_+)` (`natPsi`, Step O-23).  @census none (helper) -/
theorem E_EGel_essSurj_nonsplit (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) (V : (Gelfand.Equivalence.RepNilGel D).FullSubcategory) :
    (Gelfand.Equivalence.E_EGel (D := D) hℓ).essImage V := by
  obtain ⟨Dd⟩ := essSurj_exists (D.sqrtExt hc).card_gal hℓ (toCardTwo hc V)
  have hA := Gelfand.Equivalence.E_E_wellDefined (D.sqrtExt hc).card_gal hℓ Dd.toHCQObj
  let A : HC ℓ E D := toHC Dd
  have hAA : A.toHCEObj hc = Dd.toHCQObj := HCEObj.toHC_toHCEObj _
  let f : RationalQuiver.Rep.Hom (Gelfand.Equivalence.E_E_rep hℓ A) V.obj.toRep :=
    { ψ := EssSurjData.natPsi Dd
      edge := fun e m => Dd.natPsi_edge_all e m
      rational := fun σ v m => by
        rcases D.chi_cases σ with hσ | hσ
        · obtain rfl := D.eq_one_of_chi_one hσ
          exact rational_one _ v m
        · have hvw : σ • Gelfand.Equivalence.vtxE D v = Gelfand.Equivalence.vtxE D (RQuiver.gelfandVertexSwap v) := by
            rw [Gelfand.Equivalence.vtxE_smul]; unfold Gelfand.Equivalence.galVtx; rw [if_neg (by rw [hσ]; decide)]
          refine rational_of_φ' (EssSurjData.natPsi Dd) hvw m ?_
          have hconj := (D.sqrtExt_conj hc hσ).symm
          subst hconj
          have key := Dd.natPsi_rational_conj hA v m
          have hL : (Gelfand.Equivalence.E_E_rep hℓ A).φ' (D.sqrtExt hc).conj hvw m
              = (Gelfand.Equivalence.E_Q_rep (D.sqrtExt hc).card_gal hℓ Dd.toHCQObj hA).φ' (D.sqrtExt hc).conj
                  (Gelfand.RationalStructure.gelfandQ_smul_vertex (D.sqrtExt hc).card_gal v) m := by
            apply Subtype.ext
            rw [repPhi'_val hA, RationalQuiver.Rep.φ'_apply, E_E_rep_eqCast_val]
            show Gelfand.RationalStructure.E_E_φ hℓ A _ v m.1 = _
            rw [Gelfand.RationalStructure.E_E_φ_eq_phiC hℓ A (D.chi_sqrtExt_conj hc)]
            exact Gelfand.RationalStructure.phiC_toHC hℓ _ v m.1
          refine (congrArg (EssSurjData.natPsi Dd _) hL).trans (key.trans ?_)
          exact eqCast_eqCast V.obj.toRep _ _ _ }
  refine ⟨A, ⟨ObjectProperty.isoMk _ (fdRepIsoOfComponents (M := Gelfand.Equivalence.E_E_fdrep hℓ A) (N := V.obj) f
    (fun v => EssSurjData.natPsiInv Dd v) (fun v x => Dd.natPsiInv_natPsi v x)
    (fun v y => Dd.natPsi_natPsiInv v y))⟩⟩

/-! ### Essential surjectivity, `√-1 ∈ E`: Step O-7h -/

/-- The underlying split representation of `V ∈ Rep^nil(Γ_E)`: the same spaces and edges with the
trivial `Gal(L_E/L_E)`-structure.  @census none (helper) -/
noncomputable def toSplitRepGel (V : (Gelfand.Equivalence.RepNilGel D).FullSubcategory) :
    RationalQuiver.FDRep (gelfandSplit D.L) where
  toRep := RationalQuiver.Rep.ofFiniteDimensional (Γ := gelfandSplit D.L)
    (fun v => V.obj.toRep.M v) (fun _ _ => AddEquiv.refl _)
    (fun σ v a m => by rw [galSelf_apply]; rfl) (fun _ _ _ _ => rfl)
    (fun e => V.obj.toRep.φEdge e) (fun _ _ _ _ h => by cases h; rfl)
  finiteDimensional v := V.obj.finiteDimensional v

/-- `toSplitRepGel V` is nilpotent with the relation.  @census none (helper) -/
noncomputable abbrev toSplitGel (V : (Gelfand.Equivalence.RepNilGel D).FullSubcategory) :
    (RepNilRelSplit D.L).FullSubcategory :=
  ⟨toSplitRepGel V, V.property.1, V.property.2⟩

/-- **Essential surjectivity, `√-1 ∈ E`**: `G_E = 1`, and the split construction of tex §5.1
(Step O-7h, `Split.essSurj`: `SplitEssSurjData`, `xStar_eq_poly`, `isoPoly`) gives `M`.
@census none (helper) -/
theorem E_EGel_essSurj_split (hs : ∃ a : E, a * a = -1) (V : (Gelfand.Equivalence.RepNilGel D).FullSubcategory) :
    (Gelfand.Equivalence.E_EGel (D := D) hℓ).essImage V := by
  -- Step O-13, item (i): the equivalence over `L_E` (`prop:splitequivalence`, Step O-7); for
  -- `√-1 ∈ E` it **is** the theorem.  `X := e⁻¹(W)` and `𝔼_{L_E}(X) = e(X) ≅ W`.
  obtain ⟨eq, heq⟩ := Split.equivalence (L := D.L) ℓ hℓ
  let X := eq.inverse.obj (toSplitGel V)
  have hX : eq.functor.obj X = (Split.E_FNil (F := D.L) ℓ hℓ).obj X :=
    ObjectProperty.FullSubcategory.ext (congrArg (fun F => F.obj X) heq)
  let e : (Split.E_FNil (F := D.L) ℓ hℓ).obj X ≅ toSplitGel V :=
    (eqToIso hX).symm ≪≫ eq.counitIso.app (toSplitGel V)
  let A : HC ℓ E D := HC.ofLambda hs (Split.hcFToLambdaObj D.L ℓ X)
  let f : RationalQuiver.Rep.Hom (Gelfand.Equivalence.E_E_rep hℓ A) V.obj.toRep :=
    { ψ := e.hom.hom.ψ
      edge := e.hom.hom.edge
      rational := fun σ v m => by
        obtain rfl := D.eq_one_of_sqrt hs σ
        exact rational_one _ v m }
  refine ⟨A, ⟨ObjectProperty.isoMk _ (fdRepIsoOfComponents (M := Gelfand.Equivalence.E_E_fdrep hℓ A) (N := V.obj) f
    e.inv.hom.ψ (fun v x => ?_) (fun v y => ?_))⟩⟩
  · exact congrArg (fun φ => φ.hom.ψ v x) e.hom_inv_id
  · exact congrArg (fun φ => φ.hom.ψ v y) e.inv_hom_id

/-- **Essential surjectivity** (`ℓ ≥ 1`, every `E`).  @census none (helper) -/
theorem E_E_essSurj : (Gelfand.Equivalence.E_EGel (D := D) hℓ).EssSurj where
  mem_essImage V := by
    by_cases hs : ∃ a : E, a * a = -1
    · exact E_EGel_essSurj_split hℓ hs V
    · exact E_EGel_essSurj_nonsplit hℓ (D.exists_chi_neg_one_iff.mpr hs) V


end NativeHC

end RationalQuivers.Gelfand.EssSurj
