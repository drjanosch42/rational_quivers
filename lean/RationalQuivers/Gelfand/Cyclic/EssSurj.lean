import RationalQuivers.Gelfand.Cyclic.FullyFaithful

/-!
# the case `ℓ = 0`: essential surjectivity (§5.3, Step C-7)

Engine `E10` over T2's one `ℓ = 0` carrier `Split.cz*` (OQ-7): `φ_c^M` on the explicit `M`
(`csConj`, `eq:cyclickoecher`), Galois descent (`csForm`, `csHCQObj`), `𝔼(M) = V` by the canonical
embeddings (`csNatIsoFD`); native `cycEssSurj` (split case: T2's `Split.E_CycSplit_essSurj`).

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Cyclic.lean (§E10, residue, witness)` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.Cyclic.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

*(2026-10-21, O-V2-6 round 2.)*  Some carried docstrings below name in the present tense v1 files
and declarations that v2 deleted.  They are v1's.  `Gelfand/Equivalence.lean` (engine `E2`; since
WP-10 in `Gelfand/EssSurj/`), `Gelfand/Models.lean` (with its `zeroObjSpecC` and
`Gelfand.zeroHCQObj`) and the frozen `ℚ`-case claimants of `RQ-5.05`/`RQ-5.07`
(`Gelfand.E_Q_equivalence`, `Gelfand.cyclic_E_Q_equivalence`, on S8's `Gelfand/Category.lean`) were
deleted with the v1 Q-chain at WP-13 (`ae9eda9`, `9c6b193`).  The v2 claimants are
`Gelfand.Rational.E_Q_equivalence` (`RQ2-5.05`) and `Gelfand.Rational.cyclic_E_Q_equivalence`
(`RQ2-5.07`), and this module's `zeroObjSpecC` is the field-generic inhabitant.

@census none (module)
-/

namespace RationalQuivers.Gelfand.Cyclic

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {Dq : SqrtNegOneExt E}
open scoped TensorProduct Classical

variable {Mi : Type} [AddCommGroup Mi] [Module Dq.carrier Mi]

section Functor

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)

/-! ### Engine `E10` — the `ℓ = 0` essential-surjectivity carrier

`E2` (`Gelfand/Equivalence.lean`) builds, from a nilpotent `ℚ`-rational representation `V` of the
**Gelfand** quiver, a whole `ℚ`-rational Harish-Chandra module with `𝔼_ℚ(M) ≅ V`.  It does not
specialise to `ℓ = 0`, and the obstruction is not a hypothesis that can be dropped: its operators
are `ξ^{(j)}_{•,±} = φ_•^{1/2} ± j·𝟏`, whose square root is taken with respect to the unit
`ellUnit hℓ = ℓ ∈ ℚ[√-1]ˣ`, which **does not exist at `ℓ = 0`**; there `φ_• = ℓ²·𝟏 + 4n_• = 4n_•`
is nilpotent, not `unit² + nilpotent`, and a nilpotent operator has no square root in general
(`stages/S8/DESIGN-NOTES.md` §20.5(2)).  Ruling **`R-S8-35`** directs a fresh `ℓ = 0` carrier.

**The `ℓ = 0` construction, and why it is easier.**  `RQ-5.07`'s census clauses do not pin the
carrier (unlike `RQ-5.05`'s `C9`–`C25`), so the implementer may choose it.  With `λ = ℓ² = 0` the
Casimir *is* the nilpotent operator of the generalized infinitesimal character, and the module can
be written down with no square roots at all:

* `M_n = V(+)` for `n ≥ 1` and `V(−)` for `n ≤ -1`, and `0` for `n` even (the central character);
* `X = 𝟏` on the `+` chain and `Y = 𝟏` on the `−` chain;
* `Y = ¼(φ_+ − (n−1)²·𝟏)` on `M_n` for `n ≥ 3`, and `X = ¼(φ_- − (n+1)²·𝟏)` on `M_n` for `n ≤ -3`,
  where `φ_± = 4n_±` are the two quiver loops, each nilpotent because `V` is;
* at the wall, `X|_{M_{-1}} = φ_a` and `Y|_{M_1} = φ_b` — the two edges of the cyclic quiver.

Then `4XY = C − (n−1)²·𝟏` and `4YX = C − (n+1)²·𝟏` hold **by construction**, with `C = φ_±`
uniformly on the two chains, and `4YX|_{M_{-1}} = 4φ_bφ_a = φ_-` is the wall relation.  What
remains after the carrier is the same list `E2` had — the generalized infinitesimal character,
admissibility, the central character, finite generation, the conjugation and the `ℚ`-form by
Galois descent — minus every square root.  The transport-free design of `E2`'s step 1 (every
component a **submodule of one fixed ambient** `T`) is kept verbatim, as is its graded-carrier
lemma `isInternal_range_lof`, which is generic. -/

section E10

variable (V : RepNilCycQ hcard)

/-- **The underlying split representation** of `V` (BLUEPRINT OQ-7, route (α) at `ℓ = 0`): the same
vertex spaces and edge maps, with the trivial `Gal(L/L)`-structure, so that the one `c`-free `ℓ = 0`
carrier `Split.cz*` (`Gelfand/Split/Cyclic.lean`) read at `toSplitC V` is this engine's carrier.
@census none (helper; OQ-7) -/
noncomputable def toSplitCRep : RationalQuiver.FDRep (cyclicSplit Dq.carrier) where
  toRep := RationalQuiver.Rep.ofFiniteDimensional (Γ := cyclicSplit Dq.carrier)
    (fun v => V.obj.toRep.M v) (fun _ _ => AddEquiv.refl _)
    (fun σ v a m => by rw [galSelf_apply]; rfl) (fun _ _ _ _ => rfl)
    (fun e => V.obj.toRep.φEdge e) (fun _ _ _ _ h => by cases h; rfl)
  finiteDimensional v := V.obj.finiteDimensional v

/-- `toSplitCRep V` is nilpotent.  @census none (helper; OQ-7) -/
noncomputable abbrev toSplitC : (RationalQuiver.RepNil (cyclicSplit Dq.carrier)).FullSubcategory :=
  ⟨toSplitCRep hcard V, V.property⟩

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

/-! #### The vertex spaces, the two edges and the two loops -/
















/-! #### The graded carrier -/


















/-! #### The operators, in the ambient `T`

`X` is the identity on the `+` chain and `¼(φ_- − (n+1)²·𝟏)` on the `−` chain; `Y` is the identity
on the `−` chain and `¼(φ_+ − (n−1)²·𝟏)` on the `+` chain; the two walls are the two edges of the
cyclic quiver.  Each is attached to the **source** degree, as in `E2`. -/











/-! #### The three arithmetic identities the operators need -/







/-! #### The graded `𝔰𝔩₂`-module -/



@[simp] theorem csXComp_val (n : ℤ) (a : Split.czFib (toSplitC hcard V) n) :
    ((Split.czXComp (toSplitC hcard V) n a : Split.czFib (toSplitC hcard V) (n + 2)) : Split.czT (toSplitC hcard V))
      = Split.czXAmb (toSplitC hcard V) n (a : Split.czT (toSplitC hcard V)) := rfl
@[simp] theorem csYComp_val (n : ℤ) (a : Split.czFib (toSplitC hcard V) n) :
    ((Split.czYComp (toSplitC hcard V) n a : Split.czFib (toSplitC hcard V) (n - 2)) : Split.czT (toSplitC hcard V))
      = Split.czYAmb (toSplitC hcard V) n (a : Split.czT (toSplitC hcard V)) := rfl




@[simp] theorem csX_lof (n : ℤ) (a : Split.czFib (toSplitC hcard V) n) :
    Split.czX (toSplitC hcard V) (DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) n a)
      = DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) (n + 2) (Split.czXComp (toSplitC hcard V) n a) := by
  rw [Split.czX, DirectSum.toModule_lof]; rfl

@[simp] theorem csY_lof (n : ℤ) (a : Split.czFib (toSplitC hcard V) n) :
    Split.czY (toSplitC hcard V) (DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) n a)
      = DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) (n - 2) (Split.czYComp (toSplitC hcard V) n a) := by
  rw [Split.czY, DirectSum.toModule_lof]; rfl

@[simp] theorem csH_lof (n : ℤ) (a : Split.czFib (toSplitC hcard V) n) :
    Split.czH (toSplitC hcard V) (DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) n a)
      = (n : Dq.carrier) • DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) n a := by
  rw [Split.czH, DirectSum.toModule_lof]
  show DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) n ((n : Dq.carrier) • a) = _
  rw [map_smul]











/-! #### The generalized infinitesimal character: `λ = 0` and `C = φ_±` -/





set_option maxHeartbeats 1000000 in






/-! #### Finite generation -/







/-! #### The conjugation `c`

On the ambient `T = V(+) × V(−)` the conjugation is `V`'s own rational structure read across the
`±`-swap: `c(x₊, x₋) = (φ_{−,c}x₋, φ_{+,c}x₊)`.  It is `Dq.conj`-semilinear, an involution by the
cocycle condition, carries `M_n` to `M_{-n}` because it exchanges the two ranges, and intertwines
`X` with `Y` because `RQ-1.08-C9` says so at the wall and because `c` intertwines the two loops
`n_±` in the two interiors. -/

/-- `c` sends the `−` vertex of the cyclic quiver to the `+` vertex.  @census none (helper) -/
theorem galConj_smul_zero : Dq.conj • vtxC hcard 0 = vtxC hcard 1 := by
  rw [cyclicQ_smul_vertex hcard 0]; rfl

/-- `c` swaps the two edges.  @census none (helper) -/
theorem galConj_smul_edge0 : Dq.conj • edgeC hcard 0 = edgeC hcard 1 := by
  rw [cyclicQ_smul_edge hcard 0]; rfl

/-- @census none (helper) -/
theorem galConj_smul_edge1 : Dq.conj • edgeC hcard 1 = edgeC hcard 0 := by
  rw [cyclicQ_smul_edge hcard 1]; rfl

/-- `c` fixes `4⁻¹`.  @census none (helper; engine `E10`) -/
theorem galConj_four_inv : Dq.conj ((4 : Dq.carrier)⁻¹) = ((4 : Dq.carrier)⁻¹) := by
  rw [map_inv₀, map_ofNat]

/-- `φ_{+,c} : V(+) → V(−)`.  @census none (helper; engine `E10`) -/
noncomputable def csVphiPlus : Split.czVM (toSplitC hcard V) 1 ≃+ Split.czVM (toSplitC hcard V) 0 :=
  V.obj.toRep.φ' Dq.conj (galConj_smul_one hcard)

/-- `φ_{−,c} : V(−) → V(+)`.  @census none (helper; engine `E10`) -/
noncomputable def csVphiMinus : Split.czVM (toSplitC hcard V) 0 ≃+ Split.czVM (toSplitC hcard V) 1 :=
  V.obj.toRep.φ' Dq.conj (galConj_smul_zero hcard)

theorem csVphiPlus_smul (a : Dq.carrier) (m : Split.czVM (toSplitC hcard V) 1) :
    csVphiPlus hcard V (a • m) = Dq.conj a • csVphiPlus hcard V m :=
  RationalQuiver.Rep.φ'_smul _ _ _ _ _

theorem csVphiMinus_smul (a : Dq.carrier) (m : Split.czVM (toSplitC hcard V) 0) :
    csVphiMinus hcard V (a • m) = Dq.conj a • csVphiMinus hcard V m :=
  RationalQuiver.Rep.φ'_smul _ _ _ _ _

theorem csVphi_swap_plus (x : Split.czVM (toSplitC hcard V) 1) :
    csVphiMinus hcard V (csVphiPlus hcard V x) = x := by
  have hinv : (Dq.conj : Dq.carrier ≃ₐ[E] Dq.carrier)⁻¹ = Dq.conj :=
    inv_eq_of_mul_eq_one_right Gelfand.RationalStructure.galConj_mul_self
  have h' : (Dq.conj : Dq.carrier ≃ₐ[E] Dq.carrier)⁻¹ • vtxC hcard 0 = vtxC hcard 1 := by
    rw [hinv]; exact galConj_smul_zero hcard
  exact Eq.trans (V.obj.toRep.φ'_congr hinv h' (galConj_smul_zero hcard) _).symm (V.obj.toRep.φ'_inv Dq.conj (galConj_smul_one hcard) h' x)

theorem csVphi_swap_minus (x : Split.czVM (toSplitC hcard V) 0) :
    csVphiPlus hcard V (csVphiMinus hcard V x) = x := by
  have hinv : (Dq.conj : Dq.carrier ≃ₐ[E] Dq.carrier)⁻¹ = Dq.conj :=
    inv_eq_of_mul_eq_one_right Gelfand.RationalStructure.galConj_mul_self
  have h' : (Dq.conj : Dq.carrier ≃ₐ[E] Dq.carrier)⁻¹ • vtxC hcard 1 = vtxC hcard 0 := by
    rw [hinv]; exact galConj_smul_one hcard
  exact Eq.trans (V.obj.toRep.φ'_congr hinv h' (galConj_smul_one hcard) _).symm (V.obj.toRep.φ'_inv Dq.conj (galConj_smul_zero hcard) h' x)

/-- `RQ-1.08-C9` at the edge `a`.  @census none (helper; engine `E10`) -/
theorem csVphi_edge0 (m : Split.czVM (toSplitC hcard V) 0) :
    Split.czEdgeB (toSplitC hcard V) (csVphiMinus hcard V m) = csVphiPlus hcard V (Split.czEdgeA (toSplitC hcard V) m) :=
  RationalQuiver.Rep.φEdge'_φ' V.obj.toRep Dq.conj
    (f := edgeC hcard 0) (e := edgeC hcard 1) (galConj_smul_edge0 hcard)
    (a := vtxC hcard 0) (b := vtxC hcard 1) (a' := vtxC hcard 1) (b' := vtxC hcard 0)
    rfl rfl rfl rfl (galConj_smul_zero hcard) (galConj_smul_one hcard) m

/-- `RQ-1.08-C9` at the edge `b`.  @census none (helper; engine `E10`) -/
theorem csVphi_edge1 (m : Split.czVM (toSplitC hcard V) 1) :
    Split.czEdgeA (toSplitC hcard V) (csVphiPlus hcard V m) = csVphiMinus hcard V (Split.czEdgeB (toSplitC hcard V) m) :=
  RationalQuiver.Rep.φEdge'_φ' V.obj.toRep Dq.conj
    (f := edgeC hcard 1) (e := edgeC hcard 0) (galConj_smul_edge1 hcard)
    (a := vtxC hcard 1) (b := vtxC hcard 0) (a' := vtxC hcard 0) (b' := vtxC hcard 1)
    rfl rfl rfl rfl (galConj_smul_one hcard) (galConj_smul_zero hcard) m

/-- `c` intertwines the two loops.  @census none (helper; engine `E10`) -/
theorem csVphi_nMinus (a : Split.czVM (toSplitC hcard V) 0) :
    csVphiMinus hcard V (Split.czNMinus (toSplitC hcard V) a) = Split.czNPlus (toSplitC hcard V) (csVphiMinus hcard V a) := by
  show csVphiMinus hcard V (Split.czEdgeB (toSplitC hcard V) (Split.czEdgeA (toSplitC hcard V) a))
      = Split.czEdgeA (toSplitC hcard V) (Split.czEdgeB (toSplitC hcard V) (csVphiMinus hcard V a))
  rw [← csVphi_edge1 hcard V (Split.czEdgeA (toSplitC hcard V) a), csVphi_edge0 hcard V a]

/-- `c` intertwines `φ_-` with `φ_+`.  @census none (helper; engine `E10`) -/
theorem csVphi_phiMinus (a : Split.czVM (toSplitC hcard V) 0) :
    csVphiMinus hcard V (Split.czPhiMinus (toSplitC hcard V) a) = Split.czPhiPlus (toSplitC hcard V) (csVphiMinus hcard V a) := by
  show csVphiMinus hcard V ((4 : Dq.carrier) • Split.czNMinus (toSplitC hcard V) a)
      = (4 : Dq.carrier) • Split.czNPlus (toSplitC hcard V) (csVphiMinus hcard V a)
  rw [csVphiMinus_smul, csVphi_nMinus, map_ofNat]

/-- `c` on the ambient `T`.  @census none (helper; engine `E10`) -/
noncomputable def csConjT (x : Split.czT (toSplitC hcard V)) : Split.czT (toSplitC hcard V) :=
  (csVphiMinus hcard V x.2, csVphiPlus hcard V x.1)

theorem csConjT_involutive : Function.Involutive (csConjT hcard V) := by
  intro x
  refine Prod.ext ?_ ?_
  · exact csVphi_swap_plus hcard V x.1
  · exact csVphi_swap_minus hcard V x.2

/-- `c` on the ambient, as an additive equivalence.  @census none (helper; engine `E10`) -/
noncomputable def csConjAmb : Split.czT (toSplitC hcard V) ≃+ Split.czT (toSplitC hcard V) where
  toFun := csConjT hcard V
  invFun := csConjT hcard V
  left_inv := csConjT_involutive hcard V
  right_inv := csConjT_involutive hcard V
  map_add' x y := Prod.ext (map_add _ _ _) (map_add _ _ _)

@[simp] theorem csConjAmb_apply (x : Split.czT (toSplitC hcard V)) :
    csConjAmb hcard V x = csConjT hcard V x := rfl

theorem csConjAmb_involutive (x : Split.czT (toSplitC hcard V)) :
    csConjAmb hcard V (csConjAmb hcard V x) = x := csConjT_involutive hcard V x

theorem csConjAmb_smul (a : Dq.carrier) (x : Split.czT (toSplitC hcard V)) :
    csConjAmb hcard V (a • x) = Dq.conj a • csConjAmb hcard V x :=
  Prod.ext (csVphiMinus_smul hcard V a x.2) (csVphiPlus_smul hcard V a x.1)

theorem csConjAmb_iotaPlus (a : Split.czVM (toSplitC hcard V) 1) :
    csConjAmb hcard V (Split.czIotaPlus (toSplitC hcard V) a) = Split.czIotaMinus (toSplitC hcard V) (csVphiPlus hcard V a) :=
  Prod.ext (map_zero _) rfl

theorem csConjAmb_iotaMinus (a : Split.czVM (toSplitC hcard V) 0) :
    csConjAmb hcard V (Split.czIotaMinus (toSplitC hcard V) a) = Split.czIotaPlus (toSplitC hcard V) (csVphiMinus hcard V a) :=
  Prod.ext rfl (map_zero _)

/-- `c : M_n → M_{-n}`, in the ambient.  @census none (helper; engine `E10`) -/
theorem csConjAmb_mem (n : ℤ) (x : Split.czT (toSplitC hcard V)) (hx : x ∈ Split.czRegion (toSplitC hcard V) n) :
    csConjAmb hcard V x ∈ Split.czRegion (toSplitC hcard V) (-n) := by
  by_cases hpar : (n + 1) % 2 = 0
  · have hpar2 : (-n + 1) % 2 = 0 := by omega
    by_cases h1 : (1 : ℤ) ≤ n
    · rw [Split.czRegion_plus (toSplitC hcard V) hpar h1] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [csConjAmb_iotaPlus, Split.czRegion_minus (toSplitC hcard V) hpar2 (by omega)]
      exact ⟨_, rfl⟩
    · rw [Split.czRegion_minus (toSplitC hcard V) hpar (by omega)] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [csConjAmb_iotaMinus, Split.czRegion_plus (toSplitC hcard V) hpar2 (by omega)]
      exact ⟨_, rfl⟩
  · rw [Split.czRegion_bot_apply (toSplitC hcard V) hpar hx, map_zero]
    exact Submodule.zero_mem _

/-- **`cX = Yc`, in the ambient.**  @census none (helper; engine `E10`) -/
theorem csConjAmb_xAmb (n : ℤ) (x : Split.czT (toSplitC hcard V)) (hx : x ∈ Split.czRegion (toSplitC hcard V) n) :
    csConjAmb hcard V (Split.czXAmb (toSplitC hcard V) n x) = Split.czYAmb (toSplitC hcard V) (-n) (csConjAmb hcard V x) := by
  by_cases hpar : (n + 1) % 2 = 0
  case neg =>
    rw [Split.czRegion_bot_apply (toSplitC hcard V) hpar hx, map_zero, map_zero, map_zero]
  rcases (show (1 : ℤ) ≤ n ∨ n = -1 ∨ n ≤ -3 by omega) with h | h | h
  · rw [Split.czRegion_plus (toSplitC hcard V) hpar h] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [Split.czXAmb_up (toSplitC hcard V) h a, csConjAmb_iotaPlus,
      Split.czYAmb_dn (toSplitC hcard V) (by omega) (by omega) _]
  · subst h
    rw [Split.czRegion_minus (toSplitC hcard V) hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [Split.czXAmb_wall (toSplitC hcard V) (by omega) (by omega) rfl a, csConjAmb_iotaPlus,
      csConjAmb_iotaMinus, Split.czYAmb_wall (toSplitC hcard V) (by omega) (by omega) (by ring) _]
    exact congrArg (Split.czIotaMinus (toSplitC hcard V)) (csVphi_edge0 hcard V a).symm
  · rw [Split.czRegion_minus (toSplitC hcard V) hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [Split.czXAmb_dn (toSplitC hcard V) (by omega) h a, csConjAmb_iotaMinus, csConjAmb_iotaMinus,
      Split.czYAmb_up (toSplitC hcard V) (by omega) _]
    refine congrArg (Split.czIotaPlus (toSplitC hcard V)) ?_
    rw [csVphiMinus_smul, galConj_four_inv]
    refine congrArg (fun z => ((4 : Dq.carrier)⁻¹) • z) ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub,
      csVphi_phiMinus, csVphiMinus_smul]
    rw [show Dq.conj ((((n + 1 : ℤ)) : Dq.carrier) ^ 2) = ((((n + 1 : ℤ)) : Dq.carrier) ^ 2) by
      rw [map_pow, map_intCast],
      show ((((-n - 1 : ℤ)) : Dq.carrier) ^ 2) = ((((n + 1 : ℤ)) : Dq.carrier) ^ 2) by
      push_cast; ring]

/-! #### `c` on the graded carrier -/

/-- @census none (helper; engine `E10`) -/
theorem csOf_congr {i j : ℤ} (h : i = j) (a : Split.czFib (toSplitC hcard V) i) (b : Split.czFib (toSplitC hcard V) j)
    (hab : (a : Split.czT (toSplitC hcard V)) = (b : Split.czT (toSplitC hcard V))) :
    DirectSum.of (Split.czFib (toSplitC hcard V)) i a = DirectSum.of (Split.czFib (toSplitC hcard V)) j b := by
  subst h; exact congrArg _ (Subtype.ext hab)

/-- `c` on the fibre at `n`, landing at `-n`.  @census none (helper; engine `E10`) -/
noncomputable def csConjFib (n : ℤ) : Split.czFib (toSplitC hcard V) n →+ Split.czFib (toSplitC hcard V) (-n) where
  toFun a := ⟨csConjAmb hcard V (a : Split.czT (toSplitC hcard V)), csConjAmb_mem hcard V n _ a.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

@[simp] theorem csConjFib_coe (n : ℤ) (a : Split.czFib (toSplitC hcard V) n) :
    ((csConjFib hcard V n a : Split.czFib (toSplitC hcard V) (-n)) : Split.czT (toSplitC hcard V))
      = csConjAmb hcard V (a : Split.czT (toSplitC hcard V)) := rfl

/-- `c` on `M = ⨁_n M_n`, additively.  @census none (helper; engine `E10`) -/
noncomputable def csConjMap : Split.czCarrier (toSplitC hcard V) →+ Split.czCarrier (toSplitC hcard V) :=
  DirectSum.toAddMonoid (fun n => (DirectSum.of (Split.czFib (toSplitC hcard V)) (-n)).comp (csConjFib hcard V n))

@[simp] theorem csConjMap_of (n : ℤ) (a : Split.czFib (toSplitC hcard V) n) :
    csConjMap hcard V (DirectSum.of (Split.czFib (toSplitC hcard V)) n a)
      = DirectSum.of (Split.czFib (toSplitC hcard V)) (-n) (csConjFib hcard V n a) :=
  DirectSum.toAddMonoid_of _ _ _

theorem csConjMap_involutive : Function.Involutive (csConjMap hcard V) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n a =>
      rw [csConjMap_of, csConjMap_of]
      refine csOf_congr hcard V (neg_neg n) _ _ ?_
      exact csConjAmb_involutive hcard V (a : Split.czT (toSplitC hcard V))
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **The conjugation of the constructed module**.  @census none (helper; engine `E10`)
@clauses   RQ2-5.13-S-C7 -/
noncomputable def csConj : Split.czCarrier (toSplitC hcard V) ≃+ Split.czCarrier (toSplitC hcard V) where
  toFun := csConjMap hcard V
  invFun := csConjMap hcard V
  left_inv := csConjMap_involutive hcard V
  right_inv := csConjMap_involutive hcard V
  map_add' := map_add _

theorem csConj_involutive : Function.Involutive (csConj hcard V) := csConjMap_involutive hcard V

theorem csConj_lof (n : ℤ) (a : Split.czFib (toSplitC hcard V) n) :
    csConj hcard V (DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) n a)
      = DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) (-n) (csConjFib hcard V n a) := by
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  exact csConjMap_of hcard V n a

theorem csConj_smul (a : Dq.carrier) (v : Split.czCarrier (toSplitC hcard V)) :
    csConj hcard V (a • v) = Dq.conj a • csConj hcard V v := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of n b =>
      rw [← DirectSum.lof_eq_of (R := Dq.carrier)]
      have hL : a • DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) n b
          = DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) n (a • b) := (map_smul _ a b).symm
      have hR : Dq.conj a • DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) (-n)
            (csConjFib hcard V n b)
          = DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) (-n) (Dq.conj a • csConjFib hcard V n b) :=
        (map_smul _ (Dq.conj a) _).symm
      rw [hL, csConj_lof, csConj_lof, hR]
      refine congrArg _ (Subtype.ext ?_)
      exact csConjAmb_smul hcard V a (b : Split.czT (toSplitC hcard V))
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem csConj_comp (n : ℤ) (v : Split.czCarrier (toSplitC hcard V)) (hv : v ∈ Split.czComp (toSplitC hcard V) n) :
    csConj hcard V v ∈ Split.czComp (toSplitC hcard V) (-n) := by
  obtain ⟨a, rfl⟩ := hv
  rw [csConj_lof]
  exact ⟨_, rfl⟩

theorem csConj_X (v : Split.czCarrier (toSplitC hcard V)) :
    csConj hcard V (Split.czX (toSplitC hcard V) v) = Split.czY (toSplitC hcard V) (csConj hcard V v) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of n a =>
      rw [← DirectSum.lof_eq_of (R := Dq.carrier), csX_lof, csConj_lof, csConj_lof, csY_lof]
      refine Split.czLof_congr (toSplitC hcard V) (by ring) _ _ ?_
      exact csConjAmb_xAmb hcard V n (a : Split.czT (toSplitC hcard V)) a.2
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

theorem csConj_Y (v : Split.czCarrier (toSplitC hcard V)) :
    csConj hcard V (Split.czY (toSplitC hcard V) v) = Split.czX (toSplitC hcard V) (csConj hcard V v) := by
  have h := csConj_X hcard V (csConj hcard V v)
  rw [csConj_involutive hcard V v] at h
  calc csConj hcard V (Split.czY (toSplitC hcard V) v)
      = csConj hcard V (csConj hcard V (Split.czX (toSplitC hcard V) (csConj hcard V v))) := by rw [h]
    _ = Split.czX (toSplitC hcard V) (csConj hcard V v) := csConj_involutive hcard V _

theorem csConj_H (v : Split.czCarrier (toSplitC hcard V)) :
    csConj hcard V (Split.czH (toSplitC hcard V) v) = -Split.czH (toSplitC hcard V) (csConj hcard V v) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of n a =>
      rw [← DirectSum.lof_eq_of (R := Dq.carrier), csH_lof, csConj_smul, csConj_lof,
        csH_lof, map_intCast, ← neg_smul]
      congr 1
      push_cast
      ring
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy, neg_add]

/-! #### The `ℚ`-form, by Galois descent

The `ℚ`-form is the fixed-point space of `c`, and `RationalSetup.baseChange` is
`thm:galoisdescent`'s counit (`RQ-1.16`), exactly as in `E2`: three instances — the `ℚ`-module
structure by `Module.compHom`, the scalar tower, and the `Gal`-action (a choice of involution,
since the group has order two) — are installed by hand and never as global instances. -/

/-- @census none (helper; engine `E10`) -/
noncomputable def csGalSMul (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : Split.czCarrier (toSplitC hcard V)) :
    Split.czCarrier (toSplitC hcard V) :=
  if σ = 1 then v else csConj hcard V v

theorem csGalSMul_one (v : Split.czCarrier (toSplitC hcard V)) : csGalSMul hcard V 1 v = v := by simp [csGalSMul]

theorem csGalSMul_of_ne {σ : Dq.carrier ≃ₐ[E] Dq.carrier} (hσ : σ ≠ 1)
    (v : Split.czCarrier (toSplitC hcard V)) : csGalSMul hcard V σ v = csConj hcard V v := by simp [csGalSMul, hσ]

/-- @census none (helper; engine `E10`) -/
noncomputable def csGalAction :
    DistribMulAction (Dq.carrier ≃ₐ[E] Dq.carrier) (Split.czCarrier (toSplitC hcard V)) where
  smul σ v := csGalSMul hcard V σ v
  one_smul v := csGalSMul_one hcard V v
  mul_smul σ τ v := by
    show csGalSMul hcard V (σ * τ) v = csGalSMul hcard V σ (csGalSMul hcard V τ v)
    by_cases hσ : σ = 1
    · subst hσ; rw [one_mul, csGalSMul_one]
    · by_cases hτ : τ = 1
      · subst hτ; rw [mul_one, csGalSMul_one]
      · rw [Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ, Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hτ, Gelfand.RationalStructure.galConj_mul_self,
          csGalSMul_one, csGalSMul_of_ne hcard V Gelfand.RationalStructure.galConj_ne_one,
          csGalSMul_of_ne hcard V Gelfand.RationalStructure.galConj_ne_one, csConj_involutive hcard V v]
  smul_zero σ := by
    show csGalSMul hcard V σ 0 = 0
    by_cases hσ : σ = 1
    · subst hσ; rw [csGalSMul_one]
    · rw [csGalSMul_of_ne hcard V hσ, map_zero]
  smul_add σ v w := by
    show csGalSMul hcard V σ (v + w) = csGalSMul hcard V σ v + csGalSMul hcard V σ w
    by_cases hσ : σ = 1
    · subst hσ; rw [csGalSMul_one, csGalSMul_one, csGalSMul_one]
    · rw [csGalSMul_of_ne hcard V hσ, csGalSMul_of_ne hcard V hσ, csGalSMul_of_ne hcard V hσ,
        map_add]

/-- @census none (helper; engine `E10`) -/
theorem csIsSemilinearAction :
    letI := csGalAction hcard V
    Descent.IsSemilinearAction E Dq.carrier (Split.czCarrier (toSplitC hcard V)) := by
  letI := csGalAction hcard V
  refine ⟨fun σ a v => ?_⟩
  show csGalSMul hcard V σ (a • v) = σ a • csGalSMul hcard V σ v
  by_cases hσ : σ = 1
  · subst hσ; rw [csGalSMul_one, csGalSMul_one]; rfl
  · rw [csGalSMul_of_ne hcard V hσ, csGalSMul_of_ne hcard V hσ, csConj_smul,
      Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ]

/-- @census none (helper; engine `E10`) -/
theorem csKStructure :
    letI := csGalAction hcard V
    Descent.KStructure E Dq.carrier (Split.czCarrier (toSplitC hcard V)) := by
  letI := csGalAction hcard V
  letI := csIsSemilinearAction hcard V
  infer_instance

/-- `M` as an object of S0's category `Descent.VecK ℚ ℚ[√-1]`.  @census none (helper; `E10`) -/
noncomputable def csVecK : Descent.VecK E Dq.carrier :=
  letI : Module E (Split.czCarrier (toSplitC hcard V)) := Module.compHom _ (algebraMap E Dq.carrier)
  letI : IsScalarTower E Dq.carrier (Split.czCarrier (toSplitC hcard V)) := ⟨fun c a x => by
    show ((c • a) • x : Split.czCarrier (toSplitC hcard V)) = algebraMap E Dq.carrier c • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩
  letI := csGalAction hcard V
  { carrier := Split.czCarrier (toSplitC hcard V)
    isKStructure := csKStructure hcard V }

theorem csVecK_smul (σ : Dq.carrier ≃ₐ[E] Dq.carrier) (v : (csVecK hcard V).carrier) :
    σ • v = csGalSMul hcard V σ v := rfl

/-- **The `ℚ`-form `M_ℚ`**: the fixed points of `c`.  @census none (helper; engine `E10`) -/
noncomputable def csForm : Submodule E (csVecK hcard V).carrier :=
  Descent.fixedPoints E Dq.carrier (csVecK hcard V)

/-- **`M = ℚ[√-1] ⊗_ℚ M_ℚ`** — `thm:galoisdescent` for the `ℓ = 0` construction.
@census none (helper; engine `E10`) -/
noncomputable def csBaseChange :
    (Dq.carrier ⊗[E] ↥(csForm hcard V)) ≃ₗ[Dq.carrier] Split.czCarrier (toSplitC hcard V) :=
  LinearEquiv.ofBijective (Descent.descentCounit E Dq.carrier (csVecK hcard V))
    (Descent.descentCounit_bijective E Dq.carrier (csVecK hcard V))

/-- @census none (helper; engine `E10`) -/
theorem csConj_baseChange (v : ↥(csForm hcard V)) :
    csConj hcard V (csBaseChange hcard V ((1 : Dq.carrier) ⊗ₜ[E] v))
      = csBaseChange hcard V ((1 : Dq.carrier) ⊗ₜ[E] v) := by
  have hb : csBaseChange hcard V ((1 : Dq.carrier) ⊗ₜ[E] v) = (v.1 : Split.czCarrier (toSplitC hcard V)) := by
    show (1 : Dq.carrier) • (v.1 : Split.czCarrier (toSplitC hcard V)) = _
    rw [one_smul]
  have hfix := v.2 Dq.conj
  rw [csVecK_smul, csGalSMul_of_ne hcard V Gelfand.RationalStructure.galConj_ne_one] at hfix
  rw [hb]
  exact hfix

/-- **The `RationalSetup` of the `ℓ = 0` construction.**  @census none (helper; engine `E10`) -/
noncomputable def csRationalSetup :
    RationalSetupOver 0 E Dq ↥(csForm hcard V) (Split.czCarrier (toSplitC hcard V)) where
  baseChange := csBaseChange hcard V
  weight := Split.czWeight (toSplitC hcard V)
  gic := Split.czGIC (toSplitC hcard V)
  conj := csConj hcard V
  conj_smul := csConj_smul hcard V
  conj_involutive := csConj_involutive hcard V
  conj_baseChange := csConj_baseChange hcard V
  conj_comp := csConj_comp hcard V
  conj_X := csConj_X hcard V
  conj_Y := csConj_Y hcard V
  conj_H := csConj_H hcard V

/-- **The object of `HC_0(𝔤,K)_ℚ` that engine `E10` constructs from `V`.**
@census none (helper; engine `E10`) -/
noncomputable def csHCQObj : HCEObj 0 E Dq where
  form := ↥(csForm hcard V)
  carrier := Split.czCarrier (toSplitC hcard V)
  setup := csRationalSetup hcard V
  admissible := Split.czComp_finiteDimensional (toSplitC hcard V)
  centralCharacter := fun n hn => Split.czComp_eq_bot (toSplitC hcard V) (by omega)
  fg := Split.czFG (toSplitC hcard V)

/-! #### The comparison isomorphism `𝔼_ℚ(M) ≅ V`

At `ℓ = 0` the comparison map is not a square root of anything: `M_1` and `M_{-1}` are `V(+)` and
`V(−)` **by construction**, and the identification is the canonical injection of a summand followed
by the canonical injection into the ambient `T`.  The two edges of `𝔼_ℚ(M)` are `X|_{M_{-1}} = φ_a`
and `Y|_{M_1} = φ_b`, which are the wall branches of `Split.czXAmb`/`Split.czYAmb`, and the rational structure
of `𝔼_ℚ(M)` is `c` itself (`phiCyc_eq_conj`), which on the ambient is `V`'s own `φ_{•,c}`. -/

/-- Transport in `𝔼_ℚ(M)` at `ℓ = 0` is the identity on carrier values.  @census none (helper) -/
theorem cycRepEqCast_val {A : HCEObj 0 E Dq} (hA : ObjSpecC hcard A) {v w : (cyclicQ hcard).V}
    (h : v = w) (m : V2 A v) :
    (((E_Cyc_rep hcard A hA).eqCast h m : V2 A w)).1 = m.1 := by
  subst h; rfl

/-- The transported `c`-structure of `𝔼_ℚ(M)` at `ℓ = 0`, on carrier values.
@census none (helper) -/
theorem cycRepPhi'_val {A : HCEObj 0 E Dq} (hA : ObjSpecC hcard A) {v w : (cyclicQ hcard).V}
    (h : Dq.conj • v = w) (m : V2 A v) :
    (((E_Cyc_rep hcard A hA).φ' Dq.conj h m : V2 A w)).1 = phiCyc A v m.1 := by
  rw [RationalQuiver.Rep.φ'_apply, cycRepEqCast_val hcard hA h]
  show galActC A Dq.conj v m.1 = _
  rw [galActC_of_ne A Gelfand.RationalStructure.galConj_ne_one]

/-- `Rep.Hom`'s `rational` field, read at a NAMED target vertex.  @census none (helper) -/
theorem cyc_rational_of_phi' {M N : RationalQuiver.Rep (cyclicQ hcard)}
    (psi : ∀ v : (cyclicQ hcard).V, M.M v →ₗ[Dq.carrier] N.M v)
    {σ : Dq.carrier ≃ₐ[E] Dq.carrier} {v w : (cyclicQ hcard).V} (hvw : σ • v = w)
    (m : M.M v) (H : psi w (M.φ' σ hvw m) = N.φ' σ hvw (psi v m)) :
    psi (σ • v) (M.φ σ v m) = N.φ σ v (psi v m) := by
  subst hvw; exact H

/-- A `Rep.Hom` with invertible vertex components has an inverse `Rep.Hom`.
@census none (helper) -/
def cycRepHomInv {M N : RationalQuiver.Rep (cyclicQ hcard)}
    (f : RationalQuiver.Rep.Hom M N)
    (g : ∀ v : (cyclicQ hcard).V, N.M v →ₗ[Dq.carrier] M.M v)
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









/-- The comparison map intertwines `φ_{v,c}` with the rational structure of `𝔼_ℚ(M)` — which at
`ℓ = 0` is `c` itself.  @census none (helper; engine `E10`) -/
theorem csEmb_rational_conj (hA : ObjSpecC hcard (csHCQObj hcard V)) :
    ∀ (v : Fin 2) (m : Split.czVM (toSplitC hcard V) v),
      Split.czEmb (toSplitC hcard V) (RQuiver.twoLoopsSwapPerm v)
          (V.obj.toRep.φ' Dq.conj (cyclicQ_smul_vertex hcard v) m)
        = (E_Cyc_rep hcard (csHCQObj hcard V) hA).φ' Dq.conj (cyclicQ_smul_vertex hcard v)
            (Split.czEmb (toSplitC hcard V) v m)
  | 0, m => by
      refine Subtype.ext ?_
      rw [cycRepPhi'_val hcard hA]
      rw [phiCyc_eq_conj (csHCQObj hcard V) 0 _ (Split.czEmb (toSplitC hcard V) 0 m).2]
      show DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) 1
            (Split.czFibPlus (toSplitC hcard V) (csVphiMinus hcard V m))
          = csConj hcard V (DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) (-1)
              (Split.czFibMinus (toSplitC hcard V) m))
      rw [csConj_lof]
      exact Split.czLof_congr (toSplitC hcard V) (by norm_num) _ _
        (csConjAmb_iotaMinus hcard V m).symm
  | 1, m => by
      refine Subtype.ext ?_
      rw [cycRepPhi'_val hcard hA]
      rw [phiCyc_eq_conj (csHCQObj hcard V) 1 _ (Split.czEmb (toSplitC hcard V) 1 m).2]
      show DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) (-1)
            (Split.czFibMinus (toSplitC hcard V) (csVphiPlus hcard V m))
          = csConj hcard V (DirectSum.lof Dq.carrier ℤ (Split.czFib (toSplitC hcard V)) 1
              (Split.czFibPlus (toSplitC hcard V) m))
      rw [csConj_lof]
      exact Split.czLof_congr (toSplitC hcard V) (by norm_num) _ _
        (csConjAmb_iotaPlus hcard V m).symm

/-- **The comparison map as a morphism of rational representations** `V → 𝔼_ℚ(M)`.
@census none (helper; engine `E10`) -/
noncomputable def csNatHom (hA : ObjSpecC hcard (csHCQObj hcard V)) :
    RationalQuiver.Rep.Hom V.obj.toRep (E_Cyc_rep hcard (csHCQObj hcard V) hA) where
  ψ v := Split.czEmb (toSplitC hcard V) v
  edge e m := Split.czEmb_edge (toSplitC hcard V) e m
  rational σ v m := by
    by_cases hσ : σ = 1
    · subst hσ
      refine cyc_rational_of_phi' hcard (M := V.obj.toRep)
        (N := E_Cyc_rep hcard (csHCQObj hcard V) hA) (fun u => Split.czEmb (toSplitC hcard V) u)
        (one_smul _ v) m ?_
      rw [RationalQuiver.Rep.φ'_one, RationalQuiver.Rep.φ'_one]
      exact RationalQuiver.Rep.eqCast_natural (M := V.obj.toRep)
        (N := E_Cyc_rep hcard (csHCQObj hcard V) hA) (fun u => Split.czEmb (toSplitC hcard V) u) _ m
    · have hg := Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ
      subst hg
      exact cyc_rational_of_phi' hcard (M := V.obj.toRep)
        (N := E_Cyc_rep hcard (csHCQObj hcard V) hA) (fun u => Split.czEmb (toSplitC hcard V) u)
        (cyclicQ_smul_vertex hcard v) m (csEmb_rational_conj hcard V hA v m)

/-- The inverse morphism.  @census none (helper; engine `E10`) -/
noncomputable def csNatHomInv (hA : ObjSpecC hcard (csHCQObj hcard V)) :
    RationalQuiver.Rep.Hom (E_Cyc_rep hcard (csHCQObj hcard V) hA) V.obj.toRep :=
  cycRepHomInv hcard (csNatHom hcard V hA) (fun v => (Split.czEmbEquiv (toSplitC hcard V) v).symm.toLinearMap)
    (fun v x => (Split.czEmbEquiv (toSplitC hcard V) v).symm_apply_apply x)
    (fun v y => (Split.czEmbEquiv (toSplitC hcard V) v).apply_symm_apply y)

/-- **`𝔼_ℚ(M) ≅ V`** in the category of finite-dimensional rational representations of the cyclic
quiver.  @census none (helper; engine `E10`) -/
noncomputable def csNatIsoFD (hA : ObjSpecC hcard (csHCQObj hcard V)) :
    (E_Cyc_obj hcard (csHCQObj hcard V) hA).obj ≅ V.obj where
  hom := csNatHomInv hcard V hA
  inv := csNatHom hcard V hA
  hom_inv_id := RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun x =>
    (Split.czEmbEquiv (toSplitC hcard V) v).apply_symm_apply x)
  inv_hom_id := RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun y =>
    (Split.czEmbEquiv (toSplitC hcard V) v).symm_apply_apply y)

/-- **`𝔼_ℚ(M) ≅ V`** in `Rep^nil(cyclic_ℚ)`.  @census none (helper; engine `E10`) -/
noncomputable def csNatIsoObj (hA : ObjSpecC hcard (csHCQObj hcard V)) :
    E_Cyc_obj hcard (csHCQObj hcard V) hA ≅ V :=
  ObjectProperty.isoMk (RationalQuiver.RepNil (cyclicQ hcard)) (csNatIsoFD hcard V hA)

end E10

/-- **`RQ-5.07`, essential surjectivity of `𝔼_ℚ` at `ℓ = 0`** — engine `E10`.  Every nilpotent
finite-dimensional `ℚ`-rational representation of the cyclic quiver is `𝔼_ℚ(M)` for the
Harish-Chandra module `M` that `csHCQObj` constructs, the isomorphism being the canonical
injection of the two summands `M_1 = V(+)`, `M_{-1} = V(−)`.
@census none (helper; engine `E10`, ruling `R-S8-35`) -/
theorem E_Cyc_essSurj (h : E_CycSpec hcard) : (E_CycFunctor hcard h).EssSurj where
  mem_essImage W := ⟨csHCQObj hcard W, ⟨csNatIsoObj hcard W (h.1 _)⟩⟩


end Functor

section Functor

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)

/-- **`RQ-5.07` reduced to its three residues** — the specification, fullness and essential
surjectivity.  Faithfulness is `E_Cyc_faithful`, and the pin `e.functor = E_CycFunctor` is `rfl`
because `Functor.asEquivalence`'s functor is the given functor.  @census none (helper) -/
theorem cyclic_E_Q_equivalence_of (h : E_CycSpec hcard) (hfull : (E_CycFunctor hcard h).Full)
    (hess : (E_CycFunctor hcard h).EssSurj) :
    ∃ (h : E_CycSpec hcard) (e : HCEObj 0 E Dq ≌ RepNilCycQ hcard), e.functor = E_CycFunctor hcard h := by
  haveI := hfull
  haveI := hess
  haveI := E_Cyc_faithful hcard h
  haveI : (E_CycFunctor hcard h).IsEquivalence := { }
  exact ⟨h, (E_CycFunctor hcard h).asEquivalence, rfl⟩

/-- **`RQ-5.07` reduced to fullness and essential surjectivity** — the specification is proved
(`E_Cyc_spec`) and faithfulness is `E_Cyc_faithful`, so these two are the whole residue.
@census none (helper) -/
theorem cyclic_E_Q_equivalence_of_full_essSurj
    (hfull : (E_CycFunctor hcard (E_Cyc_spec hcard)).Full)
    (hess : (E_CycFunctor hcard (E_Cyc_spec hcard)).EssSurj) :
    ∃ (h : E_CycSpec hcard) (e : HCEObj 0 E Dq ≌ RepNilCycQ hcard), e.functor = E_CycFunctor hcard h :=
  cyclic_E_Q_equivalence_of hcard (E_Cyc_spec hcard) hfull hess

/-- **`RQ-5.07`** (`thm:cyclicEEQQequivalence`) — **Main Theorem D**.

For `ℓ = 0`, the assignment `𝔼_ℚ : M_ℚ ↦ (𝔼_{ℚ[√-1]}(M_{ℚ[√-1]}), φ_•)` from `HC_0(𝔤,K)_ℚ` to the
category of `ℚ`-rational finite-dimensional nilpotent representations of the `ℚ`-rational **cyclic**
quiver is **well defined** (`C1`: `E_CycSpec` holds, so `E_CycFunctor` is a functor) and an
**equivalence of categories** (`C3`), with that target (`C2`); the equivalence's functor **is**
`𝔼_ℚ`, on the nose.

@census none (WP-8c field-generic copy; the frozen claimant of RQ-5.07 is unchanged)
@source    thm:cyclicEEQQequivalence
(clauses of the frozen original:)   RQ-5.07-H1, RQ-5.07-H2, RQ-5.07-C1, RQ-5.07-C2, RQ-5.07-C3, RQ-5.07-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION, two items.  (1) The concrete category `HC_0(𝔤,K)_ℚ`
(`Gelfand/Category.lean`, ruling `R-S8-6`) exactly as for `RQ-5.05`'s `E_Q_equivalence`, whose
`@divergence` applies verbatim (descent presentation of the `ℚ`-objects; Galois binders).  (2)
Census clause `RQ-5.07-C4` — "it is obtained **analogously** by unipotent stabilization" — has
`if_missing = JUSTIFIED_REFORMULATION` and the census's own `notes` cell reads "proof route".  It
is realized rather than asserted: the rational structure of `E_Cyc_rep` at `ℓ = 0` **is**
`φ_{±,c} := c`, the stabilized maps being replaced by the identity (`limAtC` is the weight
projection, the identity of `M(∓1)`; `phiCyc_eq_conj`), with no stabilization run, as in the tex
(v2 amendment T3-a1, route fix F-B11). -/
theorem cyclic_E_Q_equivalence :
    ∃ (h : E_CycSpec Dq.card_gal) (e : HCEObj 0 E Dq ≌ RepNilCycQ Dq.card_gal),
      e.functor = E_CycFunctor Dq.card_gal h :=
  cyclic_E_Q_equivalence_of_full_essSurj Dq.card_gal
    (E_Cyc_fullS Dq.card_gal (E_Cyc_spec Dq.card_gal))
    (E_Cyc_essSurj Dq.card_gal (E_Cyc_spec Dq.card_gal))

end Functor

/-! ### G5.1 inhabitant of `ObjSpecC` (final-release WP-9, 2026-10-03)

*(Added 2026-10-03, `R-PROC-4` amendment of `S10`, final-release WP-9: `rqaudit models` reported
`ObjSpecC` `MODEL-MISSING`.)*  The frozen `ℚ`-case `ObjSpecC` is inhabited by
`Gelfand/Models.lean`'s `zeroObjSpecC` at `Gelfand.zeroHCQObj 0`.  Here the same object is built
over `(E, D)` — `PUnit` over `PUnit`, the degenerate `trivialWeightData`, the identity as
conjugation; disclosed as degenerate — and `ObjSpecC` at it is not proved by `Subsingleton` but
read off the general theorem `E_Cyc_spec`, which proves `ObjSpecC` at **every** object of
`HC_0(𝔤,K)_E`. -/

section Witness

variable (E) (D : SqrtNegOneExt E)

/-- `D' ⊗_E 0 = 0`.  @census none (G5 helper) -/
theorem punit_tensor_eq_zeroC (x : D.carrier ⊗[E] PUnit) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul a v => rw [Subsingleton.elim v 0, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- The zero `RationalSetupOver 0 E D`: `PUnit` over `PUnit`.  @census none (G5 helper) -/
noncomputable def zeroRationalSetupOverC : RationalSetupOver 0 E D PUnit PUnit where
  baseChange :=
    { toFun := fun _ => 0
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun _ => 0
      left_inv := fun x => (punit_tensor_eq_zeroC E D x).symm
      right_inv := fun _ => Subsingleton.elim _ _ }
  weight := trivialWeightData D.carrier PUnit
  gic := ⟨1, Subsingleton.elim _ _⟩
  conj := AddEquiv.refl PUnit
  conj_smul _ _ := Subsingleton.elim _ _
  conj_involutive _ := rfl
  conj_baseChange _ := Subsingleton.elim _ _
  conj_comp _ v _ := by
    rw [Subsingleton.elim (AddEquiv.refl PUnit v) 0]; exact Submodule.zero_mem _
  conj_X _ := Subsingleton.elim _ _
  conj_Y _ := Subsingleton.elim _ _
  conj_H _ := Subsingleton.elim _ _

/-- **The zero object of `HC_0(𝔤,K)_E`.**  The carrier of the `ObjSpecC` witness below; disclosed
as degenerate.  @census none (G5 helper) -/
noncomputable def zeroHCEObjC : HCEObj 0 E D where
  form := PUnit
  carrier := PUnit
  setup := zeroRationalSetupOverC E D
  admissible _ := ⟨⟨∅, by
    rw [eq_top_iff]
    intro v _
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _⟩⟩
  centralCharacter _ _ := by
    rw [eq_bot_iff]
    intro v _
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _
  fg := ⟨∅, gkSpanGraded_eq_top _ fun N _ _ _ => by
    rw [eq_top_iff]
    intro v _
    rw [Subsingleton.elim v 0]
    exact Submodule.zero_mem _⟩

/-- **G5 inhabitant of `ObjSpecC`** — at the zero object, as an instance of `E_Cyc_spec` (which
proves `ObjSpecC` at every object).  @census none (G5 inhabitant) -/
theorem zeroObjSpecC : ObjSpecC D.card_gal (zeroHCEObjC E D) :=
  (E_Cyc_spec D.card_gal).1 _

/-- The same witness at `E = ℚ`, `D = ℚ[√-1]`: no explicit binder.  @census none (G5 inhabitant) -/
theorem zeroObjSpecC_qi : ObjSpecC SqrtNegOneExt.qi.card_gal (zeroHCEObjC ℚ SqrtNegOneExt.qi) :=
  zeroObjSpecC ℚ SqrtNegOneExt.qi

end Witness


/-! ## The native `𝔼_E` on `HC ℓ E D` (stage T3) -/

section NativeHC

set_option linter.unusedSectionVars false

variable {D : ImagUnit E}

section CyclicEssSurj

/-- The underlying split representation of `V ∈ Rep^nil(Γ_E)`, `ℓ = 0`.  @census none (helper) -/
noncomputable def toSplitRepZ (V : (RepNilTarget D 0).FullSubcategory) :
    RationalQuiver.FDRep (cyclicSplit D.L) where
  toRep := RationalQuiver.Rep.ofFiniteDimensional (Γ := cyclicSplit D.L)
    (fun v => V.obj.toRep.M v) (fun _ _ => AddEquiv.refl _)
    (fun σ v a m => by rw [galSelf_apply]; rfl) (fun _ _ _ _ => rfl)
    (fun e => V.obj.toRep.φEdge e) (fun _ _ _ _ h => by cases h; rfl)
  finiteDimensional v := V.obj.finiteDimensional v

/-- `toSplitRepZ V` is nilpotent.  @census none (helper) -/
noncomputable abbrev toSplitZ (V : (RepNilTarget D 0).FullSubcategory) :
    (RationalQuiver.RepNil (cyclicSplit D.L)).FullSubcategory :=
  ⟨toSplitRepZ V, V.property⟩

/-- **Essential surjectivity, `ℓ = 0`, `√-1 ∈ E`** (Steps C-5b, C-5c).  @census none (helper) -/
theorem E_ECyc_essSurj_split (hs : ∃ a : E, a * a = -1) (V : (RepNilTarget D 0).FullSubcategory) :
    (E_ECyc (D := D)).essImage V := by
  obtain ⟨X, ⟨e⟩⟩ := (Split.E_CycSplit_essSurj (F := D.L)).mem_essImage (toSplitZ V)
  let A : HC 0 E D := HC.ofLambda hs (Split.hcFToLambdaObj D.L 0 X)
  let f : RationalQuiver.Rep.Hom (E_Cyc_repZ A) V.obj.toRep :=
    { ψ := e.hom.hom.ψ
      edge := e.hom.hom.edge
      rational := fun σ v m => by
        obtain rfl := D.eq_one_of_sqrt hs σ
        exact Gelfand.EssSurj.rational_one _ v m }
  refine ⟨A, ⟨ObjectProperty.isoMk _ (Gelfand.EssSurj.fdRepIsoOfComponents (M := (E_Cyc_objZ A).obj) (N := V.obj) f
    e.inv.hom.ψ (fun v x => ?_) (fun v y => ?_))⟩⟩
  · exact congrArg (fun φ => φ.hom.ψ v x) e.hom_inv_id
  · exact congrArg (fun φ => φ.hom.ψ v y) e.inv_hom_id

variable (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1)

/-- A vertex index of `cyclicOfCardTwo`.  @census none (helper) -/
abbrev vtxCZ (v : Fin 2) : (cyclicQ (Dq := D.sqrtExt hc) (D.sqrtExt hc).card_gal).V := v

/-- An edge index of `cyclicOfCardTwo`.  @census none (helper) -/
abbrev edgeCZ (e : Fin 2) : (cyclicQ (Dq := D.sqrtExt hc) (D.sqrtExt hc).card_gal).E := e

theorem cycE_smul_vertex_cardTwo (σ : D.L ≃ₐ[E] D.L) (v : Fin 2) :
    (σ • vtxZ D v : Fin 2) = (σ • vtxCZ hc v : Fin 2) := by
  classical
  have h1 : @Eq (Fin 2) (σ • vtxZ D v) (galVtxZ σ v) := vtxZ_smul σ v
  have h2 : @Eq (Fin 2) (σ • vtxCZ hc v) (if σ = 1 then v else RQuiver.twoLoopsSwapPerm v) :=
    cyclicQ_smul_eq (D.sqrtExt hc).card_gal σ v
  rw [h1, h2]
  unfold galVtxZ
  by_cases hσ : σ = 1
  · subst hσ; rw [if_pos D.chi_one, if_pos rfl]
  · rw [if_neg (by rw [D.chi_eq_one_iff]; exact fun h => hσ (D.ext_i (by rw [h]; rfl))), if_neg hσ]

theorem cycE_smul_edge_cardTwo (σ : D.L ≃ₐ[E] D.L) (e : Fin 2) :
    (σ • edgeZ D e : Fin 2) = (σ • edgeCZ hc e : Fin 2) := by
  rw [edgeZ_smul]
  by_cases hσ : σ = 1
  · subst hσ; rw [if_pos D.chi_one]; exact (one_smul (D.L ≃ₐ[E] D.L) (edgeCZ hc e)).symm
  · rw [if_neg (by rw [D.chi_eq_one_iff]; exact fun h => hσ (D.ext_i (by rw [h]; rfl))),
      Gelfand.RationalStructure.eq_galConj_of_ne_one (D.sqrtExt hc).card_gal hσ]
    exact (cyclicQ_smul_edge (D.sqrtExt hc).card_gal e).symm

/-- `V ∈ Rep^nil(Γ_E)`, `ℓ = 0`, in the engine's presentation (`cyclicOfCardTwo`).
@census none (helper) -/
noncomputable def toCardTwoZ (V : (RepNilTarget D 0).FullSubcategory) :
    RepNilCycQ (Dq := D.sqrtExt hc) (D.sqrtExt hc).card_gal :=
  ⟨⟨V.obj.toRep.reρ (Γ := RationalQuiver.cyclicOfSign E D.L D.chiHom)
      (ρ' := (cyclicQ (Dq := D.sqrtExt hc) (D.sqrtExt hc).card_gal).ρ)
      (cycE_smul_vertex_cardTwo hc) (cycE_smul_edge_cardTwo hc),
    V.obj.finiteDimensional⟩, V.property⟩

theorem E_Cyc_repZ_eqCast_val (A : HC 0 E D)
    {v w : (RationalQuiver.cyclicOfSign E D.L D.chiHom).V} (h : v = w) (m : V2Z A v) :
    (((E_Cyc_repZ A).eqCast h m : V2Z A w)).1 = m.1 := by
  subst h; rfl

/-- **Essential surjectivity, `ℓ = 0`, `√-1 ∉ E`** (Step C-7): the module `M` of the `ℓ = 0`
construction with `φ_c^M`, Galois descent, and `𝔼_E(M_E) = V` by the canonical embeddings.
@census none (helper) -/
theorem E_ECyc_essSurj_nonsplit (hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1)
    (V : (RepNilTarget D 0).FullSubcategory) :
    (E_ECyc (D := D)).essImage V := by
  let V' := toCardTwoZ hc V
  let B := csHCQObj (D.sqrtExt hc).card_gal V'
  have hA : ObjSpecC (D.sqrtExt hc).card_gal B := (E_Cyc_spec (D.sqrtExt hc).card_gal).1 B
  let A : HC 0 E D := B.toHC
  let g : RationalQuiver.Rep.Hom V.obj.toRep (E_Cyc_repZ A) :=
    { ψ := fun v => Split.czEmb (toSplitC (D.sqrtExt hc).card_gal V') v
      edge := fun e m => Split.czEmb_edge (toSplitC (D.sqrtExt hc).card_gal V') e m
      rational := fun σ v m => by
        rcases D.chi_cases σ with hσ | hσ
        · obtain rfl := D.eq_one_of_chi_one hσ
          exact Gelfand.EssSurj.rational_one (M := V.obj.toRep) (N := E_Cyc_repZ A)
            (fun u => Split.czEmb (toSplitC (D.sqrtExt hc).card_gal V') u) v m
        · have hvw : σ • vtxZ D v = vtxZ D (RQuiver.twoLoopsSwapPerm v) := by
            rw [vtxZ_smul]; unfold galVtxZ; rw [if_neg (by rw [hσ]; decide)]
          refine Gelfand.EssSurj.rational_of_φ' (M := V.obj.toRep) (N := E_Cyc_repZ A)
            (fun u => Split.czEmb (toSplitC (D.sqrtExt hc).card_gal V') u) hvw m ?_
          have hconj := (D.sqrtExt_conj hc hσ).symm
          subst hconj
          have key := csEmb_rational_conj (D.sqrtExt hc).card_gal V' hA v m
          refine Eq.trans ?_ (key.trans (Subtype.ext ?_))
          · exact congrArg (Split.czEmb (toSplitC (D.sqrtExt hc).card_gal V') _)
              (Gelfand.EssSurj.eqCast_eqCast V.obj.toRep _ _ _).symm
          · rw [cycRepPhi'_val _ hA, RationalQuiver.Rep.φ'_apply]
            refine Eq.trans ?_ (E_Cyc_repZ_eqCast_val A hvw _).symm
            exact (phiCyc_eq_conj B v _
              (Split.czEmb (toSplitC (D.sqrtExt hc).card_gal V') v m).2).trans
              (HCEObj.toHC_galAct_neg B (D.chi_sqrtExt_conj hc) _).symm }
  refine ⟨A, ⟨(ObjectProperty.isoMk _ (Gelfand.EssSurj.fdRepIsoOfComponents (M := V.obj) (N := (E_Cyc_objZ A).obj)
    g (fun v => (Split.czEmbEquiv (toSplitC (D.sqrtExt hc).card_gal V') v).symm.toLinearMap)
    (fun v x => (Split.czEmbEquiv (toSplitC (D.sqrtExt hc).card_gal V') v).symm_apply_apply x)
    (fun v y => (Split.czEmbEquiv (toSplitC (D.sqrtExt hc).card_gal V') v).apply_symm_apply y))).symm⟩⟩

end CyclicEssSurj

theorem cycEssSurj : (E_ECyc (D := D)).EssSurj where
  mem_essImage V := by
    by_cases hs : ∃ a : E, a * a = -1
    · exact E_ECyc_essSurj_split hs V
    · exact E_ECyc_essSurj_nonsplit (D.exists_chi_neg_one_iff.mpr hs) V

end NativeHC

end RationalQuivers.Gelfand.Cyclic
