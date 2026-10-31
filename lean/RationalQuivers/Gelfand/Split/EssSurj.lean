module

public import RationalQuivers.Gelfand.Split.Chains
public import RationalQuivers.Unipotent.SquareRoots

@[expose] public section

/-!
# Essential surjectivity of `𝔼_F` per the tex (tex §5.1 ES sentence; the construction of §5.3)

Step O-7h of the author's proof of `prop:splitequivalence` (census `RQ2-5.02`): essential
surjectivity "from the construction in the proof of `thm:EEequivalence` below, with all rational
structures omitted" (Step O-18a over a field `L ∋ √-1`), then "`X_⋆` on `V(⋆)` is a polynomial
`p(n_⋆)` with `p(0) = 1`" (`xStar_eq_poly`, the sole claimant of v1's `RQ-5.05-C17`), the two
intertwiners `φ_{b₊}p(n_⋆) = p(n_+)φ_{b₊}`, `p(n_⋆)φ_{a₊} = φ_{a₊}p(n_+)`, and the isomorphism
`(1_{V(−)}, 1_{V(⋆)}, p(n_+)^{−1})` (`isoPoly`, stated for **any** `p` with `p(n_⋆) = X_⋆` and
`p(0) = 1`; `essSurj` chooses `p` by `Classical.choose`).  `equivalence` is the claimant of
`RQ2-5.02`.

## The shared construction (route (α), plan rev 3a §2.1a, B-6)
The first part of this module is the `c`-free core of the essential-surjectivity construction of
`thm:EEequivalence`'s proof: `n_• `, `φ_• = ℓ² + 4n_•`, `φ_•^{1/2}` w.r.t. `γ = ℓ`
(`def:squareroots`), `ξ^{(j)}_{•,±}`, the carrier `M`, `X`, `Y`, `[X,Y] = H`, the generalized
infinitesimal character and finite generation (engine `E2`), all over a **split** representation
`W : (RepNilRelSplit L).FullSubcategory`, and `SplitEssSurjData W` with the `C9` isomorphisms and the
`C13` pins.  The non-split construction (`GF.EssSurjData V`, v1 `Gelfand/GeneralField/Equivalence.lean`,
relocated in T3; since WP-10, `542ebf7`, it is `Gelfand.EssSurj.EssSurjData` in
`Gelfand/EssSurj/Construction.lean`; 2026-10-21 note, O-V2-6 round 2) **extends**
`SplitEssSurjData (toSplitW V)` and adds only the `c`-clauses (Step O-18b).  In the tex the
construction is written once, in §5.3, and §5.1 forward-cites it;
Lean cannot forward-reference, so it sits here (`EX-ORDER-ES`, MODULE-ORDER rule `FWD-CITE`).

## Provenance (v2 WP-9, stage T2)
The core is v1's `GF/Equivalence.lean` `c`-free sections (`EssSurj` accessors, `VertexOperators`,
`PinnedComposites`, `StarChain*`, `E2Carrier`…`E2FG`, `E2Pins`), moved here and re-parametrized over
`W` (the WP-4 spike's port, `v2-spike-wp4` @ `e864192`, `R-V2-3`); `xStar_eq_poly`, the
intertwiners, `isoPoly`, `essSurj`, `equivalence` are new.  v1's split engine `E11` (the asymmetric
wall normalization) is **deleted** (OP-2); its construction survives only as the unformalized tex
remark `rmk:asymmetricsplitES` (`EX-E11-REMARK`).
-/

namespace RationalQuivers.Gelfand.Split

section EndAlgebra

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

/-- `(S + a)(S + b) = S² + (a+b)S + ab` in `End R W`: the two factors of `C11` differ from `S`
by scalars, which are central.  @census none (helper) -/
theorem end_add_smul_mul (S : Module.End R W) (a b : R) :
    (S + a • 1) * (S + b • 1) = S ^ 2 + (a + b) • S + (a * b) • 1 := by
  rw [mul_add, add_mul, add_mul]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, sq, add_smul]
  rw [mul_comm b a]
  abel

end EndAlgebra

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory RationalQuivers.Gelfand
open scoped TensorProduct Classical

/-- `ℓ` as a unit, the square root of `ℓ²` w.r.t. which `φ_•^{1/2}` is taken.
@census none (helper; core) -/
noncomputable def ellUnit (K : Type) [Field K] [CharZero K] {m : ℕ} (hm : 1 ≤ m) : Kˣ :=
  Units.mk0 (m : K) (by exact_mod_cast (by omega : m ≠ 0))

set_option linter.unusedSectionVars false

variable {L : Type} [Field L] [CharZero L] {ℓ : ℕ} (hℓ : 1 ≤ ℓ)

section Vertex

variable (W : (RepNilRelSplit L).FullSubcategory)

/-- The vertex spaces of a split representation, by index (`−`=0, `⋆`=1, `+`=2).
@census none (helper; core) -/
abbrev VM (v : Fin 3) : Type := W.obj.toRep.M v

/-- The additive group structure of `VM W v`, at the index type `Fin 3`: instance search no longer
unfolds `(gelfandSplit L).V` to `Fin 3`. Port v4.35. @census none (helper) -/
instance VM.instAddCommGroup (v : Fin 3) : AddCommGroup (VM W v) := W.obj.toRep.addCommGroup v

/-- The `L`-module structure of `VM W v`, at the index type `Fin 3` (see `VM.instAddCommGroup`).
Port v4.35. @census none (helper) -/
instance VM.instModule (v : Fin 3) : Module L (VM W v) := W.obj.toRep.module v

/-- `VM W v` is finite-dimensional, at the index type `Fin 3` (see `VM.instAddCommGroup`).
Port v4.35. @census none (helper) -/
instance VM.instFiniteDimensional (v : Fin 3) : FiniteDimensional L (VM W v) :=
  W.obj.finiteDimensional v

/-- The edge maps, by index (`a₋`=0, `b₋`=1, `a₊`=2, `b₊`=3).  @census none (helper; core) -/
noncomputable def Vedge (e : Fin 4) :
    VM W (RQuiver.gelfand.source e) →ₗ[L] VM W (RQuiver.gelfand.target e) :=
  W.obj.toRep.φEdge e

/-- `n_+ := φ_{b₊}φ_{a₊}`, `n_⋆ := φ_{a₋}φ_{b₋}`, `n_- := φ_{b₋}φ_{a₋}`.  @census none (helper; core) -/
noncomputable def nOp : ∀ v : Fin 3, Module.End L (VM W v)
  | 0 => (Vedge W 1).comp (Vedge W 0)
  | 1 => (Vedge W 0).comp (Vedge W 1)
  | 2 => (Vedge W 3).comp (Vedge W 2)

/-- `φ_{a₊}φ_{b₊}`, the other candidate for `n_⋆`.  @census none (helper; core) -/
noncomputable def nStarPlus : Module.End L (VM W 1) := (Vedge W 2).comp (Vedge W 3)

/-- `φ_• := ℓ²·𝟏 + 4n_•`.  @census none (helper; core) -/
noncomputable def phiOp (ℓ : ℕ) (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) :
    Module.End L (VM W v) :=
  ((ℓ : L) ^ 2) • 1 + (4 : L) • nOp W v

/-- `φ_•^{1/2}` (`def:squareroots` w.r.t. `ℓ`).  @census none (helper; core) -/
noncomputable def sqrtPhi (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) :
    Module.End L (VM W v) :=
  sqrtOfScalarPlusNilpotent (two_ne_zero : (2 : L) ≠ 0) (ellUnit L hℓ) (phiOp ℓ W v)

/-- `ξ^{(j)}_{•,±} := φ_•^{1/2} ± j·𝟏` (`C11`).  @census none (helper; core) -/
noncomputable def xiOp (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3)
    (s : ℤ) (j : ℤ) : Module.End L (VM W v) :=
  sqrtPhi hℓ W v + ((s * j : ℤ) : L) • 1

/-- **`C10`**: `n_⋆ = φ_{a₋}φ_{b₋} = φ_{a₊}φ_{b₊}` — the relation, read in `W`.
@census none (helper; core) -/
theorem nOp_star_eq_nStarPlus : nOp W 1 = nStarPlus W := by
  have hnil : W.obj.toRep.pathMap (a := vtxStar L) (b := vtxStar L)
      Quiver.Path.nil = LinearMap.id := RationalQuiver.Rep.pathMap_nil _ _
  have hbm : W.obj.toRep.pathMap (a := vtxStar L) (b := vtxMinus L)
      (Quiver.Path.nil.cons RQuiver.bMinus)
      = W.obj.toRep.arrowMap (a := vtxStar L) (b := vtxMinus L)
          RQuiver.bMinus
        ∘ₗ W.obj.toRep.pathMap (a := vtxStar L) (b := vtxStar L)
          Quiver.Path.nil := RationalQuiver.Rep.pathMap_cons _ _ _
  have hpm : W.obj.toRep.pathMap (a := vtxStar L) (b := vtxStar L)
      RQuiver.pathMinus
      = W.obj.toRep.arrowMap (a := vtxMinus L) (b := vtxStar L)
          RQuiver.aMinus
        ∘ₗ W.obj.toRep.pathMap (a := vtxStar L) (b := vtxMinus L)
          (Quiver.Path.nil.cons RQuiver.bMinus) := RationalQuiver.Rep.pathMap_cons _ _ _
  have hbp : W.obj.toRep.pathMap (a := vtxStar L) (b := vtxPlus L)
      (Quiver.Path.nil.cons RQuiver.bPlus)
      = W.obj.toRep.arrowMap (a := vtxStar L) (b := vtxPlus L)
          RQuiver.bPlus
        ∘ₗ W.obj.toRep.pathMap (a := vtxStar L) (b := vtxStar L)
          Quiver.Path.nil := RationalQuiver.Rep.pathMap_cons _ _ _
  have hpp : W.obj.toRep.pathMap (a := vtxStar L) (b := vtxStar L)
      RQuiver.pathPlus
      = W.obj.toRep.arrowMap (a := vtxPlus L) (b := vtxStar L)
          RQuiver.aPlus
        ∘ₗ W.obj.toRep.pathMap (a := vtxStar L) (b := vtxPlus L)
          (Quiver.Path.nil.cons RQuiver.bPlus) := RationalQuiver.Rep.pathMap_cons _ _ _
  have hrel : W.obj.toRep.pathMap (a := vtxStar L) (b := vtxStar L)
      RQuiver.pathMinus
      = W.obj.toRep.pathMap (a := vtxStar L) (b := vtxStar L)
        RQuiver.pathPlus := W.property.2
  rw [hpm, hpp, hbm, hbp, hnil] at hrel
  simp only [LinearMap.comp_id] at hrel
  exact hrel

/-- `n_⋆` is nilpotent: it is the composite along a loop of length two (moved from v1's engine
`E11`, `spNStar_isNilpotent`).  @census none (helper; core) -/
theorem isNilpotent_nOp_star : IsNilpotent (nOp W 1) := by
  have hnil : W.obj.toRep.pathMap (a := vtxStar L) (b := vtxStar L)
      Quiver.Path.nil = LinearMap.id := RationalQuiver.Rep.pathMap_nil _ _
  have hbm : W.obj.toRep.pathMap (a := vtxStar L) (b := vtxMinus L)
      (Quiver.Path.nil.cons RQuiver.bMinus)
      = W.obj.toRep.arrowMap (a := vtxStar L) (b := vtxMinus L)
          RQuiver.bMinus
        ∘ₗ W.obj.toRep.pathMap (a := vtxStar L) (b := vtxStar L)
          Quiver.Path.nil := RationalQuiver.Rep.pathMap_cons _ _ _
  have hpm : W.obj.toRep.pathMap (a := vtxStar L) (b := vtxStar L)
      RQuiver.pathMinus
      = W.obj.toRep.arrowMap (a := vtxMinus L) (b := vtxStar L)
          RQuiver.aMinus
        ∘ₗ W.obj.toRep.pathMap (a := vtxStar L) (b := vtxMinus L)
          (Quiver.Path.nil.cons RQuiver.bMinus) := RationalQuiver.Rep.pathMap_cons _ _ _
  have hval : W.obj.toRep.pathMap (a := vtxStar L) (b := vtxStar L)
      RQuiver.pathMinus = nOp W 1 := by
    rw [hpm, hbm, hnil]
    simp only [LinearMap.comp_id]
    rfl
  rw [← hval]
  exact isNilpotent_pathMap_loop _ W.property.1 _
    (by simp [RQuiver.pathMinus, Quiver.Path.length])

/-- Each `n_•` is nilpotent.  @census none (helper; core) -/
theorem isNilpotent_nOp : ∀ v : Fin 3, IsNilpotent (nOp W v) := by
  intro v
  fin_cases v
  · exact isNilpotent_comp_swap (f := Vedge W 0) (g := Vedge W 1) (isNilpotent_nOp_star W)
  · exact isNilpotent_nOp_star W
  · have h : IsNilpotent (nStarPlus W) := nOp_star_eq_nStarPlus W ▸ isNilpotent_nOp_star W
    exact isNilpotent_comp_swap (f := Vedge W 2) (g := Vedge W 3) h

/-- `φ_• = ℓ²·𝟏 + nilpotent`.  @census none (helper; core) -/
theorem phi_scalar_add_nilpotent (v : Fin 3) :
    IsNilpotent ((4 : L) • nOp W v) ∧
      phiOp ℓ W v = (((ellUnit L hℓ : Lˣ) : L) ^ 2) • 1 + (4 : L) • nOp W v :=
  ⟨IsNilpotent.smul' (isNilpotent_nOp W v) _, rfl⟩

/-- `(φ_•^{1/2})² = φ_•`.  @census none (helper; core) -/
theorem sqrtPhi_sq (v : Fin 3) : sqrtPhi hℓ W v ^ 2 = phiOp ℓ W v :=
  sqrtOfScalarPlusNilpotent_sq _ _ _ _ (phi_scalar_add_nilpotent hℓ W v).1
    (phi_scalar_add_nilpotent hℓ W v).2

/-- **`C11`**, both orders.  @census none (helper; core) -/
theorem xi_mul_xi (v : Fin 3) (j : ℤ) :
    xiOp hℓ W v 1 j * xiOp hℓ W v (-1) j = phiOp ℓ W v - ((j : L) ^ 2) • 1 ∧
      xiOp hℓ W v (-1) j * xiOp hℓ W v 1 j = phiOp ℓ W v - ((j : L) ^ 2) • 1 := by
  have hsq := sqrtPhi_sq hℓ W v
  have hc1 : (((1 * j : ℤ)) : L) = (j : L) := by push_cast; ring
  have hc2 : (((-1 * j : ℤ)) : L) = -(j : L) := by push_cast; ring
  constructor
  · show (sqrtPhi hℓ W v + (((1 * j : ℤ) : L)) • 1) * (sqrtPhi hℓ W v + (((-1 * j : ℤ) : L)) • 1) = _
    rw [hc1, hc2, end_add_smul_mul, hsq, add_neg_cancel, zero_smul, add_zero,
      show (j : L) * -(j : L) = -((j : L) ^ 2) by ring, neg_smul, ← sub_eq_add_neg]
  · show (sqrtPhi hℓ W v + (((-1 * j : ℤ) : L)) • 1) * (sqrtPhi hℓ W v + (((1 * j : ℤ) : L)) • 1) = _
    rw [hc1, hc2, end_add_smul_mul, hsq, neg_add_cancel, zero_smul, add_zero,
      show -(j : L) * (j : L) = -((j : L) ^ 2) by ring, neg_smul, ← sub_eq_add_neg]

/-- `φ_• − ℓ²·𝟏 = 4n_•`.  @census none (helper; core) -/
theorem phiOp_sub_ell (v : Fin 3) :
    phiOp ℓ W v - ((ℓ : L) ^ 2) • 1 = (4 : L) • nOp W v := by
  show ((ℓ : L) ^ 2) • 1 + (4 : L) • nOp W v - ((ℓ : L) ^ 2) • 1 = _
  abel

omit W in
/-- `4·(½ξ_+ ∘ ½ξ_-) = ξ_+ξ_-`.  @census none (helper; core) -/
theorem four_smul_half_comp {U : Type} [AddCommGroup U] [Module L U] (A B : Module.End L U) :
    (4 : L) • (((2 : L)⁻¹ • A) ∘ₗ ((2 : L)⁻¹ • B)) = A * B := by
  have h2 : (2 : L) ≠ 0 := two_ne_zero
  have hnum : (4 : L) * (2 : L)⁻¹ * (2 : L)⁻¹ = 1 := by
    field_simp
    norm_num
  ext x
  simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, Module.End.mul_apply]
  rw [smul_smul, smul_smul, hnum, one_smul]

end Vertex

section StarChain

variable {W : (RepNilRelSplit L).FullSubcategory}

/-- `∏_{k=1}^{i} ξ^{(-ℓ+2k)}_{v,+}` — the product of `C17`'s display, in the order the chain
produces it.  The factors commute (each is `φ_v^{1/2}` plus a scalar), so the order is immaterial.
@census none (helper) -/
noncomputable def xiProd (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) :
    ℕ → Module.End L (VM W v)
  | 0 => 1
  | (i + 1) => xiOp hℓ W v 1 (-(ℓ : ℤ) + 2 * ((i : ℤ) + 1)) * xiProd W v i

theorem xiProd_zero (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) : xiProd hℓ W v 0 = 1 := rfl

theorem xiProd_succ (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) (i : ℕ) :
    xiProd hℓ W v (i + 1)
      = xiOp hℓ W v 1 (-(ℓ : ℤ) + 2 * ((i : ℤ) + 1)) * xiProd hℓ W v i := rfl

/-- `∏_{k=1}^{i} 2k = 2^i·i!` — the scalar part of `xiProd`, the source's `γ̃`.
@census none (helper) -/
def prodCoeff : ℕ → ℚ
  | 0 => 1
  | (i + 1) => (2 * ((i : ℚ) + 1)) * prodCoeff i

theorem prodCoeff_succ (i : ℕ) : prodCoeff (i + 1) = (2 * ((i : ℚ) + 1)) * prodCoeff i := rfl

theorem prodCoeff_pos (i : ℕ) : 0 < prodCoeff i := by
  induction i with
  | zero => norm_num [prodCoeff]
  | succ i ih => rw [prodCoeff_succ]; exact mul_pos (by positivity) ih

/-- `prodCoeff i = 2^i · i!` (Step O-20): the scalar part of `xiProd`, i.e. the source's
`γ̃ = 2^{ℓ-1}(ℓ-1)!` at `i = ℓ - 1`, computed once and `c`-free.

@census    none (auxiliary; Step O-20)
@clauses   RQ2-5.12-S-O20 -/
theorem prodCoeff_eq (i : ℕ) : prodCoeff i = 2 ^ i * (Nat.factorial i : ℚ) := by
  induction i with
  | zero => norm_num [prodCoeff]
  | succ i ih =>
      rw [prodCoeff_succ, ih, Nat.factorial_succ]
      push_cast
      ring

/-- `φ_v^{1/2} = ℓ·𝟏 + nilpotent`: `def:squareroots`' own shape, read off `sqrt_spec`.
@census none (helper) -/
theorem sqrtPhi_sub_ell_isNilpotent (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) :
    IsNilpotent (sqrtPhi hℓ W v - ((ℓ : L)) • 1) := by
  have h2 : (2 : L) ≠ 0 := two_ne_zero
  obtain ⟨hnil, hφ⟩ := phi_scalar_add_nilpotent hℓ W v
  set γ : Lˣ := ellUnit L hℓ with hγdef
  have hval : ((((γ ^ 2)⁻¹ : Lˣ)) : L) * ((γ : L) ^ 2) = 1 := by
    rw [Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_mul_cancel₀]
    exact Units.ne_zero _
  have hρ : ((((γ ^ 2)⁻¹ : Lˣ)) : L) • phiOp ℓ W v
      = 1 + ((((γ ^ 2)⁻¹ : Lˣ)) : L) • ((4 : L) • nOp W v) := by
    rw [hφ, smul_add, smul_smul, hval, one_smul]
  obtain ⟨-, hn, -⟩ := sqrt_spec h2 _ _ (IsNilpotent.smul' hnil _) hρ
  have hrw : sqrtPhi hℓ W v - ((ℓ : L)) • 1
      = ((ℓ : L)) •
          (sqrt h2 (((((γ ^ 2)⁻¹ : Lˣ)) : L) • phiOp ℓ W v) - 1) := by
    rw [smul_sub]
    rfl
  rw [hrw]
  exact IsNilpotent.smul' hn _

/-- Every `ξ^{(j)}_{v,s}` commutes with `φ_v^{1/2}`.  @census none (helper) -/
theorem commute_xiOp_sqrtPhi (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) (s j : ℤ) :
    Commute (xiOp hℓ W v s j) (sqrtPhi hℓ W v) := by
  show Commute (sqrtPhi hℓ W v + (((s * j : ℤ) : L)) • 1) _
  exact (Commute.refl _).add_left (Commute.smul_left (Commute.one_left _) _)

/-- **`C17`'s scalar/nilpotent split**: `∏_{k=1}^{i} ξ^{(-ℓ+2k)}_{v,+} = (∏_{k=1}^{i}2k)·𝟏 + ñ`
with `ñ` nilpotent and commuting with `φ_v^{1/2}` — hence with `φ_v`.  @census none (helper) -/
theorem xiProd_split (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) (i : ℕ) :
    ∃ n : Module.End L (VM W v), IsNilpotent n ∧
      Commute n (sqrtPhi hℓ W v) ∧
      xiProd hℓ W v i = (algebraMap ℚ L (prodCoeff i)) • 1 + n := by
  set m : Module.End L (VM W v) :=
    sqrtPhi hℓ W v - ((ℓ : L)) • 1 with hm
  have hmnil : IsNilpotent m := sqrtPhi_sub_ell_isNilpotent hℓ W v
  have hmc : Commute m (sqrtPhi hℓ W v) :=
    (Commute.refl _).sub_left (Commute.smul_left (Commute.one_left _) _)
  have key : ∀ (A C : L) (rr : Module.End L (VM W v)),
      ((A • 1 + m) * (C • 1 + m * rr) : Module.End L (VM W v))
        = (A * C) • 1 + m * (A • rr + C • 1 + m * rr) := by
    intro A C rr
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add,
      smul_smul, mul_comm A C]
    abel
  suffices h : ∃ r : Module.End L (VM W v), Commute r (sqrtPhi hℓ W v) ∧
      xiProd hℓ W v i = (algebraMap ℚ L (prodCoeff i)) • 1 + m * r by
    obtain ⟨r, hr, hrw⟩ := h
    have hmr : Commute m r := by
      rw [hm]
      exact (hr.symm).sub_left (Commute.smul_left (Commute.one_left _) _)
    have hnil : IsNilpotent (m * r) := by
      obtain ⟨k, hk⟩ := hmnil
      exact ⟨k, by rw [hmr.mul_pow, hk, zero_mul]⟩
    exact ⟨m * r, hnil, hmc.mul_left hr, hrw⟩
  induction i with
  | zero =>
      refine ⟨0, Commute.zero_left _, ?_⟩
      rw [xiProd_zero]
      norm_num [prodCoeff]
  | succ i ih =>
      obtain ⟨r, hr, hrw⟩ := ih
      have hs : ((1 * (-(ℓ : ℤ) + 2 * ((i : ℤ) + 1)) : ℤ) : L)
          = (algebraMap ℚ L) (2 * ((i : ℚ) + 1)) - ((ℓ : L)) := by
        rw [← map_intCast (algebraMap ℚ L)
              (1 * (-(ℓ : ℤ) + 2 * ((i : ℤ) + 1))),
          ← map_natCast (algebraMap ℚ L) ℓ, ← map_sub]
        congr 1
        push_cast
        ring
      have hxi : xiOp hℓ W v 1 (-(ℓ : ℤ) + 2 * ((i : ℤ) + 1))
          = (algebraMap ℚ L (2 * ((i : ℚ) + 1))) • 1 + m := by
        show sqrtPhi hℓ W v
            + (((1 * (-(ℓ : ℤ) + 2 * ((i : ℤ) + 1)) : ℤ) : L)) • 1 = _
        rw [hs, hm, sub_smul]
        abel
      refine ⟨(algebraMap ℚ L (2 * ((i : ℚ) + 1))) • r
        + (algebraMap ℚ L (prodCoeff i)) • 1 + m * r, ?_, ?_⟩
      · exact ((Commute.smul_left hr _).add_left
          (Commute.smul_left (Commute.one_left _) _)).add_left (hmc.mul_left hr)
      · rw [xiProd_succ, hxi, hrw, key, prodCoeff_succ]
        simp only [map_mul]

end StarChain

section StarChain2

variable {W : (RepNilRelSplit L).FullSubcategory}

/-- `ξ^{(j)}_{v,-} = ξ^{(-j)}_{v,+}`: the two families differ by the sign of `j` only.
@census none (helper) -/
theorem xiOp_neg_one (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) (j : ℤ) :
    xiOp hℓ W v (-1) j = xiOp hℓ W v 1 (-j) := by
  show sqrtPhi hℓ W v + (((-1 * j : ℤ) : L)) • 1
      = sqrtPhi hℓ W v + (((1 * -j : ℤ) : L)) • 1
  norm_num

/-- `X⋆` at a vertex, as the normalized product of `C17`: `(γ⋆·2^{ℓ-1})^{-1}·∏ξ`.  At `⋆` this
**is** `D.xStarV` (`xStarV_eq`) and also `D.yStarV` (`yStarV_eq`).  At `−` it was, until the
author's ruling of 2026-09-11, the correction term the source's then-`C25` omitted (`AN-41`,
ruling `R-S8-17`); that sentence is deleted in the amended source, and `xStarAt … 0` survives as
the `−`-vertex operator whose naturality `edgeAm_xStarAt`/`edgeBm_xStarAt` record.
@census none (helper) -/
noncomputable def xStarAt (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) :
    Module.End L (VM W v) :=
  ((gammaStarF L ℓ) * (2 : L) ^ (ℓ - 1))⁻¹ • xiProd hℓ W v (ℓ - 1)

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

/-- `φ_{a₋} : V(−) → V(⋆)`, endpoints normalised.  @census none (helper) -/
noncomputable def edgeAm (W : (RepNilRelSplit L).FullSubcategory) : VM W 0 →ₗ[L] VM W 1 :=
  Vedge W 0

/-- `φ_{b₋} : V(⋆) → V(−)`, endpoints normalised.  @census none (helper) -/
noncomputable def edgeBm (W : (RepNilRelSplit L).FullSubcategory) : VM W 1 →ₗ[L] VM W 0 :=
  Vedge W 1

theorem edgeAm_nOp (W : (RepNilRelSplit L).FullSubcategory) (x : VM W 0) :
    edgeAm W (nOp W 0 x) = nOp W 1 (edgeAm W x) := rfl

theorem edgeBm_nOp (W : (RepNilRelSplit L).FullSubcategory) (x : VM W 1) :
    edgeBm W (nOp W 1 x) = nOp W 0 (edgeBm W x) := rfl

theorem edgeAm_phiOp (W : (RepNilRelSplit L).FullSubcategory) (x : VM W 0) :
    edgeAm W (phiOp ℓ W 0 x) = phiOp ℓ W 1 (edgeAm W x) := by
  show edgeAm W (((ℓ : L) ^ 2) • x + (4 : L) • nOp W 0 x)
      = ((ℓ : L) ^ 2) • edgeAm W x
        + (4 : L) • nOp W 1 (edgeAm W x)
  rw [map_add, map_smul, map_smul, edgeAm_nOp]

theorem edgeBm_phiOp (W : (RepNilRelSplit L).FullSubcategory) (x : VM W 1) :
    edgeBm W (phiOp ℓ W 1 x) = phiOp ℓ W 0 (edgeBm W x) := by
  show edgeBm W (((ℓ : L) ^ 2) • x + (4 : L) • nOp W 1 x)
      = ((ℓ : L) ^ 2) • edgeBm W x
        + (4 : L) • nOp W 0 (edgeBm W x)
  rw [map_add, map_smul, map_smul, edgeBm_nOp]

theorem edgeAm_sqrtPhi (W : (RepNilRelSplit L).FullSubcategory) (x : VM W 0) :
    edgeAm W (sqrtPhi hℓ W 0 x) = sqrtPhi hℓ W 1 (edgeAm W x) :=
  sqrtOfScalarPlusNilpotent_natural _ _ (phi_scalar_add_nilpotent hℓ W 0).1
    (phi_scalar_add_nilpotent hℓ W 0).2 (phi_scalar_add_nilpotent hℓ W 1).1
    (phi_scalar_add_nilpotent hℓ W 1).2 (edgeAm W) (edgeAm_phiOp W) x

theorem edgeBm_sqrtPhi (W : (RepNilRelSplit L).FullSubcategory) (x : VM W 1) :
    edgeBm W (sqrtPhi hℓ W 1 x) = sqrtPhi hℓ W 0 (edgeBm W x) :=
  sqrtOfScalarPlusNilpotent_natural _ _ (phi_scalar_add_nilpotent hℓ W 1).1
    (phi_scalar_add_nilpotent hℓ W 1).2 (phi_scalar_add_nilpotent hℓ W 0).1
    (phi_scalar_add_nilpotent hℓ W 0).2 (edgeBm W) (edgeBm_phiOp W) x

theorem edgeAm_xiOp (W : (RepNilRelSplit L).FullSubcategory) (s j : ℤ) (x : VM W 0) :
    edgeAm W (xiOp hℓ W 0 s j x) = xiOp hℓ W 1 s j (edgeAm W x) := by
  show edgeAm W (sqrtPhi hℓ W 0 x + (((s * j : ℤ) : L)) • x)
      = sqrtPhi hℓ W 1 (edgeAm W x)
        + (((s * j : ℤ) : L)) • edgeAm W x
  rw [map_add, map_smul, edgeAm_sqrtPhi]

theorem edgeBm_xiOp (W : (RepNilRelSplit L).FullSubcategory) (s j : ℤ) (x : VM W 1) :
    edgeBm W (xiOp hℓ W 1 s j x) = xiOp hℓ W 0 s j (edgeBm W x) := by
  show edgeBm W (sqrtPhi hℓ W 1 x + (((s * j : ℤ) : L)) • x)
      = sqrtPhi hℓ W 0 (edgeBm W x)
        + (((s * j : ℤ) : L)) • edgeBm W x
  rw [map_add, map_smul, edgeBm_sqrtPhi]

theorem edgeAm_xiProd (W : (RepNilRelSplit L).FullSubcategory) (i : ℕ) (x : VM W 0) :
    edgeAm W (xiProd hℓ W 0 i x) = xiProd hℓ W 1 i (edgeAm W x) := by
  induction i generalizing x with
  | zero => rw [xiProd_zero, xiProd_zero]; rfl
  | succ i ih =>
      rw [xiProd_succ, xiProd_succ, Module.End.mul_apply, Module.End.mul_apply, edgeAm_xiOp, ih]

theorem edgeBm_xiProd (W : (RepNilRelSplit L).FullSubcategory) (i : ℕ) (x : VM W 1) :
    edgeBm W (xiProd hℓ W 1 i x) = xiProd hℓ W 0 i (edgeBm W x) := by
  induction i generalizing x with
  | zero => rw [xiProd_zero, xiProd_zero]; rfl
  | succ i ih =>
      rw [xiProd_succ, xiProd_succ, Module.End.mul_apply, Module.End.mul_apply, edgeBm_xiOp, ih]

/-- `X⋆ φ_{a₋} = φ_{a₋} X⋆^{(−)}` — until 2026-09-11 the corrected left-hand `a₋` square of
`RQ-5.05-C25` (`AN-41`, ruling `R-S8-17`), and since that ruling retired `C25` simply the
`xStarAt` instance of clause (e)'s naturality (`RQ-4.05-C7`).  @census none (helper) -/
theorem edgeAm_xStarAt (W : (RepNilRelSplit L).FullSubcategory) (x : VM W 0) :
    edgeAm W (xStarAt hℓ W 0 x) = xStarAt hℓ W 1 (edgeAm W x) := by
  show edgeAm W (((gammaStarF L ℓ) * (2 : L) ^ (ℓ - 1))⁻¹
      • xiProd hℓ W 0 (ℓ - 1) x)
      = ((gammaStarF L ℓ) * (2 : L) ^ (ℓ - 1))⁻¹
      • xiProd hℓ W 1 (ℓ - 1) (edgeAm W x)
  rw [map_smul, edgeAm_xiProd]

/-- `X⋆^{(−)} φ_{b₋} = φ_{b₋} X⋆` — the `b₋` companion of `edgeAm_xStarAt`; see its docstring
for the 2026-09-11 retirement of `RQ-5.05-C25`.  @census none (helper) -/
theorem edgeBm_xStarAt (W : (RepNilRelSplit L).FullSubcategory) (x : VM W 1) :
    edgeBm W (xStarAt hℓ W 1 x) = xStarAt hℓ W 0 (edgeBm W x) := by
  show edgeBm W (((gammaStarF L ℓ) * (2 : L) ^ (ℓ - 1))⁻¹
      • xiProd hℓ W 1 (ℓ - 1) x)
      = ((gammaStarF L ℓ) * (2 : L) ^ (ℓ - 1))⁻¹
      • xiProd hℓ W 0 (ℓ - 1) (edgeBm W x)
  rw [map_smul, edgeBm_xiProd]

/-- **`C17`'s `X⋆ = γ̃'(𝟏 + ñ_⋆)` with `γ̃' = 1`**: after the `γ⋆·2^{ℓ-1}` normalization the scalar
part of the product is exactly `1`, so `X⋆` is unipotent — in particular invertible.
@census none (helper) -/
theorem xStarAt_eq_one_add (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) :
    ∃ n : Module.End L (VM W v), IsNilpotent n ∧
      Commute n (sqrtPhi hℓ W v) ∧ xStarAt hℓ W v = 1 + n := by
  have h2ne : (2 : L) ≠ 0 := two_ne_zero
  have hγ : gammaStarF L ℓ ≠ 0 := gammaStarF_ne_zero ℓ
  obtain ⟨n, hn, hc, hsplit⟩ := xiProd_split hℓ W v (ℓ - 1)
  have hcoeff : (algebraMap ℚ L) (prodCoeff (ℓ - 1))
      = (2 : L) ^ (ℓ - 1) * gammaStarF L ℓ := by
    rw [prodCoeff_eq, map_mul, map_pow, map_ofNat, gammaStarF, map_natCast]
  have hinv : (((gammaStarF L ℓ) * (2 : L) ^ (ℓ - 1))⁻¹)
      * ((algebraMap ℚ L) (prodCoeff (ℓ - 1))) = 1 := by
    rw [hcoeff, mul_comm ((2 : L) ^ (ℓ - 1)) (gammaStarF L ℓ),
      inv_mul_cancel₀ (mul_ne_zero hγ (pow_ne_zero _ h2ne))]
  refine ⟨(((gammaStarF L ℓ) * (2 : L) ^ (ℓ - 1))⁻¹) • n, IsNilpotent.smul' hn _,
    Commute.smul_left hc _, ?_⟩
  show (((gammaStarF L ℓ) * (2 : L) ^ (ℓ - 1))⁻¹) • xiProd hℓ W v (ℓ - 1) = _
  rw [hsplit, smul_add, smul_smul, hinv, one_smul]

/-- `X⋆` is a unit of `End(V(v))`.  @census none (helper) -/
theorem isUnit_xStarAt (W : (RepNilRelSplit L).FullSubcategory) (v : Fin 3) : IsUnit (xStarAt hℓ W v) := by
  obtain ⟨n, hn, -, heq⟩ := xStarAt_eq_one_add hℓ W v
  rw [heq]
  exact isUnit_one_add_of_isNilpotent hn


end StarChain2


section E2Carrier

variable (W : (RepNilRelSplit L).FullSubcategory)

/-- `T := V(+) × V(⋆) × V(−)`, the **ambient** space every component of the constructed module
sits in.  Making the three vertex spaces summands of one fixed type is what keeps the graded
carrier free of type transports: `M_n` is a *submodule of `T`* that depends on `n` only through a
`Prop`-valued case split, never a type that depends on `n`.  @census none (helper; engine `E2`) -/
abbrev EssTriple : Type := VM W 2 × VM W 1 × VM W 0

/-- `V(+) ↪ T`.  @census none (helper; engine `E2`) -/
noncomputable def essIotaPlus : VM W 2 →ₗ[L] EssTriple W :=
  LinearMap.inl _ _ _

/-- `V(⋆) ↪ T`.  @census none (helper; engine `E2`) -/
noncomputable def essIotaStar : VM W 1 →ₗ[L] EssTriple W :=
  (LinearMap.inr _ _ _).comp (LinearMap.inl _ _ _)

/-- `V(−) ↪ T`.  @census none (helper; engine `E2`) -/
noncomputable def essIotaMinus : VM W 0 →ₗ[L] EssTriple W :=
  (LinearMap.inr _ _ _).comp (LinearMap.inr _ _ _)

/-- @census none (helper; engine `E2`) -/
theorem essIotaPlus_inj : Function.Injective (essIotaPlus W) := by
  intro a b h; exact congrArg Prod.fst h

/-- @census none (helper; engine `E2`) -/
theorem essIotaStar_inj : Function.Injective (essIotaStar W) := by
  intro a b h; exact congrArg (fun z => (z.2).1) h

/-- @census none (helper; engine `E2`) -/
theorem essIotaMinus_inj : Function.Injective (essIotaMinus W) := by
  intro a b h; exact congrArg (fun z => (z.2).2) h

/-- **`C9`'s component, as a subspace of `T`**: `V(+)` for `n ≥ ℓ+1`, `V(−)` for `n ≤ -(ℓ+1)`,
`V(⋆)` in between, and `0` off the parity class `n ≡ ℓ-1 (mod 2)` — so the central character
(`EssSurjData.centralCharacter`) holds by construction rather than by a separate argument.
@census none (helper; engine `E2`) -/
noncomputable def essRegion (ℓ : ℕ) (n : ℤ) : Submodule L (EssTriple W) :=
  if (n - ((ℓ : ℤ) - 1)) % 2 ≠ 0 then ⊥
  else if (ℓ : ℤ) + 1 ≤ n then LinearMap.range (essIotaPlus W)
  else if n ≤ -((ℓ : ℤ) + 1) then LinearMap.range (essIotaMinus W)
  else LinearMap.range (essIotaStar W)

/-- The fibre of the graded carrier at `n`.  An `abbrev`, so that the `AddCommGroup`/`Module`
instances of a `Submodule` coercion are found through it.  @census none (helper; engine `E2`) -/
abbrev EssFib (ℓ : ℕ) (n : ℤ) : Type := ↥(essRegion W ℓ n)

/-- **The carrier of the constructed module**, `M = ⨁_{n ∈ ℤ} M_n`.
@census none (helper; engine `E2`) -/
abbrev EssCarrier (ℓ : ℕ) : Type := DirectSum ℤ (EssFib W ℓ)

/-- `M_n`, as a subspace of `M`: the range of the canonical injection of the `n`-th summand.
@census none (helper; engine `E2`) -/
noncomputable def essComp (ℓ : ℕ) (n : ℤ) : Submodule L (EssCarrier W ℓ) :=
  LinearMap.range (DirectSum.lof L ℤ (EssFib W ℓ) n)



end E2Carrier




section E2Carrier2

variable (W : (RepNilRelSplit L).FullSubcategory)



-- The instance `AddCommGroup ↥(essComp …)` sits four `Submodule`/`DirectSum` layers deep and is
-- not found at the default pending-synthesis depth (measured); `Module` at the same type is.
set_option maxSynthPendingDepth 4

/-- **`M = ⨁_n M_n`** for the constructed module.  @census none (helper; engine `E2`) -/
theorem essComp_isInternal : DirectSum.IsInternal (essComp W ℓ) :=
  isInternal_range_lof L ℤ (EssFib W ℓ)

/-- @census none (helper; engine `E2`) -/
theorem essRegion_eq_bot {n : ℤ} (hn : (n - ((ℓ : ℤ) - 1)) % 2 ≠ 0) :
    essRegion W ℓ n = ⊥ := by
  rw [essRegion, if_pos hn]

/-- **The central character, by construction**: `M_n = 0` off the parity class.
@census none (helper; engine `E2`) -/
theorem essComp_eq_bot {n : ℤ} (hn : (n - ((ℓ : ℤ) - 1)) % 2 ≠ 0) :
    essComp W ℓ n = ⊥ := by
  have hs : Subsingleton (EssFib W ℓ n) := by
    show Subsingleton ↥(essRegion W ℓ n)
    rw [essRegion_eq_bot W hn]
    infer_instance
  rw [essComp, LinearMap.range_eq_bot]
  refine LinearMap.ext fun x => ?_
  rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]

/-- @census none (helper; engine `E2`) -/
theorem essRegion_plus {n : ℤ} (hn : (n - ((ℓ : ℤ) - 1)) % 2 = 0) (h1 : (ℓ : ℤ) + 1 ≤ n) :
    essRegion W ℓ n = LinearMap.range (essIotaPlus W) := by
  rw [essRegion, if_neg (by simpa using hn), if_pos h1]

/-- @census none (helper; engine `E2`) -/
theorem essRegion_minus {n : ℤ} (hn : (n - ((ℓ : ℤ) - 1)) % 2 = 0) (h1 : n ≤ -((ℓ : ℤ) + 1)) :
    essRegion W ℓ n = LinearMap.range (essIotaMinus W) := by
  have h2 : ¬ ((ℓ : ℤ) + 1 ≤ n) := by omega
  rw [essRegion, if_neg (by simpa using hn), if_neg h2, if_pos h1]

/-- @census none (helper; engine `E2`) -/
theorem essRegion_star {n : ℤ} (hn : (n - ((ℓ : ℤ) - 1)) % 2 = 0)
    (h1 : -((ℓ : ℤ) - 1) ≤ n) (h2 : n ≤ (ℓ : ℤ) - 1) :
    essRegion W ℓ n = LinearMap.range (essIotaStar W) := by
  rw [essRegion, if_neg (by simpa using hn), if_neg (by omega : ¬ ((ℓ : ℤ) + 1 ≤ n)),
    if_neg (by omega : ¬ (n ≤ -((ℓ : ℤ) + 1)))]

/-- `M_n ≃` its fibre.  @census none (helper; engine `E2`) -/
noncomputable def essCompEquiv (n : ℤ) : essComp W ℓ n ≃ₗ[L] EssFib W ℓ n :=
  (LinearEquiv.ofInjective (DirectSum.lof L ℤ (EssFib W ℓ) n)
    (lof_injective L ℤ (EssFib W ℓ) n)).symm

/-- **`C9`, `+`**: `M_n ≃ V(+)` for `n ≥ ℓ+1`.  @census none (helper; engine `E2`) -/
noncomputable def essIsoPlus {n : ℤ} (hn : (n - ((ℓ : ℤ) - 1)) % 2 = 0) (h1 : (ℓ : ℤ) + 1 ≤ n) :
    essComp W ℓ n ≃ₗ[L] VM W 2 :=
  (essCompEquiv W n).trans
    ((LinearEquiv.ofEq _ _ (essRegion_plus W hn h1)).trans
      (LinearEquiv.ofInjective (essIotaPlus W) (essIotaPlus_inj W)).symm)

/-- **`C9`, `−`**: `M_n ≃ V(−)` for `n ≤ -(ℓ+1)`.  @census none (helper; engine `E2`) -/
noncomputable def essIsoMinus {n : ℤ} (hn : (n - ((ℓ : ℤ) - 1)) % 2 = 0) (h1 : n ≤ -((ℓ : ℤ) + 1)) :
    essComp W ℓ n ≃ₗ[L] VM W 0 :=
  (essCompEquiv W n).trans
    ((LinearEquiv.ofEq _ _ (essRegion_minus W hn h1)).trans
      (LinearEquiv.ofInjective (essIotaMinus W) (essIotaMinus_inj W)).symm)

/-- **`C9`, `⋆`**: `M_n ≃ V(⋆)` for `-(ℓ-1) ≤ n ≤ ℓ-1`.  @census none (helper; engine `E2`) -/
noncomputable def essIsoStar {n : ℤ} (hn : (n - ((ℓ : ℤ) - 1)) % 2 = 0)
    (h1 : -((ℓ : ℤ) - 1) ≤ n) (h2 : n ≤ (ℓ : ℤ) - 1) :
    essComp W ℓ n ≃ₗ[L] VM W 1 :=
  (essCompEquiv W n).trans
    ((LinearEquiv.ofEq _ _ (essRegion_star W hn h1 h2)).trans
      (LinearEquiv.ofInjective (essIotaStar W) (essIotaStar_inj W)).symm)

/-- **Admissibility of the constructed module** (`EssSurjData.admissible`): every component is
finite-dimensional, because `V` is.  @census none (helper; engine `E2`) -/
theorem essComp_finiteDimensional (n : ℤ) :
    FiniteDimensional L ↥(essComp W ℓ n) := by
  by_cases hn : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · by_cases h1 : (ℓ : ℤ) + 1 ≤ n
    · exact LinearEquiv.finiteDimensional (essIsoPlus W hn h1).symm
    · by_cases h2 : n ≤ -((ℓ : ℤ) + 1)
      · exact LinearEquiv.finiteDimensional (essIsoMinus W hn h2).symm
      · exact LinearEquiv.finiteDimensional
          (essIsoStar W hn (by omega) (by omega)).symm
  · rw [essComp_eq_bot W hn]; infer_instance


end E2Carrier2

/-! ### Engine `E2`, step 2 — the operators, and the graded `𝔰𝔩₂`-module

Step 1 built the carrier `M = ⨁_n M_n`.  This section puts `H`, `X`, `Y` on it, in the source's
own formulas, and proves the three `𝔰𝔩₂` relations — i.e. it produces the `HC.WeightData` that
`EssSurjData.setup.weight` will be.  What remains for `essSurj_exists` is listed in
`stages/S8/DESIGN-NOTES.md` §16.4 (residue items 4-7): the generalized infinitesimal character,
finite generation, the conjugation, the `ℚ`-form, and the fifteen pins.

**How the operators are written.**  Each of `X` and `Y` is defined *in the ambient* `T` first
(`xAmb`, `yAmb`), by a `Prop`-valued case split on the degree, and only then restricted to the
components (`xComp`, `yComp`, via `LinearMap.restrict` and `xAmb_mem`/`yAmb_mem`).  Writing the
case split in `T` rather than in the fibres is what keeps it free of type transports: `T` does not
depend on `n`, so a five-way `if` on `n` is an ordinary definition and the membership statement is
an ordinary `Prop`.  `X`, `Y` and `H` on `M` are then `DirectSum.toModule` of those.

**The case split, and its fall-through.**  `xAmb n` has five branches — the `+` interior
(`n ≥ ℓ+1`), the `−` interior (`n ≤ -(ℓ+3)`), the `a₋` wall (`n = -(ℓ+1)`), the `b₊` wall
(`n = ℓ-1`), the `⋆` interior (`-(ℓ-1) ≤ n ≤ ℓ-3`) — and a fall-through `0`.  The fall-through is
reached exactly at `n ∈ {ℓ, ℓ-2, -ℓ, -(ℓ+2)}`, each of which differs from `ℓ-1` by an odd number,
so the source component there is `⊥` and `0` is the only possible map; that is the one step of the
case analysis which has to be *argued* rather than read off, and it is `xAmb_mem`'s parity branch.

**`[X,Y] = H`.**  `essLie_ambient` is the computation, in eight cases.  The three interiors are
`C11` (`xi_mul_xi`, in both orders): `4XY = φ_• − (n−1)²` and `4YX = φ_• − (n+1)²` on `M_n`, whose
difference is `4n`.  At each of the four walls one of the two composites is a pair of edge maps —
`φ_{b₊}φ_{a₊} = n_+`, `φ_{b₋}φ_{a₋} = n_-`, `φ_{a₋}φ_{b₋} = n_⋆`, `φ_{a₊}φ_{b₊}` — and the loop
cancels against the `4n_•` inside `φ_• = ℓ²·𝟏 + 4n_•`, leaving `¼(j² − ℓ²)`.  **The eighth case is
`ℓ = 1`**, where the `⋆` block is the single component `M_0`, both walls meet it, and the identity
reduces to `n_⋆ = φ_{a₊}φ_{b₊}` — that is `C10`, i.e. **`ex:gelfand`'s relation**.  The relation is
therefore not decoration in this construction: it is the `𝔰𝔩₂` identity at the `⋆` vertex.
-/

section E2Ops

variable (W : (RepNilRelSplit L).FullSubcategory)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

/-- `φ_{a₋} : V(−) → V(⋆)`, at the reduced vertex indices.  @census none (helper; engine `E2`) -/
noncomputable def essEdgeAm : VM W 0 →ₗ[L] VM W 1 := Vedge W 0
/-- `φ_{b₋} : V(⋆) → V(−)`.  @census none (helper; engine `E2`) -/
noncomputable def essEdgeBm : VM W 1 →ₗ[L] VM W 0 := Vedge W 1
/-- `φ_{a₊} : V(+) → V(⋆)`.  @census none (helper; engine `E2`) -/
noncomputable def essEdgeAp : VM W 2 →ₗ[L] VM W 1 := Vedge W 2
/-- `φ_{b₊} : V(⋆) → V(+)`.  @census none (helper; engine `E2`) -/
noncomputable def essEdgeBp : VM W 1 →ₗ[L] VM W 2 := Vedge W 3

/-- `T → V(+)`.  @census none (helper; engine `E2`) -/
noncomputable def essPiPlus : EssTriple W →ₗ[L] VM W 2 := LinearMap.fst _ _ _
/-- `T → V(⋆)`.  @census none (helper; engine `E2`) -/
noncomputable def essPiStar : EssTriple W →ₗ[L] VM W 1 :=
  (LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)
/-- `T → V(−)`.  @census none (helper; engine `E2`) -/
noncomputable def essPiMinus : EssTriple W →ₗ[L] VM W 0 :=
  (LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _)

@[simp] theorem essPiPlus_iotaPlus (x : VM W 2) :
    essPiPlus W (essIotaPlus W x) = x := rfl
@[simp] theorem essPiStar_iotaStar (x : VM W 1) :
    essPiStar W (essIotaStar W x) = x := rfl
@[simp] theorem essPiMinus_iotaMinus (x : VM W 0) :
    essPiMinus W (essIotaMinus W x) = x := rfl


/-- **`C13` for `X`, in the ambient `T`**: `2X|_{M_{j-1}} = ξ^{(j)}_{•,+}` in the three interiors
and the two `X`-walls `φ_{a₋}` (at `n = -(ℓ+1)`) and `φ_{b₊}` (at `n = ℓ-1`), as an endomorphism of
`T` attached to the *source* degree `n`, so `j = n+1`.  The fall-through `0` is reached only for
`n` off the parity class, where the source component is `⊥` (`xAmb_mem`).
@census none (helper; engine `E2`) -/
noncomputable def xAmb (n : ℤ) : EssTriple W →ₗ[L] EssTriple W :=
  if (ℓ : ℤ) + 1 ≤ n then
    (essIotaPlus W).comp
      ((((2 : L)⁻¹) • xiOp hℓ W 2 1 (n + 1)).comp (essPiPlus W))
  else if n ≤ -((ℓ : ℤ) + 3) then
    (essIotaMinus W).comp
      ((((2 : L)⁻¹) • xiOp hℓ W 0 1 (n + 1)).comp (essPiMinus W))
  else if n = -((ℓ : ℤ) + 1) then
    (essIotaStar W).comp ((essEdgeAm W).comp (essPiMinus W))
  else if n = (ℓ : ℤ) - 1 then
    (essIotaPlus W).comp ((essEdgeBp W).comp (essPiStar W))
  else if -((ℓ : ℤ) - 1) ≤ n ∧ n ≤ (ℓ : ℤ) - 3 then
    (essIotaStar W).comp
      ((((2 : L)⁻¹) • xiOp hℓ W 1 1 (n + 1)).comp (essPiStar W))
  else 0

/-- **`C13` for `Y`, in the ambient `T`**: `2Y|_{M_{j+1}} = ξ^{(j)}_{•,-}` and the two `Y`-walls
`φ_{a₊}` (at `n = ℓ+1`) and `φ_{b₋}` (at `n = -(ℓ-1)`), attached to the source degree `n`, so
`j = n-1`.  @census none (helper; engine `E2`) -/
noncomputable def yAmb (n : ℤ) : EssTriple W →ₗ[L] EssTriple W :=
  if (ℓ : ℤ) + 3 ≤ n then
    (essIotaPlus W).comp
      ((((2 : L)⁻¹) • xiOp hℓ W 2 (-1) (n - 1)).comp (essPiPlus W))
  else if n ≤ -((ℓ : ℤ) + 1) then
    (essIotaMinus W).comp
      ((((2 : L)⁻¹) • xiOp hℓ W 0 (-1) (n - 1)).comp (essPiMinus W))
  else if n = (ℓ : ℤ) + 1 then
    (essIotaStar W).comp ((essEdgeAp W).comp (essPiPlus W))
  else if n = -((ℓ : ℤ) - 1) then
    (essIotaMinus W).comp ((essEdgeBm W).comp (essPiStar W))
  else if -((ℓ : ℤ) - 1) + 2 ≤ n ∧ n ≤ (ℓ : ℤ) - 1 then
    (essIotaStar W).comp
      ((((2 : L)⁻¹) • xiOp hℓ W 1 (-1) (n - 1)).comp (essPiStar W))
  else 0

/-- Off the parity class the component is `⊥`, so its only element is `0`.
@census none (helper; engine `E2`) -/
theorem essRegion_bot_apply {n : ℤ} (hn : (n - ((ℓ : ℤ) - 1)) % 2 ≠ 0)
    {x : EssTriple W} (hx : x ∈ essRegion W ℓ n) : x = 0 := by
  rw [essRegion_eq_bot W hn, Submodule.mem_bot] at hx
  exact hx

/-- `xAmb n` carries `M_n` into `M_{n+2}`.  @census none (helper; engine `E2`) -/
theorem xAmb_mem (n : ℤ) (x : EssTriple W) (hx : x ∈ essRegion W ℓ n) :
    xAmb hℓ W n x ∈ essRegion W ℓ (n + 2) := by
  by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · have hpar2 : (n + 2 - ((ℓ : ℤ) - 1)) % 2 = 0 := by omega
    by_cases h1 : (ℓ : ℤ) + 1 ≤ n
    · rw [xAmb, if_pos h1, essRegion_plus W hpar2 (by omega)]
      exact ⟨_, rfl⟩
    · by_cases h2 : n ≤ -((ℓ : ℤ) + 3)
      · rw [xAmb, if_neg h1, if_pos h2, essRegion_minus W hpar2 (by omega)]
        exact ⟨_, rfl⟩
      · by_cases h3 : n = -((ℓ : ℤ) + 1)
        · rw [xAmb, if_neg h1, if_neg h2, if_pos h3,
            essRegion_star W hpar2 (by omega) (by omega)]
          exact ⟨_, rfl⟩
        · by_cases h4 : n = (ℓ : ℤ) - 1
          · rw [xAmb, if_neg h1, if_neg h2, if_neg h3, if_pos h4,
              essRegion_plus W hpar2 (by omega)]
            exact ⟨_, rfl⟩
          · by_cases h5 : -((ℓ : ℤ) - 1) ≤ n ∧ n ≤ (ℓ : ℤ) - 3
            · rw [xAmb, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5,
                essRegion_star W hpar2 (by omega) (by omega)]
              exact ⟨_, rfl⟩
            · exact absurd hpar (by omega)
  · rw [essRegion_bot_apply W hpar hx, map_zero]
    exact Submodule.zero_mem _

/-- `yAmb n` carries `M_n` into `M_{n-2}`.  @census none (helper; engine `E2`) -/
theorem yAmb_mem (n : ℤ) (x : EssTriple W) (hx : x ∈ essRegion W ℓ n) :
    yAmb hℓ W n x ∈ essRegion W ℓ (n - 2) := by
  by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · have hpar2 : (n - 2 - ((ℓ : ℤ) - 1)) % 2 = 0 := by omega
    by_cases h1 : (ℓ : ℤ) + 3 ≤ n
    · rw [yAmb, if_pos h1, essRegion_plus W hpar2 (by omega)]
      exact ⟨_, rfl⟩
    · by_cases h2 : n ≤ -((ℓ : ℤ) + 1)
      · rw [yAmb, if_neg h1, if_pos h2, essRegion_minus W hpar2 (by omega)]
        exact ⟨_, rfl⟩
      · by_cases h3 : n = (ℓ : ℤ) + 1
        · rw [yAmb, if_neg h1, if_neg h2, if_pos h3,
            essRegion_star W hpar2 (by omega) (by omega)]
          exact ⟨_, rfl⟩
        · by_cases h4 : n = -((ℓ : ℤ) - 1)
          · rw [yAmb, if_neg h1, if_neg h2, if_neg h3, if_pos h4,
              essRegion_minus W hpar2 (by omega)]
            exact ⟨_, rfl⟩
          · by_cases h5 : -((ℓ : ℤ) - 1) + 2 ≤ n ∧ n ≤ (ℓ : ℤ) - 1
            · rw [yAmb, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h5,
                essRegion_star W hpar2 (by omega) (by omega)]
              exact ⟨_, rfl⟩
            · exact absurd hpar (by omega)
  · rw [essRegion_bot_apply W hpar hx, map_zero]
    exact Submodule.zero_mem _


/-- `X : M_n → M_{n+2}`, as a map of fibres.  @census none (helper; engine `E2`) -/
noncomputable def xComp (n : ℤ) : EssFib W ℓ n →ₗ[L] EssFib W ℓ (n + 2) :=
  (xAmb hℓ W n).restrict (xAmb_mem hℓ W n)

/-- `Y : M_n → M_{n-2}`, as a map of fibres.  @census none (helper; engine `E2`) -/
noncomputable def yComp (n : ℤ) : EssFib W ℓ n →ₗ[L] EssFib W ℓ (n - 2) :=
  (yAmb hℓ W n).restrict (yAmb_mem hℓ W n)

@[simp] theorem xComp_val (n : ℤ) (a : EssFib W ℓ n) :
    ((xComp hℓ W n a : EssTriple W)) = xAmb hℓ W n (a : EssTriple W) := rfl
@[simp] theorem yComp_val (n : ℤ) (a : EssFib W ℓ n) :
    ((yComp hℓ W n a : EssTriple W)) = yAmb hℓ W n (a : EssTriple W) := rfl

/-- `X` on `M = ⨁_n M_n`.  @census none (helper; engine `E2`) -/
noncomputable def essX : EssCarrier W ℓ →ₗ[L] EssCarrier W ℓ :=
  DirectSum.toModule L ℤ _ (fun n =>
    (DirectSum.lof L ℤ (EssFib W ℓ) (n + 2)).comp (xComp hℓ W n))

/-- `Y` on `M`.  @census none (helper; engine `E2`) -/
noncomputable def essY : EssCarrier W ℓ →ₗ[L] EssCarrier W ℓ :=
  DirectSum.toModule L ℤ _ (fun n =>
    (DirectSum.lof L ℤ (EssFib W ℓ) (n - 2)).comp (yComp hℓ W n))

/-- `H` on `M`: the scalar `n` on `M_n` (`WeightData.H_apply`; the convention is the paper author's
ruling of 2026-09-10, which supersedes `R-S7-6` — both fix `H|_{M_n} = n`, so nothing here moves).
@census none (helper; engine `E2`) -/
noncomputable def essH : EssCarrier W ℓ →ₗ[L] EssCarrier W ℓ :=
  DirectSum.toModule L ℤ _ (fun n =>
    (DirectSum.lof L ℤ (EssFib W ℓ) n).comp
      ((n : L) • (LinearMap.id : EssFib W ℓ n →ₗ[L] EssFib W ℓ n)))

@[simp] theorem essX_lof (n : ℤ) (a : EssFib W ℓ n) :
    essX hℓ W (DirectSum.lof L ℤ (EssFib W ℓ) n a)
      = DirectSum.lof L ℤ (EssFib W ℓ) (n + 2) (xComp hℓ W n a) := by
  rw [essX, DirectSum.toModule_lof]; rfl

@[simp] theorem essY_lof (n : ℤ) (a : EssFib W ℓ n) :
    essY hℓ W (DirectSum.lof L ℤ (EssFib W ℓ) n a)
      = DirectSum.lof L ℤ (EssFib W ℓ) (n - 2) (yComp hℓ W n a) := by
  rw [essY, DirectSum.toModule_lof]; rfl

@[simp] theorem essH_lof (n : ℤ) (a : EssFib W ℓ n) :
    essH W (DirectSum.lof L ℤ (EssFib W ℓ) n a)
      = (n : L) • DirectSum.lof L ℤ (EssFib W ℓ) n a := by
  rw [essH, DirectSum.toModule_lof]
  show DirectSum.lof L ℤ (EssFib W ℓ) n ((n : L) • a) = _
  rw [map_smul]

/-- `X : M_n → M_{n+2}` (`WeightData.X_mem`).  @census none (helper; engine `E2`) -/
theorem essX_mem (n : ℤ) (v : EssCarrier W ℓ) (hv : v ∈ essComp W ℓ n) :
    essX hℓ W v ∈ essComp W ℓ (n + 2) := by
  obtain ⟨a, rfl⟩ := hv
  rw [essX_lof]
  exact ⟨_, rfl⟩

/-- `Y : M_n → M_{n-2}` (`WeightData.Y_mem`).  @census none (helper; engine `E2`) -/
theorem essY_mem (n : ℤ) (v : EssCarrier W ℓ) (hv : v ∈ essComp W ℓ n) :
    essY hℓ W v ∈ essComp W ℓ (n - 2) := by
  obtain ⟨a, rfl⟩ := hv
  rw [essY_lof]
  exact ⟨_, rfl⟩

/-- `H` acts on `M_n` by `n` (`WeightData.H_apply`).  @census none (helper; engine `E2`) -/
theorem essH_apply (n : ℤ) (v : EssCarrier W ℓ) (hv : v ∈ essComp W ℓ n) :
    essH W v = (n : L) • v := by
  obtain ⟨a, rfl⟩ := hv
  rw [essH_lof]


/-! #### The five branches of `xAmb`, evaluated (all `@census none (helper; engine E2)`) -/

theorem xAmb_plus {n : ℤ} (h : (ℓ : ℤ) + 1 ≤ n) (a : VM W 2) :
    xAmb hℓ W n (essIotaPlus W a)
      = essIotaPlus W (((2 : L)⁻¹) • xiOp hℓ W 2 1 (n + 1) a) := by
  rw [xAmb, if_pos h]; rfl

theorem xAmb_minus {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 1 ≤ n)) (h : n ≤ -((ℓ : ℤ) + 3))
    (a : VM W 0) :
    xAmb hℓ W n (essIotaMinus W a)
      = essIotaMinus W (((2 : L)⁻¹) • xiOp hℓ W 0 1 (n + 1) a) := by
  rw [xAmb, if_neg h1, if_pos h]; rfl

theorem xAmb_wallAm {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 1 ≤ n)) (h2 : ¬ (n ≤ -((ℓ : ℤ) + 3)))
    (h : n = -((ℓ : ℤ) + 1)) (a : VM W 0) :
    xAmb hℓ W n (essIotaMinus W a)
      = essIotaStar W (essEdgeAm W a) := by
  rw [xAmb, if_neg h1, if_neg h2, if_pos h]; rfl

theorem xAmb_wallBp {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 1 ≤ n)) (h2 : ¬ (n ≤ -((ℓ : ℤ) + 3)))
    (h3 : ¬ (n = -((ℓ : ℤ) + 1))) (h : n = (ℓ : ℤ) - 1) (a : VM W 1) :
    xAmb hℓ W n (essIotaStar W a)
      = essIotaPlus W (essEdgeBp W a) := by
  rw [xAmb, if_neg h1, if_neg h2, if_neg h3, if_pos h]; rfl

theorem xAmb_star {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 1 ≤ n)) (h2 : ¬ (n ≤ -((ℓ : ℤ) + 3)))
    (h3 : ¬ (n = -((ℓ : ℤ) + 1))) (h4 : ¬ (n = (ℓ : ℤ) - 1))
    (h : -((ℓ : ℤ) - 1) ≤ n ∧ n ≤ (ℓ : ℤ) - 3) (a : VM W 1) :
    xAmb hℓ W n (essIotaStar W a)
      = essIotaStar W (((2 : L)⁻¹) • xiOp hℓ W 1 1 (n + 1) a) := by
  rw [xAmb, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h]; rfl

/-! #### The five branches of `yAmb`, evaluated (all `@census none (helper; engine E2)`) -/

theorem yAmb_plus {n : ℤ} (h : (ℓ : ℤ) + 3 ≤ n) (a : VM W 2) :
    yAmb hℓ W n (essIotaPlus W a)
      = essIotaPlus W (((2 : L)⁻¹) • xiOp hℓ W 2 (-1) (n - 1) a) := by
  rw [yAmb, if_pos h]; rfl

theorem yAmb_minus {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 3 ≤ n)) (h : n ≤ -((ℓ : ℤ) + 1))
    (a : VM W 0) :
    yAmb hℓ W n (essIotaMinus W a)
      = essIotaMinus W (((2 : L)⁻¹) • xiOp hℓ W 0 (-1) (n - 1) a) := by
  rw [yAmb, if_neg h1, if_pos h]; rfl

theorem yAmb_wallAp {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 3 ≤ n)) (h2 : ¬ (n ≤ -((ℓ : ℤ) + 1)))
    (h : n = (ℓ : ℤ) + 1) (a : VM W 2) :
    yAmb hℓ W n (essIotaPlus W a)
      = essIotaStar W (essEdgeAp W a) := by
  rw [yAmb, if_neg h1, if_neg h2, if_pos h]; rfl

theorem yAmb_wallBm {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 3 ≤ n)) (h2 : ¬ (n ≤ -((ℓ : ℤ) + 1)))
    (h3 : ¬ (n = (ℓ : ℤ) + 1)) (h : n = -((ℓ : ℤ) - 1)) (a : VM W 1) :
    yAmb hℓ W n (essIotaStar W a)
      = essIotaMinus W (essEdgeBm W a) := by
  rw [yAmb, if_neg h1, if_neg h2, if_neg h3, if_pos h]; rfl

theorem yAmb_star {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 3 ≤ n)) (h2 : ¬ (n ≤ -((ℓ : ℤ) + 1)))
    (h3 : ¬ (n = (ℓ : ℤ) + 1)) (h4 : ¬ (n = -((ℓ : ℤ) - 1)))
    (h : -((ℓ : ℤ) - 1) + 2 ≤ n ∧ n ≤ (ℓ : ℤ) - 1) (a : VM W 1) :
    yAmb hℓ W n (essIotaStar W a)
      = essIotaStar W (((2 : L)⁻¹) • xiOp hℓ W 1 (-1) (n - 1) a) := by
  rw [yAmb, if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_pos h]; rfl


/-! #### The `[X,Y] = H` computation, in the ambient space (all `@census none (helper; engine E2)`) -/

/-- The interior computation: `4XY − 4YX = ((n+1)² − (n−1)²)·𝟏 = 4n·𝟏` on `M_n`, from `C11`
(`xi_mul_xi`, in both orders).  @census none (helper; engine `E2`) -/
theorem essLie_interior (v : Fin 3) (n : ℤ) (a : VM W v) :
    ((2 : L)⁻¹) • (xiOp hℓ W v 1 (n - 1)
        (((2 : L)⁻¹) • xiOp hℓ W v (-1) (n - 1) a))
      - ((2 : L)⁻¹) • (xiOp hℓ W v (-1) (n + 1)
        (((2 : L)⁻¹) • xiOp hℓ W v 1 (n + 1) a))
      = (n : L) • a := by
  have hA : ∀ (j : ℤ) (b : VM W v),
      xiOp hℓ W v 1 j (xiOp hℓ W v (-1) j b)
        = phiOp ℓ W v b - ((j : L) ^ 2) • b := by
    intro j b
    have h := LinearMap.congr_fun (xi_mul_xi hℓ W v j).1 b
    simpa [Module.End.mul_apply] using h
  have hB : ∀ (j : ℤ) (b : VM W v),
      xiOp hℓ W v (-1) j (xiOp hℓ W v 1 j b)
        = phiOp ℓ W v b - ((j : L) ^ 2) • b := by
    intro j b
    have h := LinearMap.congr_fun (xi_mul_xi hℓ W v j).2 b
    simpa [Module.End.mul_apply] using h
  rw [map_smul, map_smul, hA, hB, smul_smul, smul_smul]
  rw [smul_sub, smul_sub]
  rw [show (((2 : L)⁻¹) * ((2 : L)⁻¹)) = ((4 : L)⁻¹) by
    rw [← mul_inv]; norm_num]
  rw [smul_smul, smul_smul]
  have hcast : ((4 : L)⁻¹) * (((n + 1 : ℤ) : L) ^ 2)
      - ((4 : L)⁻¹) * (((n - 1 : ℤ) : L) ^ 2) = (n : L) := by
    push_cast
    field_simp
    ring
  calc ((4 : L)⁻¹) • phiOp ℓ W v a
        - ((4 : L)⁻¹ * (((n - 1 : ℤ) : L) ^ 2)) • a
        - (((4 : L)⁻¹) • phiOp ℓ W v a
        - ((4 : L)⁻¹ * (((n + 1 : ℤ) : L) ^ 2)) • a)
      = (((4 : L)⁻¹ * (((n + 1 : ℤ) : L) ^ 2))
          - ((4 : L)⁻¹ * (((n - 1 : ℤ) : L) ^ 2))) • a := by
        rw [sub_smul]; abel
    _ = (n : L) • a := by rw [hcast]


/-- `φ_{b₊}φ_{a₊} = n_+`.  @census none (helper; engine `E2`) -/
theorem edgeBp_edgeAp (a : VM W 2) :
    essEdgeBp W (essEdgeAp W a) = nOp W 2 a := rfl
/-- `φ_{b₋}φ_{a₋} = n_-`.  @census none (helper; engine `E2`) -/
theorem edgeBm_edgeAm (a : VM W 0) :
    essEdgeBm W (essEdgeAm W a) = nOp W 0 a := rfl
/-- `φ_{a₋}φ_{b₋} = n_⋆`.  @census none (helper; engine `E2`) -/
theorem edgeAm_edgeBm (a : VM W 1) :
    essEdgeAm W (essEdgeBm W a) = nOp W 1 a := rfl
/-- `φ_{a₊}φ_{b₊}`, the other candidate for `n_⋆` (`C10`).  @census none (helper; engine `E2`) -/
theorem edgeAp_edgeBp (a : VM W 1) :
    essEdgeAp W (essEdgeBp W a) = nStarPlus W a := rfl

/-- `φ_• = ℓ²·𝟏 + 4n_•`, applied.  @census none (helper; engine `E2`) -/
theorem phiOp_apply (v : Fin 3) (a : VM W v) :
    phiOp ℓ W v a = ((ℓ : L) ^ 2) • a + (4 : L) • nOp W v a := rfl

/-- The half-interior computation: `4XY` on a component, expanded through `C11`.
@census none (helper; engine `E2`) -/
theorem essLie_half (v : Fin 3) (j : ℤ) (a : VM W v) :
    ((2 : L)⁻¹) • (xiOp hℓ W v 1 j (((2 : L)⁻¹) • xiOp hℓ W v (-1) j a))
      = ((4 : L)⁻¹) • phiOp ℓ W v a
        - (((4 : L)⁻¹) * ((j : L) ^ 2)) • a := by
  have h := LinearMap.congr_fun (xi_mul_xi hℓ W v j).1 a
  have hx : xiOp hℓ W v 1 j (xiOp hℓ W v (-1) j a)
      = phiOp ℓ W v a - ((j : L) ^ 2) • a := by
    simpa [Module.End.mul_apply] using h
  rw [map_smul, hx]
  simp only [smul_sub, smul_smul]
  norm_num
  ring_nf

theorem essLie_half' (v : Fin 3) (j : ℤ) (a : VM W v) :
    ((2 : L)⁻¹) • (xiOp hℓ W v (-1) j (((2 : L)⁻¹) • xiOp hℓ W v 1 j a))
      = ((4 : L)⁻¹) • phiOp ℓ W v a
        - (((4 : L)⁻¹) * ((j : L) ^ 2)) • a := by
  have h := LinearMap.congr_fun (xi_mul_xi hℓ W v j).2 a
  have hx : xiOp hℓ W v (-1) j (xiOp hℓ W v 1 j a)
      = phiOp ℓ W v a - ((j : L) ^ 2) • a := by
    simpa [Module.End.mul_apply] using h
  rw [map_smul, hx]
  simp only [smul_sub, smul_smul]
  norm_num
  ring_nf

/-- A wall computation, in the shape `n_• − ¼(φ_• − j²)`; `φ_• = ℓ²·𝟏 + 4n_•` cancels the loop.
@census none (helper; engine `E2`) -/
theorem essLie_wallA (v : Fin 3) (j : ℤ) (a : VM W v) :
    nOp W v a
      - (((4 : L)⁻¹) • phiOp ℓ W v a
        - (((4 : L)⁻¹) * ((j : L) ^ 2)) • a)
      = (((4 : L)⁻¹) * (((j : L) ^ 2) - ((ℓ : L) ^ 2))) • a := by
  rw [phiOp_apply, smul_add, smul_smul, smul_smul]
  rw [show ((4 : L)⁻¹ * (4 : L)) = 1 by field_simp, one_smul, mul_sub, sub_smul]
  abel

/-- The other shape, `¼(φ_• − j²) − n_•`.  @census none (helper; engine `E2`) -/
theorem essLie_wallB (v : Fin 3) (j : ℤ) (a : VM W v) :
    (((4 : L)⁻¹) • phiOp ℓ W v a
        - (((4 : L)⁻¹) * ((j : L) ^ 2)) • a)
      - nOp W v a
      = (((4 : L)⁻¹) * (((ℓ : L) ^ 2) - ((j : L) ^ 2))) • a := by
  rw [phiOp_apply, smul_add, smul_smul, smul_smul]
  rw [show ((4 : L)⁻¹ * (4 : L)) = 1 by field_simp, one_smul, mul_sub, sub_smul]
  abel


set_option maxHeartbeats 1000000 in
/-- **`[X,Y] = H` on `M_n`, read in the ambient `T`.**  Eight cases: the three interiors (`C11`),
the four walls (`C11` on one side and a pair of edge maps on the other), and — at `ℓ = 1`, where
the `⋆` block is the single component `M_0` and both walls meet it — `ex:gelfand`'s **relation**
`C10` itself. -/
theorem essLie_ambient (n : ℤ) (x : EssTriple W) (hx : x ∈ essRegion W ℓ n) :
    xAmb hℓ W (n - 2) (yAmb hℓ W n x)
      - yAmb hℓ W (n + 2) (xAmb hℓ W n x) = (n : L) • x := by
  by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  case neg =>
    rw [essRegion_bot_apply W hpar hx, map_zero, map_zero, map_zero, map_zero, sub_zero,
      smul_zero]
  by_cases hA : (ℓ : ℤ) + 3 ≤ n
  · rw [essRegion_plus W hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_plus hℓ W (by omega) a, xAmb_plus hℓ W (by omega) _,
      xAmb_plus hℓ W (by omega) a, yAmb_plus hℓ W (by omega) _,
      show n - 2 + 1 = n - 1 from by ring, show n + 2 - 1 = n + 1 from by ring,
      ← map_sub, essLie_interior hℓ W 2 n a, map_smul]
  by_cases hB : n = (ℓ : ℤ) + 1
  · rw [essRegion_plus W hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_wallAp hℓ W (by omega) (by omega) hB a,
      xAmb_wallBp hℓ W (by omega) (by omega) (by omega) (by omega) _,
      xAmb_plus hℓ W (by omega) a, yAmb_plus hℓ W (by omega) _,
      show n + 2 - 1 = n + 1 from by ring,
      ← map_sub, edgeBp_edgeAp, essLie_half' hℓ W 2 (n + 1) a,
      essLie_wallA W 2 (n + 1) a, map_smul]
    congr 1
    subst hB
    push_cast
    field_simp
    ring
  by_cases hE : n ≤ -((ℓ : ℤ) + 3)
  · rw [essRegion_minus W hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_minus hℓ W (by omega) (by omega) a,
      xAmb_minus hℓ W (by omega) (by omega) _,
      xAmb_minus hℓ W (by omega) (by omega) a,
      yAmb_minus hℓ W (by omega) (by omega) _,
      show n - 2 + 1 = n - 1 from by ring, show n + 2 - 1 = n + 1 from by ring,
      ← map_sub, essLie_interior hℓ W 0 n a, map_smul]
  by_cases hD : n = -((ℓ : ℤ) + 1)
  · rw [essRegion_minus W hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_minus hℓ W (by omega) (by omega) a,
      xAmb_minus hℓ W (by omega) (by omega) _,
      xAmb_wallAm hℓ W (by omega) (by omega) hD a,
      yAmb_wallBm hℓ W (by omega) (by omega) (by omega) (by omega) _,
      show n - 2 + 1 = n - 1 from by ring,
      ← map_sub, edgeBm_edgeAm, essLie_half hℓ W 0 (n - 1) a,
      essLie_wallB W 0 (n - 1) a, map_smul]
    congr 1
    subst hD
    push_cast
    field_simp
    ring
  by_cases hone : (ℓ : ℤ) = 1
  · have hn0 : n = 0 := by omega
    rw [essRegion_star W hpar (by omega) (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_wallBm hℓ W (by omega) (by omega) (by omega) (by omega) a,
      xAmb_wallAm hℓ W (by omega) (by omega) (by omega) _,
      xAmb_wallBp hℓ W (by omega) (by omega) (by omega) (by omega) a,
      yAmb_wallAp hℓ W (by omega) (by omega) (by omega) _,
      ← map_sub, edgeAm_edgeBm, edgeAp_edgeBp,
      nOp_star_eq_nStarPlus W, sub_self, map_zero, hn0]
    simp
  by_cases hC2 : n = (ℓ : ℤ) - 1
  · rw [essRegion_star W hpar (by omega) (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_star hℓ W (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ a,
      xAmb_star hℓ W (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ _,
      xAmb_wallBp hℓ W (by omega) (by omega) (by omega) hC2 a,
      yAmb_wallAp hℓ W (by omega) (by omega) (by omega) _,
      show n - 2 + 1 = n - 1 from by ring,
      ← map_sub, edgeAp_edgeBp, ← nOp_star_eq_nStarPlus W,
      essLie_half hℓ W 1 (n - 1) a, essLie_wallB W 1 (n - 1) a, map_smul]
    congr 1
    subst hC2
    push_cast
    field_simp
    ring
  by_cases hC3 : n = -((ℓ : ℤ) - 1)
  · rw [essRegion_star W hpar (by omega) (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_wallBm hℓ W (by omega) (by omega) (by omega) hC3 a,
      xAmb_wallAm hℓ W (by omega) (by omega) (by omega) _,
      xAmb_star hℓ W (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ a,
      yAmb_star hℓ W (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ _,
      show n + 2 - 1 = n + 1 from by ring,
      ← map_sub, edgeAm_edgeBm,
      essLie_half' hℓ W 1 (n + 1) a, essLie_wallA W 1 (n + 1) a, map_smul]
    congr 1
    subst hC3
    push_cast
    field_simp
    ring
  · rw [essRegion_star W hpar (by omega) (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_star hℓ W (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ a,
      xAmb_star (n := n - 2) hℓ W (by omega) (by omega) (by omega) (by omega)
        ⟨by omega, by omega⟩ _,
      xAmb_star (n := n) hℓ W (by omega) (by omega) (by omega) (by omega)
        ⟨by omega, by omega⟩ a,
      yAmb_star (n := n + 2) hℓ W (by omega) (by omega) (by omega) (by omega)
        ⟨by omega, by omega⟩ _,
      show n - 2 + 1 = n - 1 from by ring, show n + 2 - 1 = n + 1 from by ring,
      ← map_sub, essLie_interior hℓ W 1 n a, map_smul]


/-- Two summands at propositionally equal degrees with equal ambient values are equal.  The one
transport in the layer, and it is at the level of the **degree**, not of the fibre type: `n-2+2`
and `n+2-2` are not `n` syntactically, and `rw` cannot repair that under `lof`.
@census none (helper; engine `E2`) -/
theorem essLof_congr {i j : ℤ} (h : i = j) (a : EssFib W ℓ i) (b : EssFib W ℓ j)
    (hab : (a : EssTriple W) = (b : EssTriple W)) :
    DirectSum.lof L ℤ (EssFib W ℓ) i a
      = DirectSum.lof L ℤ (EssFib W ℓ) j b := by
  subst h; exact congrArg _ (Subtype.ext hab)

set_option maxHeartbeats 1000000 in
/-- `[X,Y] = H` on a summand.  @census none (helper; engine `E2`) -/
theorem essLie_lof (n : ℤ) (a : EssFib W ℓ n) :
    essX hℓ W (essY hℓ W (DirectSum.lof L ℤ (EssFib W ℓ) n a))
      - essY hℓ W (essX hℓ W (DirectSum.lof L ℤ (EssFib W ℓ) n a))
      = essH W (DirectSum.lof L ℤ (EssFib W ℓ) n a) := by
  have hm1 : xAmb hℓ W (n - 2) (yAmb hℓ W n (a : EssTriple W))
      ∈ essRegion W ℓ n := by
    have h := xAmb_mem hℓ W (n - 2) _ (yAmb_mem hℓ W n _ a.2)
    rwa [show n - 2 + 2 = n from by ring] at h
  have hm2 : yAmb hℓ W (n + 2) (xAmb hℓ W n (a : EssTriple W))
      ∈ essRegion W ℓ n := by
    have h := yAmb_mem hℓ W (n + 2) _ (xAmb_mem hℓ W n _ a.2)
    rwa [show n + 2 - 2 = n from by ring] at h
  rw [essY_lof, essX_lof, essX_lof, essY_lof, essH_lof,
    essLof_congr W (show n - 2 + 2 = n from by ring) _ (⟨_, hm1⟩ : EssFib W ℓ n) rfl,
    essLof_congr W (show n + 2 - 2 = n from by ring) _ (⟨_, hm2⟩ : EssFib W ℓ n) rfl,
    ← map_sub, ← map_smul]
  exact congrArg _ (Subtype.ext (essLie_ambient hℓ W n _ a.2))


/-- `[H,X] = 2X`: `H` is the degree and `X` raises it by two.  @census none (helper; engine `E2`) -/
theorem essLie_H_X :
    essH W * essX hℓ W - essX hℓ W * essH W
      = (2 : L) • essX hℓ W := by
  refine DirectSum.linearMap_ext _ (fun n => LinearMap.ext fun a => ?_)
  show essH W (essX hℓ W (DirectSum.lof L ℤ (EssFib W ℓ) n a))
      - essX hℓ W (essH W (DirectSum.lof L ℤ (EssFib W ℓ) n a)) = _
  rw [essX_lof, essH_lof, essH_lof, map_smul, essX_lof, ← sub_smul]
  show _ = (2 : L) • essX hℓ W (DirectSum.lof L ℤ (EssFib W ℓ) n a)
  rw [essX_lof]
  congr 1
  push_cast
  ring

/-- `[H,Y] = -2Y`.  @census none (helper; engine `E2`) -/
theorem essLie_H_Y :
    essH W * essY hℓ W - essY hℓ W * essH W
      = -((2 : L) • essY hℓ W) := by
  refine DirectSum.linearMap_ext _ (fun n => LinearMap.ext fun a => ?_)
  show essH W (essY hℓ W (DirectSum.lof L ℤ (EssFib W ℓ) n a))
      - essY hℓ W (essH W (DirectSum.lof L ℤ (EssFib W ℓ) n a)) = _
  rw [essY_lof, essH_lof, essH_lof, map_smul, essY_lof, ← sub_smul]
  show _ = -((2 : L) • essY hℓ W
    (DirectSum.lof L ℤ (EssFib W ℓ) n a))
  rw [essY_lof, ← neg_smul]
  congr 1
  push_cast
  ring

/-- `[X,Y] = H`.  @census none (helper; engine `E2`) -/
theorem essLie_X_Y :
    essX hℓ W * essY hℓ W - essY hℓ W * essX hℓ W = essH W := by
  refine DirectSum.linearMap_ext _ (fun n => LinearMap.ext fun a => ?_)
  exact essLie_lof hℓ W n a

/-- **The graded `𝔰𝔩₂`-module of the essential-surjectivity construction** — `M = ⨁_n M_n` with
the displayed `X` and `Y` and the tautological `H`, satisfying all three `𝔰𝔩₂` relations.  This is
what `EssSurjData.setup.weight` will be; what still has to be added to it is the generalized
infinitesimal character, finite generation, the conjugation and the `ℚ`-form
(`stages/S8/DESIGN-NOTES.md` §16.4, residue items 4-7).  @census none (helper; engine `E2`) -/
noncomputable def essWeight : WeightData L (EssCarrier W ℓ) where
  comp := essComp W ℓ
  isInternal := essComp_isInternal W
  H := essH W
  X := essX hℓ W
  Y := essY hℓ W
  H_apply := essH_apply W
  X_mem := essX_mem hℓ W
  Y_mem := essY_mem hℓ W
  lie_H_X := essLie_H_X hℓ W
  lie_H_Y := essLie_H_Y hℓ W
  lie_X_Y := essLie_X_Y hℓ W


end E2Ops

/-! ### Engine `E2`, step 3 — the generalized infinitesimal character

The last piece of the `ℚ[√-1]`-side of the construction: `M` has `λ = ℓ²`.  The argument is the
source's, and it is short once the operators are in place: on `M_n`, `4XY = C − (n−1)²`
(`WeightData.four_X_Y_apply`) and, by `essXY_ambient`, `XY = n_• + ¼(ℓ² − (n−1)²)`; the `(n−1)²`
cancels and `C = ℓ²·𝟏 + 4n_•` on every component.  So `C − ℓ²·𝟏` is `4n_•`, which is nilpotent
because `V` is (`phi_scalar_add_nilpotent`, the fact that replaced `HYP-07` under `R-S8-7`), and a
single exponent — the max over the three vertices — kills every summand at once.

**The uniformity is the point.**  `essXY_ambient` proves the SAME formula at the four walls as in
the three interiors: at a wall one of `X`, `Y` is an edge map and the composite is the quiver loop
`n_•` itself, while `¼(ℓ² − (n−1)²)` vanishes there because `(n−1)² = ℓ²` at every wall.  Without
that coincidence the Casimir would have to be computed region by region.

With `essQiSetup` the `ℚ[√-1]`-side of `essSurj_exists` is complete: what remains is the
conjugation and the `ℚ`-form (`DESIGN-NOTES.md` §16.4, residue items 5-7), and `essQiSetup` is
already the whole of what `RQ-5.02`'s split-case essential surjectivity needs from this layer.
-/

section E2GIC

variable (W : (RepNilRelSplit L).FullSubcategory)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

/-- `n_•` at the degree `n`, in the ambient `T`; the three regions cover `ℤ`, so there is no
fall-through here.  @census none (helper; engine `E2`) -/
noncomputable def nAmb (ℓ : ℕ) (n : ℤ) : EssTriple W →ₗ[L] EssTriple W :=
  if (ℓ : ℤ) + 1 ≤ n then
    (essIotaPlus W).comp ((nOp W 2).comp (essPiPlus W))
  else if n ≤ -((ℓ : ℤ) + 1) then
    (essIotaMinus W).comp ((nOp W 0).comp (essPiMinus W))
  else
    (essIotaStar W).comp ((nOp W 1).comp (essPiStar W))

/-- @census none (helper; engine `E2`) -/
theorem nAmb_plus {n : ℤ} (h : (ℓ : ℤ) + 1 ≤ n) (a : VM W 2) :
    nAmb W ℓ n (essIotaPlus W a) = essIotaPlus W (nOp W 2 a) := by
  rw [nAmb, if_pos h]; rfl

/-- @census none (helper; engine `E2`) -/
theorem nAmb_minus {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 1 ≤ n)) (h : n ≤ -((ℓ : ℤ) + 1))
    (a : VM W 0) :
    nAmb W ℓ n (essIotaMinus W a) = essIotaMinus W (nOp W 0 a) := by
  rw [nAmb, if_neg h1, if_pos h]; rfl

/-- @census none (helper; engine `E2`) -/
theorem nAmb_star {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 1 ≤ n)) (h2 : ¬ (n ≤ -((ℓ : ℤ) + 1)))
    (a : VM W 1) :
    nAmb W ℓ n (essIotaStar W a) = essIotaStar W (nOp W 1 a) := by
  rw [nAmb, if_neg h1, if_neg h2]; rfl

/-- `n_•` preserves each component.  @census none (helper; engine `E2`) -/
theorem nAmb_mem (n : ℤ) (x : EssTriple W) (hx : x ∈ essRegion W ℓ n) :
    nAmb W ℓ n x ∈ essRegion W ℓ n := by
  by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · by_cases h1 : (ℓ : ℤ) + 1 ≤ n
    · rw [essRegion_plus W hpar h1] at hx ⊢
      obtain ⟨a, rfl⟩ := hx
      rw [nAmb_plus W h1]
      exact ⟨_, rfl⟩
    · by_cases h2 : n ≤ -((ℓ : ℤ) + 1)
      · rw [essRegion_minus W hpar h2] at hx ⊢
        obtain ⟨a, rfl⟩ := hx
        rw [nAmb_minus W h1 h2]
        exact ⟨_, rfl⟩
      · rw [essRegion_star W hpar (by omega) (by omega)] at hx ⊢
        obtain ⟨a, rfl⟩ := hx
        rw [nAmb_star W h1 h2]
        exact ⟨_, rfl⟩
  · rw [essRegion_bot_apply W hpar hx, map_zero]
    exact Submodule.zero_mem _


/-- `¼(φ_• − j²) = n_• + ¼(ℓ² − j²)`, from `φ_• = ℓ²·𝟏 + 4n_•`.
@census none (helper; engine `E2`) -/
theorem essQuarter (v : Fin 3) (j : ℤ) (a : VM W v) :
    ((4 : L)⁻¹) • phiOp ℓ W v a - (((4 : L)⁻¹) * ((j : L) ^ 2)) • a
      = nOp W v a
        + (((4 : L)⁻¹) * (((ℓ : L) ^ 2) - ((j : L) ^ 2))) • a := by
  rw [phiOp_apply, smul_add, smul_smul, smul_smul,
    show ((4 : L)⁻¹ * (4 : L)) = 1 by field_simp, one_smul, mul_sub, sub_smul]
  abel

set_option maxHeartbeats 1000000 in
/-- **`XY` on `M_n`, uniformly**: `XY = n_• + ¼(ℓ² − (n−1)²)`, in five cases — the three
interiors (`C11`) and the two walls where the composite is a pair of edge maps.  The formula is
the SAME at the walls as in the interiors, which is what makes the Casimir computation uniform.
@census none (helper; engine `E2`) -/
theorem essXY_ambient (n : ℤ) (x : EssTriple W) (hx : x ∈ essRegion W ℓ n) :
    xAmb hℓ W (n - 2) (yAmb hℓ W n x)
      = nAmb W ℓ n x
        + (((4 : L)⁻¹)
            * (((ℓ : L) ^ 2) - (((n - 1 : ℤ) : L) ^ 2))) • x := by
  by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  case neg =>
    rw [essRegion_bot_apply W hpar hx, map_zero, map_zero, smul_zero, add_zero, map_zero]
  by_cases hA : (ℓ : ℤ) + 3 ≤ n
  · rw [essRegion_plus W hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_plus hℓ W (by omega) a, xAmb_plus hℓ W (by omega) _,
      show n - 2 + 1 = n - 1 from by ring, essLie_half hℓ W 2 (n - 1) a,
      nAmb_plus W (by omega), essQuarter W 2 (n - 1) a, map_add, map_smul]
  by_cases hB : n = (ℓ : ℤ) + 1
  · rw [essRegion_plus W hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_wallAp hℓ W (by omega) (by omega) hB a,
      xAmb_wallBp hℓ W (by omega) (by omega) (by omega) (by omega) _,
      edgeBp_edgeAp, nAmb_plus W (by omega),
      show (((4 : L)⁻¹) * (((ℓ : L) ^ 2)
          - (((n - 1 : ℤ) : L) ^ 2))) = 0 by subst hB; push_cast; ring,
      zero_smul, add_zero]
  by_cases hC : n ≤ -((ℓ : ℤ) + 1)
  · rw [essRegion_minus W hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_minus hℓ W (by omega) (by omega) a,
      xAmb_minus hℓ W (by omega) (by omega) _,
      show n - 2 + 1 = n - 1 from by ring, essLie_half hℓ W 0 (n - 1) a,
      nAmb_minus W (by omega) (by omega), essQuarter W 0 (n - 1) a, map_add, map_smul]
  by_cases hD : n = -((ℓ : ℤ) - 1)
  · rw [essRegion_star W hpar (by omega) (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_wallBm hℓ W (by omega) (by omega) (by omega) hD a,
      xAmb_wallAm hℓ W (by omega) (by omega) (by omega) _,
      edgeAm_edgeBm, nAmb_star W (by omega) (by omega),
      show (((4 : L)⁻¹) * (((ℓ : L) ^ 2)
          - (((n - 1 : ℤ) : L) ^ 2))) = 0 by subst hD; push_cast; ring,
      zero_smul, add_zero]
  · rw [essRegion_star W hpar (by omega) (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [yAmb_star hℓ W (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ a,
      xAmb_star (n := n - 2) hℓ W (by omega) (by omega) (by omega) (by omega)
        ⟨by omega, by omega⟩ _,
      show n - 2 + 1 = n - 1 from by ring, essLie_half hℓ W 1 (n - 1) a,
      nAmb_star W (by omega) (by omega), essQuarter W 1 (n - 1) a, map_add, map_smul]


set_option maxHeartbeats 1000000 in
/-- `C − ℓ²·𝟏` is `4n_•` on every component.  @census none (helper; engine `E2`) -/
theorem essCasimirSub_lof (n : ℤ) (a : EssFib W ℓ n) :
    ((essWeight hℓ W).casimir
        - (algebraMap ℚ L ((ℓ : ℚ) ^ 2))
            • (1 : Module.End L (EssCarrier W ℓ)))
        (DirectSum.lof L ℤ (EssFib W ℓ) n a)
      = DirectSum.lof L ℤ (EssFib W ℓ) n
          (⟨(4 : L) • nAmb W ℓ n (a : EssTriple W),
            Submodule.smul_mem _ _ (nAmb_mem W n _ a.2)⟩ : EssFib W ℓ n) := by
  have hm : xAmb hℓ W (n - 2) (yAmb hℓ W n (a : EssTriple W))
      ∈ essRegion W ℓ n := by
    have h := xAmb_mem hℓ W (n - 2) _ (yAmb_mem hℓ W n _ a.2)
    rwa [show n - 2 + 2 = n from by ring] at h
  have hXY : (essWeight hℓ W).X ((essWeight hℓ W).Y
        (DirectSum.lof L ℤ (EssFib W ℓ) n a))
      = DirectSum.lof L ℤ (EssFib W ℓ) n ⟨_, hm⟩ := by
    show essX hℓ W (essY hℓ W _) = _
    rw [essY_lof, essX_lof]
    exact essLof_congr W (show n - 2 + 2 = n from by ring) _ _ rfl
  have hH : (essWeight hℓ W).H (DirectSum.lof L ℤ (EssFib W ℓ) n a)
      = (n : L) • DirectSum.lof L ℤ (EssFib W ℓ) n a := essH_lof W n a
  have halg : (algebraMap ℚ L ((ℓ : ℚ) ^ 2)) = ((ℓ : L) ^ 2) := by
    push_cast; ring
  rw [LinearMap.sub_apply, (essWeight hℓ W).casimir_apply, hH, map_smul, hH, hXY,
    smul_smul, halg]
  have hrhs : (⟨(4 : L) • nAmb W ℓ n (a : EssTriple W),
        Submodule.smul_mem _ _ (nAmb_mem W n _ a.2)⟩ : EssFib W ℓ n)
      = (4 : L)
        • (⟨nAmb W ℓ n (a : EssTriple W), nAmb_mem W n _ a.2⟩
            : EssFib W ℓ n) := rfl
  rw [hrhs, map_smul]
  have hval : (⟨_, hm⟩ : EssFib W ℓ n)
      = (⟨nAmb W ℓ n (a : EssTriple W), nAmb_mem W n _ a.2⟩ : EssFib W ℓ n)
        + (((4 : L)⁻¹)
            * (((ℓ : L) ^ 2) - (((n - 1 : ℤ) : L) ^ 2))) • a :=
    Subtype.ext (essXY_ambient hℓ W n _ a.2)
  rw [hval, map_add, map_smul, smul_add]
  simp only [smul_smul, LinearMap.smul_apply, Module.End.one_apply]
  rw [show ((4 : L) * (((4 : L)⁻¹)
        * (((ℓ : L) ^ 2) - (((n - 1 : ℤ) : L) ^ 2))))
      = (((ℓ : L) ^ 2) - (((n - 1 : ℤ) : L) ^ 2)) by field_simp]
  push_cast
  module


/-- `4n_•` at the degree `n`, in the ambient `T`; nilpotent because `V` is.
@census none (helper; engine `E2`) -/
noncomputable def cAmb (ℓ : ℕ) (n : ℤ) : EssTriple W →ₗ[L] EssTriple W :=
  (4 : L) • nAmb W ℓ n

/-- @census none (helper; engine `E2`) -/
theorem cAmb_mem (n : ℤ) (x : EssTriple W) (hx : x ∈ essRegion W ℓ n) :
    cAmb W ℓ n x ∈ essRegion W ℓ n :=
  Submodule.smul_mem _ _ (nAmb_mem W n x hx)

/-- @census none (helper; engine `E2`) -/
theorem cAmbPow_mem (m : ℕ) (n : ℤ) (x : EssTriple W) (hx : x ∈ essRegion W ℓ n) :
    ((cAmb W ℓ n) ^ m) x ∈ essRegion W ℓ n := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact cAmb_mem W n _ ih

/-- @census none (helper; engine `E2`) -/
theorem cAmbPow_plus {n : ℤ} (h : (ℓ : ℤ) + 1 ≤ n) (m : ℕ) (a : VM W 2) :
    ((cAmb W ℓ n) ^ m) (essIotaPlus W a)
      = essIotaPlus W ((((4 : L) • nOp W 2) ^ m) a) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      show (4 : L) • nAmb W ℓ n _ = _
      rw [nAmb_plus W h]
      show _ = essIotaPlus W ((4 : L) • nOp W 2 _)
      rw [map_smul]

/-- @census none (helper; engine `E2`) -/
theorem cAmbPow_minus {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 1 ≤ n)) (h : n ≤ -((ℓ : ℤ) + 1)) (m : ℕ)
    (a : VM W 0) :
    ((cAmb W ℓ n) ^ m) (essIotaMinus W a)
      = essIotaMinus W ((((4 : L) • nOp W 0) ^ m) a) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      show (4 : L) • nAmb W ℓ n _ = _
      rw [nAmb_minus W h1 h]
      show _ = essIotaMinus W ((4 : L) • nOp W 0 _)
      rw [map_smul]

/-- @census none (helper; engine `E2`) -/
theorem cAmbPow_star {n : ℤ} (h1 : ¬ ((ℓ : ℤ) + 1 ≤ n)) (h2 : ¬ (n ≤ -((ℓ : ℤ) + 1))) (m : ℕ)
    (a : VM W 1) :
    ((cAmb W ℓ n) ^ m) (essIotaStar W a)
      = essIotaStar W ((((4 : L) • nOp W 1) ^ m) a) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      show (4 : L) • nAmb W ℓ n _ = _
      rw [nAmb_star W h1 h2]
      show _ = essIotaStar W ((4 : L) • nOp W 1 _)
      rw [map_smul]

set_option maxHeartbeats 1000000 in
/-- Its `m`-th power is `(4n_•)^m` on every component.  @census none (helper; engine `E2`) -/
theorem essCasimirSub_pow_lof (m : ℕ) (n : ℤ) (a : EssFib W ℓ n) :
    (((essWeight hℓ W).casimir
        - (algebraMap ℚ L ((ℓ : ℚ) ^ 2))
            • (1 : Module.End L (EssCarrier W ℓ))) ^ m)
        (DirectSum.lof L ℤ (EssFib W ℓ) n a)
      = DirectSum.lof L ℤ (EssFib W ℓ) n
          (⟨((cAmb W ℓ n) ^ m) (a : EssTriple W),
            cAmbPow_mem W m n _ a.2⟩ : EssFib W ℓ n) := by
  induction m with
  | zero => simp only [pow_zero, Module.End.one_apply]
  | succ m ih =>
      have hv : (4 : L)
            • nAmb W ℓ n (((cAmb W ℓ n) ^ m) (a : EssTriple W))
          = ((cAmb W ℓ n) ^ (m + 1)) (a : EssTriple W) := by
        rw [pow_succ', Module.End.mul_apply]; rfl
      rw [pow_succ', Module.End.mul_apply, ih, essCasimirSub_lof]
      exact congrArg _ (Subtype.ext hv)

set_option maxHeartbeats 1000000 in
/-- **The generalized infinitesimal character `λ = ℓ²`** of the constructed module (`RQ-3.02`,
what `EssSurjData.setup.gic` needs): `C − ℓ²·𝟏` is `4n_•` on every component, and `4n_•` is
nilpotent because `V` is (`phi_scalar_add_nilpotent`, the fact that replaced `HYP-07`).  A single
exponent works for all three regions, so the power kills every summand at once.
@census none (helper; engine `E2`) -/
theorem essGIC : HasGeneralizedInfinitesimalCharacter (essWeight hℓ W) ℓ := by
  obtain ⟨m0, hm0⟩ := (phi_scalar_add_nilpotent hℓ W 0).1
  obtain ⟨m1, hm1⟩ := (phi_scalar_add_nilpotent hℓ W 1).1
  obtain ⟨m2, hm2⟩ := (phi_scalar_add_nilpotent hℓ W 2).1
  refine ⟨max m0 (max m1 m2), DirectSum.linearMap_ext _ (fun n => LinearMap.ext fun a => ?_)⟩
  set M := max m0 (max m1 m2) with hM
  have hz : ∀ v : Fin 3, (((4 : L) • nOp W v) ^ M) = 0 := by
    intro v
    fin_cases v
    · exact pow_eq_zero_of_le (by omega) hm0
    · exact pow_eq_zero_of_le (by omega) hm1
    · exact pow_eq_zero_of_le (by omega) hm2
  have hkey : ∀ x ∈ essRegion W ℓ n, ((cAmb W ℓ n) ^ M) x = 0 := by
    intro x hx
    by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
    · by_cases h1 : (ℓ : ℤ) + 1 ≤ n
      · rw [essRegion_plus W hpar h1] at hx
        obtain ⟨b, hb⟩ := hx
        rw [← hb, cAmbPow_plus W h1, hz 2]
        simp
      · by_cases h2 : n ≤ -((ℓ : ℤ) + 1)
        · rw [essRegion_minus W hpar h2] at hx
          obtain ⟨b, hb⟩ := hx
          rw [← hb, cAmbPow_minus W h1 h2, hz 0]
          simp
        · rw [essRegion_star W hpar (by omega) (by omega)] at hx
          obtain ⟨b, hb⟩ := hx
          rw [← hb, cAmbPow_star W h1 h2, hz 1]
          simp
    · rw [essRegion_bot_apply W hpar hx]
      simp
  have hc0 : (⟨((cAmb W ℓ n) ^ M) (a : EssTriple W), cAmbPow_mem W M n _ a.2⟩
      : EssFib W ℓ n) = 0 := Subtype.ext (hkey _ a.2)
  show (((essWeight hℓ W).casimir
        - (algebraMap ℚ L ((ℓ : ℚ) ^ 2))
          • (1 : Module.End L (EssCarrier W ℓ))) ^ M)
        (DirectSum.lof L ℤ (EssFib W ℓ) n a) = (0 : EssCarrier W ℓ)
  rw [show (((essWeight hℓ W).casimir
        - (algebraMap ℚ L ((ℓ : ℚ) ^ 2))
          • (1 : Module.End L (EssCarrier W ℓ))) ^ M)
        (DirectSum.lof L ℤ (EssFib W ℓ) n a)
      = _ from essCasimirSub_pow_lof hℓ W M n a]
  exact (congrArg (DirectSum.lof L ℤ (EssFib W ℓ) n) hc0).trans (map_zero _)


/-- **The `QiSetup` of the constructed module**: the graded `𝔰𝔩₂`-module together with its
generalized infinitesimal character `λ = ℓ²`.  This is `EssSurjData.setup.toQiSetup`, and it is
also exactly the datum `RQ-5.02`'s split-case essential surjectivity needs — the `ℚ`-form and the
conjugation are the only things `RQ-5.05` asks for beyond it.
@census none (helper; engine `E2`) -/
noncomputable def essQiSetup : QiSetup L ℓ (EssCarrier W ℓ) :=
  ⟨essWeight hℓ W, essGIC hℓ W⟩


end E2GIC

/-! ### Engine `E2`, step 4 — finite generation

Residue item 5 of `stages/S8/DESIGN-NOTES.md` §16.4.  On the `+` region
`2X|_{M_n} = ξ^{(n+1)}_{+,+} = φ_+^{1/2} + (n+1) = (ℓ + n + 1)·𝟏 + nilpotent`, and `ℓ + n + 1 > 0`
for `n ≥ ℓ+1`, so `X : M_n → M_{n+2}` is **onto** there; symmetrically
`2Y|_{M_n} = φ_-^{1/2} − (n−1) = (ℓ − n + 1)·𝟏 + nilpotent` is invertible for `n ≤ -(ℓ+1)`, so
`Y : M_n → M_{n-2}` is onto on the `−` region.  Hence the finitely many components in the window
`-(ℓ+1) ≤ n ≤ ℓ+1` — each finite-dimensional by `essComp_finiteDimensional` — generate `M` under
the triple, and a finite spanning set of their (finite-dimensional) sum is a finite generating set.

Only the `X`/`Y` half of `WeightData.OpStable` is used: **`IsHomog` is never needed**, because the
generating window is a union of *whole* components rather than a set of inhomogeneous vectors.
-/

section E2FG

variable (W : (RepNilRelSplit L).FullSubcategory)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

/-- A unit of `End(U)` is inverted by `linInv`.  @census none (helper) -/
theorem apply_linInv_of_isUnit {U : Type} [AddCommGroup U] [Module L U]
    {f : Module.End L U} (hf : IsUnit f) (y : U) : f (linInv f y) = y := by
  obtain ⟨u, hu⟩ := hf
  have hgf : ((↑u⁻¹ : Module.End L U) : U →ₗ[L] U).comp
      (f : U →ₗ[L] U) = LinearMap.id := by
    have h : (↑u⁻¹ : Module.End L U) * f = 1 := by rw [← hu]; exact u.inv_mul
    exact h
  have hfg : (f : U →ₗ[L] U).comp
      ((↑u⁻¹ : Module.End L U) : U →ₗ[L] U) = LinearMap.id := by
    have h : f * (↑u⁻¹ : Module.End L U) = 1 := by rw [← hu]; exact u.mul_inv
    exact h
  have := comp_linInv_of_exists hgf hfg
  exact congrArg (fun g : U →ₗ[L] U => g y) this

/-- `c·𝟏 + n` is a unit for `c ≠ 0` and `n` nilpotent — the sub-lemma §16.7 asked for.
@census none (helper; engine `E2`) -/
theorem isUnit_smul_one_add_nilpotent {U : Type} [AddCommGroup U] [Module L U]
    {c : L} (hc : c ≠ 0) {n : Module.End L U} (hn : IsNilpotent n) :
    IsUnit (c • (1 : Module.End L U) + n) :=
  isUnit_add_of_isNilpotent (isUnit_smul_one_end hc) hn ((Commute.one_left n).smul_left c)

/-- A non-zero scalar multiple of a unit is a unit.  @census none (helper; engine `E2`) -/
theorem isUnit_smul_of_ne_zero {U : Type} [AddCommGroup U] [Module L U]
    {c : L} (hc : c ≠ 0) {f : Module.End L U} (hf : IsUnit f) :
    IsUnit (c • f) := by
  have h : c • f = (c • (1 : Module.End L U)) * f := by
    rw [smul_mul_assoc, one_mul]
  rw [h]
  exact (isUnit_smul_one_end hc).mul hf

/-- **`ξ^{(j)}_{v,s} = (ℓ + s·j)·𝟏 + nilpotent`**, hence a unit as soon as `ℓ + s·j ≠ 0`.
@census none (helper; engine `E2`) -/
theorem isUnit_xiOp (v : Fin 3) (s j : ℤ) (h : (ℓ : ℤ) + s * j ≠ 0) :
    IsUnit (xiOp hℓ W v s j) := by
  have hc : ((ℓ : L) + (((s * j : ℤ)) : L)) ≠ 0 := by
    have h0 : ((((ℓ : ℤ) + s * j : ℤ)) : L) ≠ 0 := Int.cast_ne_zero.2 h
    push_cast at h0 ⊢
    exact h0
  have hrw : xiOp hℓ W v s j
      = ((ℓ : L) + (((s * j : ℤ)) : L))
          • (1 : Module.End L (VM W v))
        + (sqrtPhi hℓ W v - ((ℓ : L)) • 1) := by
    rw [xiOp, add_smul]; abel
  rw [hrw]
  exact isUnit_smul_one_add_nilpotent hc (sqrtPhi_sub_ell_isNilpotent hℓ W v)

/-- **`X : M_n → M_{n+2}` is onto for `n ≥ ℓ+1`** — the `+`-region half of finite generation.
@census none (helper; engine `E2`) -/
theorem xComp_surjective_plus {n : ℤ} (h : (ℓ : ℤ) + 1 ≤ n) :
    Function.Surjective (xComp hℓ W n) := by
  intro b
  by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · have hb : (b : EssTriple W) ∈ LinearMap.range (essIotaPlus W) := by
      rw [← essRegion_plus W (show (n + 2 - ((ℓ : ℤ) - 1)) % 2 = 0 by omega)
        (show (ℓ : ℤ) + 1 ≤ n + 2 by omega)]
      exact b.2
    obtain ⟨y, hy⟩ := hb
    have h2 : (2 : L) ≠ 0 := two_ne_zero
    have hSu : IsUnit (((2 : L)⁻¹) • xiOp hℓ W 2 1 (n + 1)) :=
      isUnit_smul_of_ne_zero (inv_ne_zero h2)
        (isUnit_xiOp hℓ W 2 1 (n + 1) (by omega))
    refine ⟨⟨essIotaPlus W
      (linInv (((2 : L)⁻¹) • xiOp hℓ W 2 1 (n + 1)) y), ?_⟩, ?_⟩
    · rw [essRegion_plus W hpar h]; exact ⟨_, rfl⟩
    · refine Subtype.ext ?_
      rw [xComp_val, xAmb_plus hℓ W h, ← hy]
      exact congrArg (essIotaPlus W) (apply_linInv_of_isUnit hSu y)
  · have hpar2 : (n + 2 - ((ℓ : ℤ) - 1)) % 2 ≠ 0 := by omega
    refine ⟨0, ?_⟩
    refine Subtype.ext ?_
    rw [map_zero]
    exact (essRegion_bot_apply W hpar2 b.2).symm

/-- **`Y : M_n → M_{n-2}` is onto for `n ≤ -(ℓ+1)`** — the `−`-region half.
@census none (helper; engine `E2`) -/
theorem yComp_surjective_minus {n : ℤ} (h : n ≤ -((ℓ : ℤ) + 1)) :
    Function.Surjective (yComp hℓ W n) := by
  intro b
  by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · have hb : (b : EssTriple W) ∈ LinearMap.range (essIotaMinus W) := by
      rw [← essRegion_minus W (show (n - 2 - ((ℓ : ℤ) - 1)) % 2 = 0 by omega)
        (show n - 2 ≤ -((ℓ : ℤ) + 1) by omega)]
      exact b.2
    obtain ⟨y, hy⟩ := hb
    have h2 : (2 : L) ≠ 0 := two_ne_zero
    have hSu : IsUnit (((2 : L)⁻¹) • xiOp hℓ W 0 (-1) (n - 1)) :=
      isUnit_smul_of_ne_zero (inv_ne_zero h2)
        (isUnit_xiOp hℓ W 0 (-1) (n - 1) (by omega))
    refine ⟨⟨essIotaMinus W
      (linInv (((2 : L)⁻¹) • xiOp hℓ W 0 (-1) (n - 1)) y), ?_⟩, ?_⟩
    · rw [essRegion_minus W hpar h]; exact ⟨_, rfl⟩
    · refine Subtype.ext ?_
      rw [yComp_val, yAmb_minus hℓ W (by omega) h, ← hy]
      exact congrArg (essIotaMinus W) (apply_linInv_of_isUnit hSu y)
  · have hpar2 : (n - 2 - ((ℓ : ℤ) - 1)) % 2 ≠ 0 := by omega
    refine ⟨0, ?_⟩
    refine Subtype.ext ?_
    rw [map_zero]
    exact (essRegion_bot_apply W hpar2 b.2).symm

/-- The generating window `⨁_{|n| ≤ ℓ+1} M_n`, a finite sum of finite-dimensional components.
@census none (helper; engine `E2`) -/
noncomputable def essWindow (ℓ : ℕ) : Submodule L (EssCarrier W ℓ) :=
  ⨆ i : (Finset.Icc (-((ℓ : ℤ) + 1)) ((ℓ : ℤ) + 1) : Finset ℤ), essComp W ℓ (i : ℤ)

/-- @census none (helper; engine `E2`) -/
theorem essWindow_finiteDimensional :
    FiniteDimensional L ↥(essWindow W ℓ) := by
  haveI : ∀ i : (Finset.Icc (-((ℓ : ℤ) + 1)) ((ℓ : ℤ) + 1) : Finset ℤ),
      FiniteDimensional L ↥(essComp W ℓ (i : ℤ)) :=
    fun i => essComp_finiteDimensional W (i : ℤ)
  exact Submodule.finiteDimensional_iSup _

/-- @census none (helper; engine `E2`) -/
theorem essComp_le_essWindow {n : ℤ} (h1 : -((ℓ : ℤ) + 1) ≤ n) (h2 : n ≤ (ℓ : ℤ) + 1) :
    essComp W ℓ n ≤ essWindow W ℓ :=
  le_iSup (fun i : (Finset.Icc (-((ℓ : ℤ) + 1)) ((ℓ : ℤ) + 1) : Finset ℤ) =>
    essComp W ℓ (i : ℤ)) ⟨n, Finset.mem_Icc.2 ⟨h1, h2⟩⟩

/-- **Finite generation of the constructed module** (`EssSurjData.fg`, residue item 5).
@census none (helper; engine `E2`) -/
theorem essFG : (essWeight hℓ W).IsFG := by
  obtain ⟨S, hS⟩ : (essWindow W ℓ).FG := by
    haveI := essWindow_finiteDimensional (ℓ := ℓ) W
    exact Module.Finite.iff_fg.1 inferInstance
  refine ⟨S, gkSpanGraded_eq_top _ fun N hSN hop _ => ?_⟩
  have hW : essWindow W ℓ ≤ N := by
    rw [← hS]; exact Submodule.span_le.2 hSN
  have hmid : ∀ n : ℤ, -((ℓ : ℤ) + 1) ≤ n → n ≤ (ℓ : ℤ) + 1 → essComp W ℓ n ≤ N :=
    fun n h1 h2 => (essComp_le_essWindow W h1 h2).trans hW
  -- upward, by `X`
  have hup : ∀ k : ℕ, essComp W ℓ ((ℓ : ℤ) + 1 + 2 * (k : ℤ)) ≤ N := by
    intro k
    induction k with
    | zero => simpa using hmid ((ℓ : ℤ) + 1) (by omega) (by omega)
    | succ k ih =>
        have hstep : (ℓ : ℤ) + 1 + 2 * ((k : ℕ) + 1 : ℕ) = ((ℓ : ℤ) + 1 + 2 * (k : ℤ)) + 2 := by
          push_cast; ring
        rw [hstep]
        rintro _ ⟨b, rfl⟩
        obtain ⟨a, ha⟩ :=
          xComp_surjective_plus hℓ W (n := (ℓ : ℤ) + 1 + 2 * (k : ℤ)) (by omega) b
        have hx : essX hℓ W
            (DirectSum.lof L ℤ (EssFib W ℓ) ((ℓ : ℤ) + 1 + 2 * (k : ℤ)) a)
            = DirectSum.lof L ℤ (EssFib W ℓ)
                (((ℓ : ℤ) + 1 + 2 * (k : ℤ)) + 2) b := by
          rw [essX_lof, ha]
        rw [← hx]
        exact hop.2.1 _ (ih ⟨a, rfl⟩)
  -- downward, by `Y`
  have hdn : ∀ k : ℕ, essComp W ℓ (-((ℓ : ℤ) + 1) - 2 * (k : ℤ)) ≤ N := by
    intro k
    induction k with
    | zero => simpa using hmid (-((ℓ : ℤ) + 1)) (by omega) (by omega)
    | succ k ih =>
        have hstep : -((ℓ : ℤ) + 1) - 2 * ((k : ℕ) + 1 : ℕ)
            = (-((ℓ : ℤ) + 1) - 2 * (k : ℤ)) - 2 := by
          push_cast; ring
        rw [hstep]
        rintro _ ⟨b, rfl⟩
        obtain ⟨a, ha⟩ :=
          yComp_surjective_minus hℓ W (n := -((ℓ : ℤ) + 1) - 2 * (k : ℤ)) (by omega) b
        have hy : essY hℓ W
            (DirectSum.lof L ℤ (EssFib W ℓ) (-((ℓ : ℤ) + 1) - 2 * (k : ℤ)) a)
            = DirectSum.lof L ℤ (EssFib W ℓ)
                ((-((ℓ : ℤ) + 1) - 2 * (k : ℤ)) - 2) b := by
          rw [essY_lof, ha]
        rw [← hy]
        exact hop.2.2 _ (ih ⟨a, rfl⟩)
  have hcomp : ∀ n : ℤ, essComp W ℓ n ≤ N := by
    intro n
    by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
    · by_cases hgt : (ℓ : ℤ) + 1 < n
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = (ℓ : ℤ) + 1 + 2 * (k : ℤ) :=
          ⟨((n - ((ℓ : ℤ) + 1)) / 2).toNat, by omega⟩
        rw [hk]; exact hup k
      · by_cases hlt : n < -((ℓ : ℤ) + 1)
        · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -((ℓ : ℤ) + 1) - 2 * (k : ℤ) :=
            ⟨((-((ℓ : ℤ) + 1) - n) / 2).toNat, by omega⟩
          rw [hk]; exact hdn k
        · exact hmid n (by omega) (by omega)
    · rw [essComp_eq_bot W hpar]; exact bot_le
  rw [eq_top_iff]
  intro x _
  induction x using DirectSum.induction_on with
  | zero => exact N.zero_mem
  | of n a =>
      refine hcomp n ⟨a, ?_⟩
      rw [DirectSum.lof_eq_of]
  | add x y hx hy => exact N.add_mem (hx trivial) (hy trivial)

end E2FG


open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory RationalQuivers.Gelfand
open scoped TensorProduct Classical Polynomial



section E2Pins

variable (W : (RepNilRelSplit L).FullSubcategory)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

/-- @census none (helper; engine `E2`) -/
theorem ofInjective_symm_coe {U X : Type} [AddCommGroup U] [Module L U]
    [AddCommGroup X] [Module L X] (f : U →ₗ[L] X)
    (hf : Function.Injective f) (z : ↥(LinearMap.range f)) :
    f ((LinearEquiv.ofInjective f hf).symm z) = (z : X) :=
  congrArg Subtype.val ((LinearEquiv.ofInjective f hf).apply_symm_apply z)

variable {U : Type} [AddCommGroup U] [Module L U]

/-- The reading rule, generic in the injection: `essIso*` reads `w` through `f`.
@census none (helper; engine `E2`) -/
theorem essIsoOf_iota (ℓ : ℕ) {n : ℤ} (f : U →ₗ[L] EssTriple W)
    (hf : Function.Injective f) (hreg : essRegion W ℓ n = LinearMap.range f)
    (w : ↥(essComp W ℓ n)) :
    f (((essCompEquiv W n).trans ((LinearEquiv.ofEq _ _ hreg).trans
        (LinearEquiv.ofInjective f hf).symm)) w)
      = ((essCompEquiv W n w : EssFib W ℓ n) : EssTriple W) := by
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ofInjective_symm_coe,
    LinearEquiv.coe_ofEq_apply]

/-- @census none (helper; engine `E2`) -/
theorem essIsoOf_lof (ℓ : ℕ) {n : ℤ} (f : U →ₗ[L] EssTriple W)
    (hf : Function.Injective f) (hreg : essRegion W ℓ n = LinearMap.range f)
    (a : EssFib W ℓ n) (y : U) (hay : (a : EssTriple W) = f y) :
    ((essCompEquiv W n).trans ((LinearEquiv.ofEq _ _ hreg).trans
        (LinearEquiv.ofInjective f hf).symm))
      ⟨DirectSum.lof L ℤ (EssFib W ℓ) n a, ⟨a, rfl⟩⟩ = y := by
  refine hf ?_
  rw [essIsoOf_iota W ℓ f hf hreg]
  rw [show essCompEquiv W n
      ⟨DirectSum.lof L ℤ (EssFib W ℓ) n a, ⟨a, rfl⟩⟩ = a from
    LinearEquiv.symm_apply_apply
      (LinearEquiv.ofInjective _ (lof_injective L ℤ (EssFib W ℓ) n)) a]
  exact hay

/-- @census none (helper; engine `E2`) -/
theorem essIsoOf_symm_coe (ℓ : ℕ) {n : ℤ} (f : U →ₗ[L] EssTriple W)
    (hf : Function.Injective f) (hreg : essRegion W ℓ n = LinearMap.range f)
    (y : U) (hm : f y ∈ essRegion W ℓ n) :
    (((((essCompEquiv W n).trans ((LinearEquiv.ofEq _ _ hreg).trans
        (LinearEquiv.ofInjective f hf).symm)).symm y : ↥(essComp W ℓ n))
          : EssCarrier W ℓ))
      = DirectSum.lof L ℤ (EssFib W ℓ) n ⟨f y, hm⟩ := by
  have h : ((essCompEquiv W n).trans ((LinearEquiv.ofEq _ _ hreg).trans
      (LinearEquiv.ofInjective f hf).symm)).symm y
      = ⟨DirectSum.lof L ℤ (EssFib W ℓ) n ⟨f y, hm⟩, ⟨_, rfl⟩⟩ :=
    (LinearEquiv.symm_apply_eq _).2
      (essIsoOf_lof W ℓ f hf hreg ⟨f y, hm⟩ y rfl).symm
  rw [h]

/-- **The pin engine.**  `e₁`/`e₂` are the source and target `C9` isos, handed in as arguments so
that each pin can pass `essIsoPlus`/`essIsoStar`/`essIsoMinus` with `rfl`.
@census none (helper; engine `E2`) -/
theorem essPin_gen (ℓ : ℕ) {n m : ℤ} {W₁ W₂ : Type}
    [AddCommGroup W₁] [Module L W₁] [AddCommGroup W₂] [Module L W₂]
    (f₁ : W₁ →ₗ[L] EssTriple W) (hf₁ : Function.Injective f₁)
    (hreg₁ : essRegion W ℓ n = LinearMap.range f₁)
    (f₂ : W₂ →ₗ[L] EssTriple W) (hf₂ : Function.Injective f₂)
    (hreg₂ : essRegion W ℓ m = LinearMap.range f₂)
    (e₁ : ↥(essComp W ℓ n) ≃ₗ[L] W₁)
    (he₁ : e₁ = (essCompEquiv W n).trans ((LinearEquiv.ofEq _ _ hreg₁).trans
      (LinearEquiv.ofInjective f₁ hf₁).symm))
    (e₂ : ↥(essComp W ℓ m) ≃ₗ[L] W₂)
    (he₂ : e₂ = (essCompEquiv W m).trans ((LinearEquiv.ofEq _ _ hreg₂).trans
      (LinearEquiv.ofInjective f₂ hf₂).symm))
    (T : EssCarrier W ℓ → EssCarrier W ℓ)
    (A : EssTriple W → EssTriple W)
    (hTlof : ∀ (b : EssFib W ℓ n) (hb : A (b : EssTriple W) ∈ essRegion W ℓ m),
      T (DirectSum.lof L ℤ (EssFib W ℓ) n b)
        = DirectSum.lof L ℤ (EssFib W ℓ) m ⟨A (b : EssTriple W), hb⟩)
    (G : W₁ → W₂) (hG : ∀ y : W₁, A (f₁ y) = f₂ (G y))
    (v : EssCarrier W ℓ) (hv : v ∈ essComp W ℓ n) :
    T v = ((e₂.symm (G (e₁ ⟨v, hv⟩)) : ↥(essComp W ℓ m)) : EssCarrier W ℓ) := by
  subst he₁
  subst he₂
  have hv' := hv
  obtain ⟨a, ha⟩ := hv'
  have hareg : (a : EssTriple W) ∈ LinearMap.range f₁ := by
    rw [← hreg₁]; exact a.2
  obtain ⟨y0, hy0⟩ := hareg
  have hkey : (((essCompEquiv W n).trans ((LinearEquiv.ofEq _ _ hreg₁).trans
      (LinearEquiv.ofInjective f₁ hf₁).symm)) ⟨v, hv⟩) = y0 := by
    rw [show (⟨v, hv⟩ : ↥(essComp W ℓ n))
        = ⟨DirectSum.lof L ℤ (EssFib W ℓ) n a, ⟨a, rfl⟩⟩ from
      Subtype.ext ha.symm]
    exact essIsoOf_lof W ℓ f₁ hf₁ hreg₁ a y0 hy0.symm
  have hmem : f₂ (G y0) ∈ essRegion W ℓ m := by rw [hreg₂]; exact ⟨_, rfl⟩
  have hb : A (a : EssTriple W) ∈ essRegion W ℓ m := by
    rw [← hy0, hG, hreg₂]; exact ⟨_, rfl⟩
  rw [hkey, essIsoOf_symm_coe W ℓ f₂ hf₂ hreg₂ (G y0) hmem, ← ha, hTlof a hb]
  refine essLof_congr W rfl _ _ ?_
  show A (a : EssTriple W) = f₂ (G y0)
  rw [← hy0, hG]


/-! #### The fifteen pins, one application of `essPin_gen` each -/

/-- `X`'s summand rule, at a target degree given by an equation.  @census none (helper; engine `E2`) -/
theorem essX_lof_pin {n m : ℤ} (hm : n + 2 = m) (b : EssFib W ℓ n)
    (hb : xAmb hℓ W n (b : EssTriple W) ∈ essRegion W ℓ m) :
    essX hℓ W (DirectSum.lof L ℤ (EssFib W ℓ) n b)
      = DirectSum.lof L ℤ (EssFib W ℓ) m
          ⟨xAmb hℓ W n (b : EssTriple W), hb⟩ := by
  rw [essX_lof]
  exact essLof_congr W hm _ _ rfl

/-- `Y`'s summand rule.  @census none (helper; engine `E2`) -/
theorem essY_lof_pin {n m : ℤ} (hm : n - 2 = m) (b : EssFib W ℓ n)
    (hb : yAmb hℓ W n (b : EssTriple W) ∈ essRegion W ℓ m) :
    essY hℓ W (DirectSum.lof L ℤ (EssFib W ℓ) n b)
      = DirectSum.lof L ℤ (EssFib W ℓ) m
          ⟨yAmb hℓ W n (b : EssTriple W), hb⟩ := by
  rw [essY_lof]
  exact essLof_congr W hm _ _ rfl

/-- **`C13`, `X` on the `+` interior**.  @census none (helper; engine `E2`) -/
theorem essPin_X_plus (j : ℤ) (hj : (ℓ : ℤ) < j) (hp : (j - (ℓ : ℤ)) % 2 = 0)
    (v : EssCarrier W ℓ) (hv : v ∈ essComp W ℓ (j - 1)) :
    essX hℓ W v
      = (((essIsoPlus W (by omega) (by omega : (ℓ : ℤ) + 1 ≤ j + 1)).symm
          (((2 : L)⁻¹) • xiOp hℓ W 2 1 j
            (essIsoPlus W (by omega) (by omega : (ℓ : ℤ) + 1 ≤ j - 1) ⟨v, hv⟩))
              : ↥(essComp W ℓ (j + 1))) : EssCarrier W ℓ) :=
  essPin_gen W ℓ (essIotaPlus W) (essIotaPlus_inj W)
    (essRegion_plus W (by omega) (by omega))
    (essIotaPlus W) (essIotaPlus_inj W)
    (essRegion_plus W (by omega) (by omega))
    _ rfl _ rfl (essX hℓ W) (xAmb hℓ W (j - 1))
    (fun b hb => essX_lof_pin hℓ W (by ring) b hb)
    (fun y => ((2 : L)⁻¹) • xiOp hℓ W 2 1 j y)
    (fun y => by
      rw [xAmb_plus hℓ W (by omega : (ℓ : ℤ) + 1 ≤ j - 1),
        show j - 1 + 1 = j from by ring])
    v hv

/-- **`C13`, `X` on the `⋆` interior**.  @census none (helper; engine `E2`) -/
theorem essPin_X_star (j : ℤ) (hj : -(ℓ : ℤ) < j) (hj' : j < (ℓ : ℤ))
    (hp : (j - (ℓ : ℤ)) % 2 = 0)
    (v : EssCarrier W ℓ) (hv : v ∈ essComp W ℓ (j - 1)) :
    essX hℓ W v
      = (((essIsoStar W (by omega) (by omega) (by omega)).symm
          (((2 : L)⁻¹) • xiOp hℓ W 1 1 j
            (essIsoStar W (by omega) (by omega) (by omega) ⟨v, hv⟩))
              : ↥(essComp W ℓ (j + 1))) : EssCarrier W ℓ) :=
  essPin_gen W ℓ (essIotaStar W) (essIotaStar_inj W)
    (essRegion_star W (by omega) (by omega) (by omega))
    (essIotaStar W) (essIotaStar_inj W)
    (essRegion_star W (by omega) (by omega) (by omega))
    _ rfl _ rfl (essX hℓ W) (xAmb hℓ W (j - 1))
    (fun b hb => essX_lof_pin hℓ W (by ring) b hb)
    (fun y => ((2 : L)⁻¹) • xiOp hℓ W 1 1 j y)
    (fun y => by
      rw [xAmb_star hℓ W (by omega) (by omega) (by omega) (by omega)
          ⟨by omega, by omega⟩, show j - 1 + 1 = j from by ring])
    v hv

/-- **`C13`, `X` on the `−` interior**.  @census none (helper; engine `E2`) -/
theorem essPin_X_minus (j : ℤ) (hj : j < -(ℓ : ℤ)) (hp : (j - (ℓ : ℤ)) % 2 = 0)
    (v : EssCarrier W ℓ) (hv : v ∈ essComp W ℓ (j - 1)) :
    essX hℓ W v
      = (((essIsoMinus W (by omega) (by omega : j + 1 ≤ -((ℓ : ℤ) + 1))).symm
          (((2 : L)⁻¹) • xiOp hℓ W 0 1 j
            (essIsoMinus W (by omega) (by omega : j - 1 ≤ -((ℓ : ℤ) + 1)) ⟨v, hv⟩))
              : ↥(essComp W ℓ (j + 1))) : EssCarrier W ℓ) :=
  essPin_gen W ℓ (essIotaMinus W) (essIotaMinus_inj W)
    (essRegion_minus W (by omega) (by omega))
    (essIotaMinus W) (essIotaMinus_inj W)
    (essRegion_minus W (by omega) (by omega))
    _ rfl _ rfl (essX hℓ W) (xAmb hℓ W (j - 1))
    (fun b hb => essX_lof_pin hℓ W (by ring) b hb)
    (fun y => ((2 : L)⁻¹) • xiOp hℓ W 0 1 j y)
    (fun y => by
      rw [xAmb_minus hℓ W (by omega) (by omega), show j - 1 + 1 = j from by ring])
    v hv

/-- **`C13`, `X` at the `b₊` wall `j = ℓ`**.  @census none (helper; engine `E2`) -/
theorem essPin_X_bdry_plus (v : EssCarrier W ℓ)
    (hv : v ∈ essComp W ℓ ((ℓ : ℤ) - 1)) :
    essX hℓ W v
      = (((essIsoPlus W (by omega) (by omega : (ℓ : ℤ) + 1 ≤ (ℓ : ℤ) + 1)).symm
          (Vedge W 3
            (essIsoStar W (by omega) (by omega) (by omega) ⟨v, hv⟩))
              : ↥(essComp W ℓ ((ℓ : ℤ) + 1))) : EssCarrier W ℓ) :=
  essPin_gen W ℓ (essIotaStar W) (essIotaStar_inj W)
    (essRegion_star W (by omega) (by omega) (by omega))
    (essIotaPlus W) (essIotaPlus_inj W)
    (essRegion_plus W (by omega) (by omega))
    _ rfl _ rfl (essX hℓ W) (xAmb hℓ W ((ℓ : ℤ) - 1))
    (fun b hb => essX_lof_pin hℓ W (by ring) b hb)
    (fun y => Vedge W 3 y)
    (fun y => xAmb_wallBp hℓ W (by omega) (by omega) (by omega) rfl y)
    v hv

/-- **`C13`, `X` at the `a₋` wall `j = -ℓ`**.  @census none (helper; engine `E2`) -/
theorem essPin_X_bdry_minus (v : EssCarrier W ℓ)
    (hv : v ∈ essComp W ℓ (-((ℓ : ℤ) + 1))) :
    essX hℓ W v
      = (((essIsoStar W (by omega) (by omega) (by omega)).symm
          (Vedge W 0
            (essIsoMinus W (by omega) (by omega : -((ℓ : ℤ) + 1) ≤ -((ℓ : ℤ) + 1))
              ⟨v, hv⟩))
              : ↥(essComp W ℓ (-((ℓ : ℤ) - 1)))) : EssCarrier W ℓ) :=
  essPin_gen W ℓ (essIotaMinus W) (essIotaMinus_inj W)
    (essRegion_minus W (by omega) (by omega))
    (essIotaStar W) (essIotaStar_inj W)
    (essRegion_star W (by omega) (by omega) (by omega))
    _ rfl _ rfl (essX hℓ W) (xAmb hℓ W (-((ℓ : ℤ) + 1)))
    (fun b hb => essX_lof_pin hℓ W (by ring) b hb)
    (fun y => Vedge W 0 y)
    (fun y => xAmb_wallAm hℓ W (by omega) (by omega) rfl y)
    v hv

/-- **`C13`, `Y` on the `+` interior**.  @census none (helper; engine `E2`) -/
theorem essPin_Y_plus (j : ℤ) (hj : (ℓ : ℤ) < j) (hp : (j - (ℓ : ℤ)) % 2 = 0)
    (v : EssCarrier W ℓ) (hv : v ∈ essComp W ℓ (j + 1)) :
    essY hℓ W v
      = (((essIsoPlus W (by omega) (by omega : (ℓ : ℤ) + 1 ≤ j - 1)).symm
          (((2 : L)⁻¹) • xiOp hℓ W 2 (-1) j
            (essIsoPlus W (by omega) (by omega : (ℓ : ℤ) + 1 ≤ j + 1) ⟨v, hv⟩))
              : ↥(essComp W ℓ (j - 1))) : EssCarrier W ℓ) :=
  essPin_gen W ℓ (essIotaPlus W) (essIotaPlus_inj W)
    (essRegion_plus W (by omega) (by omega))
    (essIotaPlus W) (essIotaPlus_inj W)
    (essRegion_plus W (by omega) (by omega))
    _ rfl _ rfl (essY hℓ W) (yAmb hℓ W (j + 1))
    (fun b hb => essY_lof_pin hℓ W (by ring) b hb)
    (fun y => ((2 : L)⁻¹) • xiOp hℓ W 2 (-1) j y)
    (fun y => by
      rw [yAmb_plus hℓ W (by omega : (ℓ : ℤ) + 3 ≤ j + 1),
        show j + 1 - 1 = j from by ring])
    v hv

/-- **`C13`, `Y` on the `⋆` interior**.  @census none (helper; engine `E2`) -/
theorem essPin_Y_star (j : ℤ) (hj : -(ℓ : ℤ) < j) (hj' : j < (ℓ : ℤ))
    (hp : (j - (ℓ : ℤ)) % 2 = 0)
    (v : EssCarrier W ℓ) (hv : v ∈ essComp W ℓ (j + 1)) :
    essY hℓ W v
      = (((essIsoStar W (by omega) (by omega) (by omega)).symm
          (((2 : L)⁻¹) • xiOp hℓ W 1 (-1) j
            (essIsoStar W (by omega) (by omega) (by omega) ⟨v, hv⟩))
              : ↥(essComp W ℓ (j - 1))) : EssCarrier W ℓ) :=
  essPin_gen W ℓ (essIotaStar W) (essIotaStar_inj W)
    (essRegion_star W (by omega) (by omega) (by omega))
    (essIotaStar W) (essIotaStar_inj W)
    (essRegion_star W (by omega) (by omega) (by omega))
    _ rfl _ rfl (essY hℓ W) (yAmb hℓ W (j + 1))
    (fun b hb => essY_lof_pin hℓ W (by ring) b hb)
    (fun y => ((2 : L)⁻¹) • xiOp hℓ W 1 (-1) j y)
    (fun y => by
      rw [yAmb_star hℓ W (by omega) (by omega) (by omega) (by omega)
          ⟨by omega, by omega⟩, show j + 1 - 1 = j from by ring])
    v hv

/-- **`C13`, `Y` on the `−` interior**.  @census none (helper; engine `E2`) -/
theorem essPin_Y_minus (j : ℤ) (hj : j < -(ℓ : ℤ)) (hp : (j - (ℓ : ℤ)) % 2 = 0)
    (v : EssCarrier W ℓ) (hv : v ∈ essComp W ℓ (j + 1)) :
    essY hℓ W v
      = (((essIsoMinus W (by omega) (by omega : j - 1 ≤ -((ℓ : ℤ) + 1))).symm
          (((2 : L)⁻¹) • xiOp hℓ W 0 (-1) j
            (essIsoMinus W (by omega) (by omega : j + 1 ≤ -((ℓ : ℤ) + 1)) ⟨v, hv⟩))
              : ↥(essComp W ℓ (j - 1))) : EssCarrier W ℓ) :=
  essPin_gen W ℓ (essIotaMinus W) (essIotaMinus_inj W)
    (essRegion_minus W (by omega) (by omega))
    (essIotaMinus W) (essIotaMinus_inj W)
    (essRegion_minus W (by omega) (by omega))
    _ rfl _ rfl (essY hℓ W) (yAmb hℓ W (j + 1))
    (fun b hb => essY_lof_pin hℓ W (by ring) b hb)
    (fun y => ((2 : L)⁻¹) • xiOp hℓ W 0 (-1) j y)
    (fun y => by
      rw [yAmb_minus hℓ W (by omega) (by omega), show j + 1 - 1 = j from by ring])
    v hv

/-- **`C13`, `Y` at the `a₊` wall `j = ℓ`**.  @census none (helper; engine `E2`) -/
theorem essPin_Y_bdry_plus (v : EssCarrier W ℓ)
    (hv : v ∈ essComp W ℓ ((ℓ : ℤ) + 1)) :
    essY hℓ W v
      = (((essIsoStar W (by omega) (by omega) (by omega)).symm
          (Vedge W 2
            (essIsoPlus W (by omega) (by omega : (ℓ : ℤ) + 1 ≤ (ℓ : ℤ) + 1) ⟨v, hv⟩))
              : ↥(essComp W ℓ ((ℓ : ℤ) - 1))) : EssCarrier W ℓ) :=
  essPin_gen W ℓ (essIotaPlus W) (essIotaPlus_inj W)
    (essRegion_plus W (by omega) (by omega))
    (essIotaStar W) (essIotaStar_inj W)
    (essRegion_star W (by omega) (by omega) (by omega))
    _ rfl _ rfl (essY hℓ W) (yAmb hℓ W ((ℓ : ℤ) + 1))
    (fun b hb => essY_lof_pin hℓ W (by ring) b hb)
    (fun y => Vedge W 2 y)
    (fun y => yAmb_wallAp hℓ W (by omega) (by omega) rfl y)
    v hv

/-- **`C13`, `Y` at the `b₋` wall `j = -ℓ`**.  @census none (helper; engine `E2`) -/
theorem essPin_Y_bdry_minus (v : EssCarrier W ℓ)
    (hv : v ∈ essComp W ℓ (-((ℓ : ℤ) - 1))) :
    essY hℓ W v
      = (((essIsoMinus W (by omega) (by omega : -((ℓ : ℤ) + 1) ≤ -((ℓ : ℤ) + 1))).symm
          (Vedge W 1
            (essIsoStar W (by omega) (by omega) (by omega) ⟨v, hv⟩))
              : ↥(essComp W ℓ (-((ℓ : ℤ) + 1)))) : EssCarrier W ℓ) :=
  essPin_gen W ℓ (essIotaStar W) (essIotaStar_inj W)
    (essRegion_star W (by omega) (by omega) (by omega))
    (essIotaMinus W) (essIotaMinus_inj W)
    (essRegion_minus W (by omega) (by omega))
    _ rfl _ rfl (essY hℓ W) (yAmb hℓ W (-((ℓ : ℤ) - 1)))
    (fun b hb => essY_lof_pin hℓ W (by ring) b hb)
    (fun y => Vedge W 1 y)
    (fun y => yAmb_wallBm hℓ W (by omega) (by omega) (by omega) rfl y)
    v hv



end E2Pins

/-! ### `SplitEssSurjData` — the `c`-free construction, pinned -/

/-- **The `c`-free essential-surjectivity construction, pinned** (Step O-18a; `C9`, `C13`): an
object of `HC_λ(𝔤,K)_L` (`HCFObj`) whose components are identified with `W(+)`, `W(⋆)`, `W(−)` on
the displayed ranges, and whose `X`, `Y` are the displayed formulas `2X|_{M_{j-1}} = ξ^{(j)}_{•,+}`,
`2Y|_{M_{j+1}} = ξ^{(j)}_{•,-}` on every component, boundary cases `j = ±ℓ` included.  The
non-split `EssSurjData V` extends `SplitEssSurjData hℓ V.toSplitW` by the rational structure.
@census none (helper; route (α) core)
@clauses   RQ2-5.12-S-O18a -/
structure SplitEssSurjData (W : (RepNilRelSplit L).FullSubcategory) extends HCFObj L ℓ where
  /-- **`C9`**: `M_n = V(+)` for `ℓ + 1 ≤ n` -/
  isoPlus : ∀ n : ℤ, (ℓ : ℤ) + 1 ≤ n → (n - ((ℓ : ℤ) + 1)) % 2 = 0 →
    weight.comp n ≃ₗ[L] VM W 2
  /-- **`C9`**: `M_n = V(⋆)` for `-(ℓ-1) ≤ n ≤ ℓ-1` -/
  isoStar : ∀ n : ℤ, -((ℓ : ℤ) - 1) ≤ n → n ≤ (ℓ : ℤ) - 1 → (n - ((ℓ : ℤ) + 1)) % 2 = 0 →
    weight.comp n ≃ₗ[L] VM W 1
  /-- **`C9`**: `M_n = V(−)` for `n ≤ -(ℓ+1)` -/
  isoMinus : ∀ n : ℤ, n ≤ -((ℓ : ℤ) + 1) → (n - ((ℓ : ℤ) + 1)) % 2 = 0 →
    weight.comp n ≃ₗ[L] VM W 0
  /-- **`C13`**: `2X|_{M_{j-1}} = ξ^{(j)}_{+,+}` for `ℓ < j` -/
  X_plus : ∀ (j : ℤ) (_hj : (ℓ : ℤ) < j) (_hp : (j - (ℓ : ℤ)) % 2 = 0),
    ∀ v (hv : v ∈ weight.comp (j - 1)),
      weight.X v = (isoPlus (j + 1) (by omega) (by omega)).symm
        (((2 : L)⁻¹) • xiOp hℓ W 2 1 j (isoPlus (j - 1) (by omega) (by omega) ⟨v, hv⟩))
  /-- **`C13`**: `2X|_{M_{j-1}} = ξ^{(j)}_{⋆,+}` for `-ℓ < j < ℓ` -/
  X_star : ∀ (j : ℤ) (_hj : -(ℓ : ℤ) < j) (_hj' : j < (ℓ : ℤ)) (_hp : (j - (ℓ : ℤ)) % 2 = 0),
    ∀ v (hv : v ∈ weight.comp (j - 1)),
      weight.X v = (isoStar (j + 1) (by omega) (by omega) (by omega)).symm
        (((2 : L)⁻¹) • xiOp hℓ W 1 1 j
          (isoStar (j - 1) (by omega) (by omega) (by omega) ⟨v, hv⟩))
  /-- **`C13`**: `2X|_{M_{j-1}} = ξ^{(j)}_{-,+}` for `j < -ℓ` -/
  X_minus : ∀ (j : ℤ) (_hj : j < -(ℓ : ℤ)) (_hp : (j - (ℓ : ℤ)) % 2 = 0),
    ∀ v (hv : v ∈ weight.comp (j - 1)),
      weight.X v = (isoMinus (j + 1) (by omega) (by omega)).symm
        (((2 : L)⁻¹) • xiOp hℓ W 0 1 j (isoMinus (j - 1) (by omega) (by omega) ⟨v, hv⟩))
  /-- **`C13`, boundary `j = ℓ`**: `X|_{M_{ℓ-1}} = φ_{b₊}` -/
  X_bdry_plus : ∀ v (hv : v ∈ weight.comp ((ℓ : ℤ) - 1)),
    weight.X v = (isoPlus ((ℓ : ℤ) + 1) le_rfl (by omega)).symm
      (Vedge W 3 (isoStar ((ℓ : ℤ) - 1) (by omega) le_rfl (by omega) ⟨v, hv⟩))
  /-- **`C13`, boundary `j = -ℓ`**: `X|_{M_{-(ℓ+1)}} = φ_{a₋}` -/
  X_bdry_minus : ∀ v (hv : v ∈ weight.comp (-((ℓ : ℤ) + 1))),
    weight.X v = (isoStar (-((ℓ : ℤ) - 1)) le_rfl (by omega) (by omega)).symm
      (Vedge W 0 (isoMinus (-((ℓ : ℤ) + 1)) le_rfl (by omega) ⟨v, hv⟩))
  /-- **`C13`**: `2Y|_{M_{j+1}} = ξ^{(j)}_{+,-}` for `ℓ < j` -/
  Y_plus : ∀ (j : ℤ) (_hj : (ℓ : ℤ) < j) (_hp : (j - (ℓ : ℤ)) % 2 = 0),
    ∀ v (hv : v ∈ weight.comp (j + 1)),
      weight.Y v = (isoPlus (j - 1) (by omega) (by omega)).symm
        (((2 : L)⁻¹) • xiOp hℓ W 2 (-1) j
          (isoPlus (j + 1) (by omega) (by omega) ⟨v, hv⟩))
  /-- **`C13`**: `2Y|_{M_{j+1}} = ξ^{(j)}_{⋆,-}` for `-ℓ < j < ℓ` -/
  Y_star : ∀ (j : ℤ) (_hj : -(ℓ : ℤ) < j) (_hj' : j < (ℓ : ℤ)) (_hp : (j - (ℓ : ℤ)) % 2 = 0),
    ∀ v (hv : v ∈ weight.comp (j + 1)),
      weight.Y v = (isoStar (j - 1) (by omega) (by omega) (by omega)).symm
        (((2 : L)⁻¹) • xiOp hℓ W 1 (-1) j
          (isoStar (j + 1) (by omega) (by omega) (by omega) ⟨v, hv⟩))
  /-- **`C13`**: `2Y|_{M_{j+1}} = ξ^{(j)}_{-,-}` for `j < -ℓ` -/
  Y_minus : ∀ (j : ℤ) (_hj : j < -(ℓ : ℤ)) (_hp : (j - (ℓ : ℤ)) % 2 = 0),
    ∀ v (hv : v ∈ weight.comp (j + 1)),
      weight.Y v = (isoMinus (j - 1) (by omega) (by omega)).symm
        (((2 : L)⁻¹) • xiOp hℓ W 0 (-1) j
          (isoMinus (j + 1) (by omega) (by omega) ⟨v, hv⟩))
  /-- **`C13`, boundary `j = ℓ`**: `Y|_{M_{ℓ+1}} = φ_{a₊}` -/
  Y_bdry_plus : ∀ v (hv : v ∈ weight.comp ((ℓ : ℤ) + 1)),
    weight.Y v = (isoStar ((ℓ : ℤ) - 1) (by omega) le_rfl (by omega)).symm
      (Vedge W 2 (isoPlus ((ℓ : ℤ) + 1) le_rfl (by omega) ⟨v, hv⟩))
  /-- **`C13`, boundary `j = -ℓ`**: `Y|_{M_{-(ℓ-1)}} = φ_{b₋}` -/
  Y_bdry_minus : ∀ v (hv : v ∈ weight.comp (-((ℓ : ℤ) - 1))),
    weight.Y v = (isoMinus (-((ℓ : ℤ) + 1)) le_rfl (by omega)).symm
      (Vedge W 1 (isoStar (-((ℓ : ℤ) - 1)) le_rfl (by omega) (by omega) ⟨v, hv⟩))

namespace SplitEssSurjData

variable {hℓ} {W : (RepNilRelSplit L).FullSubcategory} (D : SplitEssSurjData hℓ W)


/-- `M_{ℓ+1} = V(+)`.  @census none (helper) -/
noncomputable def toPlus : D.weight.comp ((ℓ : ℤ) + 1) ≃ₗ[L] VM W 2 :=
  D.isoPlus _ le_rfl (by omega)

/-- `M_{-(ℓ+1)} = V(−)`.  @census none (helper) -/
noncomputable def toMinus : D.weight.comp (-((ℓ : ℤ) + 1)) ≃ₗ[L] VM W 0 :=
  D.isoMinus _ le_rfl (by omega)

/-- `M_{-(ℓ-1)} = V(⋆)`.  @census none (helper) -/
noncomputable def toStarLo : D.weight.comp (-((ℓ : ℤ) - 1)) ≃ₗ[L] VM W 1 :=
  D.isoStar _ le_rfl (by omega) (by omega)

/-- `M_{ℓ-1} = V(⋆)`.  @census none (helper) -/
noncomputable def toStarHi : D.weight.comp ((ℓ : ℤ) - 1) ≃ₗ[L] VM W 1 :=
  D.isoStar _ (by omega) le_rfl (by omega)

/-- An operator of `M` sending `M_n` into `M_m`, read on `V(•)` through the identifications.
@census none (helper) -/
noncomputable def transport {n m : ℤ} {W₁ W₂ : Type} [AddCommGroup W₁] [Module L W₁]
    [AddCommGroup W₂] [Module L W₂]
    (e₁ : D.weight.comp n ≃ₗ[L] W₁) (e₂ : D.weight.comp m ≃ₗ[L] W₂)
    (T : Module.End L D.carrier) (hT : ∀ v ∈ D.weight.comp n, T v ∈ D.weight.comp m) :
    W₁ →ₗ[L] W₂ :=
  e₂.toLinearMap ∘ₗ (T.restrict (p := D.weight.comp n) (q := D.weight.comp m) hT) ∘ₗ
    e₁.symm.toLinearMap


/-- `X⋆` of the constructed module, on `V(⋆)`.  @census none (helper) -/
noncomputable def xStarV : Module.End L (VM W 1) :=
  D.transport D.toStarLo D.toStarHi (xStar D.toHCFObj.setup)
    (fun v hv => xStar_mem (Q := D.toHCFObj.setup) (by ring) hℓ hv)

/-- `Y⋆` of the constructed module, on `V(⋆)`.  @census none (helper) -/
noncomputable def yStarV : Module.End L (VM W 1) :=
  D.transport D.toStarHi D.toStarLo (yStar D.toHCFObj.setup)
    (fun v hv => yStar_mem (Q := D.toHCFObj.setup) (by ring) hℓ hv)


end SplitEssSurjData

/-- **Step O-18a — the construction exists, `c`-free**: the engine's carrier, operators, `λ = ℓ²`,
finite generation, `C9` identifications and the ten `C13` pins, for any split `W`.
@census none (helper; route (α) core) -/
noncomputable def splitData (W : (RepNilRelSplit L).FullSubcategory) : SplitEssSurjData hℓ W where
  carrier := EssCarrier W ℓ
  weight := essWeight hℓ W
  gic := essGIC hℓ W
  admissible := fun n => essComp_finiteDimensional W n
  centralCharacter := fun _ hn => essComp_eq_bot W hn
  fg := essFG hℓ W
  isoPlus := fun _ h1 _ => essIsoPlus W (by omega) h1
  isoStar := fun _ h1 h2 _ => essIsoStar W (by omega) h1 h2
  isoMinus := fun _ h1 _ => essIsoMinus W (by omega) h1
  X_plus := fun j hj hp v hv => essPin_X_plus hℓ W j hj hp v hv
  X_star := fun j hj hj' hp v hv => essPin_X_star hℓ W j hj hj' hp v hv
  X_minus := fun j hj hp v hv => essPin_X_minus hℓ W j hj hp v hv
  X_bdry_plus := fun v hv => essPin_X_bdry_plus hℓ W v hv
  X_bdry_minus := fun v hv => essPin_X_bdry_minus hℓ W v hv
  Y_plus := fun j hj hp v hv => essPin_Y_plus hℓ W j hj hp v hv
  Y_star := fun j hj hj' hp v hv => essPin_Y_star hℓ W j hj hj' hp v hv
  Y_minus := fun j hj hp v hv => essPin_Y_minus hℓ W j hj hp v hv
  Y_bdry_plus := fun v hv => essPin_Y_bdry_plus hℓ W v hv
  Y_bdry_minus := fun v hv => essPin_Y_bdry_minus hℓ W v hv

section StarChainData

variable {hℓ} {W : (RepNilRelSplit L).FullSubcategory} (D : SplitEssSurjData hℓ W)

namespace SplitEssSurjData

/-- `M_n`'s identification with `V(⋆)` as a **plain function of `n`** (junk `0` off the middle
range or off the component).  `D.isoStar n h₁ h₂ h₃` carries `n` in its *type*, so a chain whose
index moves by `2` at every step cannot be written with it directly; with `starRead`, index
arithmetic is an ordinary `rw`.  @census none (helper) -/
noncomputable def starRead (n : ℤ) (u : D.carrier) : VM W 1 :=
  if h : (-((ℓ : ℤ) - 1) ≤ n ∧ n ≤ (ℓ : ℤ) - 1 ∧ (n - ((ℓ : ℤ) + 1)) % 2 = 0)
      ∧ u ∈ D.weight.comp n then
    D.isoStar n h.1.1 h.1.2.1 h.1.2.2 ⟨u, h.2⟩
  else 0

theorem starRead_eq {n : ℤ} (h1 : -((ℓ : ℤ) - 1) ≤ n) (h2 : n ≤ (ℓ : ℤ) - 1)
    (h3 : (n - ((ℓ : ℤ) + 1)) % 2 = 0) (u : D.carrier) (hu : u ∈ D.weight.comp n) :
    D.starRead n u = D.isoStar n h1 h2 h3 ⟨u, hu⟩ := by
  have hc : (-((ℓ : ℤ) - 1) ≤ n ∧ n ≤ (ℓ : ℤ) - 1 ∧ (n - ((ℓ : ℤ) + 1)) % 2 = 0)
      ∧ u ∈ D.weight.comp n := ⟨⟨h1, h2, h3⟩, hu⟩
  simp only [starRead, dif_pos hc]

theorem starRead_toStarLo (u : D.carrier) (hu : u ∈ D.weight.comp (-((ℓ : ℤ) - 1))) :
    D.starRead (-((ℓ : ℤ) - 1)) u = D.toStarLo ⟨u, hu⟩ :=
  D.starRead_eq le_rfl (by omega) (by omega) u hu

theorem starRead_toStarHi (u : D.carrier) (hu : u ∈ D.weight.comp ((ℓ : ℤ) - 1)) :
    D.starRead ((ℓ : ℤ) - 1) u = D.toStarHi ⟨u, hu⟩ :=
  D.starRead_eq (by omega) le_rfl (by omega) u hu

/-- **`C17`'s first display, by induction on the chain.**  `2^i X^i` carries `M_{-(ℓ-1)}` to
`M_{-(ℓ-1)+2i}` as `∏_{k=1}^{i} ξ^{(-ℓ+2k)}_{⋆,+}`, read through the `isoStar` identifications.
@census none (helper) -/
theorem xpow_chain : ∀ (i : ℕ), i + 1 ≤ ℓ → ∀ (u : D.carrier),
    u ∈ D.weight.comp (-((ℓ : ℤ) - 1)) →
    ((2 : L) ^ i) • D.starRead (-((ℓ : ℤ) - 1) + 2 * (i : ℤ))
        ((D.weight.X ^ i) u)
      = xiProd hℓ W 1 i (D.starRead (-((ℓ : ℤ) - 1)) u) := by
  have h2ne : (2 : L) ≠ 0 := two_ne_zero
  intro i
  induction i with
  | zero =>
      intro _ u hu
      rw [show (-((ℓ : ℤ) - 1) + 2 * ((0 : ℕ) : ℤ)) = -((ℓ : ℤ) - 1) by push_cast; ring]
      rw [xiProd_zero]
      simp
  | succ i ih =>
      intro hi u hu
      have hi' : i + 1 ≤ ℓ := by omega
      set j : ℤ := -(ℓ : ℤ) + 2 * ((i : ℤ) + 1) with hj
      set m : ℤ := -((ℓ : ℤ) - 1) + 2 * (i : ℤ) with hmdef
      have hjm : j - 1 = m := by rw [hj, hmdef]; ring
      have hjp : j + 1 = -((ℓ : ℤ) - 1) + 2 * (((i + 1 : ℕ)) : ℤ) := by
        rw [hj]; push_cast; ring
      set w : D.carrier := (D.weight.X ^ i) u with hw
      have hwm : w ∈ D.weight.comp m :=
        xpow_mem (Q := D.toHCFObj.setup) i hmdef.symm hu
      have hw' : w ∈ D.weight.comp (j - 1) := by rw [hjm]; exact hwm
      have hpin := D.X_star j (by push_cast; omega) (by push_cast; omega) (by rw [hj]; omega) w hw'
      have hXw : D.weight.X w ∈ D.weight.comp (j + 1) := by
        rw [hpin]; exact Submodule.coe_mem _
      have hsub : (⟨D.weight.X w, hXw⟩ : D.weight.comp (j + 1))
          = (D.isoStar (j + 1) (by omega) (by omega) (by rw [hj]; omega)).symm
              (((2 : L)⁻¹) • xiOp hℓ W 1 1 j
                (D.isoStar (j - 1) (by omega) (by omega) (by rw [hj]; omega) ⟨w, hw'⟩)) :=
        Subtype.ext hpin
      have hread : D.starRead (j + 1) (D.weight.X w)
          = ((2 : L)⁻¹) • xiOp hℓ W 1 1 j (D.starRead (j - 1) w) := by
        rw [D.starRead_eq (by omega) (by omega) (by rw [hj]; omega) _ hXw, hsub,
          LinearEquiv.apply_symm_apply,
          D.starRead_eq (n := j - 1) (by omega) (by omega) (by rw [hj]; omega) w hw']
      have hpow : (D.weight.X ^ (i + 1)) u = D.weight.X w := by
        rw [hw, pow_succ']
        rfl
      have hsc : (2 : L) ^ (i + 1) * ((2 : L)⁻¹) = (2 : L) ^ i := by
        rw [pow_succ, mul_assoc, mul_inv_cancel₀ h2ne, mul_one]
      rw [← hjp, hpow, hread, hjm, xiProd_succ, ← hj, smul_smul, hsc, ← map_smul, ih hi' u hu]
      rfl

end SplitEssSurjData

end StarChainData

section StarChainData2

variable {hℓ} {W : (RepNilRelSplit L).FullSubcategory} (D : SplitEssSurjData hℓ W)

namespace SplitEssSurjData

theorem starRead_smul {n : ℤ} (h1 : -((ℓ : ℤ) - 1) ≤ n) (h2 : n ≤ (ℓ : ℤ) - 1)
    (h3 : (n - ((ℓ : ℤ) + 1)) % 2 = 0) (c : L) (u : D.carrier)
    (hu : u ∈ D.weight.comp n) :
    D.starRead n (c • u) = c • D.starRead n u := by
  rw [D.starRead_eq h1 h2 h3 (c • u) (Submodule.smul_mem _ _ hu), D.starRead_eq h1 h2 h3 u hu,
    show (⟨c • u, Submodule.smul_mem _ c hu⟩ : D.weight.comp n)
      = c • (⟨u, hu⟩ : D.weight.comp n) from rfl, map_smul]

theorem transport_apply {n m : ℤ} {W₁ W₂ : Type} [AddCommGroup W₁] [Module L W₁]
    [AddCommGroup W₂] [Module L W₂]
    (e₁ : D.weight.comp n ≃ₗ[L] W₁)
    (e₂ : D.weight.comp m ≃ₗ[L] W₂)
    (T : Module.End L D.carrier)
    (hT : ∀ v ∈ D.weight.comp n, T v ∈ D.weight.comp m) (x : W₁) :
    D.transport e₁ e₂ T hT x
      = e₂ ⟨T ((e₁.symm x : D.weight.comp n) : D.carrier), hT _ (e₁.symm x).2⟩ := rfl

/-- **`C17`'s second display / `C18`'s first conjunct, half one**: `X⋆` is the normalized product
`∏_{k=1}^{ℓ-1} ξ^{(-ℓ+2k)}_{⋆,+}`, read on `V(⋆)`.  @census none (helper) -/
theorem xStarV_eq : D.xStarV = xStarAt hℓ W 1 := by
  have h2ne : (2 : L) ≠ 0 := two_ne_zero
  have hidx : -((ℓ : ℤ) - 1) + 2 * (((ℓ - 1 : ℕ)) : ℤ) = (ℓ : ℤ) - 1 := by
    have h : (((ℓ - 1 : ℕ)) : ℤ) = (ℓ : ℤ) - 1 := by omega
    rw [h]; ring
  ext x
  set u : D.carrier := ((D.toStarLo.symm x : D.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier)
    with hudef
  have hu : u ∈ D.weight.comp (-((ℓ : ℤ) - 1)) := (D.toStarLo.symm x).2
  have hxu : D.starRead (-((ℓ : ℤ) - 1)) u = x := by
    rw [D.starRead_toStarLo u hu]
    exact D.toStarLo.apply_symm_apply x
  have hXmem : (D.weight.X ^ (ℓ - 1)) u ∈ D.weight.comp ((ℓ : ℤ) - 1) :=
    xpow_mem (Q := D.toHCFObj.setup) (ℓ - 1) hidx hu
  have hmem : xStar D.toHCFObj.setup u ∈ D.weight.comp ((ℓ : ℤ) - 1) :=
    Submodule.smul_mem _ _ hXmem
  have hchain := D.xpow_chain (ℓ - 1) (by omega) u hu
  rw [hidx] at hchain
  have hstep : D.starRead ((ℓ : ℤ) - 1) ((D.weight.X ^ (ℓ - 1)) u)
      = (((2 : L) ^ (ℓ - 1))⁻¹) • xiProd hℓ W 1 (ℓ - 1) x := by
    rw [← hxu, ← hchain, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ h2ne), one_smul]
  have hxs : D.xStarV x = D.starRead ((ℓ : ℤ) - 1) (xStar D.toHCFObj.setup u) :=
    (D.starRead_toStarHi _ hmem).symm
  have hxu2 : xStar D.toHCFObj.setup u
      = ((gammaStarF L ℓ)⁻¹ : L) • ((D.weight.X ^ (ℓ - 1)) u) := rfl
  rw [hxs, hxu2, D.starRead_smul (by omega) le_rfl (by omega) _ _ hXmem, hstep]
  show _ = (((gammaStarF L ℓ) * (2 : L) ^ (ℓ - 1))⁻¹) • xiProd hℓ W 1 (ℓ - 1) x
  rw [smul_smul, mul_inv]


/-- **The mirror chain**: `2^i Y^i` carries `M_{ℓ-1}` to `M_{ℓ-1-2i}` as the *same* product
`∏_{k=1}^{i} ξ^{(-ℓ+2k)}_{⋆,+}` — because `ξ^{(j)}_{⋆,-} = ξ^{(-j)}_{⋆,+}` and the descending chain
meets the same `-j`.  This is the source's "symmetric definition `X|_{M_{j-1}} = Y|_{M_{1-j}}`".
@census none (helper) -/
theorem ypow_chain : ∀ (i : ℕ), i + 1 ≤ ℓ → ∀ (u : D.carrier),
    u ∈ D.weight.comp ((ℓ : ℤ) - 1) →
    ((2 : L) ^ i) • D.starRead ((ℓ : ℤ) - 1 - 2 * (i : ℤ))
        ((D.weight.Y ^ i) u)
      = xiProd hℓ W 1 i (D.starRead ((ℓ : ℤ) - 1) u) := by
  have h2ne : (2 : L) ≠ 0 := two_ne_zero
  intro i
  induction i with
  | zero =>
      intro _ u hu
      rw [show ((ℓ : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ)) = (ℓ : ℤ) - 1 by push_cast; ring]
      rw [xiProd_zero]
      simp
  | succ i ih =>
      intro hi u hu
      have hi' : i + 1 ≤ ℓ := by omega
      set j : ℤ := (ℓ : ℤ) - 2 - 2 * (i : ℤ) with hj
      set m : ℤ := (ℓ : ℤ) - 1 - 2 * (i : ℤ) with hmdef
      have hjm : j + 1 = m := by rw [hj, hmdef]; ring
      have hjp : j - 1 = (ℓ : ℤ) - 1 - 2 * (((i + 1 : ℕ)) : ℤ) := by
        rw [hj]; push_cast; ring
      have hnj : -j = -(ℓ : ℤ) + 2 * ((i : ℤ) + 1) := by rw [hj]; ring
      set w : D.carrier := (D.weight.Y ^ i) u with hw
      have hwm : w ∈ D.weight.comp m :=
        ypow_mem (Q := D.toHCFObj.setup) i hmdef.symm hu
      have hw' : w ∈ D.weight.comp (j + 1) := by rw [hjm]; exact hwm
      have hpin := D.Y_star j (by push_cast; omega) (by push_cast; omega) (by rw [hj]; omega) w hw'
      have hYw : D.weight.Y w ∈ D.weight.comp (j - 1) := by
        rw [hpin]; exact Submodule.coe_mem _
      have hsub : (⟨D.weight.Y w, hYw⟩ : D.weight.comp (j - 1))
          = (D.isoStar (j - 1) (by omega) (by omega) (by rw [hj]; omega)).symm
              (((2 : L)⁻¹) • xiOp hℓ W 1 (-1) j
                (D.isoStar (j + 1) (by omega) (by omega) (by rw [hj]; omega) ⟨w, hw'⟩)) :=
        Subtype.ext hpin
      have hread : D.starRead (j - 1) (D.weight.Y w)
          = ((2 : L)⁻¹) • xiOp hℓ W 1 (-1) j (D.starRead (j + 1) w) := by
        rw [D.starRead_eq (by omega) (by omega) (by rw [hj]; omega) _ hYw, hsub,
          LinearEquiv.apply_symm_apply,
          D.starRead_eq (n := j + 1) (by omega) (by omega) (by rw [hj]; omega) w hw']
      have hpow : (D.weight.Y ^ (i + 1)) u = D.weight.Y w := by
        rw [hw, pow_succ']
        rfl
      have hsc : (2 : L) ^ (i + 1) * ((2 : L)⁻¹) = (2 : L) ^ i := by
        rw [pow_succ, mul_assoc, mul_inv_cancel₀ h2ne, mul_one]
      rw [← hjp, hpow, hread, hjm, xiProd_succ, xiOp_neg_one, hnj, smul_smul, hsc, ← map_smul,
        ih hi' u hu]
      rfl

/-- **`C18`'s first conjunct, half two**: `Y⋆` is the same normalized product as `X⋆`.
@census none (helper) -/
theorem yStarV_eq : D.yStarV = xStarAt hℓ W 1 := by
  have h2ne : (2 : L) ≠ 0 := two_ne_zero
  have hidx : (ℓ : ℤ) - 1 - 2 * (((ℓ - 1 : ℕ)) : ℤ) = -((ℓ : ℤ) - 1) := by
    have h : (((ℓ - 1 : ℕ)) : ℤ) = (ℓ : ℤ) - 1 := by omega
    rw [h]; ring
  ext x
  set u : D.carrier := ((D.toStarHi.symm x : D.weight.comp ((ℓ : ℤ) - 1)) : D.carrier)
    with hudef
  have hu : u ∈ D.weight.comp ((ℓ : ℤ) - 1) := (D.toStarHi.symm x).2
  have hxu : D.starRead ((ℓ : ℤ) - 1) u = x := by
    rw [D.starRead_toStarHi u hu]
    exact D.toStarHi.apply_symm_apply x
  have hYmem : (D.weight.Y ^ (ℓ - 1)) u ∈ D.weight.comp (-((ℓ : ℤ) - 1)) :=
    ypow_mem (Q := D.toHCFObj.setup) (ℓ - 1) hidx hu
  have hmem : yStar D.toHCFObj.setup u ∈ D.weight.comp (-((ℓ : ℤ) - 1)) :=
    Submodule.smul_mem _ _ hYmem
  have hchain := D.ypow_chain (ℓ - 1) (by omega) u hu
  rw [hidx] at hchain
  have hstep : D.starRead (-((ℓ : ℤ) - 1)) ((D.weight.Y ^ (ℓ - 1)) u)
      = (((2 : L) ^ (ℓ - 1))⁻¹) • xiProd hℓ W 1 (ℓ - 1) x := by
    rw [← hxu, ← hchain, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ h2ne), one_smul]
  have hys : D.yStarV x = D.starRead (-((ℓ : ℤ) - 1)) (yStar D.toHCFObj.setup u) :=
    (D.starRead_toStarLo _ hmem).symm
  have hyu2 : yStar D.toHCFObj.setup u
      = ((gammaStarF L ℓ)⁻¹ : L) • ((D.weight.Y ^ (ℓ - 1)) u) := rfl
  rw [hys, hyu2, D.starRead_smul le_rfl (by omega) (by omega) _ _ hYmem, hstep]
  show _ = (((gammaStarF L ℓ) * (2 : L) ^ (ℓ - 1))⁻¹) • xiProd hℓ W 1 (ℓ - 1) x
  rw [smul_smul, mul_inv]

/-- **`C18`, first conjunct**: `X⋆ = Y⋆` on `V(⋆)`.  @census none (helper) -/
theorem xStarV_eq_yStarV : D.xStarV = D.yStarV := by
  rw [D.xStarV_eq, D.yStarV_eq]

end SplitEssSurjData

end StarChainData2

/-- `2^{ℓ-1}X^{ℓ-1}|_{M_{-(ℓ-1)}}` **is** the product of `C17`'s display, at the `transport` level
the clause states it.  @census none (helper) -/
theorem transport_two_pow_xpow (W : (RepNilRelSplit L).FullSubcategory) (D : SplitEssSurjData hℓ W) :
    D.transport D.toStarLo D.toStarHi
        (((2 : L) ^ (ℓ - 1)) • D.weight.X ^ (ℓ - 1))
        (fun v hv => Submodule.smul_mem _ _ (xpow_maps D.toHCFObj.setup hℓ v hv))
      = xiProd hℓ W 1 (ℓ - 1) := by
  have hidx : -((ℓ : ℤ) - 1) + 2 * (((ℓ - 1 : ℕ)) : ℤ) = (ℓ : ℤ) - 1 := by
    have h : (((ℓ - 1 : ℕ)) : ℤ) = (ℓ : ℤ) - 1 := by omega
    rw [h]; ring
  ext x
  set u : D.carrier := ((D.toStarLo.symm x : D.weight.comp (-((ℓ : ℤ) - 1))) : D.carrier)
    with hudef
  have hu : u ∈ D.weight.comp (-((ℓ : ℤ) - 1)) := (D.toStarLo.symm x).2
  have hxu : D.starRead (-((ℓ : ℤ) - 1)) u = x := by
    rw [D.starRead_toStarLo u hu]
    exact D.toStarLo.apply_symm_apply x
  have hXmem : (D.weight.X ^ (ℓ - 1)) u ∈ D.weight.comp ((ℓ : ℤ) - 1) :=
    xpow_mem (Q := D.toHCFObj.setup) (ℓ - 1) hidx hu
  have hchain := D.xpow_chain (ℓ - 1) (by omega) u hu
  rw [hidx] at hchain
  have hmem : (((2 : L) ^ (ℓ - 1)) • D.weight.X ^ (ℓ - 1)) u
      ∈ D.weight.comp ((ℓ : ℤ) - 1) := Submodule.smul_mem _ _ hXmem
  have hlhs : D.transport D.toStarLo D.toStarHi
      (((2 : L) ^ (ℓ - 1)) • D.weight.X ^ (ℓ - 1))
      (fun v hv => Submodule.smul_mem _ _ (xpow_maps D.toHCFObj.setup hℓ v hv)) x
      = D.starRead ((ℓ : ℤ) - 1)
          ((((2 : L) ^ (ℓ - 1)) • D.weight.X ^ (ℓ - 1)) u) :=
    (D.starRead_toStarHi _ hmem).symm
  rw [hlhs]
  show D.starRead ((ℓ : ℤ) - 1)
      (((2 : L) ^ (ℓ - 1)) • ((D.weight.X ^ (ℓ - 1)) u)) = _
  rw [D.starRead_smul (by omega) le_rfl (by omega) _ _ hXmem, hchain, hxu]

/-- **`RQ-5.05-C17`** — the two displays of the source's first paragraph, for any `D`.
The scalar `γ̃ = ∏_{k=1}^{ℓ-1}2k = 2^{ℓ-1}(ℓ-1)!` is positive, and after the `X_⋆ = γ_⋆^{-1}X^{ℓ-1}`
normalization the second display's `γ̃' ∈ ℚ^×` is exactly `1`.  @census none (helper) -/
theorem essSurj_C17 (W : (RepNilRelSplit L).FullSubcategory) (D : SplitEssSurjData hℓ W) :
    (∃ (γ : ℚ) (n : Module.End L (VM W 1)), 0 < γ ∧ IsNilpotent n ∧
        Commute n (phiOp ℓ W 1) ∧
        D.transport D.toStarLo D.toStarHi
            ((2 : L) ^ (ℓ - 1) • D.weight.X ^ (ℓ - 1))
            (fun v hv => Submodule.smul_mem _ _ (xpow_maps D.toHCFObj.setup hℓ v hv))
          = (algebraMap ℚ L γ) • 1 + n) ∧
      (∃ (γ' : ℚ) (n : Module.End L (VM W 1)), γ' ≠ 0 ∧ IsNilpotent n ∧
        D.xStarV = (algebraMap ℚ L γ') • (1 + n)) := by
  obtain ⟨n, hn, hc, hsplit⟩ := xiProd_split hℓ W 1 (ℓ - 1)
  obtain ⟨n', hn', -, heq⟩ := xStarAt_eq_one_add hℓ W 1
  refine ⟨⟨prodCoeff (ℓ - 1), n, prodCoeff_pos _, hn, ?_, ?_⟩,
    ⟨1, n', one_ne_zero, hn', ?_⟩⟩
  · have h2 : Commute n (sqrtPhi hℓ W 1 ^ 2) := hc.pow_right 2
    rwa [sqrtPhi_sq] at h2
  · rw [transport_two_pow_xpow]; exact hsplit
  · rw [D.xStarV_eq, heq, map_one, one_smul]


/-! ### `RQ-5.05-C17`: `X_⋆` is a polynomial in `n_⋆` with constant term `1`

The tex: `2^{ℓ-1}X^{ℓ-1}|_{M_{-(ℓ-1)}} = ∏ ξ^{(j)}_{⋆,+} = γ̃·1 + ñ`, `γ̃ = 2^{ℓ-1}(ℓ-1)!`, so
`X_⋆ = 1 + ñ_⋆`, and `X_⋆` is a polynomial in `n_⋆`.  Polynomiality: every `ξ^{(j)} = φ_⋆^{1/2} + j`
and `φ_⋆^{1/2}` is computed by the Newton iteration `sqrtSeq`, whose steps stay in the subalgebra
`L[n_⋆]` because the inverse of a unipotent element of a subalgebra is in the subalgebra (a finite
geometric series); `Algebra.adjoin_singleton_eq_range_aeval` supplies `p`.  The constant term:
`X_⋆ = 1 + ñ_⋆` (`xStarAt_eq_one_add`, i.e. `γ̃ = 2^{ℓ-1}γ_⋆`) with `ñ_⋆` and `p(n_⋆) − p(0)` both
nilpotent forces `p(0) = 1` (on `V(⋆) ≠ 0`; on `V(⋆) = 0` the representative is adjusted). -/

section Poly

variable {U : Type} [AddCommGroup U] [Module L U]

omit [CharZero L] in
/-- The inverse of a unipotent element of a subalgebra of `End(U)` lies in the subalgebra.
@census none (helper; C17) -/
theorem ringInverse_mem_of_unipotent (S : Subalgebra L (Module.End L U)) {u : Module.End L U}
    (hu : u ∈ S) (hn : IsNilpotent (u - 1)) : Ring.inverse u ∈ S := by
  obtain ⟨e, he⟩ := hn
  set m : Module.End L U := u - 1 with hmdef
  have hm : m ∈ S := S.sub_mem hu S.one_mem
  set v : Module.End L U := ∑ i ∈ Finset.range e, (-m) ^ i with hvdef
  have hv : v ∈ S := S.sum_mem fun i _ => S.pow_mem (S.neg_mem hm) i
  have hneg : (-m) ^ e = 0 := by rw [neg_pow, he, mul_zero]
  have hu1 : (1 : Module.End L U) - -m = u := by rw [hmdef]; abel
  have h1 : u * v = 1 := by
    have h := mul_neg_geom_sum (-m) e
    rw [hneg, sub_zero, hu1] at h
    exact h
  have h2 : v * u = 1 := by
    have h := geom_sum_mul_neg (-m) e
    rw [hneg, sub_zero, hu1] at h
    exact h
  have hinv : Ring.inverse u = v := Ring.inverse_unit (⟨u, v, h1, h2⟩ : (Module.End L U)ˣ)
  rw [hinv]
  exact hv

/-- The Newton iteration of `prop:unipotentsquareroots` stays in any subalgebra containing `φ`.
@census none (helper; C17) -/
theorem sqrtSeq_mem (h2 : (2 : L) ≠ 0) (S : Subalgebra L (Module.End L U)) {φ : Module.End L U}
    (hφ : φ ∈ S) (hn : IsNilpotent (φ - 1)) : ∀ k, sqrtSeq h2 φ k ∈ S
  | 0 => hφ
  | k + 1 => by
      rw [sqrtSeq_succ]
      exact S.smul_mem (S.add_mem (sqrtSeq_mem h2 S hφ hn k)
        (S.mul_mem (ringInverse_mem_of_unipotent S (sqrtSeq_mem h2 S hφ hn k)
          (sqrtSeq_isNilpotent_sub_one h2 hn k)) hφ)) _

/-- @census none (helper; C17) -/
theorem sqrt_mem (h2 : (2 : L) ≠ 0) (S : Subalgebra L (Module.End L U)) {φ : Module.End L U}
    (hφ : φ ∈ S) : Unipotent.sqrt h2 φ ∈ S := by
  rw [Unipotent.sqrt]
  split
  · next h => exact sqrtSeq_mem h2 S hφ h _
  · exact S.zero_mem

/-- `def:squareroots` stays in any subalgebra containing `φ`.  @census none (helper; C17) -/
theorem sqrtOfScalarPlusNilpotent_mem (h2 : (2 : L) ≠ 0) (γ : Lˣ)
    (S : Subalgebra L (Module.End L U)) {φ : Module.End L U} (hφ : φ ∈ S) :
    sqrtOfScalarPlusNilpotent h2 γ φ ∈ S :=
  S.smul_mem (sqrt_mem h2 S (S.smul_mem hφ _)) _

omit [CharZero L] in
/-- Polynomials in one endomorphism commute.  @census none (helper; C17) -/
theorem commute_aeval (n : Module.End L U) (f g : L[X]) :
    Commute (Polynomial.aeval n f) (Polynomial.aeval n g) := by
  show _ * _ = _ * _
  rw [← map_mul, ← map_mul, mul_comm]

omit [CharZero L] in
/-- **Intertwining passes to polynomials**: `f x = y f` implies `f p(x) = p(y) f`.
@census none (helper; the intertwiners) -/
theorem intertwine_aeval {U₂ : Type} [AddCommGroup U₂] [Module L U₂] (f : U →ₗ[L] U₂)
    (x : Module.End L U) (y : Module.End L U₂) (h : ∀ v, f (x v) = y (f v)) (p : L[X]) :
    ∀ v, f (Polynomial.aeval x p v) = Polynomial.aeval y p (f v) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a v
    simp only [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply, map_smul]
  · intro p q hp hq v
    simp only [map_add, LinearMap.add_apply, hp, hq]
  · intro k a ih v
    rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval x) (Polynomial.C a * Polynomial.X ^ k),
      map_mul (Polynomial.aeval y) (Polynomial.C a * Polynomial.X ^ k), Module.End.mul_apply,
      Module.End.mul_apply, Polynomial.aeval_X, Polynomial.aeval_X, ih, h]

end Poly

section XStarPoly

variable (W : (RepNilRelSplit L).FullSubcategory)

/-- `L[n_⋆]`.  @census none (helper; C17) -/
noncomputable abbrev starAlg : Subalgebra L (Module.End L (VM W 1)) := Algebra.adjoin L {nOp W 1}

theorem nStar_mem : nOp W 1 ∈ starAlg W := Algebra.subset_adjoin rfl

theorem phiOp_star_mem : phiOp ℓ W 1 ∈ starAlg W :=
  (starAlg W).add_mem ((starAlg W).smul_mem (starAlg W).one_mem _)
    ((starAlg W).smul_mem (nStar_mem W) _)

theorem sqrtPhi_star_mem : sqrtPhi hℓ W 1 ∈ starAlg W :=
  sqrtOfScalarPlusNilpotent_mem two_ne_zero _ _ (phiOp_star_mem W)

theorem xiOp_star_mem (s j : ℤ) : xiOp hℓ W 1 s j ∈ starAlg W :=
  (starAlg W).add_mem (sqrtPhi_star_mem hℓ W) ((starAlg W).smul_mem (starAlg W).one_mem _)

theorem xiProd_star_mem : ∀ i, xiProd hℓ W 1 i ∈ starAlg W
  | 0 => (starAlg W).one_mem
  | i + 1 => (starAlg W).mul_mem (xiOp_star_mem hℓ W _ _) (xiProd_star_mem i)

theorem xStarAt_star_mem : xStarAt hℓ W 1 ∈ starAlg W :=
  (starAlg W).smul_mem (xiProd_star_mem hℓ W _) _

/-- **`C17`, on the vertex operators**: the normalized product `X_⋆ = (γ_⋆2^{ℓ-1})^{-1}∏ξ^{(j)}_{⋆,+}`
is `p(n_⋆)` for a polynomial `p` with `p(0) = 1`.  @census none (helper; C17) -/
theorem xStarAt_eq_poly :
    ∃ p : L[X], Polynomial.aeval (nOp W 1) p = xStarAt hℓ W 1 ∧ p.coeff 0 = 1 := by
  have hmem := xStarAt_star_mem hℓ W
  rw [starAlg, Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨p, hp⟩ := hmem
  change Polynomial.aeval (nOp W 1) p = xStarAt hℓ W 1 at hp
  set n := nOp W 1 with hndef
  set c : L := 1 - p.coeff 0 with hcdef
  -- `p(n_⋆) = p(0)·1 + q(n_⋆)n_⋆`
  have hsplit : Polynomial.aeval n p
      = Polynomial.aeval n (Polynomial.divX p * Polynomial.X) + (p.coeff 0) • 1 := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add p]
    rw [map_add, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  obtain ⟨N, hN, -, hX⟩ := xStarAt_eq_one_add hℓ W 1
  have hNeq : N = Polynomial.aeval n (p - 1) := by
    rw [map_sub, map_one, hp, hX]; abel
  have hanil : IsNilpotent (Polynomial.aeval n (Polynomial.divX p * Polynomial.X)) := by
    rw [map_mul, Polynomial.aeval_X]
    exact Commute.isNilpotent_mul_left
      (by simpa [Polynomial.aeval_X] using commute_aeval n (Polynomial.divX p) Polynomial.X)
      (isNilpotent_nOp W 1)
  have hc : c • (1 : Module.End L (VM W 1))
      = Polynomial.aeval n (Polynomial.divX p * Polynomial.X) - N := by
    rw [hcdef, sub_smul, one_smul, hNeq, map_sub, map_one, hsplit]; abel
  have hcnil : IsNilpotent (c • (1 : Module.End L (VM W 1))) := by
    rw [hc]
    refine Commute.isNilpotent_sub ?_ hanil hN
    rw [hNeq]; exact commute_aeval n _ _
  have hc0 : c • (1 : Module.End L (VM W 1)) = 0 := by
    by_cases hc' : c = 0
    · rw [hc', zero_smul]
    · obtain ⟨k, hk⟩ := hcnil
      rw [smul_pow, one_pow] at hk
      have h1 : (1 : Module.End L (VM W 1)) = 0 := by
        have := congrArg (fun z => (c ^ k)⁻¹ • z) hk
        simpa [smul_smul, inv_mul_cancel₀ (pow_ne_zero k hc')] using this
      rw [h1, smul_zero]
  refine ⟨p + Polynomial.C c, ?_, ?_⟩
  · rw [map_add, hp, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, hc0, add_zero]
  · rw [Polynomial.coeff_add, Polynomial.coeff_C_zero, hcdef]; ring

variable {hℓ W}

/-- **`Split.xStar_eq_poly` — `RQ-5.05-C17`** (sole claimant, B-9): for the `c`-free construction
`D` over `W`, `X_⋆` read on `V(⋆)` is `p(n_⋆)` for a polynomial `p ∈ L[T]` with `p(0) = 1`.
@census none (helper; clause RQ2-5.02-C4, v1 RQ-5.05-C17)
@clauses   RQ2-5.02-S-O7h -/
theorem xStar_eq_poly (D : SplitEssSurjData hℓ W) :
    ∃ p : L[X], Polynomial.aeval (nOp W 1) p = D.xStarV ∧ p.coeff 0 = 1 := by
  rw [D.xStarV_eq]
  exact xStarAt_eq_poly hℓ W

end XStarPoly

/-! ### The two intertwiners (Step O-7h) -/

section Intertwine

variable (W : (RepNilRelSplit L).FullSubcategory)

/-- `φ_{b₊} n_⋆ = n_+ φ_{b₊}`.  @census none (helper; O-7h) -/
theorem edgeBp_nStar (v : VM W 1) :
    essEdgeBp W (nOp W 1 v) = nOp W 2 (essEdgeBp W v) := by
  rw [nOp_star_eq_nStarPlus]; rfl

/-- `n_⋆ φ_{a₊} = φ_{a₊} n_+`.  @census none (helper; O-7h) -/
theorem nStar_edgeAp (v : VM W 2) :
    essEdgeAp W (nOp W 2 v) = nOp W 1 (essEdgeAp W v) := by
  rw [nOp_star_eq_nStarPlus]; rfl

/-- **`Split.intertwine_bPlus`**: `φ_{b₊} ∘ p(n_⋆) = p(n_+) ∘ φ_{b₊}`.  @census none (helper; O-7h) -/
theorem intertwine_bPlus (p : L[X]) :
    essEdgeBp W ∘ₗ Polynomial.aeval (nOp W 1) p = Polynomial.aeval (nOp W 2) p ∘ₗ essEdgeBp W :=
  LinearMap.ext (intertwine_aeval (essEdgeBp W) _ _ (edgeBp_nStar W) p)

/-- **`Split.intertwine_aPlus`**: `p(n_⋆) ∘ φ_{a₊} = φ_{a₊} ∘ p(n_+)`.  @census none (helper; O-7h) -/
theorem intertwine_aPlus (p : L[X]) :
    Polynomial.aeval (nOp W 1) p ∘ₗ essEdgeAp W = essEdgeAp W ∘ₗ Polynomial.aeval (nOp W 2) p :=
  (LinearMap.ext (intertwine_aeval (essEdgeAp W) _ _ (nStar_edgeAp W) p)).symm

/-- `p(n_+)` is unipotent, hence a unit, when `p(0) = 1`.  @census none (helper; O-7h) -/
theorem isUnit_aeval_nPlus {p : L[X]} (h0 : p.coeff 0 = 1) :
    IsUnit (Polynomial.aeval (nOp W 2) p) := by
  have hsplit : Polynomial.aeval (nOp W 2) p
      = 1 + Polynomial.aeval (nOp W 2) (Polynomial.divX p * Polynomial.X) := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add p]
    rw [map_add, Polynomial.aeval_C, h0, map_one, add_comm]
  rw [hsplit]
  refine isUnit_one_add_of_isNilpotent ?_
  rw [map_mul, Polynomial.aeval_X]
  exact Commute.isNilpotent_mul_left
    (by simpa [Polynomial.aeval_X] using commute_aeval (nOp W 2) (Polynomial.divX p) Polynomial.X)
    (isNilpotent_nOp W 2)

end Intertwine

/-! ### The isomorphism `(1_{V(−)}, 1_{V(⋆)}, p(n_+)^{−1}) : 𝔼_L(M) ≅ W` and `Split.essSurj`

Stated for **any** `p` with `p(n_⋆) = X_⋆` and `p(0) = 1` (B-13); the components are the `C9`
identifications at `−` and `⋆` and `p(n_+)^{-1}` after the identification at `+`. -/

section Iso

variable {hℓ} {W : (RepNilRelSplit L).FullSubcategory} (D : SplitEssSurjData hℓ W)

/-- `p(n_+)^{-1}`.  @census none (helper; O-7h) -/
noncomputable def nPlusInv (p : L[X]) : Module.End L (VM W 2) :=
  Ring.inverse (Polynomial.aeval (nOp W 2) p)

/-- The vertex components `(1, 1, p(n_+)^{-1})`, read through the `C9` identifications.
@census none (helper; O-7h, the pin of `isoPoly`) -/
noncomputable def isoPolyψ (p : L[X]) :
    ∀ v : Fin 3, V3 D.toHCFObj.setup v →ₗ[L] VM W v
  | 0 => D.toMinus.toLinearMap
  | 1 => D.toStarLo.toLinearMap
  | 2 => nPlusInv p ∘ₗ D.toPlus.toLinearMap

/-- The inverse components `(1, 1, p(n_+))`.  @census none (helper; O-7h) -/
noncomputable def isoPolyψInv (p : L[X]) :
    ∀ v : Fin 3, VM W v →ₗ[L] V3 D.toHCFObj.setup v
  | 0 => D.toMinus.symm.toLinearMap
  | 1 => D.toStarLo.symm.toLinearMap
  | 2 => D.toPlus.symm.toLinearMap ∘ₗ Polynomial.aeval (nOp W 2) p

/-- **The pin of `isoPoly`**: its components are `1`, `1` and `p(n_+)^{-1}`.
@census none (helper; O-7h) -/
theorem isoPolyψ_spec (p : L[X]) :
    (∀ m, isoPolyψ D p 0 m = D.toMinus m) ∧ (∀ m, isoPolyψ D p 1 m = D.toStarLo m) ∧
      (∀ m, isoPolyψ D p 2 m = Ring.inverse (Polynomial.aeval (nOp W 2) p) (D.toPlus m)) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

variable {p : L[X]} (hp : Polynomial.aeval (nOp W 1) p = D.xStarV) (h0 : p.coeff 0 = 1)

include hp in
/-- `X_⋆` read on `V(⋆)` is injective.  @census none (helper; O-7h) -/
theorem aeval_nStar_injective : Function.Injective (Polynomial.aeval (nOp W 1) p) := by
  have hu : IsUnit (Polynomial.aeval (nOp W 1) p) := by
    rw [hp, D.xStarV_eq]; exact isUnit_xStarAt hℓ W 1
  exact ((Module.End.isUnit_iff _).1 hu).injective

/-- `xStarV` evaluated on an identified element.  @census none (helper; O-7h) -/
theorem xStarV_toStarLo (u : D.weight.comp (-((ℓ : ℤ) - 1))) :
    D.xStarV (D.toStarLo u)
      = D.toStarHi ⟨xStar D.toHCFObj.setup u, xStar_mem (Q := D.toHCFObj.setup) (by ring) hℓ u.2⟩ := by
  show D.toStarHi ⟨xStar D.toHCFObj.setup ((D.toStarLo.symm (D.toStarLo u) : D.weight.comp _) :
      D.carrier), _⟩ = _
  simp only [LinearEquiv.symm_apply_apply]

/-- Edge `a₋`.  @census none (helper; O-7h) -/
theorem isoPoly_edge0 (m : D.weight.comp (-((ℓ : ℤ) + 1))) (hm : D.weight.X m ∈ D.weight.comp (-((ℓ : ℤ) - 1))) :
    D.toStarLo ⟨D.weight.X m, hm⟩ = Vedge W 0 (D.toMinus m) := by
  have h : (⟨D.weight.X m, hm⟩ : D.weight.comp (-((ℓ : ℤ) - 1)))
      = D.toStarLo.symm (Vedge W 0 (D.toMinus m)) := Subtype.ext (D.X_bdry_minus m m.2)
  rw [h]; exact D.toStarLo.apply_symm_apply _

/-- Edge `b₋`.  @census none (helper; O-7h) -/
theorem isoPoly_edge1 (m : D.weight.comp (-((ℓ : ℤ) - 1))) (hm : D.weight.Y m ∈ D.weight.comp (-((ℓ : ℤ) + 1))) :
    D.toMinus ⟨D.weight.Y m, hm⟩ = Vedge W 1 (D.toStarLo m) := by
  have h : (⟨D.weight.Y m, hm⟩ : D.weight.comp (-((ℓ : ℤ) + 1)))
      = D.toMinus.symm (Vedge W 1 (D.toStarLo m)) := Subtype.ext (D.Y_bdry_minus m m.2)
  rw [h]; exact D.toMinus.apply_symm_apply _

include hp h0 in
/-- Edge `b₊`: `p(n_+)^{-1} φ_{b₊}^{𝔼} = φ_{b₊}`, by the intertwiner `φ_{b₊}p(n_⋆) = p(n_+)φ_{b₊}`.
@census none (helper; O-7h) -/
theorem isoPoly_edge3 (m : D.weight.comp (-((ℓ : ℤ) - 1)))
    (hm : D.weight.X (xStar D.toHCFObj.setup m) ∈ D.weight.comp ((ℓ : ℤ) + 1)) :
    nPlusInv p (D.toPlus ⟨D.weight.X (xStar D.toHCFObj.setup m), hm⟩) = Vedge W 3 (D.toStarLo m) := by
  have hw : xStar D.toHCFObj.setup m ∈ D.weight.comp ((ℓ : ℤ) - 1) :=
    xStar_mem (Q := D.toHCFObj.setup) (by ring) hℓ m.2
  have h1 : (⟨D.weight.X (xStar D.toHCFObj.setup m), hm⟩ : D.weight.comp ((ℓ : ℤ) + 1))
      = D.toPlus.symm (Vedge W 3 (D.toStarHi ⟨_, hw⟩)) :=
    Subtype.ext (D.X_bdry_plus _ hw)
  have h2 : D.toStarHi ⟨_, hw⟩ = Polynomial.aeval (nOp W 1) p (D.toStarLo m) := by
    rw [hp, xStarV_toStarLo D]
  have h3 : Vedge W 3 (Polynomial.aeval (nOp W 1) p (D.toStarLo m))
      = Polynomial.aeval (nOp W 2) p (Vedge W 3 (D.toStarLo m)) :=
    LinearMap.congr_fun (intertwine_bPlus W p) (D.toStarLo m)
  rw [h1]; erw [D.toPlus.apply_symm_apply]; rw [h2, h3, nPlusInv]
  exact LinearMap.congr_fun (Ring.inverse_mul_cancel _ (isUnit_aeval_nPlus W h0))
    (Vedge W 3 (D.toStarLo m))

include hp h0 in
/-- Edge `a₊`: `X_⋆^{-1}φ_{a₊} = φ_{a₊}p(n_+)^{-1}`, by the intertwiner
`p(n_⋆)φ_{a₊} = φ_{a₊}p(n_+)` and injectivity of `p(n_⋆) = X_⋆`.  @census none (helper; O-7h) -/
theorem isoPoly_edge2 (m : D.weight.comp ((ℓ : ℤ) + 1))
    (hm : (D.toHCFObj.setup.starInverses hℓ).xStarInv (D.weight.Y m) ∈ D.weight.comp (-((ℓ : ℤ) - 1))) :
    D.toStarLo ⟨(D.toHCFObj.setup.starInverses hℓ).xStarInv (D.weight.Y m), hm⟩
      = Vedge W 2 (nPlusInv p (D.toPlus m)) := by
  have hY : D.weight.Y m ∈ D.weight.comp ((ℓ : ℤ) - 1) :=
    y_mem (Q := D.toHCFObj.setup) (m := (ℓ : ℤ) + 1) (by ring) m.2
  refine aeval_nStar_injective D hp ?_
  have hL : Polynomial.aeval (nOp W 1) p
      (D.toStarLo ⟨(D.toHCFObj.setup.starInverses hℓ).xStarInv (D.weight.Y m), hm⟩)
      = Vedge W 2 (D.toPlus m) := by
    rw [hp, xStarV_toStarLo D]
    have hx : (⟨xStar D.toHCFObj.setup
          ((D.toHCFObj.setup.starInverses hℓ).xStarInv (D.weight.Y m)),
          xStar_mem (Q := D.toHCFObj.setup) (by ring) hℓ hm⟩ :
          D.weight.comp ((ℓ : ℤ) - 1)) = ⟨D.weight.Y m, hY⟩ :=
      Subtype.ext (xStar_xStarInv D.toHCFObj.setup (D.toHCFObj.setup.starInverses hℓ) _ hY)
    rw [hx]
    have h : (⟨D.weight.Y m, hY⟩ : D.weight.comp ((ℓ : ℤ) - 1))
        = D.toStarHi.symm (Vedge W 2 (D.toPlus m)) := Subtype.ext (D.Y_bdry_plus m m.2)
    rw [h]; exact D.toStarHi.apply_symm_apply _
  have hR : Polynomial.aeval (nOp W 1) p (Vedge W 2 (nPlusInv p (D.toPlus m)))
      = Vedge W 2 (D.toPlus m) := by
    have h : essEdgeAp W (Polynomial.aeval (nOp W 2) p (nPlusInv p (D.toPlus m)))
        = Polynomial.aeval (nOp W 1) p (essEdgeAp W (nPlusInv p (D.toPlus m))) :=
      (LinearMap.congr_fun (intertwine_aPlus W p) (nPlusInv p (D.toPlus m))).symm
    change Polynomial.aeval (nOp W 1) p (essEdgeAp W (nPlusInv p (D.toPlus m)))
      = essEdgeAp W (D.toPlus m)
    rw [← h, nPlusInv, ← Module.End.mul_apply,
      Ring.mul_inverse_cancel _ (isUnit_aeval_nPlus W h0), Module.End.one_apply]
  rw [hL, hR]

include hp h0 in
/-- The four edge squares.  @census none (helper; O-7h) -/
theorem isoPoly_edge : ∀ (e : Fin 4) (m : V3 D.toHCFObj.setup (RQuiver.gelfand.source e)),
    isoPolyψ D p (RQuiver.gelfand.target e)
        (E_F_edge D.toHCFObj.setup (D.toHCFObj.setup.starInverses hℓ) hℓ e m)
      = Vedge W e (isoPolyψ D p (RQuiver.gelfand.source e) m)
  | 0, m => isoPoly_edge0 D m _
  | 1, m => isoPoly_edge1 D m _
  | 2, m => isoPoly_edge2 D hp h0 m _
  | 3, m => isoPoly_edge3 D hp h0 m _

include hp h0 in
/-- The comparison morphism `𝔼_L(M) → W`.  @census none (helper; O-7h) -/
noncomputable def isoPolyHom :
    RationalQuiver.Rep.Hom (E_F_rep D.toHCFObj.setup (D.toHCFObj.setup.starInverses hℓ) hℓ)
      W.obj.toRep where
  ψ := isoPolyψ D p
  edge e m := isoPoly_edge D hp h0 e m
  rational σ v m := by
    have hσ : σ = 1 := galSelf_eq_one σ
    subst hσ
    refine sp_rational_of_phi'
      (M := E_F_rep D.toHCFObj.setup (D.toHCFObj.setup.starInverses hℓ) hℓ) (N := W.obj.toRep)
      (fun u => isoPolyψ D p u) (one_smul _ v) m ?_
    rw [RationalQuiver.Rep.φ'_one, RationalQuiver.Rep.φ'_one]
    exact RationalQuiver.Rep.eqCast_natural
      (M := E_F_rep D.toHCFObj.setup (D.toHCFObj.setup.starInverses hℓ) hℓ) (N := W.obj.toRep)
      (fun u => isoPolyψ D p u) _ m

include h0 in
theorem isoPoly_left : ∀ (v : Fin 3) x, isoPolyψInv D p v (isoPolyψ D p v x) = x
  | 0, x => D.toMinus.symm_apply_apply x
  | 1, x => D.toStarLo.symm_apply_apply x
  | 2, x => by
      show D.toPlus.symm (Polynomial.aeval (nOp W 2) p (nPlusInv p (D.toPlus x))) = x
      rw [nPlusInv, ← Module.End.mul_apply, Ring.mul_inverse_cancel _ (isUnit_aeval_nPlus W h0),
        Module.End.one_apply]
      exact D.toPlus.symm_apply_apply x

include h0 in
theorem isoPoly_right : ∀ (v : Fin 3) y, isoPolyψ D p v (isoPolyψInv D p v y) = y
  | 0, y => D.toMinus.apply_symm_apply y
  | 1, y => D.toStarLo.apply_symm_apply y
  | 2, y => by
      show nPlusInv p (D.toPlus (D.toPlus.symm (Polynomial.aeval (nOp W 2) p y))) = y
      rw [LinearEquiv.apply_symm_apply, nPlusInv, ← Module.End.mul_apply,
        Ring.inverse_mul_cancel _ (isUnit_aeval_nPlus W h0), Module.End.one_apply]

/-- `𝔼_L(M) ≅ W` in `FDRep`, components `(1, 1, p(n_+)^{-1})`.  @census none (helper; O-7h) -/
noncomputable def isoPolyFD : E_F_obj ℓ hℓ D.toHCFObj ≅ W.obj where
  hom := isoPolyHom D hp h0
  inv := spRepHomInv (isoPolyHom D hp h0) (isoPolyψInv D p) (isoPoly_left D h0) (isoPoly_right D h0)
  hom_inv_id := RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun x =>
    isoPoly_left D h0 v x)
  inv_hom_id := RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun y =>
    isoPoly_right D h0 v y)

/-- **`Split.isoPoly`** (Step O-7h): for **any** polynomial `p` with `p(n_⋆) = X_⋆` and `p(0) = 1`,
`(1_{V(−)}, 1_{V(⋆)}, p(n_+)^{-1})` is an isomorphism `𝔼_L(M) ≅ W` in `Rep^nil` with the relation.
@census none (helper; O-7h) -/
noncomputable def isoPoly : (E_FNil (F := L) ℓ hℓ).obj D.toHCFObj ≅ W :=
  ObjectProperty.isoMk (RepNilRelSplit L) (isoPolyFD D hp h0)

end Iso

variable (ℓ) in
/-- **`Split.essSurj`** — `prop:splitequivalence`'s essential surjectivity by the tex's route:
the `c`-free construction, `C17` (`xStar_eq_poly`, `p` chosen by `Classical.choose`, B-13) and the
isomorphism `(1, 1, p(n_+)^{-1})`.  @census none (helper; O-7h) -/
theorem essSurj : (E_FNil (F := L) ℓ hℓ).EssSurj where
  mem_essImage W := by
    have hpoly := xStar_eq_poly (splitData hℓ W)
    exact ⟨(splitData hℓ W).toHCFObj, ⟨isoPoly (splitData hℓ W)
      (Classical.choose_spec hpoly).1 (Classical.choose_spec hpoly).2⟩⟩

variable (ℓ) in
/-- **`prop:splitequivalence`** (tex §5.1, `ℓ ≥ 1`; Steps O-7d…O-7h).  The assignment
`M_L ↦ 𝔼_L(M_L)` is a functor (`C1`: `E_F`, with `E_F_map` the restriction triple) and an
**equivalence** between `HC_λ(𝔤,K)_L` and the nilpotent finite-dimensional representations of the split
Gelfand quiver satisfying its relation (`C2`), whose functor is `𝔼_L` on the nose.  The proof is the
tex's (`C3`): faithfulness and fullness along the bijections `X : M_{j−1} → M_{j+1}`, `j ≠ ±ℓ`
(`equivalence_of_essSurj`: `E_FNil_faithful` by `eq_of_eq_on_V3`, `E_FNil_full` by
`exists_hom_of_edges`), and essential surjectivity (`essSurj`) "by the construction in the proof of
`thm:EEequivalence` with all rational structures omitted" (`splitData`, the `c`-free core), in which
`X⋆` read on `V(⋆)` is a polynomial `p(n⋆)` with `p(0) = 1` (`C4`, `xStar_eq_poly`), `p` intertwines
the edges (`C5`, `intertwine_bPlus`, `intertwine_aPlus`), and `(1_{V(−)}, 1_{V(⋆)}, p(n₊)⁻¹)` is an
isomorphism `𝔼_L(M) ≅ V` (`C6`, `isoPoly`, for any such `p`; `essSurj` takes `Classical.choose`).

@census    RQ2-5.02
@source    prop:splitequivalence
@clauses   RQ2-5.02-H1, RQ2-5.02-H2, RQ2-5.02-C1, RQ2-5.02-C2, RQ2-5.02-C3, RQ2-5.02-C4,
           RQ2-5.02-C5, RQ2-5.02-C6
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation).  The source category is the concrete
`HC_λ(𝔤,K)_L` = `HCF L ℓ` (objects with their weight decomposition, morphisms the `(𝔤,K)`-maps;
ruling `R-S8-6` of v1), equivalent to `HCLambda ℓ L` by `hcLambdaFEquiv`; the field `L` is any field
of characteristic `0` (the tex's `L_E` is an instance).  The target is `Rep^nil` of the split Gelfand
quiver **with** its relation (`RepNilRelSplit`).  Essential surjectivity follows the tex's route; v1's
asymmetric engine `E11` is deleted (OP-2) and survives only as the unformalized remark
`rmk:asymmetricsplitES` (`RQ2-5.18`, `EX-E11-REMARK`).
-/
theorem equivalence :
    ∃ e : HCF L ℓ ≌ (RepNilRelSplit L).FullSubcategory,
      e.functor ⋙ (RepNilRelSplit L).ι = E_F (F := L) ℓ hℓ :=
  equivalence_of_essSurj ℓ hℓ (essSurj ℓ hℓ)


end RationalQuivers.Gelfand.Split
