module

public import RationalQuivers.Gelfand.Species.Equivalence
public import RationalQuivers.Species.Rep.PathFunctoriality

@[expose] public section

/-!
# `R_E = R_Gelfand ⊗_ℚ E` under the species isomorphism (`prop:speciesErelations`, `RQ2-5.27`; stage T6, T4-B)

`thm:speciesE` says that, in case (b) (`ℓ ≥ 1`, `√-1 ∉ E`), `S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E` (`C3`) and `R_E = R_Gelfand ⊗_ℚ E` (`C4`).
T4's `relation_baseChange` proves `C4` in the coordinates `Φ = θ_E⁻¹ ∘ κ ∘ (E ⊗ θ_ℚ)`. Here `C4` is proved under the map
**induced by the species isomorphism** on length-two path bimodules. On every length-two path `p` of `S(Γ_E)`:

```
E ⊗_ℚ {}M_{π e⁻¹ p}(S(Γ_ℚ))  --pathBaseChange-->  {}M_{e⁻¹ p}(S(Γ_ℚ) ⊗_ℚ E)  --(e⁻¹)_*-->  {}M_p(S(Γ_E))
```

* `relation_baseChange_induced`: for **every** isomorphism `e : S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E` of étale `E`-species, and every path,
  the image of `R_Gelfand ⊗_ℚ E` (the `E`-span of `1 ⊗ R_Gelfand`) is `R_E` (plan route B3′).
* `relation_baseChange_C3`: the case of the isomorphism of `C3` itself (`speciesBaseChangeIso`, transported along
  `GammaE_gel_eq`).
* `relation_baseChange_C3_ne_bot`: non-vacuity (G5). At `(⋆,±,⋆)` both sides are a non-zero line.

The proof does not unwind the isomorphism. `R` is the line spanned by a square root of `−1` in `{}_⋆M_± ≅ L_E`, and ring maps
preserve `x² = −1`. On vertices, `√-1 ∉ E` forces `e` to match `⋆` with `⋆` (`star_iff`).

The claim is made in the proof of `thm:speciesE` (label `prop:speciesErelations`) and is census row `RQ2-5.27` (census r14),
claimed here by `relation_baseChange_induced`. It witnesses `RQ2-5.16-C4` under every species isomorphism; `RQ2-5.16`
itself is claimed by the frozen T4 declaration `speciesE`.

@census none (module; claimant of `RQ2-5.27` below)
-/

namespace RationalQuivers.Gelfand.Species

open RationalQuivers.HC CategoryTheory GelfandRelation RationalQuivers.EtaleSpecies
open scoped TensorProduct

noncomputable local instance (priority := high) instAlgebraQiT : Algebra ℚ ImagUnit.qi.L :=
  ImagUnit.qi.algebra

local instance instIsGaloisQiT : IsGalois ℚ ImagUnit.qi.L := ImagUnit.isGalois _

local instance instFiniteDimensionalQiT : FiniteDimensional ℚ ImagUnit.qi.L :=
  ImagUnit.finiteDimensional _

/-- `S(Γ_ℚ)`, `ℓ ≥ 1`: the étale `ℚ`-species of the Gelfand quiver over `ℚ[√-1]`.  @census none (helper) -/
noncomputable abbrev SQ : EtaleSpecies ℚ := ES ℚ ImagUnit.qi.L cardQ

/-! ### Generic facts about the Gelfand species -/

section GelfandGeneric

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
  (hc : Nat.card Gal(L/K) = 2)

/-- The Gelfand species has exactly the two vertices `⋆`, `±`.  @census none (helper) -/
theorem node_cases (i : (ES K L hc).I) : i = nStar K L hc ∨ i = nPm K L hc := by
  induction i using Quotient.inductionOn with
  | h v =>
    have hv : ∀ n : Fin 3, n = 0 ∨ n = 1 ∨ n = 2 := by decide
    rcases hv v with rfl | rfl | rfl
    · exact Or.inr (GelfandDescent.vertexClass_0 K L hc)
    · exact Or.inl (GelfandDescent.vertexClass_1 K L hc)
    · exact Or.inr (GelfandDescent.vertexClass_2 K L hc)

/-- `i = ±` iff `i ≠ ⋆`.  @census none (helper) -/
theorem eq_pm_iff (i : (ES K L hc).I) : i = nPm K L hc ↔ i ≠ nStar K L hc := by
  refine ⟨fun h h' => GelfandDescent.star_ne_pm K L hc (h'.symm.trans h), fun h => ?_⟩
  exact (node_cases hc i).resolve_left h

/-- `L_± ≅ L` contains a square root of `−1` if `L` does.  @census none (helper) -/
theorem exists_sqrt_pm {i : (ES K L hc).I} (hi : i = nPm K L hc) {α : L} (hα : α * α = -1) :
    ∃ j : (ES K L hc).L i, j * j = -1 := by
  subst hi
  exact ⟨(eqVpm K L hc).symm α, by rw [← map_mul, hα, map_neg, map_one]⟩

/-- `cst` is multiplicative.  @census none (helper) -/
theorem cst_mul {i j : (ES K L hc).I} (z w : L) :
    cst K L hc (i := i) (j := j) z * cst K L hc w = cst K L hc (z * w) := rfl

/-- `cst (−1) = −1`.  @census none (helper) -/
theorem cst_neg_one {i j : (ES K L hc).I} : cst K L hc (i := i) (j := j) (-1) = -1 := rfl

/-- In `{}_⋆M_± ≅ L` the square roots of `−1` are `±α`.  @census none (helper) -/
theorem sqrt_cases {i j : (ES K L hc).I} (hi : i = nStar K L hc) (hj : j = nPm K L hc) {α : L}
    (hα : α * α = -1) (w : (ES K L hc).M i j) (hw : w * w = -1) :
    w = cst K L hc α ∨ w = -cst K L hc α := by
  subst hi; subst hj
  have h1 : evE K L hc (εSP K L hc) w * evE K L hc (εSP K L hc) w = α * α := by
    rw [← map_mul, hw, hα, map_neg, map_one]
  rcases mul_self_eq_mul_self_iff.mp h1 with h | h
  · exact Or.inl (evE_injective K L hc (by rw [h, evE_cst]))
  · exact Or.inr (evE_injective K L hc (by rw [h, map_neg, evE_cst]))

/-- `(R_Gelfand)_p = K·(α ⊗ 1)` as a `K`-subspace, at every path `p` of shape `(⋆, ±, ⋆)` (T4's
`RGelfand_p_restrictScalars'` is the case `p = idxG`).  @census none (helper) -/
theorem RGelfand_restrictScalars_of (α : L) {idx : ℕ → (SG K L hc).I}
    (hp : idx 0 = nStar K L hc ∧ idx 1 = nPm K L hc ∧ idx 2 = nStar K L hc) :
    (RGelfand K L hc α idx 1).toSubmodule.restrictScalars K = Submodule.span K {relGen K L hc α idx} := by
  rw [RGelfand_one, RGelfandAt_pos K L hc α hp]
  refine le_antisymm (fun y hy => ?_) (Submodule.span_le_restrictScalars K _ _)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨k, rfl⟩ := exists_algebraMap_star K L hc hp.1 c
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ k (Submodule.subset_span rfl)

/-- Off the paths of shape `(⋆, ±, ⋆)`, `R_Gelfand` is `0`.  @census none (helper) -/
theorem RGelfand_eq_bot_of (α : L) {idx : ℕ → (SG K L hc).I}
    (hp : ¬ (idx 0 = nStar K L hc ∧ idx 1 = nPm K L hc ∧ idx 2 = nStar K L hc)) :
    (RGelfand K L hc α idx 1).toSubmodule = ⊥ := by
  rw [RGelfand_one, RGelfandAt_neg K L hc α hp]

end GelfandGeneric

/-- A ring map preserves square roots of `−1`.  @census none (helper) -/
theorem sq_neg_one_map {R S' : Type} [Ring R] [Ring S'] (φ : R →+* S') {x : R} (hx : x * x = -1) :
    φ x * φ x = -1 := by
  rw [← map_mul, hx, map_neg, map_one]

/-- `mk (−x) y = −mk x y`.  @census none (helper) -/
theorem Balanced_mk_neg {K A B Y X : Type} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y] [SMulCommClass K Bᵐᵒᵖ Y]
    [SMulCommClass A Bᵐᵒᵖ Y] [IsScalarTower K A Y] [IsScalarTower K Bᵐᵒᵖ Y]
    [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X] (x : X) (y : Y) :
    Balanced.mk (K := K) (A := A) (B := B) (-x) y = -Balanced.mk x y := by
  rw [eq_neg_iff_add_eq_zero, ← Balanced.mk_add_left, neg_add_cancel, Balanced.mk_zero_left']

/-! ### Vertices: an isomorphism matches `⋆` with `⋆` -/

variable {E : Type} [Field E] [CharZero E] (D : ImagUnit E)

section Vertices

variable (h : ¬ ∃ a : E, a * a = -1)

/-- `√-1 ∉ E`: no ring map from a ring containing a square root of `−1` into an `E`-field all of whose elements come
from `E`.  @census none (helper) -/
theorem no_sqrt_of_rational (h : ¬ ∃ a : E, a * a = -1) {F R : Type} [Field F] [Algebra E F] [Ring R]
    (hF : ∀ x : F, ∃ a : E, algebraMap E F a = x) (φ : R →+* F) {j : R} (hj : j * j = -1) : False := by
  obtain ⟨a, ha⟩ := hF (φ j)
  refine h ⟨a, (algebraMap E F).injective ?_⟩
  rw [map_mul, ha, ← map_mul, hj, map_neg, map_one, map_neg, map_one]

set_option backward.isDefEq.respectTransparency.types false in
/-- A vertex of `S(Γ_ℚ) ⊗_ℚ E` over `⋆` has vertex field `E`.  @census none (helper) -/
theorem bc_star_rational (t : (SQ.baseChange E).I) (ht : SQ.fibreMap E t = nStar ℚ ImagUnit.qi.L cardQ)
    (x : (SQ.baseChange E).L t) : ∃ a : E, algebraMap E _ a = x := by
  classical
  have hall : ∀ z : E ⊗[ℚ] SQ.L (SQ.fibreMap E t), ∃ a : E, algebraMap E _ a = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul n l =>
      obtain ⟨q, rfl⟩ := exists_algebraMap_star ℚ ImagUnit.qi.L cardQ ht l
      refine ⟨q • n, ?_⟩
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      rfl
    | add z z' hz hz' =>
      obtain ⟨a, rfl⟩ := hz
      obtain ⟨a', rfl⟩ := hz'
      exact ⟨a + a', map_add _ _ _⟩
  obtain ⟨z, rfl⟩ : ∃ z, SQ.baseChangeProj E t z = x := by
    refine ⟨(SQ.vertexSplitting E t.1).equiv.symm (Function.update 0 t.2 x), ?_⟩
    show (SQ.vertexSplitting E t.1).equiv ((SQ.vertexSplitting E t.1).equiv.symm _) t.2 = x
    rw [AlgEquiv.apply_symm_apply]
    simp
  obtain ⟨a, rfl⟩ := hall z
  exact ⟨a, (AlgHom.commutes _ a).symm⟩

variable {D}

/-- The round trip on indices of an isomorphism.  @census none (helper) -/
theorem onI_hom_inv {S T : EtaleSpecies E} (e : S ≅ T) (s : S.I) : e.hom.onI (e.inv.onI s) = s :=
  congrFun (congrArg EtaleSpecies.Hom.onI e.hom_inv_id) s

/-- **Vertices.** For an isomorphism `e : S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E` and a vertex `s` of `S(Γ_E)`: `s = ⋆` iff `e⁻¹ s` lies
over `⋆`.

@census none (helper)
@clauses RQ2-5.27-C3
-/
theorem star_iff (e : SE D h ≅ SQ.baseChange E) (s : (SE D h).I) :
    s = nStar E D.L (cardE D h) ↔ SQ.fibreMap E (e.inv.onI s) = nStar ℚ ImagUnit.qi.L cardQ := by
  constructor
  · intro hs
    by_contra hne
    have hrat : ∀ x : (SQ.baseChange E).L (e.inv.onI s), ∃ a : E, algebraMap E _ a = x := by
      intro x
      obtain ⟨a, ha⟩ := exists_algebraMap_star E D.L (cardE D h) hs (e.inv.onL s x)
      refine ⟨a, (e.inv.onL s).toRingHom.injective ?_⟩
      exact ((e.inv.onL s).commutes a).trans ha
    obtain ⟨j, hj⟩ := exists_sqrt_pm cardQ ((eq_pm_iff cardQ _).mpr hne) ImagUnit.qi.i_mul_i
    exact no_sqrt_of_rational h hrat (PathDatum.bcOnL E SQ (e.inv.onI s)) hj
  · intro ht
    by_contra hne
    have hpm : e.hom.onI (e.inv.onI s) = nPm E D.L (cardE D h) := by
      rw [onI_hom_inv]; exact (eq_pm_iff (cardE D h) s).mpr hne
    obtain ⟨j, hj⟩ := exists_sqrt_pm (cardE D h) hpm D.i_mul_i
    exact no_sqrt_of_rational h (bc_star_rational (e.inv.onI s) ht)
      (e.hom.onL (e.inv.onI s)).toRingHom hj

/-- The path conditions on the two sides agree.

@census none (helper)
@clauses RQ2-5.27-C3
-/
theorem path_iff (e : SE D h ≅ SQ.baseChange E) (p : ℕ → (SE D h).I) :
    (p 0 = nStar E D.L (cardE D h) ∧ p 1 = nPm E D.L (cardE D h) ∧ p 2 = nStar E D.L (cardE D h)) ↔
      (SQ.fibreMap E (e.inv.onI (p 0)) = nStar ℚ ImagUnit.qi.L cardQ ∧
        SQ.fibreMap E (e.inv.onI (p 1)) = nPm ℚ ImagUnit.qi.L cardQ ∧
        SQ.fibreMap E (e.inv.onI (p 2)) = nStar ℚ ImagUnit.qi.L cardQ) := by
  rw [star_iff h e, star_iff h e, eq_pm_iff, eq_pm_iff, Ne, Ne, star_iff h e]

end Vertices

/-! ### The induced identification and the theorem -/

section Main

variable (h : ¬ ∃ a : E, a * a = -1)

set_option backward.isDefEq.respectTransparency.types false in
/-- B2 at the path `e⁻¹ p` of `S(Γ_ℚ) ⊗_ℚ E`: `E ⊗_ℚ {}M_{π e⁻¹ p}(S(Γ_ℚ)) → {}M_{e⁻¹ p}(S(Γ_ℚ) ⊗_ℚ E)`.
@census none (helper; T4-B) -/
noncomputable def phiBC (e : SE D h ≅ SQ.baseChange E) (p : ℕ → (SE D h).I) :
    E ⊗[ℚ] (RationalQuivers.Species.pathBimod SQ.toSpecies (fun n => SQ.fibreMap E (e.inv.onI (p n))) 1).carrier
      →ₗ[E] P2 (SQ.baseChange E) (e.inv.onI (p 0)) (e.inv.onI (p 1)) (e.inv.onI (p 2)) :=
  PathDatum.pathBaseChange E SQ (e.inv.onI (p 0)) (e.inv.onI (p 1)) (e.inv.onI (p 2))

set_option backward.isDefEq.respectTransparency.types false in
/-- B1 for `e⁻¹ : S(Γ_ℚ) ⊗_ℚ E ⟶ S(Γ_E)` at the path `p`.  @census none (helper; T4-B) -/
noncomputable def phiIso (e : SE D h ≅ SQ.baseChange E) (p : ℕ → (SE D h).I) :
    P2 (SQ.baseChange E) (e.inv.onI (p 0)) (e.inv.onI (p 1)) (e.inv.onI (p 2))
      →ₗ[E] (RationalQuivers.Species.pathBimod (SE D h).toSpecies p 1).carrier :=
  pathMapHom e.inv (p 0) (p 1) (p 2)

set_option backward.isDefEq.respectTransparency.types false in
/-- **The identification induced by a species isomorphism** `e : S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E` on the length-two path bimodule
at `p`: the base-change map of path bimodules (`phiBC`, B2), then the map induced by `e⁻¹` (`phiIso`, B1).
@census none (helper; T4-B) -/
noncomputable def inducedPhi (e : SE D h ≅ SQ.baseChange E) (p : ℕ → (SE D h).I) :
    E ⊗[ℚ] (RationalQuivers.Species.pathBimod SQ.toSpecies (fun n => SQ.fibreMap E (e.inv.onI (p n))) 1).carrier
      →ₗ[E] (RationalQuivers.Species.pathBimod (SE D h).toSpecies p 1).carrier :=
  (phiIso D h e p).comp (phiBC D h e p)

/-- `Φ_e(1 ⊗ (√-1 ⊗ 1)) = w ⊗ 1` with `w = e⁻¹(ι(√-1))`.  @census none (helper) -/
theorem inducedPhi_relGen (e : SE D h ≅ SQ.baseChange E) (p : ℕ → (SE D h).I) :
    inducedPhi D h e p ((1 : E) ⊗ₜ[ℚ] relGen ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i
        (fun n => SQ.fibreMap E (e.inv.onI (p n)))) =
      Balanced.mk (K := E) (A := (SE D h).L (p 1)) (B := (SE D h).L (p 2))
        (e.inv.onM (p 0) (p 1) (PathDatum.bcOnM E SQ (e.inv.onI (p 0)) (e.inv.onI (p 1))
          (cst ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i)))
        (cst E D.L (cardE D h) (i := p 1) (j := p 2) 1) := by
  have hbc := PathDatum.pathBaseChange_tmul_mk E SQ (e.inv.onI (p 0)) (e.inv.onI (p 1)) (e.inv.onI (p 2)) (1 : E)
    (cst ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i) (cst ℚ ImagUnit.qi.L cardQ 1)
  rw [one_smul] at hbc
  have h1 : e.inv.onM (p 1) (p 2) (PathDatum.bcOnM E SQ (e.inv.onI (p 1)) (e.inv.onI (p 2))
      (cst ℚ ImagUnit.qi.L cardQ 1)) = cst E D.L (cardE D h) (i := p 1) (j := p 2) 1 :=
    (congrArg (e.inv.onM (p 1) (p 2)) (map_one _)).trans (map_one _)
  show phiIso D h e p (phiBC D h e p _) = _
  refine (congrArg (phiIso D h e p) hbc).trans ?_
  exact congrArg (fun z => Balanced.mk (K := E) (A := (SE D h).L (p 1)) (B := (SE D h).L (p 2))
    (e.inv.onM (p 0) (p 1) (PathDatum.bcOnM E SQ (e.inv.onI (p 0)) (e.inv.onI (p 1))
      (cst ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i))) z) h1

set_option backward.isDefEq.respectTransparency.types false in
/-- **`R_E = R_Gelfand ⊗_ℚ E`, under every species isomorphism** (`RQ2-5.27`, route B3′). Let
`e : S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E` be any isomorphism of étale `E`-species, and `p` any length-two path of `S(Γ_E)`. Then the map
induced by `e` on path bimodules (`inducedPhi`) carries `R_Gelfand ⊗_ℚ E` (the `E`-span of `1 ⊗ (R_Gelfand)_{π e⁻¹ p}`)
onto `(R_E)_p`. Both relations live in length two only (`RGelfand` is `⊥` at every other length).

@census    RQ2-5.27
@source    prop:speciesErelations
@clauses   RQ2-5.27-H1, RQ2-5.27-H2, RQ2-5.27-C1
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation) on `H1`, `H2`: `S(Γ_E)` for `√-1 ∉ E` is the species of
`gelfandOfCardTwo E L_E`, which **is** `Γ_E` for every `ℓ ≥ 1` (`GammaE_gel_eq`), as in `speciesE`; the manuscript's
`g : S(Γ_ℚ) ⊗_ℚ E → S(Γ_E)` is `e.inv` for an isomorphism `e` in the other direction.  `C2` is
`relation_baseChange_C3`, `C3` is `star_iff`/`path_iff`.
-/
theorem relation_baseChange_induced (e : SE D h ≅ SQ.baseChange E) (p : ℕ → (SE D h).I) :
    (Submodule.span E ((fun x => (1 : E) ⊗ₜ[ℚ] x) ''
        (SetLike.coe (RGelfandQ (fun n => SQ.fibreMap E (e.inv.onI (p n))) 1).toSubmodule))).map
          (inducedPhi D h e p) =
      (RE D h p 1).toSubmodule.restrictScalars E := by
  show (Submodule.span E ((fun x => (1 : E) ⊗ₜ[ℚ] x) ''
      (SetLike.coe (RGelfand ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i (fun n => SQ.fibreMap E (e.inv.onI (p n))) 1).toSubmodule))).map
        (inducedPhi D h e p) =
    (RGelfand E D.L (cardE D h) D.i p 1).toSubmodule.restrictScalars E
  by_cases hp : p 0 = nStar E D.L (cardE D h) ∧ p 1 = nPm E D.L (cardE D h) ∧ p 2 = nStar E D.L (cardE D h)
  · have hq : SQ.fibreMap E (e.inv.onI (p 0)) = nStar ℚ ImagUnit.qi.L cardQ ∧
        SQ.fibreMap E (e.inv.onI (p 1)) = nPm ℚ ImagUnit.qi.L cardQ ∧
        SQ.fibreMap E (e.inv.onI (p 2)) = nStar ℚ ImagUnit.qi.L cardQ := (path_iff h e p).mp hp
    set g := relGen ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i (fun n => SQ.fibreMap E (e.inv.onI (p n)))
    have hQ : SetLike.coe (RGelfand ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i (fun n => SQ.fibreMap E (e.inv.onI (p n))) 1).toSubmodule =
        (SetLike.coe (Submodule.span ℚ {g}) : Set _) := by
      rw [← RGelfand_restrictScalars_of cardQ ImagUnit.qi.i hq, Submodule.coe_restrictScalars]
    have hspan : Submodule.span E ((fun x => (1 : E) ⊗ₜ[ℚ] x) ''
        (Submodule.span ℚ {g} : Set _)) = Submodule.span E {(1 : E) ⊗ₜ[ℚ] g} := by
      refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono ?_)
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
        dsimp only
        rw [TensorProduct.tmul_smul,
          show c • ((1 : E) ⊗ₜ[ℚ] g) = (algebraMap ℚ E c) • ((1 : E) ⊗ₜ[ℚ] g) from (algebraMap_smul E c _).symm]
        exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
      · rintro _ rfl
        exact ⟨g, Submodule.subset_span rfl, rfl⟩
    -- the image of the generator is `w ⊗ 1` with `w² = −1`
    have hw := sq_neg_one_map (e.inv.onM (p 0) (p 1)).toRingHom (sq_neg_one_map
      (PathDatum.bcOnM E SQ (e.inv.onI (p 0)) (e.inv.onI (p 1)))
      ((cst_mul cardQ _ _).trans ((congrArg _ ImagUnit.qi.i_mul_i).trans (cst_neg_one cardQ))))
    have himg := inducedPhi_relGen D h e p
    generalize e.inv.onM (p 0) (p 1) (PathDatum.bcOnM E SQ (e.inv.onI (p 0)) (e.inv.onI (p 1))
      (cst ℚ ImagUnit.qi.L cardQ ImagUnit.qi.i)) = w at hw himg
    rw [hQ, hspan, Submodule.map_span, Set.image_singleton, himg,
      RGelfand_restrictScalars_of (cardE D h) D.i hp]
    rcases sqrt_cases (cardE D h) hp.1 hp.2.1 D.i_mul_i w hw with hw' | hw'
    · rw [hw']; rfl
    · rw [hw', Balanced_mk_neg]
      exact (congrArg (Submodule.span E) (Set.neg_singleton _).symm).trans (Submodule.span_neg _)
  · have hq : ¬ (SQ.fibreMap E (e.inv.onI (p 0)) = nStar ℚ ImagUnit.qi.L cardQ ∧
        SQ.fibreMap E (e.inv.onI (p 1)) = nPm ℚ ImagUnit.qi.L cardQ ∧
        SQ.fibreMap E (e.inv.onI (p 2)) = nStar ℚ ImagUnit.qi.L cardQ) := fun hq => hp ((path_iff h e p).mpr hq)
    rw [RGelfand_eq_bot_of cardQ _ hq, RGelfand_eq_bot_of (cardE D h) _ hp, Submodule.restrictScalars_bot,
      Submodule.bot_coe, Set.image_singleton, TensorProduct.tmul_zero, Submodule.span_singleton_eq_bot.mpr rfl,
      Submodule.map_bot]

/-- `C3`'s isomorphism `S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E` (`speciesBaseChangeIso`, `ℓ = k + 1`), transported along
`Γ_E = gelfandOfCardTwo E L_E` and `Γ_ℚ = gelfandOfCardTwo ℚ ℚ[√-1]` (`GammaE_gel_eq`).  @census none (helper) -/
noncomputable def speciesBaseChangeIsoGel (k : ℕ) : SE D h ≅ SQ.baseChange E :=
  eqToIso (congrArg RationalQuiver.toSpecies (GammaE_gel_eq D h k)).symm ≪≫
    speciesBaseChangeIso D (k + 1) ≪≫
      eqToIso (congrArg (fun Γ => (RationalQuiver.toSpecies Γ).baseChange E) (GammaE_gel_eq ImagUnit.qi qi_not_sqrt' k))

set_option backward.isDefEq.respectTransparency.types false in
/-- **`prop:speciesErelations`, `C2`** (`RQ2-5.27-C2`): in case (b), `R_E = R_Gelfand ⊗_ℚ E` **under the isomorphism of `C3`**. The map
induced on length-two path bimodules by `S(Γ_E) ≅ S(Γ_ℚ) ⊗_ℚ E` (`speciesBaseChangeIso`), composed with the base change of
path bimodules, carries the `E`-span of `1 ⊗ R_Gelfand` onto `R_E`, at every path.  It witnesses `RQ2-5.16-C4` in the
sense the proof of `thm:speciesE` gives it.

@census none (helper)
@clauses RQ2-5.27-C2
-/
theorem relation_baseChange_C3 (k : ℕ) (p : ℕ → (SE D h).I) :
    (Submodule.span E ((fun x => (1 : E) ⊗ₜ[ℚ] x) ''
        (SetLike.coe (RGelfandQ (fun n => SQ.fibreMap E ((speciesBaseChangeIsoGel D h k).inv.onI (p n)))
          1).toSubmodule))).map (inducedPhi D h (speciesBaseChangeIsoGel D h k) p) =
      (RE D h p 1).toSubmodule.restrictScalars E :=
  relation_baseChange_induced D h _ p

/-- **Non-vacuity (G5)** of `relation_baseChange_C3`: at the path `(⋆, ±, ⋆)` both sides are a non-zero line.
@census none (G5 check for `relation_baseChange_C3`) -/
theorem relation_baseChange_C3_ne_bot :
    (RE D h (idxG E D.L (cardE D h)) 1).toSubmodule.restrictScalars E ≠ ⊥ := by
  intro h0
  have hmem : relGen E D.L (cardE D h) D.i (idxG E D.L (cardE D h)) ∈
      (RE D h (idxG E D.L (cardE D h)) 1).toSubmodule.restrictScalars E := by
    show _ ∈ (RGelfand E D.L (cardE D h) D.i (idxG E D.L (cardE D h)) 1).toSubmodule.restrictScalars E
    rw [RGelfand_restrictScalars_of (cardE D h) D.i
      ⟨idxG_zero E D.L (cardE D h), idxG_one E D.L (cardE D h), idxG_two E D.L (cardE D h)⟩]
    exact Submodule.subset_span rfl
  rw [h0, Submodule.mem_bot] at hmem
  exact i_ne_zero D (by
    rw [← theta_relGen E D.L (cardE D h) D.i]
    exact (congrArg (theta E D.L (cardE D h)) hmem).trans (map_zero _))

end Main

end RationalQuivers.Gelfand.Species
