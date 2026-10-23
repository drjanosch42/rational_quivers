import RationalQuivers.Gelfand.Main
import RationalQuivers.Gelfand.Compat
import RationalQuivers.Descent.Galois

/-!
# Twisted forms: `thm:twistedEEequivalence` (§5, "Twisted forms", stage T5)

Let `E` be a field of characteristic `0` and `D'/E` **any** quadratic (hence Galois) extension
(a `D : SqrtNegOneExt E`; the structure is root-free since the v2 amendments T2-a2/T3-a1/T4-a1, so in
general `√-1 ∉ D'` — variant (ii), author decision of 2026-10-18). The category
`HC_λ(𝔤,K_{D'/E})_E` of `def:HClambdaDE` is `HCEObj ℓ E D`: an `E`-space `M_E` with the structure
of an object of the split category of `rmk:splitequivalenceanyfield` over `F = D'` (the graded
presentation; for `√-1 ∈ D'` it is `HC_λ(𝔤,K)_{D'}`) on `M_{D'} = D' ⊗_E M_E` and the induced
involution `c`, subject to
`c(M_n) = M_{-n}`, `cH = -Hc`, `cX = Yc`, `cY = Xc`. The quiver `Γ_{D'/E}` of `def:GammaDE` is the
`E`-rational Gelfand quiver with relation `a₋b₋ = a₊b₊` (`RationalStructure.RepNilQ`, `ℓ ≥ 1`) or
the `E`-rational cyclic quiver (`Cyclic.RepNilCycQ`, `ℓ = 0`) for `Gal(D'/E)`.

The theorem: the assignment `𝔼_{D'/E} : M_E ↦ (𝔼_{D'}(M_{D'}), φ_•)` is well-defined and an equivalence
`HC_λ(𝔤,K_{D'/E})_E ≃ Rep^nil(Γ_{D'/E})`, for `ℓ ≥ 1` and for `ℓ = 0`. Stated with the functor pinned
(`∃ e, e.functor = 𝔼`), as `Gelfand/Main.lean` states `thm:EEequivalence`.

The proofs are the engine's (stage T3): `EssSurj.E_Q_equivalence` (`ℓ ≥ 1`) and
`Cyclic.cyclic_E_Q_equivalence` (`ℓ = 0`), which are stated for every `SqrtNegOneExt`; fullness uses
`ζ := a - c(a)` (`GF.zeta`), so no hypothesis `√-1 ∉ E` is needed. For `√-1 ∉ E` and `D' = L_E` the
theorem is `thm:EEequivalence`/`thm:cyclicEEequivalence` in the engine presentation (`R-V2-3`).

Author decision T4-A (2026-10-18, `reports/AUTHOR-QUEUE.md`): keep the twisted-form generality, and
state it in the manuscript. Module created in v2 WP-13. Variant (ii) (author decision 2026-10-18,
`VARIANT-II-T4B-PLAN.md`): the theorem holds for every quadratic `D'/E`, with no proof edited; this
module's code is unchanged by the T5-a1 amendment (docstrings only). A `D'` without `√-1` is
instantiated in stage T6 (`Gelfand/TwistedForms/Inhabitants.lean`, `E = ℚ`, `D' = ℚ(√-3)`).
-/

namespace RationalQuivers.Gelfand

open CategoryTheory

variable (E : Type) [Field E] [CharZero E] (D : SqrtNegOneExt E)

/-! ### `def:HClambdaDE` and `def:GammaDE` -/

/-- **`def:HClambdaDE`**: the category `HC_λ(𝔤,K_{D'/E})_E` for a quadratic extension `D'/E`
(`D : SqrtNegOneExt E`, root-free, `c` its non-trivial automorphism): an `E`-space `M_E` with the
structure of an object of the split category of `rmk:splitequivalenceanyfield` over `F = D'` (for
`√-1 ∈ D'`: of `HC_λ(𝔤,K)_{D'}`) on `M_{D'} = D' ⊗_E M_E` such that `c ⊗ 1` satisfies
`c(M_n) = M_{-n}`, `cH = -Hc`, `cX = Yc`, `cY = Xc`; morphisms the `D'`-linear maps preserving the `M_n`
and commuting with `H, X, Y, c`. It is `HCEObj ℓ E D` (`Gelfand/GeneralBaseCategory.lean`) with its
category structure `instCategoryHCEObj` (morphisms `HCEHom`).

@census    RQ2-5.22
@source    def:HClambdaDE
@clauses   RQ2-5.22-H1, RQ2-5.22-C1, RQ2-5.22-C2, RQ2-5.22-C3
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation), as `def:HClambdaE` (`EX-HC`): `M_{D'}` carries the
weight-data presentation of `HC_λ(𝔤,K)_{D'}` (`RationalSetupOver.weight`, `admissible`,
`centralCharacter` — the parity —, `fg`, `gic`), `baseChange : D' ⊗_E M_E ≃ M_{D'}` and `conj` (`c ⊗ 1`);
`C3` (by Galois descent the morphisms are the base changes of the `E`-linear maps `M_E → N_E` with this
property) is `HCEHom.exists_unique_descent` below, proved from `thm:galoisdescent`'s
`Descent.descentUnit_bijective`.
-/
abbrev HCTwisted (ℓ : ℕ) : Type 1 := HCEObj ℓ E D

section Descent

open TensorProduct RationalQuivers.Descent

variable {E D} {ℓ : ℕ}

/-- `c` on `M_{D'}` is `c ⊗ 1` on `D' ⊗_E M_E`.  @census none (helper) -/
theorem HCEObj.conj_baseChange_tmul (A : HCEObj ℓ E D) (a : D.carrier) (v : A.form) :
    A.setup.conj (A.setup.baseChange (a ⊗ₜ[E] v)) = A.setup.baseChange (D.conj a ⊗ₜ[E] v) := by
  have h : ∀ b : D.carrier, b ⊗ₜ[E] v = b • ((1 : D.carrier) ⊗ₜ[E] v) := fun b => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h a, h (D.conj a), LinearEquiv.map_smul, A.setup.conj_smul, A.setup.conj_baseChange,
    LinearEquiv.map_smul]

/-- The Galois action `σ ⊗ 1` (`σ ≠ 1`, i.e. `σ = c`) on `D' ⊗_E M_E` is `c` on `M_{D'}`.
@census none (helper) -/
theorem HCEObj.baseChange_galois_smul (A : HCEObj ℓ E D) (σ : Gal(D.carrier/E)) (hσ : σ ≠ 1)
    (x : D.carrier ⊗[E] A.form) :
    A.setup.baseChange (σ • x) = A.setup.conj (A.setup.baseChange x) := by
  obtain rfl := D.eq_conj_of_ne_one hσ
  rw [galoisTensorAction_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul a v => rw [TensorProduct.map_tmul, HCEObj.conj_baseChange_tmul]; rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- Galois descent for `M_{D'}`: a `c`-fixed vector is `1 ⊗ w` for a unique `w ∈ M_E`
(`Descent.descentUnit_bijective`).  @census none (helper) -/
theorem HCEObj.exists_unique_of_conj_eq (B : HCEObj ℓ E D) (y : B.carrier) (hy : B.setup.conj y = y) :
    ∃! w : B.form, B.setup.baseChange ((1 : D.carrier) ⊗ₜ[E] w) = y := by
  set x := B.setup.baseChange.symm y with hxdef
  have hx : ∀ σ : Gal(D.carrier/E), σ • x = x := by
    intro σ
    by_cases hσ : σ = 1
    · subst hσ; exact one_smul _ _
    · apply B.setup.baseChange.injective
      rw [B.baseChange_galois_smul σ hσ, hxdef, LinearEquiv.apply_symm_apply, hy]
  obtain ⟨w, hw⟩ := (descentUnit_bijective E D.carrier (ModuleCat.of E B.form)).2 ⟨x, hx⟩
  have hw' : (1 : D.carrier) ⊗ₜ[E] w = x := congrArg Subtype.val hw
  refine ⟨w, show B.setup.baseChange _ = y by rw [hw', hxdef, LinearEquiv.apply_symm_apply],
    fun w' hw'' => ?_⟩
  apply (descentUnit_bijective E D.carrier (ModuleCat.of E B.form)).1
  apply Subtype.ext
  show (1 : D.carrier) ⊗ₜ[E] w' = (1 : D.carrier) ⊗ₜ[E] w
  rw [hw', hxdef, ← hw'', LinearEquiv.symm_apply_apply]

/-- A morphism sends `1 ⊗ v` to a `c`-fixed vector.  @census none (helper) -/
theorem HCEHom.conj_apply_one_tmul {A B : HCEObj ℓ E D} (f : A ⟶ B) (v : A.form) :
    B.setup.conj (f.toLinearMap (A.setup.baseChange ((1 : D.carrier) ⊗ₜ[E] v)))
      = f.toLinearMap (A.setup.baseChange ((1 : D.carrier) ⊗ₜ[E] v)) := by
  rw [← f.map_conj, A.setup.conj_baseChange]

/-- **`def:HClambdaDE`, clause `C3`** (Galois descent of morphisms): every morphism
`f : M_{D'} → N_{D'}` of `HC_λ(𝔤,K_{D'/E})_E` is the base change `D' ⊗_E g` of a unique `E`-linear map
`g : M_E → N_E` (through the identifications `D' ⊗_E M_E ≃ M_{D'}`).

Clause witness of `RQ2-5.22-C3` (claimant: `HCTwisted`).  @census none (clause witness) -/
theorem HCEHom.exists_unique_descent {A B : HCEObj ℓ E D} (f : A ⟶ B) :
    ∃! g : A.form →ₗ[E] B.form,
      f.toLinearMap ∘ₗ A.setup.baseChange.toLinearMap
        = B.setup.baseChange.toLinearMap ∘ₗ g.baseChange D.carrier := by
  let gf : A.form → B.form := fun v =>
    (B.exists_unique_of_conj_eq _ (HCEHom.conj_apply_one_tmul f v)).exists.choose
  have hg : ∀ v, B.setup.baseChange ((1 : D.carrier) ⊗ₜ[E] gf v)
      = f.toLinearMap (A.setup.baseChange ((1 : D.carrier) ⊗ₜ[E] v)) :=
    fun v => (B.exists_unique_of_conj_eq _ (HCEHom.conj_apply_one_tmul f v)).exists.choose_spec
  have uniq : ∀ v w, B.setup.baseChange ((1 : D.carrier) ⊗ₜ[E] w)
      = f.toLinearMap (A.setup.baseChange ((1 : D.carrier) ⊗ₜ[E] v)) → w = gf v :=
    fun v w h => (B.exists_unique_of_conj_eq _ (HCEHom.conj_apply_one_tmul f v)).unique h (hg v)
  have hsm : ∀ (M : HCEObj ℓ E D) (c : E) (u : M.form),
      (1 : D.carrier) ⊗ₜ[E] (c • u) = (algebraMap E D.carrier c) • ((1 : D.carrier) ⊗ₜ[E] u) :=
    fun M c u => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
  let g : A.form →ₗ[E] B.form :=
    { toFun := gf
      map_add' := fun v w => (uniq (v + w) (gf v + gf w) (by
        rw [TensorProduct.tmul_add, map_add, hg, hg, TensorProduct.tmul_add, map_add, map_add])).symm
      map_smul' := fun c v => (uniq (c • v) (c • gf v) (by
        rw [hsm B, LinearEquiv.map_smul, hg, hsm A, LinearEquiv.map_smul, LinearMap.map_smul])).symm }
  have key : f.toLinearMap ∘ₗ A.setup.baseChange.toLinearMap
      = B.setup.baseChange.toLinearMap ∘ₗ g.baseChange D.carrier := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | tmul a v =>
      have h1 : ∀ (M : HCEObj ℓ E D) (u : M.form), a ⊗ₜ[E] u = a • ((1 : D.carrier) ⊗ₜ[E] u) :=
        fun M u => by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.baseChange_tmul]
      rw [h1 A v, h1 B (g v), LinearEquiv.map_smul, LinearMap.map_smul, LinearEquiv.map_smul]
      exact congrArg (a • ·) (hg v).symm
  refine ⟨g, key, fun g' hg' => LinearMap.ext fun v => ?_⟩
  refine uniq v (g' v) ?_
  have := congrArg (fun φ => φ ((1 : D.carrier) ⊗ₜ[E] v)) hg'
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.baseChange_tmul] at this
  exact this.symm

end Descent

/-- **`def:GammaDE`**: the `E`-rational quiver `Γ_{D'/E}` for `Gal(D'/E) = {1, c}`: the Gelfand quiver
(`ℓ ≥ 1`; its representations are required to satisfy `a₋b₋ = a₊b₊`, `RationalStructure.RepNilRelQ`)
or the cyclic quiver (`ℓ = 0`), with `c` acting as in `ex:gelfand`, `ex:cyclic`.

@census    RQ2-5.23
@source    def:GammaDE
@clauses   RQ2-5.23-C1, RQ2-5.23-C2, RQ2-5.23-C3
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation): defined by cases on `ℓ` from the T3 quivers
`RationalStructure.gelfandQ` and `Cyclic.cyclicQ` (`GammaTwisted_of_pos`, `GammaTwisted_zero`); the
relation for `ℓ ≥ 1` is the object property `RationalStructure.RepNilRelQ` of the target category.
`C3` (for `√-1 ∉ E`, `Γ_{L_E/E} = Γ_E`) is `GammaTwisted_sqrtExt` below (from T0's
`gelfandOfSign_eq_gelfandOfCardTwo` and T4's `Compat.cyclicOfSign_eq_cyclicOfCardTwo`).
-/
noncomputable def GammaTwisted (ℓ : ℕ) : RationalQuiver E D.carrier :=
  if 1 ≤ ℓ then RationalStructure.gelfandQ D.card_gal else Cyclic.cyclicQ D.card_gal

/-- `Γ_{D'/E}` for `ℓ ≥ 1` is the `E`-rational Gelfand quiver.  @census none (helper) -/
theorem GammaTwisted_of_pos {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    GammaTwisted E D ℓ = RationalStructure.gelfandQ D.card_gal := by
  rw [GammaTwisted, if_pos hℓ]

/-- `Γ_{D'/E}` for `ℓ = 0` is the `E`-rational cyclic quiver.  @census none (helper) -/
theorem GammaTwisted_zero : GammaTwisted E D 0 = Cyclic.cyclicQ D.card_gal := by
  rw [GammaTwisted, if_neg (by norm_num)]

/-- **`def:GammaDE`, clause `C3`**: for `√-1 ∉ E` (an `ImagUnit` `D₀` with `χ_E(σ) = -1` for some `σ`) and
`D' = L_E` (`D₀.sqrtExt hc`), `Γ_{L_E/E} = Γ_E` on the nose.

Clause witness of `RQ2-5.23-C3` (claimant: `GammaTwisted`).  @census none (clause witness) -/
theorem GammaTwisted_sqrtExt (D₀ : HC.ImagUnit E) (hc : ∃ σ : D₀.L ≃ₐ[E] D₀.L, D₀.chi σ = -1) (ℓ : ℕ) :
    GammaTwisted E (D₀.sqrtExt hc) ℓ = GammaE D₀ ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with rfl | h
  · rw [GammaTwisted_zero, GammaE_zero]
    exact (Compat.cyclicOfSign_eq_cyclicOfCardTwo E D₀.L (D₀.card_gal_of hc) D₀.chiHom_injective).symm
  · rw [GammaTwisted_of_pos E _ h, GammaE_of_pos D₀ h]
    exact (RationalQuiver.gelfandOfSign_eq_gelfandOfCardTwo E D₀.L (D₀.card_gal_of hc)
      D₀.chiHom_injective).symm

/-! ### `thm:twistedEEequivalence` -/

/-- **`thm:twistedEEequivalence` (a)**, `ℓ ≥ 1`: `𝔼_{D'/E}` is an equivalence
`HC_λ(𝔤,K_{D'/E})_E ≃ Rep^nil(Γ_{D'/E})`, `Γ_{D'/E}` the `E`-rational Gelfand quiver with its relation.

Clause witness of `RQ2-5.24-C1` (claimant: `gelfand_equivalence_twisted`).  @census none (clause witness) -/
theorem gelfand_equivalence_twisted_pos {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∃ e : HCEObj ℓ E D ≌ RationalStructure.RepNilQ D.card_gal,
      e.functor = Equivalence.E_QFunctor D.card_gal hℓ (Equivalence.E_Q_spec D.card_gal hℓ) := by
  obtain ⟨_, e, he⟩ := EssSurj.E_Q_equivalence (Dq := D) hℓ
  exact ⟨e, he⟩

/-- **`thm:twistedEEequivalence` (b)**, `ℓ = 0`: `𝔼_{D'/E}` is an equivalence
`HC_0(𝔤,K_{D'/E})_E ≃ Rep^nil(Γ_{D'/E})`, `Γ_{D'/E}` the `E`-rational cyclic quiver.

Clause witness of `RQ2-5.24-C2` (claimant: `gelfand_equivalence_twisted`).  @census none (clause witness) -/
theorem gelfand_equivalence_twisted_zero :
    ∃ e : HCEObj 0 E D ≌ Cyclic.RepNilCycQ D.card_gal,
      e.functor = Cyclic.E_CycFunctor D.card_gal (Cyclic.E_Cyc_spec D.card_gal) := by
  obtain ⟨_, e, he⟩ := Cyclic.cyclic_E_Q_equivalence (Dq := D)
  exact ⟨e, he⟩

/-- **Theorem** (`thm:twistedEEequivalence`).  Let `E` be a field of characteristic `0` and `D'/E` a
quadratic extension (any; `√-1 ∈ D'` is not assumed, variant (ii)).  (a) For `ℓ ≥ 1` the assignment `𝔼_{D'/E} : M_E ↦ (𝔼_{D'}(M_{D'}), φ_•)`
from `HC_λ(𝔤,K_{D'/E})_E` to `Rep^nil(Γ_{D'/E})` (Gelfand quiver, with its relation) is well-defined and
an equivalence of categories.  (b) For `ℓ = 0` the same holds with the cyclic quiver.

@census    RQ2-5.24
@source    thm:twistedEEequivalence
@clauses   RQ2-5.24-H1, RQ2-5.24-C1, RQ2-5.24-C2, RQ2-5.24-C3
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation): `HC_λ(𝔤,K_{D'/E})_E` is `HCEObj ℓ E D` (`HCTwisted`),
`D'/E` a `D : SqrtNegOneExt E` (`H1`; carrier, `IsGalois`, `FiniteDimensional`, `card_gal = 2`,
root-free after the R-PROC-4 amendments T2-a2/T3-a1/T4-a1/T5-a1, so `D'/E` is any quadratic
extension); `𝔼_{D'/E}` is the T3 engine
functor `Equivalence.E_QFunctor` (`ℓ ≥ 1`) resp. `Cyclic.E_CycFunctor` (`ℓ = 0`), pinned (`∃ e, e.functor = …`),
the target `RationalStructure.RepNilQ` resp. `Cyclic.RepNilCycQ` (on `Γ_{D'/E}`, `GammaTwisted_of_pos`,
`GammaTwisted_zero`).  (a) `gelfand_equivalence_twisted_pos`, (b) `gelfand_equivalence_twisted_zero`.
`C3` (for `√-1 ∉ E` the identification of `def:HClambdaDE` carries `𝔼_E` to `𝔼_{L_E/E}`, and
`Γ_{L_E/E} = Γ_E`) is `gelfand_equivalence_twisted_native` below (from T4's `Compat.hcEquivHCEObj`,
`Compat.engineNative`, `Compat.engineNativeZ`), with `𝔼_E` there T3's `Equivalence.E_EGel` (`ℓ ≥ 1`) and
`Cyclic.E_ECyc` (`ℓ = 0`), i.e. `E_E E D ℓ`, re-indexed along `Compat.targetEquivCardTwo(Z)`.
-/
theorem gelfand_equivalence_twisted :
    (∀ {ℓ : ℕ} (hℓ : 1 ≤ ℓ), ∃ e : HCEObj ℓ E D ≌ RationalStructure.RepNilQ D.card_gal,
        e.functor = Equivalence.E_QFunctor D.card_gal hℓ (Equivalence.E_Q_spec D.card_gal hℓ)) ∧
      ∃ e : HCEObj 0 E D ≌ Cyclic.RepNilCycQ D.card_gal,
        e.functor = Cyclic.E_CycFunctor D.card_gal (Cyclic.E_Cyc_spec D.card_gal) :=
  ⟨fun hℓ => gelfand_equivalence_twisted_pos E D hℓ, gelfand_equivalence_twisted_zero E D⟩

/-- **`thm:twistedEEequivalence`, clause `C3`**: for `√-1 ∉ E` (an `ImagUnit` `D₀` with `χ_E(σ) = -1`) and
`D' = L_E`, the identification `HC_λ(𝔤,K)_E ≃ HC_λ(𝔤,K_{L_E/E})_E` of `def:HClambdaDE` (`Compat.hcEquivHCEObj`,
functor `Compat.toHCEObjFunctor`) carries `𝔼_E` to `𝔼_{L_E/E}`: the twisted functor is naturally isomorphic to
the native `𝔼_E` (`Equivalence.E_EGel` for `ℓ ≥ 1`, `Cyclic.E_ECyc` for `ℓ = 0`) transported along it and
re-indexed along `Compat.targetEquivCardTwo(Z)`; and `Γ_{L_E/E} = Γ_E`. So the theorem contains
`thm:EEequivalence` and `thm:cyclicEEequivalence` for `√-1 ∉ E`.

Clause witness of `RQ2-5.24-C3` (claimant: `gelfand_equivalence_twisted`).  @census none (clause witness) -/
theorem gelfand_equivalence_twisted_native (D₀ : HC.ImagUnit E) (hc : ∃ σ : D₀.L ≃ₐ[E] D₀.L, D₀.chi σ = -1) :
    (∀ ℓ : ℕ, ∃ e : HC.HC ℓ E D₀ ≌ HCTwisted E (D₀.sqrtExt hc) ℓ, e.functor = Compat.toHCEObjFunctor hc) ∧
    (∀ {ℓ : ℕ} (hℓ : 1 ≤ ℓ), Nonempty (Equivalence.E_QFunctor (D₀.sqrtExt hc).card_gal hℓ
        (Equivalence.E_Q_spec (D₀.sqrtExt hc).card_gal hℓ) ≅
      Compat.ofHCEObjFunctor hc ⋙ Equivalence.E_EGel hℓ ⋙ (Compat.targetEquivCardTwo hc).functor)) ∧
    Nonempty (Cyclic.E_CycFunctor (D₀.sqrtExt hc).card_gal (Cyclic.E_Cyc_spec (D₀.sqrtExt hc).card_gal) ≅
      Compat.ofHCEObjFunctor hc ⋙ Cyclic.E_ECyc ⋙ (Compat.targetEquivCardTwoZ hc).functor) ∧
    (∀ ℓ : ℕ, GammaTwisted E (D₀.sqrtExt hc) ℓ = GammaE D₀ ℓ) :=
  ⟨fun _ => ⟨Compat.hcEquivHCEObj hc, Compat.hcEquivHCEObj_functor hc⟩,
   fun hℓ => ⟨Compat.engineNative hc hℓ _⟩, ⟨Compat.engineNativeZ hc _⟩, GammaTwisted_sqrtExt E D₀ hc⟩

end RationalQuivers.Gelfand
