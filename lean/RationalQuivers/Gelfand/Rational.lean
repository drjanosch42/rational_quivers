module

public import RationalQuivers.Gelfand.Compat
public import RationalQuivers.Gelfand.Species.Rational
public import RationalQuivers.HC.ClassicalComparison

@[expose] public section

/-!
# Over `ℚ`, `ℂ` and `ℝ` (tex §5.4, stage T4)

`thm:EEQQequivalence` and `thm:cyclicEEQQequivalence` (labels and statements kept from v1) as the
case `E = ℚ` of `thm:EEequivalence` / `thm:cyclicEEequivalence` (stage T3), Theorem A (`thm:introA`),
and the `ℂ`/`ℝ` instances of `rmk:classicalcases`.  The identifications of presentations these use
are in `Gelfand/Compat.lean` (WP-11a).

@census none (module; claimants of `RQ2-5.05`, `RQ2-5.07`, `RQ2-5.19`, `RQ2-0.01` below)
-/

namespace RationalQuivers.Gelfand.Rational

open RationalQuivers.HC RationalQuivers.Gelfand.Compat CategoryTheory

section Rat

/-- `L_ℚ/ℚ` is Galois (T1's derived instance `ImagUnit.isGalois`, which instance search does not
find through `ImagUnit.qi.L = ℚ[√-1]` on its own).  @census none (helper) -/
local instance instIsGaloisQi : IsGalois ℚ ImagUnit.qi.L := ImagUnit.isGalois _

local instance instFiniteDimensionalQi : FiniteDimensional ℚ ImagUnit.qi.L :=
  ImagUnit.finiteDimensional _

/-- `√-1 ∉ ℚ`.  @census none (helper) -/
theorem qi_not_sqrt : ¬ ∃ a : ℚ, a * a = -1 :=
  fun ⟨a, ha⟩ => by nlinarith [mul_self_nonneg a]

/-- `Γ_ℚ` (`def:GammaE` at `E = ℚ`, `ℓ ≥ 1`) **is** the `ℚ`-rational Gelfand quiver of `ex:gelfand`.
@census none (helper; `RQ2-5.05-C2`) -/
theorem GammaE_qi_of_pos {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    GammaE ImagUnit.qi ℓ = RationalQuiver.gelfandOfCardTwo ℚ ImagUnit.qi.L
      (ImagUnit.qi.card_gal_of_not_sqrt qi_not_sqrt) :=
  (GammaE_of_pos ImagUnit.qi hℓ).trans
    (ImagUnit.qi.gelfandOfSign_eq_gelfandOfCardTwo qi_not_sqrt)

/-- `Γ_ℚ` at `ℓ = 0` **is** the `ℚ`-rational cyclic quiver of `ex:cyclic`.
@census none (helper; `RQ2-5.07-C2`) -/
theorem GammaE_qi_zero :
    GammaE ImagUnit.qi 0 = RationalQuiver.cyclicOfCardTwo ℚ ImagUnit.qi.L
      (ImagUnit.qi.card_gal_of_not_sqrt qi_not_sqrt) :=
  (GammaE_zero ImagUnit.qi).trans
    (cyclicOfSign_eq_cyclicOfCardTwo ℚ ImagUnit.qi.L _ ImagUnit.qi.chiHom_injective)

/-- **Theorem** (`thm:EEQQequivalence`).  For `ℓ ≥ 1` the assignment
`𝔼_ℚ : M_ℚ ↦ (𝔼_{ℚ[√-1]}(M_{ℚ[√-1]}), φ_•)` from `HC_λ(𝔤,K)_ℚ` to the category `Rep^nil(Γ_ℚ)` of
`ℚ`-rational finite-dimensional nilpotent representations of the `ℚ`-rational Gelfand quiver is
well-defined and an equivalence of categories.

*Proof.* `thm:EEequivalence` (`gelfand_equivalence_pos`) for `E = ℚ`, `L_ℚ = ℚ[√-1]`
(`ImagUnit.qi`).

@census    RQ2-5.05
@source    thm:EEQQequivalence
@clauses   RQ2-5.05-H1, RQ2-5.05-H2, RQ2-5.05-C1, RQ2-5.05-C2, RQ2-5.05-C3, RQ2-5.05-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation).  `HC_λ(𝔤,K)_ℚ` is `HC ℓ ℚ ImagUnit.qi`, the
descent presentation of `def:HClambdaE` (`EX-HC`).  The target is `RepNilTarget ImagUnit.qi ℓ`,
`Rep^nil(Γ_ℚ)` with the relation `a₋b₋ = a₊b₊` (`C2`); `Γ_ℚ` **is** the quiver of `ex:gelfand`
(`GammaE_qi_of_pos`).  `C1` (well-defined: `φ_•` is a `ℚ`-rational structure) and `C3` are the
functor `E_E ℚ ImagUnit.qi ℓ` with values in `Rep^nil(Γ_ℚ)` and the equivalence whose functor it
**is** (`∃ e, e.functor = E_E …`); `C4` is the proof term, `gelfand_equivalence_pos` at `E = ℚ`.
-/
theorem E_Q_equivalence {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    ∃ e : HC ℓ ℚ ImagUnit.qi ≌ (RepNilTarget ImagUnit.qi ℓ).FullSubcategory,
      e.functor = E_E ℚ ImagUnit.qi ℓ :=
  gelfand_equivalence_pos hℓ

/-- **Theorem** (`thm:cyclicEEQQequivalence`).  For `ℓ = 0` the assignment
`𝔼_ℚ : M_ℚ ↦ (𝔼_{ℚ[√-1]}(M_{ℚ[√-1]}), φ_•)` from `HC_0(𝔤,K)_ℚ` to the category of `ℚ`-rational
finite-dimensional nilpotent representations of the `ℚ`-rational cyclic quiver is well-defined and
an equivalence of categories.

*Proof.* `thm:cyclicEEequivalence` (`gelfand_equivalence_zero`) for `E = ℚ`.

@census    RQ2-5.07
@source    thm:cyclicEEQQequivalence
@clauses   RQ2-5.07-H1, RQ2-5.07-H2, RQ2-5.07-C1, RQ2-5.07-C2, RQ2-5.07-C3, RQ2-5.07-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation).  `HC_0(𝔤,K)_ℚ` is `HC 0 ℚ ImagUnit.qi` (`EX-HC`);
the target is `RepNilTarget ImagUnit.qi 0`, and `Γ_ℚ` at `ℓ = 0` **is** the quiver of `ex:cyclic`
(`GammaE_qi_zero`, `C2`).  `C1`, `C3`: the functor `E_E ℚ ImagUnit.qi 0` and the equivalence whose
functor it is; `C4`: the proof term, `gelfand_equivalence_zero` at `E = ℚ`.
-/
theorem cyclic_E_Q_equivalence :
    ∃ e : HC 0 ℚ ImagUnit.qi ≌ (RepNilTarget ImagUnit.qi 0).FullSubcategory,
      e.functor = E_E ℚ ImagUnit.qi 0 :=
  gelfand_equivalence_zero

/-! ## `rmk:classicalcases`: `E = ℂ` and `E = ℝ` (`RQ2-5.19`, OQ-14) -/

/-- **`rmk:classicalcases`, `E = ℂ`** (`RQ2-5.19-C1`).  `L_ℂ = ℂ`, `Γ_ℂ` is split, and by
`rmk:HClambdaC` (`HC.ClassicalComparison.hcLambda_complex_equiv`) `thm:EEequivalence` and
`thm:cyclicEEequivalence` at `E = ℂ` are Gelfand's equivalence: `HC_λ(𝔤,K) ≃ Rep^nil` of the Gelfand
quiver with its relation (`ℓ ≥ 1`) resp. of the cyclic quiver (`ℓ = 0`), the functor being `𝔼_ℂ`
on the classical Harish-Chandra modules of `def:hcmodule`.

@census    RQ2-5.19
@source    rmk:classicalcases
@clauses   RQ2-5.19-H1, RQ2-5.19-C1, RQ2-5.19-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation): `HC_λ(𝔤,K)` is `HC.Category ℓ` (`def:hcmodule`
sliced at `λ = ℓ²`, `RQ2-3.11`), identified with `HC ℓ ℂ ImagUnit.complex` by `rmk:HClambdaC`
(`RQ2-3.15`, WP-11c); `Rep^nil` of the split Gelfand/cyclic quiver is `RepNilTarget ImagUnit.complex ℓ`
(split by `GammaE_isSplit_iff`).  The `E = ℝ` half (`C2`) is `gelfand_equivalence_real`.
-/
theorem gelfand_equivalence_complex (ℓ : ℕ) :
    ImagUnit.complex.L = ℂ ∧ (GammaE ImagUnit.complex ℓ).IsSplit ∧
    ∃ e : HC.Category.{0} ℓ ≌ (RepNilTarget ImagUnit.complex ℓ).FullSubcategory,
      e.functor = (HC.ClassicalComparison.hcLambda_complex_equiv (ℓ := ℓ)).inverse ⋙
        E_E ℂ ImagUnit.complex ℓ := by
  refine ⟨rfl, (GammaE_isSplit_iff _ ℓ).mpr ⟨Complex.I, Complex.I_mul_I⟩, ?_⟩
  obtain ⟨e₀, he₀⟩ := gelfand_equivalence ℂ ImagUnit.complex ℓ
  exact ⟨(HC.ClassicalComparison.hcLambda_complex_equiv (ℓ := ℓ)).symm.trans e₀, by
    rw [CategoryTheory.Equivalence.trans_functor, he₀]; rfl⟩

/-- **`rmk:classicalcases`, `E = ℝ`** (`RQ2-5.19-C2`).  `L_ℝ = ℂ`, `Γ_ℝ` is not split, the non-trivial
element of `G_ℝ` is complex conjugation (`χ_ℝ(conj) = -1`), and the two theorems at `E = ℝ` give the
real form of Gelfand's equivalence, `HC_λ(𝔤,K)_ℝ ≃ Rep^nil(Γ_ℝ)` with the functor `𝔼_ℝ`.
@census none (helper; clause `RQ2-5.19-C2`) -/
theorem gelfand_equivalence_real (ℓ : ℕ) :
    ImagUnit.real.L = ℂ ∧ ¬ (GammaE ImagUnit.real ℓ).IsSplit ∧
    ImagUnit.real.chi Complex.conjAe = -1 ∧
    ∃ e : HC ℓ ℝ ImagUnit.real ≌ (RepNilTarget ImagUnit.real ℓ).FullSubcategory,
      e.functor = E_E ℝ ImagUnit.real ℓ :=
  ⟨rfl, fun hs => ImagUnit.real_not_sqrt ((GammaE_isSplit_iff _ ℓ).mp hs),
    ImagUnit.real.chi_eq_neg_one_iff.mpr (by
      show (starRingEnd ℂ) Complex.I = -Complex.I; simp),
    gelfand_equivalence ℝ ImagUnit.real ℓ⟩

/-! ## Theorem A (`thm:introA`, `RQ2-0.01`) -/

/-- **Theorem A** (`thm:introA`).  For `λ = ℓ² ≥ 1` the functor `𝔼_ℚ` defines equivalences of abelian
categories `HC_λ(𝔰𝔩₂, SO(2))_ℚ ≃ Rep^nil(Γ_ℚ)` (`eq:HCquiverequivalence`) and
`HC_λ(𝔰𝔩₂, SO(2))_ℚ ≃ Rep^nil(S_Gelfand, R_Gelfand)` (`eq:HCspeciesequivalence`); for `λ = 0` the
analogous functor defines equivalences `HC_0(𝔰𝔩₂, SO(2))_ℚ ≃ Rep^nil(Γ_ℚ) ≃ Rep^nil(S(Γ_ℚ))`, `Γ_ℚ` the
`ℚ`-rational cyclic quiver.

@census    RQ2-0.01
@source    thm:introA
@clauses   RQ2-0.01-H1, RQ2-0.01-C1, RQ2-0.01-C2, RQ2-0.01-H2, RQ2-0.01-C3, RQ2-0.01-C4,
  RQ2-0.01-C5
@imports   none
@divergence JUSTIFIED_REFORMULATION (restatement; `EX-ORDER-INTRO`, `EX-HC`).  The conjunction of
`thm:EEQQequivalence` (`C1`, `E_Q_equivalence`), `cor:gelfandspecies` (`C2`,
`Species.species_equivalence_intrinsic`), `thm:cyclicEEQQequivalence` (`C3`, `cyclic_E_Q_equivalence`)
and `cor:cyclicspecies` (`C4`, `Species.cyclic_species_equivalence`), with `λ = ℓ² ≥ 1` as `ℓ = k + 1`.
`C4` is stated as the composite `HC_0(𝔤,K)_ℚ ≃ Rep^nil(S(Γ_ℚ))` (functor `E_E ⋙ FRestrictCyclicQ`); its
quiver↔species step `Rep^nil(Γ_ℚ) ≃ Rep^nil(S(Γ_ℚ))` is T0's `RQ2-2.29` (`RationalQuiver.FFunctor_isEquivalence`).
`C5` ("equivalences of **abelian** categories"): both sides are abelian — `HC.HC.abelian` for
`HC_λ(𝔤,K)_ℚ` and, for `Rep^nil(Γ_ℚ)`, `repNilTarget_abelian` at `E = ℚ` (the abelian structure
transported along `𝔼_ℚ`, unique as an additive structure; the same reading as `RQ2-0.02-C3`); the species
targets are equivalent to `Rep^nil(Γ_ℚ)` by the stated equivalences.
-/
theorem theoremA :
    (∀ k : ℕ, ∃ e : HC (k + 1) ℚ ImagUnit.qi ≌ (RepNilTarget ImagUnit.qi (k + 1)).FullSubcategory,
      e.functor = E_E ℚ ImagUnit.qi (k + 1)) ∧
    (∀ k : ℕ, ∃ e : HC (k + 1) ℚ ImagUnit.qi ≌
        (RationalQuivers.Species.RepNilRel (Species.SE ImagUnit.qi Species.not_sqrt_Q).toSpecies
          (Species.RE ImagUnit.qi Species.not_sqrt_Q)).FullSubcategory,
      e.functor = E_E ℚ ImagUnit.qi (k + 1) ⋙ Species.FRestrictPos ImagUnit.qi Species.not_sqrt_Q) ∧
    (∃ e : HC 0 ℚ ImagUnit.qi ≌ (RepNilTarget ImagUnit.qi 0).FullSubcategory,
      e.functor = E_E ℚ ImagUnit.qi 0) ∧
    (∃ e : HC 0 ℚ ImagUnit.qi ≌
        (RationalQuivers.Species.RepNil (Cyclic.cyclicQ (Dq := ImagUnit.qi.sqrtExt Species.hcQ)
          (Species.cardE ImagUnit.qi Species.not_sqrt_Q)).toSpecies.toSpecies).FullSubcategory,
      e.functor = E_E ℚ ImagUnit.qi 0 ⋙ Species.FRestrictCyclicQ) ∧
    (∀ ℓ : ℕ, Nonempty (Abelian (HC ℓ ℚ ImagUnit.qi)) ∧
      ∃ e : HC ℓ ℚ ImagUnit.qi ≌ (RepNilTarget ImagUnit.qi ℓ).FullSubcategory,
        e.functor = E_E ℚ ImagUnit.qi ℓ ∧
        ∃ A : Abelian (RepNilTarget ImagUnit.qi ℓ).FullSubcategory,
          @Functor.Additive _ _ _ _ A.toPreadditive HC.HC.abelianStr.toPreadditive e.inverse) :=
  ⟨fun k => E_Q_equivalence (by omega), fun k => Species.species_equivalence_intrinsic k,
    cyclic_E_Q_equivalence, Species.cyclic_species_equivalence,
    fun ℓ => ⟨HC.HC.abelian, repNilTarget_abelian ℚ ImagUnit.qi ℓ⟩⟩

end Rat

end RationalQuivers.Gelfand.Rational
