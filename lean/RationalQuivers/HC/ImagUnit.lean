module

public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.LinearAlgebra.Complex.Module

@[expose] public section

/-!
# `L_E = E(√-1)`, `G_E`, `χ_E` (`def:sqrtminusone`)

The datum `L_E = E(√-1)` with its Galois group `G_E` and sign character `χ_E` (census `RQ2-3.13`),
uniform in the two cases `√-1 ∈ E` (`L_E = E`, `G_E = 1`) and `√-1 ∉ E` (`L_E/E` quadratic).

## Main definitions / results

* `RationalQuivers.HC.ImagUnit` — `def:sqrtminusone` (census `RQ2-3.13`).
* `ImagUnit.isGalois`, `finiteDimensional`, `normal` — **derived** instances: `[L : E] ≤ 2`,
  characteristic `0`.
* `ImagUnit.chi`, `chiHom` — `χ_E : G_E → {±1}`, `σ(√-1) = χ_E(σ)√-1`, a monoid hom, **injective**.
* `ImagUnit.finrank_eq_one_of_sqrt`, `eq_one_of_sqrt` — `√-1 ∈ E` ⇒ `L_E = E`, `G_E = 1`;
  `finrank_eq_two_of_not_sqrt`, `exists_chi_neg_one_of_not_sqrt`, `conj` — `√-1 ∉ E` ⇒ quadratic,
  `c` the non-trivial element.
* `ImagUnit.ofSplit` (`L := E`), `stdNonsplit` (`L := E[x]/(x²+1)`), `std` (either), `iso` (any two
  data with the same minimal polynomial of `i` are isomorphic, `i ↦ i`), `real` (`ℂ/ℝ`), `complex`
  (`ℂ/ℂ`); `qi` (`ℚ[√-1]/ℚ`) is in `HC/Sl2.lean`, where `HC.Qi` is defined.
* the inhabitant of `RationalQuiver.gelfandOfSign_eq_gelfandOfCardTwo` hypotheses is in the
  leaf module `HC/ImagUnitQuiver.lean`.
-/

namespace RationalQuivers.HC

open Polynomial

/-- **Definition** (`def:sqrtminusone`).  Let `E` be a field of characteristic `0`.  An `ImagUnit E`
is the datum `L_E = E[√-1]`: a field `L` with an `E`-algebra structure, a chosen `i = √-1 ∈ L`
(`i * i = -1`) generating `L` over `E` (`Algebra.adjoin E {i} = ⊤`).  `G_E := Gal(L_E/E)` is
`L ≃ₐ[E] L`.  If `√-1 ∈ E` then `L_E = E` and `G_E` is trivial (`finrank_eq_one_of_sqrt`,
`eq_one_of_sqrt`); otherwise `L_E/E` is quadratic (`finrank_eq_two_of_not_sqrt`) and `c` is the
non-trivial element of `G_E` (`conj`); every `σ ∈ G_E` is determined by `σ(√-1) ∈ {±√-1}` (`ext_i`,
`apply_i`).  `IsGalois E L_E` and `FiniteDimensional E L_E` are **derived** instances.

@census    RQ2-3.13
@source    def:sqrtminusone
@clauses   RQ2-3.13-H1, RQ2-3.13-C1, RQ2-3.13-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (algebraic closure replaced by a generated extension,
disclosed).  The tex fixes `√-1` in an algebraic closure `Ē` and puts `L_E := E[√-1] ⊆ Ē`.  Lean
takes `L_E` as an abstract field generated over `E` by a root `i` of `X² + 1`; any two such data
are `E`-isomorphic, compatibly with `i` when `√-1 ∉ E` (`ImagUnit.iso`), and every such datum
embeds in `Ē` — so the choice is the tex's choice of `√-1`, made once.  Clause `C2` is mathlib's
`L ≃ₐ[E] L` (`IsGalois` derived); `C1`'s `E[√-1]` is `adjoin_eq_top`; the field `L` lives in
`Type` (universe `0`, disclosed).
-/
structure ImagUnit (E : Type) [Field E] where
  /-- the field `L_E` -/
  L : Type
  [field : Field L]
  [algebra : Algebra E L]
  /-- the chosen `√-1 ∈ L_E` -/
  i : L
  i_mul_i : i * i = -1
  adjoin_eq_top : Algebra.adjoin E {i} = ⊤

attribute [instance] ImagUnit.field ImagUnit.algebra

namespace ImagUnit

variable {E : Type} [Field E] (D : ImagUnit E)

theorem isIntegral_i : IsIntegral E D.i :=
  ⟨X ^ 2 + 1, by
    have : (X ^ 2 + 1 : E[X]) = X ^ 2 + C 1 := by simp
    rw [this]; exact monic_X_pow_add_C 1 two_ne_zero, by simp [sq, D.i_mul_i]⟩

/-- The power basis `1, i (, …)` of `L_E/E`.  @census none (helper) -/
noncomputable def powerBasis : PowerBasis E D.L :=
  PowerBasis.ofAdjoinEqTop D.isIntegral_i D.adjoin_eq_top

/-- **Derived**: `L_E/E` is finite.  @census none (helper) -/
instance finiteDimensional : FiniteDimensional E D.L := D.powerBasis.finite

theorem finrank_le_two : Module.finrank E D.L ≤ 2 := by
  rw [D.powerBasis.finrank]
  show (minpoly E D.i).natDegree ≤ 2
  have hq : (X ^ 2 + 1 : E[X]) = X ^ 2 + C 1 := by simp
  have hp : (X ^ 2 + 1 : E[X]) ≠ 0 := by
    rw [hq]; exact (monic_X_pow_add_C 1 two_ne_zero).ne_zero
  have hd : minpoly E D.i ∣ (X ^ 2 + 1 : E[X]) :=
    minpoly.dvd E D.i (by simp [sq, D.i_mul_i])
  calc (minpoly E D.i).natDegree ≤ (X ^ 2 + 1 : E[X]).natDegree :=
        natDegree_le_of_dvd hd hp
    _ = 2 := by
        have : (X ^ 2 + 1 : E[X]) = X ^ 2 + C 1 := by simp
        rw [this, natDegree_X_pow_add_C]

/-- **Derived**: `L_E/E` is normal (degree `≤ 2`, as mathlib's `IsQuadraticExtension.normal`).
@census none (helper) -/
instance normal : Normal E D.L where
  splits' := by
    intro x
    obtain h | h := le_iff_lt_or_eq.mp ((minpoly.natDegree_le x).trans D.finrank_le_two)
    · exact Splits.of_natDegree_le_one <| natDegree_map_le.trans (by omega)
    · exact Splits.of_natDegree_eq_two ((natDegree_map _).trans h)
        ((eval_map_algebraMap _ _).trans (minpoly.aeval E x))

section CharZero

variable [CharZero E]
set_option linter.unusedSectionVars false

/-- **Derived**: `L_E/E` is Galois.  @census none (helper) -/
instance isGalois : IsGalois E D.L := ⟨⟩

instance charZero : CharZero D.L :=
  charZero_of_injective_algebraMap (algebraMap E D.L).injective

theorem i_ne_zero : D.i ≠ 0 := by
  intro h; have := D.i_mul_i; rw [h, mul_zero] at this
  exact (neg_ne_zero.mpr (one_ne_zero (α := D.L))) this.symm

theorem i_ne_neg_i : D.i ≠ -D.i := by
  intro h
  have h2 : (2 : D.L) * D.i = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h' | h'
  · exact two_ne_zero h'
  · exact D.i_ne_zero h'

/-- Every `σ ∈ G_E` sends `√-1` to `±√-1` (`RQ2-3.13-C5`).
@census none (auxiliary; discharges clause `RQ2-3.13-C5` of `RQ2-3.13`)
@clauses   RQ2-3.13-C5 -/
theorem apply_i (σ : D.L ≃ₐ[E] D.L) : σ D.i = D.i ∨ σ D.i = -D.i := by
  have h : (σ D.i - D.i) * (σ D.i + D.i) = 0 := by
    have h1 : σ D.i * σ D.i = -1 := by rw [← map_mul, D.i_mul_i, map_neg, map_one]
    linear_combination h1 - D.i_mul_i
  rcases mul_eq_zero.mp h with h' | h'
  · left; exact sub_eq_zero.mp h'
  · right; exact eq_neg_of_add_eq_zero_left h'

/-- **`χ_E : G_E → {±1}`**, `σ(√-1) = χ_E(σ)√-1`.  @census none (helper) -/
noncomputable def chi (σ : D.L ≃ₐ[E] D.L) : ℤˣ := by
  classical exact if σ D.i = D.i then 1 else -1

theorem chi_eq_one_iff {σ : D.L ≃ₐ[E] D.L} : D.chi σ = 1 ↔ σ D.i = D.i := by
  unfold chi; split_ifs with h <;> simp [h]

theorem chi_eq_neg_one_iff {σ : D.L ≃ₐ[E] D.L} : D.chi σ = -1 ↔ σ D.i = -D.i := by
  unfold chi; split_ifs with h
  · simp only [h]; constructor
    · intro h'; exact absurd h' (by decide)
    · intro h'; exact absurd h' D.i_ne_neg_i
  · simpa using (D.apply_i σ).resolve_left h

theorem chi_cases (σ : D.L ≃ₐ[E] D.L) : D.chi σ = 1 ∨ D.chi σ = -1 := by
  rcases D.apply_i σ with h | h
  · exact Or.inl (D.chi_eq_one_iff.mpr h)
  · exact Or.inr (D.chi_eq_neg_one_iff.mpr h)

/-- `σ i = χ σ • i`.  @census none (helper) -/
theorem chi_spec (σ : D.L ≃ₐ[E] D.L) : σ D.i = ((D.chi σ : ℤ) : D.L) * D.i := by
  rcases D.chi_cases σ with h | h
  · rw [D.chi_eq_one_iff.mp h, h]; simp
  · rw [D.chi_eq_neg_one_iff.mp h, h]; simp

/-- `σ ∈ G_E` is **determined** by `σ(√-1)` (`RQ2-3.13-C5`).
@census none (auxiliary; discharges clause `RQ2-3.13-C5` of `RQ2-3.13`)
@clauses   RQ2-3.13-C5 -/
theorem ext_i {σ τ : D.L ≃ₐ[E] D.L} (h : σ D.i = τ D.i) : σ = τ := by
  apply AlgEquiv.coe_algHom_injective
  exact AlgHom.ext_of_adjoin_eq_top D.adjoin_eq_top (by
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx; exact h)

/-- **`χ_E` is injective.**  @census none (helper) -/
theorem chi_injective : Function.Injective D.chi := by
  intro σ τ h
  apply D.ext_i
  rw [D.chi_spec, D.chi_spec, h]

theorem chi_one : D.chi 1 = 1 := D.chi_eq_one_iff.mpr rfl

theorem chi_mul (σ τ : D.L ≃ₐ[E] D.L) : D.chi (σ * τ) = D.chi σ * D.chi τ := by
  have key : (σ * τ) D.i = (((D.chi σ * D.chi τ : ℤˣ) : ℤ) : D.L) * D.i := by
    show σ (τ D.i) = _
    rw [D.chi_spec τ, map_mul, map_intCast, D.chi_spec σ]
    push_cast; ring
  rcases D.chi_cases σ with hσ | hσ <;> rcases D.chi_cases τ with hτ | hτ <;>
    rw [hσ, hτ] at key ⊢ <;> norm_num at key ⊢
  · exact D.chi_eq_one_iff.mpr key
  · exact D.chi_eq_neg_one_iff.mpr key
  · exact D.chi_eq_neg_one_iff.mpr key
  · exact D.chi_eq_one_iff.mpr key

theorem chi_eq_neg_one_iff_ne_one {σ : D.L ≃ₐ[E] D.L} : D.chi σ = -1 ↔ σ ≠ 1 := by
  constructor
  · rintro h rfl; rw [chi_one] at h; exact absurd h (by decide)
  · intro h; rcases D.chi_cases σ with h' | h'
    · exact absurd (D.chi_injective (h'.trans D.chi_one.symm)) h
    · exact h'

theorem eq_of_chi_neg_one {σ τ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = -1) (hτ : D.chi τ = -1) :
    σ = τ := D.chi_injective (hσ.trans hτ.symm)

theorem eq_one_of_chi_one {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = 1) : σ = 1 :=
  D.chi_injective (hσ.trans D.chi_one.symm)

/-- Every element of `G_E` is an involution.  @census none (helper) -/
theorem mul_self (σ : D.L ≃ₐ[E] D.L) : σ * σ = 1 := by
  apply D.eq_one_of_chi_one
  rw [chi_mul]; rcases D.chi_cases σ with h | h <;> rw [h] <;> decide

/-- `|G_E| = 2` when some `σ` has `χ σ = -1`.  @census none (helper) -/
theorem card_gal_of (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) :
    Nat.card (D.L ≃ₐ[E] D.L) = 2 := by
  obtain ⟨σ, hσ⟩ := h
  rw [Nat.card_eq_two_iff]
  refine ⟨1, σ, (D.chi_eq_neg_one_iff_ne_one.mp hσ).symm, ?_⟩
  ext τ; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  rcases D.chi_cases τ with h' | h'
  · exact Or.inl (D.eq_one_of_chi_one h')
  · exact Or.inr (D.eq_of_chi_neg_one h' hσ)

/-- **`√-1 ∈ E` ⇒ `G_E = 1`**: then `χ ≡ 1`.  @census none (helper) -/
theorem chi_eq_one_of_sqrt (h : ∃ a : E, a * a = -1) (σ : D.L ≃ₐ[E] D.L) : D.chi σ = 1 := by
  obtain ⟨a, ha⟩ := h
  have ha' : algebraMap E D.L a * algebraMap E D.L a = -1 := by
    rw [← map_mul, ha, map_neg, map_one]
  rcases D.chi_cases σ with h | h
  · exact h
  · exfalso
    have hσi := D.chi_eq_neg_one_iff.mp h
    -- `i = ±a`, both fixed by `σ`
    have hfix : σ (algebraMap E D.L a) = algebraMap E D.L a := σ.commutes a
    have hia : (D.i - algebraMap E D.L a) * (D.i + algebraMap E D.L a) = 0 := by
      linear_combination D.i_mul_i - ha'
    rcases mul_eq_zero.mp hia with h' | h'
    · have hi : D.i = algebraMap E D.L a := sub_eq_zero.mp h'
      have : σ D.i = D.i := by rw [hi, hfix]
      exact D.i_ne_neg_i (this.symm.trans hσi)
    · have hi : D.i = -algebraMap E D.L a := eq_neg_of_add_eq_zero_left h'
      have : σ D.i = D.i := by rw [hi, map_neg, hfix]
      exact D.i_ne_neg_i (this.symm.trans hσi)


/-! ### `χ_E` as a monoid hom; the two cases `√-1 ∈ E`, `√-1 ∉ E` -/

/-- `χ_E : G_E →* ℤˣ`.  @census none (helper) -/
noncomputable def chiHom : (D.L ≃ₐ[E] D.L) →* ℤˣ where
  toFun := D.chi
  map_one' := D.chi_one
  map_mul' := D.chi_mul

theorem chiHom_apply (σ : D.L ≃ₐ[E] D.L) : D.chiHom σ = D.chi σ := rfl

theorem chiHom_injective : Function.Injective D.chiHom := D.chi_injective

/-- `√-1 ∈ E` ⇒ `G_E` is trivial (`RQ2-3.13-C3`).
@census none (auxiliary; discharges clause `RQ2-3.13-C3` of `RQ2-3.13`)
@clauses   RQ2-3.13-C3 -/
theorem eq_one_of_sqrt (h : ∃ a : E, a * a = -1) (σ : D.L ≃ₐ[E] D.L) : σ = 1 :=
  D.eq_one_of_chi_one (D.chi_eq_one_of_sqrt h σ)

/-- `√-1 ∈ E` ⇒ `i` lies in `E`.  @census none (helper) -/
theorem i_mem_range_of_sqrt (h : ∃ a : E, a * a = -1) :
    D.i ∈ Set.range (algebraMap E D.L) := by
  obtain ⟨a, ha⟩ := h
  have ha' : algebraMap E D.L a * algebraMap E D.L a = -1 := by
    rw [← map_mul, ha, map_neg, map_one]
  have hia : (D.i - algebraMap E D.L a) * (D.i + algebraMap E D.L a) = 0 := by
    linear_combination D.i_mul_i - ha'
  rcases mul_eq_zero.mp hia with h' | h'
  · exact ⟨a, (sub_eq_zero.mp h').symm⟩
  · exact ⟨-a, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left h').symm⟩

/-- `√-1 ∈ E` ⇒ `algebraMap E L_E` is **bijective**, i.e. `L_E = E` (`RQ2-3.13-C3`).
@census none (auxiliary; discharges clause `RQ2-3.13-C3` of `RQ2-3.13`)
@clauses   RQ2-3.13-C3 -/
theorem algebraMap_bijective_of_sqrt (h : ∃ a : E, a * a = -1) :
    Function.Bijective (algebraMap E D.L) := by
  refine ⟨(algebraMap E D.L).injective, ?_⟩
  obtain ⟨a, ha⟩ := D.i_mem_range_of_sqrt h
  have hbot : Algebra.adjoin E {D.i} ≤ (⊥ : Subalgebra E D.L) := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact ⟨a, ha⟩
  intro x
  have hx : x ∈ (⊥ : Subalgebra E D.L) := hbot (D.adjoin_eq_top ▸ Algebra.mem_top)
  exact Algebra.mem_bot.mp hx

theorem finrank_eq_one_of_sqrt (h : ∃ a : E, a * a = -1) : Module.finrank E D.L = 1 := by
  have hbot : (⊥ : Subalgebra E D.L) = ⊤ := by
    rw [eq_top_iff]; intro x _
    obtain ⟨a, rfl⟩ := (D.algebraMap_bijective_of_sqrt h).2 x
    exact Subalgebra.algebraMap_mem _ a
  exact Subalgebra.bot_eq_top_iff_finrank_eq_one.mp hbot

/-- `X² + 1` is irreducible over `E` when `√-1 ∉ E`.  @census none (helper) -/
theorem irreducible_X_sq_add_one {F : Type} [Field F] (h : ¬ ∃ a : F, a * a = -1) :
    Irreducible (X ^ 2 + 1 : F[X]) := by
  have hq : (X ^ 2 + 1 : F[X]) = X ^ 2 + C 1 := by simp
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [hq, natDegree_X_pow_add_C]; simp
  · intro x hx
    apply h
    refine ⟨x, ?_⟩
    have : x ^ 2 + 1 = 0 := by simpa using hx
    linear_combination this

/-- `√-1 ∉ E` ⇒ the minimal polynomial of `i` is `X² + 1`.  @census none (helper) -/
theorem minpoly_i_of_not_sqrt (h : ¬ ∃ a : E, a * a = -1) :
    minpoly E D.i = X ^ 2 + 1 := by
  have hq : (X ^ 2 + 1 : E[X]) = X ^ 2 + C 1 := by simp
  refine (minpoly.eq_of_irreducible_of_monic (irreducible_X_sq_add_one h)
    (by simp [sq, D.i_mul_i]) ?_).symm
  rw [hq]; exact monic_X_pow_add_C 1 two_ne_zero

/-- `√-1 ∉ E` ⇒ `L_E/E` is **quadratic** (`RQ2-3.13-C4`).
@census none (auxiliary; discharges clause `RQ2-3.13-C4` of `RQ2-3.13`)
@clauses   RQ2-3.13-C4 -/
theorem finrank_eq_two_of_not_sqrt (h : ¬ ∃ a : E, a * a = -1) : Module.finrank E D.L = 2 := by
  rw [D.powerBasis.finrank]
  show (minpoly E D.i).natDegree = 2
  rw [D.minpoly_i_of_not_sqrt h]
  have : (X ^ 2 + 1 : E[X]) = X ^ 2 + C 1 := by simp
  rw [this, natDegree_X_pow_add_C]

/-- `√-1 ∉ E` ⇒ `|G_E| = 2`.  @census none (helper) -/
theorem card_gal_of_not_sqrt (h : ¬ ∃ a : E, a * a = -1) :
    Nat.card (D.L ≃ₐ[E] D.L) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, D.finrank_eq_two_of_not_sqrt h]

/-- `√-1 ∉ E` ⇒ complex conjugation exists: some `σ` has `χ_E(σ) = -1`.  @census none (helper) -/
theorem exists_chi_neg_one_of_not_sqrt (h : ¬ ∃ a : E, a * a = -1) :
    ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1 := by
  have hc : Nat.card (D.L ≃ₐ[E] D.L) = 2 := D.card_gal_of_not_sqrt h
  obtain ⟨σ, τ, hστ, -⟩ := Nat.card_eq_two_iff.mp hc
  by_cases hσ : σ = 1
  · subst hσ
    exact ⟨τ, D.chi_eq_neg_one_iff_ne_one.mpr (Ne.symm hστ)⟩
  · exact ⟨σ, D.chi_eq_neg_one_iff_ne_one.mpr hσ⟩

/-- The dichotomy: `√-1 ∈ E` iff `χ_E ≡ 1`.  @census none (helper) -/
theorem exists_chi_neg_one_iff : (∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) ↔ ¬ ∃ a : E, a * a = -1 := by
  constructor
  · rintro ⟨σ, hσ⟩ hs
    rw [D.chi_eq_one_of_sqrt hs σ] at hσ
    exact absurd hσ (by decide)
  · exact D.exists_chi_neg_one_of_not_sqrt

/-- **Complex conjugation** `c ∈ G_E` for `√-1 ∉ E`: the element with `χ_E(c) = -1`
(`RQ2-3.13-C4`).
@census none (auxiliary; discharges clause `RQ2-3.13-C4` of `RQ2-3.13`)
@clauses   RQ2-3.13-C4 -/
noncomputable def conj (h : ¬ ∃ a : E, a * a = -1) : D.L ≃ₐ[E] D.L :=
  (D.exists_chi_neg_one_of_not_sqrt h).choose

theorem chi_conj (h : ¬ ∃ a : E, a * a = -1) : D.chi (D.conj h) = -1 :=
  (D.exists_chi_neg_one_of_not_sqrt h).choose_spec

theorem conj_i (h : ¬ ∃ a : E, a * a = -1) : D.conj h D.i = -D.i :=
  D.chi_eq_neg_one_iff.mp (D.chi_conj h)

/-- `c` is the **non-trivial** element: every `σ ≠ 1` is `c` (`RQ2-3.13-C4`).
@census none (auxiliary; discharges clause `RQ2-3.13-C4` of `RQ2-3.13`)
@clauses   RQ2-3.13-C4 -/
theorem eq_conj_of_ne_one (h : ¬ ∃ a : E, a * a = -1) {σ : D.L ≃ₐ[E] D.L} (hσ : σ ≠ 1) :
    σ = D.conj h :=
  D.eq_of_chi_neg_one (D.chi_eq_neg_one_iff_ne_one.mpr hσ) (D.chi_conj h)

/-! ### Isomorphism of data -/

/-- **`L_E` is unique up to `i`-compatible isomorphism** (when the minimal polynomials of the two
square roots agree, in particular always when `√-1 ∉ E`, `minpoly_i_of_not_sqrt`).
@census none (helper) -/
noncomputable def iso (D' : ImagUnit E) (h : minpoly E D.i = minpoly E D'.i) : D.L ≃ₐ[E] D'.L :=
  D.powerBasis.equivOfMinpoly D'.powerBasis h

theorem iso_i (D' : ImagUnit E) (h : minpoly E D.i = minpoly E D'.i) : D.iso D' h D.i = D'.i :=
  D.powerBasis.equivOfMinpoly_gen D'.powerBasis h

theorem minpoly_eq_of_not_sqrt (D' : ImagUnit E) (h : ¬ ∃ a : E, a * a = -1) :
    minpoly E D.i = minpoly E D'.i := by
  rw [D.minpoly_i_of_not_sqrt h, D'.minpoly_i_of_not_sqrt h]

end CharZero

end ImagUnit

/-! ### Constructions -/

/-- **`√-1 ∈ E`**: `L_E := E`, `i := a` for a chosen `a` with `a² = -1`.  @census none (helper) -/
noncomputable def ImagUnit.ofSplit {E : Type} [Field E] (a : E) (ha : a * a = -1) : ImagUnit E where
  L := E
  i := a
  i_mul_i := ha
  adjoin_eq_top := by
    rw [eq_top_iff]; intro x _
    exact Subalgebra.algebraMap_mem _ x

/-- **`√-1 ∉ E`**: `L_E := E[x]/(x² + 1)`, `i := x`.  @census none (helper) -/
noncomputable def ImagUnit.stdNonsplit (E : Type) [Field E] (h : ¬ ∃ a : E, a * a = -1) :
    ImagUnit E :=
  haveI : Fact (Irreducible (X ^ 2 + 1 : E[X])) := ⟨ImagUnit.irreducible_X_sq_add_one h⟩
  { L := AdjoinRoot (X ^ 2 + 1 : E[X])
    i := AdjoinRoot.root (X ^ 2 + 1 : E[X])
    i_mul_i := by
      have h0 := AdjoinRoot.eval₂_root (X ^ 2 + 1 : E[X])
      simp only [eval₂_add, eval₂_X_pow, eval₂_one] at h0
      linear_combination h0
    adjoin_eq_top := AdjoinRoot.adjoinRoot_eq_top }

/-- **The standard datum** `L_E = E(√-1)`: `ofSplit` if `√-1 ∈ E`, else `stdNonsplit`.
@census none (helper) -/
noncomputable def ImagUnit.std (E : Type) [Field E] : ImagUnit E := by
  classical
  exact if h : ∃ a : E, a * a = -1 then ImagUnit.ofSplit h.choose h.choose_spec
    else ImagUnit.stdNonsplit E h

/-! ### The two classical instances -/

/-- **`ℂ/ℝ`**, `i = I`.  @census none (helper) -/
noncomputable def ImagUnit.real : ImagUnit ℝ where
  L := ℂ
  i := Complex.I
  i_mul_i := Complex.I_mul_I
  adjoin_eq_top := by
    rw [eq_top_iff]; intro z _
    rw [← Complex.re_add_im z]
    refine Subalgebra.add_mem _ ?_ (Subalgebra.mul_mem _ ?_ (Algebra.subset_adjoin rfl))
    · exact Subalgebra.algebraMap_mem _ z.re
    · exact Subalgebra.algebraMap_mem _ z.im

/-- **`ℂ/ℂ`** (`√-1 ∈ E`, `G_E = 1`).  @census none (helper) -/
noncomputable def ImagUnit.complex : ImagUnit ℂ where
  L := ℂ
  i := Complex.I
  i_mul_i := Complex.I_mul_I
  adjoin_eq_top := by
    rw [eq_top_iff]; intro z _
    exact Subalgebra.algebraMap_mem _ z

/-- The derived instance at `ImagUnit.real` **is** `IsGalois ℝ ℂ`.  @census none (helper) -/
theorem ImagUnit.real_isGalois : IsGalois ℝ ℂ := ImagUnit.isGalois ImagUnit.real

example : IsGalois ℝ ImagUnit.real.L := inferInstance
example : FiniteDimensional ℝ ImagUnit.real.L := inferInstance

/-- Over `ℝ` there is a `σ` with `χ σ = -1` (complex conjugation).  @census none (helper) -/
theorem ImagUnit.real_exists_neg : ∃ σ : ImagUnit.real.L ≃ₐ[ℝ] ImagUnit.real.L,
    ImagUnit.real.chi σ = -1 :=
  ⟨Complex.conjAe, ImagUnit.real.chi_eq_neg_one_iff.mpr (by
    show (starRingEnd ℂ) Complex.I = -Complex.I; simp)⟩

/-- Over `ℂ`, `χ ≡ 1`.  @census none (helper) -/
theorem ImagUnit.complex_chi (σ : ImagUnit.complex.L ≃ₐ[ℂ] ImagUnit.complex.L) :
    ImagUnit.complex.chi σ = 1 :=
  ImagUnit.complex.chi_eq_one_of_sqrt ⟨Complex.I, Complex.I_mul_I⟩ σ


/-- **`IsGalois ℝ ℂ`, derived**: the instance `ImagUnit.isGalois` at `ImagUnit.real`, whose
`L` is `ℂ`.  @census none (helper) -/
example : IsGalois ℝ ℂ := ImagUnit.real_isGalois

/-- `√-1 ∉ ℝ`.  @census none (helper) -/
theorem ImagUnit.real_not_sqrt : ¬ ∃ a : ℝ, a * a = -1 := by
  rintro ⟨a, ha⟩; nlinarith [mul_self_nonneg a]

end RationalQuivers.HC
