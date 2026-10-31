module

public import RationalQuivers.Gelfand.TwistedForms
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

/-!
# Twisted forms without `√-1`: G5 inhabitants of variant (ii) (stage T6)

Since the v2 amendments T2-a2/T3-a1/T4-a1/T5-a1 (R-PROC-4, written authorization 2026-10-18,
`workflow/reports/AUTHOR-QUEUE.md`; plan `workflow/v2/analysis/VARIANT-II-T4B-PLAN.md` §1) the bundle
`SqrtNegOneExt E` is root-free: it is exactly a quadratic Galois extension `D'/E`, and
`gelfand_equivalence_twisted` (`thm:twistedEEequivalence`, `Gelfand/TwistedForms.lean`) holds for
every such `D'`, with no proof edited.  That generality is asserted by the type; this module
**instantiates** it at extensions that do *not* contain `√-1`, so that the strengthening reaches
categories the variant-(i) statement did not (G5).

## Main definitions / results

* `SqrtNegOneExt.ofNonSquare d hd` — `E(√d) := AdjoinRoot (X² - C d)` for a non-square `d ∈ E`, as a
  `SqrtNegOneExt E`; it generalizes the constructed `E(√-1)` (`Ei`, `SqrtNegOneExt.std`), which is
  the case `d = -1`.  `ofNonSquare.root`, `ofNonSquare.root_mul_root`: the root `√d`.
* `SqrtNegOneExt.not_exists_sqrt_neg_one` — a quadratic `D' = E(r)`, `r² = d`, contains `√-1` only
  if `-1` or `-d` is a square in `E`.  Coordinate-free: from `c(s) = -s`, `c(r) = -r`, so
  `s r ∈ E` and `(s r)² = -d`.
* `qSqrtNegThree`, `qSqrtTwo` — `ℚ(√-3)` and `ℚ(√2)`, with `qSqrtNegThree_no_sqrt_neg_one`,
  `qSqrtTwo_no_sqrt_neg_one`: **`√-1 ∉ D'`**, proved.  `ℚ(√-3) ⊗_ℚ ℝ ≅ ℂ`, so `K_{ℚ(√-3)/ℚ}`
  (the conic `x² + 3y² = 1`) is a `ℚ`-form of the real `SO(2)` other than `SO(2)_ℚ` (the remark
  after `rmk:twistedforms` in the manuscript, `rmk:formsofSO2`; not formalized); `ℚ(√2)` is a real
  quadratic field, whose norm-one torus splits over `ℝ`.
* `gelfand_equivalence_twisted_sqrtNegThree`, `gelfand_equivalence_twisted_sqrtTwo` —
  `thm:twistedEEequivalence` instantiated at those two extensions.

@census none (G5 inhabitants of variant (ii); stage T6)
-/

namespace RationalQuivers.Gelfand

open Polynomial

universe u

/-! ## `E(√d)` for a non-square `d` -/

section OfNonSquare

variable {E : Type u} [Field E]

/-- `X² - C d ∈ E[X]`.  @census none (helper) -/
noncomputable abbrev nonSquarePoly (d : E) : E[X] := X ^ 2 - C d

/-- `X² - C d` is irreducible over `E` when `d` is not a square in `E`.  @census none (helper) -/
theorem irreducible_nonSquarePoly (d : E) (hd : ∀ b : E, b * b ≠ d) :
    Irreducible (nonSquarePoly d) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => hd b (by rw [← hb]; ring))

variable [CharZero E]

/-- **`E(√d)` as a `SqrtNegOneExt E`**, for a non-square `d ∈ E`: the carrier is
`AdjoinRoot (X² - C d)`, a quadratic, hence (characteristic `0`) Galois, extension of `E`.  For
`d = -1` this is `SqrtNegOneExt.std E` up to the presentation of the field.  In general the carrier
need **not** contain `√-1` (`not_exists_sqrt_neg_one`), which the root-free structure now allows.

@census none (G5 inhabitant of the root-free `SqrtNegOneExt`; stage T6) -/
noncomputable def SqrtNegOneExt.ofNonSquare (d : E) (hd : ∀ b : E, b * b ≠ d) : SqrtNegOneExt E :=
  haveI : Fact (Irreducible (nonSquarePoly d)) := ⟨irreducible_nonSquarePoly d hd⟩
  haveI hfin : FiniteDimensional E (AdjoinRoot (nonSquarePoly d)) :=
    (AdjoinRoot.powerBasis (K := E) (f := nonSquarePoly d)
      (Fact.out (p := Irreducible (nonSquarePoly d))).ne_zero).finite
  have hrank : Module.finrank E (AdjoinRoot (nonSquarePoly d)) = 2 := by
    rw [(AdjoinRoot.powerBasis (K := E) (f := nonSquarePoly d)
          (Fact.out (p := Irreducible (nonSquarePoly d))).ne_zero).finrank,
        AdjoinRoot.powerBasis_dim]
    exact natDegree_X_pow_sub_C
  haveI : Algebra.IsQuadraticExtension E (AdjoinRoot (nonSquarePoly d)) := ⟨hrank⟩
  { carrier := AdjoinRoot (nonSquarePoly d)
    card_gal := by rw [IsGalois.card_aut_eq_finrank, hrank] }

@[simp] theorem SqrtNegOneExt.ofNonSquare_carrier (d : E) (hd : ∀ b : E, b * b ≠ d) :
    (SqrtNegOneExt.ofNonSquare d hd).carrier = AdjoinRoot (nonSquarePoly d) := rfl

/-- The root `√d ∈ E(√d)`.  @census none (helper) -/
noncomputable def SqrtNegOneExt.ofNonSquare.root (d : E) (hd : ∀ b : E, b * b ≠ d) :
    (SqrtNegOneExt.ofNonSquare d hd).carrier :=
  AdjoinRoot.root (nonSquarePoly d)

/-- `√d · √d = d`.  @census none (helper) -/
theorem SqrtNegOneExt.ofNonSquare.root_mul_root (d : E) (hd : ∀ b : E, b * b ≠ d) :
    root d hd * root d hd = algebraMap E (SqrtNegOneExt.ofNonSquare d hd).carrier d := by
  haveI : Fact (Irreducible (nonSquarePoly d)) := ⟨irreducible_nonSquarePoly d hd⟩
  have h0 : (AdjoinRoot.root (nonSquarePoly d)) ^ 2
      - (algebraMap E (AdjoinRoot (nonSquarePoly d))) d = 0 := by
    simpa using AdjoinRoot.eval₂_root (nonSquarePoly d)
  have h1 := sub_eq_zero.mp h0
  show AdjoinRoot.root (nonSquarePoly d) * AdjoinRoot.root (nonSquarePoly d)
    = algebraMap E (AdjoinRoot (nonSquarePoly d)) d
  rw [← h1]; ring

end OfNonSquare

/-! ## When does a quadratic `D'` contain `√-1`? -/

section NoSqrt

variable {E : Type u} [Field E] [CharZero E] (D : SqrtNegOneExt E)

/-- An element fixed by `c` lies in `E`.  @census none (helper) -/
theorem SqrtNegOneExt.exists_algebraMap_of_conj_eq {x : D.carrier} (h : D.conj x = x) :
    ∃ e : E, algebraMap E D.carrier e = x := by
  have hfix : ∀ σ : D.carrier ≃ₐ[E] D.carrier, σ x = x := by
    intro σ
    by_cases hσ : σ = 1
    · rw [hσ]; rfl
    · rw [SqrtNegOneExt.eq_conj_of_ne_one D hσ]; exact h
  exact (IsGalois.mem_range_algebraMap_iff_fixed (F := E) x).mpr hfix

/-- `c` negates every square root `x ∈ D'` of a non-square `a ∈ E`.  @census none (helper) -/
theorem SqrtNegOneExt.conj_eq_neg_of_mul_self {x : D.carrier} {a : E}
    (hx : x * x = algebraMap E D.carrier a) (ha : ∀ b : E, b * b ≠ a) : D.conj x = -x := by
  have hsq : D.conj x * D.conj x = x * x := by
    rw [← map_mul, hx, AlgEquiv.commutes]
  have hfac : (D.conj x - x) * (D.conj x + x) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exfalso
    obtain ⟨b, hb⟩ := D.exists_algebraMap_of_conj_eq (sub_eq_zero.mp h)
    apply ha b
    apply (algebraMap E D.carrier).injective
    rw [map_mul, hb, hx]
  · exact eq_neg_of_add_eq_zero_left h

/-- **`√-1 ∈ D'` forces `-1` or `-d` to be a square in `E`**, for `D' = E(r)`, `r² = d` a
non-square.  Coordinate-free: `c(s) = -s` and `c(r) = -r`, so `c(s r) = s r`, i.e. `s r ∈ E`, and
`(s r)² = -d`.  @census none (helper; G5) -/
theorem SqrtNegOneExt.not_exists_sqrt_neg_one {r : D.carrier} {d : E}
    (hr : r * r = algebraMap E D.carrier d) (hd : ∀ b : E, b * b ≠ d)
    (h1 : ∀ b : E, b * b ≠ -1) (h2 : ∀ b : E, b * b ≠ -d) :
    ¬ ∃ s : D.carrier, s * s = -1 := by
  rintro ⟨s, hs⟩
  have hs' : s * s = algebraMap E D.carrier (-1) := by rw [hs, map_neg, map_one]
  have hcs : D.conj s = -s := D.conj_eq_neg_of_mul_self hs' h1
  have hcr : D.conj r = -r := D.conj_eq_neg_of_mul_self hr hd
  have hfix : D.conj (s * r) = s * r := by rw [map_mul, hcs, hcr]; ring
  obtain ⟨e, he⟩ := D.exists_algebraMap_of_conj_eq hfix
  apply h2 e
  apply (algebraMap E D.carrier).injective
  rw [map_mul, he, map_neg, ← hr]
  linear_combination (r * r) * hs

end NoSqrt

/-! ## Inhabitants at `E = ℚ`: `ℚ(√-3)` and `ℚ(√2)` -/

section Rat

/-- `-3` is not a square in `ℚ`.  @census none (helper) -/
theorem rat_mul_self_ne_neg_three : ∀ b : ℚ, b * b ≠ -3 :=
  fun b hb => by nlinarith [mul_self_nonneg b]

/-- `-2` is not a square in `ℚ`.  @census none (helper) -/
theorem rat_mul_self_ne_neg_two : ∀ b : ℚ, b * b ≠ -2 :=
  fun b hb => by nlinarith [mul_self_nonneg b]

/-- `-1` is not a square in `ℚ`.  @census none (helper) -/
theorem rat_mul_self_ne_neg_one : ∀ b : ℚ, b * b ≠ -1 :=
  fun b hb => by nlinarith [mul_self_nonneg b]

/-- A prime `p` is not a square in `ℚ` (`√p` is irrational).  @census none (helper) -/
theorem rat_mul_self_ne_prime {p : ℕ} (hp : p.Prime) : ∀ b : ℚ, b * b ≠ p := by
  intro b hb
  apply Nat.Prime.irrational_sqrt hp
  refine ⟨|b|, ?_⟩
  have h : ((p : ℕ) : ℝ) = (b : ℝ) * b := by exact_mod_cast hb.symm
  rw [h, Real.sqrt_mul_self_eq_abs]
  push_cast; rfl

/-- `2` is not a square in `ℚ`.  @census none (helper) -/
theorem rat_mul_self_ne_two : ∀ b : ℚ, b * b ≠ 2 :=
  fun b hb => rat_mul_self_ne_prime Nat.prime_two b (by rw [hb]; norm_num)

/-- `3 = -(-3)` is not a square in `ℚ` (stated as `- -3`, the form `not_exists_sqrt_neg_one` asks for at
`d = -3`).  @census none (helper) -/
theorem rat_mul_self_ne_three : ∀ b : ℚ, b * b ≠ - -3 :=
  fun b hb => rat_mul_self_ne_prime Nat.prime_three b (by rw [hb]; norm_num)

/-- **`ℚ(√-3)`**, an imaginary quadratic field other than `ℚ(√-1)`.
@census none (G5 inhabitant; stage T6) -/
noncomputable def qSqrtNegThree : SqrtNegOneExt ℚ :=
  SqrtNegOneExt.ofNonSquare (-3) rat_mul_self_ne_neg_three

/-- **`√-1 ∉ ℚ(√-3)`**: neither `-1` nor `3` is a square in `ℚ`.
@census none (G5: the inhabitant is outside the variant-(i) scope `√-1 ∈ D'`) -/
theorem qSqrtNegThree_no_sqrt_neg_one : ¬ ∃ s : qSqrtNegThree.carrier, s * s = -1 :=
  qSqrtNegThree.not_exists_sqrt_neg_one
    (SqrtNegOneExt.ofNonSquare.root_mul_root (-3) rat_mul_self_ne_neg_three)
    rat_mul_self_ne_neg_three rat_mul_self_ne_neg_one
    rat_mul_self_ne_three

/-- **`ℚ(√2)`**, a real quadratic field.  @census none (G5 inhabitant; stage T6) -/
noncomputable def qSqrtTwo : SqrtNegOneExt ℚ :=
  SqrtNegOneExt.ofNonSquare 2 rat_mul_self_ne_two

/-- **`√-1 ∉ ℚ(√2)`**: neither `-1` nor `-2` is a square in `ℚ`.
@census none (G5: the inhabitant is outside the variant-(i) scope `√-1 ∈ D'`) -/
theorem qSqrtTwo_no_sqrt_neg_one : ¬ ∃ s : qSqrtTwo.carrier, s * s = -1 :=
  qSqrtTwo.not_exists_sqrt_neg_one
    (SqrtNegOneExt.ofNonSquare.root_mul_root 2 rat_mul_self_ne_two)
    rat_mul_self_ne_two rat_mul_self_ne_neg_one
    rat_mul_self_ne_neg_two

/-- **`thm:twistedEEequivalence` at `E = ℚ`, `D' = ℚ(√-3)`** — a twisted form with `√-1 ∉ D'`:
`𝔼_{D'/ℚ}` is an equivalence `HC_λ(𝔤,K_{ℚ(√-3)/ℚ})_ℚ ≃ Rep^nil(Γ_{ℚ(√-3)/ℚ})` for `ℓ ≥ 1`
(Gelfand quiver with its relation) and `ℓ = 0` (cyclic quiver).  `K_{ℚ(√-3)/ℚ}` is the conic
`x² + 3y² = 1`, a `ℚ`-form of the real `SO(2)` (`rmk:twistedforms` and the remark after it).

@census none (G5 instantiation of `RQ2-5.24`; stage T6) -/
theorem gelfand_equivalence_twisted_sqrtNegThree :
    (∀ {ℓ : ℕ} (hℓ : 1 ≤ ℓ), ∃ e : HCEObj ℓ ℚ qSqrtNegThree ≌
        RationalStructure.RepNilQ qSqrtNegThree.card_gal,
        e.functor = Equivalence.E_QFunctor qSqrtNegThree.card_gal hℓ
          (Equivalence.E_Q_spec qSqrtNegThree.card_gal hℓ)) ∧
      ∃ e : HCEObj 0 ℚ qSqrtNegThree ≌ Cyclic.RepNilCycQ qSqrtNegThree.card_gal,
        e.functor = Cyclic.E_CycFunctor qSqrtNegThree.card_gal
          (Cyclic.E_Cyc_spec qSqrtNegThree.card_gal) :=
  gelfand_equivalence_twisted ℚ qSqrtNegThree

/-- **`thm:twistedEEequivalence` at `E = ℚ`, `D' = ℚ(√2)`** — a real quadratic `D'`, `√-1 ∉ D'`.
@census none (G5 instantiation of `RQ2-5.24`; stage T6) -/
theorem gelfand_equivalence_twisted_sqrtTwo :
    (∀ {ℓ : ℕ} (hℓ : 1 ≤ ℓ), ∃ e : HCEObj ℓ ℚ qSqrtTwo ≌
        RationalStructure.RepNilQ qSqrtTwo.card_gal,
        e.functor = Equivalence.E_QFunctor qSqrtTwo.card_gal hℓ
          (Equivalence.E_Q_spec qSqrtTwo.card_gal hℓ)) ∧
      ∃ e : HCEObj 0 ℚ qSqrtTwo ≌ Cyclic.RepNilCycQ qSqrtTwo.card_gal,
        e.functor = Cyclic.E_CycFunctor qSqrtTwo.card_gal (Cyclic.E_Cyc_spec qSqrtTwo.card_gal) :=
  gelfand_equivalence_twisted ℚ qSqrtTwo

end Rat

end RationalQuivers.Gelfand
