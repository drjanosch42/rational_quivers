-- Import order: the mathlib modules below are listed in the order in which the v1 tree loaded them
-- here (through the archived `HC/Interface.lean`, `HC/Casimir.lean`, `Imports/Januszewski18.lean`).
-- The elaboration of the downstream `Gelfand/GeneralField/Identification*` modules is sensitive to
-- instance load order (measured at v2 T1: with a different order two declarations exceed the
-- heartbeat budget in `Field`/`Algebra` instance defeq); keeping v1's order keeps them unchanged.
module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

/-!
# `SO(2)_ℚ` and the `ℚ`-rational semisimple pair `(𝔰𝔩_{2,ℚ}, SO(2)_ℚ)`

Formalizes the `§3.1` construction of `latex/rational_quivers.tex` (census `RQ2-3.12`
`def:sotworational`, carried from v1 `RQ-3.12`; and, in `HC/PairE.lean`, `RQ2-3.14`
`def:pairE`).

## Main definitions / results

* `RationalQuivers.HC.SO2_QStructure` — `SO(2)_ℚ = Spec ℚ[x,y]/⟨x²+y²-1⟩`, as its **functor of
  points**: for a commutative ring `E`, the `E`-points are the pairs `(ξ,η)` with `ξ² + η² = 1`.
  This is the declaration that claims `RQ2-3.12`.
* `RationalQuivers.HC.so2CoordRing`, `so2PointsOfAlgHom`, `so2Points_equiv_algHom` — the coordinate ring
  `ℚ[x,y]/⟨x²+y²-1⟩`, the canonical map `φ ↦ (φ x̄, φ ȳ)`, and its bijectivity — the identification of the functor of points with its `ℚ`-algebra
  homomorphisms (clause `C1`).
* `RationalQuivers.HC.so2Matrix`, `so2_isQRationalStructure` — the specialization
  `(ξ,η) ↦ !![ξ, -η; η, ξ]`, and that it identifies the `ℂ`-points with `SO(2,ℂ) ⊆ ℂ^{2×2}`
  (clauses `C2`, `C3`).
* `RationalQuivers.HC.so2Q`, `so2Conj`, `sl2Q_so2Q_pairData` — the associated data of the pair,
  `𝔰𝔬(2)_ℚ = ℚ·W ⊆ 𝔰𝔩_{2,ℚ}` and the conjugation action of `SO(2)_ℚ` on `𝔰𝔩_{2,ℚ}`, and the
  expressible part of the statement that `(𝔤_ℚ, K_ℚ) = (𝔰𝔩_{2,ℚ}, SO(2)_ℚ)` is a `ℚ`-rational
  **semisimple** pair in the sense of `def:rationalpairs` (`RQ2-3.01`, cited, `EX-J18`; clause
  `C4`); `mem_sl2Q_iff_trace` (clause `C5`, `𝔰𝔩_{2,ℚ}` = the trace-`0` matrices).
* `RationalQuivers.HC.pairE` (in the leaf module `HC/PairE.lean`) — census `RQ2-3.14`
  (`def:pairE`): for `E` of characteristic `0`,
  `𝔤_E := E ⊗_ℚ 𝔤_ℚ ≅ 𝔰𝔩_{2,E}` as `E`-Lie algebras (`sl2BaseChange`) and the coordinate ring of
  `K_E := K_ℚ ×_ℚ E`, `E ⊗_ℚ ℚ[x,y]/⟨x²+y²-1⟩ ≅ E[x,y]/⟨x²+y²-1⟩` as `E`-algebras
  (`so2CoordRingBaseChange`), with `so2PointsE_bijective` identifying the latter's functor of points
  with `SO2_QStructure` on `E`-algebras.

## Implementation notes

**Functor of points, not a `Scheme`.**  `Spec ℚ[x,y]/⟨x²+y²-1⟩` is rendered by the `ℚ`-algebra it
is the spectrum of (`so2CoordRing`) *together with* its functor of points, the two tied by
`so2Points_equiv_algHom`.  Building `AlgebraicGeometry.Spec` of that ring is possible in mathlib,
but every use in `§3`–`§5` is through the points — the `ℂ`-points give `SO(2,ℂ)`, the `E`-points
give the group acting on an `(𝔞_E,B_E)`-module — and a `Scheme` term would add a layer nothing here
reads through.  Ledger row `MD-S7-06`.

**Why `Matrix.specialOrthogonalGroup` is the right target.**  mathlib defines it through
`starRingOfComm` (the *trivial* star) as a local instance, so `Matrix.specialOrthogonalGroup (Fin 2)
ℂ` is the **algebraic** special orthogonal group `{A : AᵀA = 1, det A = 1}` over `ℂ`, not the
unitary group — which is exactly the source's `SO(2,ℂ) ⊆ ℂ^{2×2}`.
-/

universe u

namespace RationalQuivers.HC

open Matrix LieAlgebra.SpecialLinear

/-! ## `SO(2)_ℚ` -/

/-- **`SO(2)_ℚ = Spec ℚ[x,y]/⟨x² + y² - 1⟩`** (census `RQ2-3.12`), as its functor of points: for a
commutative ring `E`, the `E`-points are the specializations `(ξ,η)` of `(x,y)` — that is, the pairs
with `ξ² + η² = 1`.  Together with `𝔰𝔩_{2,ℚ}` (mathlib's `LieAlgebra.SpecialLinear.sl (Fin 2) ℚ`)
this is the source's `ℚ`-rational semisimple pair `(𝔤_ℚ, K_ℚ)`, `SL₂` being viewed as a linear
algebraic group over `ℚ` (clause `RQ2-3.12-H1`).

The row's remaining clauses are discharged next to this definition: `so2Points_equiv_algHom` (`C1`,
that this really is the functor of points of that coordinate ring), `so2_isQRationalStructure`
(`C2`, `C3`), `sl2Q_so2Q_pairData` (`C4`) and `mem_sl2Q_iff_trace` (`C5`).

@census    RQ2-3.12
@source    def:sotworational
@clauses   RQ2-3.12-H1
@imports   none
@divergence JUSTIFIED_REFORMULATION (functor of points, disclosed).  The source writes
`SO(2)_ℚ = Spec ℚ[x,y]/⟨x²+y²-1⟩`.  This definition is the affine scheme's **functor of points**,
and `so2Points_equiv_algHom` is the statement that it *is* that functor: for every `ℚ`-algebra
`E` the **canonical** map `so2PointsOfAlgHom E : (so2CoordRing →ₐ[ℚ] E) → SO2_QStructure E`,
`φ ↦ (φ x̄, φ ȳ)`, is a bijection — which is the definition of `Spec` on points, for the map that
definition names (the map is one formula uniform in `E`, so it is natural in `E` by construction).
Nothing weaker is claimed and nothing stronger is assumed; a `AlgebraicGeometry.Spec` term would
add a layer no statement of `§3`–`§5` reads through (ledger `MD-S7-06`).
-/
abbrev SO2_QStructure (E : Type u) [CommRing E] : Type u :=
  {p : E × E // p.1 ^ 2 + p.2 ^ 2 = 1}

namespace SO2_QStructure

variable {E : Type u} [CommRing E]

/-- The rotation group law: `(ξ,η)·(ξ',η') = (ξξ' - ηη', ξη' + ηξ')`. -/
instance : Group (SO2_QStructure E) where
  mul p q := ⟨(p.1.1 * q.1.1 - p.1.2 * q.1.2, p.1.1 * q.1.2 + p.1.2 * q.1.1), by
    have h : (p.1.1 * q.1.1 - p.1.2 * q.1.2) ^ 2 + (p.1.1 * q.1.2 + p.1.2 * q.1.1) ^ 2
        = (p.1.1 ^ 2 + p.1.2 ^ 2) * (q.1.1 ^ 2 + q.1.2 ^ 2) := by ring
    rw [h, p.2, q.2, one_mul]⟩
  one := ⟨(1, 0), by ring⟩
  inv p := ⟨(p.1.1, -p.1.2), by have := p.2; rw [neg_pow]; simpa using this⟩
  mul_assoc a b c := by
    apply Subtype.ext
    apply Prod.ext
    · show (a.1.1 * b.1.1 - a.1.2 * b.1.2) * c.1.1 - (a.1.1 * b.1.2 + a.1.2 * b.1.1) * c.1.2
        = a.1.1 * (b.1.1 * c.1.1 - b.1.2 * c.1.2) - a.1.2 * (b.1.1 * c.1.2 + b.1.2 * c.1.1)
      ring
    · show (a.1.1 * b.1.1 - a.1.2 * b.1.2) * c.1.2 + (a.1.1 * b.1.2 + a.1.2 * b.1.1) * c.1.1
        = a.1.1 * (b.1.1 * c.1.2 + b.1.2 * c.1.1) + a.1.2 * (b.1.1 * c.1.1 - b.1.2 * c.1.2)
      ring
  one_mul a := by
    apply Subtype.ext
    apply Prod.ext
    · show (1 : E) * a.1.1 - (0 : E) * a.1.2 = a.1.1
      ring
    · show (1 : E) * a.1.2 + (0 : E) * a.1.1 = a.1.2
      ring
  mul_one a := by
    apply Subtype.ext
    apply Prod.ext
    · show a.1.1 * (1 : E) - a.1.2 * (0 : E) = a.1.1
      ring
    · show a.1.1 * (0 : E) + a.1.2 * (1 : E) = a.1.2
      ring
  inv_mul_cancel a := by
    apply Subtype.ext
    apply Prod.ext
    · show a.1.1 * a.1.1 - -a.1.2 * a.1.2 = (1 : E)
      have h := a.2
      linear_combination h
    · show a.1.1 * a.1.2 + -a.1.2 * a.1.1 = (0 : E)
      ring

/-! The group law, componentwise (all `rfl`; `simp` lemmas so that matrix computations with
`so2Matrix` can unfold `1`, `*`, `⁻¹` on points). -/

@[simp] theorem one_fst : (1 : SO2_QStructure E).1.1 = 1 := rfl
@[simp] theorem one_snd : (1 : SO2_QStructure E).1.2 = 0 := rfl
@[simp] theorem mul_fst (p q : SO2_QStructure E) : (p * q).1.1 = p.1.1 * q.1.1 - p.1.2 * q.1.2 := rfl
@[simp] theorem mul_snd (p q : SO2_QStructure E) : (p * q).1.2 = p.1.1 * q.1.2 + p.1.2 * q.1.1 := rfl
@[simp] theorem inv_fst (p : SO2_QStructure E) : (p⁻¹).1.1 = p.1.1 := rfl
@[simp] theorem inv_snd (p : SO2_QStructure E) : (p⁻¹).1.2 = -p.1.2 := rfl

end SO2_QStructure

/-- The ideal `⟨x² + y² - 1⟩ ⊆ ℚ[x,y]`.

@census none
-/
noncomputable def so2Ideal : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - 1}

/-- The coordinate ring `ℚ[x,y]/⟨x² + y² - 1⟩` of `SO(2)_ℚ` (clause `RQ2-3.12-C1`).

@census none
-/
noncomputable abbrev so2CoordRing : Type := MvPolynomial (Fin 2) ℚ ⧸ so2Ideal

/-- The **canonical map** from `ℚ`-algebra homomorphisms out of the coordinate ring to `E`-points,
`φ ↦ (φ x̄, φ ȳ)` — evaluation of a homomorphism on the two coordinate functions.  It lands in
`SO2_QStructure E` because `x̄² + ȳ² = 1` in `so2CoordRing`.  The formula is the same for every `E`,
so the map is natural in `E` by construction.

@census none
-/
noncomputable def so2PointsOfAlgHom (E : Type) [CommRing E] [Algebra ℚ E]
    (φ : so2CoordRing →ₐ[ℚ] E) : SO2_QStructure E :=
  ⟨(φ (Ideal.Quotient.mk so2Ideal (MvPolynomial.X 0)),
    φ (Ideal.Quotient.mk so2Ideal (MvPolynomial.X 1))), by
    have h : (Ideal.Quotient.mk so2Ideal (MvPolynomial.X 0)) ^ 2
        + (Ideal.Quotient.mk so2Ideal (MvPolynomial.X 1)) ^ 2 - 1 = 0 := by
      rw [← map_pow, ← map_pow, ← map_add, ← map_one (Ideal.Quotient.mk so2Ideal), ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have := congrArg φ h
    rw [map_sub, map_add, map_pow, map_pow, map_one, map_zero, sub_eq_zero] at this
    exact this⟩

/-- Clause `RQ2-3.12-C1`: `SO2_QStructure` **is** the functor of points of
`Spec ℚ[x,y]/⟨x²+y²-1⟩` — for every `ℚ`-algebra `E`, the **canonical** map
`so2PointsOfAlgHom E : (so2CoordRing →ₐ[ℚ] E) → SO2_QStructure E`, `φ ↦ (φ x̄, φ ȳ)`, is a
bijection.  This is the definition of `Spec R` on points (`Hom_ℚ(R, E) ≅ (Spec R)(E)`), stated for
the specific map that definition names, not as the existence of some bijection (the pre-repair
statement `Nonempty (SO2_QStructure E ≃ (so2CoordRing →ₐ[ℚ] E))` was a cardinality statement —
verifier finding V-S7-2, 2026-09-02).  Naturality in `E` holds by construction: the map is one
formula, uniform in `E`.

@census    none (auxiliary; discharges clause `RQ2-3.12-C1` of `RQ2-3.12`)
@source    def:sotworational
@clauses   RQ2-3.12-C1
@imports   none
@divergence none
-/
theorem so2Points_equiv_algHom (E : Type) [CommRing E] [Algebra ℚ E] :
    Function.Bijective (so2PointsOfAlgHom E) := by
  constructor
  · intro φ ψ h
    have h0 : φ (Ideal.Quotient.mk so2Ideal (MvPolynomial.X 0))
        = ψ (Ideal.Quotient.mk so2Ideal (MvPolynomial.X 0)) := congrArg (fun p => p.1.1) h
    have h1 : φ (Ideal.Quotient.mk so2Ideal (MvPolynomial.X 1))
        = ψ (Ideal.Quotient.mk so2Ideal (MvPolynomial.X 1)) := congrArg (fun p => p.1.2) h
    have hcomp : φ.comp (Ideal.Quotient.mkₐ ℚ so2Ideal)
        = ψ.comp (Ideal.Quotient.mkₐ ℚ so2Ideal) := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · exact h0
      · exact h1
    apply AlgHom.ext
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact AlgHom.congr_fun hcomp p
  · rintro ⟨⟨ξ, η⟩, hξη⟩
    have hker : ∀ a ∈ so2Ideal,
        (MvPolynomial.aeval ![ξ, η] : MvPolynomial (Fin 2) ℚ →ₐ[ℚ] E) a = 0 := by
      intro a ha
      rw [so2Ideal, Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [map_mul]
      convert zero_mul _
      simp only [map_sub, map_add, map_pow, MvPolynomial.aeval_X, map_one]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hξη, sub_self]
    refine ⟨Ideal.Quotient.liftₐ so2Ideal (MvPolynomial.aeval ![ξ, η]) hker, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> simp only [so2PointsOfAlgHom] <;> erw [Ideal.Quotient.lift_mk] <;> simp

/-! ## The specialization `(ξ,η) ↦ !![ξ, -η; η, ξ]` -/

/-- The matrix attached to a specialization `(ξ,η)` (clause `RQ2-3.12-C2`).

@census none
-/
def so2Matrix {E : Type u} [CommRing E] (p : SO2_QStructure E) : Matrix (Fin 2) (Fin 2) E :=
  !![p.1.1, -p.1.2; p.1.2, p.1.1]

section so2MatrixHom

variable {E : Type u} [CommRing E]

/-- `so2Matrix` is multiplicative: the group law on points is matrix multiplication. -/
theorem so2Matrix_mul (p q : SO2_QStructure E) : so2Matrix (p * q) = so2Matrix p * so2Matrix q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [so2Matrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

@[simp] theorem so2Matrix_one : so2Matrix (1 : SO2_QStructure E) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [so2Matrix]

theorem so2Matrix_inv_mul (p : SO2_QStructure E) : so2Matrix p⁻¹ * so2Matrix p = 1 := by
  rw [← so2Matrix_mul, inv_mul_cancel, so2Matrix_one]

theorem so2Matrix_mul_inv (p : SO2_QStructure E) : so2Matrix p * so2Matrix p⁻¹ = 1 := by
  rw [← so2Matrix_mul, mul_inv_cancel, so2Matrix_one]

end so2MatrixHom

/-- Clauses `RQ2-3.12-C2` and `RQ2-3.12-C3`: a specialization `(ξ,η) ∈ ℂ²` corresponds to the matrix
`!![ξ, -η; η, ξ] ∈ SO(2,ℂ)`, and this correspondence is a **bijection** onto `SO(2,ℂ) ⊆ ℂ^{2×2}` —
so `SO(2)_ℚ`, a scheme over `ℚ`, has `SO(2,ℂ)` as its complex points: a `ℚ`-rational structure on
`SO(2,ℂ)`.

@census    none (auxiliary; discharges clauses `RQ2-3.12-C2`, `RQ2-3.12-C3` of `RQ2-3.12`)
@source    def:sotworational
@clauses   RQ2-3.12-C2, RQ2-3.12-C3
@imports   none
@divergence none
-/
theorem so2_isQRationalStructure :
    (∀ p : SO2_QStructure ℂ, so2Matrix p ∈ Matrix.specialOrthogonalGroup (Fin 2) ℂ) ∧
      Function.Injective (so2Matrix (E := ℂ)) ∧
      Set.range (so2Matrix (E := ℂ)) = {A | A ∈ Matrix.specialOrthogonalGroup (Fin 2) ℂ} := by
  have hmem : ∀ p : SO2_QStructure ℂ,
      so2Matrix p ∈ Matrix.specialOrthogonalGroup (Fin 2) ℂ := by
    intro p
    rw [so2Matrix, Matrix.of_mem_specialOrthogonalGroup_fin_two_iff]
    refine ⟨rfl, rfl, ?_⟩
    have := p.2
    linear_combination this
  refine ⟨hmem, ?_, ?_⟩
  · intro p q h
    apply Subtype.ext
    apply Prod.ext
    · exact congrFun (congrFun h 0) 0
    · exact congrFun (congrFun h 1) 0
  · ext A
    constructor
    · rintro ⟨p, rfl⟩
      exact hmem p
    · intro hA
      have hA' : !![A 0 0, A 0 1; A 1 0, A 1 1] ∈ Matrix.specialOrthogonalGroup (Fin 2) ℂ := by
        rw [← Matrix.eta_fin_two A]; exact hA
      rw [Matrix.of_mem_specialOrthogonalGroup_fin_two_iff] at hA'
      obtain ⟨h1, h2, h3⟩ := hA'
      refine ⟨⟨(A 0 0, A 1 0), ?_⟩, ?_⟩
      · rw [h2] at h3
        linear_combination h3
      · show so2Matrix _ = A
        ext i j
        fin_cases i <;> fin_cases j <;> simp [so2Matrix]
        all_goals first | rfl | linear_combination h1 | linear_combination -h2

/-! ## `(𝔤_ℚ, K_ℚ)` is a pair in the sense of `def:rationalpairs` (`RQ2-3.01`, cited)

The pair's **associated data** are named, not quantified away (G2 repair of verifier finding
V-S7-1, 2026-09-02): `𝔟_ℚ = 𝔰𝔬(2)_ℚ = Lie(SO(2)_ℚ)`, the line `ℚ·W ⊆ 𝔰𝔩_{2,ℚ}` spanned by the
infinitesimal rotation `W = !![0, -1; 1, 0]`, and the action of `SO(2)_ℚ` on `𝔰𝔩_{2,ℚ}` by
conjugation `x ↦ g x g⁻¹` (the restriction of `Ad` of `SL₂` to `SO(2)`, which is what "extends the
natural action on `𝔟_ℚ`" refers to). The earlier statement `∃ b act, IsPair … b act` was provable
from `b := ⊥`, `act := 1` and said nothing about the source's pair. -/

/-- `W = !![0, -1; 1, 0] ∈ 𝔰𝔩_{2,ℚ}`, the generator of `𝔰𝔬(2)_ℚ`: `so2Matrix (ξ,η) = ξ·1 + η·W`, and
`H = −i·W` in `𝔤 = 𝔰𝔩_{2,ℂ}` (`sl2Hm = !![0, i; -i, 0]`, `HC/Sl2.lean`).  (Both clauses read
`H = i·W` and `sl2Hm = !![0, -i; i, 0]` until the paper author's ruling of 2026-09-10 negated `H`;
`W` itself does not move.)

@census none
-/
def so2Gen : ↥(sl (Fin 2) ℚ) :=
  ⟨!![0, -1; 1, 0], by
    show Matrix.trace (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) = 0
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]⟩

/-- `𝔟_ℚ = 𝔰𝔬(2)_ℚ = Lie(SO(2)_ℚ) ⊆ 𝔰𝔩_{2,ℚ}`: the Lie subalgebra generated by `W` (it is the line
`ℚ·W`, since `⁅W, W⁆ = 0`) — the antisymmetric trace-zero rational `2×2` matrices.

@census none
-/
def so2Q : LieSubalgebra ℚ ↥(sl (Fin 2) ℚ) := LieSubalgebra.lieSpan ℚ ↥(sl (Fin 2) ℚ) {so2Gen}

/-- Conjugation by the point `g ∈ SO(2)_ℚ`, `x ↦ so2Matrix g · x · so2Matrix g⁻¹`, as a `ℚ`-linear
endomorphism of `𝔰𝔩_{2,ℚ}` (it preserves the trace by `Matrix.trace_mul_cycle`).

@census none
-/
def so2ConjLin (g : SO2_QStructure ℚ) : ↥(sl (Fin 2) ℚ) →ₗ[ℚ] ↥(sl (Fin 2) ℚ) where
  toFun x := ⟨so2Matrix g * x.1 * so2Matrix g⁻¹, by
    show Matrix.trace (so2Matrix g * x.1 * so2Matrix g⁻¹) = 0
    rw [Matrix.trace_mul_cycle, so2Matrix_inv_mul, one_mul]
    exact x.2⟩
  map_add' x y := by
    apply Subtype.ext
    show so2Matrix g * (x.1 + y.1) * so2Matrix g⁻¹
      = so2Matrix g * x.1 * so2Matrix g⁻¹ + so2Matrix g * y.1 * so2Matrix g⁻¹
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' q x := by
    apply Subtype.ext
    show so2Matrix g * (q • x.1) * so2Matrix g⁻¹ = q • (so2Matrix g * x.1 * so2Matrix g⁻¹)
    rw [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem so2ConjLin_apply_coe (g : SO2_QStructure ℚ) (x : ↥(sl (Fin 2) ℚ)) :
    (so2ConjLin g x : Matrix (Fin 2) (Fin 2) ℚ) = so2Matrix g * x.1 * so2Matrix g⁻¹ := rfl

/-- **The action of `K_ℚ = SO(2)_ℚ` on `𝔤_ℚ = 𝔰𝔩_{2,ℚ}` by conjugation**, `g ↦ (x ↦ g x g⁻¹)`, as a
representation — the `act` datum of the pair `(𝔰𝔩_{2,ℚ}, SO(2)_ℚ)` in `IsPair`.  It is the
restriction to `SO(2)_ℚ` of the adjoint action of `SL₂`; on `𝔟_ℚ = 𝔰𝔬(2)_ℚ` it is the natural
(adjoint) action of `SO(2)_ℚ` on its own Lie algebra, which — `SO(2)` being abelian — is trivial.

@census none
-/
def so2Conj : Representation ℚ (SO2_QStructure ℚ) ↥(sl (Fin 2) ℚ) where
  toFun := so2ConjLin
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    show so2Matrix (g * h) * x.1 * so2Matrix (g * h)⁻¹
      = so2Matrix g * (so2Matrix h * x.1 * so2Matrix h⁻¹) * so2Matrix g⁻¹
    rw [_root_.mul_inv_rev, so2Matrix_mul, so2Matrix_mul]
    simp only [Matrix.mul_assoc]

@[simp] theorem so2Conj_apply_coe (g : SO2_QStructure ℚ) (x : ↥(sl (Fin 2) ℚ)) :
    (so2Conj g x : Matrix (Fin 2) (Fin 2) ℚ) = so2Matrix g * x.1 * so2Matrix g⁻¹ := rfl

/-- Clause `RQ2-3.12-C5`: `𝔰𝔩_{2,ℚ} ⊆ ℚ^{2×2}` is the space of **trace-`0`** matrices.  mathlib's
`LieAlgebra.SpecialLinear.sl (Fin 2) ℚ` is *defined* as the kernel of the trace, so the statement
is definitional; it is stated so that the clause has a declaration that says it.

@census    none (auxiliary; discharges clause `RQ2-3.12-C5` of `RQ2-3.12`)
@source    def:sotworational
@clauses   RQ2-3.12-C5
@imports   none
@divergence none
-/
theorem mem_sl2Q_iff_trace (A : Matrix (Fin 2) (Fin 2) ℚ) :
    A ∈ sl (Fin 2) ℚ ↔ Matrix.trace A = 0 := Iff.rfl

/-! ### `𝔰𝔩_{2,ℚ}` is a simple, hence semisimple, Lie algebra

`LieAlgebra.IsSemisimple ℚ ↥(sl (Fin 2) ℚ)` has **no instance at the mathlib pin** (measured by the
G2 delta verifier at `0428cff`): mathlib reaches `IsSemisimple` only through `IsKilling` plus
finite-dimensionality, and `Mathlib/Algebra/Lie/` carries no `IsKilling` instance for
`sl (Fin 2) K`. It is proved here by hand, from `LieAlgebra.IsSimple`, in the classical way: for
`x = p·h + q·e + r·f`, `ad_e² x = -2r·e` and `ad_f² x = -2q·f`, so a non-zero ideal contains `e`,
`f` or `h`, and each of the three drags in the other two. Non-abelian is `⁅e,f⁆ = h ≠ 0`.
`LieAlgebra.IsSimple.instIsSemisimple` then gives the conclusion; the two statements are kept as
theorems, not instances, so no `#synth` guard is owed (PROCESS-CHANGELOG 2026-08-30).
-/

/-- `e = !![0,1;0,0]`. -/
def sl2QE : ↥(sl (Fin 2) ℚ) :=
  ⟨!![0, 1; 0, 0], by
    show Matrix.trace (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) = 0
    simp [Matrix.trace_fin_two]⟩

/-- `f = !![0,0;1,0]`. -/
def sl2QF : ↥(sl (Fin 2) ℚ) :=
  ⟨!![0, 0; 1, 0], by
    show Matrix.trace (!![0, 0; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ) = 0
    simp [Matrix.trace_fin_two]⟩

/-- `h = !![1,0;0,-1]`. -/
def sl2QHgen : ↥(sl (Fin 2) ℚ) :=
  ⟨!![1, 0; 0, -1], by
    show Matrix.trace (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℚ) = 0
    simp [Matrix.trace_fin_two]⟩

theorem lie_E_F : ⁅sl2QE, sl2QF⁆ = sl2QHgen := by
  apply Subtype.ext
  rw [sl_bracket]
  show (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℚ) * !![0,0;1,0] - !![0,0;1,0] * !![0,1;0,0] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2QHgen]

theorem lie_F_E : ⁅sl2QF, sl2QE⁆ = -sl2QHgen := by
  rw [← lie_skew, lie_E_F]

theorem lie_E_H : ⁅sl2QE, sl2QHgen⁆ = (-2 : ℚ) • sl2QE := by
  apply Subtype.ext
  rw [sl_bracket]
  show (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℚ) * !![1,0;0,-1] - !![1,0;0,-1] * !![0,1;0,0] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2QE]
  all_goals norm_num

theorem lie_F_H : ⁅sl2QF, sl2QHgen⁆ = (2 : ℚ) • sl2QF := by
  apply Subtype.ext
  rw [sl_bracket]
  show (!![0,0;1,0] : Matrix (Fin 2) (Fin 2) ℚ) * !![1,0;0,-1] - !![1,0;0,-1] * !![0,0;1,0] = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2QF]
  all_goals norm_num

theorem lie_E_lie_E (x : ↥(sl (Fin 2) ℚ)) :
    ⁅sl2QE, ⁅sl2QE, x⁆⁆ = (-2 * (x : Matrix (Fin 2) (Fin 2) ℚ) 1 0) • sl2QE := by
  apply Subtype.ext
  rw [sl_bracket, sl_bracket]
  show (!![0,1;0,0] : Matrix (Fin 2) (Fin 2) ℚ) * (!![0,1;0,0] * (x : Matrix (Fin 2) (Fin 2) ℚ)
      - (x : Matrix (Fin 2) (Fin 2) ℚ) * !![0,1;0,0])
    - (!![0,1;0,0] * (x : Matrix (Fin 2) (Fin 2) ℚ)
      - (x : Matrix (Fin 2) (Fin 2) ℚ) * !![0,1;0,0]) * !![0,1;0,0] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, sl2QE,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  all_goals simp
  all_goals ring

theorem lie_F_lie_F (x : ↥(sl (Fin 2) ℚ)) :
    ⁅sl2QF, ⁅sl2QF, x⁆⁆ = (-2 * (x : Matrix (Fin 2) (Fin 2) ℚ) 0 1) • sl2QF := by
  apply Subtype.ext
  rw [sl_bracket, sl_bracket]
  show (!![0,0;1,0] : Matrix (Fin 2) (Fin 2) ℚ) * (!![0,0;1,0] * (x : Matrix (Fin 2) (Fin 2) ℚ)
      - (x : Matrix (Fin 2) (Fin 2) ℚ) * !![0,0;1,0])
    - (!![0,0;1,0] * (x : Matrix (Fin 2) (Fin 2) ℚ)
      - (x : Matrix (Fin 2) (Fin 2) ℚ) * !![0,0;1,0]) * !![0,0;1,0] = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two, sl2QF,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  all_goals simp
  all_goals ring

theorem sl2Q_decomp (x : ↥(sl (Fin 2) ℚ)) :
    x = ((x : Matrix (Fin 2) (Fin 2) ℚ) 0 0) • sl2QHgen
      + ((x : Matrix (Fin 2) (Fin 2) ℚ) 0 1) • sl2QE
      + ((x : Matrix (Fin 2) (Fin 2) ℚ) 1 0) • sl2QF := by
  have htr : Matrix.trace (x : Matrix (Fin 2) (Fin 2) ℚ) = 0 := x.2
  rw [Matrix.trace_fin_two] at htr
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2QE, sl2QF, sl2QHgen]
  all_goals linarith

theorem sl2Q_top_of_gens (I : LieIdeal ℚ ↥(sl (Fin 2) ℚ))
    (he : sl2QE ∈ I) (hf : sl2QF ∈ I) (hh : sl2QHgen ∈ I) : I = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [sl2Q_decomp x]
  exact add_mem (add_mem (SMulMemClass.smul_mem _ hh) (SMulMemClass.smul_mem _ he))
    (SMulMemClass.smul_mem _ hf)

theorem sl2Q_top_of_E (I : LieIdeal ℚ ↥(sl (Fin 2) ℚ)) (he : sl2QE ∈ I) : I = ⊤ := by
  have hh : sl2QHgen ∈ I := by
    have h1 : ⁅sl2QF, sl2QE⁆ ∈ I := I.lie_mem he
    rw [lie_F_E] at h1
    simpa using neg_mem h1
  have hf : sl2QF ∈ I := by
    have h1 : ⁅sl2QF, sl2QHgen⁆ ∈ I := I.lie_mem hh
    rw [lie_F_H] at h1
    have h2 := SMulMemClass.smul_mem ((2 : ℚ)⁻¹) h1
    rw [smul_smul] at h2
    norm_num at h2
    exact h2
  exact sl2Q_top_of_gens I he hf hh

theorem sl2Q_top_of_F (I : LieIdeal ℚ ↥(sl (Fin 2) ℚ)) (hf : sl2QF ∈ I) : I = ⊤ := by
  have hh : sl2QHgen ∈ I := by
    have h1 : ⁅sl2QE, sl2QF⁆ ∈ I := I.lie_mem hf
    rwa [lie_E_F] at h1
  have he : sl2QE ∈ I := by
    have h1 : ⁅sl2QE, sl2QHgen⁆ ∈ I := I.lie_mem hh
    rw [lie_E_H] at h1
    have h2 := SMulMemClass.smul_mem ((-2 : ℚ)⁻¹) h1
    rw [smul_smul] at h2
    norm_num at h2
    exact h2
  exact sl2Q_top_of_gens I he hf hh

theorem sl2Q_top_of_H (I : LieIdeal ℚ ↥(sl (Fin 2) ℚ)) (hh : sl2QHgen ∈ I) : I = ⊤ := by
  have he : sl2QE ∈ I := by
    have h1 : ⁅sl2QE, sl2QHgen⁆ ∈ I := I.lie_mem hh
    rw [lie_E_H] at h1
    have h2 := SMulMemClass.smul_mem ((-2 : ℚ)⁻¹) h1
    rw [smul_smul] at h2
    norm_num at h2
    exact h2
  exact sl2Q_top_of_E I he

theorem sl2Q_isSimple : LieAlgebra.IsSimple ℚ ↥(sl (Fin 2) ℚ) where
  eq_bot_or_eq_top I := by
    rcases eq_or_ne I ⊥ with h | h
    · exact Or.inl h
    refine Or.inr ?_
    obtain ⟨x, hxI, hx0⟩ : ∃ x ∈ I, x ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (by rw [LieSubmodule.eq_bot_iff]; exact hc)
    by_cases hr : (x : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = 0
    · by_cases hq : (x : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = 0
      · set p : ℚ := (x : Matrix (Fin 2) (Fin 2) ℚ) 0 0 with hp_def
        have hxh : x = p • sl2QHgen := by
          conv_lhs => rw [sl2Q_decomp x]
          rw [hq, hr, ← hp_def]
          simp
        have hp : p ≠ 0 := by
          intro hp0
          exact hx0 (by rw [hxh, hp0, zero_smul])
        have hmem : sl2QHgen ∈ I := by
          have h1 := SMulMemClass.smul_mem p⁻¹ hxI
          rw [hxh, smul_smul, inv_mul_cancel₀ hp, one_smul] at h1
          exact h1
        exact sl2Q_top_of_H I hmem
      · have h1 : ⁅sl2QF, ⁅sl2QF, x⁆⁆ ∈ I := I.lie_mem (I.lie_mem hxI)
        rw [lie_F_lie_F] at h1
        have hne : (-2 * (x : Matrix (Fin 2) (Fin 2) ℚ) 0 1) ≠ 0 := by
          simpa using hq
        have h2 := SMulMemClass.smul_mem ((-2 * (x : Matrix (Fin 2) (Fin 2) ℚ) 0 1)⁻¹) h1
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
        exact sl2Q_top_of_F I h2
    · have h1 : ⁅sl2QE, ⁅sl2QE, x⁆⁆ ∈ I := I.lie_mem (I.lie_mem hxI)
      rw [lie_E_lie_E] at h1
      have hne : (-2 * (x : Matrix (Fin 2) (Fin 2) ℚ) 1 0) ≠ 0 := by
        simpa using hr
      have h2 := SMulMemClass.smul_mem ((-2 * (x : Matrix (Fin 2) (Fin 2) ℚ) 1 0)⁻¹) h1
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
      exact sl2Q_top_of_E I h2
  non_abelian := by
    intro habel
    have h : ⁅sl2QE, sl2QF⁆ = 0 := habel.trivial sl2QE sl2QF
    rw [lie_E_F] at h
    have h2 := congrArg (fun z : ↥(sl (Fin 2) ℚ) => (z : Matrix (Fin 2) (Fin 2) ℚ) 0 0) h
    simp [sl2QHgen] at h2

theorem sl2Q_isSemisimple : LieAlgebra.IsSemisimple ℚ ↥(sl (Fin 2) ℚ) := by
  haveI := sl2Q_isSimple
  infer_instance

/-! ### The associated data of the pair: `𝔰𝔬(2)_ℚ = ℚ·W` and conjugation -/

theorem so2Matrix_comm_gen (g : SO2_QStructure ℚ) :
    so2Matrix g * (so2Gen : Matrix (Fin 2) (Fin 2) ℚ)
      = (so2Gen : Matrix (Fin 2) (Fin 2) ℚ) * so2Matrix g := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [so2Matrix, so2Gen, Matrix.mul_apply, Fin.sum_univ_two]

theorem so2Conj_gen (g : SO2_QStructure ℚ) : so2Conj g so2Gen = so2Gen := by
  apply Subtype.ext
  rw [so2Conj_apply_coe, so2Matrix_comm_gen, Matrix.mul_assoc, so2Matrix_mul_inv, Matrix.mul_one]

/-- `𝔰𝔬(2)_ℚ` is the line `ℚ·W`: the Lie span of a single element with `⁅W,W⁆ = 0`. -/
def so2Line : LieSubalgebra ℚ ↥(sl (Fin 2) ℚ) where
  __ := Submodule.span ℚ {so2Gen}
  lie_mem' := by
    intro x y hx hy
    have hx : x ∈ Submodule.span ℚ {so2Gen} := hx
    have hy : y ∈ Submodule.span ℚ {so2Gen} := hy
    rw [Submodule.mem_span_singleton] at hx hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [smul_lie, lie_smul, lie_self, smul_zero, smul_zero]
    exact Submodule.zero_mem _

theorem so2Q_eq_line : so2Q = so2Line := by
  apply le_antisymm
  · apply LieSubalgebra.lieSpan_le.mpr
    rintro z (rfl : z = so2Gen)
    exact Submodule.mem_span_singleton_self _
  · intro z hz
    have hz' : z ∈ Submodule.span ℚ {so2Gen} := hz
    rw [Submodule.mem_span_singleton] at hz'
    obtain ⟨a, rfl⟩ := hz'
    exact Submodule.smul_mem _ a (LieSubalgebra.subset_lieSpan rfl)

theorem so2Conj_mem_so2Q (g : SO2_QStructure ℚ) (x : ↥(sl (Fin 2) ℚ)) (hx : x ∈ so2Q) :
    so2Conj g x ∈ so2Q := by
  rw [so2Q_eq_line] at hx ⊢
  have hx' : x ∈ Submodule.span ℚ {so2Gen} := hx
  rw [Submodule.mem_span_singleton] at hx'
  obtain ⟨a, rfl⟩ := hx'
  have : so2Conj g (a • so2Gen) = a • so2Gen := by
    rw [map_smul, so2Conj_gen]
  rw [this]
  exact Submodule.smul_mem _ a (Submodule.mem_span_singleton_self _)

theorem so2Conj_act_lie (g : SO2_QStructure ℚ) (x y : ↥(sl (Fin 2) ℚ)) :
    so2Conj g ⁅x, y⁆ = ⁅so2Conj g x, so2Conj g y⁆ := by
  apply Subtype.ext
  rw [so2Conj_apply_coe, sl_bracket, sl_bracket, so2Conj_apply_coe, so2Conj_apply_coe]
  have hgg : so2Matrix g⁻¹ * so2Matrix g = 1 := so2Matrix_inv_mul g
  linear_combination (norm := noncomm_ring)
    (so2Matrix g * y.1) * hgg * (x.1 * so2Matrix g⁻¹)
      - (so2Matrix g * x.1) * hgg * (y.1 * so2Matrix g⁻¹)

/-- Clause `C4` of `def:sotworational`, in the part this formalization can express without the
archived Januszewski18 interface (`D-10`; `def:rationalpairs` is `OUT`, `EX-J18`): the associated
data of `(𝔤_ℚ, K_ℚ) = (𝔰𝔩_{2,ℚ}, SO(2)_ℚ)` — conjugation by `SO(2)_ℚ` acts on `𝔰𝔩_{2,ℚ}` by Lie
algebra automorphisms (`so2Conj_act_lie`) preserving `𝔟_ℚ = 𝔰𝔬(2)_ℚ` (`so2Conj_mem_so2Q`) — and
`𝔰𝔩_{2,ℚ}` is **semisimple** (mathlib's `LieAlgebra.IsSemisimple`).

The v1 form `isPair_sl2Q_so2Q` (with the five algebraic-group facts of the J18 bundle as named
hypotheses) moved with that bundle to `Archive/HC/Interface.lean` at T1.

@census    none (auxiliary; discharges clause `RQ2-3.12-C4` of `RQ2-3.12`)
@source    def:sotworational
@clauses   RQ2-3.12-C4
@imports   none
@divergence WEAKENED_OR_PARTIAL ("pair in the sense of `def:rationalpairs`": its algebraic-group
content — `K_ℚ` linear algebraic with reductive identity component, `𝔟_ℚ = Lie(K_ℚ)`, rationality of
the action — has no mathlib counterpart and is not formalized on the v2 line, `EX-J18`; what is
stated is every expressible part of the associated data plus semisimplicity).
-/
theorem sl2Q_so2Q_pairData :
    (∀ (g : SO2_QStructure ℚ) (x y : ↥(sl (Fin 2) ℚ)),
        so2Conj g ⁅x, y⁆ = ⁅so2Conj g x, so2Conj g y⁆) ∧
      (∀ (g : SO2_QStructure ℚ) (x : ↥(sl (Fin 2) ℚ)), x ∈ so2Q → so2Conj g x ∈ so2Q) ∧
      LieAlgebra.IsSemisimple ℚ ↥(sl (Fin 2) ℚ) :=
  ⟨so2Conj_act_lie, so2Conj_mem_so2Q, sl2Q_isSemisimple⟩

end RationalQuivers.HC
