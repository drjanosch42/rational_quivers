import RationalQuivers.HC.Pair
import Mathlib.Algebra.Lie.BaseChange
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# `(𝔤_E, K_E)` over every field `E` of characteristic `0` (`def:pairE`)

Census `RQ2-3.14`.  A **leaf** module: nothing in the package
imports it (only the root aggregator and the instrument).  It needs `Mathlib.Algebra.Lie.BaseChange`,
whose instance `LieAlgebra A (A ⊗[R] L)` gives every `A ⊗[R] L` a second route to `Module A`; in
modules downstream of `HC/` that route made `Module E (E ⊗[ℚ] _)` searches explore `LieRing`
instances and exceed the heartbeat budget (measured in `Gelfand/GeneralField/Identification*`),
so the base-change isomorphisms live here, after `HC/Pair`.

## Main definitions / results

* `RationalQuivers.HC.sl2BaseChange` — `E ⊗[ℚ] 𝔰𝔩_{2,ℚ} ≃ₗ⁅E⁆ 𝔰𝔩_{2,E}`.
* `RationalQuivers.HC.so2CoordRingBaseChange` — `E ⊗[ℚ] ℚ[x,y]/⟨x²+y²-1⟩ ≃ₐ[E] E[x,y]/⟨x²+y²-1⟩`.
* `RationalQuivers.HC.pairE` — census `RQ2-3.14`.
-/

namespace RationalQuivers.HC

open Matrix LieAlgebra.SpecialLinear

/-! ## `(𝔤_E, K_E)` for a field `E` of characteristic `0` (`def:pairE`, census `RQ2-3.14`)

`𝔤_E := E ⊗_ℚ 𝔤_ℚ` and `K_E := K_ℚ ×_ℚ E`.  The tex then reads these as `𝔰𝔩_{2,E}` and
`SO(2)_E = Spec E[x,y]/⟨x²+y²-1⟩`; here both identifications are **constructed**: an `E`-Lie
algebra isomorphism `E ⊗[ℚ] 𝔰𝔩_{2,ℚ} ≃ 𝔰𝔩_{2,E}` (`sl2BaseChange`) and an `E`-algebra isomorphism of
coordinate rings `E ⊗[ℚ] ℚ[x,y]/⟨x²+y²-1⟩ ≃ E[x,y]/⟨x²+y²-1⟩` (`so2CoordRingBaseChange`, built from
mathlib's `Algebra.TensorProduct.tensorQuotientEquiv` and `MvPolynomial.algebraTensorAlgEquiv`).
`K_ℚ ×_ℚ E` is rendered, as `SO(2)_ℚ` is, by its coordinate ring (the fibre product of affine
schemes is `Spec` of the tensor product), with its functor of points on `E`-algebras identified
with `SO2_QStructure` (`so2PointsE_bijective`). -/

section pairE

open TensorProduct

variable (E : Type) [Field E] [CharZero E]

/-- The ideal `⟨x² + y² - 1⟩ ⊆ E[x,y]`.

@census none
-/
noncomputable def so2IdealE : Ideal (MvPolynomial (Fin 2) E) :=
  Ideal.span {MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2 - 1}

/-- The coordinate ring `E[x,y]/⟨x² + y² - 1⟩` of `SO(2)_E`.

@census none
-/
noncomputable abbrev so2CoordRingE : Type := MvPolynomial (Fin 2) E ⧸ so2IdealE E

/-- The extended ideal: `⟨x²+y²-1⟩ ⊆ ℚ[x,y]`, pushed to `E ⊗[ℚ] ℚ[x,y] ≅ E[x,y]`, is
`⟨x²+y²-1⟩ ⊆ E[x,y]`.

@census none
-/
theorem so2Ideal_map_eq :
    (so2Ideal.map (Algebra.TensorProduct.includeRight (A := E) (R := ℚ))).map
      (MvPolynomial.algebraTensorAlgEquiv ℚ E (σ := Fin 2)) = so2IdealE E := by
  rw [so2Ideal, Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton,
    so2IdealE]
  congr 1
  simp

/-- `E ⊗[ℚ] ℚ[x,y]/⟨x²+y²-1⟩ ≃ₐ[E] E[x,y]/⟨x²+y²-1⟩`: the coordinate ring of `K_ℚ ×_ℚ E` is
that of `SO(2)_E` (clause `RQ2-3.14-C2`).

@census none
-/
noncomputable def so2CoordRingBaseChange :
    E ⊗[ℚ] so2CoordRing ≃ₐ[E] so2CoordRingE E :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := ℚ) E (MvPolynomial (Fin 2) ℚ) E so2Ideal).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv ℚ E)
      (so2Ideal_map_eq E).symm)

theorem so2CoordRingBaseChange_tmul (e : E) (p : MvPolynomial (Fin 2) ℚ) :
    so2CoordRingBaseChange E (e ⊗ₜ Ideal.Quotient.mk so2Ideal p) =
      Ideal.Quotient.mk (so2IdealE E) (e • MvPolynomial.map (algebraMap ℚ E) p) := by
  simp [so2CoordRingBaseChange]

/-- `𝔰𝔩_{2,ℚ} → 𝔰𝔩_{2,E}`, entrywise `algebraMap`, as a `ℚ`-linear map.

@census none
-/
def sl2QToE : ↥(sl (Fin 2) ℚ) →ₗ[ℚ] ↥(sl (Fin 2) E) where
  toFun x := ⟨(x : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ E), by
    have h : Matrix.trace (x : Matrix (Fin 2) (Fin 2) ℚ) = 0 := x.2
    show Matrix.trace ((x : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ E)) = 0
    rw [Matrix.trace_fin_two] at h ⊢
    simp only [Matrix.map_apply]
    rw [← map_add, h, map_zero]⟩
  map_add' x y := by apply Subtype.ext; ext i j; simp
  map_smul' q x := by
    apply Subtype.ext; ext i j
    show (algebraMap ℚ E) ((q • (x : Matrix (Fin 2) (Fin 2) ℚ)) i j) =
      (q • (x : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ E)) i j
    rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul,
      Algebra.smul_def]

@[simp] theorem sl2QToE_coe (x : ↥(sl (Fin 2) ℚ)) :
    ((sl2QToE E x : ↥(sl (Fin 2) E)) : Matrix (Fin 2) (Fin 2) E) =
      (x : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ E) := rfl

/-- `E ⊗[ℚ] 𝔰𝔩_{2,ℚ} → 𝔰𝔩_{2,E}`, `e ⊗ x ↦ e • x`, `E`-linear.

@census none
-/
noncomputable def sl2BaseChangeLin : E ⊗[ℚ] ↥(sl (Fin 2) ℚ) →ₗ[E] ↥(sl (Fin 2) E) :=
  (sl2QToE E).liftBaseChange E

theorem sl2BaseChangeLin_tmul (e : E) (x : ↥(sl (Fin 2) ℚ)) :
    sl2BaseChangeLin E (e ⊗ₜ x) = e • sl2QToE E x := rfl

/-- The inverse `A ↦ A₀₀ ⊗ h + A₀₁ ⊗ e + A₁₀ ⊗ f` (`h, e, f` = `sl2QHgen`, `sl2QE`, `sl2QF`).

@census none
-/
noncomputable def sl2BaseChangeInv : ↥(sl (Fin 2) E) →ₗ[E] E ⊗[ℚ] ↥(sl (Fin 2) ℚ) where
  toFun A := (A : Matrix (Fin 2) (Fin 2) E) 0 0 ⊗ₜ sl2QHgen
    + (A : Matrix (Fin 2) (Fin 2) E) 0 1 ⊗ₜ sl2QE + (A : Matrix (Fin 2) (Fin 2) E) 1 0 ⊗ₜ sl2QF
  map_add' A B := by
    show (A.1 + B.1) 0 0 ⊗ₜ[ℚ] sl2QHgen + (A.1 + B.1) 0 1 ⊗ₜ[ℚ] sl2QE
      + (A.1 + B.1) 1 0 ⊗ₜ[ℚ] sl2QF = _
    simp only [Matrix.add_apply, add_tmul]; abel
  map_smul' c A := by
    show (c • A.1) 0 0 ⊗ₜ[ℚ] sl2QHgen + (c • A.1) 0 1 ⊗ₜ[ℚ] sl2QE
      + (c • A.1) 1 0 ⊗ₜ[ℚ] sl2QF = _
    simp only [Matrix.smul_apply, RingHom.id_apply, smul_add, smul_tmul']

theorem sl2BaseChange_right_inv (A : ↥(sl (Fin 2) E)) :
    sl2BaseChangeLin E (sl2BaseChangeInv E A) = A := by
  have htr : Matrix.trace (A : Matrix (Fin 2) (Fin 2) E) = 0 := A.2
  rw [Matrix.trace_fin_two] at htr
  apply Subtype.ext
  simp only [sl2BaseChangeInv, LinearMap.coe_mk, AddHom.coe_mk, map_add, sl2BaseChangeLin_tmul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2QHgen, sl2QE, sl2QF]
  linear_combination -htr

theorem sl2BaseChange_left_inv (t : E ⊗[ℚ] ↥(sl (Fin 2) ℚ)) :
    sl2BaseChangeInv E (sl2BaseChangeLin E t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb]
  | tmul e x =>
    rw [sl2BaseChangeLin_tmul, map_smul]
    conv_rhs => rw [sl2Q_decomp x]
    simp only [sl2BaseChangeInv, LinearMap.coe_mk, AddHom.coe_mk, sl2QToE_coe, Matrix.map_apply,
      tmul_add, tmul_smul, smul_add, smul_tmul', smul_eq_mul]
    simp only [Algebra.smul_def, mul_comm e]

theorem sl2QToE_lie (x y : ↥(sl (Fin 2) ℚ)) :
    sl2QToE E ⁅x, y⁆ = ⁅sl2QToE E x, sl2QToE E y⁆ := by
  apply Subtype.ext
  rw [sl_bracket, sl2QToE_coe, sl2QToE_coe, sl2QToE_coe, sl_bracket,
    Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul]

/- The four `tb_*` lemmas restate bilinearity of the bracket of `E ⊗[ℚ] 𝔰𝔩_{2,ℚ}` at the raw
`Bracket` instance of `Mathlib/Algebra/Lie/BaseChange.lean`, which `rw` does not see through. -/
private theorem tb_add_lie (a b s : E ⊗[ℚ] ↥(sl (Fin 2) ℚ)) : ⁅a + b, s⁆ = ⁅a, s⁆ + ⁅b, s⁆ :=
  add_lie a b s
private theorem tb_lie_add (a b s : E ⊗[ℚ] ↥(sl (Fin 2) ℚ)) : ⁅s, a + b⁆ = ⁅s, a⁆ + ⁅s, b⁆ :=
  lie_add s a b
private theorem tb_zero_lie (s : E ⊗[ℚ] ↥(sl (Fin 2) ℚ)) :
    ⁅(0 : E ⊗[ℚ] ↥(sl (Fin 2) ℚ)), s⁆ = 0 :=
  zero_lie s
private theorem tb_lie_zero (s : E ⊗[ℚ] ↥(sl (Fin 2) ℚ)) :
    ⁅s, (0 : E ⊗[ℚ] ↥(sl (Fin 2) ℚ))⁆ = 0 :=
  lie_zero s

theorem sl2BaseChangeLin_lie (t s : E ⊗[ℚ] ↥(sl (Fin 2) ℚ)) :
    sl2BaseChangeLin E ⁅t, s⁆ = ⁅sl2BaseChangeLin E t, sl2BaseChangeLin E s⁆ := by
  induction t using TensorProduct.induction_on with
  | zero => rw [tb_zero_lie, map_zero, zero_lie]
  | add a b ha hb => rw [tb_add_lie, map_add, ha, hb, map_add, add_lie]
  | tmul e x =>
    induction s using TensorProduct.induction_on with
    | zero => rw [tb_lie_zero, map_zero, lie_zero]
    | add a b ha hb => rw [tb_lie_add, map_add, ha, hb, map_add, lie_add]
    | tmul e' y =>
      rw [LieAlgebra.ExtendScalars.bracket_tmul, sl2BaseChangeLin_tmul, sl2BaseChangeLin_tmul,
        sl2BaseChangeLin_tmul, sl2QToE_lie, smul_lie, lie_smul, smul_smul]

/-- **`𝔤_E := E ⊗_ℚ 𝔤_ℚ ≅ 𝔰𝔩_{2,E}`** as `E`-Lie algebras (clause `RQ2-3.14-C1`).

@census none
-/
noncomputable def sl2BaseChange : E ⊗[ℚ] ↥(sl (Fin 2) ℚ) ≃ₗ⁅E⁆ ↥(sl (Fin 2) E) :=
  { sl2BaseChangeLin E with
    map_lie' := fun {t s} => sl2BaseChangeLin_lie E t s
    invFun := sl2BaseChangeInv E
    left_inv := sl2BaseChange_left_inv E
    right_inv := sl2BaseChange_right_inv E }

theorem sl2BaseChange_tmul (e : E) (x : ↥(sl (Fin 2) ℚ)) :
    sl2BaseChange E (e ⊗ₜ x) = e • sl2QToE E x := rfl

/-- The canonical map `φ ↦ (φ x̄, φ ȳ)` from `E`-algebra maps out of `E[x,y]/⟨x²+y²-1⟩` to
`A`-points of `SO2_QStructure`.

@census none
-/
noncomputable def so2PointsOfAlgHomE (A : Type) [CommRing A] [Algebra E A]
    (φ : so2CoordRingE E →ₐ[E] A) : SO2_QStructure A :=
  ⟨(φ (Ideal.Quotient.mk (so2IdealE E) (MvPolynomial.X 0)),
    φ (Ideal.Quotient.mk (so2IdealE E) (MvPolynomial.X 1))), by
    have h : (Ideal.Quotient.mk (so2IdealE E) (MvPolynomial.X 0)) ^ 2
        + (Ideal.Quotient.mk (so2IdealE E) (MvPolynomial.X 1)) ^ 2 - 1 = 0 := by
      rw [← map_pow, ← map_pow, ← map_add, ← map_one (Ideal.Quotient.mk (so2IdealE E)), ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have := congrArg φ h
    rw [map_sub, map_add, map_pow, map_pow, map_one, map_zero, sub_eq_zero] at this
    exact this⟩

omit [CharZero E] in
/-- `K_E = SO(2)_E`: on `E`-algebras `A`, `Hom_E(E[x,y]/⟨x²+y²-1⟩, A) → SO2_QStructure A` is a
bijection (the `E`-analogue of `so2Points_equiv_algHom`; part of clause `RQ2-3.14-C2`).

@census none
-/
theorem so2PointsE_bijective (A : Type) [CommRing A] [Algebra E A] :
    Function.Bijective (so2PointsOfAlgHomE E A) := by
  constructor
  · intro φ ψ h
    have h0 : φ (Ideal.Quotient.mk (so2IdealE E) (MvPolynomial.X 0))
        = ψ (Ideal.Quotient.mk (so2IdealE E) (MvPolynomial.X 0)) := congrArg (fun p => p.1.1) h
    have h1 : φ (Ideal.Quotient.mk (so2IdealE E) (MvPolynomial.X 1))
        = ψ (Ideal.Quotient.mk (so2IdealE E) (MvPolynomial.X 1)) := congrArg (fun p => p.1.2) h
    have hcomp : φ.comp (Ideal.Quotient.mkₐ E (so2IdealE E))
        = ψ.comp (Ideal.Quotient.mkₐ E (so2IdealE E)) := by
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
    have hker : ∀ a ∈ so2IdealE E,
        (MvPolynomial.aeval ![ξ, η] : MvPolynomial (Fin 2) E →ₐ[E] A) a = 0 := by
      intro a ha
      rw [so2IdealE, Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [map_mul]
      convert zero_mul _
      simp only [map_sub, map_add, map_pow, MvPolynomial.aeval_X, map_one]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hξη, sub_self]
    refine ⟨Ideal.Quotient.liftₐ (so2IdealE E) (MvPolynomial.aeval ![ξ, η]) hker, ?_⟩
    apply Subtype.ext
    apply Prod.ext <;> simp [so2PointsOfAlgHomE]

/-- **Definition** (`def:pairE`).  For a field `E` of characteristic `0`,
`(𝔤_E, K_E) := (E ⊗_ℚ 𝔤_ℚ, K_ℚ ×_ℚ E)`; thus `𝔤_E = 𝔰𝔩_{2,E}` and
`K_E = SO(2)_E = Spec E[x,y]/⟨x² + y² - 1⟩`.  Lean records the pair by the two identifications the
tex states: the `E`-Lie algebra isomorphism `E ⊗[ℚ] 𝔰𝔩_{2,ℚ} ≃ₗ⁅E⁆ 𝔰𝔩_{2,E}` (`sl2BaseChange`,
`C1`) and the `E`-algebra isomorphism of coordinate rings
`E ⊗[ℚ] ℚ[x,y]/⟨x²+y²-1⟩ ≃ₐ[E] E[x,y]/⟨x²+y²-1⟩` (`so2CoordRingBaseChange`, `C2`), the latter's
functor of points on `E`-algebras being `SO2_QStructure` (`so2PointsE_bijective`).

@census    RQ2-3.14
@source    def:pairE
@clauses   RQ2-3.14-H1, RQ2-3.14-C1, RQ2-3.14-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (coordinate ring for the scheme, disclosed).  As for
`SO2_QStructure` (`RQ2-3.12`, ledger `MD-S7-06`), the affine group scheme `K_ℚ ×_ℚ E` is rendered by
its coordinate ring `E ⊗[ℚ] ℚ[x,y]/⟨x²+y²-1⟩` (the fibre product of affine schemes is `Spec` of the
tensor product) rather than an `AlgebraicGeometry.Scheme` term; the group structure on `E`-points is
`SO2_QStructure`'s.  The comultiplication (the group structure of `K_E`) is not stated; the points
are identified via `so2PointsE_bijective`.  The pair structure in the sense of `def:rationalpairs` (`RQ2-3.01`, `EX-J18`)
is not formalized, exactly as for `RQ2-3.12-C4`.  `𝔤_E` is mathlib's `E ⊗[ℚ] 𝔤_ℚ` with its
base-change Lie algebra structure (`LieAlgebra.ExtendScalars`).
-/
noncomputable def pairE :
    (E ⊗[ℚ] ↥(sl (Fin 2) ℚ) ≃ₗ⁅E⁆ ↥(sl (Fin 2) E)) × (E ⊗[ℚ] so2CoordRing ≃ₐ[E] so2CoordRingE E) :=
  (sl2BaseChange E, so2CoordRingBaseChange E)

end pairE

end RationalQuivers.HC
