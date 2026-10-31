module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Tactic.NoncommRing
public import RationalQuivers.Unipotent.Stabilization

@[expose] public section

/-!
# A non-degenerate witness for the hypotheses of §4.1

Stage **S6**, gate **G5.2**.  This module carries **no census row**: it exists to answer the
question `rqaudit models` cannot ask, because S6 introduces no `structure` — *is the hypothesis
bundle of `prop:unipotentstabilization` inhabited by anything other than the identity?*

The G2 verification (`workflow/stages/S6/VERIFICATION.md` §7) records the gap precisely: the
`ℚ²` witness of `Unipotent/SquareRoots.lean` inhabits the *nilpotency* hypothesis but not
`RQ2-4.01`'s configuration (`W_L = L ⊗_K W_K`, `L/K` quadratic, `W_±` subspaces,
`φ_± : W_± ≃ W_∓^τ`).  This module exhibits that configuration:

* `K = ℝ`, `L = ℂ` — quadratic (`Complex.finrank_real_complex`), Galois
  (`RationalQuivers.Unipotent.isGalois_real_complex`, derived, not assumed), `char ≠ 2`;
* `τ = ` complex conjugation, **non-trivial** (`witness_tau_ne_one`);
* `W_K = ℝ²`, `W_L = ℂ ⊗_ℝ ℝ²` with its canonical semi-linear `τ`-action;
* `W_+ = W_- = ⊤`, so `W_± = W_∓^τ` and the **addenda** apply too;
* `φ_+ = φ_- = 1 + N` where `N` is the base change of the real nilpotent `!![0,1;0,0]`.

The point of the witness is the last line of `witness_spec`:

  `φ_-^τ ∘ φ_+ = 1 + n` with `n^1 ≠ 0` and `n^2 = 0` — nilpotent of exponent **exactly 2**.

`n = 2N`, and `2N ≠ 0` **precisely because `char ≠ 2`**: over a field of characteristic 2 this same
configuration would give `n = 0`.  So `RQ2-4.01`'s hypothesis bundle is inhabited, it is not
inhabited only by `n = 0`, and the exactness clause `RQ2-4.01-H8` is satisfiable with `e = 2`.
-/

universe u v

open scoped TensorProduct

namespace RationalQuivers.Unipotent

/-! ## The ground data -/

/-- `ℂ/ℝ` is Galois.  Derived rather than assumed: `IsGalois ℝ ℂ` does **not** synthesize at the
pinned revision (`CONVENTIONS.md` §6 warns about exactly this), but `ℂ` is algebraically closed
and `ℂ/ℝ` is algebraic, so `IsAlgClosure.isGalois` applies.

@census none
-/
theorem isGalois_real_complex : IsGalois ℝ ℂ := by
  haveI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  infer_instance

/-- Complex conjugation is the non-trivial element of `Gal(ℂ/ℝ)` (clause `RQ2-4.01-H3`). -/
theorem witness_tau_ne_one : (Complex.conjAe : Gal(ℂ/ℝ)) ≠ 1 := by
  intro h
  have h1 := congrArg (fun f => (f : Gal(ℂ/ℝ)) Complex.I) h
  simp [Complex.conjAe_coe] at h1
  have h2 : (2 : ℂ) * Complex.I = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact Complex.I_ne_zero h3

/-- `char ℝ ≠ 2` (clause `RQ2-4.01-H2`). -/
theorem witness_two_ne_zero : (2 : ℝ) ≠ 0 := two_ne_zero

/-! ## The nilpotent operator -/

/-- `W_K = ℝ²`. -/
abbrev WitnessBase : Type := Fin 2 → ℝ

/-- `W_L = ℂ ⊗_ℝ ℝ²`, with the canonical semi-linear `τ`-action of `galoisTwist`
(clause `RQ2-4.01-H4`). -/
abbrev WitnessSpace : Type := ℂ ⊗[ℝ] WitnessBase

/-- The `ℂ`-basis of `W_L` coming from the standard basis of `ℝ²`; used only to see that the
nilpotent is non-zero. -/
noncomputable def witnessBasis : Module.Basis (Fin 2) ℂ WitnessSpace :=
  Algebra.TensorProduct.basis ℂ (Pi.basisFun ℝ (Fin 2))

/-- The real nilpotent `!![0,1;0,0]` on `ℝ²`. -/
noncomputable def witnessN₀ : WitnessBase →ₗ[ℝ] WitnessBase := Matrix.toLin' !![0, 1; 0, 0]

/-- Its base change to `W_L`: an `ℂ`-linear nilpotent commuting with the semi-linear action,
because it is defined over `ℝ`. -/
noncomputable def witnessN : Module.End ℂ WitnessSpace := LinearMap.baseChange ℂ witnessN₀

theorem witnessN₀_apply_one : witnessN₀ (Pi.basisFun ℝ (Fin 2) 1) = Pi.basisFun ℝ (Fin 2) 0 := by
  ext i
  fin_cases i <;>
    simp [witnessN₀, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Pi.basisFun_apply]

theorem witnessN₀_sq : witnessN₀ ∘ₗ witnessN₀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessN₀, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem witnessN_sq : witnessN * witnessN = 0 := by
  show LinearMap.baseChange ℂ witnessN₀ ∘ₗ LinearMap.baseChange ℂ witnessN₀ = 0
  rw [← LinearMap.baseChange_comp, witnessN₀_sq]
  ext x
  simp

theorem witnessN_ne_zero : witnessN ≠ 0 := by
  intro h
  have h1 : witnessN (witnessBasis 1) = 0 := by rw [h]; simp
  rw [witnessBasis, Algebra.TensorProduct.basis_apply] at h1
  rw [witnessN, LinearMap.baseChange_tmul, witnessN₀_apply_one,
    ← Algebra.TensorProduct.basis_apply (A := ℂ) (Pi.basisFun ℝ (Fin 2)) 0] at h1
  exact (Module.Basis.ne_zero witnessBasis 0) h1

/-- The base change commutes with the canonical semi-linear action: `N` is defined over `ℝ`. -/
theorem galoisTwist_witnessN (σ : Gal(ℂ/ℝ)) (x : WitnessSpace) :
    galoisTwist σ (witnessN x) = witnessN (galoisTwist σ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a w => simp [witnessN, LinearMap.baseChange_tmul]
  | add y z hy hz => simp only [map_add, hy, hz]

/-! ## The pair `(φ_+, φ_-)` -/

/-- `τ * τ = 1` for complex conjugation, **derived** from `RQ2-4.01-H1` + Galois via
`aut_mul_self` — the same route the census-carrying statements take. -/
theorem witnessTau_sq : (Complex.conjAe : Gal(ℂ/ℝ)) * Complex.conjAe = 1 :=
  aut_mul_self isGalois_real_complex Complex.finrank_real_complex Complex.conjAe

theorem witnessN_apply_apply (z : WitnessSpace) : witnessN (witnessN z) = 0 := by
  have h := witnessN_sq
  have := congrArg (fun f => (f : Module.End ℂ WitnessSpace) z) h
  simpa [Module.End.mul_apply] using this

theorem witness_inv_left : (1 - witnessN) * (1 + witnessN) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, witnessN_sq]
  abel

theorem witness_inv_right : (1 + witnessN) * (1 - witnessN) = 1 := by
  rw [mul_sub, mul_one, add_mul, one_mul, witnessN_sq]
  abel

/-- `φ_+ = φ_- = 1 + N`, read as an `ℂ`-linear isomorphism `W_+ → W_-^τ` with
`W_+ = W_- = ⊤` (clauses `RQ2-4.01-H5`, `RQ2-4.01-H6`).

@census none
-/
noncomputable def witnessPhi :
    (⊤ : Submodule ℂ WitnessSpace) ≃ₗ[ℂ] twist (Complex.conjAe : Gal(ℂ/ℝ))
      (⊤ : Submodule ℂ WitnessSpace) where
  toFun x := ⟨(1 + witnessN) (x : WitnessSpace), by rw [twist_top]; trivial⟩
  map_add' x y := Subtype.ext (by
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply, Module.End.one_apply,
      add_add_add_comm])
  map_smul' c x := Subtype.ext (by simp)
  invFun y := ⟨(1 - witnessN) (y : WitnessSpace), Submodule.mem_top⟩
  left_inv x := Subtype.ext (by
    show (1 - witnessN) ((1 + witnessN) (x : WitnessSpace)) = (x : WitnessSpace)
    have := congrArg (fun f => (f : Module.End ℂ WitnessSpace) (x : WitnessSpace))
      witness_inv_left
    simpa [Module.End.mul_apply] using this)
  right_inv y := Subtype.ext (by
    show (1 + witnessN) ((1 - witnessN) (y : WitnessSpace)) = (y : WitnessSpace)
    have := congrArg (fun f => (f : Module.End ℂ WitnessSpace) (y : WitnessSpace))
      witness_inv_right
    simpa [Module.End.mul_apply] using this)

@[simp]
theorem witnessPhi_coe (x : (⊤ : Submodule ℂ WitnessSpace)) :
    ((witnessPhi x : twist (Complex.conjAe : Gal(ℂ/ℝ)) (⊤ : Submodule ℂ WitnessSpace)) :
      WitnessSpace) = (1 + witnessN) (x : WitnessSpace) := rfl

/-- `n = 2N`, read as an endomorphism of `W_+ = ⊤`. -/
noncomputable def witnessNTop : Module.End ℂ (⊤ : Submodule ℂ WitnessSpace) where
  toFun x := ⟨(2 : ℂ) • witnessN (x : WitnessSpace), Submodule.mem_top⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by
    show (2 : ℂ) • witnessN (c • (x : WitnessSpace)) = c • ((2 : ℂ) • witnessN (x : WitnessSpace))
    rw [map_smul, smul_comm])

@[simp]
theorem witnessNTop_coe (x : (⊤ : Submodule ℂ WitnessSpace)) :
    ((witnessNTop x : (⊤ : Submodule ℂ WitnessSpace)) : WitnessSpace)
      = (2 : ℂ) • witnessN (x : WitnessSpace) := rfl

/-! ## The witness -/

/-- **`eq:nilpotency` holds for the witness, with `n = 2N`.** -/
theorem witness_nilpotency :
    (twistConj witnessTau_sq
        (witnessPhi : (⊤ : Submodule ℂ WitnessSpace) →ₗ[ℂ]
          twist (Complex.conjAe : Gal(ℂ/ℝ)) (⊤ : Submodule ℂ WitnessSpace))).comp
      (witnessPhi : (⊤ : Submodule ℂ WitnessSpace) →ₗ[ℂ]
        twist (Complex.conjAe : Gal(ℂ/ℝ)) (⊤ : Submodule ℂ WitnessSpace))
      = 1 + witnessNTop := by
  have hconj : ∀ z : WitnessSpace,
      galoisTwist (Complex.conjAe : Gal(ℂ/ℝ))
          ((1 + witnessN) (galoisTwist (Complex.conjAe : Gal(ℂ/ℝ)) z)) = (1 + witnessN) z := by
    intro z
    simp only [LinearMap.add_apply, Module.End.one_apply, map_add, galoisTwist_witnessN,
      galoisTwist_galoisTwist witnessTau_sq]
  refine LinearMap.ext fun x => Subtype.ext ?_
  show galoisTwist (Complex.conjAe : Gal(ℂ/ℝ))
      ((1 + witnessN) (galoisTwist (Complex.conjAe : Gal(ℂ/ℝ))
        ((1 + witnessN) (x : WitnessSpace))))
      = ((x : WitnessSpace) + (2 : ℂ) • witnessN (x : WitnessSpace))
  rw [hconj]
  simp only [LinearMap.add_apply, Module.End.one_apply, map_add, witnessN_apply_apply, add_zero,
    two_smul]
  abel

/-- The witness's `n` is nilpotent of exponent **exactly 2**: `n ≠ 0` and `n² = 0`
(clause `RQ2-4.01-H8` with `e = 2`).  `n = 2N` is non-zero **because `char ≠ 2`**. -/
theorem witnessNTop_ne_zero : witnessNTop ^ (2 - 1) ≠ 0 := by
  intro h
  rw [pow_one] at h
  refine witnessN_ne_zero (LinearMap.ext fun z => ?_)
  have hz : witnessNTop ⟨z, Submodule.mem_top⟩ = 0 := by rw [h]; simp
  have hz' : (2 : ℂ) • witnessN z = 0 := congrArg Subtype.val hz
  have := smul_eq_zero.mp hz'
  rcases this with h2 | h2
  · norm_num at h2
  · simpa using h2

theorem witnessNTop_sq : witnessNTop ^ 2 = 0 := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  show (2 : ℂ) • witnessN ((2 : ℂ) • witnessN (x : WitnessSpace)) = (0 : WitnessSpace)
  rw [map_smul, witnessN_apply_apply, smul_zero, smul_zero]

/-- **The hypothesis bundle of `prop:unipotentstabilization` is inhabited non-degenerately.**

This is not a restatement: it is `nilpotency_stabilizationStep` *applied* to the witness, so the
proposition's conclusion holds for a configuration with `n ≠ 0`.  Every hypothesis of `RQ2-4.01` is
discharged by a witness datum: `char ≠ 2` (`witness_two_ne_zero`), `L/K` quadratic
(`Complex.finrank_real_complex`) and Galois (`isGalois_real_complex`), `τ` non-trivial
(`witness_tau_ne_one`), `W_L = L ⊗_K W_K` (`WitnessSpace`), `W_±` subspaces (`⊤`), `φ_±`
isomorphisms (`witnessPhi`), `eq:nilpotency` (`witness_nilpotency`) and the **exact** exponent
`e = 2` (`witnessNTop_ne_zero`, `witnessNTop_sq`).

@census none
-/
theorem witness_applies :
    ∃ ñ : Module.End ℂ (⊤ : Submodule ℂ WitnessSpace),
      (twistConj (aut_mul_self isGalois_real_complex Complex.finrank_real_complex Complex.conjAe)
            (stabilizationStep witness_two_ne_zero
              (aut_mul_self isGalois_real_complex Complex.finrank_real_complex Complex.conjAe)
              (witnessPhi : (⊤ : Submodule ℂ WitnessSpace) →ₗ[ℂ] twist (Complex.conjAe : Gal(ℂ/ℝ)) (⊤ : Submodule ℂ WitnessSpace)) (witnessPhi : (⊤ : Submodule ℂ WitnessSpace) →ₗ[ℂ] twist (Complex.conjAe : Gal(ℂ/ℝ)) (⊤ : Submodule ℂ WitnessSpace)))).comp
          (stabilizationStep witness_two_ne_zero
            (aut_mul_self isGalois_real_complex Complex.finrank_real_complex Complex.conjAe)
            (witnessPhi : (⊤ : Submodule ℂ WitnessSpace) →ₗ[ℂ] twist (Complex.conjAe : Gal(ℂ/ℝ)) (⊤ : Submodule ℂ WitnessSpace)) (witnessPhi : (⊤ : Submodule ℂ WitnessSpace) →ₗ[ℂ] twist (Complex.conjAe : Gal(ℂ/ℝ)) (⊤ : Submodule ℂ WitnessSpace))) = 1 + ñ
        ∧ ñ ^ (2 ⌈/⌉ 2) = 0 :=
  nilpotency_stabilizationStep witness_two_ne_zero isGalois_real_complex
    Complex.finrank_real_complex Complex.conjAe witness_tau_ne_one witnessPhi witnessPhi
    witnessNTop 2 (by norm_num) witness_nilpotency witnessNTop_ne_zero witnessNTop_sq

end RationalQuivers.Unipotent
