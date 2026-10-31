module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import RationalQuivers.Unipotent.Twist

@[expose] public section

/-!
# Unipotent square roots

Formalizes §4.2 of `latex/rational_quivers.tex` (census `RQ2-4.05`, `RQ2-4.06`, `RQ2-4.07`,
`RQ2-4.08`, `RQ2-4.09`).

## Main definitions / results
* `RationalQuivers.Unipotent.sqrtSeq` — the Newton iteration `φ_{k+1} = ½(φ_k + φ_k^{-1} φ)` of
  the source's proof, and the recursion clause `RQ2-4.08-H1`.
* `RationalQuivers.Unipotent.sqrt` — the unipotent square root `φ^{1/2}`
  (`prop:unipotentsquareroots`).
* `RationalQuivers.Unipotent.sqrt_spec` — Proposition `prop:unipotentsquareroots` (census
  `RQ2-4.05`): existence, (a) unipotence, (b) the square identity; with `sqrt_commute` (c),
  `sqrt_semilinearConj` (d), `sqrt_natural` (e) and `sqrt_unique` (uniqueness).
* `RationalQuivers.Unipotent.sqrt_natural`, `…sqrtOfScalarPlusNilpotent_natural` — clause **(e)**
  of `prop:unipotentsquareroots` (`eq:squarerootnaturality`, census clause `RQ2-4.05-C7`), added to
  the source on 2026-09-11 and relocated here from stage S8 under `R-PROC-4` on the same date.
* `RationalQuivers.Unipotent.sqrt_inv` — `(φ^{1/2})^{-1} = (φ^{-1})^{1/2}`
  (`eq:squarerootinverses`, census `RQ2-4.06`).
* `RationalQuivers.Unipotent.sqrtOfScalarPlusNilpotent` — Definition `def:squareroots` (census
  `RQ2-4.07`): `φ^{1/2} := γ · (γ^{-2} φ)^{1/2}` for `φ = γ² · 1 + n`.
* `RationalQuivers.Unipotent.sqrt_galois_equivariant` — `eq:squarerootgaloisequivariance`
  (census `RQ2-4.09`), with the uniqueness-up-to-sign and `φ^{-1/2}` companions.

## Implementation notes

**`sqrt` is total.**  Following mathlib's `Ring.inverse` idiom, `sqrt h2 φ` is defined for every
`φ` and is the square root only under the hypothesis `IsNilpotent (φ - 1)` of
`eq:phinilpotency`; outside that case its value is junk (`0`).  This keeps the *hypotheses of the
source's statements in the statements* rather than hiding them inside the definition's arguments,
and it is what lets `RQ2-4.06` (`(φ^{1/2})^{-1} = (φ^{-1})^{1/2}`) be written without first
proving that `φ^{-1}` is unipotent.

**"Automorphism" is derivable.**  The source assumes `φ : W → W` is an *automorphism* with
`φ = 1 + n`, `n` nilpotent (clause `RQ2-4.05-H3`).  In Lean `IsNilpotent (φ - 1)` already implies
`IsUnit φ` (`isUnit_of_sub_one_isNilpotent`), so taking the operator and the nilpotency of
`φ - 1` as the hypotheses carries the clause without adding a redundant assumption; the
automorphism half is recorded as a conclusion of `sqrt_spec` for the square root itself.

**char ≠ 2 is carried structurally.**  Every declaration of this file mentions `sqrt` or
`sqrtOfScalarPlusNilpotent`, both of which take the proof of `(2 : L) ≠ 0` as an explicit
argument (`Unipotent/Nilpotent.lean`, `half`).  So clauses `RQ2-4.05-H1`, `RQ2-4.06-H2` and the
standing clause `RQ2-4.07-Hs1` are present in every elaborated signature, not merely in a
`variable` block that Lean would prune (`CONVENTIONS.md` §3).
-/

universe u v w

open scoped TensorProduct

namespace RationalQuivers.Unipotent

variable {L : Type u} [Field L] {W : Type v} [AddCommGroup W] [Module L W]

/-! ## The construction -/

/-- The Newton iteration of the source's proof of `prop:unipotentsquareroots`:
`φ_0 := φ` and `φ_{k+1} := ½(φ_k + φ_k^{-1} ∘ φ)`.

The inverse is mathlib's junk-valued `Ring.inverse`; every iterate is in fact a unit
(`sqrtSeq_isUnit`), so this agrees with the source's `φ_k^{-1}`.

@census none
-/
noncomputable def sqrtSeq (h2 : (2 : L) ≠ 0) (φ : Module.End L W) : ℕ → Module.End L W
  | 0 => φ
  | k + 1 => half h2 • (sqrtSeq h2 φ k + Ring.inverse (sqrtSeq h2 φ k) * φ)

@[simp] theorem sqrtSeq_zero (h2 : (2 : L) ≠ 0) (φ : Module.End L W) : sqrtSeq h2 φ 0 = φ := rfl

theorem sqrtSeq_succ (h2 : (2 : L) ≠ 0) (φ : Module.End L W) (k : ℕ) :
    sqrtSeq h2 φ (k + 1)
      = half h2 • (sqrtSeq h2 φ k + Ring.inverse (sqrtSeq h2 φ k) * φ) := rfl

theorem sqrtSeq_succ' (h2 : (2 : L) ≠ 0) (φ : Module.End L W) (k : ℕ) :
    sqrtSeq h2 φ (k + 1) = sqrtStep h2 φ (sqrtSeq h2 φ k) := rfl

/-- The two invariants of the Newton sequence, proved together because each step needs both:
every iterate is `1 + nilpotent` and commutes with `φ`. -/
theorem sqrtSeq_aux (h2 : (2 : L) ≠ 0) {φ : Module.End L W} (hφ : IsNilpotent (φ - 1)) (k : ℕ) :
    IsNilpotent (sqrtSeq h2 φ k - 1) ∧ Commute (sqrtSeq h2 φ k) φ := by
  induction k with
  | zero => exact ⟨by simpa using hφ, Commute.refl φ⟩
  | succ k ih =>
      obtain ⟨hn, hc⟩ := ih
      rw [sqrtSeq_succ']
      exact ⟨sqrtStep_isNilpotent_sub_one h2 hn hφ hc,
        sqrtStep_commute h2 (isUnit_of_sub_one_isNilpotent hn) hc⟩

/-- Every iterate is `1 + nilpotent` (`eq:phinilpotency` along the iteration). -/
theorem sqrtSeq_isNilpotent_sub_one (h2 : (2 : L) ≠ 0) {φ : Module.End L W}
    (hφ : IsNilpotent (φ - 1)) (k : ℕ) : IsNilpotent (sqrtSeq h2 φ k - 1) :=
  (sqrtSeq_aux h2 hφ k).1

/-- Every iterate commutes with `φ`. -/
theorem sqrtSeq_commute_self (h2 : (2 : L) ≠ 0) {φ : Module.End L W} (hφ : IsNilpotent (φ - 1))
    (k : ℕ) : Commute (sqrtSeq h2 φ k) φ := (sqrtSeq_aux h2 hφ k).2

/-- Every iterate of the Newton sequence is an automorphism, so the inverse in the recursion is
the honest inverse. -/
theorem sqrtSeq_isUnit (h2 : (2 : L) ≠ 0) (φ : Module.End L W) (hφ : IsNilpotent (φ - 1))
    (k : ℕ) : IsUnit (sqrtSeq h2 φ k) :=
  isUnit_of_sub_one_isNilpotent (sqrtSeq_isNilpotent_sub_one h2 hφ k)

/-- Every iterate commutes with anything that commutes with `φ`; this is what carries
`prop:unipotentsquareroots`(c) through the construction. -/
theorem sqrtSeq_commute (h2 : (2 : L) ≠ 0) {φ ψ : Module.End L W} (hφ : IsNilpotent (φ - 1))
    (hcom : Commute φ ψ) (k : ℕ) : Commute (sqrtSeq h2 φ k) ψ := by
  induction k with
  | zero => exact hcom
  | succ k ih =>
      rw [sqrtSeq_succ', sqrtStep]
      refine Commute.smul_left ?_ _
      refine ih.add_left (Commute.mul_left ?_ hcom)
      exact Commute.inverse_left (sqrtSeq_isUnit h2 φ hφ k) ih

/-- The **quantitative** form of the source's `phi_k^2 - phi = tilde n_k` with the exponent
halving at every step: after `k` steps the error kills the `(e - k + 1)`-st power. -/
theorem sqrtSeq_error (h2 : (2 : L) ≠ 0) {φ : Module.End L W} (hφ : IsNilpotent (φ - 1))
    {e : ℕ} (he : (φ - 1) ^ e = 0) (k : ℕ) :
    ((sqrtSeq h2 φ k) ^ 2 - φ) ^ (e - k + 1) = 0 := by
  induction k with
  | zero =>
      have hEq : (sqrtSeq h2 φ 0) ^ 2 - φ = φ * (φ - 1) := by
        rw [sqrtSeq_zero, mul_sub, mul_one, sq]
      have hc : Commute φ (φ - 1) := (Commute.refl φ).sub_right (Commute.one_right φ)
      rw [hEq, hc.mul_pow, Nat.sub_zero,
        show (φ - 1) ^ (e + 1) = (φ - 1) ^ e * (φ - 1) from pow_succ _ _, he, zero_mul, mul_zero]
  | succ k ih =>
      have hstep := sqrtStep_error_pow h2 (sqrtSeq_isUnit h2 φ hφ k)
        (sqrtSeq_commute_self h2 hφ k) ih
      rw [← sqrtSeq_succ'] at hstep
      have hle : (e - k + 1) ⌈/⌉ 2 ≤ e - (k + 1) + 1 := by
        rw [Nat.ceilDiv_eq_add_pred_div]
        omega
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
      rw [hj, pow_add, hstep, zero_mul]

/-- Past the nilpotency exponent the iterate is an honest square root. -/
theorem sqrtSeq_sq (h2 : (2 : L) ≠ 0) {φ : Module.End L W} (hφ : IsNilpotent (φ - 1))
    {e : ℕ} (he : (φ - 1) ^ e = 0) {k : ℕ} (hk : e ≤ k) : (sqrtSeq h2 φ k) ^ 2 = φ := by
  have h := sqrtSeq_error h2 hφ he k
  rw [Nat.sub_eq_zero_of_le hk, Nat.zero_add, pow_one] at h
  exact sub_eq_zero.mp h

/-- Past the nilpotency exponent the sequence is **constant**: this is the source's
"`phi_{k+1} = phi_k`, i.e. the sequence converges in the discrete topology". -/
theorem sqrtSeq_eq_base (h2 : (2 : L) ≠ 0) {φ : Module.End L W} (hφ : IsNilpotent (φ - 1))
    {e : ℕ} (he : (φ - 1) ^ e = 0) : ∀ {k : ℕ}, e ≤ k → sqrtSeq h2 φ k = sqrtSeq h2 φ e := by
  intro k hk
  induction k with
  | zero => simp_all
  | succ k ih =>
      rcases Nat.lt_or_ge e (k + 1) with h | h
      · have hek : e ≤ k := by omega
        rw [sqrtSeq_succ', sqrtStep_of_sq_eq h2 (sqrtSeq_isUnit h2 φ hφ k)
          (sqrtSeq_sq h2 hφ he hek)]
        exact ih hek
      · have : e = k + 1 := le_antisymm hk h
        rw [this]

open Classical in
/-- The **unipotent square root** `φ^{1/2}` of `prop:unipotentsquareroots`: the value of the
Newton iteration `sqrtSeq` at any index past the nilpotency exponent of `φ - 1`, at which point
the sequence is constant.

Total, in mathlib's `Ring.inverse` idiom: outside the unipotent case the value is `0` and no
statement of this file refers to it.  See the module docstring.

@census none
-/
noncomputable def sqrt (h2 : (2 : L) ≠ 0) (φ : Module.End L W) : Module.End L W :=
  if h : IsNilpotent (φ - 1) then sqrtSeq h2 φ h.choose else 0

/-- In the unipotent case the square root is the iteration run to (any index past) its
stabilization point: this is the "reached in finitely many explicit steps" reading of the
source's `k ≫ 0`. -/
theorem sqrt_eq_sqrtSeq (h2 : (2 : L) ≠ 0) (φ : Module.End L W) (e : ℕ)
    (he : (φ - 1) ^ e = 0) (k : ℕ) (hk : e ≤ k) : sqrt h2 φ = sqrtSeq h2 φ k := by
  classical
  have hφ : IsNilpotent (φ - 1) := ⟨e, he⟩
  rw [sqrt, dif_pos hφ]
  have hchoose : (φ - 1) ^ hφ.choose = 0 := hφ.choose_spec
  have h1 : sqrtSeq h2 φ (max e hφ.choose) = sqrtSeq h2 φ e :=
    sqrtSeq_eq_base h2 hφ he (le_max_left _ _)
  have h2' : sqrtSeq h2 φ (max e hφ.choose) = sqrtSeq h2 φ hφ.choose :=
    sqrtSeq_eq_base h2 hφ hchoose (le_max_right _ _)
  have h3 : sqrtSeq h2 φ k = sqrtSeq h2 φ e := sqrtSeq_eq_base h2 hφ he hk
  rw [← h2', h1, ← h3]

/-! ## `prop:unipotentsquareroots` -/

/-- **Proposition** (`prop:unipotentsquareroots`, §4.2 of the source).

Let `L` be a field of characteristic `≠ 2` (clause `RQ2-4.05-H1`, the argument `h2`), `W` an
`L`-vector space (clause `RQ2-4.05-H2`) and `φ : W → W` an automorphism with `φ = 1_W + n`,
`n` nilpotent (`eq:phinilpotency`, clause `RQ2-4.05-H3`).  Then `φ^{1/2} := sqrt h2 φ` is an
automorphism (clause `RQ2-4.05-C1`) with

* (a) `φ^{1/2} = 1_W + m` for a nilpotent `m` (clause `RQ2-4.05-C2`);
* (b) `(φ^{1/2})² = φ` (clause `RQ2-4.05-C3`).

Properties (c) and (d) are `sqrt_commute` and `sqrt_semilinearConj`, and property **(e)** —
naturality along an arbitrary `L`-linear intertwiner, added to the source by the author's
subsidiary ruling of 2026-09-11 on `AN-41`/`AN-42` and booked by census r14 as clause
`RQ2-4.05-C7` — is `sqrt_natural`, with `sqrtOfScalarPlusNilpotent_natural` for its second
sentence; the uniqueness statement is `sqrt_unique`.

@census    RQ2-4.05
@source    prop:unipotentsquareroots
@clauses   RQ2-4.05-H1, RQ2-4.05-H2, RQ2-4.05-H3, RQ2-4.05-C1, RQ2-4.05-C2, RQ2-4.05-C3
@imports   none
@divergence none
-/
theorem sqrt_spec (h2 : (2 : L) ≠ 0) (φ n : Module.End L W) (hn : IsNilpotent n)
    (hφ : φ = 1 + n) :
    IsUnit (sqrt h2 φ) ∧ IsNilpotent (sqrt h2 φ - 1) ∧ (sqrt h2 φ) ^ 2 = φ := by
  have hφ1 : IsNilpotent (φ - 1) := by rw [hφ]; simpa using hn
  obtain ⟨e, he⟩ := hφ1
  have hnil : IsNilpotent (φ - 1) := ⟨e, he⟩
  rw [sqrt_eq_sqrtSeq h2 φ e he e le_rfl]
  exact ⟨sqrtSeq_isUnit h2 φ hnil e, sqrtSeq_isNilpotent_sub_one h2 hnil e,
    sqrtSeq_sq h2 hnil he le_rfl⟩

/-- `prop:unipotentsquareroots`(c) (clause `RQ2-4.05-C4`): the square root commutes with every
`L`-linear automorphism that commutes with `φ`.

@census    none (auxiliary; discharges clause `RQ2-4.05-C4` of `RQ2-4.05`)
@source    prop:unipotentsquareroots
@clauses   RQ2-4.05-C4
@imports   none
@divergence none
-/
theorem sqrt_commute (h2 : (2 : L) ≠ 0) (φ n : Module.End L W) (hn : IsNilpotent n)
    (hφ : φ = 1 + n) (ψ : Module.End L W) (hψ : IsUnit ψ) (h : Commute φ ψ) :
    Commute (sqrt h2 φ) ψ := by
  have hφ1 : IsNilpotent (φ - 1) := by rw [hφ]; simpa using hn
  obtain ⟨e, he⟩ := hφ1
  have hnil : IsNilpotent (φ - 1) := ⟨e, he⟩
  rw [sqrt_eq_sqrtSeq h2 φ e he e le_rfl]
  exact sqrtSeq_commute h2 hnil h e

/-- Conjugation by a semi-linear automorphism commutes with the whole Newton iteration: the
recursion is built from `+`, `*`, `Ring.inverse` and the scalar `½`, and conjugation respects all
four (`aut_half`: a field automorphism fixes `½`).

@census none
-/
theorem semilinearConj_sqrtSeq {K : Type u} [Field K] [Algebra K L] (h2 : (2 : L) ≠ 0)
    (σ : Gal(L/K)) (ψ : W ≃+ W) (hψ : ∀ (a : L) (x : W), ψ (a • x) = σ a • ψ x)
    {φ : Module.End L W} (hφ : IsNilpotent (φ - 1)) (k : ℕ) :
    semilinearConj σ ψ hψ (sqrtSeq h2 φ k) = sqrtSeq h2 (semilinearConj σ ψ hψ φ) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [sqrtSeq_succ', sqrtSeq_succ', sqrtStep, sqrtStep, semilinearConj_smul, aut_half,
        semilinearConj_add, semilinearConj_mul,
        semilinearConj_inverse (sqrtSeq_isUnit h2 φ hφ k), ih]

/-- `prop:unipotentsquareroots`(d), `eq:semilinearconjugation` (clause `RQ2-4.05-C5`): the square
root commutes with conjugation by a semi-linear automorphism,
`(ψ φ ψ^{-1})^{1/2} = ψ φ^{1/2} ψ^{-1}`.

@census    none (auxiliary; discharges clause `RQ2-4.05-C5` of `RQ2-4.05`)
@source    prop:unipotentsquareroots
@clauses   RQ2-4.05-C5
@imports   none
@divergence WEAKENED_OR_PARTIAL. **Rewritten 2026-10-03** (docstring-only `R-PROC-4` amendment of
frozen S6, coordinator ruling `R-FR-9`, final-release WP-16b, stale item R1, `MISMATCH-TRIAGE.md`
row #1). The amended source (census r18, FA-29) states (d) for **every** field automorphism `σ` of
`L`, **every** `L`-vector space `W'` and **every** `σ`-semi-linear bijection `ψ : W → W'`. It says
that `ψφψ⁻¹` again satisfies `eq:phinilpotency`, and that `eq:semilinearconjugation` holds. This
theorem is weaker in three ways. It takes `W' = W` (`ψ : W ≃+ W`). It takes `σ ∈ Gal(L/K)` rather
than an arbitrary automorphism of `L`. And it proves the nilpotency of `ψφψ⁻¹ − 1` inside the proof
but does not state it. The faithful witness is `RationalQuivers.Unipotent.sqrt_semilinearConjTo`
(`Unipotent/SemilinearTransport.lean`, final-release WP-16a). It covers any `σ : L ≃+* L`, any
`W'` and any `ψ : W ≃+ W'`, and states both conjuncts. This theorem keeps its `@clauses` citation
because `rqaudit clauses` binds a clause only to a claimant of its row or a same-module helper of
one, and the WP-16a witness lives in another module. Until this amendment this field read
`JUSTIFIED_REFORMULATION (generalization)` and said that the theorem "strictly implies the source's
reading", because the source then stated (d) only for `W = L ⊗_K W_K`. Against the amended source
that is the reverse of the truth. `sqrt_galois_equivariant` still applies this theorem in the
`W = L ⊗_K W_K` situation, which is all that `RQ2-4.09` needs.
-/
theorem sqrt_semilinearConj {K : Type u} [Field K] [Algebra K L] (h2 : (2 : L) ≠ 0)
    (σ : Gal(L/K)) (ψ : W ≃+ W) (hψ : ∀ (a : L) (x : W), ψ (a • x) = σ a • ψ x)
    (φ n : Module.End L W) (hn : IsNilpotent n) (hφ : φ = 1 + n) :
    sqrt h2 (semilinearConj σ ψ hψ φ) = semilinearConj σ ψ hψ (sqrt h2 φ) := by
  have hφ1 : IsNilpotent (φ - 1) := by rw [hφ]; simpa using hn
  obtain ⟨e, he⟩ := hφ1
  have hnil : IsNilpotent (φ - 1) := ⟨e, he⟩
  have hc : semilinearConj σ ψ hψ φ - 1 = semilinearConj σ ψ hψ (φ - 1) := by
    rw [semilinearConj_sub, semilinearConj_one]
  have he' : (semilinearConj σ ψ hψ φ - 1) ^ e = 0 := by
    rw [hc, ← semilinearConj_pow, he, semilinearConj_zero]
  rw [sqrt_eq_sqrtSeq h2 _ e he' e le_rfl, sqrt_eq_sqrtSeq h2 φ e he e le_rfl,
    semilinearConj_sqrtSeq h2 σ ψ hψ hnil e]

/-- `prop:unipotentsquareroots`, uniqueness (clause `RQ2-4.05-C6`): `φ^{1/2}` is uniquely
determined by (a) and (b) **alone**.

@census    none (auxiliary; discharges clause `RQ2-4.05-C6` of `RQ2-4.05`)
@source    prop:unipotentsquareroots
@clauses   RQ2-4.05-C6
@imports   none
@divergence none
-/
theorem sqrt_unique (h2 : (2 : L) ≠ 0) (φ ψ m : Module.End L W) (hm : IsNilpotent m)
    (hψ : ψ = 1 + m) (hsq : ψ ^ 2 = φ) : ψ = sqrt h2 φ := by
  -- `ψ` is unipotent, hence so is `φ = ψ²`
  have hψ1 : IsNilpotent (ψ - 1) := by rw [hψ]; simpa using hm
  have hψu : IsUnit ψ := isUnit_of_sub_one_isNilpotent hψ1
  have hcomψφ : Commute ψ φ := by rw [← hsq]; exact (Commute.refl ψ).pow_right 2
  have hφ1 : IsNilpotent (φ - 1) := by
    rw [← hsq]
    have : ψ ^ 2 - 1 = (ψ - 1) * (ψ + 1) := by
      rw [sub_mul, mul_add, mul_one, one_mul, sq]; abel
    rw [this]
    refine Commute.isNilpotent_mul_right ?_ hψ1
    exact ((Commute.refl ψ).sub_left (Commute.one_left ψ)).add_right (Commute.one_right _)
  -- the square root `S` provided by the construction
  set S := sqrt h2 φ with hS
  obtain ⟨hSu, hSnil, hSsq⟩ := sqrt_spec h2 φ (φ - 1) (by simpa using hφ1) (by abel)
  have hcomSψ : Commute S ψ := sqrt_commute h2 φ (φ - 1) (by simpa using hφ1) (by abel) ψ hψu
    hcomψφ.symm
  -- `ν := ψ S^{-1}` is unipotent with `ν² = 1`
  have hbnil : IsNilpotent (Ring.inverse S - 1) := isNilpotent_inverse_sub_one hSnil
  have hcomb : Commute ψ (Ring.inverse S) := (Commute.inverse_left hSu hcomSψ).symm
  set ν := ψ * Ring.inverse S with hν
  have hνnil : IsNilpotent (ν - 1) := by
    have hEq : ν - 1 = (ψ - 1) * Ring.inverse S + (Ring.inverse S - 1) := by
      rw [hν, sub_mul, one_mul]; abel
    rw [hEq]
    refine Commute.isNilpotent_add ?_ ?_ hbnil
    · refine Commute.mul_left ?_ ?_
      · exact (hcomb.sub_left (Commute.one_left _)).sub_right (Commute.one_right _)
      · exact (Commute.refl _).sub_right (Commute.one_right _)
    · exact Commute.isNilpotent_mul_right
        (hcomb.sub_left (Commute.one_left _)) hψ1
  have hνsq : ν ^ 2 = 1 := by
    have hcomb2 : Commute (Ring.inverse S) ψ := hcomb.symm
    have : ν ^ 2 = ψ ^ 2 * (Ring.inverse S) ^ 2 := by
      rw [hν, sq, sq, sq]
      calc ψ * Ring.inverse S * (ψ * Ring.inverse S)
          = ψ * (Ring.inverse S * ψ) * Ring.inverse S := by simp [mul_assoc]
        _ = ψ * (ψ * Ring.inverse S) * Ring.inverse S := by rw [hcomb2.eq]
        _ = ψ * ψ * (Ring.inverse S * Ring.inverse S) := by simp [mul_assoc]
    rw [this, hsq, Ring.inverse_pow, hSsq]
    exact Ring.mul_inverse_cancel φ (isUnit_of_sub_one_isNilpotent hφ1)
  -- a unipotent square root of `1` is `1`
  have hx : (ν - 1) * (1 + 1 + (ν - 1)) = 0 := by
    have : (ν - 1) * (1 + 1 + (ν - 1)) = ν ^ 2 - 1 := by
      rw [show (1 : Module.End L W) + 1 + (ν - 1) = ν + 1 by abel, sub_mul, mul_add, mul_one,
        one_mul, sq]
      abel
    rw [this, hνsq, sub_self]
  have hν1 : ν - 1 = 0 := eq_zero_of_mul_two_add h2 hνnil hx
  have : ν = 1 := by rwa [sub_eq_zero] at hν1
  -- hence `ψ = S`
  have := congrArg (fun z => z * S) this
  simp only [one_mul, hν, mul_assoc, Ring.inverse_mul_cancel S hSu, mul_one] at this
  exact this

/-! ## `prop:unipotentsquareroots` clause (e) — naturality in an arbitrary intertwiner

**Added 2026-09-11 under `R-PROC-4` (round 3 of the seven-errata execution; coordinator ruling
`R-ERR-2` of the round-3 brief).**  `prop:unipotentsquareroots` gained a fifth itemized property
**(e)** by the paper author's subsidiary ruling of 2026-09-11 on `AN-41`/`AN-42`
(`workflow/reports/AUTHOR-QUEUE.md`, the `AUTHOR RULING, 2026-09-11` block): the square root is
natural along an **arbitrary**, not necessarily invertible, `L`-linear intertwiner
(`eq:squarerootnaturality`).  The census books it as `RQ2-4.05-C7` at revision r14
(`census-v1.11`).

The three declarations below were first written at stage **S8** (`Gelfand/Equivalence.lean`,
`section SqrtNatural`) as tree-side helpers for the corrected left-hand squares of `RQ-5.05-C25`;
they were already stated at this file's generality — two `L`-vector spaces and a bare `→ₗ[L]`
between them — so clause (e) lives **here**, in `RQ2-4.05`'s own stage, and S8 kept thin aliases
(deleted with v1's `Gelfand/Equivalence.lean` at WP-13, `ae9eda9`; 2026-10-21 note, O-V2-6 round 2).
The proof is the source's own one-sentence induction: every step of the Newton iteration is built
from `φ`, `+` and the inverse of the previous iterate, and all three commute with an intertwiner of
two *different* spaces — the inverse because both iterates are units (`sqrtSeq_isUnit`).
-/

section Natural

variable {W₁ : Type v} {W₂ : Type w} [AddCommGroup W₁] [Module L W₁]
  [AddCommGroup W₂] [Module L W₂]

/-- An intertwiner of two units intertwines their inverses.  @census none (helper for clause
`RQ2-4.05-C7`) -/
theorem inverse_natural {S₁ : Module.End L W₁} {S₂ : Module.End L W₂}
    (hu₁ : IsUnit S₁) (hu₂ : IsUnit S₂) (A : W₁ →ₗ[L] W₂)
    (hA : ∀ x, A (S₁ x) = S₂ (A x)) (x : W₁) :
    A (Ring.inverse S₁ x) = Ring.inverse S₂ (A x) := by
  have h1 : S₁ (Ring.inverse S₁ x) = x := by
    have h := Ring.mul_inverse_cancel S₁ hu₁
    calc S₁ (Ring.inverse S₁ x) = (S₁ * Ring.inverse S₁) x := rfl
      _ = x := by rw [h]; rfl
  have h2 : ∀ y : W₂, Ring.inverse S₂ (S₂ y) = y := by
    intro y
    have h := Ring.inverse_mul_cancel S₂ hu₂
    calc Ring.inverse S₂ (S₂ y) = (Ring.inverse S₂ * S₂) y := rfl
      _ = y := by rw [h]; rfl
  calc A (Ring.inverse S₁ x) = Ring.inverse S₂ (S₂ (A (Ring.inverse S₁ x))) := (h2 _).symm
    _ = Ring.inverse S₂ (A (S₁ (Ring.inverse S₁ x))) := by rw [hA]
    _ = Ring.inverse S₂ (A x) := by rw [h1]

/-- The Newton iteration of `prop:unipotentsquareroots` is natural in an intertwiner — the
induction the source's one-sentence proof of clause (e) performs.
@census none (helper for clause `RQ2-4.05-C7`) -/
theorem sqrtSeq_natural (h2 : (2 : L) ≠ 0) {φ₁ : Module.End L W₁} {φ₂ : Module.End L W₂}
    (h₁ : IsNilpotent (φ₁ - 1)) (h₂ : IsNilpotent (φ₂ - 1))
    (A : W₁ →ₗ[L] W₂) (hA : ∀ x, A (φ₁ x) = φ₂ (A x)) (k : ℕ) (x : W₁) :
    A (sqrtSeq h2 φ₁ k x) = sqrtSeq h2 φ₂ k (A x) := by
  induction k generalizing x with
  | zero => exact hA x
  | succ k ih =>
      have e1 : A ((sqrtSeq h2 φ₁ k + Ring.inverse (sqrtSeq h2 φ₁ k) * φ₁) x)
          = (sqrtSeq h2 φ₂ k + Ring.inverse (sqrtSeq h2 φ₂ k) * φ₂) (A x) := by
        show A (sqrtSeq h2 φ₁ k x + Ring.inverse (sqrtSeq h2 φ₁ k) (φ₁ x))
            = sqrtSeq h2 φ₂ k (A x) + Ring.inverse (sqrtSeq h2 φ₂ k) (φ₂ (A x))
        rw [map_add, ih, inverse_natural (sqrtSeq_isUnit h2 φ₁ h₁ k)
          (sqrtSeq_isUnit h2 φ₂ h₂ k) A (fun y => ih y) (φ₁ x), hA]
      rw [sqrtSeq_succ, sqrtSeq_succ, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, e1]

/-- **`prop:unipotentsquareroots` clause (e)** (`eq:squarerootnaturality`, census clause
`RQ2-4.05-C7`): for every `L`-vector space `W₂`, every automorphism `φ₂` of `W₂` satisfying
`eq:phinilpotency`, and every `L`-linear map `A : W₁ → W₂` — **not necessarily invertible** —
`A ∘ φ₁ = φ₂ ∘ A` implies `A ∘ φ₁^{1/2} = φ₂^{1/2} ∘ A`.

@census    none (auxiliary; discharges census clause `RQ2-4.05-C7` of `RQ2-4.05`)
@source    prop:unipotentsquareroots
@clauses   RQ2-4.05-C7
@imports   none
@divergence none -/
theorem sqrt_natural (h2 : (2 : L) ≠ 0) {φ₁ : Module.End L W₁} {φ₂ : Module.End L W₂}
    (h₁ : IsNilpotent (φ₁ - 1)) (h₂ : IsNilpotent (φ₂ - 1))
    (A : W₁ →ₗ[L] W₂) (hA : ∀ x, A (φ₁ x) = φ₂ (A x)) (x : W₁) :
    A (sqrt h2 φ₁ x) = sqrt h2 φ₂ (A x) := by
  obtain ⟨e₁, he₁⟩ := h₁
  obtain ⟨e₂, he₂⟩ := h₂
  have hk₁ : (φ₁ - 1) ^ (max e₁ e₂) = 0 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (le_max_left e₁ e₂)
    rw [hd, pow_add, he₁, zero_mul]
  have hk₂ : (φ₂ - 1) ^ (max e₁ e₂) = 0 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (le_max_right e₁ e₂)
    rw [hd, pow_add, he₂, zero_mul]
  rw [sqrt_eq_sqrtSeq h2 φ₁ (max e₁ e₂) hk₁ (max e₁ e₂) le_rfl,
    sqrt_eq_sqrtSeq h2 φ₂ (max e₁ e₂) hk₂ (max e₁ e₂) le_rfl]
  exact sqrtSeq_natural h2 ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ A hA (max e₁ e₂) x

end Natural

/-! ## `eq:squarerootinverses` -/

/-- **Corollary** (`UNLABELED-sqrt-inverses`, §4.2 of the source).

For an automorphism `φ` of an `L`-vector space with `φ = 1 + n`, `n` nilpotent
(`eq:phinilpotency`, clause `RQ2-4.06-H1`), over a field of characteristic `≠ 2` (clause
`RQ2-4.06-H2`, the argument `h2`, inherited from `prop:unipotentsquareroots`):
`(φ^{1/2})^{-1} = (φ^{-1})^{1/2}` (`eq:squarerootinverses`, clause `RQ2-4.06-C1`).

@census    RQ2-4.06
@source    cor:sqrtinverses
@clauses   RQ2-4.06-H1, RQ2-4.06-H2, RQ2-4.06-C1
@imports   none
@divergence none
-/
theorem sqrt_inv (h2 : (2 : L) ≠ 0) (φ n : Module.End L W) (hn : IsNilpotent n)
    (hφ : φ = 1 + n) :
    Ring.inverse (sqrt h2 φ) = sqrt h2 (Ring.inverse φ) := by
  have hφ1 : IsNilpotent (φ - 1) := by rw [hφ]; simpa using hn
  obtain ⟨hSu, hSnil, hSsq⟩ := sqrt_spec h2 φ n hn hφ
  refine sqrt_unique h2 (Ring.inverse φ) (Ring.inverse (sqrt h2 φ))
    (Ring.inverse (sqrt h2 φ) - 1) (isNilpotent_inverse_sub_one hSnil) (by abel) ?_
  rw [Ring.inverse_pow, hSsq]

/-! ## `def:squareroots` — the general (non-unipotent) square root -/

/-- **Definition** (`def:squareroots`, §4.2 of the source).

For an automorphism `φ` of an `L`-vector space `W` with `φ = γ² · 1_W + n`, `γ ∈ L^×` and `n`
nilpotent (`eq:phigammanilpotency`, clauses `RQ2-4.07-H1`, `RQ2-4.07-H2`), the *(unipotent) square
root of `φ` with respect to the square root `γ` of `γ²`* is
`φ^{1/2} := γ · (γ^{-2} φ)^{1/2}` (clause `RQ2-4.07-C1`).

The dependence on the chosen `γ` (clause `RQ2-4.07-C2`) is structural: `γ` is an explicit argument,
and `sqrtOfScalarPlusNilpotent_neg` records that the other choice `-γ` gives the negative.
The standing characteristic hypothesis of §4.2 (clause `RQ2-4.07-Hs1`) is the argument `h2`, which
`sqrt` demands; without it the unipotent square root through which this definition is written does
not exist.

@census    RQ2-4.07
@source    def:squareroots
@clauses   RQ2-4.07-Hs1, RQ2-4.07-H1, RQ2-4.07-H2, RQ2-4.07-C1, RQ2-4.07-C2,
           RQ2-5.12-S-O6
@imports   none
@divergence TOTALITY IDIOM, disclosed (G2 observation O-2): this `def` is **total** — it does
not take `eq:phigammanilpotency` (clause `RQ2-4.07-H2`) as an argument, as mathlib's `Ring.inverse`
does not take `IsUnit`.  Outside the source's hypotheses the value is junk and is not claimed to
be the paper's object; H2 is carried by `sqrtOfScalarPlusNilpotent_sq`, `_unique`, `_inv` and
`sqrt_galois_equivariant`, each of which takes `hφ : φ = γ²·1 + n` and `hn : IsNilpotent n`.
Same idiom as `sqrt`, `linInv` and `stabilization`; module docstring, "Implementation notes".
-/
noncomputable def sqrtOfScalarPlusNilpotent (h2 : (2 : L) ≠ 0) (γ : Lˣ) (φ : Module.End L W) :
    Module.End L W :=
  (γ : L) • sqrt h2 ((((γ ^ 2)⁻¹ : Lˣ) : L) • φ)

/-- The defining equation of `def:squareroots`, `φ^{1/2} = γ · (γ^{-2} φ)^{1/2}`. -/
theorem sqrtOfScalarPlusNilpotent_def (h2 : (2 : L) ≠ 0) (γ : Lˣ) (φ : Module.End L W) :
    sqrtOfScalarPlusNilpotent h2 γ φ = (γ : L) • sqrt h2 ((((γ ^ 2)⁻¹ : Lˣ) : L) • φ) := rfl

/-- `def:squareroots` is a square root: `(φ^{1/2})² = φ` for `φ = γ²·1 + n` with `n` nilpotent.

@census none
-/
theorem sqrtOfScalarPlusNilpotent_sq (h2 : (2 : L) ≠ 0) (γ : Lˣ) (φ n : Module.End L W)
    (hn : IsNilpotent n) (hφ : φ = ((γ : L) ^ 2) • 1 + n) :
    (sqrtOfScalarPlusNilpotent h2 γ φ) ^ 2 = φ := by
  have hval : ((((γ ^ 2)⁻¹ : Lˣ)) : L) * ((γ : L) ^ 2) = 1 := by
    rw [Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_mul_cancel₀]
    exact Units.ne_zero _
  have hρ : ((((γ ^ 2)⁻¹ : Lˣ)) : L) • φ = 1 + ((((γ ^ 2)⁻¹ : Lˣ)) : L) • n := by
    rw [hφ, smul_add, smul_smul, hval, one_smul]
  obtain ⟨-, -, hsq⟩ := sqrt_spec h2 (((((γ ^ 2)⁻¹ : Lˣ)) : L) • φ)
    (((((γ ^ 2)⁻¹ : Lˣ)) : L) • n) (IsNilpotent.smul' hn _) hρ
  have hval' : ((γ : L) ^ 2) * ((((γ ^ 2)⁻¹ : Lˣ)) : L) = 1 := by
    rw [mul_comm]; exact hval
  rw [sqrtOfScalarPlusNilpotent, smul_pow, hsq, smul_smul, hval', one_smul]

/-! ### Clause (e), second sentence — naturality for the `def:squareroots` normalization -/

section NaturalGamma

variable {W₁ : Type v} {W₂ : Type w} [AddCommGroup W₁] [Module L W₁]
  [AddCommGroup W₂] [Module L W₂]

/-- **`prop:unipotentsquareroots` clause (e), second sentence**: the same naturality for the
normalization of `def:squareroots`, **both square roots taken with respect to the same `γ`**
(census clause `RQ2-4.05-C7`, discharged jointly with `sqrt_natural`).
@census none (helper; the `def:squareroots` half of clause `RQ2-4.05-C7`) -/
theorem sqrtOfScalarPlusNilpotent_natural (h2 : (2 : L) ≠ 0) (γ : Lˣ)
    {φ₁ : Module.End L W₁} {φ₂ : Module.End L W₂} {n₁ : Module.End L W₁} {n₂ : Module.End L W₂}
    (hn₁ : IsNilpotent n₁) (hφ₁ : φ₁ = ((γ : L) ^ 2) • 1 + n₁)
    (hn₂ : IsNilpotent n₂) (hφ₂ : φ₂ = ((γ : L) ^ 2) • 1 + n₂)
    (A : W₁ →ₗ[L] W₂) (hA : ∀ x, A (φ₁ x) = φ₂ (A x)) (x : W₁) :
    A (sqrtOfScalarPlusNilpotent h2 γ φ₁ x) = sqrtOfScalarPlusNilpotent h2 γ φ₂ (A x) := by
  have hval : ((((γ ^ 2)⁻¹ : Lˣ)) : L) * ((γ : L) ^ 2) = 1 := by
    rw [Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_mul_cancel₀]
    exact Units.ne_zero _
  set c : L := ((((γ ^ 2)⁻¹ : Lˣ)) : L) with hc
  have hu₁ : IsNilpotent ((c • φ₁) - 1) := by
    rw [hφ₁, smul_add, smul_smul, hval, one_smul, add_sub_cancel_left]
    exact IsNilpotent.smul' hn₁ _
  have hu₂ : IsNilpotent ((c • φ₂) - 1) := by
    rw [hφ₂, smul_add, smul_smul, hval, one_smul, add_sub_cancel_left]
    exact IsNilpotent.smul' hn₂ _
  have hA' : ∀ y, A ((c • φ₁) y) = (c • φ₂) (A y) := by
    intro y
    show A (c • φ₁ y) = c • φ₂ (A y)
    rw [map_smul, hA]
  show A (((γ : L) • sqrt h2 (c • φ₁)) x) = ((γ : L) • sqrt h2 (c • φ₂)) (A x)
  show A ((γ : L) • sqrt h2 (c • φ₁) x) = (γ : L) • sqrt h2 (c • φ₂) (A x)
  rw [map_smul, sqrt_natural h2 hu₁ hu₂ A hA' x]

end NaturalGamma

/-! ## The remark following `def:squareroots` (census `RQ2-4.09`) -/

/-- The two admissible choices of the scalar square root give negatives of each other: this is
half of "`φ^{1/2}` is uniquely determined by `eq:phigammanilpotency` up to the choice of sign"
(clause `RQ2-4.09-C1`).

@census    none (auxiliary; discharges clause `RQ2-4.09-C1` of `RQ2-4.09`)
@source    UNLABELED-sqrt-uniqueness-galois
@clauses   RQ2-4.09-C1
@imports   none
@divergence none
-/
theorem sqrtOfScalarPlusNilpotent_neg (h2 : (2 : L) ≠ 0) (γ : Lˣ) (φ : Module.End L W) :
    sqrtOfScalarPlusNilpotent h2 (-γ) φ = -sqrtOfScalarPlusNilpotent h2 γ φ := by
  rw [sqrtOfScalarPlusNilpotent, sqrtOfScalarPlusNilpotent, neg_sq, Units.val_neg, neg_smul]

/-- Once the scalar square root `γ` is fixed, the operator square root is unique: any `ψ` of the
shape `γ · 1 + m` with `m` nilpotent and `ψ² = φ` **is** `φ^{1/2}` with respect to `γ`.  This is
the other half of clause `RQ2-4.09-C1`.

@census    none (auxiliary; discharges clause `RQ2-4.09-C1` of `RQ2-4.09`)
@source    UNLABELED-sqrt-uniqueness-galois
@clauses   RQ2-4.09-C1
@imports   none
@divergence none
-/
theorem sqrtOfScalarPlusNilpotent_unique (h2 : (2 : L) ≠ 0) (γ : Lˣ) (φ ψ m : Module.End L W)
    (hm : IsNilpotent m) (hψ : ψ = (γ : L) • 1 + m) (hsq : ψ ^ 2 = φ) :
    ψ = sqrtOfScalarPlusNilpotent h2 γ φ := by
  have hγ : (γ : L) ≠ 0 := Units.ne_zero γ
  have hγ2 : (((γ ^ 2 : Lˣ)) : L) = (γ : L) * (γ : L) := by rw [sq, Units.val_mul]
  have hval : ((((γ ^ 2)⁻¹ : Lˣ)) : L) = ((γ : L)⁻¹) * ((γ : L)⁻¹) := by
    rw [Units.val_inv_eq_inv_val, hγ2, mul_inv]
  have hT : ((γ : L)⁻¹) • ψ = 1 + ((γ : L)⁻¹) • m := by
    rw [hψ, smul_add, smul_smul, inv_mul_cancel₀ hγ, one_smul]
  have hTsq : (((γ : L)⁻¹) • ψ) ^ 2 = ((((γ ^ 2)⁻¹ : Lˣ)) : L) • φ := by
    rw [smul_pow, hsq, hval, ← sq]
  have := sqrt_unique h2 (((((γ ^ 2)⁻¹ : Lˣ)) : L) • φ) (((γ : L)⁻¹) • ψ)
    (((γ : L)⁻¹) • m) (IsNilpotent.smul' hm _) hT hTsq
  rw [sqrtOfScalarPlusNilpotent, ← this, smul_smul, mul_inv_cancel₀ hγ, one_smul]

/-- **Remark** (`UNLABELED-sqrt-uniqueness-galois`, §4.2 of the source), Galois equivariance.

For `W = W_L = L ⊗_K W_K` with `L/K` quadratic (`hquad`) and `c` its non-trivial automorphism
(`hc`), and `φ = γ²·1 + n` with `n` nilpotent (clause `RQ2-4.09-H1`; the extra binder `hgal` is
disclosed in `@divergence`):
`(φ^c)^{1/2} = (φ^{1/2})^c` (`eq:squarerootgaloisequivariance`, clause `RQ2-4.09-C2`), **provided
the square root of `φ^c` is taken with respect to `cγ`** — which is what the `Units.map c γ`
argument on the left says.

@census    RQ2-4.09
@source    rmk:sqrtgaloisuniqueness
@clauses   RQ2-4.09-H1, RQ2-4.09-C2
@imports   none
@divergence EXTRA BINDER, disclosed (G2 finding C-2; not a weakening): `hgal : IsGalois K L`
is an argument here but is **not** part of clause `RQ2-4.09-H1`, which asks only for a QUADRATIC
`L/K` with non-trivial `c` (`hquad`, `hc`).  `IsGalois` follows from those plus §4.2's standing
`char ≠ 2` — degree 2 is normal, separable since `char ≠ 2` — so the covered class is exactly the
source's; it is a binder only because mathlib has no one-step lemma for it at the pin.
-/
theorem sqrt_galois_equivariant {K : Type u} [Field K] [Algebra K L]
    {WK : Type v} [AddCommGroup WK] [Module K WK]
    (h2 : (2 : L) ≠ 0) (hgal : IsGalois K L) (hquad : Module.finrank K L = 2)
    (c : Gal(L/K)) (hc : c ≠ 1) (γ : Lˣ) (φ n : Module.End L (L ⊗[K] WK))
    (hn : IsNilpotent n) (hφ : φ = ((γ : L) ^ 2) • 1 + n) :
    sqrtOfScalarPlusNilpotent h2 (Units.map (c : L →* L) γ)
        (semilinearConj c (galoisTwistEquiv c) (galoisTwistEquiv_smul c) φ)
      = semilinearConj c (galoisTwistEquiv c) (galoisTwistEquiv_smul c)
          (sqrtOfScalarPlusNilpotent h2 γ φ) := by
  have hγ : (γ : L) ≠ 0 := Units.ne_zero γ
  have hval : ((((γ ^ 2)⁻¹ : Lˣ)) : L) * ((γ : L) ^ 2) = 1 := by
    rw [Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_mul_cancel₀]
    exact Units.ne_zero _
  -- the unipotent base of the square root
  have hρ : ((((γ ^ 2)⁻¹ : Lˣ)) : L) • φ = 1 + ((((γ ^ 2)⁻¹ : Lˣ)) : L) • n := by
    rw [hφ, smul_add, smul_smul, hval, one_smul]
  -- the scalar proviso: the square root of `φ^c` is taken with respect to `c γ`
  have hscal : ((((Units.map (c : L →* L) γ) ^ 2)⁻¹ : Lˣ) : L)
      = c ((((γ ^ 2)⁻¹ : Lˣ)) : L) := by
    rw [← map_pow, ← map_inv, Units.coe_map]
    rfl
  have hnil : IsNilpotent (((((γ ^ 2)⁻¹ : Lˣ)) : L) • n) := by
    obtain ⟨N, hN⟩ := hn
    exact ⟨N, by rw [smul_pow, hN, smul_zero]⟩
  rw [sqrtOfScalarPlusNilpotent, sqrtOfScalarPlusNilpotent, hscal, semilinearConj_smul,
    ← semilinearConj_smul (σ := c) (ψ := galoisTwistEquiv c) (hψ := galoisTwistEquiv_smul c),
    sqrt_semilinearConj h2 c (galoisTwistEquiv c) (galoisTwistEquiv_smul c) _
      (((((γ ^ 2)⁻¹ : Lˣ)) : L) • n) hnil hρ]
  rfl

/-- `φ^{-1/2} := (φ^{1/2})^{-1}` is well defined (clause `RQ2-4.09-C3`): the inverse of the square
root with respect to `γ` is the square root of the inverse **with respect to `γ^{-1}`**.

@census    none (auxiliary; discharges clause `RQ2-4.09-C3` of `RQ2-4.09`)
@source    UNLABELED-sqrt-uniqueness-galois
@clauses   RQ2-4.09-C3
@imports   none
@divergence none
-/
theorem sqrtOfScalarPlusNilpotent_inv (h2 : (2 : L) ≠ 0) (γ : Lˣ) (φ n : Module.End L W)
    (hn : IsNilpotent n) (hφ : φ = ((γ : L) ^ 2) • 1 + n) :
    Ring.inverse (sqrtOfScalarPlusNilpotent h2 γ φ)
      = sqrtOfScalarPlusNilpotent h2 γ⁻¹ (Ring.inverse φ) := by
  have hγ : (γ : L) ≠ 0 := Units.ne_zero γ
  have hρne : ((((γ ^ 2)⁻¹ : Lˣ)) : L) ≠ 0 := Units.ne_zero _
  have hval : ((((γ ^ 2)⁻¹ : Lˣ)) : L) * ((γ : L) ^ 2) = 1 := by
    rw [Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_mul_cancel₀]
    exact Units.ne_zero _
  have hρ : ((((γ ^ 2)⁻¹ : Lˣ)) : L) • φ = 1 + ((((γ ^ 2)⁻¹ : Lˣ)) : L) • n := by
    rw [hφ, smul_add, smul_smul, hval, one_smul]
  obtain ⟨hSu, hSnil, hSsq⟩ := sqrt_spec h2 (((((γ ^ 2)⁻¹ : Lˣ)) : L) • φ)
    (((((γ ^ 2)⁻¹ : Lˣ)) : L) • n) (IsNilpotent.smul' hn _) hρ
  set S := sqrt h2 (((((γ ^ 2)⁻¹ : Lˣ)) : L) • φ) with hSdef
  have hφu : IsUnit φ := by
    rw [hφ]
    refine IsNilpotent.isUnit_add_left_of_commute hn (isUnit_smul_one ?_) ?_
    · exact pow_ne_zero 2 hγ
    · exact (Commute.one_right n).smul_right _
  -- the inverse of the square root is a square root of the inverse, with respect to `γ⁻¹`
  refine sqrtOfScalarPlusNilpotent_unique h2 γ⁻¹ (Ring.inverse φ)
    (Ring.inverse (sqrtOfScalarPlusNilpotent h2 γ φ))
    (((γ : L)⁻¹) • (Ring.inverse S - 1)) (IsNilpotent.smul' (isNilpotent_inverse_sub_one hSnil) _)
    ?_ ?_
  · rw [sqrtOfScalarPlusNilpotent, ← hSdef, inverse_smul hγ hSu, Units.val_inv_eq_inv_val,
      smul_sub]
    abel
  · rw [sqrtOfScalarPlusNilpotent, ← hSdef, inverse_smul hγ hSu, smul_pow, Ring.inverse_pow,
      hSsq, inverse_smul hρne hφu, smul_smul]
    rw [show ((γ : L)⁻¹ ^ 2) * (((((γ ^ 2)⁻¹ : Lˣ)) : L))⁻¹ = 1 by
      rw [Units.val_inv_eq_inv_val, inv_inv, Units.val_pow_eq_pow_val, ← mul_pow,
        inv_mul_cancel₀ hγ, one_pow], one_smul]

/-! ## The initial-value remark (census `RQ2-4.08`, OPTIONAL) -/

/-- **Remark** (`UNLABELED-sqrt-initial-value`, §4.2 of the source).

The starting value `φ_0 = 1_W` leads after one iteration to the same automorphism `φ_1` as the
starting value `φ_0 = φ` (clauses `RQ2-4.08-H1`, `RQ2-4.08-C1`): both are `½(1 + φ)`.

The census marks this row OPTIONAL; it is claimed here because the recursion it speaks about is
`sqrtSeq`, which this file defines anyway.

@census    RQ2-4.08
@source    rmk:sqrtinitialvalue
@clauses   RQ2-4.08-H1, RQ2-4.08-C1
@imports   none
@divergence none
-/
theorem sqrt_initialValue (h2 : (2 : L) ≠ 0) (φ n : Module.End L W) (hn : IsNilpotent n)
    (hφ : φ = 1 + n) :
    half h2 • ((1 : Module.End L W) + Ring.inverse (1 : Module.End L W) * φ)
      = sqrtSeq h2 φ 1 := by
  have hφ1 : IsNilpotent (φ - 1) := by rw [hφ]; simpa using hn
  have hu : IsUnit φ := isUnit_of_sub_one_isNilpotent hφ1
  rw [sqrtSeq_succ', sqrtSeq_zero, sqrtStep, Ring.inverse_mul_cancel φ hu, Ring.inverse_one,
    one_mul, add_comm]

/-! ## Witnesses (G5) -/

/-- A closed form in the simplest non-trivial case, `n² = 0`: `(1 + n)^{1/2} = 1 + ½ n`.
It is the witness that `sqrt` is not the identity operation.

@census none
-/
theorem sqrt_one_add_of_sq_eq_zero (h2 : (2 : L) ≠ 0) (n : Module.End L W) (hn : n ^ 2 = 0) :
    sqrt h2 (1 + n) = 1 + half h2 • n := by
  have hmn : IsNilpotent (half h2 • n) := IsNilpotent.smul' ⟨2, hn⟩ _
  have ha : (half h2 • n) * (half h2 • n) = 0 := by
    rw [smul_mul_smul_comm, ← sq n, hn, smul_zero]
  have hsq : (1 + half h2 • n) ^ 2 = 1 + n := by
    rw [sq, mul_add, add_mul, add_mul, one_mul, mul_one, ha, add_zero, one_mul, add_assoc,
      ← add_smul, half_add_half, one_smul]
  exact (sqrt_unique h2 (1 + n) (1 + half h2 • n) (half h2 • n) hmn rfl hsq).symm

section Witnesses

open Matrix

/-- **G5 witness (non-degeneracy).**  A concrete operator on `ℚ²` that is nilpotent of exponent
**exactly** `2`: the `1 + n` it generates is a unipotent automorphism which is *not* the identity,
so the hypotheses of `prop:unipotentsquareroots` (and, through `eq:nilpotency`, of
`prop:unipotentstabilization`) are not vacuous and are not satisfied only by `n = 0`.

@census none
-/
noncomputable def witnessNilpotent : Module.End ℚ (Fin 2 → ℚ) :=
  Matrix.toLinAlgEquiv' !![0, 1; 0, 0]

/-- The witness is nilpotent with `n² = 0`. -/
theorem witnessNilpotent_sq : witnessNilpotent ^ 2 = 0 := by
  rw [witnessNilpotent, ← map_pow]
  have h : (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℚ) ^ 2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h, map_zero]

/-- The witness is **not** zero: its nilpotency exponent is exactly `2`, i.e. `n^{2-1} ≠ 0`, the
`e = 2` case of clause `RQ2-4.01-H8`. -/
theorem witnessNilpotent_ne_zero : witnessNilpotent ≠ 0 := by
  intro h
  have h1 : witnessNilpotent ![0, 1] = 0 := by rw [h]; simp
  rw [witnessNilpotent] at h1
  have h2 := congrFun h1 0
  simp [Matrix.toLinAlgEquiv'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h2

/-- The witness is nilpotent, so `1 + witnessNilpotent` is a non-identity unipotent automorphism:
`prop:unipotentsquareroots` applies to it and its square root is not `1`. -/
theorem witnessNilpotent_isNilpotent : IsNilpotent witnessNilpotent :=
  ⟨2, witnessNilpotent_sq⟩

/-- **G5 witness (the characteristic hypothesis bites).**  Over a field of characteristic `2` the
conclusion of `prop:unipotentsquareroots` is **false**: the unipotent matrix `1 + n` with
`n = !![0,1;0,0]` over `ZMod 2` has *no* square root of the shape `1 + m` with `m` nilpotent
(a nilpotent `2 × 2` matrix satisfies `m² = 0`), because in characteristic `2`
`(1 + m)² = 1 + m²`.

So clauses `RQ2-4.05-H1`, `RQ2-4.06-H2` and the standing clause `RQ2-4.07-Hs1` are not decorative:
dropping `char ≠ 2` makes the proposition false, not merely unproved.

@census none
-/
theorem char_two_no_unipotent_sqrt :
    ¬ ∃ m : Matrix (Fin 2) (Fin 2) (ZMod 2),
      m ^ 2 = 0 ∧ (1 + m) ^ 2 = 1 + !![0, 1; 0, 0] := by
  decide

end Witnesses

end RationalQuivers.Unipotent
