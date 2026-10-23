import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Unipotent operators: the elementary toolbox

Support module for §4 of `latex/rational_quivers.tex` (stage **S6**).  It carries **no census
row**: everything here is a helper that the two content modules
(`RationalQuivers/Unipotent/Stabilization.lean`, `.../SquareRoots.lean`) need in order to *state*
the paper's propositions.

## Main definitions / results
* `RationalQuivers.Unipotent.half` — the scalar `½ ∈ L`, carried as a function of the standing
  characteristic hypothesis `(2 : L) ≠ 0` of §4, so that every declaration that mentions a
  half-sum mentions the hypothesis in its elaborated signature (`CONVENTIONS.md` §3).
* `RationalQuivers.Unipotent.linInv` — the junk-valued two-sided inverse of a linear map
  `M →ₗ[R] M₂`, the exact analogue of mathlib's `Ring.inverse` for maps between two different
  modules (`ledger/MATHLIB-DECISIONS.tsv` row `MD-S6-02`).
* `RationalQuivers.Unipotent.isUnit_of_sub_one_isNilpotent` — a unipotent operator `1 + n` is an
  automorphism; this is why the source may say "automorphism `φ = 1 + n`" and we may take
  `IsNilpotent (φ - 1)` alone as the hypothesis.

## Implementation notes

**Why `half` takes the hypothesis as an argument.**  §4 runs under the standing assumption
`char ≠ 2` (census clauses `RQ2-4.01-H2`, `RQ2-4.05-H1`, `RQ2-4.06-H2`, `RQ2-4.07-Hs1`).  Lean silently
drops unused instance binders (`CONVENTIONS.md` §3, r6 delta), so a `[NeZero (2 : L)]` binder would
*not* reliably appear in the signature of a statement about the square root.  Making the halving
scalar a function of the proof `(2 : L) ≠ 0` puts the hypothesis into the *term*, hence into the
elaborated type of every declaration that mentions `sqrt` or `stabilizationSeq`; the entailment is
checkable with `#check` on the elaborated constant, as `CONVENTIONS.md` §3 requires.

**Why `linInv`.**  The paper's iterations invert maps `W₊ → W₋^τ` between two *different*
subspaces of `W_L`, and the invertibility of the `k`-th iterate is a *theorem*
(clause `RQ2-4.02-C5`), not something available when the sequence is defined.  mathlib has
`Ring.inverse` (endomorphisms) and `ContinuousLinearMap.inverse`, but nothing junk-valued for
`M →ₗ[R] M₂`; `linInv` is that, and it is the only reason the paper's recursion can be written
down *literally* rather than in an inverse-free rearrangement.
-/

universe u v w

namespace RationalQuivers.Unipotent

section Half

variable {K L : Type u} [Field K] [Field L]

/-- The scalar `½ ∈ L`, as a function of §4's standing hypothesis `char L ≠ 2` (in the form
`(2 : L) ≠ 0`).

The hypothesis is a genuine argument, not decoration: `half h2 = (2 : L)⁻¹` by `rfl`, but the
proof term occurs in the definition, so every declaration mentioning `half` carries `(2 : L) ≠ 0`
in its elaborated signature.  See the module docstring.

@census none
-/
noncomputable def half (h2 : (2 : L) ≠ 0) : L := ((Units.mk0 (2 : L) h2)⁻¹ : L)

@[simp] theorem half_eq (h2 : (2 : L) ≠ 0) : half h2 = (2 : L)⁻¹ := rfl

theorem two_mul_half (h2 : (2 : L) ≠ 0) : (2 : L) * half h2 = 1 := by
  rw [half_eq]; exact mul_inv_cancel₀ h2

theorem half_add_half (h2 : (2 : L) ≠ 0) : half h2 + half h2 = 1 := by
  have : (2 : L) * half h2 = 1 := two_mul_half h2
  rw [two_mul] at this
  simpa [add_mul] using this

/-- `char K ≠ 2` transfers to any field extension `L/K`: clause `RQ2-4.01-H2` is stated for `K`,
while the halving scalar of `eq:unipotentstabilizationiteration` is applied to `L`-linear maps. -/
theorem two_ne_zero_of_base [Algebra K L] (h2 : (2 : K) ≠ 0) : (2 : L) ≠ 0 := by
  intro h
  apply h2
  have hmap : algebraMap K L 2 = 0 := by rw [map_ofNat, h]
  exact (map_eq_zero_iff _ (algebraMap K L).injective).mp hmap

end Half

section Inverse

variable {A : Type v} [MonoidWithZero A]

/-- Helper: the inverse of a unit commutes with everything the unit commutes with. -/
theorem Commute.inverse_left {a b : A} (ha : IsUnit a) (h : Commute a b) :
    Commute (Ring.inverse a) b := by
  have h1 : a * Ring.inverse a = 1 := Ring.mul_inverse_cancel a ha
  have h2 : Ring.inverse a * a = 1 := Ring.inverse_mul_cancel a ha
  show Ring.inverse a * b = b * Ring.inverse a
  calc Ring.inverse a * b = Ring.inverse a * b * (a * Ring.inverse a) := by rw [h1, mul_one]
    _ = Ring.inverse a * (b * a) * Ring.inverse a := by simp [mul_assoc]
    _ = Ring.inverse a * (a * b) * Ring.inverse a := by rw [h.eq]
    _ = (Ring.inverse a * a) * b * Ring.inverse a := by simp [mul_assoc]
    _ = b * Ring.inverse a := by rw [h2, one_mul]

end Inverse

section Unipotent

variable {A : Type v} [Ring A]

/-- A **unipotent** operator is an automorphism: if `u - 1` is nilpotent then `u` is a unit.

This is why the source's hypothesis "`φ` is an automorphism with `φ = 1 + n`, `n` nilpotent"
(clauses `RQ2-4.05-H3`, `RQ2-4.06-H1`) may be carried in Lean as `IsNilpotent (φ - 1)` alone: the
automorphism half is *derivable*, not dropped.  mathlib: `IsNilpotent.isUnit_one_add`.

@census none
-/
theorem isUnit_of_sub_one_isNilpotent {u : A} (h : IsNilpotent (u - 1)) : IsUnit u := by
  have := h.isUnit_one_add
  simpa using this

/-- The inverse of a unipotent operator is unipotent. -/
theorem isNilpotent_inverse_sub_one {u : A} (h : IsNilpotent (u - 1)) :
    IsNilpotent (Ring.inverse u - 1) := by
  have hu : IsUnit u := isUnit_of_sub_one_isNilpotent h
  have hb : Ring.inverse u * u = 1 := Ring.inverse_mul_cancel u hu
  have hb' : u * Ring.inverse u = 1 := Ring.mul_inverse_cancel u hu
  have hcu : Commute (Ring.inverse u) u := by
    show Ring.inverse u * u = u * Ring.inverse u
    rw [hb, hb']
  have hcom : Commute (Ring.inverse u) (1 - u) := (Commute.one_right _).sub_right hcu
  have hnil : IsNilpotent (1 - u) := by
    rw [← neg_sub]
    exact h.neg
  have hEq : Ring.inverse u - 1 = Ring.inverse u * (1 - u) := by
    rw [mul_sub, mul_one, hb]
  rw [hEq]
  exact hcom.isNilpotent_mul_left hnil

end Unipotent

section Step

variable {L : Type u} [Field L] {A : Type v} [Ring A] [Algebra L A]

/-- The **averaging (Newton) step** `ψ ↦ ½(ψ + ψ^{-1} φ)` in an `L`-algebra.

Both iterations of §4 are instances of it: `prop:unipotentsquareroots` iterates
`sqrtStep h2 φ ·` towards a square root of `φ`, and `prop:unipotentstabilization` is the case
`φ = 1`, where the step reads `ψ ↦ ½(ψ + ψ^{-1})`.

@census none
-/
noncomputable def sqrtStep (h2 : (2 : L) ≠ 0) (φ ψ : A) : A :=
  half h2 • (ψ + Ring.inverse ψ * φ)

/-- Four copies of `¼` make `1`. -/
theorem half_mul_half_four (h2 : (2 : L) ≠ 0) :
    half h2 * half h2 + half h2 * half h2 + half h2 * half h2 + half h2 * half h2 = 1 := by
  rw [half_eq]
  field_simp
  ring

/-- **The key identity.**  For a unit `ψ` commuting with `φ`,
`(½(ψ + ψ^{-1}φ))² - φ = ¼ (ψ - ψ^{-1}φ)²`.

Everything in §4 that says "the error term gets squared, hence its nilpotency exponent halves"
is this line: `ψ - ψ^{-1}φ = ψ^{-1}(ψ² - φ)`, so the new error is `¼ ψ^{-2}` times the **square**
of the old one. -/
theorem sqrtStep_sq_sub (h2 : (2 : L) ≠ 0) {φ ψ : A} (hψ : IsUnit ψ) (hcom : Commute ψ φ) :
    (sqrtStep h2 φ ψ) ^ 2 - φ = (half h2 * half h2) • (ψ - Ring.inverse ψ * φ) ^ 2 := by
  have hb : ψ * Ring.inverse ψ = 1 := Ring.mul_inverse_cancel ψ hψ
  have hb' : Ring.inverse ψ * ψ = 1 := Ring.inverse_mul_cancel ψ hψ
  have hbc : Commute (Ring.inverse ψ) φ := Commute.inverse_left hψ hcom
  set b := Ring.inverse ψ
  have e1 : ψ * (b * φ) = φ := by rw [← mul_assoc, hb, one_mul]
  have e2 : b * φ * ψ = φ := by rw [mul_assoc, ← hcom.eq, ← mul_assoc, hb', one_mul]
  have e3 : b * φ * (b * φ) = b * b * (φ * φ) := by
    calc b * φ * (b * φ) = b * (φ * b) * φ := by simp [mul_assoc]
      _ = b * (b * φ) * φ := by rw [hbc.eq]
      _ = b * b * (φ * φ) := by simp [mul_assoc]
  have key : (ψ + b * φ) ^ 2 = (ψ - b * φ) ^ 2 + (φ + φ + φ + φ) := by
    simp only [sq, add_mul, mul_add, sub_mul, mul_sub, e1, e2, e3]
    abel
  have hsmul : (half h2 * half h2) • (φ + φ + φ + φ) = φ := by
    simp only [smul_add, ← add_smul, half_mul_half_four h2, one_smul]
  calc (sqrtStep h2 φ ψ) ^ 2 - φ
      = (half h2 * half h2) • (ψ + b * φ) ^ 2 - φ := by
        rw [sqrtStep, smul_pow, sq (half h2)]
    _ = (half h2 * half h2) • ((ψ - b * φ) ^ 2 + (φ + φ + φ + φ)) - φ := by rw [key]
    _ = (half h2 * half h2) • (ψ - b * φ) ^ 2 := by rw [smul_add, hsmul]; abel

/-- The error term factors: `ψ - ψ^{-1}φ = ψ^{-1}(ψ² - φ)`. -/
theorem sub_inverse_mul (φ ψ : A) (hψ : IsUnit ψ) :
    ψ - Ring.inverse ψ * φ = Ring.inverse ψ * (ψ ^ 2 - φ) := by
  have hb' : Ring.inverse ψ * ψ = 1 := Ring.inverse_mul_cancel ψ hψ
  rw [mul_sub, sq, ← mul_assoc, hb', one_mul]

/-- **The halving.**  If the error `ψ² - φ` kills the `m`-th power, the new error kills the
`⌈m/2⌉`-th. -/
theorem sqrtStep_error_pow (h2 : (2 : L) ≠ 0) {φ ψ : A} (hψ : IsUnit ψ) (hcom : Commute ψ φ)
    {m : ℕ} (hm : (ψ ^ 2 - φ) ^ m = 0) :
    ((sqrtStep h2 φ ψ) ^ 2 - φ) ^ (m ⌈/⌉ 2) = 0 := by
  have hbc : Commute (Ring.inverse ψ) φ := Commute.inverse_left hψ hcom
  have hbs : Commute (Ring.inverse ψ) (ψ ^ 2 - φ) := by
    refine Commute.sub_right ?_ hbc
    exact (Commute.inverse_left hψ (Commute.refl ψ)).pow_right 2
  have h2m : m ≤ 2 * (m ⌈/⌉ 2) := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    omega
  have hzero : (ψ ^ 2 - φ) ^ (2 * (m ⌈/⌉ 2)) = 0 := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le h2m
    rw [hj, pow_add, hm, zero_mul]
  rw [sqrtStep_sq_sub h2 hψ hcom, sub_inverse_mul φ ψ hψ, smul_pow, ← pow_mul, hbs.mul_pow,
    hzero, mul_zero, smul_zero]

/-- A square root is a fixed point of its own iteration. -/
theorem sqrtStep_of_sq_eq (h2 : (2 : L) ≠ 0) {φ ψ : A} (hψ : IsUnit ψ) (hsq : ψ ^ 2 = φ) :
    sqrtStep h2 φ ψ = ψ := by
  have hb' : Ring.inverse ψ * ψ = 1 := Ring.inverse_mul_cancel ψ hψ
  have : Ring.inverse ψ * φ = ψ := by rw [← hsq, sq, ← mul_assoc, hb', one_mul]
  rw [sqrtStep, this, ← two_smul L ψ, smul_smul, half_eq, inv_mul_cancel₀ h2, one_smul]

/-- The step preserves commuting with `φ`. -/
theorem sqrtStep_commute (h2 : (2 : L) ≠ 0) {φ ψ : A} (hψ : IsUnit ψ) (hcom : Commute ψ φ) :
    Commute (sqrtStep h2 φ ψ) φ := by
  refine Commute.smul_left ?_ _
  exact hcom.add_left ((Commute.inverse_left hψ hcom).mul_left (Commute.refl φ))

/-- `c • 1` is a unit for every non-zero scalar. -/
theorem isUnit_smul_one {c : L} (hc : c ≠ 0) : IsUnit ((c • 1 : A)) := by
  refine ⟨⟨c • 1, c⁻¹ • 1, ?_, ?_⟩, rfl⟩
  · rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hc, one_smul]
  · rw [smul_mul_smul_comm, mul_one, inv_mul_cancel₀ hc, one_smul]

/-- `1 + 1 = 2 • 1` in an `L`-algebra. -/
theorem one_add_one_eq_two_smul : (1 + 1 : A) = (2 : L) • (1 : A) := by
  rw [show (2 : L) = 1 + 1 by norm_num, add_smul, one_smul]

/-- A unipotent element in the strong sense used by the uniqueness argument: if `x` is nilpotent
and `x * (1 + 1 + x) = 0` in characteristic `≠ 2`, then `x = 0`.

This replaces the source's iteration `ñ = (-1/2)^k ñ^{2^k}`: `1 + 1 + x` is a unit (a unit plus a
commuting nilpotent), so the equation forces `x = 0` outright. -/
theorem eq_zero_of_mul_two_add (h2 : (2 : L) ≠ 0) {x : A} (hx : IsNilpotent x)
    (h : x * (1 + 1 + x) = 0) : x = 0 := by
  have hu : IsUnit ((1 : A) + 1 + x) := by
    rw [one_add_one_eq_two_smul (L := L)]
    refine IsNilpotent.isUnit_add_left_of_commute hx (isUnit_smul_one h2) ?_
    exact (Commute.one_right x).smul_right (2 : L) |>.symm.symm
  obtain ⟨u, hu'⟩ := hu
  have : x * (↑u * ↑u⁻¹) = 0 := by rw [← mul_assoc, hu', h, zero_mul]
  simpa using this

/-- The inverse of a scalar multiple. -/
theorem inverse_smul {c : L} (hc : c ≠ 0) {x : A} (hx : IsUnit x) :
    Ring.inverse (c • x) = c⁻¹ • Ring.inverse x := by
  have h1 : x * Ring.inverse x = 1 := Ring.mul_inverse_cancel x hx
  have h2 : Ring.inverse x * x = 1 := Ring.inverse_mul_cancel x hx
  have hu : IsUnit (c • x) := by
    refine ⟨⟨c • x, c⁻¹ • Ring.inverse x, ?_, ?_⟩, rfl⟩
    · rw [smul_mul_smul_comm, h1, mul_inv_cancel₀ hc, one_smul]
    · rw [smul_mul_smul_comm, h2, inv_mul_cancel₀ hc, one_smul]
  obtain ⟨u, hu'⟩ := hu
  have hinv : (c • x) * (c⁻¹ • Ring.inverse x) = 1 := by
    rw [smul_mul_smul_comm, h1, mul_inv_cancel₀ hc, one_smul]
  have hinv' : (c⁻¹ • Ring.inverse x) * (c • x) = 1 := by
    rw [smul_mul_smul_comm, h2, inv_mul_cancel₀ hc, one_smul]
  calc Ring.inverse (c • x)
      = Ring.inverse (c • x) * ((c • x) * (c⁻¹ • Ring.inverse x)) := by rw [hinv, mul_one]
    _ = (Ring.inverse (c • x) * (c • x)) * (c⁻¹ • Ring.inverse x) := by rw [mul_assoc]
    _ = c⁻¹ • Ring.inverse x := by
        rw [Ring.inverse_mul_cancel _ ⟨⟨c • x, c⁻¹ • Ring.inverse x, hinv, hinv'⟩, rfl⟩, one_mul]

/-- A scalar multiple of a nilpotent element is nilpotent. -/
theorem IsNilpotent.smul' {x : A} (h : IsNilpotent x) (c : L) : IsNilpotent (c • x) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [smul_pow, hn, smul_zero]⟩

/-- `½ · 2 = 1` inside the algebra. -/
theorem half_smul_two (h2 : (2 : L) ≠ 0) : half h2 • (1 + 1 : A) = 1 := by
  rw [smul_add, ← add_smul, half_add_half, one_smul]

/-- The step, written as a deviation from the identity. -/
theorem sqrtStep_sub_one (h2 : (2 : L) ≠ 0) (φ ψ : A) :
    sqrtStep h2 φ ψ - 1 = half h2 • ((ψ - 1) + (Ring.inverse ψ * φ - 1)) := by
  have h1 : half h2 • (1 + 1 : A) = 1 := half_smul_two h2
  calc sqrtStep h2 φ ψ - 1
      = half h2 • (ψ + Ring.inverse ψ * φ) - half h2 • (1 + 1 : A) := by rw [h1, sqrtStep]
    _ = half h2 • ((ψ + Ring.inverse ψ * φ) - (1 + 1 : A)) := by rw [smul_sub]
    _ = half h2 • ((ψ - 1) + (Ring.inverse ψ * φ - 1)) := by congr 1; abel

/-- The step preserves unipotence: if `ψ` and `φ` are `1 + nilpotent` and commute, so is the
step.  This is `eq:unipotentnilpotency1` at the level of the ring. -/
theorem sqrtStep_isNilpotent_sub_one (h2 : (2 : L) ≠ 0) {φ ψ : A}
    (hψ : IsNilpotent (ψ - 1)) (hφ : IsNilpotent (φ - 1)) (hcom : Commute ψ φ) :
    IsNilpotent (sqrtStep h2 φ ψ - 1) := by
  have hψu : IsUnit ψ := isUnit_of_sub_one_isNilpotent hψ
  have hbnil : IsNilpotent (Ring.inverse ψ - 1) := isNilpotent_inverse_sub_one hψ
  have hbc : Commute (Ring.inverse ψ) φ := Commute.inverse_left hψu hcom
  have hbc1 : Commute (Ring.inverse ψ - 1) φ := hbc.sub_left (Commute.one_left φ)
  have hbψ : Commute ψ (Ring.inverse ψ) := (Commute.inverse_left hψu (Commute.refl ψ)).symm
  have hprod : IsNilpotent (Ring.inverse ψ * φ - 1) := by
    have hEq : Ring.inverse ψ * φ - 1 = (Ring.inverse ψ - 1) * φ + (φ - 1) := by
      rw [sub_mul, one_mul]; abel
    rw [hEq]
    refine Commute.isNilpotent_add ?_ (hbc1.isNilpotent_mul_right hbnil) hφ
    exact Commute.mul_left (hbc1.sub_right (Commute.one_right _))
      ((Commute.refl φ).sub_right (Commute.one_right φ))
  rw [sqrtStep_sub_one]
  refine IsNilpotent.smul' ?_ _
  refine Commute.isNilpotent_add ?_ hψ hprod
  refine Commute.sub_right ?_ (Commute.one_right _)
  exact Commute.mul_right (hbψ.sub_left (Commute.one_left _)) (hcom.sub_left (Commute.one_left φ))

section Neumann

variable {L : Type u} [Field L] {P : Type v} [AddCommMonoid P] [Module L P]

/-- The Neumann series `∑_{i<N} (-1)^i n^i` for an endomorphism, with the signs carried by the
**scalars** rather than by a negation on the endomorphism ring.

This is not a stylistic choice: for a submodule `W ≤ L ⊗_K W_K` the ring `Module.End L ↥W` has no
`Ring` (indeed no `Neg`) instance at the pinned mathlib revision — `Submodule.addCommMonoid` and
`AddCommGroup.toAddCommMonoid Submodule.addCommGroup` are distinct instance terms, so
`Module.End.instRing` does not apply — while the `L`-action, and hence `(-1 : L) • ·`, is always
available.  §4.1 lives in exactly that situation
(`ledger/MATHLIB-DECISIONS.tsv` `MD-S6-06`).

@census none
-/
noncomputable def neumann (n : Module.End L P) (N : ℕ) : Module.End L P :=
  ∑ i ∈ Finset.range N, ((-1 : L) ^ i) • n ^ i

/-- The telescoping identity: `(1 + n) · ∑_{i<N} (-1)^i n^i + (-1)^N n^N = 1`. -/
theorem one_add_mul_neumann (n : Module.End L P) (N : ℕ) :
    (1 + n) * neumann n N + ((-1 : L) ^ N) • n ^ N = 1 := by
  induction N with
  | zero => simp [neumann]
  | succ N ih =>
      rw [neumann, Finset.sum_range_succ, ← neumann, mul_add, mul_smul_comm,
        show (1 + n) * n ^ N = n ^ N + n ^ (N + 1) by rw [add_mul, one_mul, ← pow_succ'],
        smul_add, pow_succ (-1 : L) N]
      have hz : ((-1 : L) ^ N) • n ^ (N + 1) + ((-1 : L) ^ N * (-1 : L)) • n ^ (N + 1) = 0 := by
        rw [← add_smul]
        simp
      calc (1 + n) * neumann n N + (((-1 : L) ^ N) • n ^ N + ((-1 : L) ^ N) • n ^ (N + 1))
            + ((-1 : L) ^ N * (-1 : L)) • n ^ (N + 1)
          = ((1 + n) * neumann n N + ((-1 : L) ^ N) • n ^ N)
            + (((-1 : L) ^ N) • n ^ (N + 1) + ((-1 : L) ^ N * (-1 : L)) • n ^ (N + 1)) := by abel
        _ = 1 := by rw [ih, hz, add_zero]

/-- The same on the other side. -/
theorem neumann_mul_one_add (n : Module.End L P) (N : ℕ) :
    neumann n N * (1 + n) + ((-1 : L) ^ N) • n ^ N = 1 := by
  have hcomm : neumann n N * (1 + n) = (1 + n) * neumann n N := by
    rw [neumann, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    exact ((Commute.one_left (n ^ i)).add_left ((Commute.refl n).pow_right i)).eq.symm
  rw [hcomm, one_add_mul_neumann]

/-- A scalar multiple of a nilpotent endomorphism is nilpotent. -/
theorem IsNilpotent.smul'' {x : Module.End L P} (h : IsNilpotent x) (c : L) :
    IsNilpotent (c • x) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [smul_pow, hn, smul_zero]⟩

/-- `½ · 2 = 1` in `Module.End L P`. -/
theorem half_smul_two_end (h2 : (2 : L) ≠ 0) : half h2 • (1 + 1 : Module.End L P) = 1 := by
  rw [smul_add, ← add_smul, half_add_half, one_smul]

/-- `c • 1` is a unit in `Module.End L P` for every non-zero scalar. -/
theorem isUnit_smul_one_end {c : L} (hc : c ≠ 0) : IsUnit ((c • 1 : Module.End L P)) := by
  refine ⟨⟨c • 1, c⁻¹ • 1, ?_, ?_⟩, rfl⟩
  · rw [smul_mul_smul_comm, mul_one, mul_inv_cancel₀ hc, one_smul]
  · rw [smul_mul_smul_comm, mul_one, inv_mul_cancel₀ hc, one_smul]

/-- `1 + 1 = 2 • 1` in `Module.End L P`. -/
theorem one_add_one_eq_two_smul_end : (1 + 1 : Module.End L P) = (2 : L) • 1 := by
  rw [show (2 : L) = 1 + 1 by norm_num, add_smul, one_smul]

/-- **`1 + nilpotent` is invertible**, in an endomorphism algebra with no subtraction.
This is `IsNilpotent.isUnit_one_add` for the situation of §4.1. -/
theorem isUnit_one_add_of_isNilpotent {n : Module.End L P} (hn : IsNilpotent n) :
    IsUnit (1 + n) := by
  obtain ⟨N, hN⟩ := hn
  refine ⟨⟨1 + n, neumann n N, ?_, ?_⟩, rfl⟩
  · have := one_add_mul_neumann n N
    rwa [hN, smul_zero, add_zero] at this
  · have := neumann_mul_one_add n N
    rwa [hN, smul_zero, add_zero] at this

/-- A finite sum of pairwise-commuting nilpotents is nilpotent. -/
theorem isNilpotent_sum_of_commute {ι : Type*} {s : Finset ι} {f : ι → Module.End L P}
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, Commute (f i) (f j))
    (hnil : ∀ i ∈ s, IsNilpotent (f i)) : IsNilpotent (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsNilpotent.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine Commute.isNilpotent_add ?_ (hnil a (Finset.mem_insert_self a s)) ?_
      · refine Commute.sum_right _ _ _ ?_
        intro j hj
        exact hcomm a (Finset.mem_insert_self a s) j (Finset.mem_insert_of_mem hj)
      · exact ih (fun i hi j hj => hcomm i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj)) (fun i hi => hnil i (Finset.mem_insert_of_mem hi))

/-- The inverse of a unipotent is unipotent, with the tail commuting with everything the original
nilpotent commutes with (it is a polynomial in it).

@census none
-/
theorem exists_inverse_one_add {n : Module.End L P} (hn : IsNilpotent n) :
    ∃ n' : Module.End L P, IsNilpotent n' ∧ Ring.inverse (1 + n) = 1 + n'
      ∧ ∀ x : Module.End L P, Commute n x → Commute n' x := by
  obtain ⟨N, hN⟩ := hn
  have hNs : n ^ (N + 1) = 0 := by rw [pow_succ, hN, zero_mul]
  have hunit : IsUnit (1 + n) := isUnit_one_add_of_isNilpotent ⟨N, hN⟩
  have hinv : Ring.inverse (1 + n) = neumann n (N + 1) := by
    have h1 : (1 + n) * neumann n (N + 1) = 1 := by
      have := one_add_mul_neumann n (N + 1)
      rwa [hNs, smul_zero, add_zero] at this
    have h2 : neumann n (N + 1) * (1 + n) = 1 := by
      have := neumann_mul_one_add n (N + 1)
      rwa [hNs, smul_zero, add_zero] at this
    have : Ring.inverse (1 + n) = Ring.inverse (1 + n) * ((1 + n) * neumann n (N + 1)) := by
      rw [h1, mul_one]
    rw [this, ← mul_assoc, Ring.inverse_mul_cancel _ hunit, one_mul]
  refine ⟨∑ i ∈ Finset.range N, ((-1 : L) ^ (i + 1)) • n ^ (i + 1), ?_, ?_, ?_⟩
  · refine isNilpotent_sum_of_commute ?_ ?_
    · intro i _ j _
      exact ((Commute.refl n).pow_pow (i + 1) (j + 1)).smul_left _ |>.smul_right _
    · intro i _
      have hz : (n ^ (i + 1)) ^ N = 0 := by
        rw [← pow_mul, show (i + 1) * N = N * i + N by ring, pow_add, hN, mul_zero]
      exact ⟨N, by rw [smul_pow, hz, smul_zero]⟩
  · rw [hinv, neumann, Finset.sum_range_succ']
    simp only [pow_zero, one_smul]
    exact add_comm _ _
  · intro x hx
    refine Commute.sum_left _ _ _ ?_
    intro i _
    exact ((hx.pow_left (i + 1)).smul_left _)

/-- A unit plus a commuting nilpotent is a unit — the `Semiring` version of
`IsNilpotent.isUnit_add_left_of_commute`, for endomorphism algebras with no subtraction. -/
theorem isUnit_add_of_isNilpotent {v n : Module.End L P} (hv : IsUnit v) (hn : IsNilpotent n)
    (hcom : Commute v n) : IsUnit (v + n) := by
  have hb : v * Ring.inverse v = 1 := Ring.mul_inverse_cancel v hv
  have hcb : Commute (Ring.inverse v) n := Commute.inverse_left hv hcom
  have hEq : v + n = v * (1 + Ring.inverse v * n) := by
    rw [mul_add, mul_one, ← mul_assoc, hb, one_mul]
  rw [hEq]
  exact hv.mul (isUnit_one_add_of_isNilpotent (hcb.isNilpotent_mul_left hn))

/-- **The addendum computation, commutation half** (`eq:unipotentcommutators1`): if `u` and `v`
commute, so do `½(u + v^{-1})` and `½(v + u^{-1})`. -/
theorem commute_avg (h2 : (2 : L) ≠ 0) {u v : Module.End L P} (hu : IsUnit u) (hv : IsUnit v)
    (h : Commute u v) :
    Commute (half h2 • (u + Ring.inverse v)) (half h2 • (v + Ring.inverse u)) := by
  have h1 : Commute u v := h
  have h2' : Commute u (Ring.inverse u) := (Commute.inverse_left hu (Commute.refl u)).symm
  have h3 : Commute (Ring.inverse v) v := Commute.inverse_left hv (Commute.refl v)
  have h4 : Commute (Ring.inverse v) (Ring.inverse u) :=
    (Commute.inverse_left hu (Commute.inverse_left hv h.symm).symm).symm
  exact (((h1.add_right h2').add_left (h3.add_right h4)).smul_left _).smul_right _

/-- **The addendum computation, unipotence half** (`eq:unipotentnilpotency1`): if `u = 1 + m_u`
and `v = 1 + m_v` with `m_u`, `m_v` commuting nilpotents, then `½(u + v^{-1}) = 1 + nilpotent`. -/
theorem avg_one_add (h2 : (2 : L) ≠ 0) {u v mu mv : Module.End L P} (hu : u = 1 + mu)
    (hv : v = 1 + mv) (hmu : IsNilpotent mu) (hmv : IsNilpotent mv) (hcom : Commute mu mv) :
    ∃ m : Module.End L P, IsNilpotent m ∧ half h2 • (u + Ring.inverse v) = 1 + m := by
  obtain ⟨mv', hmv', hinv, hcomm'⟩ := exists_inverse_one_add hmv
  refine ⟨half h2 • (mu + mv'), ?_, ?_⟩
  · refine IsNilpotent.smul'' ?_ _
    exact Commute.isNilpotent_add ((hcomm' mu hcom.symm).symm) hmu hmv'
  · rw [hu, hv, hinv]
    calc half h2 • (1 + mu + (1 + mv'))
        = half h2 • ((1 + 1) + (mu + mv')) := by congr 1; abel
      _ = half h2 • (1 + 1 : Module.End L P) + half h2 • (mu + mv') := by rw [smul_add]
      _ = 1 + half h2 • (mu + mv') := by rw [half_smul_two_end h2]

end Neumann

section SemiringStep

variable {L : Type u} [Field L] {A : Type v} [Semiring A] [Algebra L A]

/-- Four copies scaled by `¼` give the element back. -/
theorem quarter_smul_four (h2 : (2 : L) ≠ 0) (x : A) :
    (half h2 * half h2) • (x + x + x + x) = x := by
  simp only [smul_add, ← add_smul, half_mul_half_four h2, one_smul]

/-- **The §4.1 identity, subtraction-free.**  For a unipotent unit `u = 1 + n`,
`¼(u + 1 + 1 + u^{-1}) = 1 + ¼ u^{-1} n²`.

This is the computation of `prop:unipotentstabilization`: the composite of the two stabilized
maps deviates from the identity by the **square** of the old deviation, up to a unit.

It is stated in a `Semiring` (not a `Ring`) on purpose: the endomorphism algebra
`Module.End L ↥W` of a *submodule* of `L ⊗[K] W_K` has no `Ring` instance at the pinned mathlib
revision (`Submodule.addCommMonoid` and `AddCommGroup.toAddCommMonoid Submodule.addCommGroup` are
different instance terms), so §4.1 is carried out entirely without subtraction — which is also the
source's own spelling, `φ = 1 + n`. -/
theorem quarter_avg_of_one_add (h2 : (2 : L) ≠ 0) {u n : A} (hu : IsUnit u) (hun : u = 1 + n) :
    (half h2 * half h2) • (u + 1 + 1 + Ring.inverse u)
      = 1 + (half h2 * half h2) • (Ring.inverse u * (n * n)) := by
  have hb : u * Ring.inverse u = 1 := Ring.mul_inverse_cancel u hu
  refine hu.mul_left_cancel ?_
  have e1 : u * ((half h2 * half h2) • (u + 1 + 1 + Ring.inverse u))
      = (half h2 * half h2) • (u * u + u + u + 1) := by
    rw [mul_smul_comm, mul_add, mul_add, mul_add, mul_one, hb]
  have e2 : u * (1 + (half h2 * half h2) • (Ring.inverse u * (n * n)))
      = u + (half h2 * half h2) • (n * n) := by
    rw [mul_add, mul_one, mul_smul_comm, ← mul_assoc, hb, one_mul]
  rw [e1, e2, hun]
  have expand : (1 + n) * (1 + n) + (1 + n) + (1 + n) + 1
      = ((1 : A) + 1 + 1 + 1) + (n + n + n + n) + n * n := by
    rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul]
    abel
  rw [expand, smul_add, smul_add, quarter_smul_four h2 (1 : A), quarter_smul_four h2 n]

/-- The halving of the nilpotency exponent, subtraction-free: if `n^m = 0` then the new error
`¼ u^{-1} n²` kills the `⌈m/2⌉`-th power. -/
theorem quarter_error_pow (h2 : (2 : L) ≠ 0) {u n : A} (hu : IsUnit u) (hcom : Commute u n)
    {m : ℕ} (hm : n ^ m = 0) :
    ((half h2 * half h2) • (Ring.inverse u * (n * n))) ^ (m ⌈/⌉ 2) = 0 := by
  have hcb : Commute (Ring.inverse u) n := Commute.inverse_left hu hcom
  have h2m : m ≤ 2 * (m ⌈/⌉ 2) := by
    rw [Nat.ceilDiv_eq_add_pred_div]; omega
  have hzero : n ^ (2 * (m ⌈/⌉ 2)) = 0 := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le h2m
    rw [hj, pow_add, hm, zero_mul]
  have hnn : n * n = n ^ 2 := (sq n).symm
  rw [hnn, smul_pow, (hcb.pow_right 2).mul_pow, ← pow_mul, mul_comm 2 (m ⌈/⌉ 2),
    ← mul_comm 2 (m ⌈/⌉ 2), hzero, mul_zero, smul_zero]

end SemiringStep

/-- The §4.1 error identity.  With `u` a unit,
`¼(u + 1 + 1 + u^{-1}) - 1 = ¼ u^{-1} (u - 1)²`.

This is `prop:unipotentstabilization`'s computation: the composite of the two stabilized maps is
`¼(u + 2 + u^{-1})` where `u = φ_-^τ ∘ φ_+`, so its deviation from the identity is the **square**
of the old one, up to a unit — whence the halving `ẽ ≤ ⌈e/2⌉`. -/
theorem quarter_avg_sub_one (h2 : (2 : L) ≠ 0) {u : A} (hu : IsUnit u) :
    (half h2 * half h2) • (u + 1 + 1 + Ring.inverse u) - 1
      = (half h2 * half h2) • (Ring.inverse u * (u - 1) ^ 2) := by
  have hb : Ring.inverse u * u = 1 := Ring.inverse_mul_cancel u hu
  have key : Ring.inverse u * (u - 1) ^ 2 = u + 1 + 1 + Ring.inverse u - (1 + 1 + 1 + 1) := by
    have h1 : (u - 1) ^ 2 = u * u - u - u + 1 := by rw [sq]; noncomm_ring
    rw [h1, mul_add, mul_sub, mul_sub, mul_one, ← mul_assoc]
    simp only [hb, one_mul]
    abel
  rw [key, smul_sub]
  have h4 : (half h2 * half h2) • (1 + 1 + 1 + 1 : A) = 1 := by
    simp only [smul_add, ← add_smul, half_mul_half_four h2, one_smul]
  rw [h4]

/-- The §4.1 halving, in the ring. -/
theorem quarter_avg_error_pow (h2 : (2 : L) ≠ 0) {u : A} (hu : IsUnit u) {m : ℕ}
    (hm : (u - 1) ^ m = 0) :
    ((half h2 * half h2) • (u + 1 + 1 + Ring.inverse u) - 1) ^ (m ⌈/⌉ 2) = 0 := by
  have hcom : Commute (Ring.inverse u) ((u - 1) ^ 2) := by
    refine Commute.pow_right ?_ 2
    exact Commute.inverse_left hu ((Commute.refl u).sub_right (Commute.one_right u))
  have h2m : m ≤ 2 * (m ⌈/⌉ 2) := by
    rw [Nat.ceilDiv_eq_add_pred_div]; omega
  have hzero : (u - 1) ^ (2 * (m ⌈/⌉ 2)) = 0 := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le h2m
    rw [hj, pow_add, hm, zero_mul]
  rw [quarter_avg_sub_one h2 hu, smul_pow, hcom.mul_pow, ← pow_mul, mul_comm 2 (m ⌈/⌉ 2),
    ← mul_comm 2 (m ⌈/⌉ 2), hzero, mul_zero, smul_zero]

end Step

section LinInv

variable {R : Type u} [Semiring R] {M : Type v} {M₂ : Type w}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R M₂]

/-- The **junk-valued two-sided inverse** of a linear map: `linInv f` is the inverse of `f` when
`f` is invertible, and `0` otherwise.  This is mathlib's `Ring.inverse` idiom, transported to maps
between two different modules, where mathlib has no such operation
(`ledger/MATHLIB-DECISIONS.tsv` `MD-S6-02`).

It is what lets the recursion of `cor:unipotentstabilization` (clause `RQ2-4.02-H2`) be written
down *as the source writes it* — `φ^{(k+1)}_± = ½(φ^{(k)}_± + (φ^{(k),τ}_∓)^{-1})` — even though
the invertibility of the `k`-th iterate is only established afterwards, by clause `RQ2-4.02-C5`.

@census none
-/
noncomputable def linInv (f : M →ₗ[R] M₂) : M₂ →ₗ[R] M := by
  classical
  exact if h : ∃ g : M₂ →ₗ[R] M, g.comp f = LinearMap.id ∧ f.comp g = LinearMap.id
    then h.choose else 0

/-- `linInv` is characterized by being a two-sided inverse: any two-sided inverse **is**
`linInv f`. -/
theorem linInv_eq_of {f : M →ₗ[R] M₂} {g : M₂ →ₗ[R] M} (hgf : g.comp f = LinearMap.id)
    (hfg : f.comp g = LinearMap.id) : linInv f = g := by
  classical
  have hex : ∃ g : M₂ →ₗ[R] M, g.comp f = LinearMap.id ∧ f.comp g = LinearMap.id := ⟨g, hgf, hfg⟩
  rw [linInv, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  -- two two-sided inverses of `f` agree
  calc hex.choose = hex.choose.comp (f.comp g) := by rw [hfg, LinearMap.comp_id]
    _ = (hex.choose.comp f).comp g := by rw [LinearMap.comp_assoc]
    _ = g := by rw [h1, LinearMap.id_comp]

/-- On an isomorphism, `linInv` is the inverse. -/
theorem linInv_coe (f : M ≃ₗ[R] M₂) : linInv (f : M →ₗ[R] M₂) = (f.symm : M₂ →ₗ[R] M) :=
  linInv_eq_of (by ext x; simp) (by ext x; simp)

/-- The junk value: `linInv f = 0` when `f` has no two-sided inverse. -/
theorem linInv_of_not_exists {f : M →ₗ[R] M₂}
    (h : ¬ ∃ g : M₂ →ₗ[R] M, g.comp f = LinearMap.id ∧ f.comp g = LinearMap.id) :
    linInv f = 0 := by
  classical
  rw [linInv, dif_neg h]

/-- `linInv f` is a left inverse whenever `f` has a two-sided inverse. -/
theorem linInv_comp_of_exists {f : M →ₗ[R] M₂} {g : M₂ →ₗ[R] M} (hgf : g.comp f = LinearMap.id)
    (hfg : f.comp g = LinearMap.id) : (linInv f).comp f = LinearMap.id := by
  rw [linInv_eq_of hgf hfg]; exact hgf

/-- `linInv f` is a right inverse whenever `f` has a two-sided inverse. -/
theorem comp_linInv_of_exists {f : M →ₗ[R] M₂} {g : M₂ →ₗ[R] M} (hgf : g.comp f = LinearMap.id)
    (hfg : f.comp g = LinearMap.id) : f.comp (linInv f) = LinearMap.id := by
  rw [linInv_eq_of hgf hfg]; exact hfg

/-- `f` has a two-sided linear inverse — the condition under which `linInv f` is that inverse.
It is the invertibility clause `RQ2-4.02-C5` in the form the recursion consumes.

@census none
-/
def HasInverse (f : M →ₗ[R] M₂) : Prop :=
  ∃ g : M₂ →ₗ[R] M, g.comp f = LinearMap.id ∧ f.comp g = LinearMap.id

theorem HasInverse.linInv_comp {f : M →ₗ[R] M₂} (hf : HasInverse f) :
    (linInv f).comp f = LinearMap.id := by
  obtain ⟨g, hgf, hfg⟩ := hf
  rw [linInv_eq_of hgf hfg]; exact hgf

theorem HasInverse.comp_linInv {f : M →ₗ[R] M₂} (hf : HasInverse f) :
    f.comp (linInv f) = LinearMap.id := by
  obtain ⟨g, hgf, hfg⟩ := hf
  rw [linInv_eq_of hgf hfg]; exact hfg

theorem HasInverse.linInv {f : M →ₗ[R] M₂} (hf : HasInverse f) : HasInverse (linInv f) :=
  ⟨f, hf.comp_linInv, hf.linInv_comp⟩

theorem HasInverse.bijective {f : M →ₗ[R] M₂} (hf : HasInverse f) : Function.Bijective f := by
  obtain ⟨g, hgf, hfg⟩ := hf
  constructor
  · intro x y hxy
    have hx := congrArg (fun m => (m : M →ₗ[R] M) x) hgf
    have hy := congrArg (fun m => (m : M →ₗ[R] M) y) hgf
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at hx hy
    rw [← hx, ← hy, hxy]
  · intro y
    refine ⟨g y, ?_⟩
    have := congrArg (fun m => (m : M₂ →ₗ[R] M₂) y) hfg
    simpa using this

theorem comp_eq_id_apply {f : M →ₗ[R] M₂} {g : M₂ →ₗ[R] M} (h : g.comp f = LinearMap.id)
    (x : M) : g (f x) = x := by
  have := congrArg (fun m => (m : M →ₗ[R] M) x) h
  simpa using this

theorem linInv_linInv {f : M →ₗ[R] M₂} (hf : HasInverse f) : linInv (linInv f) = f :=
  linInv_eq_of hf.comp_linInv hf.linInv_comp

theorem comp_eq_id_symm {f : M →ₗ[R] M₂} {g : M₂ →ₗ[R] M} (hf : HasInverse f)
    (h : g.comp f = LinearMap.id) : f.comp g = LinearMap.id := by
  have hg : g = linInv f := by
    calc g = g.comp (f.comp (linInv f)) := by rw [hf.comp_linInv, LinearMap.comp_id]
      _ = (g.comp f).comp (linInv f) := by
          exact (LinearMap.comp_assoc _ _ _).symm
      _ = linInv f := by rw [h, LinearMap.id_comp]
  rw [hg, hf.comp_linInv]

theorem HasInverse.comp {M₃ : Type w} [AddCommMonoid M₃] [Module R M₃] {f : M₂ →ₗ[R] M₃}
    {g : M →ₗ[R] M₂} (hf : HasInverse f) (hg : HasInverse g) : HasInverse (f.comp g) := by
  obtain ⟨f', hf1, hf2⟩ := hf
  obtain ⟨g', hg1, hg2⟩ := hg
  refine ⟨g'.comp f', LinearMap.ext fun x => ?_, LinearMap.ext fun x => ?_⟩
  · simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [comp_eq_id_apply hf1 (g x), comp_eq_id_apply hg1 x]
  · simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [comp_eq_id_apply hg2 (f' x), comp_eq_id_apply hf2 x]

theorem linInv_comp_eq {M₃ : Type w} [AddCommMonoid M₃] [Module R M₃] {f : M₂ →ₗ[R] M₃}
    {g : M →ₗ[R] M₂} (hf : HasInverse f) (hg : HasInverse g) :
    linInv (f.comp g) = (linInv g).comp (linInv f) := by
  refine linInv_eq_of (LinearMap.ext fun x => ?_) (LinearMap.ext fun x => ?_)
  · simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [comp_eq_id_apply hf.linInv_comp (g x), comp_eq_id_apply hg.linInv_comp x]
  · simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [comp_eq_id_apply hg.comp_linInv (linInv f x), comp_eq_id_apply hf.comp_linInv x]

end LinInv

section LinInvField

variable {L : Type u} [Field L] {M : Type v} {M₂ : Type w}
variable [AddCommMonoid M] [Module L M] [AddCommMonoid M₂] [Module L M₂]

theorem HasInverse.smul {f : M →ₗ[L] M₂} (hf : HasInverse f) {c : L} (hc : c ≠ 0) :
    HasInverse (c • f) := by
  obtain ⟨g, h1, h2⟩ := hf
  refine ⟨c⁻¹ • g, ?_, ?_⟩
  · rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, h1]
  · rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, h2]

end LinInvField



section LinInvEnd

variable {R : Type u} [Semiring R] {M : Type v} [AddCommMonoid M] [Module R M]

/-- On endomorphisms the two junk-valued inverses agree: mathlib's `Ring.inverse` and `linInv`. -/
theorem ring_inverse_eq_linInv (f : Module.End R M) : Ring.inverse f = linInv f := by
  classical
  by_cases hf : IsUnit f
  · obtain ⟨u, rfl⟩ := hf
    rw [Ring.inverse_unit]
    refine (linInv_eq_of ?_ ?_).symm
    · exact u.inv_mul
    · exact u.mul_inv
  · rw [Ring.inverse_non_unit _ hf]
    refine (linInv_of_not_exists ?_).symm
    rintro ⟨g, hgf, hfg⟩
    exact hf ⟨⟨f, g, hfg, hgf⟩, rfl⟩

theorem hasInverse_iff_isUnit (f : Module.End R M) : HasInverse f ↔ IsUnit f := by
  constructor
  · rintro ⟨g, hgf, hfg⟩
    exact ⟨⟨f, g, hfg, hgf⟩, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨(u⁻¹ : (Module.End R M)ˣ), u.inv_mul, u.mul_inv⟩

end LinInvEnd



section NeumannHasInverse

variable {L : Type u} [Field L] {P : Type v} [AddCommMonoid P] [Module L P]

/-- The `HasInverse` form of `isUnit_one_add_of_isNilpotent`, which is what the recursion of
`cor:unipotentstabilization` consumes. -/
theorem hasInverse_one_add_of_isNilpotent {n : Module.End L P} (hn : IsNilpotent n) :
    HasInverse (1 + n) :=
  (hasInverse_iff_isUnit _).mpr (isUnit_one_add_of_isNilpotent hn)

end NeumannHasInverse

end RationalQuivers.Unipotent
