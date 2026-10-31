module

public import RationalQuivers.Unipotent.SquareRoots

@[expose] public section

/-!
# Semilinear transport of unipotent square roots between two spaces (final-release WP-16a)

`prop:unipotentsquareroots`(d) as the corrected source states it (census `RQ2-4.05-C5`, r18): for
**every field automorphism** `σ` of `L`, **every** `L`-vector space `W'` and **every**
`σ`-semilinear bijection `ψ : W → W'`, the automorphism `ψ φ ψ⁻¹` of `W'` again has property
`eq:phinilpotency`, and `(ψ φ ψ⁻¹)^{1/2} = ψ φ^{1/2} ψ⁻¹` (`eq:semilinearconjugation`).

The existing `sqrt_semilinearConj` (`Unipotent/SquareRoots.lean`) is the case `W' = W`,
`σ ∈ Gal(L/K)`; it is unchanged.  Here the conjugate is `semilinearConjTo`, and the proof goes
through the uniqueness clause `sqrt_unique` (`RQ2-4.05-C6`) rather than the Newton recursion.

* `RationalQuivers.Unipotent.semilinearConjTo` — `φ ↦ ψ ∘ φ ∘ ψ⁻¹`, `End_L W → End_L W'`.
* `RationalQuivers.Unipotent.sqrt_semilinearConjTo` — clause `RQ2-4.05-C5`, both conjuncts.
-/

universe u v w

namespace RationalQuivers.Unipotent

variable {L : Type u} [Field L] {W : Type v} [AddCommGroup W] [Module L W]
  {W' : Type w} [AddCommGroup W'] [Module L W']

section Transport

variable (σ : L ≃+* L) (ψ : W ≃+ W') (hψ : ∀ (a : L) (x : W), ψ (a • x) = σ a • ψ x)

/-- Conjugation `φ ↦ ψ ∘ φ ∘ ψ⁻¹` of an `L`-linear endomorphism of `W` by a `σ`-semilinear
additive bijection `ψ : W → W'`, `σ` any field automorphism of `L`.  The result is `L`-linear.
@census none (helper for `RQ2-4.05-C5`) -/
def semilinearConjTo (φ : Module.End L W) : Module.End L W' where
  toFun x := ψ (φ (ψ.symm x))
  map_add' x y := by simp
  map_smul' c x := by
    have hsymm : ψ.symm (c • x) = σ.symm c • ψ.symm x := by
      apply ψ.injective; rw [hψ]; simp
    simp only [hsymm, map_smul, RingHom.id_apply, hψ]
    simp

/-- @census none (helper) -/
@[simp] theorem semilinearConjTo_apply (φ : Module.End L W) (x : W') :
    semilinearConjTo σ ψ hψ φ x = ψ (φ (ψ.symm x)) := rfl

/-- @census none (helper) -/
theorem semilinearConjTo_one : semilinearConjTo σ ψ hψ 1 = 1 := by ext x; simp

/-- @census none (helper) -/
theorem semilinearConjTo_zero : semilinearConjTo σ ψ hψ 0 = 0 := by ext x; simp

/-- @census none (helper) -/
theorem semilinearConjTo_mul (a b : Module.End L W) :
    semilinearConjTo σ ψ hψ (a * b) = semilinearConjTo σ ψ hψ a * semilinearConjTo σ ψ hψ b := by
  ext x; simp

/-- @census none (helper) -/
theorem semilinearConjTo_add (a b : Module.End L W) :
    semilinearConjTo σ ψ hψ (a + b) = semilinearConjTo σ ψ hψ a + semilinearConjTo σ ψ hψ b := by
  ext x; simp

/-- @census none (helper) -/
theorem semilinearConjTo_sub (a b : Module.End L W) :
    semilinearConjTo σ ψ hψ (a - b) = semilinearConjTo σ ψ hψ a - semilinearConjTo σ ψ hψ b := by
  ext x; simp

/-- @census none (helper) -/
theorem semilinearConjTo_pow (a : Module.End L W) (n : ℕ) :
    semilinearConjTo σ ψ hψ (a ^ n) = (semilinearConjTo σ ψ hψ a) ^ n := by
  induction n with
  | zero => simp [semilinearConjTo_one]
  | succ n ih => rw [pow_succ, pow_succ, semilinearConjTo_mul, ih]

/-- @census none (helper) -/
theorem semilinearConjTo_isNilpotent {a : Module.End L W} (h : IsNilpotent a) :
    IsNilpotent (semilinearConjTo σ ψ hψ a) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [← semilinearConjTo_pow, hn, semilinearConjTo_zero]⟩

end Transport

/-- **`prop:unipotentsquareroots`(d), corrected text** (clause `RQ2-4.05-C5`): for every field
automorphism `σ` of `L`, every `L`-vector space `W'` and every `σ`-semilinear bijection
`ψ : W → W'`, the endomorphism `ψ φ ψ⁻¹` of `W'` is an **automorphism with property
`eq:phinilpotency`** (`ψ φ ψ⁻¹ = 𝟏 + n'` with `n'` nilpotent), and
`(ψ φ ψ⁻¹)^{1/2} = ψ φ^{1/2} ψ⁻¹` (`eq:semilinearconjugation`).

Strengthens `RationalQuivers.Unipotent.sqrt_semilinearConj` (`ψ : W ≃+ W`, `σ ∈ Gal(L/K)`, the
nilpotency conjunct not stated) for row `RQ2-4.05-C5` (final-release WP-16a, MISMATCH-TRIAGE #1).

@census    none (auxiliary; clause witness for `RQ2-4.05-C5`)
@source    prop:unipotentsquareroots
@clauses   RQ2-4.05-C5
@imports   none
@divergence none -/
theorem sqrt_semilinearConjTo (h2 : (2 : L) ≠ 0) (σ : L ≃+* L) (ψ : W ≃+ W')
    (hψ : ∀ (a : L) (x : W), ψ (a • x) = σ a • ψ x)
    (φ n : Module.End L W) (hn : IsNilpotent n) (hφ : φ = 1 + n) :
    IsUnit (semilinearConjTo σ ψ hψ φ) ∧
      (∃ n' : Module.End L W', IsNilpotent n' ∧ semilinearConjTo σ ψ hψ φ = 1 + n') ∧
      sqrt h2 (semilinearConjTo σ ψ hψ φ) = semilinearConjTo σ ψ hψ (sqrt h2 φ) := by
  have hn' : IsNilpotent (semilinearConjTo σ ψ hψ n) := semilinearConjTo_isNilpotent σ ψ hψ hn
  have hφ' : semilinearConjTo σ ψ hψ φ = 1 + semilinearConjTo σ ψ hψ n := by
    rw [hφ, semilinearConjTo_add, semilinearConjTo_one]
  refine ⟨?_, ⟨_, hn', hφ'⟩, ?_⟩
  · rw [hφ']; exact isUnit_one_add_of_isNilpotent hn'
  · obtain ⟨-, hm, hsq⟩ := sqrt_spec h2 φ n hn hφ
    refine (sqrt_unique h2 (semilinearConjTo σ ψ hψ φ) (semilinearConjTo σ ψ hψ (sqrt h2 φ))
      (semilinearConjTo σ ψ hψ (sqrt h2 φ - 1)) (semilinearConjTo_isNilpotent σ ψ hψ hm)
      ?_ ?_).symm
    · rw [semilinearConjTo_sub, semilinearConjTo_one]; abel
    · rw [← semilinearConjTo_pow, hsq]

end RationalQuivers.Unipotent
