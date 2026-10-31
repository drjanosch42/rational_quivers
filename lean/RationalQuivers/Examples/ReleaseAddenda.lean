module

public import RationalQuivers.Examples.FiniteDimensional

@[expose] public section

/-!
# §6 release addenda (final-release WP-16a)

New, gate-neutral clause witnesses for §6 rows whose bound claimant is weaker than the corrected
(census r18/r19) clause text.  Nothing here changes an existing declaration.

* `RationalQuivers.Examples.F_kTypes_all` — `RQ2-6.01-C3`: every `K`-type
  `χ_{-(ℓ-1)}, χ_{-(ℓ-3)}, …, χ_{ℓ-1}` of `F_ℓ` is one-dimensional (and these are all of them).
-/

namespace RationalQuivers.Examples

open RationalQuivers.HC RationalQuivers.Gelfand CategoryTheory

/-- **`RQ2-6.01-C3`, corrected text** — the `K`-types `χ_{-(ℓ-1)}, χ_{-(ℓ-3)}, …, χ_{ℓ-1}` of `F_ℓ`
are **one-dimensional**; in particular the two relevant for `E_ℚ`, `F_ℓ[χ_{±(ℓ-1)}]`, are
one-dimensional.  The weights `n` with `|n| ≤ ℓ - 1`, `n ≡ ℓ - 1 (mod 2)` are exactly `suppF ℓ`;
the last conjunct records that no other weight occurs.

Strengthens `RationalQuivers.Examples.F_weightSpaces` (finrank 1 only at `±(ℓ-1)`) for row
`RQ2-6.01-C3` (final-release WP-16a, MISMATCH-TRIAGE #4).

@census    none (auxiliary; clause witness for `RQ2-6.01-C3`)
@source    ex:finitedimensional
@clauses   RQ2-6.01-C3
@imports   none
@divergence none -/
theorem F_kTypes_all (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∀ n : ℤ, -((ℓ : ℤ) - 1) ≤ n → n ≤ (ℓ : ℤ) - 1 → (n - ((ℓ : ℤ) - 1)) % 2 = 0 →
      Module.finrank ImagUnit.qi.L ((F ℓ hℓ).weight.comp n) = 1) ∧
    Module.finrank ImagUnit.qi.L ((F ℓ hℓ).weight.comp ((ℓ : ℤ) - 1)) = 1 ∧
    Module.finrank ImagUnit.qi.L ((F ℓ hℓ).weight.comp (-((ℓ : ℤ) - 1))) = 1 ∧
    (∀ n : ℤ, ¬ (-((ℓ : ℤ) - 1) ≤ n ∧ n ≤ (ℓ : ℤ) - 1 ∧ (n - ((ℓ : ℤ) - 1)) % 2 = 0) →
      (F ℓ hℓ).weight.comp n = ⊥) := by
  have hall : ∀ n : ℤ, -((ℓ : ℤ) - 1) ≤ n → n ≤ (ℓ : ℤ) - 1 → (n - ((ℓ : ℤ) - 1)) % 2 = 0 →
      Module.finrank ImagUnit.qi.L ((F ℓ hℓ).weight.comp n) = 1 := by
    intro n h1 h2 h3
    rw [F_comp]
    exact wtComp_finrank (S := suppF ℓ) ⟨h1, h2, h3⟩
  have hℓz : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
  refine ⟨hall, hall _ (by omega) le_rfl (by simp), hall _ le_rfl (by omega) (by omega), ?_⟩
  intro n hn
  rw [F_comp]
  exact wtComp_eq_bot (S := suppF ℓ) hn

end RationalQuivers.Examples
