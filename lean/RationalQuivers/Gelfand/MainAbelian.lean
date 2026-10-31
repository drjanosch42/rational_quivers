module

public import RationalQuivers.Gelfand.Main

@[expose] public section

/-!
# `rmk:EEabelian` (§5.3, stage T5)

`Rep^nil(Γ_E)` is abelian, by transport of structure along `𝔼_E` from `HC_λ(𝔤,K)_E` (which is abelian,
`HC.HC.abelian`), for `ℓ ≥ 1` and `ℓ = 0`; so `𝔼_E` is an equivalence of abelian categories.

The proof is stage T3's (`Gelfand.repNilTarget_abelian`, `Gelfand/Main.lean`); this module holds the
census claimant only, so that no frozen file carries the new `@census` tag (team-lead decision
2026-10-18). Module created in v2 WP-13.
-/

namespace RationalQuivers.Gelfand

open CategoryTheory

/-- **`rmk:EEabelian`**: for every field `E` of characteristic `0` and every `ℓ`, the equivalence
`𝔼_E : HC_λ(𝔤,K)_E ≃ Rep^nil(Γ_E)` (functor pinned) carries an abelian structure on `Rep^nil(Γ_E)` for
which the inverse is additive (from `HC.HC.abelianStr`).

@census    RQ2-5.21
@source    rmk:EEabelian
@clauses   RQ2-5.21-C1, RQ2-5.21-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION, as `RQ2-0.02-C3` (`Gelfand.gelfand_equivalence`): the abelian
structure of `Rep^nil(Γ_E)` is the one transported along `𝔼_E`; the tree has no native one to compare
it with (agreement by uniqueness of additive structures, a meta-argument).  Restates
`Gelfand.repNilTarget_abelian` (T3).
-/
theorem gelfand_equivalence_abelian (E : Type) [Field E] [CharZero E] (D : HC.ImagUnit E) (ℓ : ℕ) :
    ∃ e : HC.HC ℓ E D ≌ (RepNilTarget D ℓ).FullSubcategory, e.functor = E_E E D ℓ ∧
      ∃ A : Abelian (RepNilTarget D ℓ).FullSubcategory,
        @Functor.Additive _ _ _ _ A.toPreadditive HC.HC.abelianStr.toPreadditive e.inverse :=
  repNilTarget_abelian E D ℓ

end RationalQuivers.Gelfand
