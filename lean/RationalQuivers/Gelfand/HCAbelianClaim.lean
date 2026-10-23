import RationalQuivers.HC.Abelian

/-!
# `rmk:HCabelian` (§3.2, stage T5)

`HC_λ(𝔤,K)_E` is an abelian category: kernels and cokernels are taken in `E`-vector spaces, carry
canonical structures and satisfy the universal properties; a morphism is a monomorphism iff its kernel
is `0` and an epimorphism iff its cokernel is `0`.

The proofs are stage T3's (`HC/Abelian.lean`: `HC.HC.abelian`, `kerObj`, `cokerObj`, `kernelIsLimit`,
`cokernelIsColimit`, `mono_iff_ker_eq_bot`, `epi_iff_range_eq_top`); this module holds the census
claimant only, so that no frozen file carries the new `@census` tag (team-lead decision 2026-10-18;
the permanent fix, `@census RQ2-3.16` on `HC.HC.abelian`, is in the release-time `R-PROC-4` batch).
Module created in v2 WP-13.
-/

namespace RationalQuivers.Gelfand

open CategoryTheory RationalQuivers.HC

/-- **`rmk:HCabelian`**: for every field `E` of characteristic `0`, every `ℓ` and `D : ImagUnit E`,
`HC_λ(𝔤,K)_E` is abelian, and a morphism `f` is a monomorphism (resp. an epimorphism) iff its
vector-space kernel is `0` (resp. its cokernel is `0`).

@census    RQ2-3.16
@source    rmk:HCabelian
@clauses   RQ2-3.16-H1, RQ2-3.16-C1, RQ2-3.16-C2, RQ2-3.16-C3, RQ2-3.16-C4, RQ2-3.16-C5, RQ2-3.16-C6,
  RQ2-3.16-C7
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation): `HC_λ(𝔤,K)_E` is `HC ℓ E D` (`EX-HC`); `C1` is
`Nonempty (Abelian …)` (`HC.HC.abelian`, as `harishChandraCat_abelian`); `C2`–`C5` are the constructions
`HC.HC.kerObj`/`cokerObj` with `kernelIsLimit`/`cokernelIsColimit` from which the abelian structure is
assembled (T3, not restated); `C6`, `C7` are stated here.  Restates T3's `HC/Abelian.lean`.
-/
theorem hc_abelian (E : Type) [Field E] [CharZero E] (D : ImagUnit E) (ℓ : ℕ) :
    Nonempty (Abelian (HC.HC ℓ E D)) ∧
      (∀ {A B : HC.HC ℓ E D} (f : A ⟶ B), Mono f ↔ LinearMap.ker (f : HC.HC.Hom A B).toLinearMap = ⊥) ∧
      (∀ {A B : HC.HC ℓ E D} (f : A ⟶ B), Epi f ↔ LinearMap.range (f : HC.HC.Hom A B).toLinearMap = ⊤) :=
  ⟨HC.HC.abelian, HC.HC.mono_iff_ker_eq_bot, HC.HC.epi_iff_range_eq_top⟩

end RationalQuivers.Gelfand
