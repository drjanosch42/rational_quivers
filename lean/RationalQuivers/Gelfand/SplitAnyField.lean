module

public import RationalQuivers.Gelfand.Split.EssSurj

@[expose] public section

/-!
# `rmk:splitequivalenceanyfield` (§5.1, stage T5)

The split equivalence of §5.1 holds over **every** field `F` of characteristic `0`, not only over
`L_E`: the formulas of `def:EEsplit` define an equivalence from the concrete category `HCF F ℓ` of
`F`-modules `M = ⊕_n M_n` with `H, X, Y` (`ℓ ≥ 1`) to the nilpotent finite-dimensional representations
of the Gelfand quiver over `F` satisfying its relation; and `HCF F ℓ` is equivalent to
`HC_λ(𝔤,K)_F` in the parity-cut presentation whenever `√-1 ∈ F` (in Lean: for every `F`).

The proofs are stage T2's (`Gelfand/Split/`); this module holds the census claimant only, so that no
frozen file carries the new `@census` tag (team-lead decision 2026-10-18). Module created in v2 WP-13.
-/

namespace RationalQuivers.Gelfand

open CategoryTheory

/-- **`rmk:splitequivalenceanyfield`**: for every field `F` of characteristic `0` and `ℓ ≥ 1`,
`𝔼_F` (the formulas of `def:EEsplit`) is an equivalence `HCF F ℓ ≃ Rep^nil(Gelfand quiver over F, relation)`,
with the functor pinned; and `HC_λ(𝔤,K)_F ≃ HCF F ℓ`.

@census    RQ2-5.20
@source    rmk:splitequivalenceanyfield
@clauses   RQ2-5.20-C1, RQ2-5.20-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation): the source category of `C1` is `Split.HCF F ℓ`;
`C2` is stated for every `F` (`Split.hcLambdaFEquiv`), the remark needs it only for `√-1 ∈ F`, where
`HCLambda ℓ F` is `HC_λ(𝔤,K)_F`.  Restates `Split.equivalence` and `Split.hcLambdaFEquiv` (T2).
-/
theorem split_equivalence_anyField (F : Type) [Field F] [CharZero F] {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (∃ e : Split.HCF F ℓ ≌ (RepNilRelSplit F).FullSubcategory,
        e.functor ⋙ (RepNilRelSplit F).ι = Split.E_F ℓ hℓ) ∧
      Nonempty (HC.HCLambda ℓ F ≌ Split.HCF F ℓ) :=
  ⟨Split.equivalence (L := F) ℓ hℓ, ⟨Split.hcLambdaFEquiv F ℓ⟩⟩

end RationalQuivers.Gelfand
