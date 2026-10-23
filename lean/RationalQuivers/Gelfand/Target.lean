import RationalQuivers.HC.ImagUnitQuiver
import RationalQuivers.Quiver.Rep.Nilpotent

/-!
# The target quiver `Γ_E` (tex §5, opening: `def:GammaE`, `lem:GammaEbasechange`)

Formalizes the definition of the `E`-rational quiver `Γ_E` at the opening of tex §5
(`def:GammaE`, census `RQ2-5.10`): for a field `E` of characteristic `0` with `L_E = E(√-1)`,
`G_E = Gal(L_E/E)` and the injective character `χ_E : G_E → {±1}` (`def:sqrtminusone`,
`HC.ImagUnit`), `Γ_E` is the Gelfand quiver (`ℓ ≥ 1`) resp. the cyclic quiver (`ℓ = 0`), on which
`σ ∈ G_E` acts trivially if `χ_E(σ) = 1` and by the `±`-swap of `ex:gelfand` resp. `ex:cyclic` if
`χ_E(σ) = -1`; and the target category `Rep^nil(Γ_E)`, whose objects satisfy the relation
`a₋b₋ = a₊b₊` for `ℓ ≥ 1`.

## Main definitions
* `Gelfand.GammaE D ℓ : RationalQuiver E D.L` — `def:GammaE` (claimant of `RQ2-5.10`), built from
  T0's sign-character quivers `RationalQuiver.gelfandOfSign` / `cyclicOfSign` at `χ := D.chiHom`.
* `Gelfand.SatisfiesGelfandRelationE` — the relation `a₋b₋ = a₊b₊` on a representation of `Γ_E`, `ℓ ≥ 1`.
* `Gelfand.RepNilTarget D ℓ` — `Rep^nil(Γ_E)`: finite-dimensional nilpotent representations, with the
  relation for `ℓ ≥ 1` (`RQ2-5.10-C4`).

## Main results
* `GammaE_isSplit_iff` — `Γ_E` is split iff `√-1 ∈ E` (`RQ2-5.10-C2`, and `C3` by `GammaE_ρ_of_chi_neg`).

## Implementation notes
`GammaE` is defined by recursion on `ℓ` (`0 ↦` cyclic, `k + 1 ↦` Gelfand), so that for `ℓ = k + 1` the
Gelfand quiver is the definitional value and the relation can be stated without transport.
-/

namespace RationalQuivers.Gelfand

open RationalQuivers.HC CategoryTheory

variable {E : Type} [Field E] [CharZero E]

/-- **Definition** (`def:GammaE`). For a field `E` of characteristic `0` and `D : ImagUnit E`
(`L_E = D.L`, `G_E = Gal(L_E/E)`, `χ_E = D.chi`), `Γ_E` is the `E`-rational quiver with respect to
`L_E/E` given by the cyclic quiver of `ex:cyclic` if `ℓ = 0` and by the Gelfand quiver of
`ex:gelfand` if `ℓ ≥ 1`, with `σ ∈ G_E` acting trivially if `χ_E(σ) = 1` and by the `±`-swap if
`χ_E(σ) = -1`: if `√-1 ∈ E` the action is trivial and `Γ_E` is split; if `√-1 ∉ E` the non-trivial
`c ∈ G_E` acts as the non-trivial element of `Gal(ℚ[√-1]/ℚ)` does in `ex:gelfand` resp. `ex:cyclic`.

@census    RQ2-5.10
@source    def:GammaE
@clauses   RQ2-5.10-H1, RQ2-5.10-H2, RQ2-5.10-C1, RQ2-5.10-C2, RQ2-5.10-C3, RQ2-5.10-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation). The quiver is defined by recursion on `ℓ`
(`0 ↦` cyclic, `k + 1 ↦` Gelfand) rather than by a case distinction `ℓ ≥ 1` / `ℓ = 0` on the same
`ℓ`; the two agree on every `ℓ` (`GammaE_of_pos`, `GammaE_zero`). The action "as in `ex:gelfand`
resp. `ex:cyclic`" is the sign-character action `ofSign` of T0 (`Quiver/OfSign.lean`), which is the
action of `ex:gelfand`'s `gelfandOfCardTwo` when `|G_E| = 2`
(`ImagUnit.gelfandOfSign_eq_gelfandOfCardTwo`). Clause `C2` is `GammaE_isSplit_iff`, `C3` is
`GammaE_ρ_of_chi_neg`, `C4` (the relation in the target category) is `RepNilTarget`.
-/
noncomputable def GammaE (D : ImagUnit E) : ℕ → RationalQuiver E D.L
  | 0 => RationalQuiver.cyclicOfSign E D.L D.chiHom
  | _ + 1 => RationalQuiver.gelfandOfSign E D.L D.chiHom

variable (D : ImagUnit E)

/-- `Γ_E` for `ℓ ≥ 1` is the sign-character Gelfand quiver.  @census none (helper) -/
theorem GammaE_of_pos {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    GammaE D ℓ = RationalQuiver.gelfandOfSign E D.L D.chiHom := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  rfl

/-- `Γ_E` for `ℓ = 0` is the sign-character cyclic quiver.  @census none (helper) -/
theorem GammaE_zero : GammaE D 0 = RationalQuiver.cyclicOfSign E D.L D.chiHom := rfl

/-- `χ_E` is trivial iff `√-1 ∈ E`.  @census none (helper) -/
theorem chiHom_eq_one_iff : D.chiHom = 1 ↔ ∃ a : E, a * a = -1 := by
  constructor
  · intro h
    by_contra hn
    obtain ⟨σ, hσ⟩ := D.exists_chi_neg_one_iff.mpr hn
    have h1 : D.chiHom σ = 1 := by rw [h]; rfl
    rw [ImagUnit.chiHom_apply, hσ] at h1
    exact absurd h1 (by decide)
  · intro h
    ext1 σ
    rw [ImagUnit.chiHom_apply, D.chi_eq_one_of_sqrt h σ]
    rfl

/-- **`RQ2-5.10-C2`.** `Γ_E` is split (the `G_E`-action is trivial) iff `√-1 ∈ E`.
@census none (helper: clause `RQ2-5.10-C2`) -/
theorem GammaE_isSplit_iff (ℓ : ℕ) : (GammaE D ℓ).IsSplit ↔ ∃ a : E, a * a = -1 := by
  rw [← chiHom_eq_one_iff D]
  cases ℓ with
  | zero =>
    exact RationalQuiver.ofSign_isSplit_iff E D.L _ _ _ RQuiver.cyclicSignSwap_ne_one D.chiHom
  | succ k =>
    exact RationalQuiver.ofSign_isSplit_iff E D.L _ _ _ RQuiver.gelfandSwap_ne_one D.chiHom

/-- **`RQ2-5.10-C3`.** An element `σ ∈ G_E` with `χ_E(σ) = -1` (i.e. `c`, when `√-1 ∉ E`) acts on
`Γ_E` by the `±`-swap of `ex:gelfand` (`ℓ ≥ 1`) resp. `ex:cyclic` (`ℓ = 0`).
@census none (helper: clause `RQ2-5.10-C3`) -/
theorem GammaE_ρ_of_chi_neg {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = -1) (ℓ : ℕ) :
    (GammaE D ℓ).ρ σ = (match ℓ with
      | 0 => RQuiver.cyclicSignSwap
      | _ + 1 => RQuiver.gelfandSwap) := by
  have hne : D.chiHom σ ≠ 1 := by
    rw [ImagUnit.chiHom_apply, hσ]; decide
  cases ℓ with
  | zero =>
    show (if D.chiHom σ = 1 then 1 else RQuiver.cyclicSignSwap) = _
    rw [if_neg hne]
  | succ k =>
    show (if D.chiHom σ = 1 then 1 else RQuiver.gelfandSwap) = _
    rw [if_neg hne]

/-- The relation `a₋b₋ = a₊b₊` of `ex:gelfand` on a representation of `Γ_E`, `ℓ ≥ 1`: the two
path maps `M(⋆) → M(⋆)` along `⋆ → − → ⋆` and `⋆ → + → ⋆` agree.  @census none (helper) -/
def SatisfiesGelfandRelationE (M : RationalQuiver.Rep (RationalQuiver.gelfandOfSign E D.L D.chiHom)) :
    Prop :=
  M.pathMap (a := (1 : Fin 3)) (b := (1 : Fin 3)) RQuiver.pathMinus
    = M.pathMap (a := (1 : Fin 3)) (b := (1 : Fin 3)) RQuiver.pathPlus

/-- **`Rep^nil(Γ_E)`** (`def:GammaE`, clause `C4`): the finite-dimensional nilpotent representations
of `Γ_E`, which for `ℓ ≥ 1` are required to satisfy `a₋b₋ = a₊b₊`.
@census none (auxiliary: the target category of `thm:EEequivalence`/`thm:cyclicEEequivalence`) -/
def RepNilTarget : (ℓ : ℕ) → ObjectProperty (RationalQuiver.FDRep (GammaE D ℓ))
  | 0 => fun M => M.toRep.IsNilpotent
  | _ + 1 => fun M => M.toRep.IsNilpotent ∧ SatisfiesGelfandRelationE D M.toRep

end RationalQuivers.Gelfand
