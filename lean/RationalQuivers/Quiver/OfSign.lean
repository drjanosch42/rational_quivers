import RationalQuivers.Quiver.Models

/-!
# Rational structures through a sign character

The target quiver `Γ_E` of §5 (`def:GammaE`) is the Gelfand quiver (`ℓ ≥ 1`) or the cyclic quiver
(`ℓ = 0`), split over `L_E = E(√-1)`, on which `σ ∈ G_E = Gal(L_E/E)` acts by the `±`-swap exactly
when `χ_E(σ) = -1` (`def:sqrtminusone`). This module supplies that pattern for an **arbitrary**
character `χ : Gal(L/K) →* ℤˣ` of a finite Galois extension `L/K`, before any `√-1` data exists
(that data, `ImagUnit`, is stage T1's): it is a helper module of §1.2, used by `Gelfand/Target`
(stage T2), and claims no census row.

## Main definitions / results
* `RationalQuivers.MonoidHom.signToInvolution` — `ℤˣ →* H`, `1 ↦ 1`, `-1 ↦ a`, for an involution `a`.
* `RationalQuivers.RationalQuiver.ofSign` — the `K`-rational quiver `(Γ, a ∘ χ)`.
* `RationalQuivers.RationalQuiver.gelfandOfSign`, `…cyclicOfSign` — the Gelfand and the cyclic
  quiver of `ex:gelfand` / `ex:cyclic` with the `±`-swap acting through `χ`.
* `RationalQuivers.RationalQuiver.gelfandOfSign_eq_gelfandOfCardTwo` — for `|Gal(L/K)| = 2` and `χ`
  injective, `gelfandOfSign χ` **is** the v1 quiver `gelfandOfCardTwo` (plan risk R-3: one equality,
  proved once).
* `RationalQuivers.RationalQuiver.ofSign_isSplit_iff` — `(Γ, a ∘ χ)` is split iff `χ` is trivial.

**New in v2 T0 (WP-7, 2026-10-17; plan §6.2 "`Quiver/` (+ `gelfandOfSign`/`cyclicOfSign`)").** The
cyclic quiver's `±`-swap is defined here as `RQuiver.cyclicSignSwap`, because `Species/Examples.lean`'s
`RQuiver.cyclicSwap` (the same automorphism) sits in §2.4, after this module, and carried code is
not moved (D-11). The comparison `cyclicOfSign χ = cyclicOfCardTwo` is the cyclic half of R-3; it
needs `Species/Examples` and is left to the consumer (WP-11), where it is the same two-line proof as
`gelfandOfSign_eq_gelfandOfCardTwo`.
-/

namespace RationalQuivers

namespace RQuiver

/-- The `±`-swap of `ex:cyclic`, `c(±) = ∓`, `c(a) = b`, `c(b) = a`, as an automorphism of the cyclic
quiver (vertices `−`(=0), `+`(=1); arrows `a : − → +`(=0), `b : + → −`(=1)). The same automorphism
as `Species/Examples.lean`'s `RQuiver.cyclicSwap`, defined here so that §1.2 can use it.

@census none (helper: the involution of `cyclicOfSign`)
-/
@[reducible] def cyclicSignSwap : RQuiver.Aut cyclic where
  hom := { onV := Equiv.swap 0 1, onE := Equiv.swap 0 1,
           onV_source := by decide, onV_target := by decide }
  inv := { onV := Equiv.swap 0 1, onE := Equiv.swap 0 1,
           onV_source := by decide, onV_target := by decide }
  hom_inv_id := by refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)
  inv_hom_id := by refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)

/-- The cyclic `±`-swap is an involution.  @census none (helper) -/
theorem cyclicSignSwap_mul_self : cyclicSignSwap * cyclicSignSwap = 1 := by
  refine CategoryTheory.Aut.ext ?_
  refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)

/-- The cyclic `±`-swap is not the identity.  @census none (helper) -/
theorem cyclicSignSwap_ne_one : cyclicSignSwap ≠ 1 := by
  intro h
  have : cyclicSignSwap.hom.onV 0 = (1 : RQuiver.Aut cyclic).hom.onV 0 := by rw [h]
  revert this; decide

end RQuiver

/-- A sign `u ∈ ℤˣ = {±1}` acts through a chosen involution: `1 ↦ 1`, `-1 ↦ a`.

@census none (helper)
-/
def MonoidHom.signToInvolution {H : Type*} [Group H] (a : H) (ha : a * a = 1) : ℤˣ →* H where
  toFun u := if u = 1 then 1 else a
  map_one' := by simp
  map_mul' u v := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp [ha]

/-- The value of `signToInvolution`.  @census none (helper) -/
theorem MonoidHom.signToInvolution_apply {H : Type*} [Group H] (a : H) (ha : a * a = 1)
    (u : ℤˣ) : MonoidHom.signToInvolution a ha u = if u = 1 then 1 else a := rfl

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

namespace RationalQuiver

/-- The `K`-rational quiver `(Γ, a ∘ χ)`: `σ ∈ Gal(L/K)` acts trivially if `χ(σ) = 1` and by the
involution `a` if `χ(σ) = -1`. Continuity is vacuous, `L/K` being finite (`Gal(L/K)` is discrete).

@census none (helper: the pattern of `def:GammaE`, used by `Gelfand/Target`)
-/
noncomputable def ofSign (Γ : RQuiver.{0}) (a : RQuiver.Aut Γ) (ha : a * a = 1)
    (χ : Gal(L/K) →* ℤˣ) : RationalQuiver K L where
  toRQuiver := Γ
  ρ := (MonoidHom.signToInvolution a ha).comp χ
  smooth_V := IsSmooth.of_discreteTopology _
  smooth_E := IsSmooth.of_discreteTopology _

/-- The rational structure of `ofSign`, evaluated.  @census none (helper) -/
theorem ofSign_ρ_apply (Γ : RQuiver.{0}) (a : RQuiver.Aut Γ) (ha : a * a = 1)
    (χ : Gal(L/K) →* ℤˣ) (σ : Gal(L/K)) :
    (ofSign K L Γ a ha χ).ρ σ = if χ σ = 1 then 1 else a := rfl

/-- `(Γ, a ∘ χ)` is split exactly when `χ` is trivial (for `a ≠ 1`).  @census none (helper) -/
theorem ofSign_isSplit_iff (Γ : RQuiver.{0}) (a : RQuiver.Aut Γ) (ha : a * a = 1) (ha1 : a ≠ 1)
    (χ : Gal(L/K) →* ℤˣ) : (ofSign K L Γ a ha χ).IsSplit ↔ χ = 1 := by
  constructor
  · intro h
    have h' : (ofSign K L Γ a ha χ).ρ = 1 := h
    ext1 σ
    have hσ := DFunLike.congr_fun h' σ
    rw [ofSign_ρ_apply, MonoidHom.one_apply] at hσ
    rw [MonoidHom.one_apply]
    by_contra hne
    exact ha1 (by rw [if_neg hne] at hσ; exact hσ)
  · intro h
    show (ofSign K L Γ a ha χ).ρ = 1
    ext1 σ
    rw [ofSign_ρ_apply, h, MonoidHom.one_apply, if_pos rfl]
    rfl

/-- The Gelfand quiver of `ex:gelfand` with the `±`-swap acting through the sign character `χ`:
`c(±) = ∓`, `c(⋆) = ⋆`, `c(a_±) = a_∓`, `c(b_±) = b_∓` for `χ(c) = -1`. With `χ = χ_E` this is
`Γ_E` for `ℓ ≥ 1` (`def:GammaE`, stage T2).

@census none (helper: `def:GammaE`, `ℓ ≥ 1`)
-/
noncomputable def gelfandOfSign (χ : Gal(L/K) →* ℤˣ) : RationalQuiver K L :=
  ofSign K L RQuiver.gelfand RQuiver.gelfandSwap RQuiver.gelfandSwap_mul_self χ

/-- The cyclic quiver of `ex:cyclic` with the `±`-swap acting through the sign character `χ`:
`c(±) = ∓`, `ca = b`, `cb = a` for `χ(c) = -1`. With `χ = χ_E` this is `Γ_E` for `ℓ = 0`
(`def:GammaE`, stage T2).

@census none (helper: `def:GammaE`, `ℓ = 0`)
-/
noncomputable def cyclicOfSign (χ : Gal(L/K) →* ℤˣ) : RationalQuiver K L :=
  ofSign K L RQuiver.cyclic RQuiver.cyclicSignSwap RQuiver.cyclicSignSwap_mul_self χ

/-- For a non-trivial `χ`, `gelfandOfSign χ` is not split (`gelfandSwap_ne_one`): a
non-degenerate inhabitant.  @census none (helper) -/
theorem gelfandOfSign_not_isSplit {χ : Gal(L/K) →* ℤˣ} (hχ : χ ≠ 1) :
    ¬ (gelfandOfSign K L χ).IsSplit :=
  fun h => hχ ((ofSign_isSplit_iff K L _ _ _ RQuiver.gelfandSwap_ne_one χ).mp h)

/-- For a non-trivial `χ`, `cyclicOfSign χ` is not split.  @census none (helper) -/
theorem cyclicOfSign_not_isSplit {χ : Gal(L/K) →* ℤˣ} (hχ : χ ≠ 1) :
    ¬ (cyclicOfSign K L χ).IsSplit :=
  fun h => hχ ((ofSign_isSplit_iff K L _ _ _ RQuiver.cyclicSignSwap_ne_one χ).mp h)

/-- **Plan risk R-3.** For a quadratic `L/K` (`|Gal(L/K)| = 2`) and an **injective** sign character
`χ` (so `χ(c) = -1` for the non-trivial `c`, as `χ_E` is), `gelfandOfSign χ` is, as a structure,
the v1 quiver `gelfandOfCardTwo K L h` of `ex:gelfand`: the two rational structures agree at `1`
and at `c`.

@census none (helper: plan R-3, the identification v1 ↔ v2 of `Γ_ℚ`)
-/
theorem gelfandOfSign_eq_gelfandOfCardTwo (h : Nat.card Gal(L/K) = 2) {χ : Gal(L/K) →* ℤˣ}
    (hχ : Function.Injective χ) : gelfandOfSign K L χ = gelfandOfCardTwo K L h := by
  have hρ : (gelfandOfSign K L χ).ρ = (gelfandOfCardTwo K L h).ρ := by
    ext1 σ
    by_cases hσ : σ = 1
    · subst hσ; rw [map_one, map_one]
    · have hχσ : χ σ ≠ 1 := fun h1 => hσ (hχ (h1.trans (map_one χ).symm))
      rw [show (gelfandOfSign K L χ).ρ σ = if χ σ = 1 then 1 else RQuiver.gelfandSwap from rfl,
        if_neg hχσ]
      exact (gelfandOfCardTwo_rho_apply K L h hσ).symm
  unfold gelfandOfSign ofSign at hρ ⊢
  unfold gelfandOfCardTwo at hρ ⊢
  congr 1

end RationalQuiver

end RationalQuivers
