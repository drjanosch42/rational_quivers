module

public import RationalQuivers.Examples.Basic

@[expose] public section

/-!
# §6.2 — the (limits of) discrete series `D_ℓ = D_ℓ⁺ ⊕ D_ℓ⁻`

Formalizes §6.2 of `latex/rational_quivers.tex` (census `RQ2-6.02`).

## Main definitions / results
* `RationalQuivers.Examples.D` — the object `D_ℓ ∈ HC_{ℓ²}(𝔤,K)_ℚ`, `ℓ ≥ 0`, as a term of
  `HC ℓ ℚ ImagUnit.qi`.
* `RationalQuivers.Examples.D_casimir` — `C` acts by `λ = ℓ²`.
* `RationalQuivers.Examples.D_decomposition` — `D_ℓ = D_ℓ⁺ ⊕ D_ℓ⁻` with the two summands complex
  conjugate to each other.
* `RationalQuivers.Examples.D_irreducible` — irreducibility **over `ℚ`**.
* `RationalQuivers.Examples.D_weightSpaces` — the `K`-type claims.
* `RationalQuivers.Examples.D_quiverRep_eq` / `D_speciesRep_eq` — the `ℓ ≥ 1` (Gelfand) diagrams.
* `RationalQuivers.Examples.D_zero_quiverRep_eq` / `D_zero_speciesRep_eq` — the `ℓ = 0` (cyclic)
  diagrams, where "the Gelfand quiver degenerates to the cyclic quiver".

## Implementation notes

`D_ℓ` is `Examples/Basic.lean`'s weight-line module at

* support `S = {n : |n| ≥ ℓ + 1, n ≡ ℓ - 1 (mod 2)}` — the two half-strings `n ≥ ℓ+1` (the
  holomorphic `D_ℓ⁺`) and `n ≤ -(ℓ+1)` (the anti-holomorphic `D_ℓ⁻`), with the paper's
  `D_ℓ[χ_{±(ℓ-1)}] = 0` exactly the omission of the middle;
* raising scalar `x(n) = (ℓ + n + 1)/2`, which vanishes exactly at `n = -(ℓ+1)` (so `X` kills the
  lowest weight vector of `D_ℓ⁻`) and whose mirror `x(-n) = (ℓ - n + 1)/2` vanishes exactly at
  `n = ℓ+1` (so `Y` kills the lowest weight vector of `D_ℓ⁺`).

This is the **opposite** normalization to `F_ℓ`'s: `F_ℓ` closes its string at the *outer* walls
`±(ℓ-1)`, `D_ℓ` opens it at the *inner* walls `±(ℓ+1)`.  Both satisfy `Basic.lean`'s `WtCas`,
which forces `x(n-2)·x(-n) = (ℓ² - (n-1)²)/4` in either case; which of the two solutions one takes
is exactly which of `F_ℓ`, `D_ℓ` one is building.  §6.3's `P_{ℓ,ε}` is this same normalization on
the **whole** string, and `P^∨_{ℓ,ε}` is `F_ℓ`'s.

`ℓ = 0` is not a separate construction: `suppD 0 = {n : |n| ≥ 1, n odd}` and `scalD 0 n = (n+1)/2`
are the `ℓ = 0` instances of the same formulas, so `D 0` is a term of `HC 0 ℚ ImagUnit.qi` and the `ℓ = 0`
statements are about `𝔼_ℚ` at `ℓ = 0`, i.e. the engine's **cyclic** functor `E_CycFunctor` (`RQ-5.07`).
-/

namespace RationalQuivers.Examples

open RationalQuivers.HC RationalQuivers.Gelfand CategoryTheory
open RationalQuivers.Gelfand.RationalStructure (gelfandQ vtxQ edgeQ RepNilQ)
open RationalQuivers.Gelfand.Cyclic (cyclicQ vtxC edgeC RepNilCycQ)

/-! ## The datum -/

/-- The weights of `D_ℓ`: `|n| ≥ ℓ + 1` with `n ≡ ℓ - 1 (mod 2)`.  @census none (helper) -/
abbrev suppD (ℓ : ℕ) (n : ℤ) : Prop :=
  ((ℓ : ℤ) + 1 ≤ n ∨ n ≤ -((ℓ : ℤ) + 1)) ∧ (n - ((ℓ : ℤ) - 1)) % 2 = 0

/-- The raising scalar of `D_ℓ`: `X · e_n = ((ℓ + n + 1)/2) · e_{n+2}`.  @census none (helper) -/
def scalD (ℓ : ℕ) (n : ℤ) : ℚ := ((ℓ : ℚ) + (n : ℚ) + 1) / 2

theorem scalD_apply (ℓ : ℕ) (n : ℤ) : scalD ℓ n = ((ℓ : ℚ) + (n : ℚ) + 1) / 2 := rfl

/-- The raising scalar vanishes at exactly one weight, the wall `-(ℓ+1)`.  @census none (helper) -/
theorem scalD_ne_zero {ℓ : ℕ} {n : ℤ} (h : n ≠ -((ℓ : ℤ) + 1)) : scalD ℓ n ≠ 0 := by
  intro hcon
  rw [scalD_apply, div_eq_zero_iff] at hcon
  rcases hcon with hc | hc
  · refine h ?_
    have hz : (((ℓ : ℤ) + n + 1 : ℤ) : ℚ) = 0 := by push_cast; push_cast at hc; linarith
    have hi : ((ℓ : ℤ) + n + 1 : ℤ) = 0 := by exact_mod_cast hz
    omega
  · norm_num at hc

theorem scalD_XY (ℓ : ℕ) (n : ℤ) (hn : suppD ℓ n) :
    (if suppD ℓ (n - 2) then scalD ℓ (n - 2) * scalD ℓ (-n) else 0)
      = ((ℓ : ℚ) ^ 2 - ((n : ℚ) - 1) ^ 2) / 4 := by
  by_cases h : suppD ℓ (n - 2)
  · rw [if_pos h, scalD_apply, scalD_apply]
    push_cast
    ring
  · rw [if_neg h]
    obtain ⟨h1, h2⟩ := hn
    have hval : n = (ℓ : ℤ) + 1 := by
      simp only [suppD, not_and, not_or] at h
      omega
    have hq : (n : ℚ) = (ℓ : ℚ) + 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hval
    rw [hq]; ring

theorem scalD_YX (ℓ : ℕ) (n : ℤ) (hn : suppD ℓ n) :
    (if suppD ℓ (n + 2) then scalD ℓ (-(n + 2)) * scalD ℓ n else 0)
      = ((ℓ : ℚ) ^ 2 - ((n : ℚ) + 1) ^ 2) / 4 := by
  by_cases h : suppD ℓ (n + 2)
  · rw [if_pos h, scalD_apply, scalD_apply]
    push_cast
    ring
  · rw [if_neg h]
    obtain ⟨h1, h2⟩ := hn
    have hval : n = -((ℓ : ℤ) + 1) := by
      simp only [suppD, not_and, not_or] at h
      omega
    have hq : (n : ℚ) = -((ℓ : ℚ) + 1) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hval
    rw [hq]; ring

theorem D_sl2 (ℓ : ℕ) : WtSl2 (suppD ℓ) (scalD ℓ) := by
  intro n hn
  rw [scalD_XY ℓ n hn, scalD_YX ℓ n hn]
  ring

theorem D_cas (ℓ : ℕ) : WtCas ℓ (suppD ℓ) (scalD ℓ) := by
  intro n hn
  rw [scalD_XY ℓ n hn]
  ring

theorem D_symm (ℓ : ℕ) : WtSymm (suppD ℓ) := by
  rintro n ⟨h1, h2⟩
  exact ⟨by omega, by omega⟩

theorem D_par (ℓ : ℕ) : WtPar ℓ (suppD ℓ) := fun _ h => h.2

/-! ## Finite generation: the two lowest weight vectors generate -/

/-- **From the two lowest weight vectors, every basis vector is reachable** inside a
`(𝔤,K)`-stable submodule: `X` climbs the holomorphic half and `Y` descends the anti-holomorphic
one, and neither scalar vanishes away from the two walls.  This is `D_fg`'s argument, named so
that `D_irreducible` can reuse it.  @census none (helper) -/
theorem D_top_of_lowest (ℓ : ℕ) {N : Submodule (Qi : Type) (WtCar (suppD ℓ))}
    (hop : (wtWeight (suppD ℓ) (scalD ℓ) (D_sl2 ℓ)).OpStable N)
    (hbp : suppD ℓ ((ℓ : ℤ) + 1)) (hbm : suppD ℓ (-((ℓ : ℤ) + 1)))
    (hgenp : Finsupp.single (⟨(ℓ : ℤ) + 1, hbp⟩ : WtIdx (suppD ℓ)) (1 : (Qi : Type)) ∈ N)
    (hgenm : Finsupp.single (⟨-((ℓ : ℤ) + 1), hbm⟩ : WtIdx (suppD ℓ)) (1 : (Qi : Type)) ∈ N)
    (i : WtIdx (suppD ℓ)) : Finsupp.single i (1 : (Qi : Type)) ∈ N := by
  obtain ⟨h1, h2⟩ := i.2
  rcases h1 with hup | hdn
  · -- `i ≥ ℓ+1`: climb from `e_{ℓ+1}`
    set k : ℕ := (((i : ℤ) - ((ℓ : ℤ) + 1)) / 2).toNat with hkdef
    have hkval : ((ℓ : ℤ) + 1) + 2 * (k : ℤ) = (i : ℤ) := by simp only [hkdef]; omega
    have hS : ∀ j : ℕ, j ≤ k → suppD ℓ (((ℓ : ℤ) + 1) + 2 * (j : ℤ)) := by
      intro j hj
      have hjk : (j : ℤ) ≤ (k : ℤ) := by exact_mod_cast hj
      exact ⟨by omega, by omega⟩
    have hx : ∀ j : ℕ, j < k → scalD ℓ (((ℓ : ℤ) + 1) + 2 * (j : ℤ)) ≠ 0 := by
      intro j hj
      have hjk : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      have hpos : (0 : ℚ) < (ℓ : ℚ) + ((((ℓ : ℤ) + 1) + 2 * (j : ℤ) : ℤ) : ℚ) + 1 := by
        have : (0 : ℤ) < (ℓ : ℤ) + (((ℓ : ℤ) + 1) + 2 * (j : ℤ)) + 1 := by omega
        exact_mod_cast this
      simp only [scalD_apply]
      intro hcon
      rw [div_eq_zero_iff] at hcon
      rcases hcon with hc | hc
      · exact absurd hc (ne_of_gt hpos)
      · norm_num at hc
    have hmem := wtChainUp (D_sl2 ℓ) hop ((ℓ : ℤ) + 1) hbp hgenp k hx hS
    have hidx : (⟨((ℓ : ℤ) + 1) + 2 * (k : ℤ), hS k le_rfl⟩ : WtIdx (suppD ℓ)) = i :=
      Subtype.ext hkval
    rwa [hidx] at hmem
  · -- `i ≤ -(ℓ+1)`: descend from `e_{-(ℓ+1)}`
    set k : ℕ := ((-((ℓ : ℤ) + 1) - (i : ℤ)) / 2).toNat with hkdef
    have hkval : -((ℓ : ℤ) + 1) - 2 * (k : ℤ) = (i : ℤ) := by simp only [hkdef]; omega
    have hS : ∀ j : ℕ, j ≤ k → suppD ℓ (-((ℓ : ℤ) + 1) - 2 * (j : ℤ)) := by
      intro j hj
      have hjk : (j : ℤ) ≤ (k : ℤ) := by exact_mod_cast hj
      exact ⟨by omega, by omega⟩
    have hx : ∀ j : ℕ, j < k → scalD ℓ (-(-((ℓ : ℤ) + 1) - 2 * (j : ℤ))) ≠ 0 := by
      intro j hj
      have hjk : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      have hpos : (0 : ℚ)
          < (ℓ : ℚ) + ((-(-((ℓ : ℤ) + 1) - 2 * (j : ℤ)) : ℤ) : ℚ) + 1 := by
        have : (0 : ℤ) < (ℓ : ℤ) + (-(-((ℓ : ℤ) + 1) - 2 * (j : ℤ))) + 1 := by omega
        exact_mod_cast this
      simp only [scalD_apply]
      intro hcon
      rw [div_eq_zero_iff] at hcon
      rcases hcon with hc | hc
      · exact absurd hc (ne_of_gt hpos)
      · norm_num at hc
    have hmem := wtChainDown (D_sl2 ℓ) hop (-((ℓ : ℤ) + 1)) hbm hgenm k hx hS
    have hidx : (⟨-((ℓ : ℤ) + 1) - 2 * (k : ℤ), hS k le_rfl⟩ : WtIdx (suppD ℓ)) = i :=
      Subtype.ext hkval
    rwa [hidx] at hmem

theorem D_fg (ℓ : ℕ) : (wtWeight (suppD ℓ) (scalD ℓ) (D_sl2 ℓ)).IsFG := by
  have hbp : suppD ℓ ((ℓ : ℤ) + 1) := ⟨by omega, by omega⟩
  have hbm : suppD ℓ (-((ℓ : ℤ) + 1)) := ⟨by omega, by omega⟩
  refine wtIsFG (D_sl2 ℓ)
    (wtGen2 (⟨(ℓ : ℤ) + 1, hbp⟩ : WtIdx (suppD ℓ)) (⟨-((ℓ : ℤ) + 1), hbm⟩ : WtIdx (suppD ℓ))) ?_
  intro N hN hop hhom i
  exact D_top_of_lowest ℓ hop hbp hbm (wtGen2_subset_left hN) (wtGen2_subset_right hN) i

/-! ## The two half-strings of `§6.2` -/

/-- **`D_ℓ⁺`**, the holomorphic half: the weights `n ≥ ℓ+1`, i.e. the positive ones.
@census none (helper) -/
noncomputable def Dpos (ℓ : ℕ) : Submodule (Qi : Type) (WtCar (suppD ℓ)) :=
  Finsupp.supported (Qi : Type) (Qi : Type) {i : WtIdx (suppD ℓ) | 0 < (i : ℤ)}

/-- **`D_ℓ⁻`**, the anti-holomorphic half: the weights `n ≤ -(ℓ+1)`.  @census none (helper) -/
noncomputable def Dneg (ℓ : ℕ) : Submodule (Qi : Type) (WtCar (suppD ℓ)) :=
  Finsupp.supported (Qi : Type) (Qi : Type) {i : WtIdx (suppD ℓ) | (i : ℤ) < 0}

theorem mem_Dpos {ℓ : ℕ} {v : WtCar (suppD ℓ)} :
    v ∈ Dpos ℓ ↔ ∀ i : WtIdx (suppD ℓ), ¬ (0 < (i : ℤ)) → v i = 0 :=
  Finsupp.mem_supported' (M := (Qi : Type)) (R := (Qi : Type)) v

theorem mem_Dneg {ℓ : ℕ} {v : WtCar (suppD ℓ)} :
    v ∈ Dneg ℓ ↔ ∀ i : WtIdx (suppD ℓ), ¬ ((i : ℤ) < 0) → v i = 0 :=
  Finsupp.mem_supported' (M := (Qi : Type)) (R := (Qi : Type)) v

/-- At `ℓ = 0` the two half-strings touch, and the only step across the gap has scalar `0` — the
wall.  @census none (helper) -/
theorem scalD_wall_of_cross {ℓ : ℕ} {a : ℤ} (hℓ0 : (ℓ : ℤ) = 0) (ha : a = 1) :
    scalD ℓ (-a) = 0 := by
  have hℓ : ℓ = 0 := by omega
  subst hℓ; subst ha
  simp [scalD_apply]

theorem Dpos_opStable (ℓ : ℕ) :
    (wtWeight (suppD ℓ) (scalD ℓ) (D_sl2 ℓ)).OpStable (Dpos ℓ) := by
  refine wtSupported_opStable (D_sl2 ℓ) _ ?_ ?_
  · intro i hi j hj
    simp only [Set.mem_setOf_eq] at hi ⊢
    exact Or.inl (by omega)
  · intro i hi j hj
    simp only [Set.mem_setOf_eq] at hi ⊢
    by_cases hjpos : 0 < (j : ℤ)
    · exact Or.inl hjpos
    refine Or.inr (scalD_wall_of_cross ?_ ?_)
    · obtain ⟨hi1, -⟩ := i.2; obtain ⟨hj1, -⟩ := j.2; omega
    · obtain ⟨hi1, -⟩ := i.2; obtain ⟨hj1, -⟩ := j.2; omega

theorem Dneg_opStable (ℓ : ℕ) :
    (wtWeight (suppD ℓ) (scalD ℓ) (D_sl2 ℓ)).OpStable (Dneg ℓ) := by
  refine wtSupported_opStable (D_sl2 ℓ) _ ?_ ?_
  · intro i hi j hj
    simp only [Set.mem_setOf_eq] at hi ⊢
    by_cases hjneg : (j : ℤ) < 0
    · exact Or.inl hjneg
    refine Or.inr ?_
    have hℓ0 : (ℓ : ℤ) = 0 := by
      obtain ⟨hi1, -⟩ := i.2; obtain ⟨hj1, -⟩ := j.2; omega
    have hi1 : (i : ℤ) = -1 := by
      obtain ⟨hi1, -⟩ := i.2; obtain ⟨hj1, -⟩ := j.2; omega
    have := scalD_wall_of_cross (ℓ := ℓ) (a := 1) hℓ0 rfl
    rwa [hi1]
  · intro i hi j hj
    simp only [Set.mem_setOf_eq] at hi ⊢
    exact Or.inl (by omega)

/-! ## The object -/

/-- **`D_ℓ = D_ℓ⁺ ⊕ D_ℓ⁻`** (`§6.2`): the sum of the holomorphic and anti-holomorphic (limits of)
discrete series with `C` acting by `λ = ℓ²`, as an object of the concrete `HC_{ℓ²}(𝔤,K)_ℚ`.

Its `ℚ[√-1]`-form is `⨁_{|n| ≥ ℓ+1, n ≡ ℓ-1 (2)} ℚ[√-1]·e_n` with `H·e_n = n·e_n`,
`X·e_n = ((ℓ+n+1)/2)·e_{n+2}` and `Y·e_n = ((ℓ-n+1)/2)·e_{n-2}`; its `ℚ`-form is the fixed space
of `c·(a·e_n) = c(a)·e_{-n}`, supplied by Galois descent (`RQ-1.13`).  Note that `c` **exchanges
the two half-strings**, which is `RQ2-6.02-C3` ("`D_ℓ^±` are complex conjugate to each other") and
is what makes `D_ℓ` — but neither summand — defined over `ℚ`.

@census    RQ2-6.02
@source    ex:discreteseries
@clauses   RQ2-6.02-H1, RQ2-6.02-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (the group is not in the tree, disclosed — finding
`V-S9G2-6(c)`; and presentation: `HC_λ(𝔤,K)_ℚ` is `HC ℓ ℚ ImagUnit.qi`
(`def:HClambdaE`, `EX-HC`; v2 line, WP-12/T5a), the object built through the `R-V2-3` bridge `HCEObj.toHC`
from the weight-line datum; 𝔼_ℚ is the native `E_E ℚ ImagUnit.qi ℓ` of `thm:EEequivalence`/`thm:cyclicEEequivalence`, re-indexed along `gelfandOfSign = gelfandOfCardTwo` (`EQNat`, `ECycNat`); the engine composite `EQFun`/`ECycFun` is isomorphic to it with identity components (`EQFun_iso_native`, `ECycFun_iso_native`, via `Compat.engineNative(Z)`), and the computations unfold to the engine's data by `rfl`; mathematical content unchanged), plus two structurally-carried clauses.  `RQ2-6.02-H1` calls `D_ℓ` "the direct sum of
the `(𝔤,K)`-modules of the holomorphic and anti-holomorphic (limits of) discrete series
**representations**"; no stage of this project formalizes `SL₂(ℝ)` as a group, its discrete series,
or a limit thereof, and S7's `HC_λ(𝔤,K)` (census `RQ-3.11`) is the `(𝔤,K)`-module category
throughout.  "The (limits of) discrete series" is therefore rendered as the `(𝔤,K)`-module the
source's own §6.2 data pins — the two half-strings `|n| ≥ ℓ+1` with the stated lowest weight
spaces, Casimir `ℓ²`, and the `ℚ`-form — which is the sense every later clause of `RQ2-6.02` uses.
This is the same reformulation `F_irreducible` and `P` disclose for `SL₂` and for parabolic
induction respectively; it was missing here and is added by the repair round.

The two clauses discharged here are otherwise carried **structurally**: `H1`'s `ℓ ≥ 0` is
the type of the argument `ℓ : ℕ` (no hypothesis is needed — unlike `F_ℓ`, `D_ℓ` exists at `ℓ = 0`,
which is exactly what `§6.2`'s second diagram is about), and `C2`'s "defined over `ℚ`" is the type
`HC ℓ ℚ ImagUnit.qi`, whose `galCompat` field is the descent datum of the `ℚ`-form.
`H1`'s second half (`D_ℓ` **is** the sum of the two half-series) is `D_decomposition`, and `C2`'s
second half (irreducibility over `ℚ`) is `D_irreducible`; both are `@census none` helpers of this
claimant in this module. -/
noncomputable def D (ℓ : ℕ) : HC ℓ ℚ ImagUnit.qi :=
  wtHC ℓ (suppD ℓ) (scalD ℓ) (D_sl2 ℓ) (D_cas ℓ) (D_symm ℓ) (D_par ℓ) (D_fg ℓ)

@[simp] theorem D_carrier (ℓ : ℕ) : (D ℓ).carrier = WtCar (suppD ℓ) := rfl

/-- `c` acts on `D_ℓ` as the coordinatewise conjugation.  @census none (helper) -/
theorem D_galAct (ℓ : ℕ) (w : WtCar (suppD ℓ)) :
    (D ℓ).galAct galConj w = wtConj (D_symm ℓ) w :=
  wtHC_galAct_galConj ℓ _ _ _ _ _ w

@[simp] theorem D_comp (ℓ : ℕ) (n : ℤ) : (D ℓ).weight.comp n = wtComp (suppD ℓ) n := rfl

/-! ## The statements of `RQ2-6.02` -/

/-- **`RQ2-6.02-C1`** — the Casimir `C` acts on `D_ℓ` as multiplication by `λ = ℓ²`, in the sharp
form (`C` **is** the scalar, not merely `C - ℓ²` nilpotent).

@census    none (auxiliary; discharges census clause `RQ2-6.02-C1`)
@source    ex:discreteseries
@clauses   RQ2-6.02-C1
@imports   none
@divergence none -/
theorem D_casimir (ℓ : ℕ) :
    (D ℓ).weight.casimir
      = (algebraMap ℚ (Qi : Type) ((ℓ : ℚ) ^ 2))
        • (1 : Module.End (Qi : Type) (D ℓ).carrier) :=
  wtCasimir_eq ℓ (D_sl2 ℓ) (D_cas ℓ)

set_option backward.isDefEq.respectTransparency.types false in
/-- **`RQ2-6.02-H1`'s second half and `RQ2-6.02-C3`** — `D_ℓ = D_ℓ⁺ ⊕ D_ℓ⁻`, the two summands are
`(𝔤,K)`-submodules **defined over `ℚ[√-1]`** (they are `ℚ[√-1]`-submodules of the `ℚ[√-1]`-form,
which is what "defined over `ℚ[√-1]`" says once `D_ℓ` itself is over `ℚ`), and `c` exchanges them
— "complex conjugate to each other".

`D_ℓ⁺` is the holomorphic half (weights `≥ ℓ+1`), `D_ℓ⁻` the anti-holomorphic one
(weights `≤ -(ℓ+1)`).

@census    none (auxiliary; discharges census clauses `RQ2-6.02-H1`, `RQ2-6.02-C3`)
@source    ex:discreteseries
@clauses   RQ2-6.02-H1, RQ2-6.02-C3
@imports   none
@divergence none -/
theorem D_decomposition (ℓ : ℕ) :
    ∃ Dp Dm : Submodule (Qi : Type) (D ℓ).carrier,
      (D ℓ).weight.OpStable Dp ∧ (D ℓ).weight.IsHomog Dp ∧
      (D ℓ).weight.OpStable Dm ∧ (D ℓ).weight.IsHomog Dm ∧
      IsCompl Dp Dm ∧
      (∀ n : ℤ, n < (ℓ : ℤ) + 1 → (D ℓ).weight.comp n ⊓ Dp = ⊥) ∧
      (∀ n : ℤ, -((ℓ : ℤ) + 1) < n → (D ℓ).weight.comp n ⊓ Dm = ⊥) ∧
      (∀ v : (D ℓ).carrier, v ∈ Dp ↔ (D ℓ).galAct galConj v ∈ Dm) := by
  have hconjEq : ∀ w : WtCar (suppD ℓ),
      ((D ℓ).galAct galConj w : WtCar (suppD ℓ)) = wtConj (D_symm ℓ) w := fun w => D_galAct ℓ w
  refine ⟨Dpos ℓ, Dneg ℓ, Dpos_opStable ℓ, wtSupported_isHomog (D_sl2 ℓ) _,
    Dneg_opStable ℓ, wtSupported_isHomog (D_sl2 ℓ) _, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · -- the two index sets are disjoint
    exact Finsupp.disjoint_supported_supported (by
      rw [Set.disjoint_left]
      rintro i hi hj
      simp only [Set.mem_setOf_eq] at hi hj
      omega)
  · -- and they cover: `D_ℓ` has no weight `0`, since every weight has `|n| ≥ ℓ+1 ≥ 1`
    refine Finsupp.codisjoint_supported_supported ?_
    intro u hu1 hu2 i _
    have hi2 := i.2
    obtain ⟨h1, -⟩ := hi2
    by_cases hpos : 0 < (i : ℤ)
    · exact hu1 hpos
    · have hneg : (i : ℤ) < 0 := by omega
      exact hu2 hneg
  · -- `D_ℓ⁺` meets no weight line below `ℓ+1`
    intro n hn
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    by_cases hS : suppD ℓ n
    · obtain ⟨a, rfl⟩ := exists_single_of_mem_wtComp (S := suppD ℓ) hS hv1
      have hz := mem_Dpos.mp hv2 (⟨n, hS⟩ : WtIdx (suppD ℓ))
        (by obtain ⟨h1, -⟩ := hS; show ¬ (0 < n); omega)
      rw [Finsupp.single_eq_same] at hz
      exact Finsupp.single_eq_zero.mpr hz
    · exact eq_zero_of_mem_wtComp_not_mem (S := suppD ℓ) hS hv1
  · -- `D_ℓ⁻` meets no weight line above `-(ℓ+1)`
    intro n hn
    rw [Submodule.eq_bot_iff]
    rintro v ⟨hv1, hv2⟩
    by_cases hS : suppD ℓ n
    · obtain ⟨a, rfl⟩ := exists_single_of_mem_wtComp (S := suppD ℓ) hS hv1
      have hz := mem_Dneg.mp hv2 (⟨n, hS⟩ : WtIdx (suppD ℓ))
        (by obtain ⟨h1, -⟩ := hS; show ¬ (n < 0); omega)
      rw [Finsupp.single_eq_same] at hz
      exact Finsupp.single_eq_zero.mpr hz
    · exact eq_zero_of_mem_wtComp_not_mem (S := suppD ℓ) hS hv1
  · -- `c` exchanges the two halves — `RQ2-6.02-C3`, "complex conjugate to each other"
    intro v
    constructor
    · intro hv
      refine mem_Dneg.mpr fun j hj => ?_
      rw [hconjEq, wtConj_apply,
        mem_Dpos.mp hv (wtNeg (D_symm ℓ) j) (by rw [wtNeg_val]; omega), map_zero]
    · intro hv
      refine mem_Dpos.mpr fun i hi => ?_
      have hz := mem_Dneg.mp hv (wtNeg (D_symm ℓ) i) (by rw [wtNeg_val]; omega)
      rw [hconjEq, wtConj_apply, wtNeg_wtNeg] at hz
      exact galConj.injective (hz.trans (map_zero galConj).symm)

/-- **`RQ2-6.02-C2`, second half** — `D_ℓ` is **irreducible over `ℚ`**: no `(𝔤,K)`-submodule of its
`ℚ[√-1]`-form that is also stable under the conjugation `c` (equivalently, no `ℚ`-subspace of the
`ℚ`-form that is a `(𝔤_ℚ,K_ℚ)`-submodule, by Galois descent, `RQ-1.13`) is proper and non-zero —
even though it is **reducible** over `ℚ[√-1]`, where it splits as `D_ℓ⁺ ⊕ D_ℓ⁻`
(`D_decomposition`).  The contrast is the point of the clause, so both halves are stated.

@census    none (auxiliary; discharges census clause `RQ2-6.02-C2`)
@source    ex:discreteseries
@clauses   RQ2-6.02-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (the `ℚ`-form, disclosed).  "Irreducible over `ℚ`" is stated on
the `ℚ[√-1]`-form as "`c`-stable + `(𝔤,K)`-stable ⟹ `⊥` or `⊤`" rather than on `setup.baseChange`'s
source, because that is the presentation of `HC_λ(𝔤,K)_ℚ` this project uses throughout (ruling
`R-S8-6`, v1 `Gelfand/Category.lean`'s `HCQObj` `@divergence`); by Galois descent the two are the same
lattice of submodules. -/
theorem D_irreducible (ℓ : ℕ) :
    ((⊥ : Submodule (Qi : Type) (D ℓ).carrier) ≠ ⊤ ∧
      ∀ N : Submodule (Qi : Type) (D ℓ).carrier,
        (D ℓ).weight.OpStable N → (D ℓ).weight.IsHomog N →
          (∀ v ∈ N, (D ℓ).galAct galConj v ∈ N) → N = ⊥ ∨ N = ⊤) ∧
    (1 ≤ ℓ → ∃ N : Submodule (Qi : Type) (D ℓ).carrier,
      (D ℓ).weight.OpStable N ∧ (D ℓ).weight.IsHomog N ∧ N ≠ ⊥ ∧ N ≠ ⊤) := by
  have hbp : suppD ℓ ((ℓ : ℤ) + 1) := ⟨by omega, by omega⟩
  have hbm : suppD ℓ (-((ℓ : ℤ) + 1)) := ⟨by omega, by omega⟩
  have hconjSingle : ∀ (j : WtIdx (suppD ℓ)) (a : (Qi : Type)),
      (D ℓ).galAct galConj (Finsupp.single j a)
        = Finsupp.single (wtNeg (D_symm ℓ) j) (galConj a) :=
    fun j a => (D_galAct ℓ _).trans (wtConj_single (D_symm ℓ) j a)
  refine ⟨⟨wtBot_ne_top ⟨(ℓ : ℤ) + 1, hbp⟩, ?_⟩, ?_⟩
  · -- irreducible over `ℚ`: a `c`-stable `(𝔤,K)`-submodule meets **both** half-strings
    intro N hop hhom hc
    by_cases hN : N = ⊥
    · exact Or.inl hN
    refine Or.inr ?_
    obtain ⟨i, hi⟩ := wtExists_single_mem (D_sl2 ℓ) hhom hN
    -- `c` carries a basis vector to the mirror basis vector, so `N` meets the other half too
    have hcp : ∀ j : WtIdx (suppD ℓ), Finsupp.single j (1 : (Qi : Type)) ∈ N →
        Finsupp.single (wtNeg (D_symm ℓ) j) (1 : (Qi : Type)) ∈ N := by
      intro j hj
      have hcj := hc _ hj
      rwa [hconjSingle, map_one] at hcj
    have hboth : Finsupp.single (⟨(ℓ : ℤ) + 1, hbp⟩ : WtIdx (suppD ℓ)) (1 : (Qi : Type)) ∈ N ∧
        Finsupp.single (⟨-((ℓ : ℤ) + 1), hbm⟩ : WtIdx (suppD ℓ)) (1 : (Qi : Type)) ∈ N := by
      obtain ⟨h1, h2⟩ := i.2
      rcases h1 with hup | hdn
      · -- `i ≥ ℓ+1`: descend to the holomorphic lowest weight vector, then mirror
        set k : ℕ := (((i : ℤ) - ((ℓ : ℤ) + 1)) / 2).toNat with hkdef
        have hkval : (i : ℤ) - 2 * (k : ℤ) = (ℓ : ℤ) + 1 := by simp only [hkdef]; omega
        have hS : ∀ j : ℕ, j ≤ k → suppD ℓ ((i : ℤ) - 2 * (j : ℤ)) := by
          intro j hj
          have hjk : (j : ℤ) ≤ (k : ℤ) := by exact_mod_cast hj
          exact ⟨by omega, by omega⟩
        have hx : ∀ j : ℕ, j < k → scalD ℓ (-((i : ℤ) - 2 * (j : ℤ))) ≠ 0 := by
          intro j hj
          have hjk : (j : ℤ) < (k : ℤ) := by exact_mod_cast hj
          exact scalD_ne_zero (by omega)
        have hmem := wtChainDown (D_sl2 ℓ) hop (i : ℤ) i.2 hi k hx hS
        rw [show (⟨(i : ℤ) - 2 * (k : ℤ), hS k le_rfl⟩ : WtIdx (suppD ℓ))
          = ⟨(ℓ : ℤ) + 1, hbp⟩ from Subtype.ext hkval] at hmem
        exact ⟨hmem, hcp _ hmem⟩
      · -- `i ≤ -(ℓ+1)`: climb to the anti-holomorphic lowest weight vector, then mirror
        set k : ℕ := ((-((ℓ : ℤ) + 1) - (i : ℤ)) / 2).toNat with hkdef
        have hkval : (i : ℤ) + 2 * (k : ℤ) = -((ℓ : ℤ) + 1) := by simp only [hkdef]; omega
        have hS : ∀ j : ℕ, j ≤ k → suppD ℓ ((i : ℤ) + 2 * (j : ℤ)) := by
          intro j hj
          have hjk : (j : ℤ) ≤ (k : ℤ) := by exact_mod_cast hj
          exact ⟨by omega, by omega⟩
        have hx : ∀ j : ℕ, j < k → scalD ℓ ((i : ℤ) + 2 * (j : ℤ)) ≠ 0 := by
          intro j hj
          have hjk : (j : ℤ) < (k : ℤ) := by exact_mod_cast hj
          exact scalD_ne_zero (by omega)
        have hmem := wtChainUp (D_sl2 ℓ) hop (i : ℤ) i.2 hi k hx hS
        rw [show (⟨(i : ℤ) + 2 * (k : ℤ), hS k le_rfl⟩ : WtIdx (suppD ℓ))
          = ⟨-((ℓ : ℤ) + 1), hbm⟩ from Subtype.ext hkval] at hmem
        exact ⟨hcp _ hmem, hmem⟩
    exact wtTop_of_single N (D_top_of_lowest ℓ hop hbp hbm hboth.1 hboth.2)
  · -- but reducible over `ℚ[√-1]`: the holomorphic half is a proper non-zero submodule
    intro hℓ
    refine ⟨Dpos ℓ, Dpos_opStable ℓ, wtSupported_isHomog (D_sl2 ℓ) _, ?_, ?_⟩
    · intro hbot
      have hmem : Finsupp.single (⟨(ℓ : ℤ) + 1, hbp⟩ : WtIdx (suppD ℓ)) (1 : (Qi : Type))
          ∈ Dpos ℓ :=
        Finsupp.single_mem_supported _ _ (by simp only [Set.mem_setOf_eq]; omega)
      exact (Finsupp.single_ne_zero.mpr one_ne_zero)
        ((Submodule.eq_bot_iff (Dpos ℓ)).mp hbot _ hmem)
    · intro htop
      have hmem : Finsupp.single (⟨-((ℓ : ℤ) + 1), hbm⟩ : WtIdx (suppD ℓ)) (1 : (Qi : Type))
          ∈ Dpos ℓ := by rw [htop]; trivial
      have hz := mem_Dpos.mp hmem (⟨-((ℓ : ℤ) + 1), hbm⟩ : WtIdx (suppD ℓ))
        (by show ¬ (0 < -((ℓ : ℤ) + 1)); omega)
      rw [Finsupp.single_eq_same] at hz
      exact one_ne_zero hz

/-- **`RQ2-6.02-C4`** — the lowest weight spaces `D_ℓ^±[χ_{±(ℓ+1)}]` are one-dimensional (every
`ℓ ≥ 0`), and — **for `ℓ ≥ 1`** — `D_ℓ[χ_{±(ℓ-1)}] = 0`, together with the vanishing of everything
strictly inside the two walls, which is what `RQ2-6.02-C5`'s `M(⋆) = 0` rests on.

**Where the substantive `ℓ = 0` content lives.** Not in this theorem: `PLAN.md` §S9 §5's "`ℓ ≥ 1`
**and** `ℓ = 0`" is met by `D_zero_quiverRep_eq` and `D_zero_speciesRep_eq` (clauses `RQ2-6.02-C9`,
`-C11`), which state the cyclic-quiver diagram and its species representation against S8's own
`E_CycFunctor`. The last conjunct here only keeps this theorem from asserting something false at
`ℓ = 0`; it is a guard, not the `ℓ = 0` statement.

The `ℓ ≥ 1` qualification is the census's, not this stage's: `RQ2-6.02-C4` was **qualified
post-freeze at census revision r11** (2026-09-06, `census-v1.7 → v1.8`) precisely because the
printed sentence's second half is **false at `ℓ = 0`** — there `±(ℓ-1) = ∓1` and `D_0[χ_{∓1}]` are
exactly the one-dimensional lowest `K`-types the first half asserts. The last conjunct below states
what is *true* at `ℓ = 0`, so that `PLAN.md` §S9 §5's "`ℓ ≥ 1` **and** `ℓ = 0`" is met without
instantiating a false clause.

@census    none (auxiliary; discharges census clause `RQ2-6.02-C4`, as qualified at r11)
@source    ex:discreteseries
@clauses   RQ2-6.02-C4
@imports   none
@divergence none.  The clause is stated exactly as `census-v1.8` qualifies it — the `1 ≤ ℓ` guard
below is the census's own restriction, not a weakening introduced here; the unqualified reading is
struck in that row's `notes`. -/
theorem D_weightSpaces (ℓ : ℕ) :
    Module.finrank ImagUnit.qi.L ((D ℓ).weight.comp ((ℓ : ℤ) + 1)) = 1 ∧
    Module.finrank ImagUnit.qi.L ((D ℓ).weight.comp (-((ℓ : ℤ) + 1))) = 1 ∧
    (1 ≤ ℓ →
      (D ℓ).weight.comp ((ℓ : ℤ) - 1) = ⊥ ∧
      (D ℓ).weight.comp (-((ℓ : ℤ) - 1)) = ⊥ ∧
      ∀ n : ℤ, -((ℓ : ℤ) + 1) < n → n < (ℓ : ℤ) + 1 → (D ℓ).weight.comp n = ⊥) ∧
    (∀ v : (D ℓ).carrier, v ∈ (D ℓ).weight.comp ((ℓ : ℤ) + 1) →
      (D ℓ).weight.Y v = 0) ∧
    (∀ v : (D ℓ).carrier, v ∈ (D ℓ).weight.comp (-((ℓ : ℤ) + 1)) →
      (D ℓ).weight.X v = 0) ∧
    -- What is true at `ℓ = 0`, where the clause's second half is false: `D_0[χ_{∓1}]` ARE the
    -- one-dimensional lowest `K`-types.  `comp 0 = ⊥` is stated for completeness of the picture at
    -- the one weight the clause's `±(ℓ-1) = ∓1` reading would otherwise be about; it is not extra
    -- content, since at `ℓ = 0` EVERY even weight vanishes already by the central character
    -- (`wtCentralCharacter`, `RQ-3.03-C3`), `0` among them.
    (ℓ = 0 → (D 0).weight.comp 0 = ⊥ ∧
      Module.finrank ImagUnit.qi.L ((D 0).weight.comp 1) = 1 ∧
      Module.finrank ImagUnit.qi.L ((D 0).weight.comp (-1)) = 1) := by
  have hbp : suppD ℓ ((ℓ : ℤ) + 1) := ⟨by omega, by omega⟩
  have hbm : suppD ℓ (-((ℓ : ℤ) + 1)) := ⟨by omega, by omega⟩
  -- the lowering scalar out of `M_{ℓ+1}` and the raising scalar out of `M_{-(ℓ+1)}` are the same
  -- rational number `x(-(ℓ+1)) = (ℓ - (ℓ+1) + 1)/2`, and it is `0` — the two walls of `§6.2`
  have hwall : scalD ℓ (-((ℓ : ℤ) + 1)) = 0 := by
    simp only [scalD_apply]
    push_cast
    ring
  refine ⟨wtComp_finrank hbp, wtComp_finrank hbm, ?_, ?_, ?_, ?_⟩
  · intro hℓ
    refine ⟨wtComp_eq_bot (S := suppD ℓ) ?_, wtComp_eq_bot (S := suppD ℓ) ?_, ?_⟩
    · rintro ⟨h1, h2⟩; omega
    · rintro ⟨h1, h2⟩; omega
    · intro n hn1 hn2
      exact wtComp_eq_bot (S := suppD ℓ) (by rintro ⟨h1, h2⟩; omega)
  · -- `Y` annihilates `M_{ℓ+1}`: the lower wall
    intro v hv
    rw [D_comp] at hv
    obtain ⟨a, rfl⟩ := exists_single_of_mem_wtComp (S := suppD ℓ) hbp hv
    show wtY (suppD ℓ) (scalD ℓ) _ = 0
    by_cases h : suppD ℓ (((ℓ : ℤ) + 1) - 2)
    · rw [wtY_single_eq (S := suppD ℓ) (x := scalD ℓ)
        (i := ⟨(ℓ : ℤ) + 1, hbp⟩) (j := ⟨((ℓ : ℤ) + 1) - 2, h⟩) rfl a]
      show Finsupp.single _ (((scalD ℓ (-((ℓ : ℤ) + 1)) : ℚ) : (Qi : Type)) * a) = 0
      rw [hwall]
      simp
    · exact wtY_single_eq_zero (S := suppD ℓ) (x := scalD ℓ) h a
  · -- `X` annihilates `M_{-(ℓ+1)}`: the upper wall of the anti-holomorphic half
    intro v hv
    rw [D_comp] at hv
    obtain ⟨a, rfl⟩ := exists_single_of_mem_wtComp (S := suppD ℓ) hbm hv
    show wtX (suppD ℓ) (scalD ℓ) _ = 0
    by_cases h : suppD ℓ ((-((ℓ : ℤ) + 1)) + 2)
    · rw [wtX_single_eq (S := suppD ℓ) (x := scalD ℓ)
        (i := ⟨-((ℓ : ℤ) + 1), hbm⟩) (j := ⟨(-((ℓ : ℤ) + 1)) + 2, h⟩) rfl a]
      show Finsupp.single _ (((scalD ℓ (-((ℓ : ℤ) + 1)) : ℚ) : (Qi : Type)) * a) = 0
      rw [hwall]
      simp
    · exact wtX_single_eq_zero (S := suppD ℓ) (x := scalD ℓ) h a
  · -- the `ℓ = 0` guard (the verifier's probe `P6`)
    rintro rfl
    exact ⟨wtComp_of_not_mem (S := suppD 0) (n := 0) (by decide),
      wtComp_finrank (S := suppD 0) (n := 1) (by decide),
      wtComp_finrank (S := suppD 0) (n := -1) (by decide)⟩

/-- **`RQ2-6.02-C5`, `C6`, `C7`, `C8`** — the displayed `ℚ`-rational Gelfand-quiver diagram of
`§6.2` at `ℓ ≥ 1`:

```
  ℚ[√-1]  ⇄  0  ⇄  ℚ[√-1]
     ↓ c      ↓ 0     ↓ c
  ℚ[√-1]  ⇄  0  ⇄  ℚ[√-1]
```

`M(⋆) = 0` — **for `ℓ ≥ 1`**, which is how `RQ2-6.02-C5` reads after its post-freeze qualification
at census revision r11 (at `ℓ = 0`, `M(⋆) := M[χ_{-(ℓ-1)}] = M[χ_1] = M(+)` is one-dimensional, not
`0`, and the source itself passes to the cyclic quiver there — `D_zero_quiverRep_eq`) — so every
`φ_{a_±}`, `φ_{b_±}` is zero (`C5`) and `φ_⋆ = 0` (half of `C7`); `M(±)` are
one-dimensional (`C8`); `T₋` acts as the identity on `M(−) = D_ℓ[χ_{-(ℓ+1)}]`, so the unipotent
stabilization is already trivial (`C6`); and the vertical maps `φ_±` are `c` (the other half of
`C7`), stated basis-freely, in the disjoint union `⊔_v M(v)`, as "some non-zero vector of `M(−)`
is carried to a vector of `M(+)` by `φ_-`" together with the one-dimensionality of both.

@census    none (auxiliary; discharges census clauses `RQ2-6.02-C5` (as qualified at r11), `C6`,
           `C7`, `C8`)
@source    ex:discreteseries
@clauses   RQ2-6.02-C5, RQ2-6.02-C6, RQ2-6.02-C7, RQ2-6.02-C8
@imports   none
@divergence JUSTIFIED_REFORMULATION (the vertical arrows' `c`-labels, disclosed).  As for `F_ℓ`,
the label `c` presupposes the identification `M(±) ≅ ℚ[√-1]` the display itself makes and the
source never pins.

**What the `∃ b ≠ 0` conjunct does and does not carry** (finding `V-S9G2-2`): `φ_-` is a
`c`-semilinear additive bijection `M(−) → M(+)` by S2's `Rep` axioms (`RQ-1.08-C2`–`C4`) alone, so
once both spaces are one-dimensional that conjunct is *derivable* from the adjacent `finrank = 1`
conjuncts and pins the display's isomorphism class, no more.  `RQ2-6.02-C7`'s `φ_± = c` is carried
instead by the `T₋ = 𝟏` conjunct — clause `RQ2-6.02-C6`'s own operator — through S8's definition
`φ_{v,c} = c ∘ φ^{(∞)}_v`; and `C7`'s `φ_⋆ = 0` is the `M(⋆) = 0` conjunct, since a map out of the
zero space is zero. -/
theorem D_quiverRep_eq (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∀ m : (EQObj hℓ (D ℓ)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 1), m = 0) ∧
    Module.finrank (Qi : Type)
      ((EQObj hℓ (D ℓ)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 0)) = 1 ∧
    Module.finrank (Qi : Type)
      ((EQObj hℓ (D ℓ)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 2)) = 1 ∧
    (∀ e : GQ.E, (EQObj hℓ (D ℓ)).toRep.φEdge e = 0) ∧
    (∃ b : (EQObj hℓ (D ℓ)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 0), b ≠ 0 ∧
      (EQObj hℓ (D ℓ)).toRep.φ galConj (vtxQ SqrtNegOneExt.qi.card_gal 0) b ≠ 0) ∧
    (∀ v : (D ℓ).carrier, v ∈ (D ℓ).weight.comp (-((ℓ : ℤ) + 1)) →
      Split.tMinus (qiSetupOf (D ℓ)) v = v) := by
  have hℓz : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
  have hSm : suppD ℓ (-((ℓ : ℤ) + 1)) := ⟨by omega, by omega⟩
  have hSp : suppD ℓ ((ℓ : ℤ) + 1) := ⟨by omega, by omega⟩
  -- `M(⋆) = 0` at `ℓ ≥ 1`: the weight `-(ℓ-1)` lies strictly inside the gap `|n| < ℓ+1`
  have hNs : ¬ suppD ℓ (-((ℓ : ℤ) - 1)) := by rintro ⟨h1, h2⟩; omega
  have hz1 : ∀ m : (EQObj hℓ (D ℓ)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 1), m = 0 :=
    fun m => Subtype.ext (eq_zero_of_mem_wtComp_not_mem (S := suppD ℓ) hNs m.2)
  have hcas : (qiSetupOf (D ℓ)).weight.casimir
      = (algebraMap ℚ (Qi : Type) ((ℓ : ℚ) ^ 2)) • 1 := wtCasimir_eq ℓ (D_sl2 ℓ) (D_cas ℓ)
  refine ⟨hz1, wtComp_finrank hSm, wtComp_finrank hSp, ?_, ?_, ?_⟩
  · -- every displayed horizontal map is zero, because `⋆` is one of its two ends
    have hcases : ∀ e : Fin 4, (EQObj hℓ (D ℓ)).toRep.φEdge e = 0 := by
      intro e
      fin_cases e
      · exact LinearMap.ext fun _ => hz1 _
      · -- `φ_{b_-} = Y` out of `M(⋆) = 0`
        refine LinearMap.ext fun m => Subtype.ext ?_
        show (D ℓ).weight.Y m.1 = 0
        rw [eq_zero_of_mem_wtComp_not_mem (S := suppD ℓ) hNs m.2]
        exact LinearMap.map_zero _
      · exact LinearMap.ext fun _ => hz1 _
      · -- `φ_{b_+} = X ∘ X⋆` out of `M(⋆) = 0`
        refine LinearMap.ext fun m => Subtype.ext ?_
        show (D ℓ).weight.X (Split.xStar (qiSetupOf (D ℓ)) m.1) = 0
        have hx : Split.xStar (qiSetupOf (D ℓ)) (0 : WtCar (suppD ℓ)) = 0 := LinearMap.map_zero _
        rw [eq_zero_of_mem_wtComp_not_mem (S := suppD ℓ) hNs m.2, hx]
        exact LinearMap.map_zero _
    exact fun e => hcases e
  · -- `M(−)` is non-zero and `φ_{−,c}` is injective, so the displayed vertical map is non-zero
    exact exists_ne_zero_map_ne_zero
      (e := (⟨Finsupp.single (⟨-((ℓ : ℤ) + 1), hSm⟩ : WtIdx (suppD ℓ)) (1 : (Qi : Type)),
        by exact single_mem_wtComp (⟨-((ℓ : ℤ) + 1), hSm⟩ : WtIdx (suppD ℓ)) 1⟩ :
          (EQObj hℓ (D ℓ)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 0)))
      (by exact wtComp_elt_ne_zero hSm)
      ((EQObj hℓ (D ℓ)).toRep.φ galConj (vtxQ SqrtNegOneExt.qi.card_gal 0))
  · -- `T₋ = 𝟏` on `M(−)` (`RQ2-6.02-C6`), through the scalar Casimir
    exact fun v _ => tMinus_eq_one_of_casimir_scalar (qiSetupOf (D ℓ)) hℓ hcas v

set_option backward.isDefEq.respectTransparency.types false in
/-- **`RQ2-6.02-C10`** — the displayed étale `ℚ`-species representation of `§6.2` at `ℓ ≥ 1`:
`W_{⋆} = 0`, `W_{±} = M(+)^{G_+} = ℚ[√-1]` (two-dimensional over `ℚ`, one-dimensional over the
node field `ℚ[√-1]`), all maps zero.

@census    none (auxiliary; discharges census clause `RQ2-6.02-C10`)
@source    ex:discreteseries
@clauses   RQ2-6.02-C10
@imports   none
@divergence none -/
theorem D_speciesRep_eq (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∀ w : ((RationalQuiver.FFunctor GQ).obj
      (EQObj hℓ (D ℓ))).W starNode, w = 0) ∧
    Module.finrank ℚ (((RationalQuiver.FFunctor GQ).obj
      (EQObj hℓ (D ℓ))).W pmNode) = 2 ∧
    (∀ i j : GQ.toSpecies.I,
      ((RationalQuiver.FFunctor GQ).obj
        (EQObj hℓ (D ℓ))).f i j = 0) := by
  obtain ⟨hz1, hfr0, hfr2, -, -, -⟩ := D_quiverRep_eq ℓ hℓ
  have hstar : Subsingleton ((EQObj hℓ (D ℓ)).toRep.M (GQ.vertexRep starNode)) := by
    rw [vertexRep_starNode]
    exact ⟨fun a b => (hz1 a).trans (hz1 b).symm⟩
  have hWstar := subsingleton_W_of_subsingleton (EQObj hℓ (D ℓ)) starNode hstar
  refine ⟨fun w => hWstar.elim w 0, ?_, ?_⟩
  · rw [finrank_W_pm]
    rcases vertexRep_pmNode with h | h <;> rw [h]
    · rw [hfr0]
    · rw [hfr2]
  · intro i j
    rcases node_cases i with rfl | rfl
    · exact f_zero_of_source _ _ _ hWstar
    · rcases node_cases j with rfl | rfl
      · exact f_zero_of_target _ _ _ hWstar
      · exact f_zero_of_edges _ _ _ (M_diag_subsingleton pmNode)

/-- **`RQ2-6.02-C9`** — at `ℓ = 0` "the Gelfand quiver degenerates to the cyclic quiver", and the
displayed two-node diagram is

```
  ℚ[√-1]  ⇄  ℚ[√-1]
     ↓ c        ↓ c
  ℚ[√-1]  ⇄  ℚ[√-1]
```

i.e. `𝔼_ℚ(D_0)` for S8's **cyclic** comparison functor (`RQ-5.07`'s `E_CycFunctor`, at S8's own
proved specification `E_Cyc_spec`): both vertex spaces `M(∓) = D_0[χ_{∓1}]` are one-dimensional
over `ℚ[√-1]`, both edge maps `a = X`, `b = Y` are zero, and the vertical maps are the (non-zero,
`c`-semilinear) `φ_{v,c}`.

@census    none (auxiliary; discharges census clause `RQ2-6.02-C9`)
@source    ex:discreteseries
@clauses   RQ2-6.02-C9
@imports   none
@divergence JUSTIFIED_REFORMULATION (the vertical arrows' `c`-labels, as in `D_quiverRep_eq`, and
with the same `V-S9G2-2` reading of the `∃ b ≠ 0` conjunct: it pins the display's isomorphism class
and is derivable from the two `finrank = 1` conjuncts plus S2's `Rep` axioms, rather than carrying
`φ_{v,c} = c` itself).  At `ℓ = 0` the stabilizations are trivial by S8's `E_Cyc_spec` — the
Casimir product defining `T_±` is empty and `γ_⋆(0) = 1` — so there is no triviality conjunct to
state here and none is claimed. -/
theorem D_zero_quiverRep_eq :
    Module.finrank (Qi : Type)
      ((ECycObj (D 0)).toRep.M (vtxC SqrtNegOneExt.qi.card_gal 0)) = 1 ∧
    Module.finrank (Qi : Type)
      ((ECycObj (D 0)).toRep.M (vtxC SqrtNegOneExt.qi.card_gal 1)) = 1 ∧
    (∀ e : CQ.E, (ECycObj (D 0)).toRep.φEdge e = 0) ∧
    (∃ b : (ECycObj (D 0)).toRep.M (vtxC SqrtNegOneExt.qi.card_gal 0), b ≠ 0 ∧
      (ECycObj (D 0)).toRep.φ galConj (vtxC SqrtNegOneExt.qi.card_gal 0) b ≠ 0) := by
  have hSm : suppD 0 (-1 : ℤ) := by decide
  have hSp : suppD 0 (1 : ℤ) := by decide
  -- at `ℓ = 0` both edge scalars are the same rational number, `x(-1) = (0 - 1 + 1)/2 = 0`
  have hwall : scalD 0 (-1 : ℤ) = 0 := by simp [scalD_apply]
  refine ⟨wtComp_finrank hSm, wtComp_finrank hSp, ?_, ?_⟩
  · have hcases : ∀ e : Fin 2, (ECycObj (D 0)).toRep.φEdge e = 0 := by
      intro e
      fin_cases e
      · -- `a = X : M_{-1} → M_1`
        refine wtRestrict_eq_zero (S := suppD 0) hSm (m := (1 : ℤ))
          (fun _ hv => Split.x_mem (Q := (qiSetupOf (D 0))) (m := (-1 : ℤ)) (n := (1 : ℤ))
            (by decide) hv) fun a => ?_
        show wtX (suppD 0) (scalD 0) (Finsupp.single _ a) = 0
        rw [wtX_single_eq (S := suppD 0) (x := scalD 0) (i := ⟨(-1 : ℤ), hSm⟩)
          (j := ⟨(1 : ℤ), hSp⟩) (by norm_num) a]
        show Finsupp.single _ (((scalD 0 (-1 : ℤ) : ℚ) : (Qi : Type)) * a) = 0
        rw [hwall, Rat.cast_zero, zero_mul, Finsupp.single_zero]
      · -- `b = Y : M_1 → M_{-1}`
        refine wtRestrict_eq_zero (S := suppD 0) hSp (m := (-1 : ℤ))
          (fun _ hv => Split.y_mem (Q := (qiSetupOf (D 0))) (m := (1 : ℤ)) (n := (-1 : ℤ))
            (by decide) hv) fun a => ?_
        show wtY (suppD 0) (scalD 0) (Finsupp.single _ a) = 0
        rw [wtY_single_eq (S := suppD 0) (x := scalD 0) (i := ⟨(1 : ℤ), hSp⟩)
          (j := ⟨(-1 : ℤ), hSm⟩) (by norm_num) a]
        show Finsupp.single _ (((scalD 0 (-(1 : ℤ)) : ℚ) : (Qi : Type)) * a) = 0
        rw [hwall, Rat.cast_zero, zero_mul, Finsupp.single_zero]
    exact fun e => hcases e
  · exact exists_ne_zero_map_ne_zero
      (e := (⟨Finsupp.single (⟨(-1 : ℤ), hSm⟩ : WtIdx (suppD 0)) (1 : (Qi : Type)),
        by exact single_mem_wtComp (⟨(-1 : ℤ), hSm⟩ : WtIdx (suppD 0)) 1⟩ :
          (ECycObj (D 0)).toRep.M (vtxC SqrtNegOneExt.qi.card_gal 0)))
      (by exact wtComp_elt_ne_zero hSm)
      ((ECycObj (D 0)).toRep.φ galConj (vtxC SqrtNegOneExt.qi.card_gal 0))

set_option backward.isDefEq.respectTransparency.types false in
/-- **`RQ2-6.02-C11`** — the `ℓ = 0` étale `ℚ`-species representation: the species of the cyclic
quiver has **one** node, with field `ℚ[√-1]` and twisted bimodule `ℚ[√-1]^{twisted}`
(`ex:cyclic`), and the representation is a one-dimensional `ℚ[√-1]`-space — two-dimensional over
`ℚ` — with **zero** structure map.

@census    none (auxiliary; discharges census clause `RQ2-6.02-C11`)
@source    ex:discreteseries
@clauses   RQ2-6.02-C11
@imports   none
@divergence none -/
theorem D_zero_speciesRep_eq :
    Module.finrank ℚ (((RationalQuiver.FFunctor CQ).obj
      (ECycObj (D 0))).W cycNode) = 2 ∧
    (∀ i j : CQ.toSpecies.I,
      ((RationalQuiver.FFunctor CQ).obj
        (ECycObj (D 0))).f i j = 0) := by
  obtain ⟨hfr0, hfr1, hedge, -⟩ := D_zero_quiverRep_eq
  refine ⟨?_, ?_⟩
  · rw [finrank_W, stabField_cyc, IntermediateField.finrank_top', Qi.finrank_eq_two]
    rcases vertexRep_cycNode with h | h <;> rw [h]
    · rw [hfr0]
    · rw [hfr1]
  · intro i j
    exact edgeDescentOf_eq_zero_of_edges (ECycObj (D 0)).toRep i j hedge

end RationalQuivers.Examples
