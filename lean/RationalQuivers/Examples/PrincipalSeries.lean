import RationalQuivers.Examples.FiniteDimensional
import RationalQuivers.Examples.DiscreteSeries

/-!
# §6.3 — the principal series `P_{ℓ,ε}` and its dual `P^∨_{ℓ,ε}`

Formalizes §6.3 of `latex/rational_quivers.tex` (census `RQ2-6.03`).

## Main definitions / results
* `RationalQuivers.Examples.P` — `P_{ℓ,ε} ∈ HC_{ℓ²}(𝔤,K)_ℚ`, a term of `HC ℓ ℚ ImagUnit.qi`.
* `RationalQuivers.Examples.Pdual` — `P^∨_{ℓ,ε}`.
* `RationalQuivers.Examples.P_exactSequence` — `0 → D_ℓ → P_{ℓ,ε} → F_ℓ → 0`, **non-split**.
* `RationalQuivers.Examples.Pdual_exactSequence` — `0 → F_ℓ → P^∨_{ℓ,ε} → D_ℓ → 0`.
* `RationalQuivers.Examples.P_weightSpaces` — all relevant `K`-type spaces are one-dimensional.
* `RationalQuivers.Examples.P_quiverRep_eq` / `Pdual_quiverRep_eq` — the two displayed diagrams.
* `RationalQuivers.Examples.P_speciesRep_eq` / `Pdual_speciesRep_eq` — the two species pictures,
  as corrected at census revision r11 (`AN-43`).

## Implementation notes

Both objects are `Examples/Basic.lean`'s weight-line module on the **whole** string of the right
parity, `S = {n : n ≡ ℓ - 1 (mod 2)}` — no wall at all, which is exactly the statement that
`P_{ℓ,ε}` has all four `K`-type spaces `χ_{±(ℓ±1)}` non-zero (`RQ2-6.03-C3`).  They differ only in
the raising scalar, and the two choices are precisely `D_ℓ`'s and `F_ℓ`'s:

* `P_{ℓ,ε}`: `x(n) = (ℓ + n + 1)/2` — `D_ℓ`'s normalization, which vanishes at `n = -(ℓ+1)` and
  whose mirror vanishes at `n = ℓ+1`, so the span of `{|n| ≥ ℓ+1}` is a **submodule**: this is
  `0 → D_ℓ → P_{ℓ,ε} → F_ℓ → 0`.
* `P^∨_{ℓ,ε}`: `x(n) = (ℓ - n - 1)/2` — `F_ℓ`'s normalization, so the span of `{|n| ≤ ℓ-1}` is a
  submodule: this is `0 → F_ℓ → P^∨_{ℓ,ε} → D_ℓ → 0`.

`ε` is **determined** by `ℓ`: `ε ∈ {0,1}` with `ℓ ≢ ε (mod 2)` leaves exactly one value.  It is
nevertheless carried as an explicit argument, together with its two hypotheses, so that clause
`RQ2-6.03-H1` is structurally present (`CONVENTIONS.md` §3) rather than merely remarked on.

**`RQ2-6.03-H2` is not constructed.**  The source *defines* `P_{ℓ,ε} := I(ℓ,ε)` in **normalized**
parabolic induction (census r18, FA-31 / A-4): the `K`-finite smooth `f` with
`f([[a,b],[0,a⁻¹]] g) = sgn(a)^ε |a|^{ℓ+1} f(g)`, i.e. induction from `sgn^ε |·|^ℓ` twisted by the
square root of the modulus character. *(Amended 2026-10-03, docstring-only `R-PROC-4` amendment of
frozen S9, coordinator ruling `R-FR-9`, final-release WP-16b, stale item R12: this sentence read
"induced from `sgn^ε |·|^{ℓ-1}` of the standard Borel", the superseded unnormalized definition.)*
No stage of this project formalizes parabolic induction, or `SL₂(ℝ)` as a group at all; what the source then *uses* about `P_{ℓ,ε}` is
exactly `C2` (the non-split extension) together with `C3` (the `K`-type dimensions), and those two
determine the object up to isomorphism in `HC_{ℓ²}(𝔤,K)_ℚ`.  The object below is therefore pinned
by that characterization rather than by the induction; disclosed in `P`'s `@divergence`.

## `F-S9-1` — the §6.3 repair this module is stated against (closed)

The statements below are stated against **§6.3 as corrected**, i.e. `latex/rational_quivers.tex`
at census revision **r11** / tag **`census-v1.8`**, not against the text as first printed.

§6.3 as printed was internally inconsistent: its quiver displays print `φ_{a_±} = 0` and
`φ_{b_±} = "="`, while the prose above them called the maps `M(±) → M(⋆)` "non-zero isomorphisms"
and the maps `M(⋆) → M(±)` "zero", and the two species captions attached the trace picture to
`P_{ℓ,ε}` and the inclusion to `P^∨`.  The deciding clause is `RQ2-6.03-C2`, the exact sequence
`0 → D_ℓ → P_{ℓ,ε} → F_ℓ → 0` with `D_ℓ` a **submodule**: `M(±) = M[χ_{±(ℓ+1)}] ⊆ D_ℓ` and
`M(⋆) = M[χ_{-(ℓ-1)}]` meets `D_ℓ` in `0`, and `φ_{a_-}` is `X` restricted to `M(−)`, so its image
lies in `D_ℓ ⊓ M(⋆) = 0`.  Hence `φ_{a_±} = 0` is forced with no normalization freedom, and
non-splitness forces `φ_{b_±} ≠ 0`; dually for `P^∨`.  So `-C2 ⟹ ¬-C6`-as-printed, and the
displays are the correct half.

Raised as finding `F-S9-1` (S9 implementer, 2026-09-06), independently re-derived twice, **ruled by
the author** ("the swap is right, apply it") and applied at census revision r11: see
`workflow/reports/AUTHOR-QUEUE.md` `AN-43` (CLOSED) and `workflow/census/ATTESTATION.md` §5/§7.10/
§15.  The corrected clauses `RQ2-6.03-C6`, `-C7`, `-C10`, `-C11` are what the statements below
render; nothing here diverges from them.
-/

namespace RationalQuivers.Examples

open RationalQuivers.HC RationalQuivers.Gelfand CategoryTheory
open RationalQuivers.Gelfand.RationalStructure (gelfandQ vtxQ edgeQ RepNilQ)
open RationalQuivers.Gelfand.Cyclic (cyclicQ vtxC edgeC RepNilCycQ)

/-! ## The datum -/

/-- The weights of `P_{ℓ,ε}` and of `P^∨_{ℓ,ε}`: the whole string `n ≡ ℓ - 1 (mod 2)`.
@census none (helper) -/
abbrev suppP (ℓ : ℕ) (n : ℤ) : Prop := (n - ((ℓ : ℤ) - 1)) % 2 = 0

theorem suppP_sub2 {ℓ : ℕ} {n : ℤ} (hn : suppP ℓ n) : suppP ℓ (n - 2) := by
  simp only [suppP] at *; omega

theorem suppP_add2 {ℓ : ℕ} {n : ℤ} (hn : suppP ℓ n) : suppP ℓ (n + 2) := by
  simp only [suppP] at *; omega

theorem P_symm (ℓ : ℕ) : WtSymm (suppP ℓ) := by
  intro n hn; simp only [suppP] at *; omega

theorem P_par (ℓ : ℕ) : WtPar ℓ (suppP ℓ) := fun _ h => h

/-! ### `P_{ℓ,ε}`: `D_ℓ`'s normalization on the whole string -/

theorem P_sl2 (ℓ : ℕ) : WtSl2 (suppP ℓ) (scalD ℓ) := by
  intro n hn
  rw [if_pos (suppP_sub2 hn), if_pos (suppP_add2 hn), scalD_apply, scalD_apply, scalD_apply,
    scalD_apply]
  push_cast
  ring

theorem P_cas (ℓ : ℕ) : WtCas ℓ (suppP ℓ) (scalD ℓ) := by
  intro n hn
  rw [if_pos (suppP_sub2 hn), scalD_apply, scalD_apply]
  push_cast
  ring

theorem P_fg (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : (wtWeight (suppP ℓ) (scalD ℓ) (P_sl2 ℓ)).IsFG := by
  have hb : suppP ℓ ((ℓ : ℤ) - 1) := by simp only [suppP]; omega
  refine wtIsFG (P_sl2 ℓ) (wtGen (⟨(ℓ : ℤ) - 1, hb⟩ : WtIdx (suppP ℓ))) ?_
  intro N hN hop hhom i
  have hgen := wtGen_subset hN
  have hi : suppP ℓ (i : ℤ) := i.2
  simp only [suppP] at hi
  by_cases hup : ((ℓ : ℤ) - 1) ≤ (i : ℤ)
  · set k : ℕ := (((i : ℤ) - ((ℓ : ℤ) - 1)) / 2).toNat with hkdef
    have hkval : ((ℓ : ℤ) - 1) + 2 * (k : ℤ) = (i : ℤ) := by simp only [hkdef]; omega
    have hS : ∀ j : ℕ, j ≤ k → suppP ℓ (((ℓ : ℤ) - 1) + 2 * (j : ℤ)) := by
      intro j _; simp only [suppP]; omega
    have hx : ∀ j : ℕ, j < k → scalD ℓ (((ℓ : ℤ) - 1) + 2 * (j : ℤ)) ≠ 0 := by
      intro j _
      have hjn : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      have hpos : (0 : ℚ) < (ℓ : ℚ) + ((((ℓ : ℤ) - 1) + 2 * (j : ℤ) : ℤ) : ℚ) + 1 := by
        have : (0 : ℤ) < (ℓ : ℤ) + (((ℓ : ℤ) - 1) + 2 * (j : ℤ)) + 1 := by omega
        exact_mod_cast this
      simp only [scalD_apply]
      intro hcon
      rw [div_eq_zero_iff] at hcon
      rcases hcon with hc | hc
      · exact absurd hc (ne_of_gt hpos)
      · norm_num at hc
    have hmem := wtChainUp (P_sl2 ℓ) hop ((ℓ : ℤ) - 1) hb hgen k hx hS
    rwa [show (⟨((ℓ : ℤ) - 1) + 2 * (k : ℤ), hS k le_rfl⟩ : WtIdx (suppP ℓ)) = i from
      Subtype.ext hkval] at hmem
  · rw [not_le] at hup
    set k : ℕ := ((((ℓ : ℤ) - 1) - (i : ℤ)) / 2).toNat with hkdef
    have hkval : ((ℓ : ℤ) - 1) - 2 * (k : ℤ) = (i : ℤ) := by simp only [hkdef]; omega
    have hS : ∀ j : ℕ, j ≤ k → suppP ℓ (((ℓ : ℤ) - 1) - 2 * (j : ℤ)) := by
      intro j _; simp only [suppP]; omega
    have hx : ∀ j : ℕ, j < k → scalD ℓ (-(((ℓ : ℤ) - 1) - 2 * (j : ℤ))) ≠ 0 := by
      intro j _
      have hjn : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      have hpos : (0 : ℚ) < (ℓ : ℚ) + ((-(((ℓ : ℤ) - 1) - 2 * (j : ℤ)) : ℤ) : ℚ) + 1 := by
        have : (0 : ℤ) < (ℓ : ℤ) + (-(((ℓ : ℤ) - 1) - 2 * (j : ℤ))) + 1 := by omega
        exact_mod_cast this
      simp only [scalD_apply]
      intro hcon
      rw [div_eq_zero_iff] at hcon
      rcases hcon with hc | hc
      · exact absurd hc (ne_of_gt hpos)
      · norm_num at hc
    have hmem := wtChainDown (P_sl2 ℓ) hop ((ℓ : ℤ) - 1) hb hgen k hx hS
    rwa [show (⟨((ℓ : ℤ) - 1) - 2 * (k : ℤ), hS k le_rfl⟩ : WtIdx (suppP ℓ)) = i from
      Subtype.ext hkval] at hmem

/-! ### `P^∨_{ℓ,ε}`: `F_ℓ`'s normalization on the whole string -/

theorem Pdual_sl2 (ℓ : ℕ) : WtSl2 (suppP ℓ) (scalF ℓ) := by
  intro n hn
  rw [if_pos (suppP_sub2 hn), if_pos (suppP_add2 hn), scalF_apply, scalF_apply, scalF_apply,
    scalF_apply]
  push_cast
  ring

theorem Pdual_cas (ℓ : ℕ) : WtCas ℓ (suppP ℓ) (scalF ℓ) := by
  intro n hn
  rw [if_pos (suppP_sub2 hn), scalF_apply, scalF_apply]
  push_cast
  ring

theorem Pdual_fg (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : (wtWeight (suppP ℓ) (scalF ℓ) (Pdual_sl2 ℓ)).IsFG := by
  have hbp : suppP ℓ ((ℓ : ℤ) + 1) := by simp only [suppP]; omega
  have hbm : suppP ℓ (-((ℓ : ℤ) + 1)) := by simp only [suppP]; omega
  refine wtIsFG (Pdual_sl2 ℓ)
    (wtGen2 (⟨(ℓ : ℤ) + 1, hbp⟩ : WtIdx (suppP ℓ)) (⟨-((ℓ : ℤ) + 1), hbm⟩ : WtIdx (suppP ℓ))) ?_
  intro N hN hop hhom i
  have hgenp := wtGen2_subset_left hN
  have hgenm := wtGen2_subset_right hN
  have hi : suppP ℓ (i : ℤ) := i.2
  simp only [suppP] at hi
  by_cases hup : ((ℓ : ℤ) + 1) ≤ (i : ℤ)
  · -- above the upper wall: climb from `e_{ℓ+1}`
    set k : ℕ := (((i : ℤ) - ((ℓ : ℤ) + 1)) / 2).toNat with hkdef
    have hkval : ((ℓ : ℤ) + 1) + 2 * (k : ℤ) = (i : ℤ) := by simp only [hkdef]; omega
    have hS : ∀ j : ℕ, j ≤ k → suppP ℓ (((ℓ : ℤ) + 1) + 2 * (j : ℤ)) := by
      intro j _; simp only [suppP]; omega
    have hx : ∀ j : ℕ, j < k → scalF ℓ (((ℓ : ℤ) + 1) + 2 * (j : ℤ)) ≠ 0 := by
      intro j _
      have hjn : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
      have hneg : ((ℓ : ℚ) - ((((ℓ : ℤ) + 1) + 2 * (j : ℤ) : ℤ) : ℚ) - 1) < 0 := by
        have : ((ℓ : ℤ) - (((ℓ : ℤ) + 1) + 2 * (j : ℤ)) - 1) < 0 := by omega
        exact_mod_cast this
      simp only [scalF_apply]
      intro hcon
      rw [div_eq_zero_iff] at hcon
      rcases hcon with hc | hc
      · exact absurd hc (ne_of_lt hneg)
      · norm_num at hc
    have hmem := wtChainUp (Pdual_sl2 ℓ) hop ((ℓ : ℤ) + 1) hbp hgenp k hx hS
    rwa [show (⟨((ℓ : ℤ) + 1) + 2 * (k : ℤ), hS k le_rfl⟩ : WtIdx (suppP ℓ)) = i from
      Subtype.ext hkval] at hmem
  · rw [not_le] at hup
    by_cases hdn : (i : ℤ) ≤ -((ℓ : ℤ) + 1)
    · -- below the lower wall: descend from `e_{-(ℓ+1)}`
      set k : ℕ := ((-((ℓ : ℤ) + 1) - (i : ℤ)) / 2).toNat with hkdef
      have hkval : -((ℓ : ℤ) + 1) - 2 * (k : ℤ) = (i : ℤ) := by simp only [hkdef]; omega
      have hS : ∀ j : ℕ, j ≤ k → suppP ℓ (-((ℓ : ℤ) + 1) - 2 * (j : ℤ)) := by
        intro j _; simp only [suppP]; omega
      have hx : ∀ j : ℕ, j < k → scalF ℓ (-(-((ℓ : ℤ) + 1) - 2 * (j : ℤ))) ≠ 0 := by
        intro j _
        have hjn : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg j
        have hneg : ((ℓ : ℚ) - ((-(-((ℓ : ℤ) + 1) - 2 * (j : ℤ)) : ℤ) : ℚ) - 1) < 0 := by
          have : ((ℓ : ℤ) - (-(-((ℓ : ℤ) + 1) - 2 * (j : ℤ))) - 1) < 0 := by omega
          exact_mod_cast this
        simp only [scalF_apply]
        intro hcon
        rw [div_eq_zero_iff] at hcon
        rcases hcon with hc | hc
        · exact absurd hc (ne_of_lt hneg)
        · norm_num at hc
      have hmem := wtChainDown (Pdual_sl2 ℓ) hop (-((ℓ : ℤ) + 1)) hbm hgenm k hx hS
      rwa [show (⟨-((ℓ : ℤ) + 1) - 2 * (k : ℤ), hS k le_rfl⟩ : WtIdx (suppP ℓ)) = i from
        Subtype.ext hkval] at hmem
    · rw [not_le] at hdn
      -- strictly between the walls: descend from `e_{ℓ+1}`, stopping before `Y` dies at `1-ℓ`
      set k : ℕ := ((((ℓ : ℤ) + 1) - (i : ℤ)) / 2).toNat with hkdef
      have hkval : ((ℓ : ℤ) + 1) - 2 * (k : ℤ) = (i : ℤ) := by simp only [hkdef]; omega
      have hkle : (k : ℤ) ≤ (ℓ : ℤ) := by simp only [hkdef]; omega
      have hS : ∀ j : ℕ, j ≤ k → suppP ℓ (((ℓ : ℤ) + 1) - 2 * (j : ℤ)) := by
        intro j _; simp only [suppP]; omega
      have hx : ∀ j : ℕ, j < k → scalF ℓ (-(((ℓ : ℤ) + 1) - 2 * (j : ℤ))) ≠ 0 := by
        intro j hj
        have hjk : (j : ℤ) < (k : ℤ) := by exact_mod_cast hj
        have hpos : (0 : ℚ) < ((ℓ : ℚ) - ((-(((ℓ : ℤ) + 1) - 2 * (j : ℤ)) : ℤ) : ℚ) - 1) := by
          have : (0 : ℤ) < ((ℓ : ℤ) - (-(((ℓ : ℤ) + 1) - 2 * (j : ℤ))) - 1) := by omega
          exact_mod_cast this
        simp only [scalF_apply]
        intro hcon
        rw [div_eq_zero_iff] at hcon
        rcases hcon with hc | hc
        · exact absurd hc (ne_of_gt hpos)
        · norm_num at hc
      have hmem := wtChainDown (Pdual_sl2 ℓ) hop ((ℓ : ℤ) + 1) hbp hgenp k hx hS
      rwa [show (⟨((ℓ : ℤ) + 1) - 2 * (k : ℤ), hS k le_rfl⟩ : WtIdx (suppP ℓ)) = i from
        Subtype.ext hkval] at hmem

/-! ## The two objects -/

/-- **`P_{ℓ,ε}`** (`§6.3`): the principal series representation, as an object of the concrete
`HC_{ℓ²}(𝔤,K)_ℚ`.

Its `ℚ[√-1]`-form is `⨁_{n ≡ ℓ-1 (2)} ℚ[√-1]·e_n` — the whole string, with **no** wall — carrying
`D_ℓ`'s scalars `X·e_n = ((ℓ+n+1)/2)·e_{n+2}`, `Y·e_n = ((ℓ-n+1)/2)·e_{n-2}`, so that the span of
`{|n| ≥ ℓ+1}` is a submodule isomorphic to `D_ℓ` with quotient `F_ℓ`.  Its `ℚ`-form is the fixed
space of `c·(a·e_n) = c(a)·e_{-n}` (Galois descent, `RQ-1.13`).

@census    RQ2-6.03
@source    ex:principalseries
@clauses   RQ2-6.03-H1, RQ2-6.03-H2, RQ2-6.03-C1
@imports   none
@divergence JUSTIFIED_REFORMULATION (`H2`, the induction datum, disclosed; and presentation: `HC_λ(𝔤,K)_ℚ` is `HC ℓ ℚ ImagUnit.qi`
(`def:HClambdaE`, `EX-HC`; v2 line, WP-12/T5a), the object built through the `R-V2-3` bridge `HCEObj.toHC`
from the weight-line datum; 𝔼_ℚ is the native `E_E ℚ ImagUnit.qi ℓ` of `thm:EEequivalence`/`thm:cyclicEEequivalence`, re-indexed along `gelfandOfSign = gelfandOfCardTwo` (`EQNat`, `ECycNat`); the engine composite `EQFun`/`ECycFun` is isomorphic to it with identity components (`EQFun_iso_native`, `ECycFun_iso_native`, via `Compat.engineNative(Z)`), and the computations unfold to the engine's data by `rfl`; mathematical content unchanged).  `H1` and `C1` are
carried structurally — `H1`'s `ℓ > 0`, `ε ∈ {0,1}` and `ℓ ≢ ε (mod 2)` are the explicit arguments
`hℓ`, `hε`, `hpe` (`CONVENTIONS.md` §3; `ε` is in fact *determined* by them, and is carried anyway
so the clause is visible in the signature), and `C1`'s "defined over `ℚ`" is the type
`HC ℓ ℚ ImagUnit.qi`, whose `galCompat` field is the descent datum of the `ℚ`-form.  `H2` — "`P_{ℓ,ε} := I(ℓ,ε)`
in normalized parabolic induction" (census r18; until 2026-10-03, `R-FR-9`, this paragraph quoted the
superseded "induced from the character `sgn^ε |·|^{ℓ-1}` of the standard Borel") — is
**not** rendered as a construction: no stage of this project formalizes parabolic induction, or
`SL₂(ℝ)` as a group.  The object is instead pinned by the characterization the source itself uses
downstream, namely `C2` (the non-split extension `0 → D_ℓ → P_{ℓ,ε} → F_ℓ → 0`,
`P_exactSequence`) together with `C3` (all four relevant `K`-type spaces one-dimensional,
`P_weightSpaces`), which determine an object of `HC_{ℓ²}(𝔤,K)_ℚ` up to isomorphism.  Nothing
`§6.3` asserts about `P_{ℓ,ε}` uses the induction beyond those two. -/
noncomputable def P (ℓ : ℕ) (ε : ℕ) (hℓ : 1 ≤ ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpe : (ℓ : ℤ) % 2 ≠ (ε : ℤ) % 2) : HC ℓ ℚ ImagUnit.qi :=
  wtHC ℓ (suppP ℓ) (scalD ℓ) (P_sl2 ℓ) (P_cas ℓ) (P_symm ℓ) (P_par ℓ) (P_fg ℓ hℓ)

/-- **`P^∨_{ℓ,ε}`** (`§6.3`): the dual principal series, the same string with `F_ℓ`'s scalars, so
that the span of `{|n| ≤ ℓ-1}` is a submodule isomorphic to `F_ℓ` with quotient `D_ℓ`.

@census    none (auxiliary; the second object of `RQ2-6.03`, whose clause `RQ2-6.03-C4` names it)
@source    ex:principalseries
@clauses   RQ2-6.03-H1
@imports   none
@divergence WEAKENED_OR_PARTIAL (parallel to `P`'s `H2` disclosure; added 2026-10-03, docstring-only
`R-PROC-4` amendment of frozen S9, coordinator ruling `R-FR-9`, final-release WP-16b,
`MISMATCH-TRIAGE.md` row #18; until then `none`). The source (census r18, clause `RQ2-6.03-C4`)
defines `P^∨_{ℓ,ε} := I(-ℓ,ε)`, the **contragredient** of `P_{ℓ,ε}`, and realizes `F_ℓ` inside it
by the functions `f(g) = p(γ,δ)` for homogeneous polynomials `p` of degree `ℓ-1` in the bottom row
of `g`. None of this is formalized: parabolic induction, contragredience and the polynomial model
all need `SL₂(ℝ)` as a group. This object is pinned instead by its weight-line model with `F_ℓ`'s
scalars, by the exact sequence `0 → F_ℓ → P^∨ → D_ℓ → 0` (`Pdual_exactSequence`) and by its
`K`-types. -/
noncomputable def Pdual (ℓ : ℕ) (ε : ℕ) (hℓ : 1 ≤ ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpe : (ℓ : ℤ) % 2 ≠ (ε : ℤ) % 2) : HC ℓ ℚ ImagUnit.qi :=
  wtHC ℓ (suppP ℓ) (scalF ℓ) (Pdual_sl2 ℓ) (Pdual_cas ℓ) (P_symm ℓ) (P_par ℓ) (Pdual_fg ℓ hℓ)

/-- `c` acts on `P_{ℓ,ε}` as the coordinatewise conjugation.  @census none (helper) -/
theorem P_galAct (ℓ ε : ℕ) (hℓ : 1 ≤ ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpe : (ℓ : ℤ) % 2 ≠ (ε : ℤ) % 2) (w : WtCar (suppP ℓ)) :
    (P ℓ ε hℓ hε hpe).galAct galConj w = wtConj (P_symm ℓ) w :=
  wtHC_galAct_galConj ℓ _ _ _ _ _ w

/-- `c` acts on `P^∨_{ℓ,ε}` as the coordinatewise conjugation.  @census none (helper) -/
theorem Pdual_galAct (ℓ ε : ℕ) (hℓ : 1 ≤ ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpe : (ℓ : ℤ) % 2 ≠ (ε : ℤ) % 2) (w : WtCar (suppP ℓ)) :
    (Pdual ℓ ε hℓ hε hpe).galAct galConj w = wtConj (P_symm ℓ) w :=
  wtHC_galAct_galConj ℓ _ _ _ _ _ w

@[simp] theorem P_carrier (ℓ ε : ℕ) (hℓ : 1 ≤ ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpe : (ℓ : ℤ) % 2 ≠ (ε : ℤ) % 2) :
    (P ℓ ε hℓ hε hpe).carrier = WtCar (suppP ℓ) := rfl

@[simp] theorem Pdual_carrier (ℓ ε : ℕ) (hℓ : 1 ≤ ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpe : (ℓ : ℤ) % 2 ≠ (ε : ℤ) % 2) :
    (Pdual ℓ ε hℓ hε hpe).carrier = WtCar (suppP ℓ) := rfl

/-! ## Weight-diagonal morphisms

`§6.3`'s two exact sequences relate three objects built on **different** scalar normalizations —
`P_{ℓ,ε}` and `D_ℓ` carry `scalD`, `P^∨_{ℓ,ε}` and `F_ℓ` carry `scalF` — so neither map is an
inclusion of basis vectors on the nose: each is `e_n ↦ c(n)·e_n` for a rational family `c` fixed
by the two intertwining identities.  This section builds that map once.  @census none (helper) -/

/-- `e_n ↦ c(n)·e_n`, from one weight line to another, read as `0` at a weight outside the target's
support.  @census none (helper) -/
noncomputable def wtDiag (S T : ℤ → Prop) [DecidablePred S] [DecidablePred T] (c : ℤ → ℚ) :
    WtCar S →ₗ[(Qi : Type)] WtCar T :=
  Finsupp.lsum ℕ fun i : WtIdx S =>
    if h : T (i : ℤ) then ((c (i : ℤ) : (Qi : Type))) • Finsupp.lsingle (⟨(i : ℤ), h⟩ : WtIdx T)
    else 0

variable {S T : ℤ → Prop} [DecidablePred S] [DecidablePred T] {c : ℤ → ℚ}

theorem wtDiag_single (i : WtIdx S) (a : (Qi : Type)) :
    wtDiag S T c (Finsupp.single i a)
      = if h : T (i : ℤ) then
          Finsupp.single (⟨(i : ℤ), h⟩ : WtIdx T) (((c (i : ℤ) : ℚ) : (Qi : Type)) * a)
        else 0 := by
  rw [wtDiag, Finsupp.lsum_single]
  by_cases h : T (i : ℤ)
  · rw [dif_pos h, dif_pos h, LinearMap.smul_apply, Finsupp.lsingle_apply, Finsupp.smul_single,
      smul_eq_mul]
  · rw [dif_neg h, dif_neg h, LinearMap.zero_apply]

/-- The map coefficientwise.  @census none (helper) -/
theorem wtDiag_apply (v : WtCar S) (j : WtIdx T) :
    wtDiag S T c v j
      = if h : S (j : ℤ) then ((c (j : ℤ) : ℚ) : (Qi : Type)) * v ⟨(j : ℤ), h⟩ else 0 := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => by_cases h : S (j : ℤ) <;> simp [h]
  | add f g hf hg =>
      rw [map_add, Finsupp.add_apply, hf, hg]
      by_cases h : S (j : ℤ) <;> simp [h, mul_add]
  | single i a =>
      rw [wtDiag_single]
      by_cases hij : (i : ℤ) = (j : ℤ)
      · have hiT : T (i : ℤ) := hij ▸ j.2
        have hjS : S (j : ℤ) := hij ▸ i.2
        rw [dif_pos hiT, dif_pos hjS, Finsupp.single_apply, Finsupp.single_apply,
          if_pos (show (⟨(i : ℤ), hiT⟩ : WtIdx T) = j from Subtype.ext hij),
          if_pos (show i = (⟨(j : ℤ), hjS⟩ : WtIdx S) from Subtype.ext hij), hij]
      · have hne1 : ∀ hiT : T (i : ℤ), (⟨(i : ℤ), hiT⟩ : WtIdx T) ≠ j :=
          fun _ hh => hij (congrArg Subtype.val hh)
        have hne2 : ∀ hjS : S (j : ℤ), i ≠ (⟨(j : ℤ), hjS⟩ : WtIdx S) :=
          fun _ hh => hij (congrArg Subtype.val hh)
        by_cases hjS : S (j : ℤ)
        · rw [dif_pos hjS, Finsupp.single_apply, if_neg (hne2 hjS), mul_zero]
          by_cases hiT : T (i : ℤ)
          · rw [dif_pos hiT, Finsupp.single_apply, if_neg (hne1 hiT)]
          · rw [dif_neg hiT, Finsupp.zero_apply]
        · rw [dif_neg hjS]
          by_cases hiT : T (i : ℤ)
          · rw [dif_pos hiT, Finsupp.single_apply, if_neg (hne1 hiT)]
          · rw [dif_neg hiT, Finsupp.zero_apply]

theorem wtDiag_comp {n : ℤ} {v : WtCar S} (hv : v ∈ wtComp S n) :
    wtDiag S T c v ∈ wtComp T n := by
  by_cases hn : S n
  · obtain ⟨a, rfl⟩ := exists_single_of_mem_wtComp (S := S) hn hv
    rw [wtDiag_single]
    by_cases hT : T ((⟨n, hn⟩ : WtIdx S) : ℤ)
    · rw [dif_pos hT]; exact single_mem_wtComp (⟨n, hT⟩ : WtIdx T) _
    · rw [dif_neg hT]; exact Submodule.zero_mem _
  · rw [eq_zero_of_mem_wtComp_not_mem (S := S) hn hv, map_zero]; exact Submodule.zero_mem _

theorem wtDiag_H (v : WtCar S) : wtDiag S T c (wtH S v) = wtH T (wtDiag S T c v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | single i a =>
      rw [wtH_single, wtDiag_single, wtDiag_single]
      by_cases h : T (i : ℤ)
      · rw [dif_pos h, dif_pos h, wtH_single]
        congr 1
        ring
      · rw [dif_neg h, dif_neg h, map_zero]

theorem wtDiag_X {x y : ℤ → ℚ}
    (hX : ∀ n : ℤ, S n →
      (if S (n + 2) then (if T (n + 2) then c (n + 2) * x n else 0) else 0)
        = (if T n then (if T (n + 2) then y n * c n else 0) else 0))
    (v : WtCar S) : wtDiag S T c (wtX S x v) = wtX T y (wtDiag S T c v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | single i a =>
      have key := hX (i : ℤ) i.2
      rw [wtX_single, wtDiag_single]
      by_cases hS2 : S ((i : ℤ) + 2)
      · rw [if_pos hS2] at key
        rw [dif_pos hS2, wtDiag_single]
        by_cases hT2 : T ((i : ℤ) + 2)
        · rw [if_pos hT2] at key
          rw [dif_pos (show T (((⟨(i : ℤ) + 2, hS2⟩ : WtIdx S)) : ℤ) from hT2)]
          by_cases hT : T (i : ℤ)
          · rw [if_pos hT, if_pos hT2] at key
            rw [dif_pos hT, wtX_single,
              dif_pos (show T (((⟨(i : ℤ), hT⟩ : WtIdx T) : ℤ) + 2) from hT2)]
            refine congrArg₂ Finsupp.single (Subtype.ext rfl) ?_
            rw [← mul_assoc, ← mul_assoc, ← Rat.cast_mul, ← Rat.cast_mul, key]
          · rw [if_neg hT] at key
            rw [dif_neg hT, map_zero, ← mul_assoc, ← Rat.cast_mul, key, Rat.cast_zero,
              zero_mul, Finsupp.single_zero]
        · rw [if_neg hT2] at key
          rw [dif_neg (show ¬ T (((⟨(i : ℤ) + 2, hS2⟩ : WtIdx S)) : ℤ) from hT2)]
          by_cases hT : T (i : ℤ)
          · rw [dif_pos hT, wtX_single,
              dif_neg (show ¬ T (((⟨(i : ℤ), hT⟩ : WtIdx T) : ℤ) + 2) from hT2)]
          · rw [dif_neg hT, map_zero]
      · rw [if_neg hS2] at key
        rw [dif_neg hS2, map_zero]
        by_cases hT : T (i : ℤ)
        · rw [if_pos hT] at key
          rw [dif_pos hT, wtX_single]
          by_cases hT2 : T ((i : ℤ) + 2)
          · rw [if_pos hT2] at key
            rw [dif_pos (show T (((⟨(i : ℤ), hT⟩ : WtIdx T) : ℤ) + 2) from hT2),
              ← mul_assoc, ← Rat.cast_mul, ← key, Rat.cast_zero, zero_mul, Finsupp.single_zero]
          · rw [dif_neg (show ¬ T (((⟨(i : ℤ), hT⟩ : WtIdx T) : ℤ) + 2) from hT2)]
        · rw [dif_neg hT, map_zero]

theorem wtDiag_Y {x y : ℤ → ℚ}
    (hY : ∀ n : ℤ, S n →
      (if S (n - 2) then (if T (n - 2) then c (n - 2) * x (-n) else 0) else 0)
        = (if T n then (if T (n - 2) then y (-n) * c n else 0) else 0))
    (v : WtCar S) : wtDiag S T c (wtY S x v) = wtY T y (wtDiag S T c v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | single i a =>
      have key := hY (i : ℤ) i.2
      rw [wtY_single, wtDiag_single]
      by_cases hS2 : S ((i : ℤ) - 2)
      · rw [if_pos hS2] at key
        rw [dif_pos hS2, wtDiag_single]
        by_cases hT2 : T ((i : ℤ) - 2)
        · rw [if_pos hT2] at key
          rw [dif_pos (show T (((⟨(i : ℤ) - 2, hS2⟩ : WtIdx S)) : ℤ) from hT2)]
          by_cases hT : T (i : ℤ)
          · rw [if_pos hT, if_pos hT2] at key
            rw [dif_pos hT, wtY_single,
              dif_pos (show T (((⟨(i : ℤ), hT⟩ : WtIdx T) : ℤ) - 2) from hT2)]
            refine congrArg₂ Finsupp.single (Subtype.ext rfl) ?_
            rw [← mul_assoc, ← mul_assoc, ← Rat.cast_mul, ← Rat.cast_mul, key]
          · rw [if_neg hT] at key
            rw [dif_neg hT, map_zero, ← mul_assoc, ← Rat.cast_mul, key, Rat.cast_zero,
              zero_mul, Finsupp.single_zero]
        · rw [if_neg hT2] at key
          rw [dif_neg (show ¬ T (((⟨(i : ℤ) - 2, hS2⟩ : WtIdx S)) : ℤ) from hT2)]
          by_cases hT : T (i : ℤ)
          · rw [dif_pos hT, wtY_single,
              dif_neg (show ¬ T (((⟨(i : ℤ), hT⟩ : WtIdx T) : ℤ) - 2) from hT2)]
          · rw [dif_neg hT, map_zero]
      · rw [if_neg hS2] at key
        rw [dif_neg hS2, map_zero]
        by_cases hT : T (i : ℤ)
        · rw [if_pos hT] at key
          rw [dif_pos hT, wtY_single]
          by_cases hT2 : T ((i : ℤ) - 2)
          · rw [if_pos hT2] at key
            rw [dif_pos (show T (((⟨(i : ℤ), hT⟩ : WtIdx T) : ℤ) - 2) from hT2),
              ← mul_assoc, ← Rat.cast_mul, ← key, Rat.cast_zero, zero_mul, Finsupp.single_zero]
          · rw [dif_neg (show ¬ T (((⟨(i : ℤ), hT⟩ : WtIdx T) : ℤ) - 2) from hT2)]
        · rw [dif_neg hT, map_zero]

theorem wtDiag_conj (hsymS : WtSymm S) (hsymT : WtSymm T) (hc : ∀ n : ℤ, c (-n) = c n)
    (v : WtCar S) :
    wtDiag S T c (wtConj hsymS v) = wtConj hsymT (wtDiag S T c v) := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add, map_add]
  | single i a =>
      rw [wtConj_single, wtDiag_single, wtDiag_single]
      by_cases h : T (i : ℤ)
      · have h' : T ((wtNeg hsymS i : WtIdx S) : ℤ) := by rw [wtNeg_val]; exact hsymT _ h
        rw [dif_pos h, dif_pos h', wtConj_single]
        refine congrArg₂ Finsupp.single (Subtype.ext (by simp)) ?_
        rw [map_mul, map_ratCast, wtNeg_val, hc]
      · have h' : ¬ T ((wtNeg hsymS i : WtIdx S) : ℤ) := by
          rw [wtNeg_val]
          intro hcon
          exact h (by simpa using hsymT _ hcon)
        rw [dif_neg h, dif_neg h', map_zero]

theorem wtDiag_injective (hST : ∀ n : ℤ, S n → T n) (hc : ∀ n : ℤ, S n → c n ≠ 0) :
    Function.Injective (wtDiag S T c) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  refine Finsupp.ext fun i => ?_
  have hT : T (i : ℤ) := hST _ i.2
  have hcoe := congrArg (fun w : WtCar T => w (⟨(i : ℤ), hT⟩ : WtIdx T)) hv
  simp only [Finsupp.zero_apply] at hcoe
  rw [wtDiag_apply, dif_pos (show S (((⟨(i : ℤ), hT⟩ : WtIdx T)) : ℤ) from i.2)] at hcoe
  have hcne : ((c (i : ℤ) : ℚ) : (Qi : Type)) ≠ 0 := Rat.cast_ne_zero.mpr (hc _ i.2)
  have hz := (mul_eq_zero.mp hcoe).resolve_left hcne
  rwa [show (⟨(i : ℤ), i.2⟩ : WtIdx S) = i from Subtype.ext rfl] at hz

theorem wtDiag_surjective (hTS : ∀ n : ℤ, T n → S n) (hc : ∀ n : ℤ, T n → c n ≠ 0) :
    Function.Surjective (wtDiag S T c) := by
  intro w
  induction w using Finsupp.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add f g hf hg =>
      obtain ⟨u, hu⟩ := hf
      obtain ⟨v, hv⟩ := hg
      exact ⟨u + v, by rw [map_add, hu, hv]⟩
  | single j b =>
      have hcne : ((c (j : ℤ) : ℚ) : (Qi : Type)) ≠ 0 := Rat.cast_ne_zero.mpr (hc _ j.2)
      refine ⟨Finsupp.single (⟨(j : ℤ), hTS _ j.2⟩ : WtIdx S)
        (((c (j : ℤ) : ℚ) : (Qi : Type))⁻¹ * b), ?_⟩
      rw [wtDiag_single,
        dif_pos (show T (((⟨(j : ℤ), hTS _ j.2⟩ : WtIdx S)) : ℤ) from j.2),
        ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]

theorem wtDiag_ker (hc : ∀ n : ℤ, T n → S n → c n ≠ 0) :
    LinearMap.ker (wtDiag S T c)
      = Finsupp.supported (Qi : Type) (Qi : Type) {i : WtIdx S | ¬ T (i : ℤ)} := by
  refine le_antisymm (fun v hv => ?_) (fun v hv => ?_)
  · rw [LinearMap.mem_ker] at hv
    refine (Finsupp.mem_supported' (M := (Qi : Type)) (R := (Qi : Type)) v).mpr fun i hi => ?_
    have hT : T (i : ℤ) := not_not.mp hi
    have hcoe := congrArg (fun w : WtCar T => w (⟨(i : ℤ), hT⟩ : WtIdx T)) hv
    simp only [Finsupp.zero_apply] at hcoe
    rw [wtDiag_apply, dif_pos (show S (((⟨(i : ℤ), hT⟩ : WtIdx T)) : ℤ) from i.2)] at hcoe
    have hcne : ((c (i : ℤ) : ℚ) : (Qi : Type)) ≠ 0 := Rat.cast_ne_zero.mpr (hc _ hT i.2)
    have hz := (mul_eq_zero.mp hcoe).resolve_left hcne
    rwa [show (⟨(i : ℤ), i.2⟩ : WtIdx S) = i from Subtype.ext rfl] at hz
  · rw [LinearMap.mem_ker]
    refine Finsupp.ext fun j => ?_
    rw [wtDiag_apply, Finsupp.zero_apply]
    by_cases hS : S (j : ℤ)
    · rw [dif_pos hS,
        (Finsupp.mem_supported' (M := (Qi : Type)) (R := (Qi : Type)) v).mp hv
          (⟨(j : ℤ), hS⟩ : WtIdx S) (by simpa using j.2), mul_zero]
    · rw [dif_neg hS]

theorem wtDiag_range (hST : ∀ n : ℤ, S n → T n) (hc : ∀ n : ℤ, S n → c n ≠ 0) :
    LinearMap.range (wtDiag S T c)
      = Finsupp.supported (Qi : Type) (Qi : Type) {j : WtIdx T | S (j : ℤ)} := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    refine (Finsupp.mem_supported' (M := (Qi : Type)) (R := (Qi : Type)) _).mpr fun j hj => ?_
    rw [wtDiag_apply, dif_neg (show ¬ S (j : ℤ) from hj)]
  · conv_lhs => rw [Finsupp.supported_eq_span_single]
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hcne : ((c (j : ℤ) : ℚ) : (Qi : Type)) ≠ 0 := Rat.cast_ne_zero.mpr (hc _ hj)
    refine ⟨Finsupp.single (⟨(j : ℤ), hj⟩ : WtIdx S) ((c (j : ℤ) : ℚ) : (Qi : Type))⁻¹, ?_⟩
    rw [wtDiag_single, dif_pos (show T (((⟨(j : ℤ), hj⟩ : WtIdx S)) : ℤ) from j.2),
      mul_inv_cancel₀ hcne]

/-- The composite of two weight-diagonal maps with disjoint supports is zero — the "`g ∘ f = 0`"
half of an exact sequence.  @census none (helper) -/
theorem wtDiag_comp_eq_zero (S T U : ℤ → Prop) [DecidablePred S] [DecidablePred T]
    [DecidablePred U] (c c' : ℤ → ℚ) (hdisj : ∀ n : ℤ, S n → ¬ U n) (u : WtCar S) :
    wtDiag T U c' (wtDiag S T c u) = 0 := by
  refine Finsupp.ext fun j => ?_
  rw [wtDiag_apply, Finsupp.zero_apply]
  by_cases hT : T (j : ℤ)
  · rw [dif_pos hT, wtDiag_apply,
      dif_neg (show ¬ S (((⟨(j : ℤ), hT⟩ : WtIdx T)) : ℤ) from fun hc => hdisj _ hc j.2), mul_zero]
  · rw [dif_neg hT]

/-- …and conversely, anything the second map kills comes from the first — the "`ker g ⊆ im f`"
half.  @census none (helper) -/
theorem wtDiag_exists_preimage (S T U : ℤ → Prop) [DecidablePred S] [DecidablePred T]
    [DecidablePred U] (c c' : ℤ → ℚ) (hST : ∀ n : ℤ, S n → T n) (hc : ∀ n : ℤ, S n → c n ≠ 0)
    (hc' : ∀ n : ℤ, U n → c' n ≠ 0) (hcover : ∀ n : ℤ, T n → ¬ U n → S n)
    (w : WtCar T) (hw : wtDiag T U c' w = 0) :
    ∃ u : WtCar S, wtDiag S T c u = w := by
  have hsupp : w ∈ Finsupp.supported (Qi : Type) (Qi : Type) {j : WtIdx T | S (j : ℤ)} := by
    refine (Finsupp.mem_supported' (M := (Qi : Type)) (R := (Qi : Type)) _).mpr fun j hj => ?_
    have hU : U (j : ℤ) := by
      by_contra hc2
      exact hj (hcover _ j.2 hc2)
    have hcoe := congrArg (fun z : WtCar U => z (⟨(j : ℤ), hU⟩ : WtIdx U)) hw
    simp only [Finsupp.zero_apply] at hcoe
    rw [wtDiag_apply, dif_pos (show T (((⟨(j : ℤ), hU⟩ : WtIdx U)) : ℤ) from j.2)] at hcoe
    have hcne : ((c' (j : ℤ) : ℚ) : (Qi : Type)) ≠ 0 := Rat.cast_ne_zero.mpr (hc' _ hU)
    have hz := (mul_eq_zero.mp hcoe).resolve_left hcne
    rwa [show (⟨(j : ℤ), j.2⟩ : WtIdx T) = j from Subtype.ext rfl] at hz
  rw [← wtDiag_range (S := S) (T := T) (c := c) hST hc] at hsupp
  exact hsupp

/-! ### The two comparison scalars

`§6.3`'s sequences are `0 → D_ℓ → P_{ℓ,ε} → F_ℓ → 0` and `0 → F_ℓ → P^∨_{ℓ,ε} → D_ℓ → 0`.  The
two **injections** are inclusions of basis vectors on the nose, because the scalars agree
(`D_ℓ` and `P_{ℓ,ε}` both carry `scalD`; `F_ℓ` and `P^∨_{ℓ,ε}` both carry `scalF`).  The two
**surjections** are not: they change normalization, and the scalar family is forced by
`c(n+2)/c(n) = y(n)/x(n)` together with `c(-n) = c(n)` (which is what makes the map commute with
`c`).  For `P ↠ F` the solution is a row of Pascal's triangle.  @census none (helper) -/

/-- The position of the weight `n` in `F_ℓ`'s string: `n = -(ℓ-1) + 2k`.  @census none (helper) -/
def fIdx (ℓ : ℕ) (n : ℤ) : ℕ := ((n + (ℓ : ℤ) - 1) / 2).toNat

/-- The scalar family of `P_{ℓ,ε} ↠ F_ℓ`: the `(ℓ-1)`-st row of Pascal's triangle.
@census none (helper) -/
noncomputable def cPF (ℓ : ℕ) (n : ℤ) : ℚ :=
  if suppF ℓ n then (((ℓ - 1).choose (fIdx ℓ n) : ℕ) : ℚ) else 0

theorem cPF_symm (ℓ : ℕ) (n : ℤ) : cPF ℓ (-n) = cPF ℓ n := by
  by_cases h : suppF ℓ n
  · have h' : suppF ℓ (-n) := F_symm ℓ n h
    obtain ⟨h1, h2, h3⟩ := h
    rw [cPF, cPF, if_pos h', if_pos ⟨h1, h2, h3⟩]
    congr 1
    have hle : fIdx ℓ n ≤ ℓ - 1 := by simp only [fIdx]; omega
    have hsym : fIdx ℓ (-n) = (ℓ - 1) - fIdx ℓ n := by simp only [fIdx]; omega
    rw [hsym, Nat.choose_symm hle]
  · have h' : ¬ suppF ℓ (-n) := by
      intro hc
      exact h (by simpa using F_symm ℓ (-n) hc)
    rw [cPF, cPF, if_neg h', if_neg h]

/-- The one identity the family has to satisfy — Pascal's recurrence in the form
`C(m,k+1)·(k+1) = C(m,k)·(m−k)`.  @census none (helper) -/
theorem cPF_step (ℓ : ℕ) (n : ℤ) (hn : suppF ℓ n) (hn2 : suppF ℓ (n + 2)) :
    cPF ℓ (n + 2) * scalD ℓ n = scalF ℓ n * cPF ℓ n := by
  obtain ⟨h1, h2, h3⟩ := hn
  obtain ⟨g1, g2, g3⟩ := hn2
  set k : ℕ := fIdx ℓ n with hk
  have hkz : ((k : ℕ) : ℤ) = (n + (ℓ : ℤ) - 1) / 2 := by simp only [hk, fIdx]; omega
  have hnz : n = 2 * ((k : ℕ) : ℤ) - (ℓ : ℤ) + 1 := by omega
  have hnq : (n : ℚ) = 2 * ((k : ℕ) : ℚ) - (ℓ : ℚ) + 1 := by exact_mod_cast hnz
  have hk2 : fIdx ℓ (n + 2) = k + 1 := by simp only [hk, fIdx] at *; omega
  have hkle : k ≤ ℓ - 1 := by omega
  have hℓ1 : 1 ≤ ℓ := by omega
  rw [cPF, cPF, if_pos ⟨g1, g2, g3⟩, if_pos ⟨h1, h2, h3⟩, hk2, ← hk]
  have hd : scalD ℓ n = ((k + 1 : ℕ) : ℚ) := by
    rw [scalD_apply, hnq]; push_cast; ring
  have hf : scalF ℓ n = (((ℓ - 1) - k : ℕ) : ℚ) := by
    rw [scalF_apply, hnq, Nat.cast_sub hkle, Nat.cast_sub hℓ1]; push_cast; ring
  rw [hd, hf]
  have hnat : ((ℓ - 1).choose (k + 1) * (k + 1) : ℕ) = ((ℓ - 1).choose k * ((ℓ - 1) - k) : ℕ) :=
    Nat.choose_succ_right_eq (ℓ - 1) k
  have hq := congrArg (fun m : ℕ => (m : ℚ)) hnat
  push_cast at hq ⊢
  linear_combination hq

/-- The position of the weight `n` in `D_ℓ`'s string, counted from the wall.
@census none (helper) -/
def dIdx (ℓ : ℕ) (n : ℤ) : ℕ := ((|n| - (ℓ : ℤ) - 1) / 2).toNat

/-- The scalar family of `P^∨_{ℓ,ε} ↠ D_ℓ`.  @census none (helper) -/
noncomputable def dPD (ℓ : ℕ) (n : ℤ) : ℚ :=
  if suppD ℓ n then (-1 : ℚ) ^ (dIdx ℓ n) * (((ℓ + dIdx ℓ n).choose (dIdx ℓ n) : ℕ) : ℚ) else 0

theorem dPD_symm (ℓ : ℕ) (n : ℤ) : dPD ℓ (-n) = dPD ℓ n := by
  by_cases h : suppD ℓ n
  · have h' : suppD ℓ (-n) := D_symm ℓ n h
    obtain ⟨h1, h2⟩ := h
    rw [dPD, dPD, if_pos h', if_pos ⟨h1, h2⟩]
    have : dIdx ℓ (-n) = dIdx ℓ n := by simp only [dIdx, abs_neg]
    rw [this]
  · have h' : ¬ suppD ℓ (-n) := by
      intro hc
      exact h (by simpa using D_symm ℓ (-n) hc)
    rw [dPD, dPD, if_neg h', if_neg h]

/-- The identity for the dual's family: the same Pascal recurrence, in the form
`(m+1)·C(ℓ+m,m) = C(ℓ+m+1,m+1)·(m+1)`.  The sign `(-1)^k` is forced because `P^∨`'s raising
scalar is **negative** on `D_ℓ`'s half-strings.  @census none (helper) -/
theorem dPD_step (ℓ : ℕ) (n : ℤ) (hn : suppD ℓ n) (hn2 : suppD ℓ (n + 2)) :
    dPD ℓ (n + 2) * scalF ℓ n = scalD ℓ n * dPD ℓ n := by
  obtain ⟨h1, h2⟩ := hn
  obtain ⟨g1, g2⟩ := hn2
  rcases h1 with hup | hdn
  · -- the holomorphic half: `n ≥ ℓ+1`, and the index moves `k ↦ k+1`
    have hpos : (0 : ℤ) < n := by omega
    have hkz : ((dIdx ℓ n : ℕ) : ℤ) = (n - (ℓ : ℤ) - 1) / 2 := by
      simp only [dIdx, abs_of_pos hpos]; omega
    have hnq : (n : ℚ) = (ℓ : ℚ) + 1 + 2 * ((dIdx ℓ n : ℕ) : ℚ) := by
      have hz : n = (ℓ : ℤ) + 1 + 2 * ((dIdx ℓ n : ℕ) : ℤ) := by omega
      exact_mod_cast hz
    have hk2 : dIdx ℓ (n + 2) = dIdx ℓ n + 1 := by
      simp only [dIdx, abs_of_pos (show (0 : ℤ) < n + 2 by omega), abs_of_pos hpos]
      omega
    rw [dPD, dPD, if_pos ⟨g1, g2⟩, if_pos ⟨Or.inl hup, h2⟩, hk2, scalF_apply, scalD_apply, hnq]
    have hnat : (ℓ + dIdx ℓ n + 1) * (ℓ + dIdx ℓ n).choose (dIdx ℓ n)
        = (ℓ + (dIdx ℓ n + 1)).choose (dIdx ℓ n + 1) * (dIdx ℓ n + 1) :=
      Nat.add_one_mul_choose_eq _ _
    have hq := congrArg (fun j : ℕ => (j : ℚ)) hnat
    push_cast at hq ⊢
    rw [pow_succ]
    linear_combination (-((-1 : ℚ) ^ (dIdx ℓ n))) * hq
  · rcases g1 with gup | gdn
    · -- the degenerate crossing, only possible at `ℓ = 0`, `n = -1`: both scalars are `0`
      have hℓ0 : ((ℓ : ℕ) : ℚ) = 0 := by
        have : (ℓ : ℤ) = 0 := by omega
        exact_mod_cast this
      have hn1 : (n : ℚ) = -1 := by
        have : n = -1 := by omega
        exact_mod_cast this
      have hz1 : scalF ℓ n = 0 := by rw [scalF_apply, hn1, hℓ0]; ring
      have hz2 : scalD ℓ n = 0 := by rw [scalD_apply, hn1, hℓ0]; ring
      rw [hz1, hz2, mul_zero, zero_mul]
    · -- the anti-holomorphic half: `n ≤ -(ℓ+3)`, and the index moves `k ↦ k-1`
      have hneg : n < 0 := by omega
      have hkz : ((dIdx ℓ n : ℕ) : ℤ) = (-n - (ℓ : ℤ) - 1) / 2 := by
        simp only [dIdx, abs_of_neg hneg]; omega
      obtain ⟨m, hm⟩ : ∃ m : ℕ, dIdx ℓ n = m + 1 := ⟨dIdx ℓ n - 1, by omega⟩
      rw [hm] at hkz
      have hnq : (n : ℚ) = -((ℓ : ℚ) + 1 + 2 * ((m : ℕ) : ℚ) + 2) := by
        have hz : n = -((ℓ : ℤ) + 1 + 2 * ((m : ℕ) : ℤ) + 2) := by omega
        exact_mod_cast hz
      have hk2 : dIdx ℓ (n + 2) = m := by
        simp only [dIdx, abs_of_neg (show n + 2 < 0 by omega)]
        omega
      rw [dPD, dPD, if_pos ⟨Or.inr gdn, g2⟩, if_pos ⟨Or.inr hdn, h2⟩, hk2, hm,
        scalF_apply, scalD_apply, hnq]
      have hnat : (ℓ + m + 1) * (ℓ + m).choose m = (ℓ + (m + 1)).choose (m + 1) * (m + 1) :=
        Nat.add_one_mul_choose_eq _ _
      have hq := congrArg (fun j : ℕ => (j : ℚ)) hnat
      push_cast at hq ⊢
      rw [pow_succ]
      linear_combination ((-1 : ℚ) ^ m) * hq

theorem cPF_ne_zero (ℓ : ℕ) {n : ℤ} (hn : suppF ℓ n) : cPF ℓ n ≠ 0 := by
  obtain ⟨h1, h2, h3⟩ := hn
  rw [cPF, if_pos ⟨h1, h2, h3⟩]
  have hle : fIdx ℓ n ≤ ℓ - 1 := by simp only [fIdx]; omega
  exact Nat.cast_ne_zero.mpr (Nat.choose_pos hle).ne'

theorem dPD_ne_zero (ℓ : ℕ) {n : ℤ} (hn : suppD ℓ n) : dPD ℓ n ≠ 0 := by
  obtain ⟨h1, h2⟩ := hn
  rw [dPD, if_pos ⟨h1, h2⟩]
  have hle : dIdx ℓ n ≤ ℓ + dIdx ℓ n := Nat.le_add_left _ _
  have hpos : 0 < (ℓ + dIdx ℓ n).choose (dIdx ℓ n) := Nat.choose_pos hle
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  exact Nat.cast_ne_zero.mpr hpos.ne'

/-- `suppP` splits as `suppD ⊔ suppF`: every weight of the right parity is either outside the gap
or inside it.  @census none (helper) -/
theorem suppD_iff_not_suppF (ℓ : ℕ) {n : ℤ} (hn : suppP ℓ n) : suppD ℓ n ↔ ¬ suppF ℓ n := by
  simp only [suppD, suppF, suppP] at *
  constructor
  · rintro ⟨h1, -⟩ ⟨g1, g2, -⟩; omega
  · intro h
    refine ⟨?_, hn⟩
    by_contra hc
    exact h ⟨by omega, by omega, hn⟩

/-! ### The four morphisms -/

theorem incDP_hX (ℓ : ℕ) : ∀ n : ℤ, suppD ℓ n →
    (if suppD ℓ (n + 2) then (if suppP ℓ (n + 2) then (1 : ℚ) * scalD ℓ n else 0) else 0)
      = (if suppP ℓ n then (if suppP ℓ (n + 2) then scalD ℓ n * (1 : ℚ) else 0) else 0) := by
  intro n hn
  have hp : suppP ℓ n := hn.2
  have hp2 : suppP ℓ (n + 2) := suppP_add2 hp
  rw [if_pos hp, if_pos hp2, if_pos hp2, one_mul, mul_one]
  by_cases hd2 : suppD ℓ (n + 2)
  · rw [if_pos hd2]
  · rw [if_neg hd2]
    obtain ⟨h1, h2⟩ := hn
    have hor : ¬ (((ℓ : ℤ) + 1 ≤ n + 2) ∨ (n + 2 ≤ -((ℓ : ℤ) + 1))) := fun hc => hd2 ⟨hc, hp2⟩
    push_neg at hor
    have hn' : n = -((ℓ : ℤ) + 1) := by omega
    rw [scalD_apply, show (n : ℚ) = -((ℓ : ℚ) + 1) by exact_mod_cast hn']
    ring

theorem incDP_hY (ℓ : ℕ) : ∀ n : ℤ, suppD ℓ n →
    (if suppD ℓ (n - 2) then (if suppP ℓ (n - 2) then (1 : ℚ) * scalD ℓ (-n) else 0) else 0)
      = (if suppP ℓ n then (if suppP ℓ (n - 2) then scalD ℓ (-n) * (1 : ℚ) else 0) else 0) := by
  intro n hn
  have hp : suppP ℓ n := hn.2
  have hp2 : suppP ℓ (n - 2) := suppP_sub2 hp
  rw [if_pos hp, if_pos hp2, if_pos hp2, one_mul, mul_one]
  by_cases hd2 : suppD ℓ (n - 2)
  · rw [if_pos hd2]
  · rw [if_neg hd2]
    obtain ⟨h1, h2⟩ := hn
    have hor : ¬ (((ℓ : ℤ) + 1 ≤ n - 2) ∨ (n - 2 ≤ -((ℓ : ℤ) + 1))) := fun hc => hd2 ⟨hc, hp2⟩
    push_neg at hor
    have hn' : n = (ℓ : ℤ) + 1 := by omega
    rw [scalD_apply, show ((-n : ℤ) : ℚ) = -((ℓ : ℚ) + 1) by
      rw [show (-n : ℤ) = -((ℓ : ℤ) + 1) by omega]; push_cast; ring]
    ring

theorem incFPdual_hX (ℓ : ℕ) : ∀ n : ℤ, suppF ℓ n →
    (if suppF ℓ (n + 2) then (if suppP ℓ (n + 2) then (1 : ℚ) * scalF ℓ n else 0) else 0)
      = (if suppP ℓ n then (if suppP ℓ (n + 2) then scalF ℓ n * (1 : ℚ) else 0) else 0) := by
  intro n hn
  have hp : suppP ℓ n := hn.2.2
  have hp2 : suppP ℓ (n + 2) := suppP_add2 hp
  rw [if_pos hp, if_pos hp2, if_pos hp2, one_mul, mul_one]
  by_cases hf2 : suppF ℓ (n + 2)
  · rw [if_pos hf2]
  · rw [if_neg hf2]
    obtain ⟨h1, h2, h3⟩ := hn
    have hn' : n = (ℓ : ℤ) - 1 := by
      by_contra hne
      exact hf2 ⟨by omega, by omega, hp2⟩
    rw [scalF_apply, show (n : ℚ) = (ℓ : ℚ) - 1 by exact_mod_cast hn']
    ring

theorem incFPdual_hY (ℓ : ℕ) : ∀ n : ℤ, suppF ℓ n →
    (if suppF ℓ (n - 2) then (if suppP ℓ (n - 2) then (1 : ℚ) * scalF ℓ (-n) else 0) else 0)
      = (if suppP ℓ n then (if suppP ℓ (n - 2) then scalF ℓ (-n) * (1 : ℚ) else 0) else 0) := by
  intro n hn
  have hp : suppP ℓ n := hn.2.2
  have hp2 : suppP ℓ (n - 2) := suppP_sub2 hp
  rw [if_pos hp, if_pos hp2, if_pos hp2, one_mul, mul_one]
  by_cases hf2 : suppF ℓ (n - 2)
  · rw [if_pos hf2]
  · rw [if_neg hf2]
    obtain ⟨h1, h2, h3⟩ := hn
    have hn' : n = -((ℓ : ℤ) - 1) := by
      by_contra hne
      exact hf2 ⟨by omega, by omega, hp2⟩
    rw [scalF_apply, show ((-n : ℤ) : ℚ) = (ℓ : ℚ) - 1 by
      rw [show (-n : ℤ) = (ℓ : ℤ) - 1 by omega]; push_cast; ring]
    ring

theorem projPF_hX (ℓ : ℕ) : ∀ n : ℤ, suppP ℓ n →
    (if suppP ℓ (n + 2) then (if suppF ℓ (n + 2) then cPF ℓ (n + 2) * scalD ℓ n else 0) else 0)
      = (if suppF ℓ n then (if suppF ℓ (n + 2) then scalF ℓ n * cPF ℓ n else 0) else 0) := by
  intro n hn
  rw [if_pos (suppP_add2 hn)]
  by_cases hf2 : suppF ℓ (n + 2)
  · rw [if_pos hf2, if_pos hf2]
    by_cases hf : suppF ℓ n
    · rw [if_pos hf]; exact cPF_step ℓ n hf hf2
    · rw [if_neg hf]
      obtain ⟨g1, g2, g3⟩ := hf2
      have hn' : n = -((ℓ : ℤ) + 1) := by
        by_contra hne
        exact hf ⟨by omega, by omega, hn⟩
      rw [scalD_apply, show (n : ℚ) = -((ℓ : ℚ) + 1) by exact_mod_cast hn']
      ring
  · rw [if_neg hf2, if_neg hf2, ite_self]

theorem projPF_hY (ℓ : ℕ) : ∀ n : ℤ, suppP ℓ n →
    (if suppP ℓ (n - 2) then (if suppF ℓ (n - 2) then cPF ℓ (n - 2) * scalD ℓ (-n) else 0) else 0)
      = (if suppF ℓ n then (if suppF ℓ (n - 2) then scalF ℓ (-n) * cPF ℓ n else 0) else 0) := by
  intro n hn
  rw [if_pos (suppP_sub2 hn)]
  by_cases hf2 : suppF ℓ (n - 2)
  · rw [if_pos hf2, if_pos hf2]
    by_cases hf : suppF ℓ n
    · rw [if_pos hf]
      have hstep := cPF_step ℓ (-n) (F_symm ℓ n hf) (by
        have := F_symm ℓ (n - 2) hf2
        simpa [show -(n - 2) = -n + 2 by ring] using this)
      rw [cPF_symm, show -n + 2 = -(n - 2) by ring, cPF_symm] at hstep
      exact hstep
    · rw [if_neg hf]
      obtain ⟨g1, g2, g3⟩ := hf2
      have hn' : n = (ℓ : ℤ) + 1 := by
        by_contra hne
        exact hf ⟨by omega, by omega, hn⟩
      rw [scalD_apply, show ((-n : ℤ) : ℚ) = -((ℓ : ℚ) + 1) by
        rw [show (-n : ℤ) = -((ℓ : ℤ) + 1) by omega]; push_cast; ring]
      ring
  · rw [if_neg hf2, if_neg hf2, ite_self]

theorem projPdualD_hX (ℓ : ℕ) : ∀ n : ℤ, suppP ℓ n →
    (if suppP ℓ (n + 2) then (if suppD ℓ (n + 2) then dPD ℓ (n + 2) * scalF ℓ n else 0) else 0)
      = (if suppD ℓ n then (if suppD ℓ (n + 2) then scalD ℓ n * dPD ℓ n else 0) else 0) := by
  intro n hn
  rw [if_pos (suppP_add2 hn)]
  by_cases hd2 : suppD ℓ (n + 2)
  · rw [if_pos hd2, if_pos hd2]
    by_cases hd : suppD ℓ n
    · rw [if_pos hd]; exact dPD_step ℓ n hd hd2
    · rw [if_neg hd]
      have hf : suppF ℓ n := by
        by_contra hc
        exact hd ((suppD_iff_not_suppF ℓ hn).mpr hc)
      obtain ⟨h1, h2, h3⟩ := hf
      obtain ⟨g1, g2⟩ := hd2
      have hn' : n = (ℓ : ℤ) - 1 := by omega
      rw [scalF_apply, show (n : ℚ) = (ℓ : ℚ) - 1 by exact_mod_cast hn']
      ring
  · rw [if_neg hd2, if_neg hd2, ite_self]

theorem projPdualD_hY (ℓ : ℕ) : ∀ n : ℤ, suppP ℓ n →
    (if suppP ℓ (n - 2) then (if suppD ℓ (n - 2) then dPD ℓ (n - 2) * scalF ℓ (-n) else 0) else 0)
      = (if suppD ℓ n then (if suppD ℓ (n - 2) then scalD ℓ (-n) * dPD ℓ n else 0) else 0) := by
  intro n hn
  rw [if_pos (suppP_sub2 hn)]
  by_cases hd2 : suppD ℓ (n - 2)
  · rw [if_pos hd2, if_pos hd2]
    by_cases hd : suppD ℓ n
    · rw [if_pos hd]
      have hstep := dPD_step ℓ (-n) (D_symm ℓ n hd) (by
        have := D_symm ℓ (n - 2) hd2
        simpa [show -(n - 2) = -n + 2 by ring] using this)
      rw [dPD_symm, show -n + 2 = -(n - 2) by ring, dPD_symm] at hstep
      exact hstep
    · rw [if_neg hd]
      have hf : suppF ℓ n := by
        by_contra hc
        exact hd ((suppD_iff_not_suppF ℓ hn).mpr hc)
      obtain ⟨h1, h2, h3⟩ := hf
      obtain ⟨g1, g2⟩ := hd2
      have hn' : n = -((ℓ : ℤ) - 1) := by omega
      rw [scalF_apply, show ((-n : ℤ) : ℚ) = (ℓ : ℚ) - 1 by
        rw [show (-n : ℤ) = (ℓ : ℤ) - 1 by omega]; push_cast; ring]
      ring
  · rw [if_neg hd2, if_neg hd2, ite_self]

/-- `D_ℓ ↪ P_{ℓ,ε}`: the inclusion of basis vectors — no rescaling, because the two objects carry
the **same** raising scalar `scalD`.  @census none (helper) -/
noncomputable def incDP (ℓ ε : ℕ) (hℓ : 1 ≤ ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpe : (ℓ : ℤ) % 2 ≠ (ε : ℤ) % 2) : (D ℓ) ⟶ (P ℓ ε hℓ hε hpe) :=
  wtHomOf (wtDiag (suppD ℓ) (suppP ℓ) (fun _ => 1))
    (fun v => wtDiag_H v)
    (fun v => wtDiag_X (x := scalD ℓ) (y := scalD ℓ) (incDP_hX ℓ) v)
    (fun v => wtDiag_Y (x := scalD ℓ) (y := scalD ℓ) (incDP_hY ℓ) v)
    (fun _ _ hv => wtDiag_comp hv)
    (fun v => by
      rw [D_galAct ℓ, P_galAct ℓ ε hℓ hε hpe]
      exact wtDiag_conj (D_symm ℓ) (P_symm ℓ) (fun _ => rfl) v)

/-- `P_{ℓ,ε} ↠ F_ℓ`: the rescaling by the `(ℓ-1)`-st row of Pascal's triangle.
@census none (helper) -/
noncomputable def projPF (ℓ ε : ℕ) (hℓ : 1 ≤ ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpe : (ℓ : ℤ) % 2 ≠ (ε : ℤ) % 2) : (P ℓ ε hℓ hε hpe) ⟶ (F ℓ hℓ) :=
  wtHomOf (wtDiag (suppP ℓ) (suppF ℓ) (cPF ℓ))
    (fun v => wtDiag_H v)
    (fun v => wtDiag_X (x := scalD ℓ) (y := scalF ℓ) (projPF_hX ℓ) v)
    (fun v => wtDiag_Y (x := scalD ℓ) (y := scalF ℓ) (projPF_hY ℓ) v)
    (fun _ _ hv => wtDiag_comp hv)
    (fun v => by
      rw [P_galAct ℓ ε hℓ hε hpe, F_galAct ℓ hℓ]
      exact wtDiag_conj (P_symm ℓ) (F_symm ℓ) (cPF_symm ℓ) v)

/-- `F_ℓ ↪ P^∨_{ℓ,ε}`: again an inclusion of basis vectors, since both carry `scalF`.
@census none (helper) -/
noncomputable def incFPdual (ℓ ε : ℕ) (hℓ : 1 ≤ ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpe : (ℓ : ℤ) % 2 ≠ (ε : ℤ) % 2) : (F ℓ hℓ) ⟶ (Pdual ℓ ε hℓ hε hpe) :=
  wtHomOf (wtDiag (suppF ℓ) (suppP ℓ) (fun _ => 1))
    (fun v => wtDiag_H v)
    (fun v => wtDiag_X (x := scalF ℓ) (y := scalF ℓ) (incFPdual_hX ℓ) v)
    (fun v => wtDiag_Y (x := scalF ℓ) (y := scalF ℓ) (incFPdual_hY ℓ) v)
    (fun _ _ hv => wtDiag_comp hv)
    (fun v => by
      rw [F_galAct ℓ hℓ, Pdual_galAct ℓ ε hℓ hε hpe]
      exact wtDiag_conj (F_symm ℓ) (P_symm ℓ) (fun _ => rfl) v)

/-- `P^∨_{ℓ,ε} ↠ D_ℓ`.  @census none (helper) -/
noncomputable def projPdualD (ℓ ε : ℕ) (hℓ : 1 ≤ ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpe : (ℓ : ℤ) % 2 ≠ (ε : ℤ) % 2) : (Pdual ℓ ε hℓ hε hpe) ⟶ (D ℓ) :=
  wtHomOf (wtDiag (suppP ℓ) (suppD ℓ) (dPD ℓ))
    (fun v => wtDiag_H v)
    (fun v => wtDiag_X (x := scalF ℓ) (y := scalD ℓ) (projPdualD_hX ℓ) v)
    (fun v => wtDiag_Y (x := scalF ℓ) (y := scalD ℓ) (projPdualD_hY ℓ) v)
    (fun _ _ hv => wtDiag_comp hv)
    (fun v => by
      rw [Pdual_galAct ℓ ε hℓ hε hpe, D_galAct ℓ]
      exact wtDiag_conj (P_symm ℓ) (D_symm ℓ) (dPD_symm ℓ) v)

/-! ## The statements of `RQ2-6.03` -/

section Statements

variable (ℓ ε : ℕ) (hℓ : 1 ≤ ℓ) (hε : ε = 0 ∨ ε = 1) (hpe : (ℓ : ℤ) % 2 ≠ (ε : ℤ) % 2)

/-- **`RQ2-6.03-C2`** — `P_{ℓ,ε}` fits into a **non-split** short exact sequence
`0 → D_ℓ → P_{ℓ,ε} → F_ℓ → 0` in `HC_{ℓ²}(𝔤,K)_ℚ`.

Exactness is stated on the underlying `ℚ[√-1]`-linear maps of morphisms of `HC_λ(𝔤,K)_ℚ` (`HC.Hom`, built by `wtHomOf`; the v1 `HCQHom`
of S8 was the same notion; these are the `ℚ[√-1]`-maps commuting with `H, X, Y`, the grading **and** `c`,
i.e. exactly the maps descending to the `ℚ`-forms, ruling `R-S8-6`); non-splitness is the absence
of a section of the surjection.

@census    none (auxiliary; discharges census clause `RQ2-6.03-C2`)
@source    ex:principalseries
@clauses   RQ2-6.03-C2
@imports   none
@divergence none -/
theorem P_exactSequence :
    ∃ (f : (D ℓ) ⟶ (P ℓ ε hℓ hε hpe)) (g : (P ℓ ε hℓ hε hpe) ⟶ (F ℓ hℓ)),
      Function.Injective f.toLinearMap ∧
      Function.Surjective g.toLinearMap ∧
      LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap ∧
      ¬ ∃ s : (F ℓ hℓ) ⟶ (P ℓ ε hℓ hε hpe),
          ∀ v, g.toLinearMap (s.toLinearMap v) = v := by
  have hℓz : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
  refine ⟨incDP ℓ ε hℓ hε hpe, projPF ℓ ε hℓ hε hpe, ?_, ?_, ?_, ?_⟩
  · exact wtDiag_injective (S := suppD ℓ) (T := suppP ℓ) (c := fun _ => 1)
      (fun _ hn => hn.2) (fun _ _ => one_ne_zero)
  · exact wtDiag_surjective (S := suppP ℓ) (T := suppF ℓ) (c := cPF ℓ)
      (fun _ hn => hn.2.2) (fun _ hn => cPF_ne_zero ℓ hn)
  · -- `suppP = suppD ⊔ suppF`, so the image of `D_ℓ` is exactly what `P ↠ F_ℓ` kills.  Stated
    -- elementwise: comparing the two submodules directly forces a defeq between the two objects'
    -- module instances that does not terminate.
    have hfp : ∀ u : (D ℓ).carrier, (incDP ℓ ε hℓ hε hpe).toLinearMap u
        = wtDiag (suppD ℓ) (suppP ℓ) (fun _ => 1) u := fun _ => rfl
    have hgp : ∀ u : (P ℓ ε hℓ hε hpe).carrier, (projPF ℓ ε hℓ hε hpe).toLinearMap u
        = wtDiag (suppP ℓ) (suppF ℓ) (cPF ℓ) u := fun _ => rfl
    refine SetLike.ext fun w => ?_
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨u, hu⟩
      rw [← hu, hfp, hgp]
      exact wtDiag_comp_eq_zero (suppD ℓ) (suppP ℓ) (suppF ℓ) (fun _ => 1) (cPF ℓ)
        (fun _ hn => (suppD_iff_not_suppF ℓ hn.2).mp hn) u
    · intro hw
      rw [hgp] at hw
      obtain ⟨u, hu⟩ := wtDiag_exists_preimage (suppD ℓ) (suppP ℓ) (suppF ℓ) (fun _ => 1)
        (cPF ℓ) (fun _ hn => hn.2) (fun _ _ => one_ne_zero) (fun _ hn => cPF_ne_zero ℓ hn)
        (fun _ hT hU => (suppD_iff_not_suppF ℓ hT).mpr hU) w hw
      exact ⟨u, by rw [hfp]; exact hu⟩
  · -- non-split: any section would have to send the highest weight vector of `F_ℓ` to a vector
    -- `X` does not kill, and `X` is injective there because its scalar `x(ℓ-1) = ℓ` is non-zero
    rintro ⟨s, hs⟩
    have hFt : suppF ℓ ((ℓ : ℤ) - 1) := ⟨by omega, by omega, by omega⟩
    have hPt : suppP ℓ ((ℓ : ℤ) - 1) := hFt.2.2
    have hPt2 : suppP ℓ ((ℓ : ℤ) + 1) := by simp only [suppP]; omega
    have hstepne : (((scalD ℓ ((ℓ : ℤ) - 1) : ℚ) : (Qi : Type))) ≠ 0 := by
      have h1 : scalD ℓ ((ℓ : ℤ) - 1) = (ℓ : ℚ) := by simp only [scalD_apply]; push_cast; ring
      rw [h1]
      exact Rat.cast_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))
    have hXe : (F ℓ hℓ).weight.X
        (Finsupp.single (⟨(ℓ : ℤ) - 1, hFt⟩ : WtIdx (suppF ℓ)) (1 : (Qi : Type))) = 0 := by
      show wtX (suppF ℓ) (scalF ℓ) _ = 0
      refine wtX_single_eq_zero (S := suppF ℓ) (x := scalF ℓ) ?_ 1
      show ¬ suppF ℓ ((ℓ : ℤ) - 1 + 2)
      rintro ⟨u1, u2, u3⟩
      omega
    have hmem : s.toLinearMap
        (Finsupp.single (⟨(ℓ : ℤ) - 1, hFt⟩ : WtIdx (suppF ℓ)) (1 : (Qi : Type)))
          ∈ (P ℓ ε hℓ hε hpe).weight.comp ((ℓ : ℤ) - 1) :=
      s.map_comp _ _ (by exact single_mem_wtComp (⟨(ℓ : ℤ) - 1, hFt⟩ : WtIdx (suppF ℓ)) 1)
    obtain ⟨a, ha⟩ := exists_single_of_mem_wtComp (S := suppP ℓ) hPt hmem
    have hXP : (P ℓ ε hℓ hε hpe).weight.X (s.toLinearMap
        (Finsupp.single (⟨(ℓ : ℤ) - 1, hFt⟩ : WtIdx (suppF ℓ)) (1 : (Qi : Type)))) = 0 := by
      rw [← s.map_X, hXe, map_zero]
    rw [ha] at hXP
    have hXP' : wtX (suppP ℓ) (scalD ℓ)
        (Finsupp.single (⟨(ℓ : ℤ) - 1, hPt⟩ : WtIdx (suppP ℓ)) a) = 0 := hXP
    rw [wtX_single_eq (S := suppP ℓ) (x := scalD ℓ) (i := ⟨(ℓ : ℤ) - 1, hPt⟩)
      (j := ⟨(ℓ : ℤ) + 1, hPt2⟩) (by show (ℓ : ℤ) + 1 = ((ℓ : ℤ) - 1) + 2; ring) a] at hXP'
    have haz : a = 0 :=
      (mul_eq_zero.mp (Finsupp.single_eq_zero.mp hXP')).resolve_left hstepne
    have hse : s.toLinearMap
        (Finsupp.single (⟨(ℓ : ℤ) - 1, hFt⟩ : WtIdx (suppF ℓ)) (1 : (Qi : Type))) = 0 := by
      rw [ha, haz, Finsupp.single_zero]
      rfl
    have hkey := hs (Finsupp.single (⟨(ℓ : ℤ) - 1, hFt⟩ : WtIdx (suppF ℓ)) (1 : (Qi : Type)))
    rw [hse, map_zero] at hkey
    exact (Finsupp.single_ne_zero.mpr one_ne_zero) hkey.symm

/-- **`RQ2-6.03-C4`** — the dual fits into `0 → F_ℓ → P^∨_{ℓ,ε} → D_ℓ → 0`.

@census    none (auxiliary; discharges census clause `RQ2-6.03-C4`)
@source    ex:principalseries
@clauses   RQ2-6.03-C4
@imports   none
@divergence WEAKENED_OR_PARTIAL (added 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S9,
coordinator ruling `R-FR-9`, final-release WP-16b, `MISMATCH-TRIAGE.md` row #18; until then `none`).
Clause `RQ2-6.03-C4` (census r18) defines `P^∨_{ℓ,ε} := I(-ℓ,ε)` as the contragredient of `P_{ℓ,ε}`
and realizes `F_ℓ ⊆ P^∨` as degree-`(ℓ-1)` polynomials in the bottom row. This theorem states only
the exact sequence `0 → F_ℓ → P^∨_{ℓ,ε} → D_ℓ → 0` for the weight-line object `Pdual`. Induction,
contragredience and the polynomial model are not formalized (see `Pdual`'s divergence field). -/
theorem Pdual_exactSequence :
    ∃ (f : (F ℓ hℓ) ⟶ (Pdual ℓ ε hℓ hε hpe)) (g : (Pdual ℓ ε hℓ hε hpe) ⟶ (D ℓ)),
      Function.Injective f.toLinearMap ∧
      Function.Surjective g.toLinearMap ∧
      LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap := by
  refine ⟨incFPdual ℓ ε hℓ hε hpe, projPdualD ℓ ε hℓ hε hpe, ?_, ?_, ?_⟩
  · exact wtDiag_injective (S := suppF ℓ) (T := suppP ℓ) (c := fun _ => 1)
      (fun _ hn => hn.2.2) (fun _ _ => one_ne_zero)
  · exact wtDiag_surjective (S := suppP ℓ) (T := suppD ℓ) (c := dPD ℓ)
      (fun _ hn => hn.2) (fun _ hn => dPD_ne_zero ℓ hn)
  · have hfp : ∀ u : (F ℓ hℓ).carrier, (incFPdual ℓ ε hℓ hε hpe).toLinearMap u
        = wtDiag (suppF ℓ) (suppP ℓ) (fun _ => 1) u := fun _ => rfl
    have hgp : ∀ u : (Pdual ℓ ε hℓ hε hpe).carrier, (projPdualD ℓ ε hℓ hε hpe).toLinearMap u
        = wtDiag (suppP ℓ) (suppD ℓ) (dPD ℓ) u := fun _ => rfl
    refine SetLike.ext fun w => ?_
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨u, hu⟩
      rw [← hu, hfp, hgp]
      exact wtDiag_comp_eq_zero (suppF ℓ) (suppP ℓ) (suppD ℓ) (fun _ => 1) (dPD ℓ)
        (fun _ hn hd => ((suppD_iff_not_suppF ℓ hn.2.2).mp hd) hn) u
    · intro hw
      rw [hgp] at hw
      obtain ⟨u, hu⟩ := wtDiag_exists_preimage (suppF ℓ) (suppP ℓ) (suppD ℓ) (fun _ => 1)
        (dPD ℓ) (fun _ hn => hn.2.2) (fun _ _ => one_ne_zero) (fun _ hn => dPD_ne_zero ℓ hn)
        (fun _ hT hU => by
          by_contra hc
          exact hU ((suppD_iff_not_suppF ℓ hT).mpr hc)) w hw
      exact ⟨u, by rw [hfp]; exact hu⟩

/-- **`RQ2-6.03-C3`** — all relevant `K`-type spaces `P_{ℓ,ε}[χ_{±(ℓ±1)}]` are one-dimensional
(and, for the dual, likewise).  This is what distinguishes `P_{ℓ,ε}` from `D_ℓ ⊕ F_ℓ` at the level
of `K`-types: nothing vanishes.

@census    none (auxiliary; discharges census clause `RQ2-6.03-C3`)
@source    ex:principalseries
@clauses   RQ2-6.03-C3
@imports   none
@divergence none -/
theorem P_weightSpaces :
    (∀ n : ℤ, (n - ((ℓ : ℤ) - 1)) % 2 = 0 →
      Module.finrank ImagUnit.qi.L ((P ℓ ε hℓ hε hpe).weight.comp n) = 1) ∧
    (∀ n : ℤ, (n - ((ℓ : ℤ) - 1)) % 2 ≠ 0 →
      (P ℓ ε hℓ hε hpe).weight.comp n = ⊥) ∧
    (∀ n : ℤ, (n - ((ℓ : ℤ) - 1)) % 2 = 0 →
      Module.finrank ImagUnit.qi.L ((Pdual ℓ ε hℓ hε hpe).weight.comp n) = 1) :=
  ⟨fun _ hn => wtComp_finrank (S := suppP ℓ) hn,
   fun _ hn => wtComp_eq_bot (S := suppP ℓ) hn,
   fun _ hn => wtComp_finrank (S := suppP ℓ) hn⟩

/-- **`RQ2-6.03-C5`, `C6`, `C7`, `C8` (first display)** — the displayed `ℚ`-rational Gelfand-quiver
diagram of `P_{ℓ,ε}`:

```
  ℚ[√-1]  --0-->  ℚ[√-1]  --=-->  ℚ[√-1]
     ↓ c    <-=--    ↓ c    <--0--   ↓ c
  ℚ[√-1]          ℚ[√-1]          ℚ[√-1]
```

All three vertex spaces are one-dimensional (`C3`, and what turns `C7`'s "non-zero" into
"isomorphism"); the two edges **into** `⋆` (`a_-` = edge `0`, `a_+` = edge `2`) are **zero**
(`C6`); the two edges **out of** `⋆` (`b_-` = edge `1`, `b_+` = edge `3`) are **isomorphisms**
(`C7`).

**`C5` is carried by the two stabilization-triviality conjuncts, one per vertex family**, and by
those alone — this is the repair of finding `V-S9G2-1`, whose defect was that the `(⋆)` half was
missing:

* `T₋ = 𝟏` on `M(−)` is the `(±)` half of "unipotent stabilization is trivial", and through S8's
  definition `φ_{v,c} = c ∘ φ^{(∞)}_v` (v1's `Gelfand.phiC`, `Gelfand.limAt`; since WP-10
  `RationalStructure.phiC`, `RationalStructure.limAt`) it is what carries `φ_± = c`;
* `Y⋆X⋆ = 𝟏` on `M(⋆)` is the `(⋆)` half, and through the same definition it is the **whole**
  content of `φ_⋆ = c ∘ X⋆`. It is stated on the tree's own normalized operators
  `Split.xStar`/`Split.yStar` at `(qiSetupOf (P …))`, exactly as `F_quiverRep_eq` states it for
  `F_ℓ`, because those are the operators the clause names.  *(2026-10-21, O-V2-6 round 2: this
  sentence named them by their v1 names `Gelfand.xStar`/`Gelfand.yStar`; v1's `Gelfand.phiC`,
  `Gelfand.limAt`, `Gelfand.xStar` and `Gelfand.yStar` were deleted with the v1 Q-chain at WP-13,
  `ae9eda9`.)*

The final conjunct (`∃ b ≠ 0` fixed by `φ_⋆`, in the disjoint union) is **not** what carries
`φ_⋆ = c ∘ X⋆`, and is no longer claimed to be: see the `@divergence`.

@census    none (auxiliary; discharges census clauses `RQ2-6.03-C5`, `C6`, `C7`, `C8`)
@source    ex:principalseries
@clauses   RQ2-6.03-C5, RQ2-6.03-C6, RQ2-6.03-C7, RQ2-6.03-C8
@imports   none
@divergence JUSTIFIED_REFORMULATION (the vertical arrows' `c`-labels, disclosed).  `C6` and `C7`
are stated exactly as `census-v1.8` reads them after revision r11's author-approved correction
(`AN-43`, CLOSED), and `C5` is now stated at **both** vertex families, which is what
`V-S9G2-1` found missing.

What remains reformulated is only the display's three vertical `c`-labels.  Writing `φ_⋆ = c` on
the nose would pin the identification `M(⋆) ≅ ℚ[√-1]` that the source introduces only "after
choosing suitable bases"; the `∃ b ≠ 0` conjunct is stated instead.  **What that conjunct does and
does not do** (finding `V-S9G2-2`): it pins the display's *isomorphism class* — it is derivable
from the adjacent `finrank = 1` conjunct together with S2's `Rep` axioms alone (`φ` is an `≃+`,
`c`-semilinear and involutive, so Hilbert 90 supplies a fixed vector), with no reference to any
operator of §6.  It is therefore **not** the carrier of `φ_⋆ = c ∘ X⋆`; the `Y⋆X⋆ = 𝟏` conjunct
above is, through S8's definition of `φ_{v,c}`.  Stated in the disjoint union `⊔_v M(v)` (S2's
`Rep.tot`) to keep a transport along `c · ⋆ = ⋆` out of the statement. -/
theorem P_quiverRep_eq :
    Module.finrank (Qi : Type)
      ((EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 0)) = 1 ∧
    Module.finrank (Qi : Type)
      ((EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 1)) = 1 ∧
    Module.finrank (Qi : Type)
      ((EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 2)) = 1 ∧
    (EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.φEdge (0 : Fin 4) = 0 ∧
    (EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.φEdge (2 : Fin 4) = 0 ∧
    Function.Bijective ((EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.φEdge (1 : Fin 4)) ∧
    Function.Bijective ((EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.φEdge (3 : Fin 4)) ∧
    (∀ v : (P ℓ ε hℓ hε hpe).carrier,
      v ∈ (P ℓ ε hℓ hε hpe).weight.comp (-((ℓ : ℤ) + 1)) →
        Split.tMinus (qiSetupOf (P ℓ ε hℓ hε hpe)) v = v) ∧
    -- `RQ2-6.03-C5`, the `(⋆)` half: `Y⋆ ∘ X⋆ = 𝟏` on `M(⋆)`, which through S8's
    -- `φ_{v,c} = c ∘ φ^{(∞)}_v` is the whole content of `φ_⋆ = c ∘ X⋆`.  Repair of `V-S9G2-1`.
    (∀ v : (P ℓ ε hℓ hε hpe).carrier,
      v ∈ (P ℓ ε hℓ hε hpe).weight.comp (-((ℓ : ℤ) - 1)) →
        Split.yStar (qiSetupOf (P ℓ ε hℓ hε hpe))
          (Split.xStar (qiSetupOf (P ℓ ε hℓ hε hpe)) v) = v) ∧
    (∃ b : (EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 1), b ≠ 0 ∧
      (EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.tot _
          ((EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.φ galConj (vtxQ SqrtNegOneExt.qi.card_gal 1) b)
        = (EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.tot (vtxQ SqrtNegOneExt.qi.card_gal 1) b) := by
  have hℓz : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
  have hSm : suppP ℓ (-((ℓ : ℤ) + 1)) := by simp only [suppP]; omega
  have hSs : suppP ℓ (-((ℓ : ℤ) - 1)) := by simp only [suppP]; omega
  have hSp : suppP ℓ ((ℓ : ℤ) + 1) := by simp only [suppP]; omega
  have hSt : suppP ℓ ((ℓ : ℤ) - 1) := by simp only [suppP]; omega
  -- the two rational numbers the whole display turns on
  have hwall : scalD ℓ (-((ℓ : ℤ) + 1)) = 0 := by simp only [scalD_apply]; push_cast; ring
  have hstep : scalD ℓ ((ℓ : ℤ) - 1) = (ℓ : ℚ) := by simp only [scalD_apply]; push_cast; ring
  have hstepne : (((scalD ℓ ((ℓ : ℤ) - 1) : ℚ) : (Qi : Type))) ≠ 0 := by
    rw [hstep]
    have hq : ((ℓ : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact_mod_cast fun h => hq (by exact_mod_cast h)
  have hcas : (qiSetupOf (P ℓ ε hℓ hε hpe)).weight.casimir
      = (algebraMap ℚ (Qi : Type) ((ℓ : ℚ) ^ 2)) • 1 := wtCasimir_eq ℓ (P_sl2 ℓ) (P_cas ℓ)
  refine ⟨wtComp_finrank hSm, wtComp_finrank hSs, wtComp_finrank hSp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `φ_{a_-} = X` out of `M(−)`: the raising scalar at `-(ℓ+1)` is `0`
    refine wtRestrict_eq_zero (S := suppP ℓ) hSm (m := -((ℓ : ℤ) - 1))
      (fun _ hv => Split.x_mem (Q := (qiSetupOf (P ℓ ε hℓ hε hpe))) (m := -((ℓ : ℤ) + 1))
        (n := -((ℓ : ℤ) - 1)) (by ring) hv) fun a => ?_
    show wtX (suppP ℓ) (scalD ℓ) (Finsupp.single _ a) = 0
    rw [wtX_single_eq (S := suppP ℓ) (x := scalD ℓ) (i := ⟨-((ℓ : ℤ) + 1), hSm⟩)
      (j := ⟨-((ℓ : ℤ) - 1), hSs⟩) (by show -((ℓ : ℤ) - 1) = -((ℓ : ℤ) + 1) + 2; ring) a]
    show Finsupp.single _ (((scalD ℓ (-((ℓ : ℤ) + 1)) : ℚ) : (Qi : Type)) * a) = 0
    rw [hwall]; simp
  · -- `φ_{a_+} = X⋆⁻¹ ∘ Y` out of `M(+)`: `Y`'s scalar at `ℓ+1` is the same `0`
    refine wtRestrict_eq_zero (S := suppP ℓ) hSp (m := -((ℓ : ℤ) - 1))
      (f := (((qiSetupOf (P ℓ ε hℓ hε hpe)).starInverses hℓ).xStarInv).comp
        (qiSetupOf (P ℓ ε hℓ hε hpe)).Y)
      (fun _ hv => ((qiSetupOf (P ℓ ε hℓ hε hpe)).starInverses hℓ).xStarInv_mem
        (Split.y_mem (Q := (qiSetupOf (P ℓ ε hℓ hε hpe))) (m := (ℓ : ℤ) + 1) (n := (ℓ : ℤ) - 1)
          (by ring) hv)) fun a => ?_
    show (((qiSetupOf (P ℓ ε hℓ hε hpe)).starInverses hℓ).xStarInv)
      (wtY (suppP ℓ) (scalD ℓ) (Finsupp.single _ a)) = 0
    rw [wtY_single_eq (S := suppP ℓ) (x := scalD ℓ) (i := ⟨(ℓ : ℤ) + 1, hSp⟩)
      (j := ⟨(ℓ : ℤ) - 1, hSt⟩) (by show (ℓ : ℤ) - 1 = ((ℓ : ℤ) + 1) - 2; ring) a]
    show (((qiSetupOf (P ℓ ε hℓ hε hpe)).starInverses hℓ).xStarInv)
      (Finsupp.single _ (((scalD ℓ (-((ℓ : ℤ) + 1)) : ℚ) : (Qi : Type)) * a)) = 0
    rw [hwall, Rat.cast_zero, zero_mul, Finsupp.single_zero]
    exact LinearMap.map_zero (((qiSetupOf (P ℓ ε hℓ hε hpe)).starInverses hℓ).xStarInv)
  · -- `φ_{b_-} = Y` out of `M(⋆)`: scalar `x(ℓ-1) = ℓ ≠ 0`, so an isomorphism
    refine wtRestrict_bijective_of_scalar (S := suppP ℓ) hSs hSm _
      (fun _ hv => Split.y_mem (Q := (qiSetupOf (P ℓ ε hℓ hε hpe))) (m := -((ℓ : ℤ) - 1))
        (n := -((ℓ : ℤ) + 1)) (by ring) hv) hstepne fun a => ?_
    show wtY (suppP ℓ) (scalD ℓ) (Finsupp.single _ a) = _
    rw [wtY_single_eq (S := suppP ℓ) (x := scalD ℓ) (i := ⟨-((ℓ : ℤ) - 1), hSs⟩)
      (j := ⟨-((ℓ : ℤ) + 1), hSm⟩) (by show -((ℓ : ℤ) + 1) = -((ℓ : ℤ) - 1) - 2; ring) a]
    norm_num
  · -- `φ_{b_+} = X ∘ X⋆` out of `M(⋆)`: `X⋆` is invertible there (its inverse is `Y⋆`, because
    -- `T₋ = 𝟏`) and `X`'s scalar at `ℓ-1` is `ℓ ≠ 0`
    refine wtBijective_of_injective (S := suppP ℓ) hSs hSp ?_
    refine wtRestrict_injective (S := suppP ℓ) hSs
      (f := ((qiSetupOf (P ℓ ε hℓ hε hpe)).X).comp (Split.xStar (qiSetupOf (P ℓ ε hℓ hε hpe))))
      (fun _ hv => Split.x_mem (Q := (qiSetupOf (P ℓ ε hℓ hε hpe))) (m := (ℓ : ℤ) - 1)
        (n := (ℓ : ℤ) + 1) (by ring)
        (Split.xStar_mem (Q := (qiSetupOf (P ℓ ε hℓ hε hpe))) (m := -((ℓ : ℤ) - 1))
          (n := (ℓ : ℤ) - 1) (by ring) hℓ hv)) fun a ha => ?_
    have ha' : (qiSetupOf (P ℓ ε hℓ hε hpe)).X (Split.xStar (qiSetupOf (P ℓ ε hℓ hε hpe))
        (Finsupp.single (⟨-((ℓ : ℤ) - 1), hSs⟩ : WtIdx (suppP ℓ)) a)) = 0 := ha
    have hmem : Split.xStar (qiSetupOf (P ℓ ε hℓ hε hpe))
        (Finsupp.single (⟨-((ℓ : ℤ) - 1), hSs⟩ : WtIdx (suppP ℓ)) a)
          ∈ wtComp (suppP ℓ) ((ℓ : ℤ) - 1) :=
      Split.xStar_mem (Q := (qiSetupOf (P ℓ ε hℓ hε hpe))) (m := -((ℓ : ℤ) - 1)) (n := (ℓ : ℤ) - 1)
        (by ring) hℓ (single_mem_wtComp (⟨-((ℓ : ℤ) - 1), hSs⟩ : WtIdx (suppP ℓ)) a)
    obtain ⟨b, hb⟩ := exists_single_of_mem_wtComp (S := suppP ℓ) hSt hmem
    rw [hb] at ha'
    -- `X` kills nothing on `M_{ℓ-1}`, so `X⋆ e = 0`
    have hXa : wtX (suppP ℓ) (scalD ℓ)
        (Finsupp.single (⟨(ℓ : ℤ) - 1, hSt⟩ : WtIdx (suppP ℓ)) b) = 0 := ha'
    rw [wtX_single_eq (S := suppP ℓ) (x := scalD ℓ) (i := ⟨(ℓ : ℤ) - 1, hSt⟩)
      (j := ⟨(ℓ : ℤ) + 1, hSp⟩) (by show (ℓ : ℤ) + 1 = ((ℓ : ℤ) - 1) + 2; ring) b] at hXa
    have hbz : (((scalD ℓ ((ℓ : ℤ) - 1) : ℚ) : (Qi : Type))) * b = 0 :=
      Finsupp.single_eq_zero.mp hXa
    have hXzero : Split.xStar (qiSetupOf (P ℓ ε hℓ hε hpe))
        (Finsupp.single (⟨-((ℓ : ℤ) - 1), hSs⟩ : WtIdx (suppP ℓ)) a) = 0 := by
      rw [hb, (mul_eq_zero.mp hbz).resolve_left hstepne, Finsupp.single_zero]
      rfl
    -- and `Y⋆X⋆ = T₋ = 𝟏` on `M(⋆)`, so the vector itself was zero
    have hid := (Split.yStar_xStar_apply (Q := (qiSetupOf (P ℓ ε hℓ hε hpe))) hℓ _
      (single_mem_wtComp (⟨-((ℓ : ℤ) - 1), hSs⟩ : WtIdx (suppP ℓ)) a)).trans
      (tMinus_eq_one_of_casimir_scalar (qiSetupOf (P ℓ ε hℓ hε hpe)) hℓ hcas _)
    rw [hXzero, map_zero] at hid
    exact Finsupp.single_eq_zero.mp hid.symm
  · -- `T₋ = 𝟏` on `M(−)`
    exact fun v _ => tMinus_eq_one_of_casimir_scalar (qiSetupOf (P ℓ ε hℓ hε hpe)) hℓ hcas v
  · -- `Y⋆X⋆ = 𝟏` on `M(⋆)` — the `(⋆)` half `V-S9G2-1` found missing
    exact fun v hv => (Split.yStar_xStar_apply (Q := (qiSetupOf (P ℓ ε hℓ hε hpe))) hℓ v hv).trans
      (tMinus_eq_one_of_casimir_scalar (qiSetupOf (P ℓ ε hℓ hε hpe)) hℓ hcas v)
  · -- a non-zero `φ_⋆`-fixed vector: Hilbert 90 at the `c`-fixed vertex `⋆` (verifier probe `P4`)
    have hfix : galConj • vtxQ SqrtNegOneExt.qi.card_gal 1 = vtxQ SqrtNegOneExt.qi.card_gal 1 := by
      rw [gelfandQ_smul_vertex]; rfl
    have hinvc : (galConj : (Qi : Type) ≃ₐ[ℚ] (Qi : Type))⁻¹ = galConj :=
      inv_eq_of_mul_eq_one_right galConj_mul_self
    set R := (EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep with hR
    have hne : (⟨Finsupp.single (⟨-((ℓ : ℤ) - 1), hSs⟩ : WtIdx (suppP ℓ)) (1 : (Qi : Type)),
        by exact single_mem_wtComp (⟨-((ℓ : ℤ) - 1), hSs⟩ : WtIdx (suppP ℓ)) 1⟩ :
          R.M (vtxQ SqrtNegOneExt.qi.card_gal 1)) ≠ 0 := by exact wtComp_elt_ne_zero hSs
    obtain ⟨b, hb0, hbfix⟩ := exists_fixed_ne_zero (V := R.M (vtxQ SqrtNegOneExt.qi.card_gal 1)) hne (R.φ' galConj hfix)
      (fun a m => R.φ'_smul galConj hfix a m)
      (fun m => by
        have h := R.φ'_inv galConj hfix (by rw [hinvc]; exact hfix) m
        rwa [R.φ'_congr hinvc (by rw [hinvc]; exact hfix) hfix] at h)
    exact ⟨b, hb0, (R.sigma_mk_eq_iff hfix _ b).mpr hbfix⟩

/-- **`RQ2-6.03-C8` (second display)** — the diagram of `P^∨_{ℓ,ε}`, with the horizontal arrows
reversed: the two edges **into** `⋆` are isomorphisms and the two edges **out of** `⋆` are zero.

@census    none (auxiliary; discharges the second half of census clause `RQ2-6.03-C8`)
@source    ex:principalseries
@clauses   RQ2-6.03-C8
@imports   none
@divergence none -/
theorem Pdual_quiverRep_eq :
    Module.finrank (Qi : Type)
      ((EQObj hℓ (Pdual ℓ ε hℓ hε hpe)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 0)) = 1 ∧
    Module.finrank (Qi : Type)
      ((EQObj hℓ (Pdual ℓ ε hℓ hε hpe)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 1)) = 1 ∧
    Module.finrank (Qi : Type)
      ((EQObj hℓ (Pdual ℓ ε hℓ hε hpe)).toRep.M (vtxQ SqrtNegOneExt.qi.card_gal 2)) = 1 ∧
    Function.Bijective ((EQObj hℓ (Pdual ℓ ε hℓ hε hpe)).toRep.φEdge (0 : Fin 4)) ∧
    Function.Bijective ((EQObj hℓ (Pdual ℓ ε hℓ hε hpe)).toRep.φEdge (2 : Fin 4)) ∧
    (EQObj hℓ (Pdual ℓ ε hℓ hε hpe)).toRep.φEdge (1 : Fin 4) = 0 ∧
    (EQObj hℓ (Pdual ℓ ε hℓ hε hpe)).toRep.φEdge (3 : Fin 4) = 0 := by
  have hℓz : (1 : ℤ) ≤ (ℓ : ℤ) := by exact_mod_cast hℓ
  have hSm : suppP ℓ (-((ℓ : ℤ) + 1)) := by simp only [suppP]; omega
  have hSs : suppP ℓ (-((ℓ : ℤ) - 1)) := by simp only [suppP]; omega
  have hSp : suppP ℓ ((ℓ : ℤ) + 1) := by simp only [suppP]; omega
  have hSt : suppP ℓ ((ℓ : ℤ) - 1) := by simp only [suppP]; omega
  -- the dual's two numbers are the mirror image of `P`'s: the wall has moved to `ℓ-1`
  have hwall : scalF ℓ ((ℓ : ℤ) - 1) = 0 := by simp only [scalF_apply]; push_cast; ring
  have hstep : scalF ℓ (-((ℓ : ℤ) + 1)) = (ℓ : ℚ) := by simp only [scalF_apply]; push_cast; ring
  have hstepne : (((scalF ℓ (-((ℓ : ℤ) + 1)) : ℚ) : (Qi : Type))) ≠ 0 := by
    rw [hstep]
    have hq : ((ℓ : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact_mod_cast fun h => hq (by exact_mod_cast h)
  refine ⟨wtComp_finrank hSm, wtComp_finrank hSs, wtComp_finrank hSp, ?_, ?_, ?_, ?_⟩
  · -- `φ_{a_-} = X : M(−) → M(⋆)`, scalar `x(-(ℓ+1)) = ℓ ≠ 0`
    refine wtRestrict_bijective_of_scalar (S := suppP ℓ) hSm hSs _
      (fun _ hv => Split.x_mem (Q := (qiSetupOf (Pdual ℓ ε hℓ hε hpe))) (m := -((ℓ : ℤ) + 1))
        (n := -((ℓ : ℤ) - 1)) (by ring) hv) hstepne fun a => ?_
    show wtX (suppP ℓ) (scalF ℓ) (Finsupp.single _ a) = _
    rw [wtX_single_eq (S := suppP ℓ) (x := scalF ℓ) (i := ⟨-((ℓ : ℤ) + 1), hSm⟩)
      (j := ⟨-((ℓ : ℤ) - 1), hSs⟩) (by show -((ℓ : ℤ) - 1) = -((ℓ : ℤ) + 1) + 2; ring) a]
  · -- `φ_{a_+} = X⋆⁻¹ ∘ Y : M(+) → M(⋆)`; `Y`'s scalar at `ℓ+1` is `ℓ ≠ 0` and `X⋆⁻¹` is
    -- invertible, its inverse being `X⋆` (`Split.xStar_xStarInv`)
    refine wtBijective_of_injective (S := suppP ℓ) hSp hSs ?_
    refine wtRestrict_injective (S := suppP ℓ) hSp
      (f := (((qiSetupOf (Pdual ℓ ε hℓ hε hpe)).starInverses hℓ).xStarInv).comp
        (qiSetupOf (Pdual ℓ ε hℓ hε hpe)).Y)
      (fun _ hv => ((qiSetupOf (Pdual ℓ ε hℓ hε hpe)).starInverses hℓ).xStarInv_mem
        (Split.y_mem (Q := (qiSetupOf (Pdual ℓ ε hℓ hε hpe))) (m := (ℓ : ℤ) + 1) (n := (ℓ : ℤ) - 1)
          (by ring) hv)) fun a ha => ?_
    have ha' : (((qiSetupOf (Pdual ℓ ε hℓ hε hpe)).starInverses hℓ).xStarInv)
        ((qiSetupOf (Pdual ℓ ε hℓ hε hpe)).Y
          (Finsupp.single (⟨(ℓ : ℤ) + 1, hSp⟩ : WtIdx (suppP ℓ)) a)) = 0 := ha
    have hY : (qiSetupOf (Pdual ℓ ε hℓ hε hpe)).Y
        (Finsupp.single (⟨(ℓ : ℤ) + 1, hSp⟩ : WtIdx (suppP ℓ)) a)
          = Finsupp.single (⟨(ℓ : ℤ) - 1, hSt⟩ : WtIdx (suppP ℓ))
            (((scalF ℓ (-((ℓ : ℤ) + 1)) : ℚ) : (Qi : Type)) * a) := by
      show wtY (suppP ℓ) (scalF ℓ) (Finsupp.single _ a) = _
      rw [wtY_single_eq (S := suppP ℓ) (x := scalF ℓ) (i := ⟨(ℓ : ℤ) + 1, hSp⟩)
        (j := ⟨(ℓ : ℤ) - 1, hSt⟩) (by show (ℓ : ℤ) - 1 = ((ℓ : ℤ) + 1) - 2; ring) a]
    rw [hY] at ha'
    -- `X⋆` undoes `X⋆⁻¹` on `M_{ℓ-1}`, so the argument itself was zero
    have hz := Split.xStar_xStarInv (Q := (qiSetupOf (Pdual ℓ ε hℓ hε hpe)))
      ((qiSetupOf (Pdual ℓ ε hℓ hε hpe)).starInverses hℓ)
      (Finsupp.single (⟨(ℓ : ℤ) - 1, hSt⟩ : WtIdx (suppP ℓ))
        (((scalF ℓ (-((ℓ : ℤ) + 1)) : ℚ) : (Qi : Type)) * a))
      (single_mem_wtComp (⟨(ℓ : ℤ) - 1, hSt⟩ : WtIdx (suppP ℓ))
        (((scalF ℓ (-((ℓ : ℤ) + 1)) : ℚ) : (Qi : Type)) * a))
    rw [ha', map_zero] at hz
    exact (mul_eq_zero.mp (Finsupp.single_eq_zero.mp hz.symm)).resolve_left hstepne
  · -- `φ_{b_-} = Y : M(⋆) → M(−)`: the dual's lowering scalar at `ℓ-1` is `0`
    refine wtRestrict_eq_zero (S := suppP ℓ) hSs (m := -((ℓ : ℤ) + 1))
      (fun _ hv => Split.y_mem (Q := (qiSetupOf (Pdual ℓ ε hℓ hε hpe))) (m := -((ℓ : ℤ) - 1))
        (n := -((ℓ : ℤ) + 1)) (by ring) hv) fun a => ?_
    show wtY (suppP ℓ) (scalF ℓ) (Finsupp.single _ a) = 0
    rw [wtY_single_eq (S := suppP ℓ) (x := scalF ℓ) (i := ⟨-((ℓ : ℤ) - 1), hSs⟩)
      (j := ⟨-((ℓ : ℤ) + 1), hSm⟩) (by show -((ℓ : ℤ) + 1) = -((ℓ : ℤ) - 1) - 2; ring) a]
    show Finsupp.single _ (((scalF ℓ (-(-((ℓ : ℤ) - 1))) : ℚ) : (Qi : Type)) * a) = 0
    rw [neg_neg, hwall, Rat.cast_zero, zero_mul, Finsupp.single_zero]
  · -- `φ_{b_+} = X ∘ X⋆ : M(⋆) → M(+)`: `X⋆` lands on `M_{ℓ-1}`, where `X`'s scalar is `0`
    refine wtRestrict_eq_zero (S := suppP ℓ) hSs (m := (ℓ : ℤ) + 1)
      (f := ((qiSetupOf (Pdual ℓ ε hℓ hε hpe)).X).comp (Split.xStar (qiSetupOf (Pdual ℓ ε hℓ hε hpe))))
      (fun _ hv => Split.x_mem (Q := (qiSetupOf (Pdual ℓ ε hℓ hε hpe))) (m := (ℓ : ℤ) - 1)
        (n := (ℓ : ℤ) + 1) (by ring)
        (Split.xStar_mem (Q := (qiSetupOf (Pdual ℓ ε hℓ hε hpe))) (m := -((ℓ : ℤ) - 1))
          (n := (ℓ : ℤ) - 1) (by ring) hℓ hv)) fun a => ?_
    have hmem : Split.xStar (qiSetupOf (Pdual ℓ ε hℓ hε hpe))
        (Finsupp.single (⟨-((ℓ : ℤ) - 1), hSs⟩ : WtIdx (suppP ℓ)) a)
          ∈ wtComp (suppP ℓ) ((ℓ : ℤ) - 1) :=
      Split.xStar_mem (Q := (qiSetupOf (Pdual ℓ ε hℓ hε hpe))) (m := -((ℓ : ℤ) - 1)) (n := (ℓ : ℤ) - 1)
        (by ring) hℓ (single_mem_wtComp (⟨-((ℓ : ℤ) - 1), hSs⟩ : WtIdx (suppP ℓ)) a)
    obtain ⟨b, hb⟩ := exists_single_of_mem_wtComp (S := suppP ℓ) hSt hmem
    show (qiSetupOf (Pdual ℓ ε hℓ hε hpe)).X (Split.xStar (qiSetupOf (Pdual ℓ ε hℓ hε hpe))
      (Finsupp.single (⟨-((ℓ : ℤ) - 1), hSs⟩ : WtIdx (suppP ℓ)) a)) = 0
    rw [hb]
    show wtX (suppP ℓ) (scalF ℓ) (Finsupp.single _ b) = 0
    rw [wtX_single_eq (S := suppP ℓ) (x := scalF ℓ) (i := ⟨(ℓ : ℤ) - 1, hSt⟩)
      (j := ⟨(ℓ : ℤ) + 1, hSp⟩) (by show (ℓ : ℤ) + 1 = ((ℓ : ℤ) - 1) + 2; ring) b]
    show Finsupp.single _ (((scalF ℓ ((ℓ : ℤ) - 1) : ℚ) : (Qi : Type)) * b) = 0
    rw [hwall, Rat.cast_zero, zero_mul, Finsupp.single_zero]

/-- **`RQ2-6.03-C9`, `C10`** — the étale `ℚ`-species representation attached to `P_{ℓ,ε}`:
`W_{⋆} = ℚ` and `W_{±} = ℚ[√-1]` (`C9`), with `f_{{⋆},{±}}` the **non-zero** structure map and
`f_{{±},{⋆}} = 0` (`C10`, as corrected by `F-S9-1`).

@census    none (auxiliary; discharges census clauses `RQ2-6.03-C9`, `RQ2-6.03-C10`)
@source    ex:principalseries
@clauses   RQ2-6.03-C9, RQ2-6.03-C10
@imports   none
@divergence JUSTIFIED_REFORMULATION (the identification, disclosed).  The direction is **not** a
divergence: `census-v1.8`'s `RQ2-6.03-C10`, as corrected at revision r11 under the author's ruling
(`AN-43`, CLOSED), reads "for `P_{ℓ,ε}`, `f_{{⋆},{±}} : ℚ ⊗_ℚ ℚ[√-1] → ℚ[√-1]` is the canonical
INCLUSION `ℚ → ℚ[√-1]`, corresponding to the non-zero maps `φ_{b_±}`, and `f_{{±},{⋆}} = 0`",
which is what the two map conjuncts below say.

What *is* reformulated is "**is** the canonical inclusion".  `W_{⋆}` is one-dimensional over `ℚ`
and `W_{±}` one-dimensional over `ℚ[√-1]`, so the source of `f_{{⋆},{±}}` — the balanced product
`W_⋆ ⊗_ℚ M_{⋆,±}` — is two-dimensional over `ℚ`, as is its target; "the canonical inclusion" names
that map only through the identifications the source introduces "after choosing suitable bases",
and it pins none of them.  It is therefore rendered as **bijectivity**, which for these two spaces
is exactly the content of "is the inclusion" modulo the choice of bases, together with the two
dimension counts (`-C9`).  `Function.Bijective`, not merely `Surjective`: source and target have
equal finite dimension here, so the sharper form is the true one. -/
theorem P_speciesRep_eq :
    Module.finrank ℚ (((RationalQuiver.FFunctor GQ).obj
      (EQObj hℓ (P ℓ ε hℓ hε hpe))).W starNode) = 1 ∧
    Module.finrank ℚ (((RationalQuiver.FFunctor GQ).obj
      (EQObj hℓ (P ℓ ε hℓ hε hpe))).W pmNode) = 2 ∧
    ((RationalQuiver.FFunctor GQ).obj
      (EQObj hℓ (P ℓ ε hℓ hε hpe))).f pmNode starNode = 0 ∧
    Function.Bijective (((RationalQuiver.FFunctor GQ).obj
      (EQObj hℓ (P ℓ ε hℓ hε hpe))).f starNode pmNode) := by
  obtain ⟨hd0, hd1, hd2, he0, he2, hb1, hb3, -, -, -⟩ := P_quiverRep_eq ℓ ε hℓ hε hpe
  have hpmfr : Module.finrank (Qi : Type)
      ((EQObj hℓ (P ℓ ε hℓ hε hpe)).toRep.M (GQ.vertexRep pmNode)) = 1 := by
    rcases vertexRep_pmNode with h | h
    · rw [h]; exact hd0
    · rw [h]; exact hd2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [finrank_W_star]; exact hd1
  · rw [finrank_W_pm, hpmfr]
  · exact edgeDescentOf_eq_zero_of_edgeSet (Γ := GQ) _ pmNode starNode (fun e => by
      rcases edgeSet_pm_star e with h | h
      · rw [h]; exact he0
      · rw [h]; exact he2)
  · exact species_star_pm_bijective _ hd1 hpmfr (fun e => by
      rcases edgeSet_star_pm e with h | h
      · rw [h]; exact hb1.1
      · rw [h]; exact hb3.1)

/-- **`RQ2-6.03-C11`** — the species representation attached to `P^∨_{ℓ,ε}`: the same two spaces,
with `f_{{±},{⋆}}` the **non-zero** structure map (the trace, up to identification) and
`f_{{⋆},{±}} = 0`.

@census    none (auxiliary; discharges census clause `RQ2-6.03-C11`)
@source    ex:principalseries
@clauses   RQ2-6.03-C11
@imports   none
@divergence JUSTIFIED_REFORMULATION (the identification, disclosed), mirroring `P_speciesRep_eq`.
Again the direction is not a divergence: `census-v1.8`'s `RQ2-6.03-C11`, as corrected at r11
(`AN-43`), reads "for the dual, `f_{{±},{⋆}} : ℚ[√-1] ⊗_{ℚ[√-1]} ℚ[√-1] → ℚ` is the TRACE map
`tr_{ℚ[√-1]/ℚ}`, corresponding to the non-zero maps `φ_{a_±}`, and `f_{{⋆},{±}} = 0`".  "Is the
trace" is rendered as **surjectivity** — here, and unlike `P`'s inclusion, the sharper `Bijective`
would be **false**: the source is two-dimensional over `ℚ` and the target one-dimensional, so the
trace cannot be injective.  Surjectivity plus the two dimension counts pins the map up to a
`ℚ[√-1]`-scalar, which is exactly "is the trace" modulo the basis choice the source leaves open. -/
theorem Pdual_speciesRep_eq :
    Module.finrank ℚ (((RationalQuiver.FFunctor GQ).obj
      (EQObj hℓ (Pdual ℓ ε hℓ hε hpe))).W starNode) = 1 ∧
    Module.finrank ℚ (((RationalQuiver.FFunctor GQ).obj
      (EQObj hℓ (Pdual ℓ ε hℓ hε hpe))).W pmNode) = 2 ∧
    ((RationalQuiver.FFunctor GQ).obj
      (EQObj hℓ (Pdual ℓ ε hℓ hε hpe))).f starNode pmNode = 0 ∧
    Function.Surjective (((RationalQuiver.FFunctor GQ).obj
      (EQObj hℓ (Pdual ℓ ε hℓ hε hpe))).f pmNode starNode) := by
  obtain ⟨hd0, hd1, hd2, hb0, hb2, he1, he3⟩ := Pdual_quiverRep_eq ℓ ε hℓ hε hpe
  have hpmfr : Module.finrank (Qi : Type)
      ((EQObj hℓ (Pdual ℓ ε hℓ hε hpe)).toRep.M (GQ.vertexRep pmNode)) = 1 := by
    rcases vertexRep_pmNode with h | h
    · rw [h]; exact hd0
    · rw [h]; exact hd2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [finrank_W_star]; exact hd1
  · rw [finrank_W_pm, hpmfr]
  · exact edgeDescentOf_eq_zero_of_edgeSet (Γ := GQ) _ starNode pmNode (fun e => by
      rcases edgeSet_star_pm e with h | h
      · rw [h]; exact he1
      · rw [h]; exact he3)
  · exact species_pm_star_surjective _ hd1 hpmfr (fun e => by
      rcases edgeSet_pm_star e with h | h
      · rw [h]; exact hb0.1
      · rw [h]; exact hb2.1)

end Statements

end RationalQuivers.Examples
