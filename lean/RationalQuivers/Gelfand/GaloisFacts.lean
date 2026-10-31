module

public import Mathlib.FieldTheory.Galois.Basic
public import RationalQuivers.HC.Sl2

@[expose] public section

/-!
# The Galois facts of `ℚ[√-1]/ℚ`, in-tree (commission `C-M2-1`)

`HC.Qi := IntermediateField.adjoin ℚ {Complex.I}` (`HC/Sl2.lean`, stage S7) is the concrete field
`ℚ(i) = ℚ[√-1]` every §5 statement is written over.  Until this module, the three standard facts

* `FiniteDimensional ℚ ℚ[√-1]`,
* `IsGalois ℚ ℚ[√-1]`,
* `#Gal(ℚ[√-1]/ℚ) = 2`,

were carried by **every** `RQ-5.05`–`RQ-5.09` claimant as binders — two instance-implicit, one
explicit (`hcard`) — disclosed in each `@divergence` and in `stages/S8/DESIGN-NOTES.md` §3.2 as
"true and standard, not synthesizable at the pin; establishing them is G4 work".  They were
therefore invisible to `rqaudit hyps` (they are not `Imports.*` fields), which is exactly finding
**`F-M2-02`** of the M2 primary audit (`workflow/audit/M2/FINAL_AUDIT.md` §5.1 item 4).

This module establishes all three from mathlib at the pin, so the binders can be dropped and the
claimants become unconditional in this respect.  See `stages/S8/DESIGN-NOTES.md` §25 (renumbered on
merge into `main` from this commission's own working `§24`, which collided with M2 process repair
round 1's own `§24`, `F-M2-07`, landed the same day — `m2-merge-resolver`).

## Provenance

The `FiniteDimensional`/`finrank` half is the M2 primary audit's own scratch probe
`workflow/audit/M2/probe/GaloisProbe.lean` (read it with
`git show audit/M2-halfB:workflow/audit/M2/probe/GaloisProbe.lean`; author `g8-m2-auditor`), reused here with attribution and unchanged in substance: `Qi.isIntegral_I`,
`Qi.finrank_le_two`, `Qi.two_le_finrank`, `Qi.finrank_eq_two` and `Qi.card_gal` are its (1)–(4).
What the probe did **not** attempt inside its time box — `IsGalois ℚ ℚ[√-1]` itself, which it
scoped to `IsGalois.of_separable_splitting_field` with `X² + 1` — is `Qi.instIsGalois` below, and
the route that worked is shorter than the scoped one: mathlib's
`Algebra.IsQuadraticExtension.isGalois` turns `finrank = 2` plus separability straight into
`IsGalois`, and separability over `ℚ` is found by instance search
(`PerfectField.ofCharZero` → `Algebra.IsAlgebraic.isSeparable_of_perfectField`).

## Main results

* `Qi.instFiniteDimensional` — `FiniteDimensional ℚ ℚ[√-1]`, an instance.
* `Qi.finrank_eq_two` — `Module.finrank ℚ ℚ[√-1] = 2`.
* `Qi.instIsQuadraticExtension` — `Algebra.IsQuadraticExtension ℚ ℚ[√-1]`, an instance.
* `Qi.instIsGalois` — `IsGalois ℚ ℚ[√-1]`, an instance.
* `Qi.card_gal` — `Nat.card (ℚ[√-1] ≃ₐ[ℚ] ℚ[√-1]) = 2`, i.e. the former `hcard` binder.

## Implementation notes

The module sits in `Gelfand/` (stage **S8** by `workflow/instrument/STAGE-MAP.tsv`'s
`RationalQuivers.Gelfand` prefix row) rather than beside `Qi` in `HC/Sl2.lean` (stage S7): the
consumers are all S8's, and adding content to S7's module set would amend a second frozen stage's
packet for no gain.  It was imported by `Gelfand/Category.lean`, the root of S8's own import DAG,
so the three instances were in scope for every S8 module.

*(2026-10-21, O-V2-6 round 2.)*  The paragraph above describes v1.  `Gelfand/Category.lean` was
deleted at v2 WP-13 (`9c6b193`).  This module has been stage T2 since the perimeter amendment T2-a1
of 2026-10-18 (`workflow/v2/instrument/STAGE-MAP.tsv`), and today `Gelfand/QuadraticExtension.lean`
imports it.
-/

namespace RationalQuivers.Gelfand

open RationalQuivers.HC Polynomial

/-- `i` is integral over `ℚ`, witnessed by `X² + 1`.

@census none (auxiliary; commission `C-M2-1`, after `audit/M2` `probe/GaloisProbe.lean` (1)) -/
theorem Qi.isIntegral_I : IsIntegral ℚ Complex.I :=
  ⟨X ^ 2 + C 1, monic_X_pow_add_C 1 two_ne_zero, by simp⟩

/-- `ℚ[√-1]/ℚ` is finite. — `IntermediateField.adjoin.finiteDimensional` at `Qi.isIntegral_I`.

@census none (auxiliary; commission `C-M2-1`, after `audit/M2` `probe/GaloisProbe.lean` (1)) -/
noncomputable instance Qi.instFiniteDimensional : FiniteDimensional ℚ (Qi : Type) :=
  IntermediateField.adjoin.finiteDimensional Qi.isIntegral_I

/-- `[ℚ[√-1] : ℚ] ≤ 2`, from `minpoly ℚ i ∣ X² + 1`.

@census none (auxiliary; commission `C-M2-1`, after `audit/M2` `probe/GaloisProbe.lean` (2)) -/
theorem Qi.finrank_le_two : Module.finrank ℚ (Qi : Type) ≤ 2 := by
  rw [IntermediateField.adjoin.finrank Qi.isIntegral_I]
  have h := minpoly.min ℚ Complex.I (monic_X_pow_add_C (R := ℚ) 1 two_ne_zero)
    (by simp : aeval Complex.I (X ^ 2 + C 1 : ℚ[X]) = 0)
  have h2 : (X ^ 2 + C 1 : ℚ[X]).natDegree = 2 := by
    rw [natDegree_X_pow_add_C]
  calc (minpoly ℚ Complex.I).natDegree ≤ (X ^ 2 + C 1 : ℚ[X]).natDegree :=
        natDegree_le_natDegree h
    _ = 2 := h2

/-- `2 ≤ [ℚ[√-1] : ℚ]`: `1` and `i` are `ℚ`-linearly independent in `ℚ[√-1]`.

@census none (auxiliary; commission `C-M2-1`, after `audit/M2` `probe/GaloisProbe.lean` (3)) -/
theorem Qi.two_le_finrank : 2 ≤ Module.finrank ℚ (Qi : Type) := by
  have hI : Complex.I ∈ (Qi : IntermediateField ℚ ℂ) := IntermediateField.subset_adjoin ℚ _ rfl
  have hli : LinearIndependent ℚ ![(1 : (Qi : Type)), ⟨Complex.I, hI⟩] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := congrArg (fun z : (Qi : Type) => (z : ℂ)) hst
    simp only [IntermediateField.coe_zero] at h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp at hre him
    exact ⟨by exact_mod_cast hre, by exact_mod_cast him⟩
  simpa using hli.fintype_card_le_finrank

/-- `[ℚ[√-1] : ℚ] = 2`.

@census none (auxiliary; commission `C-M2-1`, after `audit/M2` `probe/GaloisProbe.lean` (2)+(3)) -/
theorem Qi.finrank_eq_two : Module.finrank ℚ (Qi : Type) = 2 :=
  le_antisymm Qi.finrank_le_two Qi.two_le_finrank

/-- `ℚ[√-1]/ℚ` is a quadratic extension — `Module.Free` (a field) of `finrank` `2`.

@census none (auxiliary; commission `C-M2-1`) -/
noncomputable instance Qi.instIsQuadraticExtension :
    Algebra.IsQuadraticExtension ℚ (Qi : Type) where
  finrank_eq_two' := Qi.finrank_eq_two

/-- **`ℚ[√-1]/ℚ` is Galois.**  A quadratic separable extension is Galois
(`Algebra.IsQuadraticExtension.isGalois`); separability over `ℚ` is automatic in characteristic `0`
(`PerfectField.ofCharZero`, `Algebra.IsAlgebraic.isSeparable_of_perfectField`), and quadraticity is
`Qi.instIsQuadraticExtension`.  This is the one of the three facts the M2 audit's probe did not
attempt (`FINAL_AUDIT.md` §5.1 item 4, finding `F-M2-02`).

@census none (auxiliary; commission `C-M2-1`) -/
noncomputable instance Qi.instIsGalois : IsGalois ℚ (Qi : Type) := inferInstance

/-- **`#Gal(ℚ[√-1]/ℚ) = 2`** — the former `hcard` binder of `RQ-5.05`, `RQ-5.06`, `RQ-5.07` and
`RQ-5.09`, now a theorem: `IsGalois.card_aut_eq_finrank` at `Qi.finrank_eq_two`.

@census none (auxiliary; commission `C-M2-1`, after `audit/M2` `probe/GaloisProbe.lean` (4)) -/
theorem Qi.card_gal : Nat.card ((Qi : Type) ≃ₐ[ℚ] (Qi : Type)) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, Qi.finrank_eq_two]

end RationalQuivers.Gelfand
