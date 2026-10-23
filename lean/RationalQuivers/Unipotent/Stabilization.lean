import Mathlib.Algebra.Order.Floor.Div
import RationalQuivers.Unipotent.Twist

/-!
# Unipotent stabilization

Formalizes §4.1 of `latex/rational_quivers.tex` (census `RQ2-4.01` – `RQ2-4.04`).

## Main definitions / results
* `RationalQuivers.Unipotent.stabilizationStep` — one step
  `φ̃_± = ½(φ_± + (φ_∓^τ)^{-1})` (`eq:unipotentstabilizationiteration`, clause `RQ2-4.01-C1`).
* `RationalQuivers.Unipotent.nilpotency_stabilizationStep` — Proposition
  `prop:unipotentstabilization` (census `RQ2-4.01`): the step halves the nilpotency exponent,
  `ẽ ≤ ⌈e/2⌉`; with `stabilizationStep_bijective` and the two addenda.
* `RationalQuivers.Unipotent.stabilizationSeq` — the iteration `φ^{(k)}_±` of
  `cor:unipotentstabilization` (clause `RQ2-4.02-H2`).
* `RationalQuivers.Unipotent.stabilization_spec` — Corollary `cor:unipotentstabilization`
  (census `RQ2-4.02`): the sequence is eventually constant and reaches `eq:conjugateinverse`.
* `RationalQuivers.Unipotent.stabilization` — Definition `def:unipotentstabilization`
  (census `RQ2-4.03`), the unipotent stabilization `φ^{(∞)}_±`.
* `RationalQuivers.Unipotent.stabilization_symm` — Remark `rmk:unipotentstabilization`
  (census `RQ2-4.04`).

## Implementation notes

**`⌈e/2⌉`.**  The source's `⌈e/2⌉` is mathlib's ceiling division `e ⌈/⌉ 2`
(`Nat.instCeilDiv`, `Nat.ceilDiv_eq_add_pred_div : a ⌈/⌉ b = (a + b - 1) / b`), used with
mathlib's own spelling per `CONVENTIONS.md` §6 ladder step 1.  The bound is stated
**quantitatively**, as clause `RQ2-4.01-C4` demands: `ñ ^ (e ⌈/⌉ 2) = 0`, never "`ñ` is nilpotent
for some exponent" — the halving is the whole content of `prop:unipotentstabilization` and the
reason `cor:unipotentstabilization` terminates.

**Why the recursion can be written literally.**  `φ^{(k+1)}_±` is defined from `(φ^{(k),τ}_∓)^{-1}`,
whose existence is only established afterwards (clause `RQ2-4.02-C5`, the post-freeze verifier
addition).  `linInv` (`Unipotent/Nilpotent.lean`) is the junk-valued inverse that lets the
recursion be *defined* in the source's own shape, with invertibility proved separately as
`stabilizationSeq_bijective`.

**The standing hypotheses.**  `L/K` quadratic (clause `RQ2-4.01-H1`, the binder `hquad`) and
`τ ≠ 1` (clause `RQ2-4.01-H3`, the binder `hτne`) enter the constructions only through
`τ * τ = 1` (`aut_mul_self`), which is what makes `W_∓^{ττ} = W_∓` and hence `φ_-^τ ∘ φ_+` an
endomorphism of `W_+`.  Every census-carrying declaration below takes `hquad`, `τ` and `hτne` as
**explicit arguments** and applies `aut_mul_self` itself, so that each appears in its elaborated
signature (`CONVENTIONS.md` §3); nothing is left to a `variable` block that Lean would prune.

**`hgal` is an extra binder, and is disclosed as one** (G2 verification finding **C-2**).  Each of
those declarations also takes `hgal : IsGalois K L`, which is *not* clause `RQ2-4.01-H1`: the
census text of H1 is only "L/K is a QUADRATIC field extension".  `IsGalois K L` follows from H1
and H2 — a degree-2 extension is normal, and separable because `char K ≠ 2` — so every
configuration the source admits satisfies it and the theorems cover exactly the source's class;
`census/NOTATION.md` §3 also reads the `Gal(L/K)` that §4 itself writes as the Galois group of a
Galois extension.  It is carried as a hypothesis rather than derived because mathlib has no
one-step "degree 2 and `char ≠ 2` ⇒ Galois" at the pinned revision, and deriving it (normality of
a degree-2 extension plus separability in `char ≠ 2`) is a mathlib-side project this stage does
not undertake.  Each affected declaration repeats the disclosure in its `@divergence` field, so
that the correspondence table carries it too.

**Symmetry for free.**  `stabilizationSeq` is a function of the *pair* `(φ_+, φ_-)` and of nothing
that distinguishes the two signs, so `rmk:unipotentstabilization` (census `RQ2-4.04`) is the
literal statement that transposing the arguments transposes the output — no `HEq`, no transport.
-/

universe u v

open scoped TensorProduct

namespace RationalQuivers.Unipotent

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {WK : Type v} [AddCommGroup WK] [Module K WK]

/-! ## One stabilization step -/

/-- **One unipotent stabilization step** (`eq:unipotentstabilizationiteration`, clause
`RQ2-4.01-C1`):
`φ̃_+ := ½(φ_+ + (φ_-^τ)^{-1}) : W_+ → W_-^τ`.

`φ_-^τ` is `twistConj`, the source's `τ ∘ φ_- ∘ τ^{-1}`; the inverse is the junk-valued `linInv`,
which agrees with the honest inverse whenever `φ_-^τ` is an isomorphism — which it is under the
hypotheses of `prop:unipotentstabilization`.  Applying the same definition with the two arguments
transposed gives `φ̃_-`.

@census    none (auxiliary; discharges clause `RQ2-4.01-C1` of `RQ2-4.01`)
@source    prop:unipotentstabilization
@clauses   RQ2-4.01-C1
@imports   none
@divergence none
-/
noncomputable def stabilizationStep (h2 : (2 : K) ≠ 0) {τ : Gal(L/K)} (hτ : τ * τ = 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) : Wp →ₗ[L] twist τ Wm :=
  half (two_ne_zero_of_base (L := L) h2) • (φp + linInv (twistConj hτ φm))

theorem stabilizationStep_def (h2 : (2 : K) ≠ 0) {τ : Gal(L/K)} (hτ : τ * τ = 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) :
    stabilizationStep h2 hτ φp φm
      = half (two_ne_zero_of_base (L := L) h2) • (φp + linInv (twistConj hτ φm)) := rfl

/-! ### Bridges between the pair picture and the endomorphism algebra of `W₊` -/

section Bridges

variable (h2 : (2 : K) ≠ 0) {τ : Gal(L/K)} (hτ : τ * τ = 1)
  {Wp Wm : Submodule L (L ⊗[K] WK)}

/-- The conjugate `φ̃_-^τ` of the minus-step is the plus-step of the conjugated pair.

This is the observation that makes §4.1 a statement about a *single* pair `(F, H)` of mutually
composable maps `F : W₊ → W_-^τ`, `H = φ_-^τ : W_-^τ → W₊`: conjugation exchanges the two
recursions (`twistConj_linInv_twistConj`).

@census none
-/
theorem twistConj_stabilizationStep (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)
    (hp : HasInverse φp) :
    twistConj hτ (stabilizationStep h2 hτ φm φp)
      = half (two_ne_zero_of_base (L := L) h2) • (twistConj hτ φm + linInv φp) := by
  rw [stabilizationStep, twistConj_smul, twistConj_add,
    aut_half (two_ne_zero_of_base (L := L) h2) τ, twistConj_linInv_twistConj hτ φp hp]

/-- The plus-step factors through `W₊`: `½(φ_+ + (φ_-^τ)^{-1}) = ½ φ_+ ∘ (1 + u^{-1})` for
`u = φ_-^τ ∘ φ_+`.  This is what makes clause `RQ2-4.01-C2` (the step is again an isomorphism)
a consequence of `char ≠ 2`: `1 + u^{-1} = 2 + nilpotent`.

@census none
-/
theorem stabilizationStep_eq_comp (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)
    (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm)) :
    stabilizationStep h2 hτ φp φm
      = half (two_ne_zero_of_base (L := L) h2) •
          (φp.comp (1 + Ring.inverse ((twistConj hτ φm).comp φp))) := by
  rw [stabilizationStep]
  congr 1
  rw [LinearMap.comp_add, Module.End.one_eq_id, LinearMap.comp_id, ring_inverse_eq_linInv,
    linInv_comp_eq hm hp, ← LinearMap.comp_assoc, hp.comp_linInv, LinearMap.id_comp]

/-- The composite of the two stabilized maps, in `End(W₊)`: `¼(u + 1 + 1 + u^{-1})`. -/
theorem stabilizationStep_comp (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)
    (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm)) :
    (twistConj hτ (stabilizationStep h2 hτ φm φp)).comp (stabilizationStep h2 hτ φp φm)
      = (half (two_ne_zero_of_base (L := L) h2) * half (two_ne_zero_of_base (L := L) h2)) •
          ((twistConj hτ φm).comp φp + 1 + 1
            + Ring.inverse ((twistConj hτ φm).comp φp)) := by
  rw [twistConj_stabilizationStep h2 hτ φp φm hp, stabilizationStep, LinearMap.smul_comp,
    LinearMap.comp_smul, smul_smul]
  congr 1
  rw [LinearMap.add_comp, LinearMap.comp_add, LinearMap.comp_add, hm.comp_linInv,
    hp.linInv_comp, ← linInv_comp_eq hm hp, ← ring_inverse_eq_linInv, Module.End.one_eq_id]
  abel

/-- A linear equivalence has a two-sided inverse. -/
theorem hasInverse_of_linearEquiv {U V : Submodule L (L ⊗[K] WK)} (f : U ≃ₗ[L] V) :
    HasInverse (f : U →ₗ[L] V) :=
  ⟨(f.symm : V →ₗ[L] U), by ext x; simp, by ext x; simp⟩

include h2 in
/-- `1 + u^{-1}` is a unit when `u = 1 + nilpotent`: it is `2 + nilpotent`, and `2` is invertible
because `char ≠ 2` (clause `RQ2-4.01-H2`).

@census none
-/
theorem isUnit_one_add_inverse (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)
    (n : Module.End L Wp) (hn : (twistConj hτ φm).comp φp = 1 + n) (hnil : IsNilpotent n) :
    IsUnit ((1 : Module.End L Wp) + Ring.inverse ((twistConj hτ φm).comp φp)) := by
  have hL : (2 : L) ≠ 0 := two_ne_zero_of_base (L := L) h2
  have hu : IsUnit ((twistConj hτ φm).comp φp) := by
    rw [hn]; exact isUnit_one_add_of_isNilpotent hnil
  have hinvu : IsUnit (Ring.inverse ((twistConj hτ φm).comp φp)) := by
    obtain ⟨u, hu'⟩ := hu
    rw [← hu', Ring.inverse_unit]
    exact (u⁻¹ : (Module.End L Wp)ˣ).isUnit
  have hsum : IsUnit ((twistConj hτ φm).comp φp + 1) := by
    rw [hn, add_assoc, add_comm n 1, ← add_assoc, one_add_one_eq_two_smul_end]
    exact isUnit_add_of_isNilpotent (isUnit_smul_one_end hL) hnil
      ((Commute.one_right n).smul_right (2 : L)).symm
  have hone : (1 : Module.End L Wp) + Ring.inverse ((twistConj hτ φm).comp φp)
      = Ring.inverse ((twistConj hτ φm).comp φp) * ((twistConj hτ φm).comp φp + 1) := by
    rw [mul_add, mul_one, Ring.inverse_mul_cancel _ hu]
  rw [hone]
  exact hinvu.mul hsum

/-- The conjugated minus-step also factors: `½(φ_-^τ + φ_+^{-1}) = ½ (1 + u^{-1}) ∘ φ_-^τ`. -/
theorem twistConj_stabilizationStep_eq_comp (φp : Wp →ₗ[L] twist τ Wm)
    (φm : Wm →ₗ[L] twist τ Wp) (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm)) :
    twistConj hτ (stabilizationStep h2 hτ φm φp)
      = half (two_ne_zero_of_base (L := L) h2) •
          ((1 + Ring.inverse ((twistConj hτ φm).comp φp)).comp (twistConj hτ φm)) := by
  rw [twistConj_stabilizationStep h2 hτ φp φm hp]
  congr 1
  rw [LinearMap.add_comp, Module.End.one_eq_id, LinearMap.id_comp, ring_inverse_eq_linInv,
    linInv_comp_eq hm hp, LinearMap.comp_assoc, hm.linInv_comp, LinearMap.comp_id]

/-- The conjugated minus-step is invertible, by the same argument as the plus-step. -/
theorem hasInverse_twistConj_stabilizationStep (φp : Wp →ₗ[L] twist τ Wm)
    (φm : Wm →ₗ[L] twist τ Wp) (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm))
    (n : Module.End L Wp) (hn : (twistConj hτ φm).comp φp = 1 + n) (hnil : IsNilpotent n) :
    HasInverse (twistConj hτ (stabilizationStep h2 hτ φm φp)) := by
  have hL : (2 : L) ≠ 0 := two_ne_zero_of_base (L := L) h2
  rw [twistConj_stabilizationStep_eq_comp h2 hτ φp φm hp hm]
  refine HasInverse.smul (HasInverse.comp
    ((hasInverse_iff_isUnit _).mpr (isUnit_one_add_inverse h2 hτ φp φm n hn hnil)) hm) ?_
  rw [half_eq]
  exact inv_ne_zero hL

/-- **Clause `RQ2-4.01-C2` / `RQ2-4.02-C5`, the invertibility of a step.**  The step
`½(φ_+ + (φ_-^τ)^{-1}) = ½ φ_+ ∘ (1 + u^{-1})` is invertible because `1 + u^{-1} = 2 + nilpotent`
is — and *this* is where `char ≠ 2` enters the well-formedness of the recursion.

@census none
-/
theorem hasInverse_stabilizationStep (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)
    (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm)) (n : Module.End L Wp)
    (hn : (twistConj hτ φm).comp φp = 1 + n) (hnil : IsNilpotent n) :
    HasInverse (stabilizationStep h2 hτ φp φm) := by
  have hL : (2 : L) ≠ 0 := two_ne_zero_of_base (L := L) h2
  rw [stabilizationStep_eq_comp h2 hτ φp φm hp hm]
  refine HasInverse.smul (hp.comp ((hasInverse_iff_isUnit _).mpr
    (isUnit_one_add_inverse h2 hτ φp φm n hn hnil))) ?_
  rw [half_eq]
  exact inv_ne_zero hL

/-- The composite `u = φ_-^τ ∘ φ_+` is invertible whenever both factors are. -/
theorem hasInverse_comp (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)
    (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm)) :
    HasInverse ((twistConj hτ φm).comp φp) := hm.comp hp

end Bridges

/-! ## `prop:unipotentstabilization` -/

/-- **Proposition** (`prop:unipotentstabilization`, §4.1 of the source).

Let `L/K` be a quadratic field extension (clause `RQ2-4.01-H1`: `hquad`; the extra binder
`hgal` is disclosed in `@divergence`) with `K` of
characteristic `≠ 2` (clause `RQ2-4.01-H2`: `h2`), let `τ` be the non-trivial element of
`Gal(L/K)` (clause `RQ2-4.01-H3`: `hτne`), let `W_K` be a `K`-vector space and
`W_L = L ⊗_K W_K` with its canonical semi-linear `τ`-action (clause `RQ2-4.01-H4`: the ambient
type and `galoisTwist`), let `W_±` be `L`-subspaces of `W_L` (clause `RQ2-4.01-H5`) and
`φ_± : W_± → W_∓^τ` `L`-linear isomorphisms (clause `RQ2-4.01-H6`) with
`φ_-^τ ∘ φ_+ = 1_{W_+} + n` (`eq:nilpotency`, clause `RQ2-4.01-H7`), `n` nilpotent of exponent
**exactly** `e ≥ 1`, i.e. `n^{e-1} ≠ 0` and `n^e = 0` (clause `RQ2-4.01-H8`).

Then `φ̃_-^τ ∘ φ̃_+ = 1_{W_+} + ñ` (`eq:nilpotencytilde`, clause `RQ2-4.01-C3`) with `ñ` nilpotent
of exponent `ẽ ≤ ⌈e/2⌉ = e ⌈/⌉ 2` (clause `RQ2-4.01-C4`, quantitative).  That `φ̃_+` is again an `L`-linear
isomorphism is `stabilizationStep_bijective` (clause `RQ2-4.01-C2`); the iteration formula itself
is the definition `stabilizationStep` (clause `RQ2-4.01-C1`).

@census    RQ2-4.01
@source    prop:unipotentstabilization
@clauses   RQ2-4.01-H1, RQ2-4.01-H2, RQ2-4.01-H3, RQ2-4.01-H4, RQ2-4.01-H5, RQ2-4.01-H6,
           RQ2-4.01-H7, RQ2-4.01-H8, RQ2-4.01-C3, RQ2-4.01-C4
@imports   none
@divergence EXTRA BINDER, disclosed (G2 finding C-2; not a weakening): `hgal : IsGalois K L`
is an argument here but is **not** clause `RQ2-4.01-H1`, whose text is only "L/K is a QUADRATIC
field extension" (`hquad` is that clause).  `IsGalois` follows from H1 + H2 — degree 2 is normal,
separable since `char K ≠ 2` — so the covered class is exactly the source's; it is a binder only
because mathlib has no one-step lemma for it at the pin.  Argument: module docstring, "The
standing hypotheses".
-/
theorem nilpotency_stabilizationStep (h2 : (2 : K) ≠ 0) (hgal : IsGalois K L)
    (hquad : Module.finrank K L = 2) (τ : Gal(L/K)) (hτne : τ ≠ 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp ≃ₗ[L] twist τ Wm) (φm : Wm ≃ₗ[L] twist τ Wp)
    (n : Module.End L Wp) (e : ℕ) (he : 1 ≤ e)
    (hn : (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)).comp
        (φp : Wp →ₗ[L] twist τ Wm) = 1 + n)
    (hexact : n ^ (e - 1) ≠ 0) (hnilp : n ^ e = 0) :
    ∃ ñ : Module.End L Wp,
      (twistConj (aut_mul_self hgal hquad τ)
            (stabilizationStep h2 (aut_mul_self hgal hquad τ)
              (φm : Wm →ₗ[L] twist τ Wp) (φp : Wp →ₗ[L] twist τ Wm))).comp
          (stabilizationStep h2 (aut_mul_self hgal hquad τ)
            (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)) = 1 + ñ
        ∧ ñ ^ (e ⌈/⌉ 2) = 0 := by
  have hp : HasInverse (φp : Wp →ₗ[L] twist τ Wm) := hasInverse_of_linearEquiv φp
  have hm : HasInverse (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)) :=
    (hasInverse_of_linearEquiv φm).twistConj _
  have hu : IsUnit ((twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)).comp
      (φp : Wp →ₗ[L] twist τ Wm)) := by
    rw [hn]; exact isUnit_one_add_of_isNilpotent ⟨e, hnilp⟩
  have hcom : Commute ((twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)).comp
      (φp : Wp →ₗ[L] twist τ Wm)) n := by
    rw [hn]; exact (Commute.one_left n).add_left (Commute.refl n)
  refine ⟨(half (two_ne_zero_of_base (L := L) h2) * half (two_ne_zero_of_base (L := L) h2)) •
    (Ring.inverse ((twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)).comp
      (φp : Wp →ₗ[L] twist τ Wm)) * (n * n)), ?_, ?_⟩
  · rw [stabilizationStep_comp h2 (aut_mul_self hgal hquad τ) _ _ hp hm]
    exact quarter_avg_of_one_add (two_ne_zero_of_base (L := L) h2) hu hn
  · exact quarter_error_pow (two_ne_zero_of_base (L := L) h2) hu hcom hnilp

/-- Clause `RQ2-4.01-C2`: `φ̃_+ : W_+ → W_-^τ` is again an `L`-linear **isomorphism**.  This is
what makes the next step of `cor:unipotentstabilization` well formed.

@census    none (auxiliary; discharges clause `RQ2-4.01-C2` of `RQ2-4.01`)
@source    prop:unipotentstabilization
@clauses   RQ2-4.01-C2
@imports   none
@divergence EXTRA BINDER, disclosed (G2 finding C-2; not a weakening): `hgal : IsGalois K L`
is an argument here but is **not** clause `RQ2-4.01-H1`, whose text is only "L/K is a QUADRATIC
field extension" (`hquad` is that clause).  `IsGalois` follows from H1 + H2 — degree 2 is normal,
separable since `char K ≠ 2` — so the covered class is exactly the source's; it is a binder only
because mathlib has no one-step lemma for it at the pin.  Argument: module docstring, "The
standing hypotheses".
-/
theorem stabilizationStep_bijective (h2 : (2 : K) ≠ 0) (hgal : IsGalois K L)
    (hquad : Module.finrank K L = 2) (τ : Gal(L/K)) (hτne : τ ≠ 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp ≃ₗ[L] twist τ Wm) (φm : Wm ≃ₗ[L] twist τ Wp)
    (n : Module.End L Wp)
    (hn : (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)).comp
        (φp : Wp →ₗ[L] twist τ Wm) = 1 + n)
    (hnil : IsNilpotent n) :
    Function.Bijective (stabilizationStep h2 (aut_mul_self hgal hquad τ)
      (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)) := by
  have hp : HasInverse (φp : Wp →ₗ[L] twist τ Wm) := hasInverse_of_linearEquiv φp
  have hm : HasInverse (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)) :=
    (hasInverse_of_linearEquiv φm).twistConj _
  exact (hasInverse_stabilizationStep h2 (aut_mul_self hgal hquad τ) _ _ hp hm n hn hnil).bijective

/-! ### The addenda of `prop:unipotentstabilization` -/

/-- In the situation `W_∓^τ = W_±` of the addenda, `φ_+ : W_+ → W_-^τ` **is** an endomorphism of
`W_+`.  This is the identification under which `eq:unipotentcommutators0` and
`eq:unipotentnilpotency0` are equations in `End_L(W_+)`.

@census none
-/
def asEnd {τ : Gal(L/K)} {Wp Wm : Submodule L (L ⊗[K] WK)} (hW : twist τ Wm = Wp)
    (f : Wp →ₗ[L] twist τ Wm) : Module.End L Wp :=
  (LinearEquiv.ofEq _ _ hW).toLinearMap.comp f

/-- In the situation `W_∓^τ = W_±` of the addenda, `φ_-^τ : W_-^τ → W_+` is an endomorphism of
`W_+`.

@census none
-/
def asEndConj {τ : Gal(L/K)} (hτ : τ * τ = 1) {Wp Wm : Submodule L (L ⊗[K] WK)}
    (hW : twist τ Wm = Wp) (f : Wm →ₗ[L] twist τ Wp) : Module.End L Wp :=
  (twistConj hτ f).comp (LinearEquiv.ofEq _ _ hW).symm.toLinearMap

/-! ### The addenda: the situation `W_± = W_∓^τ` -/

section Addenda

variable (h2 : (2 : K) ≠ 0) {τ : Gal(L/K)} (hτ : τ * τ = 1)
  {Wp Wm : Submodule L (L ⊗[K] WK)}

/-- Under `W_∓^τ = W_±` the canonical semi-linear involution restricts to a `τ`-semi-linear
additive bijection `W_+ → W_-`.

@census none
-/
def twistSwap (hτ : τ * τ = 1) (hW : twist τ Wm = Wp) (x : Wp) : Wm :=
  twistBack hτ ((LinearEquiv.ofEq _ _ hW).symm x)

@[simp]
theorem twistSwap_coe (hW : twist τ Wm = Wp) (x : Wp) :
    ((twistSwap hτ hW x : Wm) : L ⊗[K] WK) = galoisTwist τ (x : L ⊗[K] WK) := rfl

theorem twistSwap_add (hW : twist τ Wm = Wp) (x y : Wp) :
    twistSwap hτ hW (x + y) = twistSwap hτ hW x + twistSwap hτ hW y :=
  Subtype.ext (by simp)

theorem twistSwap_smul (hW : twist τ Wm = Wp) (c : L) (x : Wp) :
    twistSwap hτ hW (c • x) = τ c • twistSwap hτ hW x :=
  Subtype.ext (by simp [galoisTwist_smul])

theorem twistSwap_twistSwap (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm) (x : Wp) :
    twistSwap hτ hWm (twistSwap hτ hWp x) = x :=
  Subtype.ext (by simp [galoisTwist_galoisTwist hτ])

/-- Conjugation of an endomorphism of `W_-` by that involution: `p ↦ p^τ`, an endomorphism of
`W_+`.  It is a ring homomorphism, so it preserves `1`, products, powers and nilpotency — which
is how the minus-side hypotheses of the addenda reach the plus side.

@census none
-/
def semiConj (hτ : τ * τ = 1) (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm)
    (p : Module.End L Wm) : Module.End L Wp where
  toFun x := twistSwap hτ hWm (p (twistSwap hτ hWp x))
  map_add' x y := by rw [twistSwap_add, map_add, twistSwap_add]
  map_smul' c x := by
    simp only [RingHom.id_apply]
    rw [twistSwap_smul, map_smul, twistSwap_smul, aut_apply_aut hτ]

@[simp]
theorem semiConj_apply (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm) (p : Module.End L Wm)
    (x : Wp) : semiConj hτ hWp hWm p x = twistSwap hτ hWm (p (twistSwap hτ hWp x)) := rfl

@[simp]
theorem semiConj_one (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm) :
    semiConj hτ hWp hWm 1 = 1 := by
  refine LinearMap.ext fun x => ?_
  show twistSwap hτ hWm (twistSwap hτ hWp x) = x
  exact twistSwap_twistSwap hτ hWp hWm x

theorem semiConj_mul (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm) (p q : Module.End L Wm) :
    semiConj hτ hWp hWm (p * q) = semiConj hτ hWp hWm p * semiConj hτ hWp hWm q := by
  refine LinearMap.ext fun x => ?_
  show twistSwap hτ hWm (p (q (twistSwap hτ hWp x)))
      = twistSwap hτ hWm (p (twistSwap hτ hWp (twistSwap hτ hWm (q (twistSwap hτ hWp x)))))
  rw [twistSwap_twistSwap hτ hWm hWp]

theorem semiConj_pow (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm) (p : Module.End L Wm)
    (k : ℕ) : semiConj hτ hWp hWm (p ^ k) = (semiConj hτ hWp hWm p) ^ k := by
  induction k with
  | zero => simpa using semiConj_one hτ hWp hWm
  | succ k ih => rw [pow_succ, pow_succ, semiConj_mul, ih]

@[simp]
theorem semiConj_zero (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm) :
    semiConj hτ hWp hWm 0 = 0 := by
  refine LinearMap.ext fun x => ?_
  show twistSwap hτ hWm ((0 : Module.End L Wm) (twistSwap hτ hWp x)) = 0
  exact Subtype.ext (by simp)

theorem semiConj_add (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm) (p q : Module.End L Wm) :
    semiConj hτ hWp hWm (p + q) = semiConj hτ hWp hWm p + semiConj hτ hWp hWm q := by
  refine LinearMap.ext fun x => ?_
  show twistSwap hτ hWm (p (twistSwap hτ hWp x) + q (twistSwap hτ hWp x))
      = twistSwap hτ hWm (p (twistSwap hτ hWp x)) + twistSwap hτ hWm (q (twistSwap hτ hWp x))
  exact twistSwap_add hτ hWm _ _

theorem semiConj_isNilpotent (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm)
    {p : Module.End L Wm} (hp : IsNilpotent p) : IsNilpotent (semiConj hτ hWp hWm p) := by
  obtain ⟨k, hk⟩ := hp
  exact ⟨k, by rw [← semiConj_pow, hk, semiConj_zero]⟩

theorem semiConj_semiConj (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm)
    (p : Module.End L Wm) : semiConj hτ hWm hWp (semiConj hτ hWp hWm p) = p := by
  refine LinearMap.ext fun y => ?_
  show twistSwap hτ hWp (twistSwap hτ hWm (p (twistSwap hτ hWp (twistSwap hτ hWm y)))) = p y
  rw [twistSwap_twistSwap hτ hWm hWp, twistSwap_twistSwap hτ hWm hWp]

/-- Addition of endomorphisms of a submodule is cancellative — the submodule *is* an additive
group, even though `Module.End L ↥W` carries no `Ring` instance at the pinned mathlib revision
(see `MD-S6-06`).  This is what lets `Commute (1 + a) (1 + b)` be cancelled down to
`Commute a b`. -/
theorem end_add_right_cancel {U : Submodule L (L ⊗[K] WK)} {f g h : Module.End L U}
    (hfh : f + h = g + h) : f = g := by
  refine LinearMap.ext fun x => ?_
  have hx := congrArg (fun m => (m : Module.End L U) x) hfh
  simp only [LinearMap.add_apply] at hx
  exact add_right_cancel hx

/-- `eq:unipotentcommutators0` for unipotent maps is a commutation of the nilpotent parts. -/
theorem commute_of_commute_one_add {U : Submodule L (L ⊗[K] WK)} {a b : Module.End L U}
    (h : Commute (1 + a) (1 + b)) : Commute a b := by
  have hexp : (1 + a) * (1 + b) = 1 + a + b + a * b := by
    rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul]; abel
  have hexp' : (1 + b) * (1 + a) = 1 + a + b + b * a := by
    rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul]; abel
  have := h.eq
  rw [hexp, hexp'] at this
  have h2 : a * b + (1 + a + b) = b * a + (1 + a + b) := by
    rw [add_comm (a * b), add_comm (b * a)]; exact this
  exact end_add_right_cancel h2

/-- `φ_-^τ`, read as an endomorphism of `W_+`, is the conjugate of `φ_-` read as an endomorphism
of `W_-`. -/
theorem asEndConj_eq_semiConj (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm)
    (φm : Wm →ₗ[L] twist τ Wp) :
    asEndConj hτ hWp φm = semiConj hτ hWp hWm (asEnd hWm φm) := by
  refine LinearMap.ext fun x => ?_
  exact Subtype.ext rfl

/-- The minus-side unipotency crosses to the plus side. -/
theorem asEndConj_unipotent (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm)
    (φm : Wm →ₗ[L] twist τ Wp) {mm : Module.End L Wm} (hmm : IsNilpotent mm)
    (hum : asEnd hWm φm = 1 + mm) :
    ∃ mq : Module.End L Wp, IsNilpotent mq ∧ asEndConj hτ hWp φm = 1 + mq := by
  refine ⟨semiConj hτ hWp hWm mm, semiConj_isNilpotent hτ hWp hWm hmm, ?_⟩
  rw [asEndConj_eq_semiConj hτ hWp hWm, hum, semiConj_add, semiConj_one]

/-- The plus-step, read in `End(W₊)`: `½(P + Q^{-1})` where `P = φ_+`, `Q = φ_-^τ`. -/
theorem asEnd_stabilizationStep (hWp : twist τ Wm = Wp) (φp : Wp →ₗ[L] twist τ Wm)
    (φm : Wm →ₗ[L] twist τ Wp) (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm)) :
    asEnd hWp (stabilizationStep h2 hτ φp φm)
      = half (two_ne_zero_of_base (L := L) h2) •
          (asEnd hWp φp + Ring.inverse (asEndConj hτ hWp φm)) := by
  have hι : HasInverse ((LinearEquiv.ofEq _ _ hWp).symm.toLinearMap : Wp →ₗ[L] twist τ Wm) :=
    hasInverse_of_linearEquiv _
  have hQinv : Ring.inverse (asEndConj hτ hWp φm)
      = (LinearEquiv.ofEq _ _ hWp).toLinearMap.comp (linInv (twistConj hτ φm)) := by
    rw [ring_inverse_eq_linInv, asEndConj, linInv_comp_eq hm hι,
      linInv_coe ((LinearEquiv.ofEq _ _ hWp).symm)]
    rfl
  rw [hQinv]
  simp only [asEnd, stabilizationStep, LinearMap.comp_smul, LinearMap.comp_add]

/-- The conjugated minus-step, read in `End(W₊)`: `½(Q + P^{-1})`. -/
theorem asEndConj_stabilizationStep (hWp : twist τ Wm = Wp) (φp : Wp →ₗ[L] twist τ Wm)
    (φm : Wm →ₗ[L] twist τ Wp) (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm)) :
    asEndConj hτ hWp (stabilizationStep h2 hτ φm φp)
      = half (two_ne_zero_of_base (L := L) h2) •
          (asEndConj hτ hWp φm + Ring.inverse (asEnd hWp φp)) := by
  have hι : HasInverse ((LinearEquiv.ofEq _ _ hWp).toLinearMap : twist τ Wm →ₗ[L] Wp) :=
    hasInverse_of_linearEquiv _
  have hPinv : Ring.inverse (asEnd hWp φp)
      = (linInv φp).comp (LinearEquiv.ofEq _ _ hWp).symm.toLinearMap := by
    rw [ring_inverse_eq_linInv, asEnd, linInv_comp_eq hι hp,
      linInv_coe (LinearEquiv.ofEq _ _ hWp)]
  rw [hPinv]
  simp only [asEndConj]
  rw [twistConj_stabilizationStep h2 hτ φp φm hp]
  simp only [LinearMap.smul_comp, LinearMap.add_comp]

/-- Invertibility of `φ_+` can be read off its avatar in `End(W₊)`. -/
theorem hasInverse_of_isUnit_asEnd (hWp : twist τ Wm = Wp) (φp : Wp →ₗ[L] twist τ Wm)
    (h : IsUnit (asEnd hWp φp)) : HasInverse φp := by
  have hEq : φp = ((LinearEquiv.ofEq _ _ hWp).symm.toLinearMap).comp (asEnd hWp φp) := by
    simp only [asEnd, ← LinearMap.comp_assoc]
    rw [show ((LinearEquiv.ofEq (twist τ Wm) Wp hWp).symm.toLinearMap).comp
        ((LinearEquiv.ofEq (twist τ Wm) Wp hWp).toLinearMap) = LinearMap.id from by
      ext x; simp, LinearMap.id_comp]
  rw [hEq]
  exact (hasInverse_of_linearEquiv (LinearEquiv.ofEq _ _ hWp).symm).comp
    ((hasInverse_iff_isUnit _).mpr h)

/-- Invertibility of `φ_-^τ` can be read off its avatar in `End(W₊)`. -/
theorem hasInverse_twistConj_of_isUnit_asEndConj (hWp : twist τ Wm = Wp)
    (φm : Wm →ₗ[L] twist τ Wp) (h : IsUnit (asEndConj hτ hWp φm)) :
    HasInverse (twistConj hτ φm) := by
  have hEq : twistConj hτ φm = (asEndConj hτ hWp φm).comp
      ((LinearEquiv.ofEq _ _ hWp).toLinearMap) := by
    simp only [asEndConj, LinearMap.comp_assoc]
    rw [show ((LinearEquiv.ofEq (twist τ Wm) Wp hWp).symm.toLinearMap).comp
        ((LinearEquiv.ofEq (twist τ Wm) Wp hWp).toLinearMap) = LinearMap.id from by
      ext x; simp, LinearMap.comp_id]
  rw [hEq]
  exact ((hasInverse_iff_isUnit _).mpr h).comp (hasInverse_of_linearEquiv _)

/-- `P` and `Q` are invertible whenever the two maps are. -/
theorem isUnit_asEnd (hWp : twist τ Wm = Wp) (φp : Wp →ₗ[L] twist τ Wm) (hp : HasInverse φp) :
    IsUnit (asEnd hWp φp) :=
  (hasInverse_iff_isUnit _).mp
    ((hasInverse_of_linearEquiv (LinearEquiv.ofEq _ _ hWp)).comp hp)

theorem isUnit_asEndConj (hWp : twist τ Wm = Wp) (φm : Wm →ₗ[L] twist τ Wp)
    (hm : HasInverse (twistConj hτ φm)) : IsUnit (asEndConj hτ hWp φm) :=
  (hasInverse_iff_isUnit _).mp (hm.comp (hasInverse_of_linearEquiv _))

end Addenda

/-- **Addendum** to `prop:unipotentstabilization` (clause `RQ2-4.01-C5`): if `W_± = W_∓^τ` then
`eq:unipotentcommutators0` (`φ_± ∘ φ_∓^τ = φ_∓^τ ∘ φ_±`) implies `eq:unipotentcommutators1`
(the same relation for the stabilized `φ̃_±`).

@census    none (auxiliary; discharges clause `RQ2-4.01-C5` of `RQ2-4.01`)
@source    prop:unipotentstabilization
@clauses   RQ2-4.01-C5
@imports   none
@divergence EXTRA BINDER, disclosed (G2 finding C-2; not a weakening): `hgal : IsGalois K L`
is an argument here but is **not** clause `RQ2-4.01-H1`, whose text is only "L/K is a QUADRATIC
field extension" (`hquad` is that clause).  `IsGalois` follows from H1 + H2 — degree 2 is normal,
separable since `char K ≠ 2` — so the covered class is exactly the source's; it is a binder only
because mathlib has no one-step lemma for it at the pin.  Argument: module docstring, "The
standing hypotheses".
-/
theorem stabilizationStep_commute (h2 : (2 : K) ≠ 0) (hgal : IsGalois K L)
    (hquad : Module.finrank K L = 2) (τ : Gal(L/K)) (hτne : τ ≠ 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm)
    (φp : Wp ≃ₗ[L] twist τ Wm) (φm : Wm ≃ₗ[L] twist τ Wp)
    (hcomm : Commute (asEnd hWp (φp : Wp →ₗ[L] twist τ Wm))
      (asEndConj (aut_mul_self hgal hquad τ) hWp (φm : Wm →ₗ[L] twist τ Wp))) :
    Commute
      (asEnd hWp (stabilizationStep h2 (aut_mul_self hgal hquad τ)
        (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)))
      (asEndConj (aut_mul_self hgal hquad τ) hWp
        (stabilizationStep h2 (aut_mul_self hgal hquad τ)
          (φm : Wm →ₗ[L] twist τ Wp) (φp : Wp →ₗ[L] twist τ Wm))) := by
  have hp : HasInverse (φp : Wp →ₗ[L] twist τ Wm) := hasInverse_of_linearEquiv φp
  have hm : HasInverse (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)) :=
    (hasInverse_of_linearEquiv φm).twistConj _
  rw [asEnd_stabilizationStep h2 (aut_mul_self hgal hquad τ) hWp _ _ hp hm,
    asEndConj_stabilizationStep h2 (aut_mul_self hgal hquad τ) hWp _ _ hp hm]
  exact commute_avg (two_ne_zero_of_base (L := L) h2) (isUnit_asEnd hWp _ hp)
    (isUnit_asEndConj (aut_mul_self hgal hquad τ) hWp _ hm) hcomm

/-- **Addendum** to `prop:unipotentstabilization` (clause `RQ2-4.01-C6`): if in addition
`φ_± = 1 + m_±` with `m_±` nilpotent (`eq:unipotentnilpotency0`), then `φ̃_± = 1 + m̃_±` with
`m̃_±` nilpotent (`eq:unipotentnilpotency1`).

@census    none (auxiliary; discharges clause `RQ2-4.01-C6` of `RQ2-4.01`)
@source    prop:unipotentstabilization
@clauses   RQ2-4.01-C6
@imports   none
@divergence EXTRA BINDER, disclosed (G2 finding C-2; not a weakening): `hgal : IsGalois K L`
is an argument here but is **not** clause `RQ2-4.01-H1`, whose text is only "L/K is a QUADRATIC
field extension" (`hquad` is that clause).  `IsGalois` follows from H1 + H2 — degree 2 is normal,
separable since `char K ≠ 2` — so the covered class is exactly the source's; it is a binder only
because mathlib has no one-step lemma for it at the pin.  Argument: module docstring, "The
standing hypotheses".
-/
theorem stabilizationStep_unipotent (h2 : (2 : K) ≠ 0) (hgal : IsGalois K L)
    (hquad : Module.finrank K L = 2) (τ : Gal(L/K)) (hτne : τ ≠ 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm)
    (φp : Wp ≃ₗ[L] twist τ Wm) (φm : Wm ≃ₗ[L] twist τ Wp)
    (hcomm : Commute (asEnd hWp (φp : Wp →ₗ[L] twist τ Wm))
      (asEndConj (aut_mul_self hgal hquad τ) hWp (φm : Wm →ₗ[L] twist τ Wp)))
    (hup : ∃ mp : Module.End L Wp, IsNilpotent mp ∧
      asEnd hWp (φp : Wp →ₗ[L] twist τ Wm) = 1 + mp)
    (hum : ∃ mm : Module.End L Wm, IsNilpotent mm ∧
      asEnd hWm (φm : Wm →ₗ[L] twist τ Wp) = 1 + mm) :
    ∃ mp : Module.End L Wp, IsNilpotent mp ∧
      asEnd hWp (stabilizationStep h2 (aut_mul_self hgal hquad τ)
        (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)) = 1 + mp := by
  have hp : HasInverse (φp : Wp →ₗ[L] twist τ Wm) := hasInverse_of_linearEquiv φp
  have hm : HasInverse (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)) :=
    (hasInverse_of_linearEquiv φm).twistConj _
  obtain ⟨mp, hmp, hP⟩ := hup
  obtain ⟨mm, hmm, hM⟩ := hum
  obtain ⟨mq, hmq, hQ⟩ :=
    asEndConj_unipotent (aut_mul_self hgal hquad τ) hWp hWm _ hmm hM
  rw [asEnd_stabilizationStep h2 (aut_mul_self hgal hquad τ) hWp _ _ hp hm]
  exact avg_one_add (two_ne_zero_of_base (L := L) h2) hP hQ hmp hmq
    (commute_of_commute_one_add (by rw [← hP, ← hQ]; exact hcomm))

/-! ## `cor:unipotentstabilization` — the iteration -/

/-- The iteration of `cor:unipotentstabilization` (clause `RQ2-4.02-H2`):
`φ^{(0)}_± := φ_±` and `φ^{(k+1)}_± := ½(φ^{(k)}_± + (φ^{(k),τ}_∓)^{-1})`, as a sequence of
**pairs** `(φ^{(k)}_+, φ^{(k)}_-)`.

The two components are the *same* function of the pair with its arguments transposed, which is
what `rmk:unipotentstabilization` (census `RQ2-4.04`) observes.

@census    none (auxiliary; discharges clause `RQ2-4.02-H2` of `RQ2-4.02`)
@source    cor:unipotentstabilization
@clauses   RQ2-4.02-H2,
           RQ2-5.12-S-O5
@imports   none
@divergence none
-/
noncomputable def stabilizationSeq (h2 : (2 : K) ≠ 0) {τ : Gal(L/K)} (hτ : τ * τ = 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) :
    ℕ → (Wp →ₗ[L] twist τ Wm) × (Wm →ₗ[L] twist τ Wp)
  | 0 => (φp, φm)
  | k + 1 =>
      (stabilizationStep h2 hτ (stabilizationSeq h2 hτ φp φm k).1
          (stabilizationSeq h2 hτ φp φm k).2,
        stabilizationStep h2 hτ (stabilizationSeq h2 hτ φp φm k).2
          (stabilizationSeq h2 hτ φp φm k).1)

@[simp]
theorem stabilizationSeq_zero (h2 : (2 : K) ≠ 0) {τ : Gal(L/K)} (hτ : τ * τ = 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) :
    stabilizationSeq h2 hτ φp φm 0 = (φp, φm) := rfl

theorem stabilizationSeq_succ (h2 : (2 : K) ≠ 0) {τ : Gal(L/K)} (hτ : τ * τ = 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) (k : ℕ) :
    stabilizationSeq h2 hτ φp φm (k + 1)
      = (stabilizationStep h2 hτ (stabilizationSeq h2 hτ φp φm k).1
            (stabilizationSeq h2 hτ φp φm k).2,
          stabilizationStep h2 hτ (stabilizationSeq h2 hτ φp φm k).2
            (stabilizationSeq h2 hτ φp φm k).1) := rfl

/-! ### The invariants of the iteration -/

section SeqLemmas

variable (h2 : (2 : K) ≠ 0) {τ : Gal(L/K)} (hτ : τ * τ = 1)
  {Wp Wm : Submodule L (L ⊗[K] WK)}

@[simp]
theorem stabilizationSeq_succ_fst (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) (k : ℕ) :
    (stabilizationSeq h2 hτ φp φm (k + 1)).1
      = stabilizationStep h2 hτ (stabilizationSeq h2 hτ φp φm k).1
          (stabilizationSeq h2 hτ φp φm k).2 := rfl

@[simp]
theorem stabilizationSeq_succ_snd (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) (k : ℕ) :
    (stabilizationSeq h2 hτ φp φm (k + 1)).2
      = stabilizationStep h2 hτ (stabilizationSeq h2 hτ φp φm k).2
          (stabilizationSeq h2 hτ φp φm k).1 := rfl

/-- **Transposing the pair transposes the sequence** — the content of
`rmk:unipotentstabilization` (census `RQ2-4.04`).  Both components of `stabilizationSeq` are the
same function of the pair, with the arguments exchanged.

@census none
-/
theorem stabilizationSeq_symm (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) (k : ℕ) :
    stabilizationSeq h2 hτ φm φp k
      = ((stabilizationSeq h2 hτ φp φm k).2, (stabilizationSeq h2 hτ φp φm k).1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      refine Prod.ext ?_ ?_ <;>
        simp only [stabilizationSeq_succ_fst, stabilizationSeq_succ_snd, ih]

/-- **The invariant of the iteration.**  For every `k`: the `k`-th plus-iterate and the
conjugated `k`-th minus-iterate are isomorphisms (clause `RQ2-4.02-C5`), and their composite is
`1 + n^{(k)}` with `n^{(k)}` killing the `(e - k + 1)`-st power.

**That recorded bound is linear, not the halving** (G4 verification observation O-G4-1).  The
`succ` step *does* apply the halving — `quarter_error_pow` gives
`n^{(k+1)} ^ ((e - k + 1) ⌈/⌉ 2) = 0` — and then **relaxes** it along
`(e - k + 1) ⌈/⌉ 2 ≤ e - (k + 1) + 1`, because a linear decay is all
`cor:unipotentstabilization` needs: it has to reach exponent `1` by `k = e`, not to reach it
fastest.  The source's quantitative halving `ẽ ≤ ⌈e/2⌉` is proved exactly and separately, where
the census demands it — `nilpotency_stabilizationStep` (clause `RQ2-4.01-C4`).

@census none
-/
theorem stabilizationSeq_invariant (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)
    (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm)) (n : Module.End L Wp) (e : ℕ)
    (hn : (twistConj hτ φm).comp φp = 1 + n) (hnilp : n ^ e = 0) (k : ℕ) :
    HasInverse (stabilizationSeq h2 hτ φp φm k).1
      ∧ HasInverse (twistConj hτ (stabilizationSeq h2 hτ φp φm k).2)
      ∧ ∃ nk : Module.End L Wp,
          (twistConj hτ (stabilizationSeq h2 hτ φp φm k).2).comp
              (stabilizationSeq h2 hτ φp φm k).1 = 1 + nk ∧ nk ^ (e - k + 1) = 0 := by
  have hL : (2 : L) ≠ 0 := two_ne_zero_of_base (L := L) h2
  induction k with
  | zero =>
      refine ⟨hp, hm, n, hn, ?_⟩
      rw [Nat.sub_zero, pow_succ, hnilp, zero_mul]
  | succ k ih =>
      obtain ⟨hF, hH, nk, hnk, hnkpow⟩ := ih
      have hnil : IsNilpotent nk := ⟨e - k + 1, hnkpow⟩
      have hu : IsUnit ((twistConj hτ (stabilizationSeq h2 hτ φp φm k).2).comp
          (stabilizationSeq h2 hτ φp φm k).1) := by
        rw [hnk]; exact isUnit_one_add_of_isNilpotent hnil
      have hcom : Commute ((twistConj hτ (stabilizationSeq h2 hτ φp φm k).2).comp
          (stabilizationSeq h2 hτ φp φm k).1) nk := by
        rw [hnk]; exact (Commute.one_left nk).add_left (Commute.refl nk)
      refine ⟨?_, ?_, ?_⟩
      · rw [stabilizationSeq_succ_fst]
        exact hasInverse_stabilizationStep h2 hτ _ _ hF hH nk hnk hnil
      · rw [stabilizationSeq_succ_snd]
        exact hasInverse_twistConj_stabilizationStep h2 hτ _ _ hF hH nk hnk hnil
      · refine ⟨(half hL * half hL) • (Ring.inverse ((twistConj hτ
          (stabilizationSeq h2 hτ φp φm k).2).comp (stabilizationSeq h2 hτ φp φm k).1)
            * (nk * nk)), ?_, ?_⟩
        · rw [stabilizationSeq_succ_fst, stabilizationSeq_succ_snd,
            stabilizationStep_comp h2 hτ _ _ hF hH]
          exact quarter_avg_of_one_add hL hu hnk
        · have hstep := quarter_error_pow hL hu hcom hnkpow
          have hle : (e - k + 1) ⌈/⌉ 2 ≤ e - (k + 1) + 1 := by
            rw [Nat.ceilDiv_eq_add_pred_div]; omega
          obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
          rw [hj, pow_add, hstep, zero_mul]

/-- Past the nilpotency exponent the composite is the identity: `eq:conjugateinverse`. -/
theorem stabilizationSeq_conjugate_inverse (φp : Wp →ₗ[L] twist τ Wm)
    (φm : Wm →ₗ[L] twist τ Wp) (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm))
    (n : Module.End L Wp) (e : ℕ) (hn : (twistConj hτ φm).comp φp = 1 + n) (hnilp : n ^ e = 0)
    {k : ℕ} (hk : e ≤ k) :
    (twistConj hτ (stabilizationSeq h2 hτ φp φm k).2).comp
      (stabilizationSeq h2 hτ φp φm k).1 = 1 := by
  obtain ⟨-, -, nk, hnk, hnkpow⟩ := stabilizationSeq_invariant h2 hτ φp φm hp hm n e hn hnilp k
  rw [Nat.sub_eq_zero_of_le hk, Nat.zero_add, pow_one] at hnkpow
  rw [hnk, hnkpow, add_zero]

/-- Past the nilpotency exponent the sequence is **constant** (clause `RQ2-4.02-C1`). -/
theorem stabilizationSeq_succ_eq (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)
    (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm)) (n : Module.End L Wp) (e : ℕ)
    (hn : (twistConj hτ φm).comp φp = 1 + n) (hnilp : n ^ e = 0) {k : ℕ} (hk : e ≤ k) :
    stabilizationSeq h2 hτ φp φm (k + 1) = stabilizationSeq h2 hτ φp φm k := by
  obtain ⟨hF, hH, -⟩ := stabilizationSeq_invariant h2 hτ φp φm hp hm n e hn hnilp k
  have hHF := stabilizationSeq_conjugate_inverse h2 hτ φp φm hp hm n e hn hnilp hk
  set F := (stabilizationSeq h2 hτ φp φm k).1 with hFdef
  set G := (stabilizationSeq h2 hτ φp φm k).2 with hGdef
  -- `φ_-^τ` is the inverse of `φ_+`, so both halves of the step are the same map
  have hHF' : (twistConj hτ G).comp F = LinearMap.id := by
    rw [hHF, Module.End.one_eq_id]
  have hHeq : twistConj hτ G = linInv F := by
    calc twistConj hτ G = (twistConj hτ G).comp (F.comp (linInv F)) := by
          rw [hF.comp_linInv, LinearMap.comp_id]
      _ = ((twistConj hτ G).comp F).comp (linInv F) := (LinearMap.comp_assoc _ _ _).symm
      _ = linInv F := by rw [hHF', LinearMap.id_comp]
  have hFH : F.comp (twistConj hτ G) = LinearMap.id := comp_eq_id_symm hF hHF'
  have hlinH : linInv (twistConj hτ G) = F := by rw [hHeq, linInv_linInv hF]
  -- and symmetrically for the other sign
  have hGconj : (twistConj hτ F).comp G = LinearMap.id := twistConj_comp_eq_id hτ F G hFH
  have hGconj' : G.comp (twistConj hτ F) = LinearMap.id :=
    comp_eq_id_symm (hasInverse_of_twistConj hτ hH) hGconj
  have hlinF : linInv (twistConj hτ F) = G := linInv_eq_of hGconj' hGconj
  refine Prod.ext ?_ ?_
  · rw [stabilizationSeq_succ_fst, stabilizationStep, ← hFdef, ← hGdef, hlinH, ← two_smul L F,
      smul_smul, half_eq, inv_mul_cancel₀ (two_ne_zero_of_base (L := L) h2), one_smul]
  · rw [stabilizationSeq_succ_snd, stabilizationStep, ← hFdef, ← hGdef, hlinF, ← two_smul L G,
      smul_smul, half_eq, inv_mul_cancel₀ (two_ne_zero_of_base (L := L) h2), one_smul]

/-- The sequence is constant from the nilpotency exponent on. -/
theorem stabilizationSeq_eq_of_le (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)
    (hp : HasInverse φp) (hm : HasInverse (twistConj hτ φm)) (n : Module.End L Wp) (e : ℕ)
    (hn : (twistConj hτ φm).comp φp = 1 + n) (hnilp : n ^ e = 0) :
    ∀ {k : ℕ}, e ≤ k → stabilizationSeq h2 hτ φp φm k = stabilizationSeq h2 hτ φp φm e := by
  intro k hk
  induction k with
  | zero => simp_all
  | succ k ih =>
      rcases Nat.lt_or_ge e (k + 1) with h | h
      · have hek : e ≤ k := by omega
        rw [stabilizationSeq_succ_eq h2 hτ φp φm hp hm n e hn hnilp hek]
        exact ih hek
      · have : e = k + 1 := le_antisymm hk h
        rw [this]

end SeqLemmas

/-- **Corollary** (`cor:unipotentstabilization`, §4.1 of the source).

Under the hypotheses of `prop:unipotentstabilization` (clause `RQ2-4.02-H1`) and with the
recursion `stabilizationSeq` (clause `RQ2-4.02-H2`), there **exists** `k₀ ≥ 0` such that for all
`k ≥ k₀` (clause `RQ2-4.02-H3`) the sequence is constant, `φ^{(k)}_± = φ^{(k₀)}_±` (clause
`RQ2-4.02-C1`), and `φ^{(k),τ}_∓ ∘ φ^{(k)}_± = 1_{W_±}` (`eq:conjugateinverse`, clause
`RQ2-4.02-C2`, stated for both signs).

@census    RQ2-4.02
@source    cor:unipotentstabilization
@clauses   RQ2-4.02-H1, RQ2-4.02-H3, RQ2-4.02-C1, RQ2-4.02-C2
@imports   none
@divergence EXTRA BINDER, disclosed (G2 finding C-2; not a weakening): `hgal : IsGalois K L`
is an argument here but is **not** clause `RQ2-4.01-H1`, whose text is only "L/K is a QUADRATIC
field extension" (`hquad` is that clause).  `IsGalois` follows from H1 + H2 — degree 2 is normal,
separable since `char K ≠ 2` — so the covered class is exactly the source's; it is a binder only
because mathlib has no one-step lemma for it at the pin.  Argument: module docstring, "The
standing hypotheses".
-/
theorem stabilization_spec (h2 : (2 : K) ≠ 0) (hgal : IsGalois K L)
    (hquad : Module.finrank K L = 2) (τ : Gal(L/K)) (hτne : τ ≠ 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp ≃ₗ[L] twist τ Wm) (φm : Wm ≃ₗ[L] twist τ Wp)
    (n : Module.End L Wp) (e : ℕ) (he : 1 ≤ e)
    (hn : (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)).comp
        (φp : Wp →ₗ[L] twist τ Wm) = 1 + n)
    (hexact : n ^ (e - 1) ≠ 0) (hnilp : n ^ e = 0) :
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      stabilizationSeq h2 (aut_mul_self hgal hquad τ)
          (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k
        = stabilizationSeq h2 (aut_mul_self hgal hquad τ)
          (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k₀
      ∧ (twistConj (aut_mul_self hgal hquad τ)
            (stabilizationSeq h2 (aut_mul_self hgal hquad τ)
              (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k).2).comp
          (stabilizationSeq h2 (aut_mul_self hgal hquad τ)
            (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k).1 = 1
      ∧ (twistConj (aut_mul_self hgal hquad τ)
            (stabilizationSeq h2 (aut_mul_self hgal hquad τ)
              (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k).1).comp
          (stabilizationSeq h2 (aut_mul_self hgal hquad τ)
            (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k).2 = 1 := by
  have hp : HasInverse (φp : Wp →ₗ[L] twist τ Wm) := hasInverse_of_linearEquiv φp
  have hm : HasInverse (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)) :=
    (hasInverse_of_linearEquiv φm).twistConj _
  refine ⟨e, fun k hk => ⟨?_, ?_, ?_⟩⟩
  · rw [stabilizationSeq_eq_of_le h2 _ _ _ hp hm n e hn hnilp hk]
  · exact stabilizationSeq_conjugate_inverse h2 _ _ _ hp hm n e hn hnilp hk
  · obtain ⟨hF, hH, -⟩ :=
      stabilizationSeq_invariant h2 (aut_mul_self hgal hquad τ) _ _ hp hm n e hn hnilp k
    have hHF := stabilizationSeq_conjugate_inverse h2 _ _ _ hp hm n e hn hnilp hk
    have hHF' : (twistConj (aut_mul_self hgal hquad τ)
        (stabilizationSeq h2 (aut_mul_self hgal hquad τ) (φp : Wp →ₗ[L] twist τ Wm)
          (φm : Wm →ₗ[L] twist τ Wp) k).2).comp
        (stabilizationSeq h2 (aut_mul_self hgal hquad τ) (φp : Wp →ₗ[L] twist τ Wm)
          (φm : Wm →ₗ[L] twist τ Wp) k).1 = LinearMap.id := by
      rw [hHF, Module.End.one_eq_id]
    rw [Module.End.one_eq_id]
    exact twistConj_comp_eq_id _ _ _ (comp_eq_id_symm hF hHF')

/-- Clause `RQ2-4.02-C5` (added post-freeze by the census verifier, finding F-5): **every** iterate
`φ^{(k)}_±` is itself an `L`-linear isomorphism `W_± → W_∓^τ`, so the inverse appearing in step
`k+1` of the recursion is defined — i.e. the recursion is well formed at every stage.

@census    none (auxiliary; discharges clause `RQ2-4.02-C5` of `RQ2-4.02`)
@source    cor:unipotentstabilization
@clauses   RQ2-4.02-C5
@imports   none
@divergence EXTRA BINDER, disclosed (G2 finding C-2; not a weakening): `hgal : IsGalois K L`
is an argument here but is **not** clause `RQ2-4.01-H1`, whose text is only "L/K is a QUADRATIC
field extension" (`hquad` is that clause).  `IsGalois` follows from H1 + H2 — degree 2 is normal,
separable since `char K ≠ 2` — so the covered class is exactly the source's; it is a binder only
because mathlib has no one-step lemma for it at the pin.  Argument: module docstring, "The
standing hypotheses".
-/
theorem stabilizationSeq_bijective (h2 : (2 : K) ≠ 0) (hgal : IsGalois K L)
    (hquad : Module.finrank K L = 2) (τ : Gal(L/K)) (hτne : τ ≠ 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp ≃ₗ[L] twist τ Wm) (φm : Wm ≃ₗ[L] twist τ Wp)
    (n : Module.End L Wp)
    (hn : (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)).comp
        (φp : Wp →ₗ[L] twist τ Wm) = 1 + n)
    (hnil : IsNilpotent n) (k : ℕ) :
    Function.Bijective (stabilizationSeq h2 (aut_mul_self hgal hquad τ)
        (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k).1
      ∧ Function.Bijective (stabilizationSeq h2 (aut_mul_self hgal hquad τ)
        (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k).2 := by
  have hp : HasInverse (φp : Wp →ₗ[L] twist τ Wm) := hasInverse_of_linearEquiv φp
  have hm : HasInverse (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)) :=
    (hasInverse_of_linearEquiv φm).twistConj _
  obtain ⟨N, hN⟩ := hnil
  obtain ⟨hF, hH, -⟩ :=
    stabilizationSeq_invariant h2 (aut_mul_self hgal hquad τ) _ _ hp hm n N hn hN k
  exact ⟨hF.bijective, (hasInverse_of_twistConj _ hH).bijective⟩

section IteratedAddenda

variable (h2 : (2 : K) ≠ 0) {τ : Gal(L/K)} (hτ : τ * τ = 1)
  {Wp Wm : Submodule L (L ⊗[K] WK)}

/-- **The addenda, iterated.**  Under `W_± = W_∓^τ`, if `eq:unipotentcommutators0` and
`eq:unipotentnilpotency0` hold at `k = 0` then they hold at every `k`: this is
`eq:unipotentcommutatorsk` and `eq:unipotentnilpotencyk` (clauses `RQ2-4.02-C3`, `RQ2-4.02-C4`).

@census none
-/
theorem stabilizationSeq_addendum (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm)
    (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp)
    (hcomm : Commute (asEnd hWp φp) (asEndConj hτ hWp φm))
    (hup : ∃ mp : Module.End L Wp, IsNilpotent mp ∧ asEnd hWp φp = 1 + mp)
    (hum : ∃ mm : Module.End L Wm, IsNilpotent mm ∧ asEnd hWm φm = 1 + mm) (k : ℕ) :
    Commute (asEnd hWp (stabilizationSeq h2 hτ φp φm k).1)
        (asEndConj hτ hWp (stabilizationSeq h2 hτ φp φm k).2)
      ∧ (∃ mp : Module.End L Wp, IsNilpotent mp
          ∧ asEnd hWp (stabilizationSeq h2 hτ φp φm k).1 = 1 + mp)
      ∧ (∃ mq : Module.End L Wp, IsNilpotent mq
          ∧ asEndConj hτ hWp (stabilizationSeq h2 hτ φp φm k).2 = 1 + mq) := by
  have hL : (2 : L) ≠ 0 := two_ne_zero_of_base (L := L) h2
  induction k with
  | zero =>
      obtain ⟨mm, hmm, hM⟩ := hum
      exact ⟨hcomm, hup, asEndConj_unipotent hτ hWp hWm φm hmm hM⟩
  | succ k ih =>
      obtain ⟨hc, ⟨mp, hmp, hP⟩, ⟨mq, hmq, hQ⟩⟩ := ih
      have hPu : IsUnit (asEnd hWp (stabilizationSeq h2 hτ φp φm k).1) := by
        rw [hP]; exact isUnit_one_add_of_isNilpotent hmp
      have hQu : IsUnit (asEndConj hτ hWp (stabilizationSeq h2 hτ φp φm k).2) := by
        rw [hQ]; exact isUnit_one_add_of_isNilpotent hmq
      have hp' : HasInverse (stabilizationSeq h2 hτ φp φm k).1 :=
        hasInverse_of_isUnit_asEnd hWp _ hPu
      have hm' : HasInverse (twistConj hτ (stabilizationSeq h2 hτ φp φm k).2) :=
        hasInverse_twistConj_of_isUnit_asEndConj hτ hWp _ hQu
      have hmpq : Commute mp mq := commute_of_commute_one_add (by rw [← hP, ← hQ]; exact hc)
      rw [stabilizationSeq_succ_fst, stabilizationSeq_succ_snd]
      refine ⟨?_, ?_, ?_⟩
      · rw [asEnd_stabilizationStep h2 hτ hWp _ _ hp' hm',
          asEndConj_stabilizationStep h2 hτ hWp _ _ hp' hm']
        exact commute_avg hL hPu hQu hc
      · rw [asEnd_stabilizationStep h2 hτ hWp _ _ hp' hm']
        exact avg_one_add hL hP hQ hmp hmq hmpq
      · rw [asEndConj_stabilizationStep h2 hτ hWp _ _ hp' hm']
        exact avg_one_add hL hQ hP hmq hmp hmpq.symm

/-- The minus-side unipotency, transported back from `End(W₊)` to `End(W₋)`. -/
theorem asEnd_unipotent_of_asEndConj (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm)
    (φm : Wm →ₗ[L] twist τ Wp) {mq : Module.End L Wp} (hmq : IsNilpotent mq)
    (hQ : asEndConj hτ hWp φm = 1 + mq) :
    ∃ mm : Module.End L Wm, IsNilpotent mm ∧ asEnd hWm φm = 1 + mm := by
  refine ⟨semiConj hτ hWm hWp mq, semiConj_isNilpotent hτ hWm hWp hmq, ?_⟩
  have := congrArg (fun p => semiConj hτ hWm hWp p) (asEndConj_eq_semiConj hτ hWp hWm φm)
  simp only [semiConj_semiConj] at this
  rw [← this, hQ, semiConj_add, semiConj_one]

end IteratedAddenda

/-- **Addendum** to `cor:unipotentstabilization` (clause `RQ2-4.02-C3`): under `W_± = W_∓^τ`,
`eq:unipotentcommutators0` and `eq:unipotentnilpotency0`, the relation `eq:unipotentcommutatorsk`
holds for **all** `k ≥ 0`.

@census    none (auxiliary; discharges clause `RQ2-4.02-C3` of `RQ2-4.02`)
@source    cor:unipotentstabilization
@clauses   RQ2-4.02-C3
@imports   none
@divergence EXTRA BINDER, disclosed (G2 finding C-2; not a weakening): `hgal : IsGalois K L`
is an argument here but is **not** clause `RQ2-4.01-H1`, whose text is only "L/K is a QUADRATIC
field extension" (`hquad` is that clause).  `IsGalois` follows from H1 + H2 — degree 2 is normal,
separable since `char K ≠ 2` — so the covered class is exactly the source's; it is a binder only
because mathlib has no one-step lemma for it at the pin.  Argument: module docstring, "The
standing hypotheses".
-/
theorem stabilizationSeq_commute (h2 : (2 : K) ≠ 0) (hgal : IsGalois K L)
    (hquad : Module.finrank K L = 2) (τ : Gal(L/K)) (hτne : τ ≠ 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm)
    (φp : Wp ≃ₗ[L] twist τ Wm) (φm : Wm ≃ₗ[L] twist τ Wp)
    (hcomm : Commute (asEnd hWp (φp : Wp →ₗ[L] twist τ Wm))
      (asEndConj (aut_mul_self hgal hquad τ) hWp (φm : Wm →ₗ[L] twist τ Wp)))
    (hup : ∃ mp : Module.End L Wp, IsNilpotent mp ∧
      asEnd hWp (φp : Wp →ₗ[L] twist τ Wm) = 1 + mp)
    (hum : ∃ mm : Module.End L Wm, IsNilpotent mm ∧
      asEnd hWm (φm : Wm →ₗ[L] twist τ Wp) = 1 + mm) (k : ℕ) :
    Commute
      (asEnd hWp (stabilizationSeq h2 (aut_mul_self hgal hquad τ)
        (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k).1)
      (asEndConj (aut_mul_self hgal hquad τ) hWp
        (stabilizationSeq h2 (aut_mul_self hgal hquad τ)
          (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k).2) := by
  exact (stabilizationSeq_addendum h2 (aut_mul_self hgal hquad τ) hWp hWm _ _ hcomm hup hum k).1

/-- **Addendum** to `cor:unipotentstabilization` (clause `RQ2-4.02-C4`): under the same
hypotheses, `φ^{(k)}_± = 1 + m^{(k)}_±` with `m^{(k)}_±` nilpotent for **all** `k ≥ 0`
(`eq:unipotentnilpotencyk`).  This is the form consumed by `RQ-5.05`.

@census    none (auxiliary; discharges clause `RQ2-4.02-C4` of `RQ2-4.02`)
@source    cor:unipotentstabilization
@clauses   RQ2-4.02-C4
@imports   none
@divergence EXTRA BINDER, disclosed (G2 finding C-2; not a weakening): `hgal : IsGalois K L`
is an argument here but is **not** clause `RQ2-4.01-H1`, whose text is only "L/K is a QUADRATIC
field extension" (`hquad` is that clause).  `IsGalois` follows from H1 + H2 — degree 2 is normal,
separable since `char K ≠ 2` — so the covered class is exactly the source's; it is a binder only
because mathlib has no one-step lemma for it at the pin.  Argument: module docstring, "The
standing hypotheses".
-/
theorem stabilizationSeq_unipotent (h2 : (2 : K) ≠ 0) (hgal : IsGalois K L)
    (hquad : Module.finrank K L = 2) (τ : Gal(L/K)) (hτne : τ ≠ 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (hWp : twist τ Wm = Wp) (hWm : twist τ Wp = Wm)
    (φp : Wp ≃ₗ[L] twist τ Wm) (φm : Wm ≃ₗ[L] twist τ Wp)
    (hcomm : Commute (asEnd hWp (φp : Wp →ₗ[L] twist τ Wm))
      (asEndConj (aut_mul_self hgal hquad τ) hWp (φm : Wm →ₗ[L] twist τ Wp)))
    (hup : ∃ mp : Module.End L Wp, IsNilpotent mp ∧
      asEnd hWp (φp : Wp →ₗ[L] twist τ Wm) = 1 + mp)
    (hum : ∃ mm : Module.End L Wm, IsNilpotent mm ∧
      asEnd hWm (φm : Wm →ₗ[L] twist τ Wp) = 1 + mm) (k : ℕ) :
    (∃ mp : Module.End L Wp, IsNilpotent mp ∧
        asEnd hWp (stabilizationSeq h2 (aut_mul_self hgal hquad τ)
          (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k).1 = 1 + mp)
      ∧ (∃ mm : Module.End L Wm, IsNilpotent mm ∧
        asEnd hWm (stabilizationSeq h2 (aut_mul_self hgal hquad τ)
          (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k).2 = 1 + mm) := by
  obtain ⟨-, hplus, mq, hmq, hQ⟩ :=
    stabilizationSeq_addendum h2 (aut_mul_self hgal hquad τ) hWp hWm _ _ hcomm hup hum k
  exact ⟨hplus, asEnd_unipotent_of_asEndConj (aut_mul_self hgal hquad τ) hWp hWm _ hmq hQ⟩

/-! ## `def:unipotentstabilization` -/

-- `hτne` (clause `RQ2-4.01-H3` / `RQ2-4.03-H1`) is carried in the signature for fidelity but is
-- not needed by the construction: `aut_mul_self` holds for every element of `Gal(L/K)`.
set_option linter.unusedVariables false in
/-- **Definition** (`def:unipotentstabilization`, §4.1 of the source).

Under the hypotheses of `prop:unipotentstabilization` (clause `RQ2-4.03-H1`) and with `k₀` as in
`cor:unipotentstabilization` (clause `RQ2-4.03-H2`), the **unipotent stabilization** of the pair
`(φ_+, φ_-)` is `φ^{(∞)}_± := φ^{(k)}_±` for any `k ≥ k₀` (clauses `RQ2-4.03-C1`, `RQ2-4.03-C3`).

The definition takes the nilpotency exponent `e` of `eq:nilpotency` as the index at which to
read the sequence off: `e ≥ k₀` always (the exponent at least halves at each step, so it reaches
`1`, i.e. `n = 0`, after at most `e` steps), so this is one admissible choice of `k ≥ k₀` and the
limit is *reached in finitely many explicit steps*, not merely approached.  Independence of the
choice (clause `RQ2-4.03-C2`) is `stabilization_eq_seq`.

@census    RQ2-4.03
@source    def:unipotentstabilization
@clauses   RQ2-4.03-H1, RQ2-4.03-H2, RQ2-4.03-C1, RQ2-4.03-C3
@imports   none
@divergence TWO disclosures in ONE field.  `CONVENTIONS.md` §4's contract gives each declaration
a single `@divergence`; carrying two fields here is what hid the first from `rqaudit table`
(G4 finding F-1), so they are merged rather than the instrument taught to concatenate.
**(i) TOTALITY IDIOM** (G2 observation O-2): this `def` is **total** — it takes neither
`eq:nilpotency` nor any tie between the read-off index `e` and the exponent it names, as mathlib's
`Ring.inverse` takes no `IsUnit`; outside the source's hypotheses the value is junk and is not
claimed to be the paper's object, and the hypotheses are carried by `stabilization_eq_seq`
(clause `RQ2-4.03-C2`) and `stabilization_spec`.  Same idiom as `sqrt`,
`sqrtOfScalarPlusNilpotent` and `linInv`.
**(ii) EXTRA BINDER** (G2 finding C-2; not a weakening): `hgal : IsGalois K L` is an argument here
but is **not** clause `RQ2-4.01-H1`, whose text is only "L/K is a QUADRATIC field extension"
(`hquad` is that clause); `IsGalois` follows from H1 + H2 — degree 2 is normal, separable since
`char K ≠ 2` — so the covered class is exactly the source's, and it is a binder only because
mathlib has no one-step lemma for it at the pin.  Argument: module docstring, "The standing
hypotheses".
-/
noncomputable def stabilization (h2 : (2 : K) ≠ 0) (hgal : IsGalois K L)
    (hquad : Module.finrank K L = 2) (τ : Gal(L/K)) (hτne : τ ≠ 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp ≃ₗ[L] twist τ Wm) (φm : Wm ≃ₗ[L] twist τ Wp) (e : ℕ) :
    (Wp →ₗ[L] twist τ Wm) × (Wm →ₗ[L] twist τ Wp) :=
  stabilizationSeq h2 (aut_mul_self hgal hquad τ)
    (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) e

/-- Clause `RQ2-4.03-C2`: the unipotent stabilization is **independent of the choice** of
`k ≥ k₀` — every index past the nilpotency exponent gives the same pair.

@census    none (auxiliary; discharges clause `RQ2-4.03-C2` of `RQ2-4.03`)
@source    def:unipotentstabilization
@clauses   RQ2-4.03-C2
@imports   none
@divergence EXTRA BINDER, disclosed (G2 finding C-2; not a weakening): `hgal : IsGalois K L`
is an argument here but is **not** clause `RQ2-4.01-H1`, whose text is only "L/K is a QUADRATIC
field extension" (`hquad` is that clause).  `IsGalois` follows from H1 + H2 — degree 2 is normal,
separable since `char K ≠ 2` — so the covered class is exactly the source's; it is a binder only
because mathlib has no one-step lemma for it at the pin.  Argument: module docstring, "The
standing hypotheses".
-/
theorem stabilization_eq_seq (h2 : (2 : K) ≠ 0) (hgal : IsGalois K L)
    (hquad : Module.finrank K L = 2) (τ : Gal(L/K)) (hτne : τ ≠ 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp ≃ₗ[L] twist τ Wm) (φm : Wm ≃ₗ[L] twist τ Wp)
    (n : Module.End L Wp) (e : ℕ) (he : 1 ≤ e)
    (hn : (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)).comp
        (φp : Wp →ₗ[L] twist τ Wm) = 1 + n)
    (hexact : n ^ (e - 1) ≠ 0) (hnilp : n ^ e = 0) (k : ℕ) (hk : e ≤ k) :
    stabilizationSeq h2 (aut_mul_self hgal hquad τ)
        (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) k
      = stabilization h2 hgal hquad τ hτne φp φm e := by
  have hp : HasInverse (φp : Wp →ₗ[L] twist τ Wm) := hasInverse_of_linearEquiv φp
  have hm : HasInverse (twistConj (aut_mul_self hgal hquad τ) (φm : Wm →ₗ[L] twist τ Wp)) :=
    (hasInverse_of_linearEquiv φm).twistConj _
  exact stabilizationSeq_eq_of_le h2 _ _ _ hp hm n e hn hnilp hk

/-! ## `rmk:unipotentstabilization` -/

/-- **Remark** (`rmk:unipotentstabilization`, §4.1 of the source).

The unipotent stabilization of `(φ_+, φ_-)` coincides with that of `(φ_-, φ_+)`, **up to
transposition** (clauses `RQ2-4.04-H1`, `RQ2-4.04-C1`): transposing the input pair transposes the
output pair, componentwise and on the nose.

@census    RQ2-4.04
@source    rmk:unipotentstabilization
@clauses   RQ2-4.04-H1, RQ2-4.04-C1
@imports   none
@divergence EXTRA BINDER, disclosed (G2 finding C-2; not a weakening): `hgal : IsGalois K L`
is an argument here but is **not** clause `RQ2-4.01-H1`, whose text is only "L/K is a QUADRATIC
field extension" (`hquad` is that clause).  `IsGalois` follows from H1 + H2 — degree 2 is normal,
separable since `char K ≠ 2` — so the covered class is exactly the source's; it is a binder only
because mathlib has no one-step lemma for it at the pin.  Argument: module docstring, "The
standing hypotheses".
-/
theorem stabilization_symm (h2 : (2 : K) ≠ 0) (hgal : IsGalois K L)
    (hquad : Module.finrank K L = 2) (τ : Gal(L/K)) (hτne : τ ≠ 1)
    {Wp Wm : Submodule L (L ⊗[K] WK)}
    (φp : Wp ≃ₗ[L] twist τ Wm) (φm : Wm ≃ₗ[L] twist τ Wp) (e : ℕ) :
    (stabilization h2 hgal hquad τ hτne φm φp e).1
        = (stabilization h2 hgal hquad τ hτne φp φm e).2
      ∧ (stabilization h2 hgal hquad τ hτne φm φp e).2
        = (stabilization h2 hgal hquad τ hτne φp φm e).1 := by
  have h := stabilizationSeq_symm h2 (aut_mul_self hgal hquad τ)
    (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) e
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end RationalQuivers.Unipotent
