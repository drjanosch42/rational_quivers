import RationalQuivers.Unipotent.Stabilization

/-!
# The addenda of `cor:unipotentstabilization` relative to an identification (`rmk:stabilizationaddenda`)

Formalizes part (ii) of `rmk:stabilizationaddenda` (§4.1 of `latex/rational_quivers.tex`, census
`RQ2-4.10`): the recursion of `cor:unipotentstabilization` read in `End_L(W_+)` through an arbitrary
`L`-linear identification `e : W_-^τ ≃ W_+`.

## Main results
* `RationalQuivers.Unipotent.stabilizationSeq_addendum_via` — commuting unipotent `P_0`, `Q_0` stay
  commuting and unipotent along the recursion (`RQ2-4.10`, claimant).
* `RationalQuivers.Unipotent.asEndVia_eq_asEndConjVia` — `P_0 = Q_0` implies `P_k = Q_k` for all `k`.
* `RationalQuivers.Unipotent.eq_one_of_sq_eq_one_of_unipotent` — a unipotent square root of `𝟏` is `𝟏`.

**Moved, v2 T0 (WP-7, 2026-10-17).** This section is the `GeneralisedAddendum` section of
`Gelfand/Stabilization.lean` at `final-release-v1`, moved verbatim (code unchanged) into `Unipotent/`
and from namespace `RationalQuivers.Gelfand` to `RationalQuivers.Unipotent` (BLUEPRINT OQ-9, approved
2026-10-16); the renamed declarations are listed in `workflow/v2/stages/T0/DECL-ALLOWLIST.tsv`. Every
dependency already lived in `Unipotent/`; the users in `Gelfand/` open `RationalQuivers.Unipotent`, so
no proof changed.
-/

open scoped TensorProduct

namespace RationalQuivers.Unipotent

/-! ### `E3` — the addendum of `cor:unipotentstabilization`, off the `W_± = W_∓^τ` shape

`stages/S8/DESIGN-NOTES.md` §13.4's missing engine `E3`, obtained **on S8's own layer** under
coordinator ruling `R-S8-21`: no `Unipotent/` statement, proof or instance is touched, and no
hypothesis `hWp : twist τ Wm = Wp` is assumed anywhere below.

S6's `Unipotent.stabilizationSeq_addendum` reads the pair `(φ_+, φ_-^τ)` as a pair of
endomorphisms of `W_+` through `LinearEquiv.ofEq _ _ hWp`, so it needs `W_-^τ = W_+`.  The `(⋆)`
run of §5.2 has `W_+ = W_- = M_{-(ℓ-1)}` and `W_-^τ = M_{ℓ-1}`, so that hypothesis is **false**
for it — the instantiation `AN-38` identified (ruling `R-S8-8`) and the one the source has itemized
since the author's ruling of 2026-09-11 — which is exactly the obstacle recorded as `E3`
obstacle (a).

The observation that removes it: the *only* thing S6's induction asks of `LinearEquiv.ofEq _ _ hWp`
is that it be **some** `L`-linear equivalence `W_-^τ ≃ W_+`.  Through any such `e` the pair becomes
`P := e ∘ φ_+`, `Q := φ_-^τ ∘ e⁻¹` in `End_L(W_+)`, with `Q ∘ P = φ_-^τ ∘ φ_+` independent of `e`,
and the recursion is the same one, `P_{k+1} = ½(P_k + Q_k^{-1})`, `Q_{k+1} = ½(Q_k + P_k^{-1})`.
The `(⋆)` run does have such an equivalence — the one `eq:limitsquarerootdiagram0` itself uses,
which identifies both of `M_{∓(ℓ-1)}` with `V(⋆)`.

The generalisation is **strictly weaker in hypotheses** than S6's: taking `e = LinearEquiv.ofEq _ _
hWp` gives `asEndVia e = Unipotent.asEnd hWp` and `asEndConjVia hτ e = Unipotent.asEndConj hτ hWp`
definitionally, and `stabilizationSeq_addendum_via` then has S6's `stabilizationSeq_addendum` as an
instance (it drops S6's `hWm`, which is used there only to move the minus-side unipotency across —
here that hypothesis is stated on the plus side to begin with).
-/

section GeneralisedAddendum

open RationalQuivers.Unipotent

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable {WK : Type} [AddCommGroup WK] [Module K WK]
variable {τ : Gal(L/K)} {Wp Wm : Submodule L (L ⊗[K] WK)}

/-- `φ_+ : W_+ → W_-^τ` read as an endomorphism of `W_+` through an **arbitrary** identification
`e : W_-^τ ≃ W_+`.  With `e = LinearEquiv.ofEq _ _ hWp` this is `Unipotent.asEnd hWp`.
@census none (helper: the `E3` engine, `R-S8-21`) -/
def asEndVia (e : twist τ Wm ≃ₗ[L] Wp) (f : Wp →ₗ[L] twist τ Wm) : Module.End L Wp :=
  e.toLinearMap.comp f

/-- `φ_-^τ : W_-^τ → W_+` read as an endomorphism of `W_+` through the same identification.
With `e = LinearEquiv.ofEq _ _ hWp` this is `Unipotent.asEndConj hτ hWp`.
@census none (helper: the `E3` engine, `R-S8-21`) -/
def asEndConjVia (hτ : τ * τ = 1) (e : twist τ Wm ≃ₗ[L] Wp) (f : Wm →ₗ[L] twist τ Wp) :
    Module.End L Wp :=
  (twistConj hτ f).comp e.symm.toLinearMap

/-- `Q ∘ P = φ_-^τ ∘ φ_+`: the composite does not see the identification.  @census none (helper) -/
theorem asEndConjVia_comp_asEndVia (hτ : τ * τ = 1) (e : twist τ Wm ≃ₗ[L] Wp)
    (φp : Wp →ₗ[L] twist τ Wm) (φm : Wm →ₗ[L] twist τ Wp) :
    asEndConjVia hτ e φm * asEndVia e φp = (twistConj hτ φm).comp φp := by
  refine LinearMap.ext fun x => ?_
  show twistConj hτ φm (e.symm (e (φp x))) = twistConj hτ φm (φp x)
  rw [e.symm_apply_apply]

/-- With `e = LinearEquiv.ofEq _ _ hWp` the generalisation **is** S6's reading.
@census none (helper) -/
theorem asEndVia_ofEq (hWp : twist τ Wm = Wp) (f : Wp →ₗ[L] twist τ Wm) :
    asEndVia (LinearEquiv.ofEq _ _ hWp) f = Unipotent.asEnd hWp f := rfl

theorem asEndConjVia_ofEq (hτ : τ * τ = 1) (hWp : twist τ Wm = Wp)
    (f : Wm →ₗ[L] twist τ Wp) :
    asEndConjVia hτ (LinearEquiv.ofEq _ _ hWp) f = Unipotent.asEndConj hτ hWp f := rfl

variable (h2 : (2 : K) ≠ 0) (hτ : τ * τ = 1)

include h2 in
/-- The plus-step in `End(W_+)`, through an arbitrary `e`: `½(P + Q^{-1})`.  @census none -/
theorem asEndVia_stabilizationStep (e : twist τ Wm ≃ₗ[L] Wp) (φp : Wp →ₗ[L] twist τ Wm)
    (φm : Wm →ₗ[L] twist τ Wp) (hm : HasInverse (twistConj hτ φm)) :
    asEndVia e (stabilizationStep h2 hτ φp φm)
      = half (two_ne_zero_of_base (L := L) h2) •
          (asEndVia e φp + Ring.inverse (asEndConjVia hτ e φm)) := by
  have hι : HasInverse (e.symm.toLinearMap : Wp →ₗ[L] twist τ Wm) :=
    hasInverse_of_linearEquiv _
  have hQinv : Ring.inverse (asEndConjVia hτ e φm)
      = e.toLinearMap.comp (linInv (twistConj hτ φm)) := by
    rw [ring_inverse_eq_linInv, asEndConjVia, linInv_comp_eq hm hι, linInv_coe e.symm]
    rfl
  rw [hQinv]
  simp only [asEndVia, stabilizationStep, LinearMap.comp_smul, LinearMap.comp_add]

include h2 in
/-- The conjugated minus-step in `End(W_+)`, through an arbitrary `e`: `½(Q + P^{-1})`.
@census none -/
theorem asEndConjVia_stabilizationStep (e : twist τ Wm ≃ₗ[L] Wp) (φp : Wp →ₗ[L] twist τ Wm)
    (φm : Wm →ₗ[L] twist τ Wp) (hp : HasInverse φp) :
    asEndConjVia hτ e (stabilizationStep h2 hτ φm φp)
      = half (two_ne_zero_of_base (L := L) h2) •
          (asEndConjVia hτ e φm + Ring.inverse (asEndVia e φp)) := by
  have hι : HasInverse (e.toLinearMap : twist τ Wm →ₗ[L] Wp) := hasInverse_of_linearEquiv _
  have hPinv : Ring.inverse (asEndVia e φp) = (linInv φp).comp e.symm.toLinearMap := by
    rw [ring_inverse_eq_linInv, asEndVia, linInv_comp_eq hι hp, linInv_coe e]
  rw [hPinv]
  simp only [asEndConjVia]
  rw [twistConj_stabilizationStep h2 hτ φp φm hp]
  simp only [LinearMap.smul_comp, LinearMap.add_comp]

/-- Invertibility of `φ_+` read off its avatar, through an arbitrary `e`.  @census none -/
theorem hasInverse_of_isUnit_asEndVia (e : twist τ Wm ≃ₗ[L] Wp) (φp : Wp →ₗ[L] twist τ Wm)
    (h : IsUnit (asEndVia e φp)) : HasInverse φp := by
  have hEq : φp = (e.symm.toLinearMap).comp (asEndVia e φp) := by
    refine LinearMap.ext fun x => ?_
    show φp x = e.symm (e (φp x))
    rw [e.symm_apply_apply]
  rw [hEq]
  exact (hasInverse_of_linearEquiv e.symm).comp ((hasInverse_iff_isUnit _).mpr h)

/-- Invertibility of `φ_-^τ` read off its avatar, through an arbitrary `e`.  @census none -/
theorem hasInverse_twistConj_of_isUnit_asEndConjVia (e : twist τ Wm ≃ₗ[L] Wp)
    (φm : Wm →ₗ[L] twist τ Wp) (h : IsUnit (asEndConjVia hτ e φm)) :
    HasInverse (twistConj hτ φm) := by
  have hEq : twistConj hτ φm = (asEndConjVia hτ e φm).comp e.toLinearMap := by
    refine LinearMap.ext fun x => ?_
    show twistConj hτ φm x = twistConj hτ φm (e.symm (e x))
    rw [e.symm_apply_apply]
  rw [hEq]
  exact ((hasInverse_iff_isUnit _).mpr h).comp (hasInverse_of_linearEquiv _)

include h2 in
/-- **`E3`** — the addendum of `cor:unipotentstabilization`, generalised off `W_± = W_∓^τ`.

Through **any** identification `e : W_-^τ ≃ W_+`: if `φ_+` and `φ_-^τ` are unipotent endomorphisms
of `W_+` which commute (`eq:unipotentcommutators0`, `eq:unipotentnilpotency0` at `k = 0`), then so
are all their iterates — `eq:unipotentcommutatorsk`, `eq:unipotentnilpotencyk`.  This is
`Unipotent.stabilizationSeq_addendum` with `hWp`/`hWm` removed; its proof is S6's induction, whose
`zero` case here is the hypothesis itself (S6 needs `hWm` there only to move `hum` from the minus
side to the plus side).

This is also the claimant of `rmk:stabilizationaddenda` (census `RQ2-4.10`), bound by a
docstring-only `R-PROC-4` amendment of frozen S8 (coordinator ruling `R-FR-5`, 2026-10-02); until
then it read `@census none (helper: the E3 engine, R-S8-21; stages/S8/DESIGN-NOTES.md §14)`.

@census    RQ2-4.10
@source    rmk:stabilizationaddenda
@clauses   RQ2-4.10-Hs1, RQ2-4.10-H1, RQ2-4.10-H2, RQ2-4.10-C1, RQ2-4.10-H3, RQ2-4.10-C2, RQ2-4.10-C3, RQ2-4.10-C4, RQ2-4.10-C5
@imports   none
@divergence Part (ii) is this theorem: `e` is the identification `twist τ Wm ≃ₗ[L] Wp`, `P_k` and
`Q_k` are `asEndVia e` and `asEndConjVia hτ e` of the `k`-th iterate, and the conclusion is `C3`
for every `k`; `C2`'s recursion is the rewriting `asEndVia_stabilizationStep` /
`asEndConjVia_stabilizationStep` the induction step uses; `C4` is the same-module
`asEndVia_eq_asEndConjVia`; `C5` (`e = 1` recovers the Addendum) is the reading of S6's
`Unipotent.stabilizationSeq_addendum` as the case `W_± = W_∓^τ`, not a separate statement. Part (i)
(`H1`, `H2`, `C1`, naturality in a second datum along a not necessarily invertible `f`) is
`Gelfand.RationalStructure.seq_natural` / `Gelfand.RationalStructure.lim_natural` in
`Gelfand/RationalStructure/Stabilization.lean` (stated on `StabInput`), stated for the `L_E`-runs
`StabInput` of §5 (over a quadratic `D' : SqrtNegOneExt E`) rather than for an abstract datum over a
quadratic `L/K`; `Hs1` is this section's standing variables (`h2`, `hτ`). Partial,
disclosed; no statement is moved by this amendment. -/
theorem stabilizationSeq_addendum_via (e : twist τ Wm ≃ₗ[L] Wp) (φp : Wp →ₗ[L] twist τ Wm)
    (φm : Wm →ₗ[L] twist τ Wp)
    (hcomm : Commute (asEndVia e φp) (asEndConjVia hτ e φm))
    (hup : ∃ mp : Module.End L Wp, IsNilpotent mp ∧ asEndVia e φp = 1 + mp)
    (huq : ∃ mq : Module.End L Wp, IsNilpotent mq ∧ asEndConjVia hτ e φm = 1 + mq) (k : ℕ) :
    Commute (asEndVia e (stabilizationSeq h2 hτ φp φm k).1)
        (asEndConjVia hτ e (stabilizationSeq h2 hτ φp φm k).2)
      ∧ (∃ mp : Module.End L Wp, IsNilpotent mp
          ∧ asEndVia e (stabilizationSeq h2 hτ φp φm k).1 = 1 + mp)
      ∧ (∃ mq : Module.End L Wp, IsNilpotent mq
          ∧ asEndConjVia hτ e (stabilizationSeq h2 hτ φp φm k).2 = 1 + mq) := by
  have hL : (2 : L) ≠ 0 := two_ne_zero_of_base (L := L) h2
  induction k with
  | zero => exact ⟨hcomm, hup, huq⟩
  | succ k ih =>
      obtain ⟨hc, ⟨mp, hmp, hP⟩, ⟨mq, hmq, hQ⟩⟩ := ih
      have hPu : IsUnit (asEndVia e (stabilizationSeq h2 hτ φp φm k).1) := by
        rw [hP]; exact isUnit_one_add_of_isNilpotent hmp
      have hQu : IsUnit (asEndConjVia hτ e (stabilizationSeq h2 hτ φp φm k).2) := by
        rw [hQ]; exact isUnit_one_add_of_isNilpotent hmq
      have hp' : HasInverse (stabilizationSeq h2 hτ φp φm k).1 :=
        hasInverse_of_isUnit_asEndVia e _ hPu
      have hm' : HasInverse (twistConj hτ (stabilizationSeq h2 hτ φp φm k).2) :=
        hasInverse_twistConj_of_isUnit_asEndConjVia hτ e _ hQu
      have hmpq : Commute mp mq := Unipotent.commute_of_commute_one_add (by rw [← hP, ← hQ]; exact hc)
      rw [stabilizationSeq_succ_fst, stabilizationSeq_succ_snd]
      refine ⟨?_, ?_, ?_⟩
      · rw [asEndVia_stabilizationStep h2 hτ e _ _ hm',
          asEndConjVia_stabilizationStep h2 hτ e _ _ hp']
        exact commute_avg hL hPu hQu hc
      · rw [asEndVia_stabilizationStep h2 hτ e _ _ hm']
        exact avg_one_add hL hP hQ hmp hmq hmpq
      · rw [asEndConjVia_stabilizationStep h2 hτ e _ _ hp']
        exact avg_one_add hL hQ hP hmq hmp hmpq.symm

include h2 in
/-- **The two recursions are the same recursion.**  If `P₀ = Q₀` then `P_k = Q_k` at every step —
`P_{k+1} = ½(P_k + Q_k^{-1})` and `Q_{k+1} = ½(Q_k + P_k^{-1})` are literally interchanged by that
hypothesis.  For the `(⋆)` run `P₀ = Q₀` is `X⋆ = Y⋆` (`RQ-5.05-C18`), and this is what makes
`(φ^{(∞)}_⋆)² = 𝟏` available without `eq:conjugateinversestar`.
@census none (helper: the `E3` engine, `R-S8-21`) -/
theorem asEndVia_eq_asEndConjVia (e : twist τ Wm ≃ₗ[L] Wp) (φp : Wp →ₗ[L] twist τ Wm)
    (φm : Wm →ₗ[L] twist τ Wp)
    (hcomm : Commute (asEndVia e φp) (asEndConjVia hτ e φm))
    (hup : ∃ mp : Module.End L Wp, IsNilpotent mp ∧ asEndVia e φp = 1 + mp)
    (huq : ∃ mq : Module.End L Wp, IsNilpotent mq ∧ asEndConjVia hτ e φm = 1 + mq)
    (h0 : asEndVia e φp = asEndConjVia hτ e φm) (k : ℕ) :
    asEndVia e (stabilizationSeq h2 hτ φp φm k).1
      = asEndConjVia hτ e (stabilizationSeq h2 hτ φp φm k).2 := by
  induction k with
  | zero => exact h0
  | succ k ih =>
      obtain ⟨-, ⟨mp, hmp, hP⟩, ⟨mq, hmq, hQ⟩⟩ :=
        stabilizationSeq_addendum_via h2 hτ e φp φm hcomm hup huq k
      have hPu : IsUnit (asEndVia e (stabilizationSeq h2 hτ φp φm k).1) := by
        rw [hP]; exact isUnit_one_add_of_isNilpotent hmp
      have hQu : IsUnit (asEndConjVia hτ e (stabilizationSeq h2 hτ φp φm k).2) := by
        rw [hQ]; exact isUnit_one_add_of_isNilpotent hmq
      have hp' : HasInverse (stabilizationSeq h2 hτ φp φm k).1 :=
        hasInverse_of_isUnit_asEndVia e _ hPu
      have hm' : HasInverse (twistConj hτ (stabilizationSeq h2 hτ φp φm k).2) :=
        hasInverse_twistConj_of_isUnit_asEndConjVia hτ e _ hQu
      rw [stabilizationSeq_succ_fst, stabilizationSeq_succ_snd,
        asEndVia_stabilizationStep h2 hτ e _ _ hm',
        asEndConjVia_stabilizationStep h2 hτ e _ _ hp', ih]

/-- **A unipotent square root of `𝟏` is `𝟏`.**  The last step of `RQ-5.05-C19`, in the semiring
`End_L(W_+)` (which carries no `Ring` instance at the pin, `MD-S6-06`, so this is written
additively).  @census none (helper: the `E3` engine) -/
theorem eq_one_of_sq_eq_one_of_unipotent {U : Submodule L (L ⊗[K] WK)}
    (hL : (2 : L) ≠ 0) {A m : Module.End L U} (hm : IsNilpotent m) (hA : A = 1 + m)
    (hsq : A * A = 1) : A = 1 := by
  have hexp : A * A = 1 + ((2 : L) • m + m * m) := by
    rw [hA, mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, two_smul]
    abel
  have hzero : (2 : L) • m + m * m = 0 := by
    have h : (1 : Module.End L U) + ((2 : L) • m + m * m) = 1 := hexp.symm.trans hsq
    refine end_add_right_cancel (h := (1 : Module.End L U)) ?_
    rw [zero_add, add_comm]
    exact h
  have hfac : m * ((2 : L) • (1 : Module.End L U) + m) = (2 : L) • m + m * m := by
    rw [mul_add, mul_smul_comm, mul_one]
  have hunit : IsUnit ((2 : L) • (1 : Module.End L U) + m) :=
    isUnit_add_of_isNilpotent (isUnit_smul_one_end hL) hm
      ((Commute.one_right m).smul_right (2 : L)).symm
  obtain ⟨u, hu⟩ := hunit
  have hm0 : m = 0 := by
    calc m = m * ((u : Module.End L U) * (↑u⁻¹ : Module.End L U)) := by
            rw [u.mul_inv, mul_one]
      _ = (m * (u : Module.End L U)) * (↑u⁻¹ : Module.End L U) := (mul_assoc _ _ _).symm
      _ = 0 := by rw [hu, hfac, hzero, zero_mul]
  rw [hA, hm0, add_zero]

end GeneralisedAddendum

end RationalQuivers.Unipotent
