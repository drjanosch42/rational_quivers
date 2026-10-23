import RationalQuivers.Gelfand.Equivalence.Full
import RationalQuivers.Gelfand.Split.EssSurj
import RationalQuivers.Unipotent.SquareRoots
import RationalQuivers.Descent.Galois

/-!
# essential surjectivity, the construction and its `c`-clauses (§5.3, Steps O-18a/b)

`EssSurjData V` **extends** T2's `Split.SplitEssSurjData` (the `c`-free core, Step O-18a, read via
`D.toSplitEssSurjData`, never copied) by the form, `c` and the `C16` pins; the vertex operators'
`c`-conjugates (`conjBy_nOp`, `conjBy_sqrtPhi`, `conjBy_xiOp`, `conjBy_sqrtOfScalarPlusNilpotent`) and
the conjugation on the carrier (`essConjAmb_xAmb` = `eq:Xconjugation`, `essConj_X/Y/H`) — Step O-18b.

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Equivalence.lean (§CrossConj … §VertexOperators, §E3 prelude, §E2Carrier … §E2Conj)` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.EssSurj.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

*(2026-10-21, O-V2-6 round 2.)*  Two carried docstrings below name v1 declarations that v2 deleted
or moved.  `stabilizationSeq_addendum_via`, placed there in v1's `Gelfand/Stabilization.lean`
(deleted at WP-13, `ae9eda9`), moved at WP-7 to `Unipotent/Addendum.lean` as
`Unipotent.stabilizationSeq_addendum_via`.  `RQ-5.02`'s split case `E_Qi_equivalence` was deleted
with the v1 Q-chain at WP-13.  On the v2 line `prop:splitequivalence` (`RQ2-5.02`) is claimed by
`Split.equivalence` (`Gelfand/Split/EssSurj.lean`).

@census none (module)
-/

namespace RationalQuivers.Gelfand.EssSurj

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {Dq : SqrtNegOneExt E}
open scoped TensorProduct Classical

variable {ℓ : ℕ}

/-! ### Helpers for `essSurj_operators` (`C10`–`C12`, `C14`)

The four groups below are, in order: two generic facts about linear maps and endomorphism
algebra; the path-composite form of nilpotency, which is what `Rep.IsNilpotent` gives at a loop;
the cross-space semi-linear conjugation `conjBy` (the two-space companion of
`Unipotent.semilinearConj`, needed because `φ_{v,c} : V(v) → V(c·v)` changes the space) together
with the transport of `def:squareroots` along it; and `pin_compose`/`pin_compose'`, which read a
composite `XY` or `YX` of the pinned formulas of `EssSurjData` on `V(•)`. -/




section CrossConj

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable {W₁ W₂ : Type} [AddCommGroup W₁] [Module L W₁] [AddCommGroup W₂] [Module L W₂]
variable (σ : L ≃ₐ[K] L) (ψ : W₁ ≃+ W₂) (hψ : ∀ (a : L) (x : W₁), ψ (a • x) = σ a • ψ x)

/-- Conjugation `φ ↦ ψ φ ψ^{-1}` of an `L`-linear endomorphism by a `σ`-semi-linear additive
isomorphism **between two spaces**.  `Unipotent.semilinearConj` is the case `W₁ = W₂`; the rational
structure `φ_{v,c} : V(v) → V(c·v)` of `Rep^nil(Γ_ℚ)` moves the space, so `C12` needs this form.
@census none (helper) -/
def conjBy (φ : Module.End L W₁) : Module.End L W₂ where
  toFun x := ψ (φ (ψ.symm x))
  map_add' x y := by simp
  map_smul' c x := by
    have hsymm : ψ.symm (c • x) = σ.symm c • ψ.symm x := by
      apply ψ.injective; rw [hψ]; simp
    simp only [hsymm, map_smul, RingHom.id_apply, hψ]
    simp

@[simp] theorem conjBy_apply (φ : Module.End L W₁) (x : W₂) :
    conjBy σ ψ hψ φ x = ψ (φ (ψ.symm x)) := rfl

/-- @census none (helper) -/
theorem conjBy_one : conjBy σ ψ hψ 1 = 1 := by ext x; simp

/-- @census none (helper) -/
theorem conjBy_mul (a b : Module.End L W₁) :
    conjBy σ ψ hψ (a * b) = conjBy σ ψ hψ a * conjBy σ ψ hψ b := by ext x; simp

/-- @census none (helper) -/
theorem conjBy_add (a b : Module.End L W₁) :
    conjBy σ ψ hψ (a + b) = conjBy σ ψ hψ a + conjBy σ ψ hψ b := by ext x; simp

/-- @census none (helper) -/
theorem conjBy_zero : conjBy σ ψ hψ 0 = 0 := by ext x; simp

/-- @census none (helper) -/
theorem conjBy_pow (a : Module.End L W₁) (n : ℕ) :
    conjBy σ ψ hψ (a ^ n) = (conjBy σ ψ hψ a) ^ n := by
  induction n with
  | zero => simp [conjBy_one]
  | succ n ih => rw [pow_succ, pow_succ, conjBy_mul, ih]

/-- @census none (helper) -/
theorem conjBy_smul (c : L) (a : Module.End L W₁) :
    conjBy σ ψ hψ (c • a) = σ c • conjBy σ ψ hψ a := by ext x; simp [hψ]

/-- @census none (helper) -/
theorem conjBy_isNilpotent {a : Module.End L W₁} (h : IsNilpotent a) :
    IsNilpotent (conjBy σ ψ hψ a) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [← conjBy_pow, hn, conjBy_zero]⟩

/-- **`def:squareroots` transports along a `σ`-semi-linear isomorphism of two spaces**, provided
the chosen scalar square root is `σ`-fixed.  The two-space companion of
`Unipotent.sqrt_galois_equivariant`, proved from `sqrtOfScalarPlusNilpotent_unique`: the conjugate
of `φ^{1/2}` is `γ·𝟏 + nilpotent` and squares to the conjugate of `φ`.  @census none (helper) -/
theorem conjBy_sqrtOfScalarPlusNilpotent (h2 : (2 : L) ≠ 0) (γ : Lˣ) (hγ : σ (γ : L) = (γ : L))
    (φ n : Module.End L W₁) (hn : IsNilpotent n) (hφ : φ = ((γ : L) ^ 2) • 1 + n) :
    conjBy σ ψ hψ (sqrtOfScalarPlusNilpotent h2 γ φ)
      = sqrtOfScalarPlusNilpotent h2 γ (conjBy σ ψ hψ φ) := by
  have hval : ((((γ ^ 2)⁻¹ : Lˣ)) : L) * ((γ : L) ^ 2) = 1 := by
    rw [Units.val_inv_eq_inv_val, ← Units.val_pow_eq_pow_val, inv_mul_cancel₀]
    exact Units.ne_zero _
  have hρ : ((((γ ^ 2)⁻¹ : Lˣ)) : L) • φ = 1 + ((((γ ^ 2)⁻¹ : Lˣ)) : L) • n := by
    rw [hφ, smul_add, smul_smul, hval, one_smul]
  obtain ⟨-, hSnil, -⟩ := sqrt_spec h2 (((((γ ^ 2)⁻¹ : Lˣ)) : L) • φ)
    (((((γ ^ 2)⁻¹ : Lˣ)) : L) • n) (IsNilpotent.smul' hn _) hρ
  set S := sqrtOfScalarPlusNilpotent h2 γ φ with hS
  have hSshape : S = (γ : L) • 1 + (γ : L) • (sqrt h2 ((((γ ^ 2)⁻¹ : Lˣ) : L) • φ) - 1) := by
    rw [hS, sqrtOfScalarPlusNilpotent, smul_sub]; abel
  refine (sqrtOfScalarPlusNilpotent_unique h2 γ (conjBy σ ψ hψ φ) (conjBy σ ψ hψ S)
    (conjBy σ ψ hψ ((γ : L) • (sqrt h2 ((((γ ^ 2)⁻¹ : Lˣ) : L) • φ) - 1)))
    (conjBy_isNilpotent σ ψ hψ (IsNilpotent.smul' hSnil _)) ?_ ?_)
  · rw [hSshape, conjBy_add, conjBy_smul, conjBy_one, hγ]
  · rw [← conjBy_pow]
    congr 1
    rw [hS]
    exact sqrtOfScalarPlusNilpotent_sq h2 γ φ n hn hφ

end CrossConj

/-! ### `prop:unipotentsquareroots` clause (e) — the square root is natural in an intertwiner

`prop:unipotentsquareroots`'s square root is the value of a Newton iteration whose every step is
built from `φ`, `+` and the inverse of the previous iterate.  All three commute with an
intertwiner `A` of two *different* spaces — the inverse because both iterates are units — so
`A φ_1 = φ_2 A` forces `A φ_1^{1/2} = φ_2^{1/2} A`.  This is `sqrt_galois_equivariant` /
`conjBy_sqrtOfScalarPlusNilpotent` for a map that is **not** required to be invertible.

**This is now a printed clause of the source**, not an addition of the tree: on 2026-09-11 the
paper author ruled (`workflow/reports/AUTHOR-QUEUE.md`, the `AUTHOR RULING, 2026-09-11` block, the
subsidiary ruling on `AN-41`/`AN-42`) that `prop:unipotentsquareroots` gains a fifth itemized
property **(e)** — naturality along an arbitrary, not necessarily invertible, `L`-linear
intertwiner, `eq:squarerootnaturality` — with a one-sentence inductive proof along the same
recurrence.  The census books it as the new clause **`RQ-4.05-C7`** at revision r14 (tag
`census-v1.11`); `sqrt_natural` and `sqrtOfScalarPlusNilpotent_natural` below are what render it.
Until that ruling it was carried here as a tree-side helper, needed for the corrected left-hand
squares of the then-`RQ-5.05-C25` (`AN-41`, ruling `R-S8-17`), whose intertwiner is the edge map
`φ_{a₋} : V(−) → V(⋆)`. -/

section SqrtNatural

variable {L : Type} [Field L] {W₁ W₂ : Type} [AddCommGroup W₁] [Module L W₁]
  [AddCommGroup W₂] [Module L W₂]

/-- An intertwiner of two units intertwines their inverses.

**Relocated 2026-09-11 under `R-PROC-4` (round 3, coordinator ruling `R-ERR-2`)**: the content is
now `RationalQuivers.Unipotent.inverse_natural`, in `RQ-4.05`'s own stage S6
(`Unipotent/SquareRoots.lean`); this is a thin alias kept so that S8's declaration set is
unchanged.  @census none (helper) -/
theorem inverse_natural {S₁ : Module.End L W₁} {S₂ : Module.End L W₂}
    (hu₁ : IsUnit S₁) (hu₂ : IsUnit S₂) (A : W₁ →ₗ[L] W₂)
    (hA : ∀ x, A (S₁ x) = S₂ (A x)) (x : W₁) :
    A (Ring.inverse S₁ x) = Ring.inverse S₂ (A x) :=
  RationalQuivers.Unipotent.inverse_natural hu₁ hu₂ A hA x

/-- The Newton iteration of `prop:unipotentsquareroots` is natural in an intertwiner.

**Relocated 2026-09-11 under `R-PROC-4` (round 3, `R-ERR-2`)** to
`RationalQuivers.Unipotent.sqrtSeq_natural` (stage S6); thin alias.  @census none (helper) -/
theorem sqrtSeq_natural (h2 : (2 : L) ≠ 0) {φ₁ : Module.End L W₁} {φ₂ : Module.End L W₂}
    (h₁ : IsNilpotent (φ₁ - 1)) (h₂ : IsNilpotent (φ₂ - 1))
    (A : W₁ →ₗ[L] W₂) (hA : ∀ x, A (φ₁ x) = φ₂ (A x)) (k : ℕ) (x : W₁) :
    A (sqrtSeq h2 φ₁ k x) = sqrtSeq h2 φ₂ k (A x) :=
  RationalQuivers.Unipotent.sqrtSeq_natural h2 h₁ h₂ A hA k x

/-- `prop:unipotentsquareroots` clause (e) (`eq:squarerootnaturality`): the square root is natural
in an arbitrary `L`-linear intertwiner `A`, invertible or not.

**Relocated 2026-09-11 under `R-PROC-4` (round 3 of the seven-errata execution, coordinator ruling
`R-ERR-2`).**  Clause `RQ-4.05-C7` belongs to `prop:unipotentsquareroots`, an **S6** row, and is
now claimed by `RationalQuivers.Unipotent.sqrt_natural` next to `sqrt_spec`; this S8 declaration is
a thin alias and **no longer cites the clause** — before the move `RQ-4.05-C7` was cited only from
here, which `rqaudit clauses` reported as `CLAUSE-UNCITED RQ-4.05-C7` (no claimant bound to
`RQ-4.05`).

@census none (helper; the S6 claimant of `RQ-4.05-C7` is `Unipotent.sqrt_natural`) -/
theorem sqrt_natural (h2 : (2 : L) ≠ 0) {φ₁ : Module.End L W₁} {φ₂ : Module.End L W₂}
    (h₁ : IsNilpotent (φ₁ - 1)) (h₂ : IsNilpotent (φ₂ - 1))
    (A : W₁ →ₗ[L] W₂) (hA : ∀ x, A (φ₁ x) = φ₂ (A x)) (x : W₁) :
    A (sqrt h2 φ₁ x) = sqrt h2 φ₂ (A x) :=
  RationalQuivers.Unipotent.sqrt_natural h2 h₁ h₂ A hA x

/-- `prop:unipotentsquareroots` clause (e), second sentence: the same naturality for the
normalization of `def:squareroots`, both square roots taken with respect to the same `γ`.

**Relocated 2026-09-11 under `R-PROC-4` (round 3, `R-ERR-2`)** to
`RationalQuivers.Unipotent.sqrtOfScalarPlusNilpotent_natural` (stage S6), which is where the
`def:squareroots` half of clause `RQ-4.05-C7` is now discharged; thin alias.
@census none (helper) -/
theorem sqrtOfScalarPlusNilpotent_natural (h2 : (2 : L) ≠ 0) (γ : Lˣ)
    {φ₁ : Module.End L W₁} {φ₂ : Module.End L W₂} {n₁ : Module.End L W₁} {n₂ : Module.End L W₂}
    (hn₁ : IsNilpotent n₁) (hφ₁ : φ₁ = ((γ : L) ^ 2) • 1 + n₁)
    (hn₂ : IsNilpotent n₂) (hφ₂ : φ₂ = ((γ : L) ^ 2) • 1 + n₂)
    (A : W₁ →ₗ[L] W₂) (hA : ∀ x, A (φ₁ x) = φ₂ (A x)) (x : W₁) :
    A (sqrtOfScalarPlusNilpotent h2 γ φ₁ x) = sqrtOfScalarPlusNilpotent h2 γ φ₂ (A x) :=
  RationalQuivers.Unipotent.sqrtOfScalarPlusNilpotent_natural h2 γ hn₁ hφ₁ hn₂ hφ₂ A hA x

end SqrtNatural


/-! ### `C8`–`C25`: essential surjectivity — the construction, pinned to its formulas

**Repaired** (verifier findings `V-S8-4`, `V-S8-5`).  `EssSurjData` is the output of the source's
construction with **every** datum pinned: the components `M_n` are identified with `V(+)`, `V(⋆)`,
`V(−)` by the displayed ranges through actual linear isomorphisms (not `Nonempty` of one), and the
operators `X`, `Y` and the conjugation `c` are pinned on every component to the displayed formulas
`2X|_{M_{j-1}} = ξ^{(j)}_{•,+}`, `2Y|_{M_{j+1}} = ξ^{(j)}_{•,-}` (including the boundary cases
`j = ±ℓ`) and `c|_{M_j} = φ_{•,c}` (`eq:varphicj`).  A degenerate inhabitant is impossible for
`V ≠ 0`: the pins force `X ≠ 0` wherever `ξ ≠ 0`.  The **existence** of such data
(`essSurj_exists`) is the content of clauses `C9`, `C13`, `C15`, `C16` — that the pinned formulas
define a `(𝔤,K)`-module with a `ℚ`-structure — and the identities `C10`, `C11`, `C12`, `C14` are
stated about any such datum (`essSurj_operators`); the natural isomorphism `C17`–`C25`
(`essSurj_naturalIsomorphism`) is about the `𝔼_ℚ`-data of the constructed object. -/

section EssSurj

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2) (hℓ : 1 ≤ ℓ)

/-- The rational structure `φ_{v,c} : V(v) → V(c·v)` of a representation of `Γ_ℚ`.
@census none (helper) -/
noncomputable def Vphi (V : Gelfand.RationalStructure.RepNilQ hcard) (v : Fin 3) :
    Split.VM (Gelfand.RationalStructure.toSplitW hcard V) v ≃+ Split.VM (Gelfand.RationalStructure.toSplitW hcard V) (RQuiver.gelfandVertexSwap v) :=
  V.obj.toRep.φ' Dq.conj (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard v)

/-- **The essential-surjectivity construction, pinned** (clauses `C9`, `C13`, `C16`): a
`ℚ`-rational Harish-Chandra module `M = ⨁_{k} M_{2k+ε}` (an object of `HC_λ(𝔤,K)_ℚ`, hence a
`RationalSetup` with the finiteness conditions) whose components are **identified** with
`V(+)`, `V(⋆)`, `V(−)` on the displayed ranges (`isoPlus`, `isoStar`, `isoMinus`), whose `X` and `Y`
are the displayed formulas on every component, boundary cases `j = ±ℓ` included (`X_*`, `Y_*`),
and whose conjugation is `φ_c^M = Σ_j φ_c^{(j)}` (`conj_*`, `eq:varphicj`).

@census    none (auxiliary; carries census clauses `RQ-5.05-C9`, `RQ-5.05-C13`, `RQ-5.05-C16`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C9, RQ-5.05-C13, RQ-5.05-C16
@imports   none
@divergence none
@clauses   RQ2-5.12-S-O18b -/
structure EssSurjData (V : Gelfand.RationalStructure.RepNilQ hcard) extends Split.SplitEssSurjData hℓ (Gelfand.RationalStructure.toSplitW hcard V) where
  /-- the `ℚ`-form -/
  form : Type
  [formAddCommGroup : AddCommGroup form]
  [formModule : Module E form]
  /-- `M = L ⊗_E M_E` -/
  baseChange : (Dq.carrier ⊗[E] form) ≃ₗ[Dq.carrier] carrier
  /-- the conjugation of `M` -/
  conj : carrier ≃+ carrier
  conj_smul : ∀ (a : Dq.carrier) (v : carrier), conj (a • v) = Dq.conj a • conj v
  conj_involutive : Function.Involutive conj
  conj_baseChange : ∀ v : form, conj (baseChange ((1 : Dq.carrier) ⊗ₜ[E] v))
    = baseChange ((1 : Dq.carrier) ⊗ₜ[E] v)
  conj_comp : ∀ (n : ℤ) (v : carrier), v ∈ weight.comp n → conj v ∈ weight.comp (-n)
  conj_X : ∀ v, conj (weight.X v) = weight.Y (conj v)
  conj_Y : ∀ v, conj (weight.Y v) = weight.X (conj v)
  conj_H : ∀ v, conj (weight.H v) = -weight.H (conj v)
  /-- **`C16`** (`eq:varphicj`): `c|_{M_n} = φ_{+,c}` for `ℓ + 1 ≤ n` -/
  conj_plus : ∀ n : ℤ, ∀ (h1 : (ℓ : ℤ) + 1 ≤ n) (h2 : (n - ((ℓ : ℤ) + 1)) % 2 = 0),
    ∀ v (hv : v ∈ weight.comp n),
      conj v = (isoMinus (-n) (by omega) (by omega)).symm
        (Vphi hcard V 2 (isoPlus n h1 h2 ⟨v, hv⟩))
  /-- **`C16`**: `c|_{M_n} = φ_{⋆,c}` for `-(ℓ-1) ≤ n ≤ ℓ-1` -/
  conj_star : ∀ n : ℤ, ∀ (h1 : -((ℓ : ℤ) - 1) ≤ n) (h2 : n ≤ (ℓ : ℤ) - 1)
      (h3 : (n - ((ℓ : ℤ) + 1)) % 2 = 0),
    ∀ v (hv : v ∈ weight.comp n),
      conj v = (isoStar (-n) (by omega) (by omega) (by omega)).symm
        (Vphi hcard V 1 (isoStar n h1 h2 h3 ⟨v, hv⟩))
  /-- **`C16`**: `c|_{M_n} = φ_{-,c}` for `n ≤ -(ℓ+1)` -/
  conj_minus : ∀ n : ℤ, ∀ (h1 : n ≤ -((ℓ : ℤ) + 1)) (h2 : (n - ((ℓ : ℤ) + 1)) % 2 = 0),
    ∀ v (hv : v ∈ weight.comp n),
      conj v = (isoPlus (-n) (by omega) (by omega)).symm
        (Vphi hcard V 0 (isoMinus n h1 h2 ⟨v, hv⟩))

attribute [instance] EssSurjData.formAddCommGroup EssSurjData.formModule

namespace EssSurjData

variable {hcard hℓ} {V : Gelfand.RationalStructure.RepNilQ hcard} (D : EssSurjData hcard hℓ V)

/-- The `RationalSetupOver` of the constructed module, assembled from the core's weight datum and
the `c`-extension's fields.  @census none (spike; route (α)) -/
abbrev setup : RationalSetupOver ℓ E Dq D.form D.carrier where
  baseChange := D.baseChange
  weight := D.weight
  gic := D.gic
  conj := D.conj
  conj_smul := D.conj_smul
  conj_involutive := D.conj_involutive
  conj_baseChange := D.conj_baseChange
  conj_comp := D.conj_comp
  conj_X := D.conj_X
  conj_Y := D.conj_Y
  conj_H := D.conj_H

/-- The constructed Harish-Chandra module, as an object of `HC_λ(𝔤,K)_ℚ`.  @census none (helper) -/
noncomputable def toHCQObj : HCEObj ℓ E Dq where
  form := D.form
  carrier := D.carrier
  setup := D.setup
  admissible := D.admissible
  centralCharacter := D.centralCharacter
  fg := D.fg

/-- `φ^{(∞)}_+` of the constructed module, on `V(+)`.  @census none (helper) -/
noncomputable def limPlusV : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :=
  D.transport D.toPlus D.toPlus (Gelfand.RationalStructure.inputPlus D.setup).limPlus (fun v _ => (Gelfand.RationalStructure.inputPlus D.setup).limPlus_mem v)

/-- `φ^{(∞)}_-` of the constructed module, on `V(−)`.  @census none (helper) -/
noncomputable def limMinusV : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) :=
  D.transport D.toMinus D.toMinus (Gelfand.RationalStructure.inputMinus D.setup).limPlus
    (fun v _ => (Gelfand.RationalStructure.inputMinus D.setup).limPlus_mem v)

/-- `φ^{(∞)}_⋆` of the constructed module, `M_{-(ℓ-1)} → M_{ℓ-1}`, on `V(⋆)`.  @census none (helper) -/
noncomputable def limStarV : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :=
  D.transport D.toStarLo D.toStarHi (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus
    (fun v _ => by
      have h := (Gelfand.RationalStructure.inputStar D.setup hℓ).limPlus_mem v
      rwa [show -(Gelfand.RationalStructure.inputStar D.setup hℓ).idxMinus = (ℓ : ℤ) - 1 by simp [Gelfand.RationalStructure.inputStar]] at h)

/-- The rational structure `φ_{v,c}` **of `𝔼_ℚ(M)`** for the constructed `M`, read on `V(v)`
(an additive semi-linear map).  @census none (helper) -/
noncomputable def phiV (v : Fin 3) : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) v → Split.VM (Gelfand.RationalStructure.toSplitW hcard V) (RQuiver.gelfandVertexSwap v) :=
  match v with
  | 0 => fun x => D.toPlus ⟨Gelfand.RationalStructure.phiC hℓ D.toHCQObj 0 (D.toMinus.symm x : D.carrier),
      Gelfand.RationalStructure.phiC_mem hℓ D.toHCQObj 0 _⟩
  | 1 => fun x => D.toStarLo ⟨Gelfand.RationalStructure.phiC hℓ D.toHCQObj 1 (D.toStarLo.symm x : D.carrier),
      Gelfand.RationalStructure.phiC_mem hℓ D.toHCQObj 1 _⟩
  | 2 => fun x => D.toMinus ⟨Gelfand.RationalStructure.phiC hℓ D.toHCQObj 2 (D.toPlus.symm x : D.carrier),
      Gelfand.RationalStructure.phiC_mem hℓ D.toHCQObj 2 _⟩

end EssSurjData


/-! #### The three vertex operators `n_•`, `φ_•`, `ξ^{(j)}_{•,±}` and their `c`-conjugates -/

section VertexOperators

/-- `φ_{⋆,c}` intertwines `φ_{a₋}` with `φ_{a₊}` (`RQ-1.08-C9` at the edge `a₋`).
@census none (helper) -/
theorem Vphi_edge0 (V : Gelfand.RationalStructure.RepNilQ hcard) (m : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) :
    Vphi hcard V 1 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 m) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (Vphi hcard V 0 m) :=
  (RationalQuiver.Rep.φEdge'_φ' V.obj.toRep Dq.conj
    (f := Gelfand.RationalStructure.edgeQ hcard 0) (e := Gelfand.RationalStructure.edgeQ hcard 2) (Gelfand.RationalStructure.gelfandQ_smul_edge hcard 0)
    (a := Gelfand.RationalStructure.vtxQ hcard 0) (b := Gelfand.RationalStructure.vtxQ hcard 1) (a' := Gelfand.RationalStructure.vtxQ hcard 2) (b' := Gelfand.RationalStructure.vtxQ hcard 1)
    rfl rfl rfl rfl (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 0) (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 1) m).symm

/-- `RQ-1.08-C9` at the edge `b₋`.  @census none (helper) -/
theorem Vphi_edge1 (V : Gelfand.RationalStructure.RepNilQ hcard) (m : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Vphi hcard V 0 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 m) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (Vphi hcard V 1 m) :=
  (RationalQuiver.Rep.φEdge'_φ' V.obj.toRep Dq.conj
    (f := Gelfand.RationalStructure.edgeQ hcard 1) (e := Gelfand.RationalStructure.edgeQ hcard 3) (Gelfand.RationalStructure.gelfandQ_smul_edge hcard 1)
    (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 0) (a' := Gelfand.RationalStructure.vtxQ hcard 1) (b' := Gelfand.RationalStructure.vtxQ hcard 2)
    rfl rfl rfl rfl (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 1) (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 0) m).symm

/-- `RQ-1.08-C9` at the edge `a₊`.  @census none (helper) -/
theorem Vphi_edge2 (V : Gelfand.RationalStructure.RepNilQ hcard) (m : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :
    Vphi hcard V 1 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 m) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (Vphi hcard V 2 m) :=
  (RationalQuiver.Rep.φEdge'_φ' V.obj.toRep Dq.conj
    (f := Gelfand.RationalStructure.edgeQ hcard 2) (e := Gelfand.RationalStructure.edgeQ hcard 0) (Gelfand.RationalStructure.gelfandQ_smul_edge hcard 2)
    (a := Gelfand.RationalStructure.vtxQ hcard 2) (b := Gelfand.RationalStructure.vtxQ hcard 1) (a' := Gelfand.RationalStructure.vtxQ hcard 0) (b' := Gelfand.RationalStructure.vtxQ hcard 1)
    rfl rfl rfl rfl (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 2) (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 1) m).symm

/-- `RQ-1.08-C9` at the edge `b₊`.  @census none (helper) -/
theorem Vphi_edge3 (V : Gelfand.RationalStructure.RepNilQ hcard) (m : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    Vphi hcard V 2 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 m) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (Vphi hcard V 1 m) :=
  (RationalQuiver.Rep.φEdge'_φ' V.obj.toRep Dq.conj
    (f := Gelfand.RationalStructure.edgeQ hcard 3) (e := Gelfand.RationalStructure.edgeQ hcard 1) (Gelfand.RationalStructure.gelfandQ_smul_edge hcard 3)
    (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 2) (a' := Gelfand.RationalStructure.vtxQ hcard 1) (b' := Gelfand.RationalStructure.vtxQ hcard 0)
    rfl rfl rfl rfl (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 1) (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 2) m).symm

/-- `φ_{v,c}` is `c`-semi-linear.  @census none (helper) -/
theorem Vphi_smul (V : Gelfand.RationalStructure.RepNilQ hcard) (v : Fin 3) (a : Dq.carrier) (m : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) v) :
    Vphi hcard V v (a • m) = Dq.conj a • Vphi hcard V v m :=
  RationalQuiver.Rep.φ'_smul _ _ _ _ _

/-- The composite along `a₋b₋` is `n_⋆`.  @census none (helper) -/
theorem pathMap_gelfandPathMinus (V : Gelfand.RationalStructure.RepNilQ hcard) :
    V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 1)
        (Examples.gelfandPathMinus E Dq.carrier hcard) = Split.nOp (Gelfand.RationalStructure.toSplitW hcard V) 1 := by
  have h1 : V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 1) Quiver.Path.nil
      = LinearMap.id := RationalQuiver.Rep.pathMap_nil _ _
  have h2 : V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 0)
      (Quiver.Path.nil.cons RQuiver.bMinus)
      = V.obj.toRep.arrowMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 0) RQuiver.bMinus
        ∘ₗ V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 1) Quiver.Path.nil :=
    RationalQuiver.Rep.pathMap_cons _ _ _
  have h3 : V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 1)
      (Examples.gelfandPathMinus E Dq.carrier hcard)
      = V.obj.toRep.arrowMap (a := Gelfand.RationalStructure.vtxQ hcard 0) (b := Gelfand.RationalStructure.vtxQ hcard 1) RQuiver.aMinus
        ∘ₗ V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 0)
          (Quiver.Path.nil.cons RQuiver.bMinus) := RationalQuiver.Rep.pathMap_cons _ _ _
  have ha : V.obj.toRep.arrowMap (a := Gelfand.RationalStructure.vtxQ hcard 0) (b := Gelfand.RationalStructure.vtxQ hcard 1) RQuiver.aMinus
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 := rfl
  have hb : V.obj.toRep.arrowMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 0) RQuiver.bMinus
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 := rfl
  rw [h3, h2, h1, ha, hb]
  simp only [LinearMap.comp_id]
  rfl

/-- The composite along `a₊b₊` is `φ_{a₊}φ_{b₊}`.  @census none (helper) -/
theorem pathMap_gelfandPathPlus (V : Gelfand.RationalStructure.RepNilQ hcard) :
    V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 1)
        (Examples.gelfandPathPlus E Dq.carrier hcard) = Split.nStarPlus (Gelfand.RationalStructure.toSplitW hcard V) := by
  have h1 : V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 1) Quiver.Path.nil
      = LinearMap.id := RationalQuiver.Rep.pathMap_nil _ _
  have h2 : V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 2)
      (Quiver.Path.nil.cons RQuiver.bPlus)
      = V.obj.toRep.arrowMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 2) RQuiver.bPlus
        ∘ₗ V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 1) Quiver.Path.nil :=
    RationalQuiver.Rep.pathMap_cons _ _ _
  have h3 : V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 1)
      (Examples.gelfandPathPlus E Dq.carrier hcard)
      = V.obj.toRep.arrowMap (a := Gelfand.RationalStructure.vtxQ hcard 2) (b := Gelfand.RationalStructure.vtxQ hcard 1) RQuiver.aPlus
        ∘ₗ V.obj.toRep.pathMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 2)
          (Quiver.Path.nil.cons RQuiver.bPlus) := RationalQuiver.Rep.pathMap_cons _ _ _
  have ha : V.obj.toRep.arrowMap (a := Gelfand.RationalStructure.vtxQ hcard 2) (b := Gelfand.RationalStructure.vtxQ hcard 1) RQuiver.aPlus
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 := rfl
  have hb : V.obj.toRep.arrowMap (a := Gelfand.RationalStructure.vtxQ hcard 1) (b := Gelfand.RationalStructure.vtxQ hcard 2) RQuiver.bPlus
      = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 := rfl
  rw [h3, h2, h1, ha, hb]
  simp only [LinearMap.comp_id]
  rfl

/-- `c`-conjugation carries `n_•` to `n_{c•}`.  @census none (helper) -/
theorem conjBy_nOp (V : Gelfand.RationalStructure.RepNilQ hcard) (v : Fin 3) :
    conjBy Dq.conj (Vphi hcard V v) (Vphi_smul hcard V v) (Split.nOp (Gelfand.RationalStructure.toSplitW hcard V) v)
      = Split.nOp (Gelfand.RationalStructure.toSplitW hcard V) (RQuiver.gelfandVertexSwap v) := by
  fin_cases v
  · ext x
    show Vphi hcard V 0 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 ((Vphi hcard V 0).symm x)))
        = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 x)
    rw [Vphi_edge1, Vphi_edge0]
    simp only [AddEquiv.apply_symm_apply]
  · ext x
    show Vphi hcard V 1 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 ((Vphi hcard V 1).symm x)))
        = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 x)
    rw [Vphi_edge0, Vphi_edge1]
    simp only [AddEquiv.apply_symm_apply]
    exact (LinearMap.congr_fun (Split.nOp_star_eq_nStarPlus (Gelfand.RationalStructure.toSplitW hcard V)) x).symm
  · ext x
    show Vphi hcard V 2 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 ((Vphi hcard V 2).symm x)))
        = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 x)
    rw [Vphi_edge3, Vphi_edge2]
    simp only [AddEquiv.apply_symm_apply]

/-- `c`-conjugation carries `φ_•` to `φ_{c•}`.  @census none (helper) -/
theorem conjBy_phiOp (V : Gelfand.RationalStructure.RepNilQ hcard) (v : Fin 3) :
    conjBy Dq.conj (Vphi hcard V v) (Vphi_smul hcard V v) (Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) v)
      = Split.phiOp ℓ (Gelfand.RationalStructure.toSplitW hcard V) (RQuiver.gelfandVertexSwap v) := by
  have h4 : Dq.conj (4 : Dq.carrier) = (4 : Dq.carrier) := by
    rw [show (4 : Dq.carrier) = ((4 : ℕ) : Dq.carrier) by norm_num, map_natCast]
  have hl : Dq.conj (((ℓ : Dq.carrier) ^ 2)) = ((ℓ : Dq.carrier) ^ 2) := by
    rw [map_pow, map_natCast]
  show conjBy Dq.conj (Vphi hcard V v) (Vphi_smul hcard V v)
      (((ℓ : Dq.carrier) ^ 2) • 1 + (4 : Dq.carrier) • Split.nOp (Gelfand.RationalStructure.toSplitW hcard V) v) = _
  rw [conjBy_add, conjBy_smul, conjBy_smul, conjBy_one, conjBy_nOp, h4, hl]
  rfl

/-- `c`-conjugation carries `φ_•^{1/2}` to `φ_{c•}^{1/2}`: `ℓ` is rational, so the scalar square
root is `c`-fixed.  @census none (helper) -/
theorem conjBy_sqrtPhi (V : Gelfand.RationalStructure.RepNilQ hcard) (v : Fin 3) :
    conjBy Dq.conj (Vphi hcard V v) (Vphi_smul hcard V v) (Split.sqrtPhi hℓ (Gelfand.RationalStructure.toSplitW hcard V) v)
      = Split.sqrtPhi hℓ (Gelfand.RationalStructure.toSplitW hcard V) (RQuiver.gelfandVertexSwap v) := by
  have hγ : Dq.conj (((Split.ellUnit Dq.carrier hℓ : Dq.carrierˣ) : Dq.carrier))
      = ((Split.ellUnit Dq.carrier hℓ : Dq.carrierˣ) : Dq.carrier) := map_natCast Dq.conj ℓ
  rw [Split.sqrtPhi, conjBy_sqrtOfScalarPlusNilpotent _ _ _ _ _ hγ _
    ((4 : Dq.carrier) • Split.nOp (Gelfand.RationalStructure.toSplitW hcard V) v) (Split.phi_scalar_add_nilpotent hℓ (Gelfand.RationalStructure.toSplitW hcard V) v).1
    (Split.phi_scalar_add_nilpotent hℓ (Gelfand.RationalStructure.toSplitW hcard V) v).2, conjBy_phiOp]
  rfl

/-- **`C12`**: `φ_{•,c} ξ^{(j)}_{•,±} φ_{•,c}^{-1} = ξ^{(j)}_{c•,±}` (`eq:semilinearconjugation`).
@census none (helper) -/
theorem conjBy_xiOp (V : Gelfand.RationalStructure.RepNilQ hcard) (v : Fin 3) (s j : ℤ) :
    conjBy Dq.conj (Vphi hcard V v) (Vphi_smul hcard V v) (Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) v s j)
      = Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) (RQuiver.gelfandVertexSwap v) s j := by
  show conjBy Dq.conj (Vphi hcard V v) (Vphi_smul hcard V v)
      (Split.sqrtPhi hℓ (Gelfand.RationalStructure.toSplitW hcard V) v + (((s * j : ℤ) : Dq.carrier)) • 1) = _
  rw [conjBy_add, conjBy_sqrtPhi, conjBy_smul, conjBy_one, map_intCast]
  rfl

end VertexOperators

end EssSurj

section EssSurj

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2) (hℓ : 1 ≤ ℓ)

/-! #### `E3` applied — the three stabilization limits, read on `V(•)`

`stages/S8/DESIGN-NOTES.md` §13.4's engine, discharged: `Gelfand/Stabilization.lean`'s
`stabilizationSeq_addendum_via` (no `hWp`) plus the bridge `toEnd_read`/`asEndConjVia_read` gives
`φ^{(∞)}_± − 𝟏` nilpotent (`C21`) and, for the `(⋆)` run whose `W_+ = W_-` puts it outside S6's
addendum entirely, the sharper `φ^{(∞)}_⋆ = 𝟏` (`C19`) — because there `P₀ = Q₀` is `X⋆ = Y⋆`.
-/

/-- `φ_{v,c}` and `φ_{c·v,c}` are mutually inverse at `+`: the cocycle condition
(`RQ-1.08-C5`) at `σ = c`, `σ⁻¹ = c`.  @census none (helper) -/
theorem Vphi_swap_plus (V : Gelfand.RationalStructure.RepNilQ hcard) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :
    Vphi hcard V 0 (Vphi hcard V 2 x) = x := by
  have hinv : (Dq.conj : Dq.carrier ≃ₐ[E] Dq.carrier)⁻¹ = Dq.conj :=
    inv_eq_of_mul_eq_one_right Gelfand.RationalStructure.galConj_mul_self
  have h' : (Dq.conj : Dq.carrier ≃ₐ[E] Dq.carrier)⁻¹ • Gelfand.RationalStructure.vtxQ hcard 0 = Gelfand.RationalStructure.vtxQ hcard 2 := by
    rw [hinv]; exact Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 0
  exact Eq.trans (V.obj.toRep.φ'_congr hinv h' (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 0) _).symm (V.obj.toRep.φ'_inv Dq.conj (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 2) h' x)

/-- The same at `−`.  @census none (helper) -/
theorem Vphi_swap_minus (V : Gelfand.RationalStructure.RepNilQ hcard) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) :
    Vphi hcard V 2 (Vphi hcard V 0 x) = x := by
  have hinv : (Dq.conj : Dq.carrier ≃ₐ[E] Dq.carrier)⁻¹ = Dq.conj :=
    inv_eq_of_mul_eq_one_right Gelfand.RationalStructure.galConj_mul_self
  have h' : (Dq.conj : Dq.carrier ≃ₐ[E] Dq.carrier)⁻¹ • Gelfand.RationalStructure.vtxQ hcard 2 = Gelfand.RationalStructure.vtxQ hcard 0 := by
    rw [hinv]; exact Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 2
  exact Eq.trans (V.obj.toRep.φ'_congr hinv h' (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 2) _).symm (V.obj.toRep.φ'_inv Dq.conj (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 0) h' x)

/-- `(φ_{+,c})^{-1} = φ_{-,c}`.  @census none (helper) -/
theorem Vphi_symm_plus (V : Gelfand.RationalStructure.RepNilQ hcard) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) :
    (Vphi hcard V 2).symm x = Vphi hcard V 0 x :=
  ((Vphi hcard V 2).symm_apply_eq).2 (Vphi_swap_minus hcard V x).symm

/-- `(φ_{-,c})^{-1} = φ_{+,c}`.  @census none (helper) -/
theorem Vphi_symm_minus (V : Gelfand.RationalStructure.RepNilQ hcard) (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :
    (Vphi hcard V 0).symm x = Vphi hcard V 2 x :=
  ((Vphi hcard V 0).symm_apply_eq).2 (Vphi_swap_plus hcard V x).symm

/-- @census none (helper) -/
theorem conjBy_sub {K L : Type} [Field K] [Field L] [Algebra K L]
    {W₁ W₂ : Type} [AddCommGroup W₁] [Module L W₁] [AddCommGroup W₂] [Module L W₂]
    (σ : L ≃ₐ[K] L) (ψ : W₁ ≃+ W₂) (hψ : ∀ (a : L) (x : W₁), ψ (a • x) = σ a • ψ x)
    (a b : Module.End L W₁) :
    conjBy σ ψ hψ (a - b) = conjBy σ ψ hψ a - conjBy σ ψ hψ b := by
  refine LinearMap.ext fun x => ?_
  simp [conjBy]

/-- `c`-conjugation of endomorphisms, `End(V(+)) → End(V(−))` — `conjBy` with its target type
pinned to `V(−)` (rather than `V(c·+)`), which is what lets `rw` see through it.
@census none (helper) -/
noncomputable def cjPlus (V : Gelfand.RationalStructure.RepNilQ hcard) (A : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2)) :
    Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) :=
  conjBy Dq.conj (Vphi hcard V 2) (Vphi_smul hcard V 2) A

/-- `c`-conjugation of endomorphisms, `End(V(−)) → End(V(+))`.  @census none (helper) -/
noncomputable def cjMinus (V : Gelfand.RationalStructure.RepNilQ hcard) (A : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0)) :
    Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :=
  conjBy Dq.conj (Vphi hcard V 0) (Vphi_smul hcard V 0) A

theorem cjPlus_apply (V : Gelfand.RationalStructure.RepNilQ hcard) (A : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2))
    (y : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) : cjPlus hcard V A y = Vphi hcard V 2 (A (Vphi hcard V 0 y)) := by
  show Vphi hcard V 2 (A ((Vphi hcard V 2).symm y)) = _
  rw [Vphi_symm_plus]

theorem cjMinus_apply (V : Gelfand.RationalStructure.RepNilQ hcard) (A : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0))
    (y : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) : cjMinus hcard V A y = Vphi hcard V 0 (A (Vphi hcard V 2 y)) := by
  show Vphi hcard V 0 (A ((Vphi hcard V 0).symm y)) = _
  rw [Vphi_symm_minus]

theorem cjPlus_pow (V : Gelfand.RationalStructure.RepNilQ hcard) (A : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2)) (n : ℕ) :
    cjPlus hcard V (A ^ n) = (cjPlus hcard V A) ^ n :=
  conjBy_pow Dq.conj (Vphi hcard V 2) (Vphi_smul hcard V 2) A n

theorem cjMinus_pow (V : Gelfand.RationalStructure.RepNilQ hcard) (A : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0)) (n : ℕ) :
    cjMinus hcard V (A ^ n) = (cjMinus hcard V A) ^ n :=
  conjBy_pow Dq.conj (Vphi hcard V 0) (Vphi_smul hcard V 0) A n

theorem cjPlus_one (V : Gelfand.RationalStructure.RepNilQ hcard) : cjPlus hcard V 1 = 1 :=
  conjBy_one Dq.conj (Vphi hcard V 2) (Vphi_smul hcard V 2)

theorem cjMinus_one (V : Gelfand.RationalStructure.RepNilQ hcard) : cjMinus hcard V 1 = 1 :=
  conjBy_one Dq.conj (Vphi hcard V 0) (Vphi_smul hcard V 0)

theorem cjPlus_sub (V : Gelfand.RationalStructure.RepNilQ hcard) (A B : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2)) :
    cjPlus hcard V (A - B) = cjPlus hcard V A - cjPlus hcard V B :=
  conjBy_sub Dq.conj (Vphi hcard V 2) (Vphi_smul hcard V 2) A B

theorem cjMinus_sub (V : Gelfand.RationalStructure.RepNilQ hcard) (A B : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0)) :
    cjMinus hcard V (A - B) = cjMinus hcard V A - cjMinus hcard V B :=
  conjBy_sub Dq.conj (Vphi hcard V 0) (Vphi_smul hcard V 0) A B

theorem cjPlus_isNilpotent (V : Gelfand.RationalStructure.RepNilQ hcard) {A : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2)}
    (h : IsNilpotent A) : IsNilpotent (cjPlus hcard V A) :=
  conjBy_isNilpotent Dq.conj (Vphi hcard V 2) (Vphi_smul hcard V 2) h

theorem cjMinus_isNilpotent (V : Gelfand.RationalStructure.RepNilQ hcard) {A : Module.End Dq.carrier (Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0)}
    (h : IsNilpotent A) : IsNilpotent (cjMinus hcard V A) :=
  conjBy_isNilpotent Dq.conj (Vphi hcard V 0) (Vphi_smul hcard V 0) h


end EssSurj

section EssSurj

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2) (hℓ : 1 ≤ ℓ)

/-! ### Engine `E2`, step 1 — the graded carrier of the essential-surjectivity construction

`essSurj_exists` must produce, from a nilpotent `ℚ`-rational representation `V` of `Γ_ℚ`, a whole
`ℚ`-rational Harish-Chandra module `M = ⨁_n M_n` with `M_n` identified with `V(+)`, `V(⋆)`, `V(−)`
on the displayed ranges.  This section builds the **carrier and its grading** — the design question
that had to be settled before any of the operator formulas can be written — and nothing else.  The
remaining obligations are listed in `stages/S8/DESIGN-NOTES.md` §16.4.

**The design, and why.**  The components have three *different* underlying spaces, so a fibre
family `n ↦ V(region n)` would be a type depending on `n` through a case split, and every
statement about a component would carry a transport (`Eq.rec`) that no `rw` can see through — the
`CONVENTIONS.md` §3 family of hazards, at its worst.  Instead every component is a **submodule of
one fixed ambient space** `T = V(+) × V(⋆) × V(−)` (`EssTriple`): `essRegion ℓ n` is the range of
whichever of the three injections the region calls for, and `⊥` off the parity class.  The fibre
`EssFib` is then a `Submodule` coercion, whose instances are automatic; the carrier is
`⨁_{n ∈ ℤ} EssFib n`, `M_n` is the range of the `n`-th canonical injection, and

* `EssSurjData.centralCharacter` is `essComp_eq_bot` — **free**, because the fibre off the parity
  class is `↥⊥`;
* `WeightData.isInternal` is `essComp_isInternal` — the generic `isInternal_range_lof`;
* `EssSurjData.admissible` is `essComp_finiteDimensional`;
* `EssSurjData.isoPlus`/`isoStar`/`isoMinus` (`C9`) are `essIsoPlus`/`essIsoStar`/`essIsoMinus`,
  each a composite of `LinearEquiv.ofInjective` and one `LinearEquiv.ofEq` on a **submodule**
  equality — never a type equality.

Nothing here consumes `hℓ`, and nothing here is `V`-specific beyond the three vertex spaces, so the
same layer serves `RQ-5.02`'s split case (`E_Qi_equivalence`), where the conjugation half is absent.
-/

section E2Carrier

variable (V : Gelfand.RationalStructure.RepNilQ hcard)

end E2Carrier




section E2Carrier2

variable (V : Gelfand.RationalStructure.RepNilQ hcard)



-- The instance `AddCommGroup ↥(essComp …)` sits four `Submodule`/`DirectSum` layers deep and is
-- not found at the default pending-synthesis depth (measured); `Module` at the same type is.
set_option maxSynthPendingDepth 4

end E2Carrier2

/-! ### Engine `E2`, step 2 — the operators, and the graded `𝔰𝔩₂`-module

Step 1 built the carrier `M = ⨁_n M_n`.  This section puts `H`, `X`, `Y` on it, in the source's
own formulas, and proves the three `𝔰𝔩₂` relations — i.e. it produces the `HC.WeightData` that
`EssSurjData.setup.weight` will be.  What remains for `essSurj_exists` is listed in
`stages/S8/DESIGN-NOTES.md` §16.4 (residue items 4-7): the generalized infinitesimal character,
finite generation, the conjugation, the `ℚ`-form, and the fifteen pins.

**How the operators are written.**  Each of `X` and `Y` is defined *in the ambient* `T` first
(`xAmb`, `yAmb`), by a `Prop`-valued case split on the degree, and only then restricted to the
components (`xComp`, `yComp`, via `LinearMap.restrict` and `xAmb_mem`/`yAmb_mem`).  Writing the
case split in `T` rather than in the fibres is what keeps it free of type transports: `T` does not
depend on `n`, so a five-way `if` on `n` is an ordinary definition and the membership statement is
an ordinary `Prop`.  `X`, `Y` and `H` on `M` are then `DirectSum.toModule` of those.

**The case split, and its fall-through.**  `xAmb n` has five branches — the `+` interior
(`n ≥ ℓ+1`), the `−` interior (`n ≤ -(ℓ+3)`), the `a₋` wall (`n = -(ℓ+1)`), the `b₊` wall
(`n = ℓ-1`), the `⋆` interior (`-(ℓ-1) ≤ n ≤ ℓ-3`) — and a fall-through `0`.  The fall-through is
reached exactly at `n ∈ {ℓ, ℓ-2, -ℓ, -(ℓ+2)}`, each of which differs from `ℓ-1` by an odd number,
so the source component there is `⊥` and `0` is the only possible map; that is the one step of the
case analysis which has to be *argued* rather than read off, and it is `xAmb_mem`'s parity branch.

**`[X,Y] = H`.**  `essLie_ambient` is the computation, in eight cases.  The three interiors are
`C11` (`xi_mul_xi`, in both orders): `4XY = φ_• − (n−1)²` and `4YX = φ_• − (n+1)²` on `M_n`, whose
difference is `4n`.  At each of the four walls one of the two composites is a pair of edge maps —
`φ_{b₊}φ_{a₊} = n_+`, `φ_{b₋}φ_{a₋} = n_-`, `φ_{a₋}φ_{b₋} = n_⋆`, `φ_{a₊}φ_{b₊}` — and the loop
cancels against the `4n_•` inside `φ_• = ℓ²·𝟏 + 4n_•`, leaving `¼(j² − ℓ²)`.  **The eighth case is
`ℓ = 1`**, where the `⋆` block is the single component `M_0`, both walls meet it, and the identity
reduces to `n_⋆ = φ_{a₊}φ_{b₊}` — that is `C10`, i.e. **`ex:gelfand`'s relation**.  The relation is
therefore not decoration in this construction: it is the `𝔰𝔩₂` identity at the `⋆` vertex.
-/

section E2Ops

variable (V : Gelfand.RationalStructure.RepNilQ hcard)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

/-! #### The five branches of `xAmb`, evaluated (all `@census none (helper; engine E2)`) -/

/-! #### The five branches of `yAmb`, evaluated (all `@census none (helper; engine E2)`) -/

/-! #### The `[X,Y] = H` computation, in the ambient space (all `@census none (helper; engine E2)`) -/

end E2Ops

/-! ### Engine `E2`, step 3 — the generalized infinitesimal character

The last piece of the `ℚ[√-1]`-side of the construction: `M` has `λ = ℓ²`.  The argument is the
source's, and it is short once the operators are in place: on `M_n`, `4XY = C − (n−1)²`
(`WeightData.four_X_Y_apply`) and, by `essXY_ambient`, `XY = n_• + ¼(ℓ² − (n−1)²)`; the `(n−1)²`
cancels and `C = ℓ²·𝟏 + 4n_•` on every component.  So `C − ℓ²·𝟏` is `4n_•`, which is nilpotent
because `V` is (`phi_scalar_add_nilpotent`, the fact that replaced `HYP-07` under `R-S8-7`), and a
single exponent — the max over the three vertices — kills every summand at once.

**The uniformity is the point.**  `essXY_ambient` proves the SAME formula at the four walls as in
the three interiors: at a wall one of `X`, `Y` is an edge map and the composite is the quiver loop
`n_•` itself, while `¼(ℓ² − (n−1)²)` vanishes there because `(n−1)² = ℓ²` at every wall.  Without
that coincidence the Casimir would have to be computed region by region.

With `essQiSetup` the `ℚ[√-1]`-side of `essSurj_exists` is complete: what remains is the
conjugation and the `ℚ`-form (`DESIGN-NOTES.md` §16.4, residue items 5-7), and `essQiSetup` is
already the whole of what `RQ-5.02`'s split-case essential surjectivity needs from this layer.
-/

section E2GIC

variable (V : Gelfand.RationalStructure.RepNilQ hcard)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

end E2GIC

/-! ### Engine `E2`, step 4 — finite generation

Residue item 5 of `stages/S8/DESIGN-NOTES.md` §16.4.  On the `+` region
`2X|_{M_n} = ξ^{(n+1)}_{+,+} = φ_+^{1/2} + (n+1) = (ℓ + n + 1)·𝟏 + nilpotent`, and `ℓ + n + 1 > 0`
for `n ≥ ℓ+1`, so `X : M_n → M_{n+2}` is **onto** there; symmetrically
`2Y|_{M_n} = φ_-^{1/2} − (n−1) = (ℓ − n + 1)·𝟏 + nilpotent` is invertible for `n ≤ -(ℓ+1)`, so
`Y : M_n → M_{n-2}` is onto on the `−` region.  Hence the finitely many components in the window
`-(ℓ+1) ≤ n ≤ ℓ+1` — each finite-dimensional by `essComp_finiteDimensional` — generate `M` under
the triple, and a finite spanning set of their (finite-dimensional) sum is a finite generating set.

Only the `X`/`Y` half of `WeightData.OpStable` is used: **`IsHomog` is never needed**, because the
generating window is a union of *whole* components rather than a set of inhomogeneous vectors.
-/

section E2FG

variable (V : Gelfand.RationalStructure.RepNilQ hcard)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

end E2FG

/-! ### Engine `E2`, step 5 — the conjugation `c`, on the ambient `T` and on `M`

Residue item 6 of `stages/S8/DESIGN-NOTES.md` §16.4, first half.  On the ambient
`T = V(+) × V(⋆) × V(−)` the conjugation is `V`'s own rational structure read across the
`±`-swap: `c(x₊,x⋆,x₋) = (φ_{-,c}x₋, φ_{⋆,c}x⋆, φ_{+,c}x₊)`.  It is `Dq.conj`-semilinear
(`Vphi_smul`), an involution (the cocycle condition `RQ-1.08-C5`, i.e. `Vphi_swap_*`), it carries
`M_n` to `M_{-n}` because it exchanges the `+` and `−` ranges and fixes the `⋆` one, and it
intertwines `X` with `Y` because `C12` (`conjBy_xiOp`) says so in the three interiors and
`RQ-1.08-C9` (`Vphi_edge0`, `Vphi_edge3`) says so at the two walls.

Which walls appear is worth recording: `c` sends the `a₋` wall of `X` (at `n = -(ℓ+1)`) to the
`a₊` wall of `Y` (at `n = ℓ+1`), and the `b₊` wall of `X` (at `n = ℓ-1`) to the `b₋` wall of `Y`
(at `n = -(ℓ-1)`).  That is why `xAmb` and `yAmb` carry *different* wall pairs, and
`essConjAmb_xAmb` is the only place in the engine where the two definitions are compared.
-/

section E2Conj

variable (V : Gelfand.RationalStructure.RepNilQ hcard)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

/-- `φ_{⋆,c}` is an involution: the `⋆` vertex is `Gal`-fixed, so the cocycle condition there is
`φ_{⋆,c}² = 𝟏`.  @census none (helper; engine `E2`) -/
theorem Vphi_swap_star (x : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) : Vphi hcard V 1 (Vphi hcard V 1 x) = x := by
  have hinv : (Dq.conj : Dq.carrier ≃ₐ[E] Dq.carrier)⁻¹ = Dq.conj :=
    inv_eq_of_mul_eq_one_right Gelfand.RationalStructure.galConj_mul_self
  have h' : (Dq.conj : Dq.carrier ≃ₐ[E] Dq.carrier)⁻¹ • Gelfand.RationalStructure.vtxQ hcard 1 = Gelfand.RationalStructure.vtxQ hcard 1 := by
    rw [hinv]; exact Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 1
  exact Eq.trans (V.obj.toRep.φ'_congr hinv h' (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 1) _).symm (V.obj.toRep.φ'_inv Dq.conj (Gelfand.RationalStructure.gelfandQ_smul_vertex hcard 1) h' x)

/-- `c` fixes `2⁻¹` (indeed every rational).  @census none (helper; engine `E2`) -/
theorem galConj_two_inv : Dq.conj ((2 : Dq.carrier)⁻¹) = ((2 : Dq.carrier)⁻¹) := by
  rw [map_inv₀, map_ofNat]

/-- `ξ^{(j)}_{v,s}` depends on `(s,j)` only through the product `s·j`.
@census none (helper; engine `E2`) -/
theorem xiOp_congr (v : Fin 3) {s j s' j' : ℤ} (h : s * j = s' * j') :
    Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) v s j = Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) v s' j' := by
  rw [Split.xiOp, Split.xiOp, h]

/-- **`C12`, applied**: `φ_{v,c}(ξ^{(j)}_{v,s} a) = ξ^{(j)}_{c·v,s}(φ_{v,c} a)`.
@census none (helper; engine `E2`) -/
theorem Vphi_xiOp (v : Fin 3) (s j : ℤ) (a : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) v) :
    Vphi hcard V v (Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) v s j a)
      = Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) (RQuiver.gelfandVertexSwap v) s j (Vphi hcard V v a) := by
  have h := LinearMap.congr_fun (conjBy_xiOp hcard hℓ V v s j) (Vphi hcard V v a)
  rw [conjBy_apply, AddEquiv.symm_apply_apply] at h
  exact h

/-- The combination the three interior branches of `essConjAmb_xAmb` need.
@census none (helper; engine `E2`) -/
theorem Vphi_half_xiOp (v : Fin 3) (s j s' j' : ℤ) (h : s * j = s' * j') (a : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) v) :
    Vphi hcard V v (((2 : Dq.carrier)⁻¹) • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) v s j a)
      = ((2 : Dq.carrier)⁻¹)
          • Split.xiOp hℓ (Gelfand.RationalStructure.toSplitW hcard V) (RQuiver.gelfandVertexSwap v) s' j' (Vphi hcard V v a) := by
  rw [Vphi_smul, galConj_two_inv, Vphi_xiOp,
    xiOp_congr hcard hℓ V (RQuiver.gelfandVertexSwap v) h]

/-- `c` on the ambient `T`, as a function.  @census none (helper; engine `E2`) -/
noncomputable def essConjT (x : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V) :=
  (Vphi hcard V 0 x.2.2, Vphi hcard V 1 x.2.1, Vphi hcard V 2 x.1)

/-- @census none (helper; engine `E2`) -/
theorem essConjT_involutive : Function.Involutive (essConjT hcard V) := by
  rintro ⟨x1, x2, x3⟩
  show ((Vphi hcard V 0 (Vphi hcard V 2 x1), Vphi hcard V 1 (Vphi hcard V 1 x2),
      Vphi hcard V 2 (Vphi hcard V 0 x3)) : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) = _
  rw [Vphi_swap_plus, Vphi_swap_star, Vphi_swap_minus]

/-- **`c` on the ambient `T`**.  @census none (helper; engine `E2`) -/
noncomputable def essConjAmb : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V) ≃+ Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V) where
  toFun := essConjT hcard V
  invFun := essConjT hcard V
  left_inv := essConjT_involutive hcard V
  right_inv := essConjT_involutive hcard V
  map_add' x y := by
    obtain ⟨x1, x2, x3⟩ := x
    obtain ⟨y1, y2, y3⟩ := y
    show ((Vphi hcard V 0 (x3 + y3), Vphi hcard V 1 (x2 + y2), Vphi hcard V 2 (x1 + y1))
        : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) = _
    rw [map_add, map_add, map_add]
    rfl

theorem essConjAmb_apply (x : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) :
    essConjAmb hcard V x = essConjT hcard V x := rfl

/-- @census none (helper; engine `E2`) -/
theorem essConjAmb_involutive (x : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) :
    essConjAmb hcard V (essConjAmb hcard V x) = x := essConjT_involutive hcard V x

/-- `c` is `Dq.conj`-semilinear.  @census none (helper; engine `E2`) -/
theorem essConjAmb_smul (a : Dq.carrier) (x : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) :
    essConjAmb hcard V (a • x) = Dq.conj a • essConjAmb hcard V x := by
  obtain ⟨x1, x2, x3⟩ := x
  show ((Vphi hcard V 0 (a • x3), Vphi hcard V 1 (a • x2), Vphi hcard V 2 (a • x1))
      : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) = _
  rw [Vphi_smul, Vphi_smul, Vphi_smul]
  rfl

/-- @census none (helper; engine `E2`) -/
theorem essConjAmb_iotaPlus (a : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 2) :
    essConjAmb hcard V (Split.essIotaPlus (Gelfand.RationalStructure.toSplitW hcard V) a) = Split.essIotaMinus (Gelfand.RationalStructure.toSplitW hcard V) (Vphi hcard V 2 a) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact map_zero (Vphi hcard V 0)
  · exact map_zero (Vphi hcard V 1)
  · rfl

/-- @census none (helper; engine `E2`) -/
theorem essConjAmb_iotaMinus (a : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 0) :
    essConjAmb hcard V (Split.essIotaMinus (Gelfand.RationalStructure.toSplitW hcard V) a) = Split.essIotaPlus (Gelfand.RationalStructure.toSplitW hcard V) (Vphi hcard V 0 a) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · rfl
  · exact map_zero (Vphi hcard V 1)
  · exact map_zero (Vphi hcard V 2)

/-- @census none (helper; engine `E2`) -/
theorem essConjAmb_iotaStar (a : Split.VM (Gelfand.RationalStructure.toSplitW hcard V) 1) :
    essConjAmb hcard V (Split.essIotaStar (Gelfand.RationalStructure.toSplitW hcard V) a) = Split.essIotaStar (Gelfand.RationalStructure.toSplitW hcard V) (Vphi hcard V 1 a) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact map_zero (Vphi hcard V 0)
  · rfl
  · exact map_zero (Vphi hcard V 2)

/-- **`c : M_n → M_{-n}`**, in the ambient.  @census none (helper; engine `E2`) -/
theorem essConjAmb_mem (ℓ : ℕ) (n : ℤ) (x : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) (hx : x ∈ Split.essRegion (Gelfand.RationalStructure.toSplitW hcard V) ℓ n) :
    essConjAmb hcard V x ∈ Split.essRegion (Gelfand.RationalStructure.toSplitW hcard V) ℓ (-n) := by
  by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · have hpar2 : (-n - ((ℓ : ℤ) - 1)) % 2 = 0 := by omega
    by_cases h1 : (ℓ : ℤ) + 1 ≤ n
    · rw [Split.essRegion_plus (Gelfand.RationalStructure.toSplitW hcard V) hpar h1] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [essConjAmb_iotaPlus, Split.essRegion_minus (Gelfand.RationalStructure.toSplitW hcard V) hpar2 (by omega)]
      exact ⟨_, rfl⟩
    · by_cases h2 : n ≤ -((ℓ : ℤ) + 1)
      · rw [Split.essRegion_minus (Gelfand.RationalStructure.toSplitW hcard V) hpar h2] at hx
        obtain ⟨a, rfl⟩ := hx
        rw [essConjAmb_iotaMinus, Split.essRegion_plus (Gelfand.RationalStructure.toSplitW hcard V) hpar2 (by omega)]
        exact ⟨_, rfl⟩
      · rw [Split.essRegion_star (Gelfand.RationalStructure.toSplitW hcard V) hpar (by omega) (by omega)] at hx
        obtain ⟨a, rfl⟩ := hx
        rw [essConjAmb_iotaStar, Split.essRegion_star (Gelfand.RationalStructure.toSplitW hcard V) hpar2 (by omega) (by omega)]
        exact ⟨_, rfl⟩
  · rw [Split.essRegion_bot_apply (Gelfand.RationalStructure.toSplitW hcard V) hpar hx, map_zero]
    exact Submodule.zero_mem _

set_option maxHeartbeats 1000000 in
/-- **`cX = Yc` in the ambient** — `eq:Xconjugation`/`eq:Yconjugation` for the constructed module.
@census none (helper; engine `E2`) -/
theorem essConjAmb_xAmb (n : ℤ) (x : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) (hx : x ∈ Split.essRegion (Gelfand.RationalStructure.toSplitW hcard V) ℓ n) :
    essConjAmb hcard V (Split.xAmb hℓ (Gelfand.RationalStructure.toSplitW hcard V) n x)
      = Split.yAmb hℓ (Gelfand.RationalStructure.toSplitW hcard V) (-n) (essConjAmb hcard V x) := by
  by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · by_cases h1 : (ℓ : ℤ) + 1 ≤ n
    · rw [Split.essRegion_plus (Gelfand.RationalStructure.toSplitW hcard V) hpar h1] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [Split.xAmb_plus hℓ (Gelfand.RationalStructure.toSplitW hcard V) h1, essConjAmb_iotaPlus, essConjAmb_iotaPlus,
        Split.yAmb_minus hℓ (Gelfand.RationalStructure.toSplitW hcard V) (by omega) (by omega)]
      exact congrArg (Split.essIotaMinus (Gelfand.RationalStructure.toSplitW hcard V))
        (Vphi_half_xiOp hcard hℓ V 2 1 (n + 1) (-1) (-n - 1) (by ring) a)
    · by_cases h2 : n ≤ -((ℓ : ℤ) + 3)
      · rw [Split.essRegion_minus (Gelfand.RationalStructure.toSplitW hcard V) hpar (by omega)] at hx
        obtain ⟨a, rfl⟩ := hx
        rw [Split.xAmb_minus hℓ (Gelfand.RationalStructure.toSplitW hcard V) h1 h2, essConjAmb_iotaMinus, essConjAmb_iotaMinus,
          Split.yAmb_plus hℓ (Gelfand.RationalStructure.toSplitW hcard V) (by omega)]
        exact congrArg (Split.essIotaPlus (Gelfand.RationalStructure.toSplitW hcard V))
          (Vphi_half_xiOp hcard hℓ V 0 1 (n + 1) (-1) (-n - 1) (by ring) a)
      · by_cases h3 : n = -((ℓ : ℤ) + 1)
        · rw [Split.essRegion_minus (Gelfand.RationalStructure.toSplitW hcard V) hpar (by omega)] at hx
          obtain ⟨a, rfl⟩ := hx
          rw [Split.xAmb_wallAm hℓ (Gelfand.RationalStructure.toSplitW hcard V) h1 h2 h3, essConjAmb_iotaStar, essConjAmb_iotaMinus,
            Split.yAmb_wallAp hℓ (Gelfand.RationalStructure.toSplitW hcard V) (by omega) (by omega) (by omega)]
          refine congrArg (Split.essIotaStar (Gelfand.RationalStructure.toSplitW hcard V)) ?_
          show Vphi hcard V 1 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 0 a) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 2 (Vphi hcard V 0 a)
          exact Vphi_edge0 hcard V a
        · by_cases h4 : n = (ℓ : ℤ) - 1
          · rw [Split.essRegion_star (Gelfand.RationalStructure.toSplitW hcard V) hpar (by omega) (by omega)] at hx
            obtain ⟨a, rfl⟩ := hx
            rw [Split.xAmb_wallBp hℓ (Gelfand.RationalStructure.toSplitW hcard V) h1 h2 h3 h4, essConjAmb_iotaPlus, essConjAmb_iotaStar,
              Split.yAmb_wallBm hℓ (Gelfand.RationalStructure.toSplitW hcard V) (by omega) (by omega) (by omega) (by omega)]
            refine congrArg (Split.essIotaMinus (Gelfand.RationalStructure.toSplitW hcard V)) ?_
            show Vphi hcard V 2 (Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 3 a) = Split.Vedge (Gelfand.RationalStructure.toSplitW hcard V) 1 (Vphi hcard V 1 a)
            exact Vphi_edge3 hcard V a
          · rw [Split.essRegion_star (Gelfand.RationalStructure.toSplitW hcard V) hpar (by omega) (by omega)] at hx
            obtain ⟨a, rfl⟩ := hx
            rw [Split.xAmb_star hℓ (Gelfand.RationalStructure.toSplitW hcard V) h1 h2 h3 h4 ⟨by omega, by omega⟩, essConjAmb_iotaStar,
              essConjAmb_iotaStar,
              Split.yAmb_star hℓ (Gelfand.RationalStructure.toSplitW hcard V) (by omega) (by omega) (by omega) (by omega)
                ⟨by omega, by omega⟩]
            exact congrArg (Split.essIotaStar (Gelfand.RationalStructure.toSplitW hcard V))
              (Vphi_half_xiOp hcard hℓ V 1 1 (n + 1) (-1) (-n - 1) (by ring) a)
  · rw [Split.essRegion_bot_apply (Gelfand.RationalStructure.toSplitW hcard V) hpar hx]
    simp only [map_zero]

/-! #### `c` on the graded carrier -/

/-- @census none (helper; engine `E2`) -/
theorem essOf_congr (ℓ : ℕ) {i j : ℤ} (h : i = j) (a : Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ i)
    (b : Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ j) (hab : (a : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) = (b : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V))) :
    DirectSum.of (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) i a = DirectSum.of (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) j b := by
  subst h; exact congrArg _ (Subtype.ext hab)

/-- `c` on the fibre at `n`, landing at `-n`.  @census none (helper; engine `E2`) -/
noncomputable def essConjFib (ℓ : ℕ) (n : ℤ) : Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ n →+ Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ (-n) where
  toFun a := ⟨essConjAmb hcard V (a : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)), essConjAmb_mem hcard V ℓ n _ a.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ _ _)

@[simp] theorem essConjFib_coe (ℓ : ℕ) (n : ℤ) (a : Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ n) :
    ((essConjFib hcard V ℓ n a : Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ (-n)) : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V))
      = essConjAmb hcard V (a : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) := rfl

/-- `c` on `M = ⨁_n M_n`, additively.  @census none (helper; engine `E2`) -/
noncomputable def essConjMap (ℓ : ℕ) : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ →+ Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ :=
  DirectSum.toAddMonoid (fun n =>
    (DirectSum.of (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) (-n)).comp (essConjFib hcard V ℓ n))

@[simp] theorem essConjMap_of (ℓ : ℕ) (n : ℤ) (a : Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ n) :
    essConjMap hcard V ℓ (DirectSum.of (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) n a)
      = DirectSum.of (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) (-n) (essConjFib hcard V ℓ n a) :=
  DirectSum.toAddMonoid_of _ _ _

/-- @census none (helper; engine `E2`) -/
theorem essConjMap_involutive (ℓ : ℕ) : Function.Involutive (essConjMap hcard V ℓ) := by
  intro x
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n a =>
      rw [essConjMap_of, essConjMap_of]
      refine essOf_congr hcard V ℓ (neg_neg n) _ _ ?_
      exact essConjAmb_involutive hcard V (a : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V))
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- **The conjugation of the constructed module**.  @census none (helper; engine `E2`)
@clauses   RQ2-5.12-S-O19 -/
noncomputable def essConj (ℓ : ℕ) : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ ≃+ Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ where
  toFun := essConjMap hcard V ℓ
  invFun := essConjMap hcard V ℓ
  left_inv := essConjMap_involutive hcard V ℓ
  right_inv := essConjMap_involutive hcard V ℓ
  map_add' := map_add _

@[simp] theorem essConj_apply (ℓ : ℕ) (x : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) :
    essConj hcard V ℓ x = essConjMap hcard V ℓ x := rfl

/-- @census none (helper; engine `E2`) -/
theorem essConj_involutive (ℓ : ℕ) : Function.Involutive (essConj hcard V ℓ) :=
  essConjMap_involutive hcard V ℓ

theorem essConj_lof (ℓ : ℕ) (n : ℤ) (a : Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ n) :
    essConj hcard V ℓ (DirectSum.lof Dq.carrier ℤ (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) n a)
      = DirectSum.lof Dq.carrier ℤ (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) (-n) (essConjFib hcard V ℓ n a) := by
  rw [DirectSum.lof_eq_of, DirectSum.lof_eq_of]
  exact essConjMap_of hcard V ℓ n a

/-- `c` is `Dq.conj`-semilinear on `M`.  @census none (helper; engine `E2`) -/
theorem essConj_smul (ℓ : ℕ) (a : Dq.carrier) (v : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) :
    essConj hcard V ℓ (a • v) = Dq.conj a • essConj hcard V ℓ v := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of n b =>
      rw [← DirectSum.lof_eq_of (R := Dq.carrier)]
      have hL : a • DirectSum.lof Dq.carrier ℤ (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) n b
          = DirectSum.lof Dq.carrier ℤ (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) n (a • b) :=
        (map_smul _ a b).symm
      have hR : Dq.conj a • DirectSum.lof Dq.carrier ℤ (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) (-n)
            (essConjFib hcard V ℓ n b)
          = DirectSum.lof Dq.carrier ℤ (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) (-n)
            (Dq.conj a • essConjFib hcard V ℓ n b) :=
        (map_smul _ (Dq.conj a) _).symm
      rw [hL, essConj_lof, essConj_lof, hR]
      refine congrArg _ (Subtype.ext ?_)
      exact essConjAmb_smul hcard V a (b : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V))
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

/-- **`c : M_n → M_{-n}`**.  @census none (helper; engine `E2`) -/
theorem essConj_comp (ℓ : ℕ) (n : ℤ) (v : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) (hv : v ∈ Split.essComp (Gelfand.RationalStructure.toSplitW hcard V) ℓ n) :
    essConj hcard V ℓ v ∈ Split.essComp (Gelfand.RationalStructure.toSplitW hcard V) ℓ (-n) := by
  obtain ⟨a, rfl⟩ := hv
  rw [essConj_lof]
  exact ⟨_, rfl⟩

/-- **`cX = Yc`** (`RationalSetup.conj_X`).  @census none (helper; engine `E2`) -/
theorem essConj_X (v : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) :
    essConj hcard V ℓ (Split.essX hℓ (Gelfand.RationalStructure.toSplitW hcard V) v) = Split.essY hℓ (Gelfand.RationalStructure.toSplitW hcard V) (essConj hcard V ℓ v) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of n a =>
      rw [← DirectSum.lof_eq_of (R := Dq.carrier), Split.essX_lof, essConj_lof, essConj_lof, Split.essY_lof]
      refine Split.essLof_congr (Gelfand.RationalStructure.toSplitW hcard V) (by ring) _ _ ?_
      exact essConjAmb_xAmb hcard hℓ V n (a : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) a.2
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- **`cY = Xc`** (`RationalSetup.conj_Y`), from `essConj_X` and `c² = 𝟏`.
@census none (helper; engine `E2`) -/
theorem essConj_Y (v : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) :
    essConj hcard V ℓ (Split.essY hℓ (Gelfand.RationalStructure.toSplitW hcard V) v) = Split.essX hℓ (Gelfand.RationalStructure.toSplitW hcard V) (essConj hcard V ℓ v) := by
  have h := essConj_X hcard hℓ V (essConj hcard V ℓ v)
  rw [essConj_involutive hcard V ℓ v] at h
  calc essConj hcard V ℓ (Split.essY hℓ (Gelfand.RationalStructure.toSplitW hcard V) v)
      = essConj hcard V ℓ (essConj hcard V ℓ (Split.essX hℓ (Gelfand.RationalStructure.toSplitW hcard V) (essConj hcard V ℓ v))) := by
        rw [h]
    _ = Split.essX hℓ (Gelfand.RationalStructure.toSplitW hcard V) (essConj hcard V ℓ v) := essConj_involutive hcard V ℓ _

/-- **`cH = -Hc`** (`RationalSetup.conj_H`).  @census none (helper; engine `E2`) -/
theorem essConj_H (ℓ : ℕ) (v : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) :
    essConj hcard V ℓ (Split.essH (Gelfand.RationalStructure.toSplitW hcard V) v) = -Split.essH (Gelfand.RationalStructure.toSplitW hcard V) (essConj hcard V ℓ v) := by
  induction v using DirectSum.induction_on with
  | zero => simp
  | of n a =>
      rw [← DirectSum.lof_eq_of (R := Dq.carrier), Split.essH_lof, essConj_smul, essConj_lof,
        Split.essH_lof, map_intCast, ← neg_smul]
      congr 1
      push_cast
      ring
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy, neg_add]

end E2Conj

end EssSurj

end RationalQuivers.Gelfand.EssSurj
