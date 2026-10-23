import RationalQuivers.Gelfand.RationalStructure.Conjugate
import RationalQuivers.Unipotent.Addendum

/-!
# unipotent stabilization for `L_E/E`, `τ = c` (§5.2, Steps O-9 … O-11)

`prop:unipotentstabilization` applied simultaneously in the situations `(+)`, `(−)`, `(⋆)`
(`StabInput`, `inputPlus`/`inputMinus`/`inputStar`, `stab_prereq`), the first iteration
(`first_iteration`, `eq:firstiteration`), the limits and `eq:conjugateinversepm/star` (`varphi_spec`,
claimant of `RQ2-5.04`), the limit diagram `eq:limitdiagram` and naturality (`lim_natural`).

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Stabilization.lean` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.RationalStructure.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

*(2026-10-21, O-V2-6 round 2.)*  Carried docstrings and `@divergence` fields
below name, in the present tense, the following v1 declarations and file:
* S7's `HC.RationalSetup`, `HC.Tplus_isUnit` and `HC.xstar_ystar_relations`;
* S8's `Gelfand.HCQObj`;
* v1's `Gelfand/Cyclic.lean`.
All of them were deleted at WP-13 (`9c6b193`, `ae9eda9`).  The v2 forms are
`HC.WeightData.Tplus_isUnit` and `HC.WeightData.xStar_yStar_relations` (see *v2 change* above),
`HCEObj` over `RationalSetupOver`, and `Gelfand.Cyclic.tMinus_zero` in
`Gelfand/Cyclic/Rational.lean`.

*v2 change.*  `GF/Normalization.lean` is not relocated: `cor:X_Y_inverses`, `cor:T_operators` and the
`X⋆`/`Y⋆` relations are read from T1's `HC.WeightData.isUnit_pow_X`, `Tplus_isUnit`,
`xStar_yStar_relations` (`stab_prereq`, `conjStar_limit`), as the T1 handover asked.

@census none (module)
-/

namespace RationalQuivers.Gelfand.RationalStructure

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {D : SqrtNegOneExt E}
open scoped TensorProduct

variable {ℓ : ℕ} {Mq : Type} [AddCommGroup Mq] [Module E Mq]
variable {Mi : Type} [AddCommGroup Mi] [Module D.carrier Mi]


/-! ### The three cases, in `StabCase` shape (`RQ-5.04-C1`)

`casePlus` and `caseMinus` are the source's itemized `(+)` and `(−)` data.  `caseStar` is the
`c`-conjugate description `(M_{ℓ-1}, Y⋆)` of the `(⋆)` datum; the datum the source itemizes since
2026-09-11 is `inputStar`, and `case_eq_input` identifies the two (source note (1)). -/

/-- One of §5.2's three stabilization data, in the shape the source's `(+)`/`(−)` items have: two
weight components `W_±` named by their indices and two maps `φ_±`.  The `(⋆)` datum the source
itemizes since 2026-09-11 has `W₊ = W₋` and `φ₊ = φ₋` — a `StabInput`, not a `StabCase`, since
`φ_±` there goes `W_± → W_∓^c` — and `caseStar` carries its `c`-conjugate description instead
(source note (1)).

@census none (auxiliary; carries census clause `RQ-5.04-C1`) -/
structure StabCase (S : RationalSetupOver ℓ E D Mq Mi) where
  /-- `W₊`, a weight component of `M_{ℚ[√-1]}`, named by its index. -/
  idxPlus : ℤ
  /-- `W₋`. -/
  idxMinus : ℤ
  /-- `φ₊`, typed `W₊ → W₋` in the `(+)`/`(−)` items.  (In the `(⋆)` datum the source itemizes
  since 2026-09-11 the typing is `W₊ → W₋^c`; that datum is `inputStar`.) -/
  phiPlus : Module.End D.carrier Mi
  /-- `φ₋`, typed `W₋ → W₊` in the `(+)`/`(−)` items; see `phiPlus` for the `(⋆)` datum. -/
  phiMinus : Module.End D.carrier Mi

/-- **`RQ-5.04-C1`** — the three stabilization data of the source's itemized list:
`(+)` `W₊ = M_{ℓ+1}`, `W₋ = M_{-(ℓ+1)}`, `φ₊ = 𝟏_{M_{ℓ+1}}`, `φ₋ = T₋`;
`(−)` `W₊ = M_{-(ℓ+1)}`, `W₋ = M_{ℓ+1}`, `φ₊ = T₋`, `φ₋ = 𝟏_{M_{ℓ+1}}`;
`(⋆)` `W₊ = W₋ = M_{-(ℓ-1)}`, `φ₊ = φ₋ = X⋆`, with `W₋^c = M_{ℓ-1}` and `φ₋^c = Y⋆`, so that the
pair `(M_{ℓ-1}, Y⋆)` is the `c`-conjugate description of that same instantiation and not a second
one.

The `(⋆)` line is the item **as the source has printed it since the author's ruling of 2026-09-11**
(`AN-38`; until then it printed `W₊ = M_{-(ℓ-1)}`, `W₋ = M_{ℓ-1}`, `φ₊ = X⋆`, `φ₋ = Y⋆`, which
**did not** type-check — ruled and applied 2026-09-11, module docstring, note (1); re-tensed
2026-09-12, the amendment's close-out round, to agree with that note).  `inputStar` renders the amended item;
`caseStar` below renders its `c`-conjugate description, and `case_eq_input` identifies the two.

@census none (auxiliary; discharges census clause `RQ-5.04-C1`)
@source    eq:varphiplus
@clauses   RQ2-5.04-C1
@imports   none
@divergence none -/
noncomputable def casePlus (S : RationalSetupOver ℓ E D Mq Mi) : StabCase S :=
  ⟨(ℓ : ℤ) + 1, -((ℓ : ℤ) + 1), 1, Split.tMinus S.toQiSetup⟩

/-- The `(−)` case; see `casePlus`.  @census none (auxiliary; discharges `RQ-5.04-C1`) -/
noncomputable def caseMinus (S : RationalSetupOver ℓ E D Mq Mi) : StabCase S :=
  ⟨-((ℓ : ℤ) + 1), (ℓ : ℤ) + 1, Split.tMinus S.toQiSetup, 1⟩

/-- The `(⋆)` case in its **`c`-conjugate description** `(M_{ℓ-1}, Y⋆)` — which the amended source
names as such, and which it printed as the primary datum until 2026-09-11; see `casePlus` and the
module docstring's source note (1).  @census none (auxiliary; discharges `RQ-5.04-C1`) -/
noncomputable def caseStar (S : RationalSetupOver ℓ E D Mq Mi) : StabCase S :=
  ⟨-((ℓ : ℤ) - 1), (ℓ : ℤ) - 1, Split.xStar S.toQiSetup, Split.yStar S.toQiSetup⟩

/-- **`RQ-5.04-C3`** — the Galois symmetry that makes the three stabilizations *simultaneous*:
`T₋^c = T₊` and `X⋆^c = Y⋆`.  The census's own `notes` cell reads "the Galois symmetry driving the
simultaneous stabilization".  Both are the `RQ-5.03-C1` conjugations, restated here at the point
`RQ-5.04` consumes them.

@census    none (auxiliary; discharges census clause `RQ-5.04-C3`)
@source    eq:varphiplus
@clauses   RQ2-5.04-C3,
           RQ2-5.24-S-TW2
@imports   none
@divergence none -/
theorem conj_symmetry (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ) :
    (∀ v : Mi, S.conj (Split.tMinus S.toQiSetup (S.conj v)) = Split.tPlus S.toQiSetup v) ∧
    (∀ v : Mi, S.conj (Split.xStar S.toQiSetup (S.conj v)) = Split.yStar S.toQiSetup v) := by
  obtain ⟨-, -, hxy, hT⟩ := conj_normalized_operators S hℓ
  exact ⟨hT, hxy⟩

/-! ### The transport to S6's setting

`prop:unipotentstabilization` and its corollary (S6) are stated on `W_L = L ⊗_K W_K` with the
canonical semi-linear action `galoisTwist` and the twist `W^τ = τ(W)`.  §3.4's standing setup
(S7's `RationalSetup`) presents `M_{ℚ[√-1]}` abstractly, with the base change
`ℚ[√-1] ⊗_ℚ M_ℚ ≃ M_{ℚ[√-1]}` and the conjugation `c` as fields.  The two are identified by
`galoisTwist_eq_conj`: `c` **is** the canonical action, read through the base change — which is
exactly what `RationalSetup.conj_baseChange` pins it to be. -/

section Transport

variable (S : RationalSetupOver ℓ E D Mq Mi)

/-- `c ∈ Gal(ℚ[√-1]/ℚ)` is an involution.  @census none (helper) -/
theorem galConj_mul_self : D.conj * D.conj = 1 := GF.conj_mul_self

theorem galConj_galConj (a : D.carrier) : D.conj (D.conj a) = a := D.conj_conj a

/-- `M_n` read on `ℚ[√-1] ⊗_ℚ M_ℚ`, through the base change.  @census none (helper) -/
noncomputable def Wc (n : ℤ) : Submodule D.carrier (D.carrier ⊗[E] Mq) :=
  (S.weight.comp n).comap (S.baseChange : (D.carrier ⊗[E] Mq) →ₗ[D.carrier] Mi)

theorem mem_Wc {n : ℤ} {x : D.carrier ⊗[E] Mq} :
    x ∈ Wc S n ↔ S.baseChange x ∈ S.weight.comp n := Iff.rfl

/-- **`c` is the canonical semi-linear action**, read through the base change: the content of
`RationalSetup.conj_baseChange` + `conj_smul`.  @census none (helper) -/
theorem galoisTwist_eq_conj (x : D.carrier ⊗[E] Mq) :
    galoisTwist D.conj x = S.baseChange.symm (S.conj (S.baseChange x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [galoisTwist_tmul]
    have h1 : S.baseChange (a ⊗ₜ[E] v) = a • S.baseChange ((1 : D.carrier) ⊗ₜ[E] v) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, S.conj_smul, S.conj_baseChange, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one, LinearEquiv.symm_apply_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- `(M_n)^τ = M_{-n}`: the twist of a component is the opposite component
(`RationalSetup.conj_comp` transported).  @census none (helper) -/
theorem twist_Wc (n : ℤ) : twist D.conj (Wc S n) = Wc S (-n) := by
  ext x
  rw [mem_twist]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show S.baseChange (galoisTwist D.conj y) ∈ S.weight.comp (-n)
    rw [galoisTwist_eq_conj S, LinearEquiv.apply_symm_apply]
    exact S.conj_comp n _ hy
  · intro hx
    refine ⟨galoisTwist D.conj x, ?_, galoisTwist_galoisTwist galConj_mul_self x⟩
    show S.baseChange (galoisTwist D.conj x) ∈ S.weight.comp n
    rw [galoisTwist_eq_conj S, LinearEquiv.apply_symm_apply]
    have := S.conj_comp (-n) _ hx
    rwa [neg_neg] at this

/-- The projection `M_{ℚ[√-1]} → M_n` (`WeightData.proj`), read on `ℚ[√-1] ⊗_ℚ M_ℚ`.
@census none (helper) -/
noncomputable def projT (n : ℤ) : (D.carrier ⊗[E] Mq) →ₗ[D.carrier] Wc S n :=
  LinearMap.codRestrict (Wc S n)
    (S.baseChange.symm.toLinearMap.comp ((S.weight.proj n).comp S.baseChange.toLinearMap))
    (fun x => by
      show S.baseChange (S.baseChange.symm (S.weight.proj n (S.baseChange x))) ∈ S.weight.comp n
      rw [LinearEquiv.apply_symm_apply]
      exact S.weight.proj_mem n _)

theorem projT_apply (n : ℤ) (x : D.carrier ⊗[E] Mq) :
    ((projT S n x : Wc S n) : D.carrier ⊗[E] Mq)
      = S.baseChange.symm (S.weight.proj n (S.baseChange x)) := rfl

/-- A map `W_+ → W_-^τ` of S6's shape, read back as an endomorphism of `M_{ℚ[√-1]}`: precompose with
the projection onto `M_{idx}` and the base change, postcompose with the inclusion and the base
change.  On `M_{idx}` it *is* the map; elsewhere it factors through the projection.
@census none (helper) -/
noncomputable def toEnd {p m : ℤ} (f : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m)) :
    Module.End D.carrier Mi :=
  S.baseChange.toLinearMap.comp ((twist D.conj (Wc S m)).subtype.comp
    (f.comp ((projT S p).comp S.baseChange.symm.toLinearMap)))

theorem toEnd_apply {p m : ℤ} (f : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m)) (v : Mi) :
    toEnd S f v = S.baseChange (f (projT S p (S.baseChange.symm v)) : D.carrier ⊗[E] Mq) := rfl

/-- A transported map lands in `W₋^τ = M_{-m}`.  @census none (helper) -/
theorem toEnd_mem {p m : ℤ} (f : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m)) (v : Mi) :
    toEnd S f v ∈ S.weight.comp (-m) := by
  rw [toEnd_apply]
  have h := (f (projT S p (S.baseChange.symm v))).2
  exact (twist_Wc S m).le h

end Transport

/-! ### The three cases as `prop:unipotentstabilization` consumes them -/

/-- A stabilization input: `φ_± : W_± → W_∓^τ` between two components of `M_{ℚ[√-1]}`, with the
membership proofs that make `φ_±` land in `W_∓^τ = M_{-idx_∓}` (`twist_Wc`).  This is the data of
`prop:unipotentstabilization`'s hypothesis (clause `RQ-4.01-H6`) in S7's vocabulary.

@census none (auxiliary; the input shape of `RQ-5.04-C2`)
@clauses   RQ2-5.04-S-O9 -/
structure StabInput (S : RationalSetupOver ℓ E D Mq Mi) where
  /-- `W₊ = M_{idxPlus}` -/
  idxPlus : ℤ
  /-- `W₋ = M_{idxMinus}` -/
  idxMinus : ℤ
  /-- `φ₊ : W₊ → W₋^τ = M_{-idxMinus}` -/
  phiPlus : Module.End D.carrier Mi
  /-- `φ₋ : W₋ → W₊^τ = M_{-idxPlus}` -/
  phiMinus : Module.End D.carrier Mi
  phiPlus_mem : ∀ v ∈ S.weight.comp idxPlus, phiPlus v ∈ S.weight.comp (-idxMinus)
  phiMinus_mem : ∀ v ∈ S.weight.comp idxMinus, phiMinus v ∈ S.weight.comp (-idxPlus)

/-- `c ∘ A ∘ c`, the conjugate of an endomorphism of `M_{ℚ[√-1]}` (`census/NOTATION.md` §3,
`φ^c = c ∘ φ ∘ c^{-1}` with `c = c^{-1}`); `ℚ[√-1]`-linear because `c` is semilinear over the
involution `D.conj`.  @census none (helper) -/
noncomputable def conjEnd (S : RationalSetupOver ℓ E D Mq Mi) (A : Module.End D.carrier Mi) :
    Module.End D.carrier Mi where
  toFun v := S.conj (A (S.conj v))
  map_add' v w := by rw [map_add, map_add, map_add]
  map_smul' a v := by
    simp only [RingHom.id_apply]
    rw [S.conj_smul, map_smul, S.conj_smul, galConj_galConj]

@[simp] theorem conjEnd_apply (S : RationalSetupOver ℓ E D Mq Mi) (A : Module.End D.carrier Mi)
    (v : Mi) : conjEnd S A v = S.conj (A (S.conj v)) := rfl

namespace StabInput

variable {S : RationalSetupOver ℓ E D Mq Mi} (C : StabInput S)

/-- The `τ`-conjugate description of the same datum: `(W₊^τ, W₋^τ, φ₊^τ, φ₋^τ)` with
`φ^τ = c ∘ φ ∘ c`.  For `inputStar` this is the pair `(M_{ℓ-1}, Y⋆)` that the amended source names
as the `c`-conjugate description of the `(⋆)` item (module docstring, note (1)).
@census none (helper) -/
noncomputable def conj : StabInput S where
  idxPlus := -C.idxPlus
  idxMinus := -C.idxMinus
  phiPlus := conjEnd S C.phiPlus
  phiMinus := conjEnd S C.phiMinus
  phiPlus_mem v hv := by
    rw [conjEnd_apply, neg_neg]
    have h1 := S.conj_comp _ _ hv
    rw [neg_neg] at h1
    have h2 := S.conj_comp _ _ (C.phiPlus_mem _ h1)
    rwa [neg_neg] at h2
  phiMinus_mem v hv := by
    rw [conjEnd_apply, neg_neg]
    have h1 := S.conj_comp _ _ hv
    rw [neg_neg] at h1
    have h2 := S.conj_comp _ _ (C.phiMinus_mem _ h1)
    rwa [neg_neg] at h2

/-- `φ₊` in S6's shape, `W₊ → W₋^τ`.  @census none (helper) -/
noncomputable def phpT : Wc S C.idxPlus →ₗ[D.carrier] twist D.conj (Wc S C.idxMinus) :=
  LinearMap.codRestrict _
    ((S.baseChange.symm.toLinearMap.comp (C.phiPlus.comp S.baseChange.toLinearMap)).comp
      (Wc S C.idxPlus).subtype)
    (fun x => by
      rw [twist_Wc]
      show S.baseChange (S.baseChange.symm (C.phiPlus (S.baseChange (x : D.carrier ⊗[E] Mq))))
        ∈ S.weight.comp (-C.idxMinus)
      rw [LinearEquiv.apply_symm_apply]
      exact C.phiPlus_mem _ x.2)

/-- `φ₋` in S6's shape, `W₋ → W₊^τ`.  @census none (helper) -/
noncomputable def phmT : Wc S C.idxMinus →ₗ[D.carrier] twist D.conj (Wc S C.idxPlus) :=
  LinearMap.codRestrict _
    ((S.baseChange.symm.toLinearMap.comp (C.phiMinus.comp S.baseChange.toLinearMap)).comp
      (Wc S C.idxMinus).subtype)
    (fun x => by
      rw [twist_Wc]
      show S.baseChange (S.baseChange.symm (C.phiMinus (S.baseChange (x : D.carrier ⊗[E] Mq))))
        ∈ S.weight.comp (-C.idxPlus)
      rw [LinearEquiv.apply_symm_apply]
      exact C.phiMinus_mem _ x.2)

theorem phpT_coe (x : Wc S C.idxPlus) :
    ((C.phpT x : twist D.conj (Wc S C.idxMinus)) : D.carrier ⊗[E] Mq)
      = S.baseChange.symm (C.phiPlus (S.baseChange (x : D.carrier ⊗[E] Mq))) := rfl

theorem phmT_coe (x : Wc S C.idxMinus) :
    ((C.phmT x : twist D.conj (Wc S C.idxPlus)) : D.carrier ⊗[E] Mq)
      = S.baseChange.symm (C.phiMinus (S.baseChange (x : D.carrier ⊗[E] Mq))) := rfl

/-- **The recursion of `cor:unipotentstabilization`** for this input — S6's `stabilizationSeq`,
`φ^{(0)}_± = φ_±`, `φ^{(k+1)}_± = ½(φ^{(k)}_± + (φ^{(k),τ}_∓)^{-1})`, on `ℚ[√-1] ⊗_ℚ M_ℚ`.
@census none (helper: the recursion `RQ-5.04-C7` is about) -/
noncomputable def seqT (k : ℕ) :
    (Wc S C.idxPlus →ₗ[D.carrier] twist D.conj (Wc S C.idxMinus)) ×
      (Wc S C.idxMinus →ₗ[D.carrier] twist D.conj (Wc S C.idxPlus)) :=
  stabilizationSeq (K := E) two_ne_zero galConj_mul_self C.phpT C.phmT k

@[simp] theorem seqT_zero : C.seqT 0 = (C.phpT, C.phmT) := rfl

/-- `φ^{(k)}_{•,+}` as an endomorphism of `M_{ℚ[√-1]}`.  @census none (helper) -/
noncomputable def seqPlus (k : ℕ) : Module.End D.carrier Mi := toEnd S (C.seqT k).1

/-- `φ^{(k)}_{•,−}` as an endomorphism of `M_{ℚ[√-1]}`.  @census none (helper) -/
noncomputable def seqMinus (k : ℕ) : Module.End D.carrier Mi := toEnd S (C.seqT k).2

/-- The value guard: at `k = 0` the transported plus-iterate is `φ₊` on `W₊`.  @census none -/
theorem seqPlus_zero_apply (v : Mi) (hv : v ∈ S.weight.comp C.idxPlus) :
    C.seqPlus 0 v = C.phiPlus v := by
  simp only [seqPlus, toEnd_apply, seqT_zero, phpT_coe, projT_apply, LinearEquiv.apply_symm_apply]
  rw [S.weight.proj_of_mem_same hv]

theorem seqMinus_zero_apply (v : Mi) (hv : v ∈ S.weight.comp C.idxMinus) :
    C.seqMinus 0 v = C.phiMinus v := by
  simp only [seqMinus, toEnd_apply, seqT_zero, phmT_coe, projT_apply, LinearEquiv.apply_symm_apply]
  rw [S.weight.proj_of_mem_same hv]

end StabInput

open Classical in
/-- The eventual value of an eventually constant sequence — `def:unipotentstabilization`'s
"`φ^{(∞)} := φ^{(k)}` for `k ≥ k₀`" as a total function (the `Ring.inverse` idiom of S6: junk `0`
if the sequence does not stabilize, and no statement of this stage refers to that case).
@census none (helper) -/
noncomputable def eventualValue {α : Type*} [Zero α] (f : ℕ → α) : α :=
  if h : ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → f k = f k₀ then f h.choose else 0

theorem eventualValue_eq {α : Type*} [Zero α] (f : ℕ → α) {k₀ : ℕ}
    (h : ∀ k, k₀ ≤ k → f k = f k₀) : eventualValue f = f k₀ := by
  classical
  have hex : ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → f k = f k₀ := ⟨k₀, h⟩
  rw [eventualValue, dif_pos hex]
  rw [← h (max k₀ hex.choose) (le_max_left _ _), hex.choose_spec _ (le_max_right _ _)]

namespace StabInput

variable {S : RationalSetupOver ℓ E D Mq Mi} (C : StabInput S)

/-- **The unipotent stabilization** `φ^{(∞)}_{•,±}` of this input (`def:unipotentstabilization`):
the eventual value of the recursion, in S6's shape.  @census none (helper) -/
noncomputable def limT :
    (Wc S C.idxPlus →ₗ[D.carrier] twist D.conj (Wc S C.idxMinus)) ×
      (Wc S C.idxMinus →ₗ[D.carrier] twist D.conj (Wc S C.idxPlus)) :=
  eventualValue C.seqT

/-- `φ^{(∞)}_{•,+}` on `M_{ℚ[√-1]}`.  @census none (helper) -/
noncomputable def limPlus : Module.End D.carrier Mi := toEnd S C.limT.1

/-- `φ^{(∞)}_{•,−}` on `M_{ℚ[√-1]}`.  @census none (helper) -/
noncomputable def limMinus : Module.End D.carrier Mi := toEnd S C.limT.2

theorem limPlus_mem (v : Mi) : C.limPlus v ∈ S.weight.comp (-C.idxMinus) := toEnd_mem S _ v
theorem limMinus_mem (v : Mi) : C.limMinus v ∈ S.weight.comp (-C.idxPlus) := toEnd_mem S _ v
theorem seqPlus_mem (k : ℕ) (v : Mi) : C.seqPlus k v ∈ S.weight.comp (-C.idxMinus) :=
  toEnd_mem S _ v
theorem seqMinus_mem (k : ℕ) (v : Mi) : C.seqMinus k v ∈ S.weight.comp (-C.idxPlus) :=
  toEnd_mem S _ v

end StabInput

/-! ### The three inputs -/

section Inputs

variable (S : RationalSetupOver ℓ E D Mq Mi)

theorem tMinus_mem_comp (n : ℤ) (v : Mi) (hv : v ∈ S.weight.comp n) :
    Split.tMinus S.toQiSetup v ∈ S.weight.comp n :=
  Submodule.smul_mem _ _ (casimirFactorProd_mem_comp S.weight _ _ n v hv)

/-- The `(+)` input: `W₊ = M_{ℓ+1}`, `W₋ = M_{-(ℓ+1)}`, `φ₊ = 𝟏`, `φ₋ = T₋` — the itemized
`casePlus`, with its typing.  @census none (helper) -/
noncomputable def inputPlus : StabInput S where
  idxPlus := (ℓ : ℤ) + 1
  idxMinus := -((ℓ : ℤ) + 1)
  phiPlus := 1
  phiMinus := Split.tMinus S.toQiSetup
  phiPlus_mem v hv := by rw [neg_neg]; exact hv
  phiMinus_mem v hv := tMinus_mem_comp S _ v hv

/-- The `(−)` input: the transpose of `(+)` — the itemized `caseMinus`, with its typing.
@census none (helper) -/
noncomputable def inputMinus : StabInput S where
  idxPlus := -((ℓ : ℤ) + 1)
  idxMinus := (ℓ : ℤ) + 1
  phiPlus := Split.tMinus S.toQiSetup
  phiMinus := 1
  phiPlus_mem v hv := tMinus_mem_comp S _ v hv
  phiMinus_mem v hv := by rw [neg_neg]; exact hv

/-- The `(⋆)` input: `W₊ = W₋ = M_{-(ℓ-1)}`, `φ₊ = φ₋ = X⋆ : M_{-(ℓ-1)} → M_{ℓ-1} = W_∓^τ` — the
instantiation that type-checks, and **the one the source itemizes** since the author's ruling of
2026-09-11 (module docstring, note (1)).  Its `τ`-conjugate description `(inputStar S hℓ).conj` has
`W = M_{ℓ-1}`, `φ = Y⋆` — the pair `(M_{ℓ-1}, Y⋆)` the source now names as exactly that.
@census none (helper) -/
noncomputable def inputStar (hℓ : 1 ≤ ℓ) : StabInput S where
  idxPlus := -((ℓ : ℤ) - 1)
  idxMinus := -((ℓ : ℤ) - 1)
  phiPlus := Split.xStar S.toQiSetup
  phiMinus := Split.xStar S.toQiSetup
  phiPlus_mem v hv := by
    rw [neg_neg]; exact Split.xStar_mem (Q := S.toQiSetup) (by ring) hℓ hv
  phiMinus_mem v hv := by
    rw [neg_neg]; exact Split.xStar_mem (Q := S.toQiSetup) (by ring) hℓ hv

/-- The itemized `casePlus`/`caseMinus` **are** the inputs `inputPlus`/`inputMinus`, field by
field; `caseStar` is the `τ`-conjugate description of `inputStar` in its `W₋`/`φ₋` half and
`inputStar` itself in its `W₊`/`φ₊` half.  Since the author's ruling of 2026-09-11 this is not a
repair of the source but a **sentence the source itself asserts** — that `(M_{ℓ-1}, Y⋆)` is the
`c`-conjugate description of the `(⋆)` item "and not a second one" (module docstring, note (1)).
@census none (helper) -/
theorem case_eq_input (hℓ : 1 ≤ ℓ) :
    ((casePlus S).idxPlus = (inputPlus S).idxPlus ∧ (casePlus S).idxMinus = (inputPlus S).idxMinus ∧
      (casePlus S).phiPlus = (inputPlus S).phiPlus ∧ (casePlus S).phiMinus = (inputPlus S).phiMinus) ∧
    ((caseMinus S).idxPlus = (inputMinus S).idxPlus ∧
      (caseMinus S).idxMinus = (inputMinus S).idxMinus ∧
      (caseMinus S).phiPlus = (inputMinus S).phiPlus ∧
      (caseMinus S).phiMinus = (inputMinus S).phiMinus) ∧
    ((caseStar S).idxPlus = (inputStar S hℓ).idxPlus ∧ (caseStar S).phiPlus = (inputStar S hℓ).phiPlus ∧
      (caseStar S).idxMinus = (inputStar S hℓ).conj.idxMinus ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) - 1),
        (caseStar S).phiMinus v = (inputStar S hℓ).conj.phiMinus v)) := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, by simp [caseStar, inputStar,
    StabInput.conj], ?_⟩
  intro v hv
  show Split.yStar S.toQiSetup v = S.conj (Split.xStar S.toQiSetup (S.conj v))
  exact ((conj_symmetry S hℓ).2 v).symm

end Inputs

/-! ### Transport of an endomorphism of `M_{ℚ[√-1]}` to `ℚ[√-1] ⊗_ℚ M_ℚ` -/

/-- An endomorphism of `M_{ℚ[√-1]}`, read on `ℚ[√-1] ⊗_ℚ M_ℚ` through the base change.
@census none (helper) -/
noncomputable def endWc (S : RationalSetupOver ℓ E D Mq Mi) (A : Module.End D.carrier Mi) :
    Module.End D.carrier (D.carrier ⊗[E] Mq) :=
  S.baseChange.symm.toLinearMap ∘ₗ (A ∘ₗ S.baseChange.toLinearMap)

theorem endWc_apply (S : RationalSetupOver ℓ E D Mq Mi) (A : Module.End D.carrier Mi)
    (x : D.carrier ⊗[E] Mq) : endWc S A x = S.baseChange.symm (A (S.baseChange x)) := rfl

theorem endWc_pow (S : RationalSetupOver ℓ E D Mq Mi) (A : Module.End D.carrier Mi) :
    ∀ (k : ℕ) (x : D.carrier ⊗[E] Mq),
      (endWc S A ^ k) x = S.baseChange.symm ((A ^ k) (S.baseChange x))
  | 0, x => by simp
  | (k + 1), x => by
      rw [pow_succ, Module.End.mul_apply, endWc_pow S A k, endWc_apply, pow_succ,
        Module.End.mul_apply, LinearEquiv.apply_symm_apply]

theorem isNilpotent_endWc (S : RationalSetupOver ℓ E D Mq Mi) {A : Module.End D.carrier Mi}
    (h : IsNilpotent A) : IsNilpotent (endWc S A) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, LinearMap.ext fun x => ?_⟩
  rw [endWc_pow S A k x, hk]
  simp

theorem endWc_mem {S : RationalSetupOver ℓ E D Mq Mi} {A : Module.End D.carrier Mi} {n : ℤ}
    (hA : ∀ v ∈ S.weight.comp n, A v ∈ S.weight.comp n) :
    ∀ x ∈ Wc S n, endWc S A x ∈ Wc S n := by
  intro x hx
  rw [mem_Wc, endWc_apply, LinearEquiv.apply_symm_apply]
  exact hA _ hx

/-- An endomorphism of `M` preserving `M_n`, read as an endomorphism of `Wc S n`. -/
noncomputable def endWcR (S : RationalSetupOver ℓ E D Mq Mi) {A : Module.End D.carrier Mi} {n : ℤ}
    (hA : ∀ v ∈ S.weight.comp n, A v ∈ S.weight.comp n) : Module.End D.carrier (Wc S n) :=
  (endWc S A).restrict (endWc_mem hA)

theorem endWcR_coe (S : RationalSetupOver ℓ E D Mq Mi) {A : Module.End D.carrier Mi} {n : ℤ}
    (hA : ∀ v ∈ S.weight.comp n, A v ∈ S.weight.comp n) (x : Wc S n) :
    ((endWcR S hA x : Wc S n) : D.carrier ⊗[E] Mq)
      = S.baseChange.symm (A (S.baseChange (x : D.carrier ⊗[E] Mq))) := rfl

theorem isNilpotent_endWcR (S : RationalSetupOver ℓ E D Mq Mi) {A : Module.End D.carrier Mi} {n : ℤ}
    (hA : ∀ v ∈ S.weight.comp n, A v ∈ S.weight.comp n) (h : IsNilpotent A) :
    IsNilpotent (endWcR S hA) :=
  Module.End.isNilpotent.restrict _ (isNilpotent_endWc S h)

/-! ### `HasInverse` for the transported maps -/

/-- `φ₊` bijective from `W₊` onto `W₋^τ` makes the transported `phpT` invertible.
@census none (helper) -/
theorem hasInverse_phpT {S : RationalSetupOver ℓ E D Mq Mi} (C : StabInput S)
    (h : Set.BijOn C.phiPlus (S.weight.comp C.idxPlus) (S.weight.comp (-C.idxMinus))) :
    HasInverse C.phpT := by
  have hbij : Function.Bijective C.phpT := by
    constructor
    · intro a b hab
      have h1 := congrArg (Subtype.val (p := fun x => x ∈ twist D.conj (Wc S C.idxMinus))) hab
      rw [C.phpT_coe, C.phpT_coe] at h1
      have h2 : C.phiPlus (S.baseChange (a : D.carrier ⊗[E] Mq))
          = C.phiPlus (S.baseChange (b : D.carrier ⊗[E] Mq)) :=
        S.baseChange.symm.injective h1
      exact Subtype.ext (S.baseChange.injective (h.injOn a.2 b.2 h2))
    · intro z
      have hz : (z : D.carrier ⊗[E] Mq) ∈ Wc S (-C.idxMinus) := by
        rw [← twist_Wc S C.idxMinus]; exact z.2
      obtain ⟨w, hw, hwz⟩ := h.surjOn hz
      refine ⟨⟨S.baseChange.symm w, ?_⟩, ?_⟩
      · rw [mem_Wc, LinearEquiv.apply_symm_apply]; exact hw
      · refine Subtype.ext ?_
        rw [C.phpT_coe]
        show S.baseChange.symm (C.phiPlus (S.baseChange (S.baseChange.symm w)))
          = (z : D.carrier ⊗[E] Mq)
        rw [LinearEquiv.apply_symm_apply, hwz]
        exact S.baseChange.symm_apply_apply _
  exact hasInverse_of_linearEquiv (LinearEquiv.ofBijective C.phpT hbij)

/-- `φ₋` bijective from `W₋` onto `W₊^τ` makes the transported `phmT` invertible.
@census none (helper) -/
theorem hasInverse_phmT {S : RationalSetupOver ℓ E D Mq Mi} (C : StabInput S)
    (h : Set.BijOn C.phiMinus (S.weight.comp C.idxMinus) (S.weight.comp (-C.idxPlus))) :
    HasInverse C.phmT := by
  have hbij : Function.Bijective C.phmT := by
    constructor
    · intro a b hab
      have h1 := congrArg (Subtype.val (p := fun x => x ∈ twist D.conj (Wc S C.idxPlus))) hab
      rw [C.phmT_coe, C.phmT_coe] at h1
      have h2 : C.phiMinus (S.baseChange (a : D.carrier ⊗[E] Mq))
          = C.phiMinus (S.baseChange (b : D.carrier ⊗[E] Mq)) :=
        S.baseChange.symm.injective h1
      exact Subtype.ext (S.baseChange.injective (h.injOn a.2 b.2 h2))
    · intro z
      have hz : (z : D.carrier ⊗[E] Mq) ∈ Wc S (-C.idxPlus) := by
        rw [← twist_Wc S C.idxPlus]; exact z.2
      obtain ⟨w, hw, hwz⟩ := h.surjOn hz
      refine ⟨⟨S.baseChange.symm w, ?_⟩, ?_⟩
      · rw [mem_Wc, LinearEquiv.apply_symm_apply]; exact hw
      · refine Subtype.ext ?_
        rw [C.phmT_coe]
        show S.baseChange.symm (C.phiMinus (S.baseChange (S.baseChange.symm w)))
          = (z : D.carrier ⊗[E] Mq)
        rw [LinearEquiv.apply_symm_apply, hwz]
        exact S.baseChange.symm_apply_apply _
  exact hasInverse_of_linearEquiv (LinearEquiv.ofBijective C.phmT hbij)

/-! ### The nilpotency identity, transported -/

/-- `eq:nilpotency` transported: `φ_-^τ ∘ φ_+ = 𝟏 + n` on `W₊` follows from the same identity
read on the component `M_{idxPlus}` of `M_{ℚ[√-1]}`.  @census none (helper) -/
theorem twistConj_phmT_comp_phpT {S : RationalSetupOver ℓ E D Mq Mi} (C : StabInput S)
    {n₀ : Module.End D.carrier Mi}
    (hmem : ∀ v ∈ S.weight.comp C.idxPlus, n₀ v ∈ S.weight.comp C.idxPlus)
    (hkey : ∀ v ∈ S.weight.comp C.idxPlus,
      S.conj (C.phiMinus (S.conj (C.phiPlus v))) = v + n₀ v) :
    (twistConj galConj_mul_self C.phmT).comp C.phpT = 1 + endWcR S hmem := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have hx : S.baseChange (x : D.carrier ⊗[E] Mq) ∈ S.weight.comp C.idxPlus := x.2
  show ((twistBack galConj_mul_self (C.phmT (twistBack galConj_mul_self (C.phpT x)))
      : Wc S C.idxPlus) : D.carrier ⊗[E] Mq)
    = ((x + endWcR S hmem x : Wc S C.idxPlus) : D.carrier ⊗[E] Mq)
  rw [Submodule.coe_add, endWcR_coe, twistBack_coe, galoisTwist_eq_conj S]
  have h1 : ((C.phmT (twistBack galConj_mul_self (C.phpT x))
      : twist D.conj (Wc S C.idxPlus)) : D.carrier ⊗[E] Mq)
      = S.baseChange.symm (C.phiMinus (S.conj (C.phiPlus
          (S.baseChange (x : D.carrier ⊗[E] Mq))))) := by
    rw [C.phmT_coe, twistBack_coe, galoisTwist_eq_conj S, LinearEquiv.apply_symm_apply,
      C.phpT_coe, LinearEquiv.apply_symm_apply]
  rw [h1, LinearEquiv.apply_symm_apply, hkey _ hx, map_add, S.baseChange.symm_apply_apply]

/-- The three `RQ-5.04-C2` conclusions for one input, from the component-level data. -/
theorem stab_prereq_of {S : RationalSetupOver ℓ E D Mq Mi} (C : StabInput S)
    (hp : Set.BijOn C.phiPlus (S.weight.comp C.idxPlus) (S.weight.comp (-C.idxMinus)))
    (hm : Set.BijOn C.phiMinus (S.weight.comp C.idxMinus) (S.weight.comp (-C.idxPlus)))
    {n₀ : Module.End D.carrier Mi} (hnil : IsNilpotent n₀)
    (hmem : ∀ v ∈ S.weight.comp C.idxPlus, n₀ v ∈ S.weight.comp C.idxPlus)
    (hkey : ∀ v ∈ S.weight.comp C.idxPlus,
      S.conj (C.phiMinus (S.conj (C.phiPlus v))) = v + n₀ v) :
    HasInverse C.phpT ∧ HasInverse C.phmT ∧
      ∃ n : Module.End D.carrier (Wc S C.idxPlus), IsNilpotent n ∧
        (twistConj galConj_mul_self C.phmT).comp C.phpT = 1 + n :=
  ⟨hasInverse_phpT C hp, hasInverse_phmT C hm,
    endWcR S hmem, isNilpotent_endWcR S hmem hnil, twistConj_phmT_comp_phpT C hmem hkey⟩

/-! ### The three inputs -/

/-- Rescaling by a nonzero scalar preserves bijectivity between two components.
@census none (helper) -/
theorem bijOn_smul_comp {S : RationalSetupOver ℓ E D Mq Mi} {A : Module.End D.carrier Mi} {p m : ℤ}
    {c : D.carrier} (hc : c ≠ 0)
    (h : Set.BijOn A (S.weight.comp p) (S.weight.comp m)) :
    Set.BijOn (c • A) (S.weight.comp p) (S.weight.comp m) := by
  refine ⟨fun v hv => ?_, fun a ha b hb hab => ?_, fun u hu => ?_⟩
  · exact Submodule.smul_mem _ _ (h.mapsTo hv)
  · refine h.injOn ha hb (smul_right_injective Mi hc ?_)
    exact hab
  · obtain ⟨v, hv, hvu⟩ := h.surjOn (Submodule.smul_mem _ c⁻¹ hu)
    refine ⟨v, hv, ?_⟩
    show c • A v = u
    rw [hvu, smul_inv_smul₀ hc]

/-- `𝟏` is a bijection of every component onto itself.  @census none (helper) -/
theorem bijOn_one_comp {S : RationalSetupOver ℓ E D Mq Mi} (p : ℤ) :
    Set.BijOn (1 : Module.End D.carrier Mi) (S.weight.comp p) (S.weight.comp p) :=
  ⟨fun _ hv => hv, fun _ _ _ _ h => h, fun u hu => ⟨u, hu, rfl⟩⟩

/-- `X⋆ : M_{-(ℓ-1)} → M_{ℓ-1}` is a bijection — `bijOn_pow_X` rescaled by `γ⋆⁻¹`.
@census none (helper) -/
theorem bijOn_xStar {S : RationalSetupOver ℓ E D Mq Mi} (hℓ : 1 ≤ ℓ) :
    Set.BijOn (Split.xStar S.toQiSetup) (S.weight.comp (-((ℓ : ℤ) - 1)))
      (S.weight.comp ((ℓ : ℤ) - 1)) :=
  bijOn_smul_comp (inv_ne_zero (Split.gammaStarF_ne_zero ℓ)) (Split.bijOn_pow_X S.toQiSetup hℓ).1

/-! ### `RQ-5.04-C2` — the prerequisites of `prop:unipotentstabilization`, on the components -/

/-- **`RQ-5.04-C2`** — in all three cases the prerequisites of `prop:unipotentstabilization` are
satisfied, **on the components** (ruling `R-S8-9`): `φ_±` are isomorphisms `W_± → W_∓^τ`, and
`φ_-^τ ∘ φ_+ = 𝟏_{W_+} + n` with `n` nilpotent (`eq:nilpotency`) — for `(+)`/`(−)` this is
`T_± = 𝟏 + n_±` on `M_{±(ℓ+1)}` (`cor:T_operators`, S7's `HC.Tplus_isUnit`), for `(⋆)` it is
`Y⋆X⋆ = 𝟏 + n̄⋆` on `M_{-(ℓ-1)}` (`cor:X_Y_inverses`, S7's `HC.xstar_ystar_relations`).  A
conclusion, no longer a hypothesis: both S7 results are proved on the merged tree (`R-S8-8`).

@census    none (auxiliary; discharges census clause `RQ-5.04-C2`)
@source    eq:varphiplus
@clauses   RQ2-5.04-C2
@imports   none
@divergence Stated for a bare `RationalSetup` (`gic` only), not `Gelfand.HCQObj` (`RQ-5.05`'s own
category, additionally admissibility/finite-generation/central-character) — a **true generalization**
(`CONVENTIONS.md` §3), since the proof uses none of the three extra conditions (2026-09-03,
`R-S8-16`(c), `V-S8-D1-4`(b)). -/
theorem stab_prereq (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ) :
    ∀ C ∈ ({inputPlus S, inputMinus S, inputStar S hℓ} : Set (StabInput S)),
      HasInverse C.phpT ∧ HasInverse C.phmT ∧
      ∃ n : Module.End D.carrier (Wc S C.idxPlus), IsNilpotent n ∧
        (twistConj galConj_mul_self C.phmT).comp C.phpT = 1 + n := by
  obtain ⟨hcT, hcX⟩ := conj_symmetry S hℓ
  obtain ⟨-, hbTm, np, nm, hnp, hnm, hTp, hTm⟩ := HC.WeightData.Tplus_isUnit S.weight S.gic hℓ
  obtain ⟨hnst, -, hYsXs⟩ := HC.WeightData.xStar_yStar_relations S.weight S.gic hℓ
  -- the `(+)` case
  have hmemP : ∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), np v ∈ S.weight.comp ((ℓ : ℤ) + 1) := by
    intro v hv
    have h : np v = Split.tMinus S.toQiSetup v - v := by
      rw [show Split.tMinus S.toQiSetup v = S.weight.Tplus ℓ v from rfl, hTp v hv]; abel
    rw [h]
    exact sub_mem (tMinus_mem_comp S _ v hv) hv
  have hP : HasInverse (inputPlus S).phpT ∧ HasInverse (inputPlus S).phmT ∧
      ∃ n : Module.End D.carrier (Wc S (inputPlus S).idxPlus), IsNilpotent n ∧
        (twistConj galConj_mul_self (inputPlus S).phmT).comp (inputPlus S).phpT = 1 + n := by
    refine stab_prereq_of (inputPlus S) ?_ ?_ hnp (n₀ := np) hmemP ?_
    · show Set.BijOn (1 : Module.End D.carrier Mi) (S.weight.comp ((ℓ : ℤ) + 1))
        (S.weight.comp (-(-((ℓ : ℤ) + 1))))
      rw [neg_neg]; exact bijOn_one_comp _
    · show Set.BijOn (Split.tMinus S.toQiSetup) (S.weight.comp (-((ℓ : ℤ) + 1)))
        (S.weight.comp (-((ℓ : ℤ) + 1)))
      exact hbTm
    · intro v hv
      show S.conj (Split.tMinus S.toQiSetup (S.conj ((1 : Module.End D.carrier Mi) v))) = v + np v
      rw [Module.End.one_apply, hcT v]
      exact hTp v hv
  -- the `(−)` case
  have hmemM : ∀ v ∈ S.weight.comp (-((ℓ : ℤ) + 1)), nm v ∈ S.weight.comp (-((ℓ : ℤ) + 1)) := by
    intro v hv
    have h : nm v = Split.tMinus S.toQiSetup v - v := by
      rw [show Split.tMinus S.toQiSetup v = S.weight.Tminus ℓ v from rfl, hTm v hv]; abel
    rw [h]
    exact sub_mem (tMinus_mem_comp S _ v hv) hv
  have hM : HasInverse (inputMinus S).phpT ∧ HasInverse (inputMinus S).phmT ∧
      ∃ n : Module.End D.carrier (Wc S (inputMinus S).idxPlus), IsNilpotent n ∧
        (twistConj galConj_mul_self (inputMinus S).phmT).comp (inputMinus S).phpT = 1 + n := by
    refine stab_prereq_of (inputMinus S) ?_ ?_ hnm (n₀ := nm) hmemM ?_
    · show Set.BijOn (Split.tMinus S.toQiSetup) (S.weight.comp (-((ℓ : ℤ) + 1)))
        (S.weight.comp (-((ℓ : ℤ) + 1)))
      exact hbTm
    · show Set.BijOn (1 : Module.End D.carrier Mi) (S.weight.comp ((ℓ : ℤ) + 1))
        (S.weight.comp (-(-((ℓ : ℤ) + 1))))
      rw [neg_neg]; exact bijOn_one_comp _
    · intro v hv
      show S.conj ((1 : Module.End D.carrier Mi)
        (S.conj (Split.tMinus S.toQiSetup v))) = v + nm v
      rw [Module.End.one_apply, S.conj_involutive]
      exact hTm v hv
  -- the `(⋆)` case
  have hmemS : ∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)),
      ((HC.WeightData.gammaStar D.carrier ℓ ^ 2)⁻¹ • S.weight.normRemainder ℓ) v
        ∈ S.weight.comp (-((ℓ : ℤ) - 1)) := fun v hv =>
    Submodule.smul_mem _ _ (S.weight.normRemainder_mem_comp _ v hv)
  have hS : HasInverse (inputStar S hℓ).phpT ∧ HasInverse (inputStar S hℓ).phmT ∧
      ∃ n : Module.End D.carrier (Wc S (inputStar S hℓ).idxPlus), IsNilpotent n ∧
        (twistConj galConj_mul_self (inputStar S hℓ).phmT).comp (inputStar S hℓ).phpT = 1 + n := by
    refine stab_prereq_of (inputStar S hℓ) ?_ ?_ hnst (n₀ := (HC.WeightData.gammaStar D.carrier ℓ ^ 2)⁻¹ • S.weight.normRemainder ℓ)
      hmemS ?_
    · show Set.BijOn (Split.xStar S.toQiSetup) (S.weight.comp (-((ℓ : ℤ) - 1)))
        (S.weight.comp (-(-((ℓ : ℤ) - 1))))
      rw [neg_neg]; exact bijOn_xStar hℓ
    · show Set.BijOn (Split.xStar S.toQiSetup) (S.weight.comp (-((ℓ : ℤ) - 1)))
        (S.weight.comp (-(-((ℓ : ℤ) - 1))))
      rw [neg_neg]; exact bijOn_xStar hℓ
    · intro v hv
      show S.conj (Split.xStar S.toQiSetup (S.conj (Split.xStar S.toQiSetup v)))
        = v + ((HC.WeightData.gammaStar D.carrier ℓ ^ 2)⁻¹ • S.weight.normRemainder ℓ) v
      rw [hcX (Split.xStar S.toQiSetup v)]
      exact hYsXs v hv
  rintro C (rfl | rfl | rfl)
  · exact hP
  · exact hM
  · exact hS

/-! ### `RQ-5.04-C7`–`C11` — the limits, and what they satisfy -/


section Lim

variable {S : RationalSetupOver ℓ E D Mq Mi}

/-- The projection `projT` is the identity on `Wc S p` itself.  @census none (helper) -/
theorem projT_coe_of_mem {p : ℤ} (x : Wc S p) :
    projT S p (x : D.carrier ⊗[E] Mq) = x := by
  have hx : S.baseChange (x : D.carrier ⊗[E] Mq) ∈ S.weight.comp p := x.2
  refine Subtype.ext ?_
  rw [projT_apply, S.weight.proj_of_mem_same hx]
  exact S.baseChange.symm_apply_apply _

/-- `toEnd S F` evaluated at a point of the component it is supported on.  @census none (helper) -/
theorem toEnd_apply_coe {p m : ℤ} (F : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m))
    (x : Wc S p) :
    toEnd S F (S.baseChange (x : D.carrier ⊗[E] Mq))
      = S.baseChange ((F x : twist D.conj (Wc S m)) : D.carrier ⊗[E] Mq) := by
  rw [toEnd_apply, S.baseChange.symm_apply_apply, projT_coe_of_mem]

/-- `c` read through the base change, in the direction `toEnd` needs.  @census none (helper) -/
theorem conj_baseChange_eq (y : D.carrier ⊗[E] Mq) :
    S.conj (S.baseChange y) = S.baseChange (galoisTwist D.conj y) := by
  rw [galoisTwist_eq_conj S, LinearEquiv.apply_symm_apply]

/-- **`eq:conjugateinverse` transported to the components.**  If `G^τ ∘ F = 𝟏` at the `Wc` level
then `c ∘ G ∘ c ∘ F = 𝟏` on `M_p`.  @census none (helper) -/
theorem conj_toEnd_conj_toEnd {p m : ℤ}
    (F : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m))
    (G : Wc S m →ₗ[D.carrier] twist D.conj (Wc S p))
    (h : (twistConj galConj_mul_self G).comp F = 1) (x : Wc S p) :
    S.conj (toEnd S G (S.conj (toEnd S F (S.baseChange (x : D.carrier ⊗[E] Mq)))))
      = S.baseChange (x : D.carrier ⊗[E] Mq) := by
  rw [toEnd_apply_coe, conj_baseChange_eq]
  have hy : galoisTwist D.conj ((F x : twist D.conj (Wc S m)) : D.carrier ⊗[E] Mq)
      = ((twistBack galConj_mul_self (F x) : Wc S m) : D.carrier ⊗[E] Mq) := rfl
  rw [hy, toEnd_apply_coe, conj_baseChange_eq]
  have hz : galoisTwist D.conj
      ((G (twistBack galConj_mul_self (F x)) : twist D.conj (Wc S p)) : D.carrier ⊗[E] Mq)
      = ((twistBack galConj_mul_self (G (twistBack galConj_mul_self (F x))) : Wc S p)
          : D.carrier ⊗[E] Mq) := rfl
  rw [hz]
  refine congrArg S.baseChange (congrArg Subtype.val ?_)
  have hh := congrArg (fun (f : Module.End D.carrier (Wc S p)) => f x) h
  simpa only [LinearMap.comp_apply, twistConj_apply, Module.End.one_apply] using hh

/-- `conj_toEnd_conj_toEnd`, read on the component as a `∀ v ∈ M_p`.  @census none (helper) -/
theorem conj_toEnd_conj_toEnd' {p m : ℤ}
    (F : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m))
    (G : Wc S m →ₗ[D.carrier] twist D.conj (Wc S p))
    (h : (twistConj galConj_mul_self G).comp F = 1) :
    ∀ v ∈ S.weight.comp p, S.conj (toEnd S G (S.conj (toEnd S F v))) = v := by
  intro v hv
  have hx : S.baseChange.symm v ∈ Wc S p := by
    rw [mem_Wc, LinearEquiv.apply_symm_apply]; exact hv
  have h2 : S.baseChange ((⟨S.baseChange.symm v, hx⟩ : Wc S p) : D.carrier ⊗[E] Mq) = v :=
    S.baseChange.apply_symm_apply v
  have := conj_toEnd_conj_toEnd F G h ⟨S.baseChange.symm v, hx⟩
  rwa [h2] at this

/-- **`RQ-5.04-C11`'s bijectivity, once.**  If `F : W_p → W_m^τ` is invertible then
`c ∘ F` is a bijection `M_p → M_m`.  @census none (helper) -/
theorem bijOn_conj_toEnd {p m : ℤ} (F : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m))
    (hF : HasInverse F) :
    Set.BijOn (fun v => S.conj (toEnd S F v)) (S.weight.comp p) (S.weight.comp m) := by
  obtain ⟨hinj, hsurj⟩ := hF.bijective
  refine ⟨fun v hv => ?_, fun a ha b hb hab => ?_, fun u hu => ?_⟩
  · have h1 := S.conj_comp (-m) _ (toEnd_mem S F v)
    rwa [neg_neg] at h1
  · have ha' : S.baseChange.symm a ∈ Wc S p := by
      rw [mem_Wc, LinearEquiv.apply_symm_apply]; exact ha
    have hb' : S.baseChange.symm b ∈ Wc S p := by
      rw [mem_Wc, LinearEquiv.apply_symm_apply]; exact hb
    have hab' : toEnd S F a = toEnd S F b := S.conj.injective hab
    rw [toEnd_apply, toEnd_apply] at hab'
    have h3 : F (projT S p (S.baseChange.symm a)) = F (projT S p (S.baseChange.symm b)) :=
      Subtype.ext (S.baseChange.injective hab')
    have h4 := hinj h3
    rw [show S.baseChange.symm a = ((⟨S.baseChange.symm a, ha'⟩ : Wc S p)
          : D.carrier ⊗[E] Mq) from rfl,
      show S.baseChange.symm b = ((⟨S.baseChange.symm b, hb'⟩ : Wc S p)
          : D.carrier ⊗[E] Mq) from rfl,
      projT_coe_of_mem, projT_coe_of_mem] at h4
    have h5 : S.baseChange.symm a = S.baseChange.symm b := congrArg Subtype.val h4
    exact S.baseChange.symm.injective h5
  · have hu' : S.baseChange.symm u ∈ Wc S m := by
      rw [mem_Wc, LinearEquiv.apply_symm_apply]; exact hu
    have hz : galoisTwist D.conj (S.baseChange.symm u) ∈ twist D.conj (Wc S m) :=
      galoisTwist_mem_twist hu'
    obtain ⟨x, hx⟩ := hsurj ⟨galoisTwist D.conj (S.baseChange.symm u), hz⟩
    refine ⟨S.baseChange (x : D.carrier ⊗[E] Mq), x.2, ?_⟩
    show S.conj (toEnd S F (S.baseChange (x : D.carrier ⊗[E] Mq))) = u
    rw [toEnd_apply_coe, conj_baseChange_eq, hx]
    show S.baseChange (galoisTwist D.conj (galoisTwist D.conj (S.baseChange.symm u))) = u
    rw [galoisTwist_galoisTwist galConj_mul_self, LinearEquiv.apply_symm_apply]

end Lim

section Limits

variable {S : RationalSetupOver ℓ E D Mq Mi}

/-- The `(−)` run's `φ₊` **is** the `(+)` run's `φ₋` — the `(−)` item is the transpose of the
`(+)` item (module docstring, note (2)).  @census none (helper) -/
theorem inputMinus_phpT (S : RationalSetupOver ℓ E D Mq Mi) :
    (inputMinus S).phpT = (inputPlus S).phmT := rfl
/-- The `(−)` run's `φ₋` is the `(+)` run's `φ₊`.  @census none (helper) -/
theorem inputMinus_phmT (S : RationalSetupOver ℓ E D Mq Mi) :
    (inputMinus S).phmT = (inputPlus S).phpT := rfl
/-- The `(⋆)` run is symmetric: `φ₊ = φ₋ = X⋆` on `W₊ = W₋ = M_{-(ℓ-1)}`.
@census none (helper) -/
theorem inputStar_phpT (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ) :
    (inputStar S hℓ).phpT = (inputStar S hℓ).phmT := rfl

/-- **The transposition identity** (`RQ-5.04-C5`/`C8`, `(±)` half): the `(−)` run's iterates are
the `(+)` run's, transposed — `rmk:unipotentstabilization` (S6's `stabilizationSeq_symm`) applied
to `inputMinus_phpT`/`inputMinus_phmT`.  @census none (helper) -/
theorem seqT_minus (S : RationalSetupOver ℓ E D Mq Mi) (k : ℕ) :
    (inputMinus S).seqT k = (((inputPlus S).seqT k).2, ((inputPlus S).seqT k).1) := by
  show stabilizationSeq (K := E) two_ne_zero galConj_mul_self
      (inputMinus S).phpT (inputMinus S).phmT k = _
  rw [inputMinus_phpT, inputMinus_phmT]
  exact stabilizationSeq_symm two_ne_zero galConj_mul_self _ _ k

/-- The `(⋆)` run's two iterates coincide at every step, by the same symmetry.
@census none (helper) -/
theorem seqT_star_fst_eq_snd (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ) (k : ℕ) :
    ((inputStar S hℓ).seqT k).1 = ((inputStar S hℓ).seqT k).2 := by
  have h : (inputStar S hℓ).seqT k = (((inputStar S hℓ).seqT k).2, ((inputStar S hℓ).seqT k).1) := by
    show stabilizationSeq (K := E) two_ne_zero galConj_mul_self
        (inputStar S hℓ).phpT (inputStar S hℓ).phmT k = _
    conv_lhs => rw [← inputStar_phpT S hℓ]
    exact stabilizationSeq_symm two_ne_zero galConj_mul_self _ _ k
  exact congrArg Prod.fst h

/-- **`cor:unipotentstabilization` for one run, without the Galois binders.**  The sequence is
constant past the nilpotency exponent, the limit `φ^{(∞)}` is that value, `eq:conjugateinverse`
holds in both directions, and both limit maps are invertible.  @census none (helper) -/
theorem stab_limit_spec (C : StabInput S)
    (hp : HasInverse C.phpT) (hm : HasInverse C.phmT)
    {n : Module.End D.carrier (Wc S C.idxPlus)} (hnil : IsNilpotent n)
    (hn : (twistConj galConj_mul_self C.phmT).comp C.phpT = 1 + n) :
    ∃ e : ℕ, (∀ k, e ≤ k → C.seqT k = C.seqT e) ∧ C.limT = C.seqT e ∧
      (twistConj galConj_mul_self C.limT.2).comp C.limT.1 = 1 ∧
      (twistConj galConj_mul_self C.limT.1).comp C.limT.2 = 1 ∧
      HasInverse C.limT.1 ∧ HasInverse C.limT.2 := by
  obtain ⟨e, he⟩ := hnil
  have hmT : HasInverse (twistConj galConj_mul_self C.phmT) := hm.twistConj _
  have hconst : ∀ k, e ≤ k → C.seqT k = C.seqT e := fun k hk =>
    stabilizationSeq_eq_of_le two_ne_zero galConj_mul_self C.phpT C.phmT hp hmT n e hn he hk
  have hlim : C.limT = C.seqT e := eventualValue_eq _ hconst
  obtain ⟨hF, hH, -⟩ := stabilizationSeq_invariant two_ne_zero galConj_mul_self
    C.phpT C.phmT hp hmT n e hn he e
  have hHF := stabilizationSeq_conjugate_inverse two_ne_zero galConj_mul_self
    C.phpT C.phmT hp hmT n e hn he (le_refl e)
  have hHF' : (twistConj galConj_mul_self (C.seqT e).2).comp (C.seqT e).1 = LinearMap.id := by
    rw [show (twistConj galConj_mul_self (C.seqT e).2).comp (C.seqT e).1 = 1 from hHF,
      Module.End.one_eq_id]
  refine ⟨e, hconst, hlim, ?_, ?_, ?_, ?_⟩
  · rw [hlim]; exact hHF
  · rw [hlim, Module.End.one_eq_id]
    exact twistConj_comp_eq_id _ _ _ (comp_eq_id_symm hF hHF')
  · rw [hlim]; exact hF
  · rw [hlim]; exact hasInverse_of_twistConj _ hH

end Limits

section Assembly

/-- **`RQ-5.04`'s conclusion, reduced to its one then-open conjunct.**  Everything `varphi_spec` claims
— `C7` (the three recursions stabilize), `C8`'s `(±)` half (the transposition identities), `C9`
(`eq:conjugateinversepm`), `C10` (`eq:conjugateinversestar`) and `C11` (semi-linearity and
bijectivity of `φ_± = c ∘ φ^{(∞)}_±`, `φ_⋆ = c ∘ φ^{(∞)}_⋆`) — follows from the ONE remaining
identity, `C8`'s `(⋆)` half: that the `τ`-conjugate `(⋆)` run's limit is the conjugate of the
`(⋆)` run's limit.  Written as an explicit reduction rather than left inside `varphi_spec`'s
then-`sorry`, so that shift 4's residue was exactly one conjunct and a verifier could see which
(`stages/S8/DESIGN-NOTES.md` §10.2); **that residue was discharged at shift 5 by
`conjStar_limit`**, so `varphi_spec` carries no `sorry` today and this module carries none.
(Re-tensed 2026-09-12, the seven-errata amendment's close-out round.)

Nothing here consumes `IsGalois ℚ ℚ[√-1]` or `FiniteDimensional ℚ ℚ[√-1]`: S6's `hgal`-carrying
`stabilization_spec`/`stabilizationSeq_bijective` are **not** used — the `SeqLemmas`
(`stabilizationSeq_eq_of_le`, `_conjugate_inverse`, `_invariant`) carry no Galois hypothesis, and
they are what `stab_limit_spec` consumes.  @census none (helper) -/
theorem varphi_spec_of_conjStar (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ)
    (hconjStar : ∀ v ∈ S.weight.comp ((ℓ : ℤ) - 1),
      S.conj ((inputStar S hℓ).limPlus (S.conj v)) = (inputStar S hℓ).conj.limPlus v) :
    ((∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (inputPlus S).seqT k = (inputPlus S).seqT k₀) ∧
      (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (inputMinus S).seqT k = (inputMinus S).seqT k₀) ∧
      (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (inputStar S hℓ).seqT k = (inputStar S hℓ).seqT k₀)) ∧
    (((inputMinus S).limPlus = (inputPlus S).limMinus ∧
        (inputMinus S).limMinus = (inputPlus S).limPlus) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) - 1),
        S.conj ((inputStar S hℓ).limPlus (S.conj v)) = (inputStar S hℓ).conj.limPlus v)) ∧
    ((∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1),
        S.conj ((inputMinus S).limPlus (S.conj ((inputPlus S).limPlus v))) = v) ∧
      (∀ v ∈ S.weight.comp (-((ℓ : ℤ) + 1)),
        S.conj ((inputPlus S).limPlus (S.conj ((inputMinus S).limPlus v))) = v)) ∧
    ((∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)),
        S.conj ((inputStar S hℓ).limPlus (S.conj ((inputStar S hℓ).limPlus v))) = v) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) - 1),
        (inputStar S hℓ).limPlus (S.conj ((inputStar S hℓ).limPlus (S.conj v))) = v)) ∧
    ((∀ (a : D.carrier) (v : Mi),
        S.conj ((inputPlus S).limPlus (a • v)) = D.conj a • S.conj ((inputPlus S).limPlus v)) ∧
      Set.BijOn (fun v => S.conj ((inputPlus S).limPlus v))
        (S.weight.comp ((ℓ : ℤ) + 1)) (S.weight.comp (-((ℓ : ℤ) + 1))) ∧
      (∀ (a : D.carrier) (v : Mi),
        S.conj ((inputMinus S).limPlus (a • v)) = D.conj a • S.conj ((inputMinus S).limPlus v)) ∧
      Set.BijOn (fun v => S.conj ((inputMinus S).limPlus v))
        (S.weight.comp (-((ℓ : ℤ) + 1))) (S.weight.comp ((ℓ : ℤ) + 1)) ∧
      (∀ (a : D.carrier) (v : Mi),
        S.conj ((inputStar S hℓ).limPlus (a • v))
          = D.conj a • S.conj ((inputStar S hℓ).limPlus v)) ∧
      Set.BijOn (fun v => S.conj ((inputStar S hℓ).limPlus v))
        (S.weight.comp (-((ℓ : ℤ) - 1))) (S.weight.comp (-((ℓ : ℤ) - 1)))) := by
  obtain ⟨hpP, hmP, nP, hnilP, hnP⟩ := stab_prereq S hℓ (inputPlus S) (by simp)
  obtain ⟨hpS, hmS, nS, hnilS, hnS⟩ := stab_prereq S hℓ (inputStar S hℓ) (by simp)
  obtain ⟨eP, hconstP, hlimP, hciP1, hciP2, hinvP1, hinvP2⟩ :=
    stab_limit_spec (inputPlus S) hpP hmP hnilP hnP
  obtain ⟨eS, hconstS, hlimS, hciS1, hciS2, hinvS1, hinvS2⟩ :=
    stab_limit_spec (inputStar S hℓ) hpS hmS hnilS hnS
  have hconstM : ∀ k, eP ≤ k → (inputMinus S).seqT k = (inputMinus S).seqT eP := by
    intro k hk
    rw [seqT_minus, seqT_minus, hconstP k hk]
  have hlimM : (inputMinus S).limT = (inputMinus S).seqT eP := eventualValue_eq _ hconstM
  have hMP : (inputMinus S).limT = (((inputPlus S).limT).2, ((inputPlus S).limT).1) := by
    rw [hlimM, hlimP, seqT_minus]
  have hC8a1 : (inputMinus S).limPlus = (inputPlus S).limMinus := by
    show toEnd S ((inputMinus S).limT).1 = toEnd S ((inputPlus S).limT).2
    rw [hMP]
    rfl
  have hC8a2 : (inputMinus S).limMinus = (inputPlus S).limPlus := by
    show toEnd S ((inputMinus S).limT).2 = toEnd S ((inputPlus S).limT).1
    rw [hMP]
    rfl
  have h12 : ((inputStar S hℓ).limT).1 = ((inputStar S hℓ).limT).2 := by
    rw [hlimS]; exact seqT_star_fst_eq_snd S hℓ eS
  have hC10a : ∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)),
      S.conj ((inputStar S hℓ).limPlus (S.conj ((inputStar S hℓ).limPlus v))) = v := by
    intro v hv
    have hthis := conj_toEnd_conj_toEnd' ((inputStar S hℓ).limT).1 ((inputStar S hℓ).limT).2
      hciS1 v hv
    rw [← h12] at hthis
    exact hthis
  refine ⟨⟨⟨eP, hconstP⟩, ⟨eP, hconstM⟩, ⟨eS, hconstS⟩⟩,
    ⟨⟨hC8a1, hC8a2⟩, ?_⟩,
    ⟨?_, ?_⟩, ⟨hC10a, ?_⟩,
    ⟨fun a v => by rw [map_smul, S.conj_smul], ?_,
     fun a v => by rw [map_smul, S.conj_smul], ?_,
     fun a v => by rw [map_smul, S.conj_smul], ?_⟩⟩
  · exact hconjStar
  · rw [hC8a1]
    exact conj_toEnd_conj_toEnd' ((inputPlus S).limT).1 ((inputPlus S).limT).2 hciP1
  · rw [hC8a1]
    exact conj_toEnd_conj_toEnd' ((inputPlus S).limT).2 ((inputPlus S).limT).1 hciP2
  · intro v hv
    have hcv : S.conj v ∈ S.weight.comp (-((ℓ : ℤ) - 1)) := S.conj_comp _ _ hv
    have h2 := congrArg S.conj (hC10a (S.conj v) hcv)
    rwa [S.conj_involutive, S.conj_involutive] at h2
  · exact bijOn_conj_toEnd ((inputPlus S).limT).1 hinvP1
  · rw [hC8a1]
    exact bijOn_conj_toEnd ((inputPlus S).limT).2 hinvP2
  · exact bijOn_conj_toEnd ((inputStar S hℓ).limT).1 hinvS1

end Assembly

/-! ### The first-iteration machinery: the transported step, and `linInv` against a named
inverse -/

section FirstIterMachinery

variable {S : RationalSetupOver ℓ E D Mq Mi}

/-- An endomorphism `A` of `M` sending `M_p` into `M_{-m}`, as a map `W_p → W_m^τ`. -/
noncomputable def ofEnd (S : RationalSetupOver ℓ E D Mq Mi) {p m : ℤ} (A : Module.End D.carrier Mi)
    (hA : ∀ v ∈ S.weight.comp p, A v ∈ S.weight.comp (-m)) :
    Wc S p →ₗ[D.carrier] twist D.conj (Wc S m) :=
  LinearMap.codRestrict _
    ((S.baseChange.symm.toLinearMap.comp (A.comp S.baseChange.toLinearMap)).comp
      (Wc S p).subtype)
    (fun x => by
      have hx : S.baseChange (x : D.carrier ⊗[E] Mq) ∈ S.weight.comp p := x.2
      rw [twist_Wc]
      show S.baseChange (S.baseChange.symm (A (S.baseChange (x : D.carrier ⊗[E] Mq))))
        ∈ S.weight.comp (-m)
      rw [LinearEquiv.apply_symm_apply]
      exact hA _ hx)

/-- The coercion of `ofEnd`.  @census none (helper) -/
theorem ofEnd_coe {p m : ℤ} (A : Module.End D.carrier Mi)
    (hA : ∀ v ∈ S.weight.comp p, A v ∈ S.weight.comp (-m)) (x : Wc S p) :
    ((ofEnd S A hA x : twist D.conj (Wc S m)) : D.carrier ⊗[E] Mq)
      = S.baseChange.symm (A (S.baseChange (x : D.carrier ⊗[E] Mq))) := rfl

/-- `toEnd` undoes `ofEnd` on the component `ofEnd` was built from.  @census none (helper) -/
theorem toEnd_ofEnd {p m : ℤ} (A : Module.End D.carrier Mi)
    (hA : ∀ v ∈ S.weight.comp p, A v ∈ S.weight.comp (-m)) (v : Mi)
    (hv : v ∈ S.weight.comp p) : toEnd S (ofEnd S A hA) v = A v := by
  have hx : S.baseChange.symm v ∈ Wc S p := by
    rw [mem_Wc, LinearEquiv.apply_symm_apply]; exact hv
  have h2 : S.baseChange ((⟨S.baseChange.symm v, hx⟩ : Wc S p) : D.carrier ⊗[E] Mq) = v :=
    S.baseChange.apply_symm_apply v
  have := toEnd_apply_coe (ofEnd S A hA) (⟨S.baseChange.symm v, hx⟩ : Wc S p)
  rw [h2, ofEnd_coe] at this
  rw [this]
  show S.baseChange (S.baseChange.symm (A (S.baseChange (S.baseChange.symm v)))) = A v
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- `toEnd` is additive in the map.  @census none (helper) -/
theorem toEnd_add {p m : ℤ} (F G : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m)) :
    toEnd S (F + G) = toEnd S F + toEnd S G := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.add_apply, toEnd_apply, toEnd_apply, toEnd_apply, LinearMap.add_apply,
    Submodule.coe_add, map_add]

/-- `toEnd` is `ℚ[√-1]`-linear in the map.  @census none (helper) -/
theorem toEnd_smul {p m : ℤ} (c : D.carrier)
    (F : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m)) :
    toEnd S (c • F) = c • toEnd S F := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.smul_apply, toEnd_apply, toEnd_apply, LinearMap.smul_apply,
    Submodule.coe_smul, map_smul]

/-- The junk-valued `linInv` agrees, after transport, with a NAMED two-sided inverse on the
components: the missing bridge of `DESIGN-NOTES.md` §10.3/§10.4. -/
theorem linInv_twistConj_phmT (C : StabInput S) (B : Module.End D.carrier Mi)
    (hB : ∀ v ∈ S.weight.comp C.idxPlus, B v ∈ S.weight.comp (-C.idxMinus))
    (hleft : ∀ v ∈ S.weight.comp (-C.idxMinus),
      B (S.conj (C.phiMinus (S.conj v))) = v)
    (hright : ∀ v ∈ S.weight.comp C.idxPlus,
      S.conj (C.phiMinus (S.conj (B v))) = v) :
    linInv (twistConj galConj_mul_self C.phmT) = ofEnd S B hB := by
  refine linInv_eq_of (LinearMap.ext fun y => Subtype.ext ?_) (LinearMap.ext fun x => Subtype.ext ?_)
  · have hy : S.baseChange (y : D.carrier ⊗[E] Mq) ∈ S.weight.comp (-C.idxMinus) :=
      (SetLike.ext_iff.mp (twist_Wc S C.idxMinus) (y : D.carrier ⊗[E] Mq)).mp y.2
    show ((ofEnd S B hB (twistBack galConj_mul_self (C.phmT
        (twistBack galConj_mul_self y))) : twist D.conj (Wc S C.idxMinus))
          : D.carrier ⊗[E] Mq) = (y : D.carrier ⊗[E] Mq)
    rw [ofEnd_coe]
    have hstep : S.baseChange ((twistBack galConj_mul_self (C.phmT
        (twistBack galConj_mul_self y)) : Wc S C.idxPlus) : D.carrier ⊗[E] Mq)
        = S.conj (C.phiMinus (S.conj (S.baseChange (y : D.carrier ⊗[E] Mq)))) := by
      show S.baseChange (galoisTwist D.conj ((C.phmT (twistBack galConj_mul_self y)
          : twist D.conj (Wc S C.idxPlus)) : D.carrier ⊗[E] Mq)) = _
      rw [C.phmT_coe]
      show S.baseChange (galoisTwist D.conj (S.baseChange.symm (C.phiMinus (S.baseChange
        (galoisTwist D.conj (y : D.carrier ⊗[E] Mq)))))) = _
      rw [galoisTwist_eq_conj S, LinearEquiv.apply_symm_apply, galoisTwist_eq_conj S,
        LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rw [hstep, hleft _ hy]
    exact S.baseChange.symm_apply_apply _
  · have hx : S.baseChange (x : D.carrier ⊗[E] Mq) ∈ S.weight.comp C.idxPlus := x.2
    show ((twistBack galConj_mul_self (C.phmT (twistBack galConj_mul_self
        (ofEnd S B hB x))) : Wc S C.idxPlus) : D.carrier ⊗[E] Mq)
      = (x : D.carrier ⊗[E] Mq)
    have h2 : S.baseChange ((twistBack galConj_mul_self (ofEnd S B hB x) : Wc S C.idxMinus)
        : D.carrier ⊗[E] Mq) = S.conj (B (S.baseChange (x : D.carrier ⊗[E] Mq))) := by
      rw [twistBack_coe, galoisTwist_eq_conj S, ofEnd_coe, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
    rw [twistBack_coe, galoisTwist_eq_conj S, C.phmT_coe, LinearEquiv.apply_symm_apply, h2,
      hright _ hx]
    exact S.baseChange.symm_apply_apply _

/-- One stabilization step, read on the component, with the junk inverse replaced by a named one. -/
theorem seqPlus_one_apply (C : StabInput S) {B : Module.End D.carrier Mi}
    (hB : ∀ v ∈ S.weight.comp C.idxPlus, B v ∈ S.weight.comp (-C.idxMinus))
    (hleft : ∀ v ∈ S.weight.comp (-C.idxMinus), B (S.conj (C.phiMinus (S.conj v))) = v)
    (hright : ∀ v ∈ S.weight.comp C.idxPlus, S.conj (C.phiMinus (S.conj (B v))) = v)
    (v : Mi) (hv : v ∈ S.weight.comp C.idxPlus) :
    C.seqPlus 1 v = ((2 : D.carrier)⁻¹) • (C.phiPlus v + B v) := by
  have h1 : (C.seqT 1).1 = half (two_ne_zero_of_base (K := E) two_ne_zero) •
      (C.phpT + linInv (twistConj galConj_mul_self C.phmT)) := rfl
  show toEnd S (C.seqT 1).1 v = _
  rw [h1, linInv_twistConj_phmT C B hB hleft hright, toEnd_smul, toEnd_add,
    LinearMap.smul_apply, LinearMap.add_apply, half_eq, toEnd_ofEnd B hB v hv,
    show toEnd S C.phpT v = C.phiPlus v from C.seqPlus_zero_apply v hv]

/-- `T₋` commutes with `Y⋆` (`T₋` is a polynomial in the Casimir).  @census none (helper) -/
theorem tMinus_yStar_apply (Q : Split.QiSetup D.carrier ℓ Mi) (v : Mi) :
    Split.tMinus Q (Split.yStar Q v) = Split.yStar Q (Split.tMinus Q v) := by
  have h : Commute (Split.tMinus Q) (Q.weight.Y ^ (ℓ - 1)) := (Split.commute_tMinus_Y Q).pow_right _
  show Split.tMinus Q (((Split.gammaStarF D.carrier ℓ)⁻¹ • Q.weight.Y ^ (ℓ - 1)) v)
    = ((Split.gammaStarF D.carrier ℓ)⁻¹ • Q.weight.Y ^ (ℓ - 1)) (Split.tMinus Q v)
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
  congr 1
  simpa only [Module.End.mul_apply] using congrArg (fun f : Module.End D.carrier Mi => f v) h

section C4

variable (S)

/-- `φ^{(1)}_{+,+} = ½(𝟏 + T₊⁻¹)` on `M_{ℓ+1}` — census clause `RQ-5.04-C4`, first display.
@census none (helper) -/
theorem first_iter_plus (hℓ : 1 ≤ ℓ) (tPlusInv : Module.End D.carrier Mi)
    (htPlusInv : (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), tPlusInv v ∈ S.weight.comp ((ℓ : ℤ) + 1)) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), tPlusInv (Split.tPlus S.toQiSetup v) = v) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), Split.tPlus S.toQiSetup (tPlusInv v) = v))
    (v : Mi) (hv : v ∈ S.weight.comp ((ℓ : ℤ) + 1)) :
    (inputPlus S).seqPlus 1 v = ((2 : D.carrier)⁻¹) • (v + tPlusInv v) := by
  obtain ⟨hm, hl, hr⟩ := htPlusInv
  obtain ⟨hcT, -⟩ := conj_symmetry S hℓ
  have hidx : -(inputPlus S).idxMinus = ((ℓ : ℤ) + 1) := by simp [inputPlus]
  refine seqPlus_one_apply (inputPlus S) (B := tPlusInv) ?_ ?_ ?_ v hv
  · intro w hw
    rw [hidx]
    exact hm w hw
  · intro w hw
    rw [hidx] at hw
    show tPlusInv (S.conj (Split.tMinus S.toQiSetup (S.conj w))) = w
    rw [hcT w]
    exact hl w hw
  · intro w hw
    show S.conj (Split.tMinus S.toQiSetup (S.conj (tPlusInv w))) = w
    rw [hcT (tPlusInv w)]
    exact hr w hw

/-- `φ^{(1)}_{+,−} = ½(T₋ + 𝟏)` on `M_{-(ℓ+1)}` — `RQ-5.04-C4`, second display, from the `(+)`
case through the transposition identity `seqT_minus`.  @census none (helper) -/
theorem first_iter_minus (v : Mi) (hv : v ∈ S.weight.comp (-((ℓ : ℤ) + 1))) :
    (inputPlus S).seqMinus 1 v = ((2 : D.carrier)⁻¹) • (Split.tMinus S.toQiSetup v + v) := by
  have hswap : (inputPlus S).seqMinus 1 = (inputMinus S).seqPlus 1 := by
    show toEnd S ((inputPlus S).seqT 1).2 = toEnd S ((inputMinus S).seqT 1).1
    rw [seqT_minus]
    rfl
  have hidx : -(inputMinus S).idxMinus = -((ℓ : ℤ) + 1) := by simp [inputMinus]
  rw [hswap]
  refine seqPlus_one_apply (inputMinus S) (B := 1) ?_ ?_ ?_ v hv
  · intro w hw
    rw [hidx]
    exact hw
  · intro w _
    show (1 : Module.End D.carrier Mi) (S.conj ((1 : Module.End D.carrier Mi) (S.conj w))) = w
    rw [Module.End.one_apply, Module.End.one_apply, S.conj_involutive]
  · intro w _
    show S.conj ((1 : Module.End D.carrier Mi) (S.conj ((1 : Module.End D.carrier Mi) w))) = w
    rw [Module.End.one_apply, Module.End.one_apply, S.conj_involutive]

end C4

/-- `X⋆ ∘ c = c ∘ Y⋆`, the form of `RQ-5.04-C3` the `(⋆)` first iteration consumes.
@census none (helper) -/
theorem xStar_conj_apply (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ) (u : Mi) :
    Split.xStar S.toQiSetup (S.conj u) = S.conj (Split.yStar S.toQiSetup u) := by
  obtain ⟨-, hcX⟩ := conj_symmetry S hℓ
  have h := hcX u
  rw [← h, S.conj_involutive]

/-- **`c ∘ Y⋆⁻¹ ∘ c = X⋆⁻¹` on `M_{ℓ-1}`.**  `StarInverses` does NOT require its two inverse
fields to be Galois-conjugate; they are, because both sides are right inverses of the bijection
`X⋆ : M_{-(ℓ-1)} → M_{ℓ-1}`.  @census none (helper) -/
theorem conj_yStarInv_conj (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup)
    (hℓ : 1 ≤ ℓ) (v : Mi) (hv : v ∈ S.weight.comp ((ℓ : ℤ) - 1)) :
    S.conj (I.yStarInv (S.conj v)) = I.xStarInv v := by
  have hcv : S.conj v ∈ S.weight.comp (-((ℓ : ℤ) - 1)) := S.conj_comp _ _ hv
  have h1 : S.conj (I.yStarInv (S.conj v)) ∈ S.weight.comp (-((ℓ : ℤ) - 1)) :=
    S.conj_comp _ _ (I.yStarInv_mem hcv)
  have h2 : I.xStarInv v ∈ S.weight.comp (-((ℓ : ℤ) - 1)) := I.xStarInv_mem hv
  refine (bijOn_xStar hℓ).injOn h1 h2 ?_
  rw [xStar_conj_apply S hℓ, Split.yStar_yStarInv S.toQiSetup I _ hcv, S.conj_involutive,
    Split.xStar_xStarInv S.toQiSetup I _ hv]

/-- `φ^{(1)}_{⋆,+} = ½(X⋆ + Y⋆⁻¹)` on `M_{-(ℓ-1)}` — `RQ-5.04-C4`, third display.
@census none (helper) -/
theorem first_iter_star (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup)
    (hℓ : 1 ≤ ℓ) (v : Mi) (hv : v ∈ S.weight.comp (-((ℓ : ℤ) - 1))) :
    (inputStar S hℓ).seqPlus 1 v
      = ((2 : D.carrier)⁻¹) • (Split.xStar S.toQiSetup v + I.yStarInv v) := by
  obtain ⟨-, hcX⟩ := conj_symmetry S hℓ
  have hidx : -(inputStar S hℓ).idxMinus = ((ℓ : ℤ) - 1) := by simp [inputStar]
  refine seqPlus_one_apply (inputStar S hℓ) (B := I.yStarInv) ?_ ?_ ?_ v hv
  · intro w hw
    rw [hidx]
    exact I.yStarInv_mem hw
  · intro w hw
    rw [hidx] at hw
    show I.yStarInv (S.conj (Split.xStar S.toQiSetup (S.conj w))) = w
    rw [hcX w]
    exact Split.yStarInv_yStar S.toQiSetup I w hw
  · intro w hw
    show S.conj (Split.xStar S.toQiSetup (S.conj (I.yStarInv w))) = w
    rw [hcX (I.yStarInv w)]
    exact Split.yStar_yStarInv S.toQiSetup I w hw

/-- `φ^{(1)}_{⋆,−} = ½(Y⋆ + X⋆⁻¹)` on `M_{ℓ-1}` — `RQ-5.04-C4`, fourth display, on the
`τ`-conjugate `(⋆)` run.  @census none (helper) -/
theorem first_iter_starConj (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup)
    (hℓ : 1 ≤ ℓ) (v : Mi) (hv : v ∈ S.weight.comp ((ℓ : ℤ) - 1)) :
    (inputStar S hℓ).conj.seqPlus 1 v
      = ((2 : D.carrier)⁻¹) • (Split.yStar S.toQiSetup v + I.xStarInv v) := by
  obtain ⟨-, hcX⟩ := conj_symmetry S hℓ
  have hidxP : (inputStar S hℓ).conj.idxPlus = ((ℓ : ℤ) - 1) := by
    simp [StabInput.conj, inputStar]
  have hidxM : -(inputStar S hℓ).conj.idxMinus = -((ℓ : ℤ) - 1) := by
    simp [StabInput.conj, inputStar]
  have hv' : v ∈ S.weight.comp (inputStar S hℓ).conj.idxPlus := by rw [hidxP]; exact hv
  have hkey := seqPlus_one_apply (inputStar S hℓ).conj (B := I.xStarInv)
    (fun w hw => by
      rw [hidxP] at hw
      rw [hidxM]
      exact I.xStarInv_mem hw)
    (fun w hw => by
      rw [hidxM] at hw
      show I.xStarInv (S.conj (S.conj (Split.xStar S.toQiSetup (S.conj (S.conj w))))) = w
      rw [S.conj_involutive, S.conj_involutive]
      exact Split.xStarInv_xStar S.toQiSetup I w hw)
    (fun w hw => by
      rw [hidxP] at hw
      show S.conj (S.conj (Split.xStar S.toQiSetup (S.conj (S.conj (I.xStarInv w))))) = w
      rw [S.conj_involutive, S.conj_involutive]
      exact Split.xStar_xStarInv S.toQiSetup I w hw)
    v hv'
  rw [hkey]
  congr 2
  show S.conj (Split.xStar S.toQiSetup (S.conj v)) = Split.yStar S.toQiSetup v
  exact hcX v

/-- `RQ-5.04-C5`'s `(⋆)` half at `k = 1`: the displayed `φ^{(1)}_{⋆,−}` is the conjugate of
`φ^{(1)}_{⋆,+}`.  @census none (helper) -/
theorem first_iter_C5_star (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup)
    (hℓ : 1 ≤ ℓ) (v : Mi) (hv : v ∈ S.weight.comp ((ℓ : ℤ) - 1)) :
    S.conj ((inputStar S hℓ).seqPlus 1 (S.conj v)) = (inputStar S hℓ).conj.seqPlus 1 v := by
  obtain ⟨-, hcX⟩ := conj_symmetry S hℓ
  have hcv : S.conj v ∈ S.weight.comp (-((ℓ : ℤ) - 1)) := S.conj_comp _ _ hv
  have hfix : D.conj ((2 : D.carrier)⁻¹) = ((2 : D.carrier)⁻¹) := by
    rw [map_inv₀, GF.conj_ofNat]
  rw [first_iter_star S I hℓ _ hcv, first_iter_starConj S I hℓ v hv,
    S.conj_smul_fixed hfix, map_add, hcX v, conj_yStarInv_conj S I hℓ v hv]


/-- `Y⋆ : M_{ℓ-1} → M_{-(ℓ-1)}` is a bijection — `bijOn_pow_X` rescaled by `γ⋆⁻¹`.
@census none (helper) -/
theorem bijOn_yStar (hℓ : 1 ≤ ℓ) :
    Set.BijOn (Split.yStar S.toQiSetup) (S.weight.comp ((ℓ : ℤ) - 1))
      (S.weight.comp (-((ℓ : ℤ) - 1))) :=
  bijOn_smul_comp (inv_ne_zero (Split.gammaStarF_ne_zero ℓ)) (Split.bijOn_pow_X S.toQiSetup hℓ).2

section C6

/-- `T₋ ∘ Y⋆⁻¹ = X⋆` on `M_{-(ℓ-1)}`; both sides have the same `Y⋆`-image and `Y⋆` is injective
there.  @census none (helper) -/
theorem tMinus_yStarInv (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup)
    (hℓ : 1 ≤ ℓ) (v : Mi) (hv : v ∈ S.weight.comp (-((ℓ : ℤ) - 1))) :
    Split.tMinus S.toQiSetup (I.yStarInv v) = Split.xStar S.toQiSetup v := by
  have h1 : Split.tMinus S.toQiSetup (I.yStarInv v) ∈ S.weight.comp ((ℓ : ℤ) - 1) :=
    tMinus_mem_comp S _ _ (I.yStarInv_mem hv)
  have h2 : Split.xStar S.toQiSetup v ∈ S.weight.comp ((ℓ : ℤ) - 1) :=
    Split.xStar_mem (Q := S.toQiSetup) (by ring) hℓ hv
  refine (bijOn_yStar hℓ).injOn h1 h2 ?_
  have e1 : Split.yStar S.toQiSetup (Split.tMinus S.toQiSetup (I.yStarInv v))
      = Split.tMinus S.toQiSetup (Split.yStar S.toQiSetup (I.yStarInv v)) :=
    (tMinus_yStar_apply S.toQiSetup _).symm
  have e2 : Split.yStar S.toQiSetup (I.yStarInv v) = v := Split.yStar_yStarInv S.toQiSetup I _ hv
  have e3 : Split.yStar S.toQiSetup (Split.xStar S.toQiSetup v) = Split.tMinus S.toQiSetup v :=
    Split.yStar_xStar_apply S.toQiSetup hℓ v hv
  rw [e1, e2, e3]

/-- `T₊⁻¹ ∘ X ∘ X⋆ = X ∘ Y⋆⁻¹` on `M_{-(ℓ-1)}` — the identity `eq:firstiteration`'s **second**
square needs and the normalized diagram's second square (trivially `rfl`) does not.
@census none (helper) -/
theorem tPlusInv_X_xStar (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup) (hℓ : 1 ≤ ℓ)
    (tPlusInv : Module.End D.carrier Mi)
    (hl : ∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), tPlusInv (Split.tPlus S.toQiSetup v) = v)
    (v : Mi) (hv : v ∈ S.weight.comp (-((ℓ : ℤ) - 1))) :
    tPlusInv (S.weight.X (Split.xStar S.toQiSetup v)) = S.weight.X (I.yStarInv v) := by
  have hmem : S.weight.X (I.yStarInv v) ∈ S.weight.comp ((ℓ : ℤ) + 1) :=
    Split.x_mem (Q := S.toQiSetup) (m := (ℓ : ℤ) - 1) (by ring) (I.yStarInv_mem hv)
  have e1 : Split.tMinus S.toQiSetup (S.weight.X (I.yStarInv v))
      = S.weight.X (Split.tMinus S.toQiSetup (I.yStarInv v)) := Split.tMinus_X_apply S.toQiSetup _
  have hstep : Split.tPlus S.toQiSetup (S.weight.X (I.yStarInv v))
      = S.weight.X (Split.xStar S.toQiSetup v) := by
    have : Split.tMinus S.toQiSetup (S.weight.X (I.yStarInv v))
        = S.weight.X (Split.xStar S.toQiSetup v) := by
      rw [e1, tMinus_yStarInv S I hℓ v hv]
    exact this
  rw [← hstep, hl _ hmem]

/-- `Y⋆⁻¹ ∘ X⋆⁻¹ ∘ Y = Y ∘ T₊⁻¹` on `M_{ℓ+1}` — the identity `eq:firstiteration`'s **fourth**
square needs beyond `sq_back_right`.  @census none (helper) -/
theorem yStarInv_xStarInv_Y (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup) (hℓ : 1 ≤ ℓ)
    (tPlusInv : Module.End D.carrier Mi)
    (hr : ∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), Split.tPlus S.toQiSetup (tPlusInv v) = v)
    (hm : ∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), tPlusInv v ∈ S.weight.comp ((ℓ : ℤ) + 1))
    (v : Mi) (hv : v ∈ S.weight.comp ((ℓ : ℤ) + 1)) :
    I.yStarInv (I.xStarInv (S.weight.Y v)) = S.weight.Y (tPlusInv v) := by
  have hYv : S.weight.Y v ∈ S.weight.comp ((ℓ : ℤ) - 1) :=
    Split.y_mem (Q := S.toQiSetup) (m := (ℓ : ℤ) + 1) (by ring) hv
  have hxi : I.xStarInv (S.weight.Y v) ∈ S.weight.comp (-((ℓ : ℤ) - 1)) := I.xStarInv_mem hYv
  have hYt : S.weight.Y (tPlusInv v) ∈ S.weight.comp ((ℓ : ℤ) - 1) :=
    Split.y_mem (Q := S.toQiSetup) (m := (ℓ : ℤ) + 1) (by ring) (hm v hv)
  have hL : I.yStarInv (I.xStarInv (S.weight.Y v)) ∈ S.weight.comp ((ℓ : ℤ) - 1) :=
    I.yStarInv_mem hxi
  have hkey : Split.yStar S.toQiSetup (S.weight.Y (tPlusInv v)) = I.xStarInv (S.weight.Y v) := by
    have h1 : Split.yStar S.toQiSetup (S.weight.Y (tPlusInv v)) ∈ S.weight.comp (-((ℓ : ℤ) - 1)) :=
      Split.yStar_mem (Q := S.toQiSetup) (m := (ℓ : ℤ) - 1) (by ring) hℓ hYt
    refine (bijOn_xStar hℓ).injOn h1 hxi ?_
    have e1 : Split.xStar S.toQiSetup (Split.yStar S.toQiSetup (S.weight.Y (tPlusInv v)))
        = Split.tMinus S.toQiSetup (S.weight.Y (tPlusInv v)) := Split.xStar_yStar_apply S.toQiSetup hℓ _ hYt
    have e2 : Split.tMinus S.toQiSetup (S.weight.Y (tPlusInv v))
        = S.weight.Y (Split.tMinus S.toQiSetup (tPlusInv v)) := Split.tMinus_Y_apply S.toQiSetup _
    have e3 : Split.tMinus S.toQiSetup (tPlusInv v) = v := hr v hv
    have e4 : Split.xStar S.toQiSetup (I.xStarInv (S.weight.Y v)) = S.weight.Y v :=
      Split.xStar_xStarInv S.toQiSetup I _ hYv
    rw [e1, e2, e3, e4]
  refine (bijOn_yStar hℓ).injOn hL hYt ?_
  rw [Split.yStar_yStarInv S.toQiSetup I _ hxi, hkey]

end C6

end FirstIterMachinery

/-! ### `RQ-5.04-C4`/`C5`/`C6` — the first iteration -/

/-! ### `RQ-5.04-C8`, the `(⋆)` half — the conjugate run, step by step

The one conjunct of `varphi_spec` that shift 4 left open (`DESIGN-NOTES.md` §10.3): the limit of
the `τ`-conjugate `(⋆)` run is the conjugate of the `(⋆)` run's limit.  Proved along §10.3's
**route 2** — induction on `k` at the `M_{ℚ[√-1]}` level rather than transport of
`stabilizationSeq` along `LinearEquiv.ofEq (twist_Wc …)` — with the generalisation §10.3 named as
the missing piece supplied not by weakening `linInv_twistConj_phmT`'s named inverse `B` but by
**taking the junk inverse itself as the name**: `seqInvPlus k := toEnd S (linInv (φ^{(k),τ}_-))`
is an honest endomorphism of `M_{ℚ[√-1]}`, the step formula `φ^{(k+1)}_+ = ½(φ^{(k)}_+ + Ψ_k)`
holds with **no** membership side condition (`toEnd` is additive and `ℚ[√-1]`-linear in the map),
and the two component inverse laws for `Ψ_k` are `conj_toEnd_conj_toEnd'` read at
`linInv`'s two sides.  The induction then closes by uniqueness of a two-sided component inverse
(`conj_inv_unique`), which is exactly `conj_yStarInv_conj`'s argument at a general `k`. -/

section ConjRun

variable {S : RationalSetupOver ℓ E D Mq Mi}

/-- `c` is an involution, as a rewrite.  @census none (helper) -/
theorem conj_conj (S : RationalSetupOver ℓ E D Mq Mi) (v : Mi) : S.conj (S.conj v) = v :=
  S.conj_involutive v

/-- `c` is injective.  @census none (helper) -/
theorem conj_inj (S : RationalSetupOver ℓ E D Mq Mi) : Function.Injective S.conj :=
  S.conj_involutive.injective

/-- `c` sends `M_{-n}` to `M_n`.  @census none (helper) -/
theorem conj_comp' (S : RationalSetupOver ℓ E D Mq Mi) {n : ℤ} {v : Mi} (hv : v ∈ S.weight.comp (-n)) :
    S.conj v ∈ S.weight.comp n := by
  have := S.conj_comp _ _ hv; rwa [neg_neg] at this

/-- Conjugation carries a bijection `M_p → M_m` to a bijection `M_{-p} → M_{-m}`.
@census none (helper) -/
theorem bijOn_conjEnd {A : Module.End D.carrier Mi} {p m : ℤ}
    (h : Set.BijOn A (S.weight.comp p) (S.weight.comp m)) :
    Set.BijOn (conjEnd S A) (S.weight.comp (-p)) (S.weight.comp (-m)) := by
  refine ⟨fun v hv => ?_, fun a ha b hb hab => ?_, fun u hu => ?_⟩
  · exact S.conj_comp _ _ (h.mapsTo (conj_comp' S hv))
  · rw [conjEnd_apply, conjEnd_apply] at hab
    exact conj_inj S (h.injOn (conj_comp' S ha) (conj_comp' S hb) (conj_inj S hab))
  · obtain ⟨w, hw, hwu⟩ := h.surjOn (conj_comp' S hu)
    refine ⟨S.conj w, S.conj_comp _ _ hw, ?_⟩
    rw [conjEnd_apply, S.conj_involutive, hwu, S.conj_involutive]

/-- `(A^c)^k = (A^k)^c`.  @census none (helper) -/
theorem conjEnd_pow (A : Module.End D.carrier Mi) :
    ∀ (k : ℕ), conjEnd S (A ^ k) = (conjEnd S A) ^ k
  | 0 => by
      refine LinearMap.ext fun v => ?_
      rw [pow_zero, pow_zero, conjEnd_apply, Module.End.one_apply, Module.End.one_apply,
        S.conj_involutive]
  | (k + 1) => by
      refine LinearMap.ext fun v => ?_
      rw [pow_succ, pow_succ, Module.End.mul_apply, conjEnd_apply, Module.End.mul_apply,
        ← conjEnd_pow A k, conjEnd_apply, conjEnd_apply, S.conj_involutive]

/-- Nilpotency travels along conjugation.  @census none (helper) -/
theorem isNilpotent_conjEnd {A : Module.End D.carrier Mi} (h : IsNilpotent A) :
    IsNilpotent (conjEnd S A) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_⟩
  rw [← conjEnd_pow A k, hk]
  refine LinearMap.ext fun v => ?_
  rw [conjEnd_apply]
  simp

/-- **The component-level prerequisites transfer to the `τ`-conjugate description.**  The
conjugate run's nilpotent is `n₀^c`: `c φ_-^c c φ_+^c = φ_- c φ_+ c` on `M_{-idxPlus}`, which is
`eq:nilpotency` on `M_{idxPlus}` with `c` applied to both sides.  @census none (helper) -/
theorem stab_prereq_of_conj (C : StabInput S)
    (hp : Set.BijOn C.phiPlus (S.weight.comp C.idxPlus) (S.weight.comp (-C.idxMinus)))
    (hm : Set.BijOn C.phiMinus (S.weight.comp C.idxMinus) (S.weight.comp (-C.idxPlus)))
    {n₀ : Module.End D.carrier Mi} (hnil : IsNilpotent n₀)
    (hmem : ∀ v ∈ S.weight.comp C.idxPlus, n₀ v ∈ S.weight.comp C.idxPlus)
    (hkey : ∀ v ∈ S.weight.comp C.idxPlus,
      S.conj (C.phiMinus (S.conj (C.phiPlus v))) = v + n₀ v) :
    HasInverse C.conj.phpT ∧ HasInverse C.conj.phmT ∧
      ∃ n : Module.End D.carrier (Wc S C.conj.idxPlus), IsNilpotent n ∧
        (twistConj galConj_mul_self C.conj.phmT).comp C.conj.phpT = 1 + n := by
  refine stab_prereq_of C.conj ?_ ?_ (isNilpotent_conjEnd hnil) (n₀ := conjEnd S n₀) ?_ ?_
  · exact bijOn_conjEnd hp
  · exact bijOn_conjEnd hm
  · intro v hv
    exact S.conj_comp _ _ (hmem _ (conj_comp' S hv))
  · intro v hv
    have hcv : S.conj v ∈ S.weight.comp C.idxPlus := conj_comp' S hv
    show S.conj (conjEnd S C.phiMinus (S.conj (conjEnd S C.phiPlus v))) = v + conjEnd S n₀ v
    rw [conjEnd_apply, conjEnd_apply, conjEnd_apply, S.conj_involutive, S.conj_involutive]
    have h2 := congrArg S.conj (hkey _ hcv)
    simp only [map_add, conj_conj] at h2
    exact h2

namespace StabInput

variable (C : StabInput S)

/-- `Ψ_k`, the junk inverse of `φ^{(k),τ}_-` appearing in the `(k+1)`-st plus-step, read as an
endomorphism of `M_{ℚ[√-1]}`.  @census none (helper) -/
noncomputable def seqInvPlus (k : ℕ) : Module.End D.carrier Mi :=
  toEnd S (linInv (twistConj galConj_mul_self (C.seqT k).2))

/-- `Ψ̃_k`, the junk inverse of `φ^{(k),τ}_+` appearing in the `(k+1)`-st minus-step.
@census none (helper) -/
noncomputable def seqInvMinus (k : ℕ) : Module.End D.carrier Mi :=
  toEnd S (linInv (twistConj galConj_mul_self (C.seqT k).1))

theorem seqInvPlus_mem (k : ℕ) (v : Mi) : C.seqInvPlus k v ∈ S.weight.comp (-C.idxMinus) :=
  toEnd_mem S _ v

theorem seqInvMinus_mem (k : ℕ) (v : Mi) : C.seqInvMinus k v ∈ S.weight.comp (-C.idxPlus) :=
  toEnd_mem S _ v

/-- **The stabilization step on `M_{ℚ[√-1]}`, at every `k`, with no side condition**:
`φ^{(k+1)}_+ = ½(φ^{(k)}_+ + Ψ_k)`.  Unlike `seqPlus_one_apply` this needs no membership
hypothesis, because `toEnd` is additive and `ℚ[√-1]`-linear in the map.  @census none (helper) -/
theorem seqPlus_succ (k : ℕ) :
    C.seqPlus (k + 1) = ((2 : D.carrier)⁻¹) • (C.seqPlus k + C.seqInvPlus k) := by
  show toEnd S (C.seqT (k + 1)).1 = _
  have h : (C.seqT (k + 1)).1
      = half (two_ne_zero_of_base (K := E) two_ne_zero) •
        ((C.seqT k).1 + linInv (twistConj galConj_mul_self (C.seqT k).2)) := rfl
  rw [h, toEnd_smul, toEnd_add, half_eq]
  rfl

/-- `φ^{(k+1)}_- = ½(φ^{(k)}_- + Ψ̃_k)`.  @census none (helper) -/
theorem seqMinus_succ (k : ℕ) :
    C.seqMinus (k + 1) = ((2 : D.carrier)⁻¹) • (C.seqMinus k + C.seqInvMinus k) := by
  show toEnd S (C.seqT (k + 1)).2 = _
  have h : (C.seqT (k + 1)).2
      = half (two_ne_zero_of_base (K := E) two_ne_zero) •
        ((C.seqT k).2 + linInv (twistConj galConj_mul_self (C.seqT k).1)) := rfl
  rw [h, toEnd_smul, toEnd_add, half_eq]
  rfl

/-- `Ψ_k` is a right inverse of `c ∘ φ^{(k)}_- ∘ c` on `M_{idxPlus}`.  @census none (helper) -/
theorem seqInvPlus_right (k : ℕ) (h : HasInverse (twistConj galConj_mul_self (C.seqT k).2)) :
    ∀ v ∈ S.weight.comp C.idxPlus, S.conj (C.seqMinus k (S.conj (C.seqInvPlus k v))) = v := by
  refine conj_toEnd_conj_toEnd' (linInv (twistConj galConj_mul_self (C.seqT k).2))
    (C.seqT k).2 ?_
  rw [Module.End.one_eq_id]
  exact h.comp_linInv

/-- `Ψ_k` is a left inverse of `c ∘ φ^{(k)}_- ∘ c` on `M_{-idxMinus}` (stated on `M_{idxMinus}`).
@census none (helper) -/
theorem seqInvPlus_left (k : ℕ) (h : HasInverse (C.seqT k).2) :
    ∀ v ∈ S.weight.comp C.idxMinus, S.conj (C.seqInvPlus k (S.conj (C.seqMinus k v))) = v := by
  refine conj_toEnd_conj_toEnd' (C.seqT k).2
    (linInv (twistConj galConj_mul_self (C.seqT k).2)) ?_
  rw [twistConj_linInv_twistConj galConj_mul_self (C.seqT k).2 h, Module.End.one_eq_id]
  exact h.linInv_comp

/-- `Ψ̃_k` is a right inverse of `c ∘ φ^{(k)}_+ ∘ c` on `M_{idxMinus}`.  @census none (helper) -/
theorem seqInvMinus_right (k : ℕ) (h : HasInverse (twistConj galConj_mul_self (C.seqT k).1)) :
    ∀ v ∈ S.weight.comp C.idxMinus, S.conj (C.seqPlus k (S.conj (C.seqInvMinus k v))) = v := by
  refine conj_toEnd_conj_toEnd' (linInv (twistConj galConj_mul_self (C.seqT k).1))
    (C.seqT k).1 ?_
  rw [Module.End.one_eq_id]
  exact h.comp_linInv

/-- `Ψ̃_k` is a left inverse of `c ∘ φ^{(k)}_+ ∘ c`.  @census none (helper) -/
theorem seqInvMinus_left (k : ℕ) (h : HasInverse (C.seqT k).1) :
    ∀ v ∈ S.weight.comp C.idxPlus, S.conj (C.seqInvMinus k (S.conj (C.seqPlus k v))) = v := by
  refine conj_toEnd_conj_toEnd' (C.seqT k).1
    (linInv (twistConj galConj_mul_self (C.seqT k).1)) ?_
  rw [twistConj_linInv_twistConj galConj_mul_self (C.seqT k).1 h, Module.End.one_eq_id]
  exact h.linInv_comp

/-- Every iterate, and every conjugated iterate, is invertible — S6's
`stabilizationSeq_invariant` at this input.  @census none (helper) -/
theorem hasInverse_seqT (hp : HasInverse C.phpT) (hm : HasInverse C.phmT)
    {n : Module.End D.carrier (Wc S C.idxPlus)} (hnil : IsNilpotent n)
    (hn : (twistConj galConj_mul_self C.phmT).comp C.phpT = 1 + n) (k : ℕ) :
    HasInverse (C.seqT k).1 ∧ HasInverse (twistConj galConj_mul_self (C.seqT k).2) := by
  obtain ⟨e, he⟩ := hnil
  have hmT : HasInverse (twistConj galConj_mul_self C.phmT) := hm.twistConj _
  obtain ⟨h1, h2, -⟩ := stabilizationSeq_invariant two_ne_zero galConj_mul_self
    C.phpT C.phmT hp hmT n e hn he k
  exact ⟨h1, h2⟩

end StabInput

/-- **Uniqueness of a two-sided component inverse, under conjugation.**  If `Ψ` is a right inverse
of `c ∘ B ∘ c` on `M_p`, `Ψ'` a left inverse of `c ∘ B' ∘ c` on `M_{-m}`, and `B' = c ∘ B ∘ c` on
`M_{-m}`, then `Ψ' = c ∘ Ψ ∘ c` on `M_{-p}`.  This is `conj_yStarInv_conj`'s argument at a general
step of the recursion.  @census none (helper) -/
theorem conj_inv_unique {p m : ℤ} {B B' Ψ Ψ' : Module.End D.carrier Mi}
    (hΨmem : ∀ v, Ψ v ∈ S.weight.comp (-m))
    (hR : ∀ v ∈ S.weight.comp p, S.conj (B (S.conj (Ψ v))) = v)
    (hL' : ∀ v ∈ S.weight.comp (-m), S.conj (Ψ' (S.conj (B' v))) = v)
    (hBB' : ∀ w ∈ S.weight.comp (-m), S.conj (B (S.conj w)) = B' w) :
    ∀ v ∈ S.weight.comp (-p), S.conj (Ψ (S.conj v)) = Ψ' v := by
  intro v hv
  have hcv : S.conj v ∈ S.weight.comp p := conj_comp' S hv
  have hSX : S.conj (S.conj (Ψ (S.conj v))) ∈ S.weight.comp (-m) := by
    rw [conj_conj]; exact hΨmem _
  have key : S.conj (B' (S.conj (S.conj (Ψ (S.conj v))))) = v := by
    rw [← hBB' _ hSX, conj_conj, conj_conj]
    have h2 := congrArg S.conj (hR _ hcv)
    rw [conj_conj, conj_conj] at h2
    exact h2
  have h3 := hL' _ hSX
  rw [key] at h3
  exact (conj_inj S h3).symm

namespace StabInput

/-- **The `τ`-conjugate run's iterates are the conjugates of the run's iterates**, at every `k`.
The induction of `DESIGN-NOTES.md` §10.3's route 2: the base case is the definition of
`StabInput.conj`, and the step is `seqPlus_succ` plus `conj_inv_unique`, the inverse laws being
`seqInv*_right`/`_left` fed by `hasInverse_seqT`.  @census none (helper) -/
theorem conj_seq (C : StabInput S) (hp : HasInverse C.phpT) (hm : HasInverse C.phmT)
    {n : Module.End D.carrier (Wc S C.idxPlus)} (hnil : IsNilpotent n)
    (hn : (twistConj galConj_mul_self C.phmT).comp C.phpT = 1 + n)
    (hp' : HasInverse C.conj.phpT) (hm' : HasInverse C.conj.phmT)
    {n' : Module.End D.carrier (Wc S C.conj.idxPlus)} (hnil' : IsNilpotent n')
    (hn' : (twistConj galConj_mul_self C.conj.phmT).comp C.conj.phpT = 1 + n') :
    ∀ k,
      (∀ v ∈ S.weight.comp (-C.idxPlus), S.conj (C.seqPlus k (S.conj v)) = C.conj.seqPlus k v) ∧
      (∀ v ∈ S.weight.comp (-C.idxMinus),
        S.conj (C.seqMinus k (S.conj v)) = C.conj.seqMinus k v) := by
  have hfix : D.conj ((2 : D.carrier)⁻¹) = ((2 : D.carrier)⁻¹) := by
    rw [map_inv₀, GF.conj_ofNat]
  intro k
  induction k with
  | zero =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [C.seqPlus_zero_apply _ (conj_comp' S hv), C.conj.seqPlus_zero_apply v hv]
      rfl
    · rw [C.seqMinus_zero_apply _ (conj_comp' S hv), C.conj.seqMinus_zero_apply v hv]
      rfl
  | succ k ih =>
    obtain ⟨h1, h2⟩ := C.hasInverse_seqT hp hm hnil hn k
    obtain ⟨h1', h2'⟩ := C.conj.hasInverse_seqT hp' hm' hnil' hn' k
    have hinvP : ∀ v ∈ S.weight.comp (-C.idxPlus),
        S.conj (C.seqInvPlus k (S.conj v)) = C.conj.seqInvPlus k v :=
      conj_inv_unique (C.seqInvPlus_mem k) (C.seqInvPlus_right k h2)
        (C.conj.seqInvPlus_left k (hasInverse_of_twistConj _ h2')) ih.2
    have hinvM : ∀ v ∈ S.weight.comp (-C.idxMinus),
        S.conj (C.seqInvMinus k (S.conj v)) = C.conj.seqInvMinus k v :=
      conj_inv_unique (C.seqInvMinus_mem k) (C.seqInvMinus_right k (h1.twistConj _))
        (C.conj.seqInvMinus_left k h1') ih.1
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [C.seqPlus_succ, C.conj.seqPlus_succ, LinearMap.smul_apply, LinearMap.smul_apply,
        LinearMap.add_apply, LinearMap.add_apply, S.conj_smul_fixed hfix, map_add,
        ih.1 v hv, hinvP v hv]
    · rw [C.seqMinus_succ, C.conj.seqMinus_succ, LinearMap.smul_apply, LinearMap.smul_apply,
        LinearMap.add_apply, LinearMap.add_apply, S.conj_smul_fixed hfix, map_add,
        ih.2 v hv, hinvM v hv]

end StabInput

/-- **`RQ-5.04-C8`, the `(⋆)` half** — the limit of the `τ`-conjugate `(⋆)` run is the conjugate
of the `(⋆)` run's limit.  Both runs stabilize (`stab_limit_spec`), so both limits are the
iterate at `max eC eD`, where `conj_seq` compares them.  @census none (helper) -/
theorem conjStar_limit (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ) :
    ∀ v ∈ S.weight.comp ((ℓ : ℤ) - 1),
      S.conj ((inputStar S hℓ).limPlus (S.conj v)) = (inputStar S hℓ).conj.limPlus v := by
  obtain ⟨-, hcX⟩ := conj_symmetry S hℓ
  obtain ⟨hnst, -, hYsXs⟩ := HC.WeightData.xStar_yStar_relations S.weight S.gic hℓ
  have hmemS : ∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)),
      ((HC.WeightData.gammaStar D.carrier ℓ ^ 2)⁻¹ • S.weight.normRemainder ℓ) v
        ∈ S.weight.comp (-((ℓ : ℤ) - 1)) := fun v hv =>
    Submodule.smul_mem _ _ (S.weight.normRemainder_mem_comp _ v hv)
  have hbij : Set.BijOn (Split.xStar S.toQiSetup) (S.weight.comp (-((ℓ : ℤ) - 1)))
      (S.weight.comp (-(-((ℓ : ℤ) - 1)))) := by rw [neg_neg]; exact bijOn_xStar hℓ
  have hkey : ∀ v ∈ S.weight.comp (inputStar S hℓ).idxPlus,
      S.conj ((inputStar S hℓ).phiMinus (S.conj ((inputStar S hℓ).phiPlus v)))
        = v + ((HC.WeightData.gammaStar D.carrier ℓ ^ 2)⁻¹ • S.weight.normRemainder ℓ) v := by
    intro v hv
    show S.conj (Split.xStar S.toQiSetup (S.conj (Split.xStar S.toQiSetup v))) = _
    rw [hcX (Split.xStar S.toQiSetup v)]
    exact hYsXs v hv
  obtain ⟨hpC, hmC, nC, hnilC, hnC⟩ := stab_prereq S hℓ (inputStar S hℓ) (by simp)
  obtain ⟨hpD, hmD, nD, hnilD, hnD⟩ :=
    stab_prereq_of_conj (inputStar S hℓ) hbij hbij hnst hmemS hkey
  obtain ⟨eC, hconstC, hlimC, -, -, -, -⟩ := stab_limit_spec (inputStar S hℓ) hpC hmC hnilC hnC
  obtain ⟨eD, hconstD, hlimD, -, -, -, -⟩ :=
    stab_limit_spec (inputStar S hℓ).conj hpD hmD hnilD hnD
  have hC : (inputStar S hℓ).limPlus = (inputStar S hℓ).seqPlus (max eC eD) := by
    show toEnd S _ = toEnd S _
    rw [hlimC, ← hconstC _ (le_max_left _ _)]
  have hD : (inputStar S hℓ).conj.limPlus = (inputStar S hℓ).conj.seqPlus (max eC eD) := by
    show toEnd S _ = toEnd S _
    rw [hlimD, ← hconstD _ (le_max_right _ _)]
  intro v hv
  rw [hC, hD]
  refine ((inputStar S hℓ).conj_seq hpC hmC hnilC hnC hpD hmD hnilD hnD (max eC eD)).1 v ?_
  show v ∈ S.weight.comp (-(-((ℓ : ℤ) - 1)))
  rwa [neg_neg]

end ConjRun

/-! ### `RQ-5.05-C3` — `eq:limitdiagram`, by induction on the recursion

The source proves `eq:limitdiagram` "by induction, as in the case of the first iteration
`eq:firstiteration`".  That is what happens here: `DiagSq` names the four squares of
`eq:normalizedcomparison` for an arbitrary triple of verticals, `diagSq_seq` runs the induction
(base case the three normalized squares `sq_front_left`/`sq_back_left`/`sq_back_right`; step
`DiagSq.inv` — the same four squares for the junk inverses `Ψ_k` — plus linearity of
`φ^{(k+1)} = ½(φ^{(k)} + Ψ_k)`), and `limit_diagram` evaluates it past both nilpotency exponents.

`DiagSq.inv` is where the content is, and it is the general-`k` form of the four extra lemmas
`eq:firstiteration` needed at `k = 0` (`tPlusInv_X_xStar`, `yStarInv_xStarInv_Y`,
`yStar_yStarInv`, and the trivial one): each inverse square is one **map** square read through
`c`, squares 1 and 4 exchanging and squares 2 and 3 exchanging, using `cX = Yc`, `cY = Xc`,
`cY⋆ = X⋆c`, `cY⋆⁻¹ = X⋆⁻¹c` and a two-sided inverse law. -/

section LimitDiagram

variable {S : RationalSetupOver ℓ E D Mq Mi}

/-- `c ∘ Y⋆ = X⋆ ∘ c`.  @census none (helper) -/
theorem conj_yStar (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ) (w : Mi) :
    S.conj (Split.yStar S.toQiSetup w) = Split.xStar S.toQiSetup (S.conj w) :=
  (xStar_conj_apply S hℓ w).symm

/-- `c ∘ Y⋆⁻¹ = X⋆⁻¹ ∘ c` on `M_{-(ℓ-1)}`.  @census none (helper) -/
theorem conj_yStarInv (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup) (hℓ : 1 ≤ ℓ)
    {w : Mi} (hw : w ∈ S.weight.comp (-((ℓ : ℤ) - 1))) :
    S.conj (I.yStarInv w) = I.xStarInv (S.conj w) := by
  have hcw : S.conj w ∈ S.weight.comp ((ℓ : ℤ) - 1) := conj_comp' S hw
  have h := conj_yStarInv_conj S I hℓ _ hcw
  rwa [conj_conj] at h

/-- **The four squares of `eq:normalizedcomparison`** with the verticals `(N, A, P)` — the shape
`eq:firstiteration` and `eq:limitdiagram` share with the normalized display.
@census none (helper) -/
def DiagSq (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup)
    (N A P : Module.End D.carrier Mi) : Prop :=
  (∀ v ∈ S.weight.comp (-((ℓ : ℤ) + 1)),
      A (S.weight.X v) = I.yStarInv (S.weight.X (N v))) ∧
  (∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)),
      P (S.weight.X (Split.xStar S.toQiSetup v)) = S.weight.X (A v)) ∧
  (∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)),
      N (S.weight.Y v) = S.weight.Y (Split.yStar S.toQiSetup (A v))) ∧
  (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1),
      A (I.xStarInv (S.weight.Y v)) = S.weight.Y (P v))

theorem DiagSq.add {I : Split.StarInverses S.toQiSetup} {N A P N' A' P' : Module.End D.carrier Mi}
    (h : DiagSq S I N A P) (h' : DiagSq S I N' A' P') :
    DiagSq S I (N + N') (A + A') (P + P') := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h1', h2', h3', h4'⟩ := h'
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [LinearMap.add_apply, h1 v hv, h1' v hv, LinearMap.add_apply, map_add, map_add]
  · rw [LinearMap.add_apply, h2 v hv, h2' v hv, LinearMap.add_apply, map_add]
  · rw [LinearMap.add_apply, h3 v hv, h3' v hv, LinearMap.add_apply, map_add, map_add]
  · rw [LinearMap.add_apply, h4 v hv, h4' v hv, LinearMap.add_apply, map_add]

theorem DiagSq.smul {I : Split.StarInverses S.toQiSetup} {N A P : Module.End D.carrier Mi}
    (c : D.carrier) (h : DiagSq S I N A P) : DiagSq S I (c • N) (c • A) (c • P) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · rw [LinearMap.smul_apply, h1 v hv, LinearMap.smul_apply, map_smul, map_smul]
  · rw [LinearMap.smul_apply, h2 v hv, LinearMap.smul_apply, map_smul]
  · rw [LinearMap.smul_apply, h3 v hv, LinearMap.smul_apply, map_smul, map_smul]
  · rw [LinearMap.smul_apply, h4 v hv, LinearMap.smul_apply, map_smul]

/-- **The four squares for the inverses**, from the four squares for the maps.  Each inverse
square is one map square read through `c`, using `c X = Y c`, `c Y = X c`, `c Y⋆ = X⋆ c` and
`c Y⋆⁻¹ = X⋆⁻¹ c`, and then a two-sided inverse law: squares 1 and 4 exchange, as do 2 and 3.
@census none (helper) -/
theorem DiagSq.inv (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup) (hℓ : 1 ≤ ℓ)
    {N A P NI AI PI : Module.End D.carrier Mi}
    (hsq : DiagSq S I N A P)
    (hNmem : ∀ v ∈ S.weight.comp (-((ℓ : ℤ) + 1)), N v ∈ S.weight.comp (-((ℓ : ℤ) + 1)))
    (hAImem : ∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)), AI v ∈ S.weight.comp ((ℓ : ℤ) - 1))
    (hNImem : ∀ v ∈ S.weight.comp (-((ℓ : ℤ) + 1)), NI v ∈ S.weight.comp (-((ℓ : ℤ) + 1)))
    (hPImem : ∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), PI v ∈ S.weight.comp ((ℓ : ℤ) + 1))
    (hA1 : ∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)), S.conj (A (S.conj (AI v))) = v)
    (hA2 : ∀ w ∈ S.weight.comp ((ℓ : ℤ) - 1), AI (S.conj (A (S.conj w))) = w)
    (hN1 : ∀ v ∈ S.weight.comp (-((ℓ : ℤ) + 1)), S.conj (P (S.conj (NI v))) = v)
    (hN2 : ∀ w ∈ S.weight.comp (-((ℓ : ℤ) + 1)), NI (S.conj (P (S.conj w))) = w)
    (hP1 : ∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), S.conj (N (S.conj (PI v))) = v)
    (hP2 : ∀ w ∈ S.weight.comp ((ℓ : ℤ) + 1), PI (S.conj (N (S.conj w))) = w) :
    DiagSq S I NI AI PI := by
  obtain ⟨h1, h2, h3, h4⟩ := hsq
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · -- square 1, from square 4
    have hu : NI v ∈ S.weight.comp (-((ℓ : ℤ) + 1)) := hNImem v hv
    have hXu : S.weight.X (NI v) ∈ S.weight.comp (-((ℓ : ℤ) - 1)) :=
      Split.x_mem (Q := S.toQiSetup) (m := -((ℓ : ℤ) + 1)) (by ring) hu
    have hmem : I.yStarInv (S.weight.X (NI v)) ∈ S.weight.comp ((ℓ : ℤ) - 1) :=
      I.yStarInv_mem hXu
    have hcu : S.conj (NI v) ∈ S.weight.comp ((ℓ : ℤ) + 1) := conj_comp' S hu
    have key : S.conj (A (S.conj (I.yStarInv (S.weight.X (NI v))))) = S.weight.X v := by
      rw [conj_yStarInv S I hℓ hXu, S.conj_X, h4 _ hcu, S.conj_Y, hN1 v hv]
    rw [← key, hA2 _ hmem]
  · -- square 2, from square 3
    have hAI : AI v ∈ S.weight.comp ((ℓ : ℤ) - 1) := hAImem v hv
    have hmem : S.weight.X (AI v) ∈ S.weight.comp ((ℓ : ℤ) + 1) :=
      Split.x_mem (Q := S.toQiSetup) (m := (ℓ : ℤ) - 1) (by ring) hAI
    have hcAI : S.conj (AI v) ∈ S.weight.comp (-((ℓ : ℤ) - 1)) := S.conj_comp _ _ hAI
    have key : S.conj (N (S.conj (S.weight.X (AI v)))) = S.weight.X (Split.xStar S.toQiSetup v) := by
      rw [S.conj_X, h3 _ hcAI, S.conj_Y, conj_yStar S hℓ, hA1 v hv]
    rw [← key, hP2 _ hmem]
  · -- square 3, from square 2
    have hAI : AI v ∈ S.weight.comp ((ℓ : ℤ) - 1) := hAImem v hv
    have hyAI : Split.yStar S.toQiSetup (AI v) ∈ S.weight.comp (-((ℓ : ℤ) - 1)) :=
      Split.yStar_mem (Q := S.toQiSetup) (m := (ℓ : ℤ) - 1) (by ring) hℓ hAI
    have hmem : S.weight.Y (Split.yStar S.toQiSetup (AI v)) ∈ S.weight.comp (-((ℓ : ℤ) + 1)) :=
      Split.y_mem (Q := S.toQiSetup) (m := -((ℓ : ℤ) - 1)) (by ring) hyAI
    have hcAI : S.conj (AI v) ∈ S.weight.comp (-((ℓ : ℤ) - 1)) := S.conj_comp _ _ hAI
    have key : S.conj (P (S.conj (S.weight.Y (Split.yStar S.toQiSetup (AI v))))) = S.weight.Y v := by
      rw [S.conj_Y, conj_yStar S hℓ, h2 _ hcAI, S.conj_X, hA1 v hv]
    rw [← key, hN2 _ hmem]
  · -- square 4, from square 1
    have hPI : PI v ∈ S.weight.comp ((ℓ : ℤ) + 1) := hPImem v hv
    have hmem : S.weight.Y (PI v) ∈ S.weight.comp ((ℓ : ℤ) - 1) :=
      Split.y_mem (Q := S.toQiSetup) (m := (ℓ : ℤ) + 1) (by ring) hPI
    have hcPI : S.conj (PI v) ∈ S.weight.comp (-((ℓ : ℤ) + 1)) := S.conj_comp _ _ hPI
    have hXN : S.weight.X (N (S.conj (PI v))) ∈ S.weight.comp (-((ℓ : ℤ) - 1)) :=
      Split.x_mem (Q := S.toQiSetup) (m := -((ℓ : ℤ) + 1)) (by ring) (hNmem _ hcPI)
    have key : S.conj (A (S.conj (S.weight.Y (PI v)))) = I.xStarInv (S.weight.Y v) := by
      rw [S.conj_Y, h1 _ hcPI, conj_yStarInv S I hℓ hXN, S.conj_X, hP1 v hv]
    rw [← key, hA2 _ hmem]

namespace StabInput

/-- `seqInvPlus_left`, in the form `Ψ_k ∘ (c φ^{(k)}_- c) = 𝟏` on `M_{-idxMinus}`.
@census none (helper) -/
theorem seqInvPlus_left' (C : StabInput S) (k : ℕ) (h : HasInverse (C.seqT k).2) :
    ∀ w ∈ S.weight.comp (-C.idxMinus),
      C.seqInvPlus k (S.conj (C.seqMinus k (S.conj w))) = w := fun _ hw =>
  conj_inj S (C.seqInvPlus_left k h _ (conj_comp' S hw))

/-- `seqInvMinus_left`, in the form `Ψ̃_k ∘ (c φ^{(k)}_+ c) = 𝟏` on `M_{-idxPlus}`.
@census none (helper) -/
theorem seqInvMinus_left' (C : StabInput S) (k : ℕ) (h : HasInverse (C.seqT k).1) :
    ∀ w ∈ S.weight.comp (-C.idxPlus),
      C.seqInvMinus k (S.conj (C.seqPlus k (S.conj w))) = w := fun _ hw =>
  conj_inj S (C.seqInvMinus_left k h _ (conj_comp' S hw))

end StabInput

/-- The `(⋆)` run's two iterates coincide, read on `M_{ℚ[√-1]}`.  @census none (helper) -/
theorem inputStar_seqMinus (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ) (k : ℕ) :
    (inputStar S hℓ).seqMinus k = (inputStar S hℓ).seqPlus k := by
  exact congrArg (toEnd S) (seqT_star_fst_eq_snd S hℓ k).symm

/-- The normalized comparison diagram `eq:normalizedcomparison` with the verticals `φ^{(0)}`
(Step O-7a): the base case of the iteration.  @census none (helper) -/
theorem diagSq_zero (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup) (hℓ : 1 ≤ ℓ) :
    DiagSq S I ((inputPlus S).seqMinus 0) ((inputStar S hℓ).seqPlus 0) ((inputPlus S).seqPlus 0) := by
  refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · have hXv : S.weight.X v ∈ S.weight.comp (-((ℓ : ℤ) - 1)) :=
      Split.x_mem (Q := S.toQiSetup) (m := -((ℓ : ℤ) + 1)) (by ring) hv
    rw [(inputStar S hℓ).seqPlus_zero_apply _ hXv, (inputPlus S).seqMinus_zero_apply _ hv]
    exact Split.sq_front_left S.toQiSetup I hℓ v hv
  · have hXx : S.weight.X (Split.xStar S.toQiSetup v) ∈ S.weight.comp ((ℓ : ℤ) + 1) :=
      Split.x_mem (Q := S.toQiSetup) (m := (ℓ : ℤ) - 1) (by ring)
        (Split.xStar_mem (Q := S.toQiSetup) (by ring) hℓ hv)
    rw [(inputPlus S).seqPlus_zero_apply _ hXx, (inputStar S hℓ).seqPlus_zero_apply _ hv]
    rfl
  · have hYv : S.weight.Y v ∈ S.weight.comp (-((ℓ : ℤ) + 1)) :=
      Split.y_mem (Q := S.toQiSetup) (m := -((ℓ : ℤ) - 1)) (by ring) hv
    rw [(inputPlus S).seqMinus_zero_apply _ hYv, (inputStar S hℓ).seqPlus_zero_apply _ hv]
    exact Split.sq_back_left S.toQiSetup hℓ v hv
  · have hYv : S.weight.Y v ∈ S.weight.comp ((ℓ : ℤ) - 1) :=
      Split.y_mem (Q := S.toQiSetup) (m := (ℓ : ℤ) + 1) (by ring) hv
    have hxi : I.xStarInv (S.weight.Y v) ∈ S.weight.comp (-((ℓ : ℤ) - 1)) := I.xStarInv_mem hYv
    rw [(inputStar S hℓ).seqPlus_zero_apply _ hxi, (inputPlus S).seqPlus_zero_apply _ hv]
    exact Split.sq_back_right S.toQiSetup I v hv

/-- **The averaging step** (`eq:firstiteration`'s argument, Step O-10; the induction step of
`eq:limitdiagram`, Step O-14): if the diagram with verticals `φ^{(k)}` commutes, so does the one
with `φ^{(k+1)} = ½(φ^{(k)} + (φ^{(k),c})^{-1})`: the inverses' squares (`DiagSq.inv`), their sum
(`DiagSq.add`) and the factor `½` (`DiagSq.smul`).  @census none (helper) -/
theorem DiagSq.step (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup) (hℓ : 1 ≤ ℓ)
    (k : ℕ) (ih : DiagSq S I ((inputPlus S).seqMinus k) ((inputStar S hℓ).seqPlus k)
      ((inputPlus S).seqPlus k)) :
    DiagSq S I ((inputPlus S).seqMinus (k + 1)) ((inputStar S hℓ).seqPlus (k + 1))
      ((inputPlus S).seqPlus (k + 1)) := by
  obtain ⟨hpP, hmP, nP, hnilP, hnP⟩ := stab_prereq S hℓ (inputPlus S) (by simp)
  obtain ⟨hpS, hmS, nS, hnilS, hnS⟩ := stab_prereq S hℓ (inputStar S hℓ) (by simp)
  obtain ⟨h1P, h2P⟩ := (inputPlus S).hasInverse_seqT hpP hmP hnilP hnP k
  obtain ⟨h1S, h2S⟩ := (inputStar S hℓ).hasInverse_seqT hpS hmS hnilS hnS k
  have hAA := inputStar_seqMinus S hℓ k
  have hinv : DiagSq S I ((inputPlus S).seqInvMinus k) ((inputStar S hℓ).seqInvPlus k)
      ((inputPlus S).seqInvPlus k) := by
    refine DiagSq.inv S I hℓ ih (fun v _ => (inputPlus S).seqMinus_mem k v)
      (fun v _ => ?_) (fun v _ => (inputPlus S).seqInvMinus_mem k v) (fun v _ => ?_)
      ?_ ?_ ?_ ?_ ?_ ?_
    · have h := (inputStar S hℓ).seqInvPlus_mem k v
      rwa [show -(inputStar S hℓ).idxMinus = (ℓ : ℤ) - 1 by simp [inputStar]] at h
    · have h := (inputPlus S).seqInvPlus_mem k v
      rwa [show -(inputPlus S).idxMinus = (ℓ : ℤ) + 1 by simp [inputPlus]] at h
    · intro v hv
      have h := (inputStar S hℓ).seqInvPlus_right k h2S v hv
      rwa [hAA] at h
    · intro w hw
      have h := (inputStar S hℓ).seqInvPlus_left' k (hasInverse_of_twistConj _ h2S) w
        (by rwa [show -(inputStar S hℓ).idxMinus = (ℓ : ℤ) - 1 by simp [inputStar]])
      rwa [hAA] at h
    · exact (inputPlus S).seqInvMinus_right k (h1P.twistConj _)
    · exact (inputPlus S).seqInvMinus_left' k h1P
    · exact (inputPlus S).seqInvPlus_right k h2P
    · intro w hw
      exact (inputPlus S).seqInvPlus_left' k (hasInverse_of_twistConj _ h2P) w
        (by rwa [show -(inputPlus S).idxMinus = (ℓ : ℤ) + 1 by simp [inputPlus]])
  rw [(inputPlus S).seqMinus_succ, (inputStar S hℓ).seqPlus_succ, (inputPlus S).seqPlus_succ]
  exact (ih.add hinv).smul _

/-- **`RQ-5.04-C4`/`C5`/`C6`** — the first iteration.

`C4`: the step-1 iterates of the three runs are the four displayed maps — `φ^{(1)}_{+,+} =
½(𝟏 + T₊⁻¹)` on `M_{ℓ+1}`, `φ^{(1)}_{+,-} = ½(T₋ + 𝟏)` on `M_{-(ℓ+1)}`, `φ^{(1)}_{⋆,+} =
½(X⋆ + Y⋆⁻¹)` on `M_{-(ℓ-1)}`, and the `(−)` run's iterates are the transposes; `T₊⁻¹` is any
two-sided inverse of `T₊` on `M_{ℓ+1}` (pinned by `htPlusInv`), `Y⋆⁻¹`, `X⋆⁻¹` are
`StarInverses`' (`RQ-5.01-H3`).  These are genuine identities — S6's step is
`½(φ₊ + linInv(φ₋^τ))`, and the content is `T₋^τ = T₊`, `X⋆^τ = Y⋆` (`C3`) plus the agreement of
the junk-valued `linInv` with the named inverses.
`C5`: the relations licensing `φ^{(1)}_± := φ^{(1)}_{±,+}`, `φ^{(1)}_⋆ := φ^{(1)}_{⋆,+}` — for `(±)`
the transposition identities, which is what the source has printed since 2026-09-11 (module
docstring, note (2)); for `(⋆)` that the displayed
`φ^{(1)}_{⋆,-} = ½(Y⋆ + X⋆⁻¹)` is the conjugate of `φ^{(1)}_{⋆,+}`, i.e. the first iterate of the
`τ`-conjugate `(⋆)` run.
`C6`: `eq:firstiteration` — `eq:normalizedcomparison` with the verticals replaced by
`φ^{(1)}_-`, `φ^{(1)}_⋆`, `φ^{(1)}_+` — commutes.

@census    none (auxiliary; discharges census clauses `RQ-5.04-C4`, `RQ-5.04-C5`, `RQ-5.04-C6`)
@source    eq:firstiteration
@clauses   RQ2-5.04-C4, RQ2-5.04-C5, RQ2-5.04-C6,
           RQ2-5.04-S-O10
@imports   none
**`AN-39` RETIRED, 2026-09-11 — clause `C5`'s `(±)` half is no longer a reformulation.**  Until the
paper author's ruling of that date the source printed `φ^{(1),c}_{+,±} = φ^{(1)}_{-,±}`, false for
the `(±)` runs: the `(−)` item is the transpose of the `(+)` item, so the relation read
`c ∘ φ^{(1)}_{+,+} ∘ c = φ^{(1)}_{+,-}`, i.e. `½(𝟏 + T₋⁻¹) = ½(T₋ + 𝟏)` on `M_{-(ℓ+1)}`, which
fails whenever `n₋ ≠ 0` (and at `k = 0` read `𝟏 = T₋`); the index-corrected reading compared maps on
different components.  This declaration rendered the transposition identity
`φ^{(1)}_{-,±} = φ^{(1)}_{+,∓}` (`rmk:unipotentstabilization`) instead, under a disclosed
`JUSTIFIED_REFORMULATION`.  The author accepted the resolution dossier's §3 diff (no fork), the
`latex/` edit landed at `388f0f8`, and census r14 (tag `census-v1.11`) re-transcribed `RQ-5.04-C5`
to exactly that identity plus `φ^{(1)}_{⋆,-} = φ^{(1),c}_{⋆,+}` by construction — which is what is
stated below.  **The tree and the source now agree**, and only the generalisation disclosure
survives.

@divergence (T3, AI-R-V2-3 / O-10) `C6` is proved by the averaging step `DiagSq.step` from the
normalized diagram (`diagSq_zero`), as in the tex, and `diagSq_seq` takes its `k = 1` case from this
theorem, so the first iteration is on the main line's proof path.   JUSTIFIED_REFORMULATION (stated for a bare `RationalSetup`, not `Gelfand.HCQObj`
(`RQ-5.05`'s own category) — a **true generalization** (`CONVENTIONS.md` §3), unused by the proof;
2026-09-03, `R-S8-16`(c), `V-S8-D1-4`(b)). -/
theorem first_iteration (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup) (hℓ : 1 ≤ ℓ)
    (tPlusInv : Module.End D.carrier Mi)
    (htPlusInv : (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), tPlusInv v ∈ S.weight.comp ((ℓ : ℤ) + 1)) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), tPlusInv (Split.tPlus S.toQiSetup v) = v) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), Split.tPlus S.toQiSetup (tPlusInv v) = v)) :
    -- `C4`: the four displayed first-iteration maps
    ((∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1),
        (inputPlus S).seqPlus 1 v = ((2 : D.carrier)⁻¹) • (v + tPlusInv v)) ∧
      (∀ v ∈ S.weight.comp (-((ℓ : ℤ) + 1)),
        (inputPlus S).seqMinus 1 v = ((2 : D.carrier)⁻¹) • (Split.tMinus S.toQiSetup v + v)) ∧
      (∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)),
        (inputStar S hℓ).seqPlus 1 v
          = ((2 : D.carrier)⁻¹) • (Split.xStar S.toQiSetup v + I.yStarInv v)) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) - 1),
        (inputStar S hℓ).conj.seqPlus 1 v
          = ((2 : D.carrier)⁻¹) • (Split.yStar S.toQiSetup v + I.xStarInv v))) ∧
    -- `C5`: the relations that license `φ^{(1)}_±`, `φ^{(1)}_⋆`
    (((inputMinus S).seqPlus 1 = (inputPlus S).seqMinus 1 ∧
        (inputMinus S).seqMinus 1 = (inputPlus S).seqPlus 1) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) - 1),
        S.conj ((inputStar S hℓ).seqPlus 1 (S.conj v)) = (inputStar S hℓ).conj.seqPlus 1 v)) ∧
    -- `C6`: `eq:firstiteration` commutes — the four squares of `eq:normalizedcomparison` with the
    -- verticals `φ^{(1)}_-`, `φ^{(1)}_⋆`, `φ^{(1)}_+`
    ((∀ v ∈ S.weight.comp (-((ℓ : ℤ) + 1)),
        (inputStar S hℓ).seqPlus 1 (S.weight.X v)
          = I.yStarInv (S.weight.X ((inputPlus S).seqMinus 1 v))) ∧
      (∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)),
        (inputPlus S).seqPlus 1 (S.weight.X (Split.xStar S.toQiSetup v))
          = S.weight.X ((inputStar S hℓ).seqPlus 1 v)) ∧
      (∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)),
        (inputPlus S).seqMinus 1 (S.weight.Y v)
          = S.weight.Y (Split.yStar S.toQiSetup ((inputStar S hℓ).seqPlus 1 v))) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1),
        (inputStar S hℓ).seqPlus 1 (I.xStarInv (S.weight.Y v))
          = S.weight.Y ((inputPlus S).seqPlus 1 v))) := by
  refine ⟨⟨fun v hv => first_iter_plus S hℓ tPlusInv htPlusInv v hv,
      fun v hv => first_iter_minus S v hv,
      fun v hv => first_iter_star S I hℓ v hv,
      fun v hv => first_iter_starConj S I hℓ v hv⟩,
    ⟨⟨?_, ?_⟩, fun v hv => first_iter_C5_star S I hℓ v hv⟩,
    DiagSq.step S I hℓ 0 (diagSq_zero S I hℓ)⟩
  · show toEnd S ((inputMinus S).seqT 1).1 = toEnd S ((inputPlus S).seqT 1).2
    rw [seqT_minus]
    rfl
  · show toEnd S ((inputMinus S).seqT 1).2 = toEnd S ((inputPlus S).seqT 1).1
    rw [seqT_minus]
    rfl

/-- An inverse of `T₊` on `M_{ℓ+1}` as an endomorphism of `M` (restriction, inverted, composed with the
projection): the datum `first_iteration`'s `φ^{(1)}_{+,+}` formula needs.  @census none (helper) -/
theorem exists_tPlusInv (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ) :
    ∃ tPlusInv : Module.End D.carrier Mi,
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), tPlusInv v ∈ S.weight.comp ((ℓ : ℤ) + 1)) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), tPlusInv (Split.tPlus S.toQiSetup v) = v) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1), Split.tPlus S.toQiSetup (tPlusInv v) = v) := by
  obtain ⟨hb, -⟩ := HC.WeightData.Tplus_isUnit S.weight S.gic hℓ
  set W := S.weight.comp ((ℓ : ℤ) + 1)
  let T : W →ₗ[D.carrier] W := (Split.tPlus S.toQiSetup).restrict (fun v hv => hb.mapsTo hv)
  have hT : Function.Bijective T :=
    ⟨fun x y hxy => Subtype.ext (hb.injOn x.2 y.2 (congrArg Subtype.val hxy)),
     fun y => by obtain ⟨x, hx, hxy⟩ := hb.surjOn y.2; exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩
  let e := LinearEquiv.ofBijective T hT
  let pr : Mi →ₗ[D.carrier] W := LinearMap.codRestrict W (S.weight.proj ((ℓ : ℤ) + 1))
    (fun v => S.weight.proj_mem _ v)
  refine ⟨W.subtype ∘ₗ e.symm.toLinearMap ∘ₗ pr, fun v _ => (e.symm (pr v)).2, fun v hv => ?_,
    fun v hv => ?_⟩
  · have hTv : Split.tPlus S.toQiSetup v ∈ W := hb.mapsTo hv
    have : pr (Split.tPlus S.toQiSetup v) = T ⟨v, hv⟩ :=
      Subtype.ext (S.weight.proj_of_mem_same hTv)
    show ((e.symm (pr _)) : Mi) = v
    rw [this]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨v, hv⟩)
  · have : pr v = ⟨v, hv⟩ := Subtype.ext (S.weight.proj_of_mem_same hv)
    show (T (e.symm (pr v)) : Mi) = v
    rw [this]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)

/-- **The limit diagram's induction** (Step O-14): the diagram with verticals `φ^{(k)}` commutes for
every `k` — `k = 0` is `eq:normalizedcomparison` (`diagSq_zero`), `k = 1` is `eq:firstiteration`
(`first_iteration`, Step O-10), and the induction step is the averaging argument (`DiagSq.step`).
@census none (helper) -/
theorem diagSq_seq (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup) (hℓ : 1 ≤ ℓ) :
    ∀ k, DiagSq S I ((inputPlus S).seqMinus k) ((inputStar S hℓ).seqPlus k)
      ((inputPlus S).seqPlus k) := by
  obtain ⟨tPlusInv, htPlusInv⟩ := exists_tPlusInv S hℓ
  intro k
  induction k with
  | zero => exact diagSq_zero S I hℓ
  | succ k ih =>
    match k, ih with
    | 0, _ => exact (first_iteration S I hℓ tPlusInv htPlusInv).2.2
    | k + 1, ih => exact DiagSq.step S I hℓ (k + 1) ih

/-- **`RQ-5.05-C3`, `eq:limitdiagram`** — the normalized comparison diagram with the three
verticals replaced by the limits `φ^{(∞)}_-`, `φ^{(∞)}_⋆`, `φ^{(∞)}_+` commutes.  Both runs are
constant past their nilpotency exponents, so all three limits are the iterate at `max eP eS`,
where `diagSq_seq` compares them.  @census none (helper) -/
theorem limit_diagram (S : RationalSetupOver ℓ E D Mq Mi) (I : Split.StarInverses S.toQiSetup) (hℓ : 1 ≤ ℓ) :
    DiagSq S I ((inputMinus S).limPlus) ((inputStar S hℓ).limPlus) ((inputPlus S).limPlus) := by
  obtain ⟨hpP, hmP, nP, hnilP, hnP⟩ := stab_prereq S hℓ (inputPlus S) (by simp)
  obtain ⟨hpS, hmS, nS, hnilS, hnS⟩ := stab_prereq S hℓ (inputStar S hℓ) (by simp)
  obtain ⟨eP, hconstP, hlimP, -, -, -, -⟩ := stab_limit_spec (inputPlus S) hpP hmP hnilP hnP
  obtain ⟨eS, hconstS, hlimS, -, -, -, -⟩ := stab_limit_spec (inputStar S hℓ) hpS hmS hnilS hnS
  have hconstM : ∀ k, eP ≤ k → (inputMinus S).seqT k = (inputMinus S).seqT eP := by
    intro k hk; rw [seqT_minus, seqT_minus, hconstP k hk]
  have hlimM : (inputMinus S).limT = (inputMinus S).seqT eP := eventualValue_eq _ hconstM
  have hlimPk : (inputPlus S).limT = (inputPlus S).seqT (max eP eS) := by
    rw [hlimP, ← hconstP _ (le_max_left eP eS)]
  have hlimSk : (inputStar S hℓ).limT = (inputStar S hℓ).seqT (max eP eS) := by
    rw [hlimS, ← hconstS _ (le_max_right eP eS)]
  have hlimMk : (inputMinus S).limT = (inputMinus S).seqT (max eP eS) := by
    rw [hlimM, ← hconstM _ (le_max_left eP eS)]
  have hN : (inputMinus S).limPlus = (inputPlus S).seqMinus (max eP eS) := by
    show toEnd S ((inputMinus S).limT).1 = toEnd S ((inputPlus S).seqT (max eP eS)).2
    rw [hlimMk, seqT_minus]
    rfl
  have hA : (inputStar S hℓ).limPlus = (inputStar S hℓ).seqPlus (max eP eS) := by
    show toEnd S ((inputStar S hℓ).limT).1 = toEnd S ((inputStar S hℓ).seqT (max eP eS)).1
    rw [hlimSk]
  have hP : (inputPlus S).limPlus = (inputPlus S).seqPlus (max eP eS) := by
    show toEnd S ((inputPlus S).limT).1 = toEnd S ((inputPlus S).seqT (max eP eS)).1
    rw [hlimPk]
  rw [hN, hA, hP]
  exact diagSq_seq S I hℓ (max eP eS)

end LimitDiagram

/-! ### `RQ-5.05-C5` — the limits are natural in the module

The source: functoriality "follows inductively from the recursive process of unipotent
stabilization".  That induction is `seq_natural`, and its step is the same uniqueness argument
`conj_seq`'s is, in the form *`f` carries a two-sided component inverse to a two-sided component
inverse*.  Nothing here needs `f` to be invertible.

`toEnd_apply_proj` is the other half: a `toEnd`-transported map sees its argument only through the
projection onto the component it is supported on, so `HomSpec`'s `∀ m` (over the whole module)
reduces to the component statement `lim_natural` proves, by `WeightData.proj_comm_of_map`. -/

section Naturality

variable {Mq' : Type} [AddCommGroup Mq'] [Module E Mq']
variable {Mi' : Type} [AddCommGroup Mi'] [Module D.carrier Mi']
variable {S : RationalSetupOver ℓ E D Mq Mi} {T : RationalSetupOver ℓ E D Mq' Mi'}

/-- A `toEnd`-transported map depends on its argument only through the projection onto the
component it is supported on.  @census none (helper) -/
theorem toEnd_apply_proj {p m : ℤ} (F : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m)) (v : Mi) :
    toEnd S F v = toEnd S F (S.weight.proj p v) := by
  have h : projT S p (S.baseChange.symm v)
      = projT S p (S.baseChange.symm (S.weight.proj p v)) := by
    refine Subtype.ext ?_
    rw [projT_apply, projT_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      S.weight.proj_of_mem_same (S.weight.proj_mem p v)]
  rw [toEnd_apply, toEnd_apply, h]

/-- A map commuting with `H`, `X`, `Y` commutes with the Casimir.  @census none (helper) -/
theorem map_casimir (f : Mi →ₗ[D.carrier] Mi')
    (hH : ∀ v, f (S.weight.H v) = T.weight.H (f v))
    (hX : ∀ v, f (S.weight.X v) = T.weight.X (f v))
    (hY : ∀ v, f (S.weight.Y v) = T.weight.Y (f v)) (v : Mi) :
    f (S.weight.casimir v) = T.weight.casimir (f v) := by
  rw [S.weight.casimir_apply, T.weight.casimir_apply, map_add, map_add, map_sub, map_smul,
    map_smul, hH, hH, hX, hY]

/-- ... hence with every Casimir factor product.  @census none (helper) -/
theorem map_casimirFactorProd (f : Mi →ₗ[D.carrier] Mi')
    (hH : ∀ v, f (S.weight.H v) = T.weight.H (f v))
    (hX : ∀ v, f (S.weight.X v) = T.weight.X (f v))
    (hY : ∀ v, f (S.weight.Y v) = T.weight.Y (f v)) :
    ∀ (k : ℤ) (m : ℕ) (v : Mi),
      f (casimirFactorProd S.weight.casimir k m v)
        = casimirFactorProd T.weight.casimir k m (f v)
  | _, 0, v => by simp [casimirFactorProd_zero]
  | k, (m + 1), v => by
      rw [casimirFactorProd_succ, casimirFactorProd_succ, Module.End.mul_apply,
        Module.End.mul_apply, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_sub, map_smul,
        map_casimir f hH hX hY, map_casimirFactorProd f hH hX hY (k - 2) m v]

/-- ... hence with `T₋`.  @census none (helper) -/
theorem map_tMinus (f : Mi →ₗ[D.carrier] Mi')
    (hH : ∀ v, f (S.weight.H v) = T.weight.H (f v))
    (hX : ∀ v, f (S.weight.X v) = T.weight.X (f v))
    (hY : ∀ v, f (S.weight.Y v) = T.weight.Y (f v)) (v : Mi) :
    f (Split.tMinus S.toQiSetup v) = Split.tMinus T.toQiSetup (f v) := by
  show f ((((4 : D.carrier) ^ (ℓ - 1) * Split.gammaStarF D.carrier ℓ ^ 2)⁻¹)
      • casimirFactorProd S.weight.casimir ((ℓ : ℤ) - 2) (ℓ - 1) v)
    = (((4 : D.carrier) ^ (ℓ - 1) * Split.gammaStarF D.carrier ℓ ^ 2)⁻¹)
      • casimirFactorProd T.weight.casimir ((ℓ : ℤ) - 2) (ℓ - 1) (f v)
  rw [map_smul, map_casimirFactorProd f hH hX hY]

/-- ... and with `X^r`.  @census none (helper) -/
theorem map_pow_X' (f : Mi →ₗ[D.carrier] Mi')
    (hX : ∀ v, f (S.weight.X v) = T.weight.X (f v)) :
    ∀ (r : ℕ) (v : Mi), f ((S.weight.X ^ r) v) = (T.weight.X ^ r) (f v)
  | 0, v => by simp
  | (r + 1), v => by
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
        map_pow_X' f hX r, hX]

/-- ... hence with `X⋆`.  @census none (helper) -/
theorem map_xStar (f : Mi →ₗ[D.carrier] Mi')
    (hX : ∀ v, f (S.weight.X v) = T.weight.X (f v)) (v : Mi) :
    f (Split.xStar S.toQiSetup v) = Split.xStar T.toQiSetup (f v) := by
  show f (((Split.gammaStarF D.carrier ℓ)⁻¹ : D.carrier) • (S.weight.X ^ (ℓ - 1)) v)
    = ((Split.gammaStarF D.carrier ℓ)⁻¹ : D.carrier) • (T.weight.X ^ (ℓ - 1)) (f v)
  rw [map_smul, map_pow_X' f hX]

/-- **The iterates are natural in the module**: a grading-preserving, `c`-commuting map that
intertwines the two inputs' `φ_±` intertwines every iterate of the two recursions.  The step is
the same uniqueness argument as `conj_inv_unique`, in the form "`f` conjugates two-sided
inverses to two-sided inverses": `Ψ_T ∘ f = Ψ_T ∘ f ∘ (cφ_-^S c) ∘ Ψ_S = Ψ_T ∘ (cφ_-^T c) ∘ f ∘ Ψ_S
= f ∘ Ψ_S`.  @census none (helper) -/
theorem seq_natural (CS : StabInput S) (CT : StabInput T) (f : Mi →ₗ[D.carrier] Mi')
    (hmem : ∀ (n : ℤ) (v : Mi), v ∈ S.weight.comp n → f v ∈ T.weight.comp n)
    (hconj : ∀ v, f (S.conj v) = T.conj (f v))
    (hp : CT.idxPlus = CS.idxPlus) (hm : CT.idxMinus = CS.idxMinus)
    (hfp : ∀ v ∈ S.weight.comp CS.idxPlus, f (CS.phiPlus v) = CT.phiPlus (f v))
    (hfm : ∀ v ∈ S.weight.comp CS.idxMinus, f (CS.phiMinus v) = CT.phiMinus (f v))
    (hpS : HasInverse CS.phpT) (hmS : HasInverse CS.phmT)
    {nS : Module.End D.carrier (Wc S CS.idxPlus)} (hnilS : IsNilpotent nS)
    (hnS : (twistConj galConj_mul_self CS.phmT).comp CS.phpT = 1 + nS)
    (hpT : HasInverse CT.phpT) (hmT : HasInverse CT.phmT)
    {nT : Module.End D.carrier (Wc T CT.idxPlus)} (hnilT : IsNilpotent nT)
    (hnT : (twistConj galConj_mul_self CT.phmT).comp CT.phpT = 1 + nT) :
    ∀ k, (∀ v ∈ S.weight.comp CS.idxPlus, f (CS.seqPlus k v) = CT.seqPlus k (f v)) ∧
      (∀ v ∈ S.weight.comp CS.idxMinus, f (CS.seqMinus k v) = CT.seqMinus k (f v)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [CS.seqPlus_zero_apply v hv,
        CT.seqPlus_zero_apply (f v) (by rw [hp]; exact hmem _ _ hv), hfp v hv]
    · rw [CS.seqMinus_zero_apply v hv,
        CT.seqMinus_zero_apply (f v) (by rw [hm]; exact hmem _ _ hv), hfm v hv]
  | succ k ih =>
    obtain ⟨h1S, h2S⟩ := CS.hasInverse_seqT hpS hmS hnilS hnS k
    obtain ⟨h1T, h2T⟩ := CT.hasInverse_seqT hpT hmT hnilT hnT k
    have hIP : ∀ v ∈ S.weight.comp CS.idxPlus,
        f (CS.seqInvPlus k v) = CT.seqInvPlus k (f v) := by
      intro v hv
      have hΨ : CS.seqInvPlus k v ∈ S.weight.comp (-CS.idxMinus) := CS.seqInvPlus_mem k v
      have hcΨ : S.conj (CS.seqInvPlus k v) ∈ S.weight.comp CS.idxMinus := conj_comp' S hΨ
      have hfΨ : f (CS.seqInvPlus k v) ∈ T.weight.comp (-CT.idxMinus) := by
        rw [hm]; exact hmem _ _ hΨ
      have e1 := CS.seqInvPlus_right k h2S v hv
      have e2 := CT.seqInvPlus_left' k (hasInverse_of_twistConj _ h2T) _ hfΨ
      calc f (CS.seqInvPlus k v)
          = CT.seqInvPlus k (T.conj (CT.seqMinus k (T.conj (f (CS.seqInvPlus k v))))) := e2.symm
        _ = CT.seqInvPlus k (f v) := by
              rw [← hconj, ← ih.2 _ hcΨ, ← hconj, e1]
    have hIM : ∀ v ∈ S.weight.comp CS.idxMinus,
        f (CS.seqInvMinus k v) = CT.seqInvMinus k (f v) := by
      intro v hv
      have hΨ : CS.seqInvMinus k v ∈ S.weight.comp (-CS.idxPlus) := CS.seqInvMinus_mem k v
      have hcΨ : S.conj (CS.seqInvMinus k v) ∈ S.weight.comp CS.idxPlus := conj_comp' S hΨ
      have hfΨ : f (CS.seqInvMinus k v) ∈ T.weight.comp (-CT.idxPlus) := by
        rw [hp]; exact hmem _ _ hΨ
      have e1 := CS.seqInvMinus_right k (h1S.twistConj _) v hv
      have e2 := CT.seqInvMinus_left' k h1T _ hfΨ
      calc f (CS.seqInvMinus k v)
          = CT.seqInvMinus k (T.conj (CT.seqPlus k (T.conj (f (CS.seqInvMinus k v))))) := e2.symm
        _ = CT.seqInvMinus k (f v) := by
              rw [← hconj, ← ih.1 _ hcΨ, ← hconj, e1]
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [CS.seqPlus_succ, CT.seqPlus_succ, LinearMap.smul_apply, LinearMap.smul_apply,
        LinearMap.add_apply, LinearMap.add_apply, map_smul, map_add, ih.1 v hv, hIP v hv]
    · rw [CS.seqMinus_succ, CT.seqMinus_succ, LinearMap.smul_apply, LinearMap.smul_apply,
        LinearMap.add_apply, LinearMap.add_apply, map_smul, map_add, ih.2 v hv, hIM v hv]

/-- **The limits are natural in the module** — clause `RQ-5.05-C5` for one run.
@census none (helper) -/
theorem lim_natural (CS : StabInput S) (CT : StabInput T) (f : Mi →ₗ[D.carrier] Mi')
    (hmem : ∀ (n : ℤ) (v : Mi), v ∈ S.weight.comp n → f v ∈ T.weight.comp n)
    (hconj : ∀ v, f (S.conj v) = T.conj (f v))
    (hp : CT.idxPlus = CS.idxPlus) (hm : CT.idxMinus = CS.idxMinus)
    (hfp : ∀ v ∈ S.weight.comp CS.idxPlus, f (CS.phiPlus v) = CT.phiPlus (f v))
    (hfm : ∀ v ∈ S.weight.comp CS.idxMinus, f (CS.phiMinus v) = CT.phiMinus (f v))
    (hpS : HasInverse CS.phpT) (hmS : HasInverse CS.phmT)
    {nS : Module.End D.carrier (Wc S CS.idxPlus)} (hnilS : IsNilpotent nS)
    (hnS : (twistConj galConj_mul_self CS.phmT).comp CS.phpT = 1 + nS)
    (hpT : HasInverse CT.phpT) (hmT : HasInverse CT.phmT)
    {nT : Module.End D.carrier (Wc T CT.idxPlus)} (hnilT : IsNilpotent nT)
    (hnT : (twistConj galConj_mul_self CT.phmT).comp CT.phpT = 1 + nT) :
    ∀ v ∈ S.weight.comp CS.idxPlus, f (CS.limPlus v) = CT.limPlus (f v) := by
  obtain ⟨eS, hconstS, hlimS, -, -, -, -⟩ := stab_limit_spec CS hpS hmS hnilS hnS
  obtain ⟨eT, hconstT, hlimT, -, -, -, -⟩ := stab_limit_spec CT hpT hmT hnilT hnT
  have hS : CS.limPlus = CS.seqPlus (max eS eT) := by
    show toEnd S (CS.limT).1 = toEnd S (CS.seqT (max eS eT)).1
    rw [hlimS, ← hconstS _ (le_max_left eS eT)]
  have hT : CT.limPlus = CT.seqPlus (max eS eT) := by
    show toEnd T (CT.limT).1 = toEnd T (CT.seqT (max eS eT)).1
    rw [hlimT, ← hconstT _ (le_max_right eS eT)]
  intro v hv
  rw [hS, hT]
  exact (seq_natural CS CT f hmem hconj hp hm hfp hfm hpS hmS hnilS hnS hpT hmT hnilT hnT
    (max eS eT)).1 v hv

end Naturality

/-! ### `RQ-5.04` — the claimant -/

/-- **`RQ-5.04`** (`eq:varphiplus`, `eq:varphiminus`, `eq:varphistar`) — simultaneous stabilization.

For `ℓ ≥ 1` and a `ℚ[√-1]`-rational Harish-Chandra module descending to `ℚ` (`H1`), with
`RQ-3.06`, `RQ-3.07`, `RQ-4.01`, `RQ-4.02` (`H2`, all proved on the merged tree):
* `C7`: the three recursions **stabilize** — each is eventually constant, "in the sense of
  `cor:unipotentstabilization`" (its `RQ-4.02-C1`) — so the limits `limPlus`/`limMinus` are the
  values `φ^{(∞)}_•` of `def:unipotentstabilization`;
* `C8`: the limit relations — for `(±)` the transposition identities `φ^{(∞)}_{-,±} = φ^{(∞)}_{+,∓}`
  (what the source prints since 2026-09-11; see the retirement note below), for `(⋆)` that the
  `τ`-conjugate run's limit is the conjugate of the `(⋆)` run's limit;
* `C9` = `eq:conjugateinversepm`, `C10` = `eq:conjugateinversestar`, on the components;
* `C11`: `φ_± := c ∘ φ^{(∞)}_±`, `φ_⋆ := c ∘ φ^{(∞)}_⋆` are **semi-linear isomorphisms** between the
  components they connect (`M(+) → M(−)`, `M(−) → M(+)`, `M(⋆) → M(⋆)`), semi-linear over the
  non-trivial element of `Gal(ℚ[√-1]/ℚ)` (`HC.RationalSetup.conj_smul`'s sense).

@census    RQ2-5.04
@source    eq:varphiplus
@clauses   RQ2-5.04-H1, RQ2-5.04-H2, RQ2-5.04-C7, RQ2-5.04-C8, RQ2-5.04-C9, RQ2-5.04-C10,
  RQ2-5.04-C11, RQ2-5.04-C12,
  RQ2-5.04-S-O11
@imports   none
**`AN-38` and `AN-39` RETIRED, 2026-09-11.**  Until the paper author's ruling of that date this
declaration disclosed two things, and both are now what the source prints.  (i) Clause `C8`'s
`(±)` half: the printed `φ^{(∞),c}_{+,±} = φ^{(∞)}_{-,±}` under the itemized `(−)` data (the
transpose of `(+)`) would have forced `(φ^{(∞)}_{+,+})² = 𝟏`, whereas
`(φ^{(∞)}_{+,+})² = T₊⁻¹` on `M_{ℓ+1}`; what §5.3 uses is `eq:conjugateinversepm` (`C9`), which
holds.  The source now prints the transposition identities, which is what the `(±)` half is
rendered as (`AN-39`, census `RQ-5.04-C8` at r14).  (ii) The `(⋆)` input is the type-checking
instantiation `W₊ = W₋ = M_{-(ℓ-1)}`, `φ₊ = φ₋ = X⋆`, which the source now itemizes (`AN-38`,
census `RQ-5.04-C1` at r14; module docstring, notes (1) and (2)).  **The tree and the source agree
on both**, and only the generalisation disclosure survives.

@divergence JUSTIFIED_REFORMULATION (stated for a bare `RationalSetup`, not `Gelfand.HCQObj`
(`RQ-5.05`'s own category) — a **true generalization** (`CONVENTIONS.md` §3), unused by the proof;
2026-09-03, `R-S8-16`(c), `V-S8-D1-4`(b)).  v2 (`R-V2-3`, presentation): `H1` (`√-1 ∉ E`, `M_{L_E} =
L_E ⊗_E M_E`) is the datum `S`, which an object of `HC ℓ E D` provides through `HC.setup`
(`conj := galAct c`, `RationalStructure/Bridge.lean`).  `C12` (`√-1 ∈ E`: `G_E = 1`, `φ_•` trivial) is
the dispatch of `E_E_φ` (`E_E_φ_of_one`, module `RationalStructure/Phi`): no stabilization is run. -/
theorem varphi_spec (S : RationalSetupOver ℓ E D Mq Mi) (hℓ : 1 ≤ ℓ) :
    -- `C7`: the three stabilizations exist (the recursions are eventually constant)
    ((∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (inputPlus S).seqT k = (inputPlus S).seqT k₀) ∧
      (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (inputMinus S).seqT k = (inputMinus S).seqT k₀) ∧
      (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (inputStar S hℓ).seqT k = (inputStar S hℓ).seqT k₀)) ∧
    -- `C8`: the limit relations
    (((inputMinus S).limPlus = (inputPlus S).limMinus ∧
        (inputMinus S).limMinus = (inputPlus S).limPlus) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) - 1),
        S.conj ((inputStar S hℓ).limPlus (S.conj v)) = (inputStar S hℓ).conj.limPlus v)) ∧
    -- `C9` = `eq:conjugateinversepm`
    ((∀ v ∈ S.weight.comp ((ℓ : ℤ) + 1),
        S.conj ((inputMinus S).limPlus (S.conj ((inputPlus S).limPlus v))) = v) ∧
      (∀ v ∈ S.weight.comp (-((ℓ : ℤ) + 1)),
        S.conj ((inputPlus S).limPlus (S.conj ((inputMinus S).limPlus v))) = v)) ∧
    -- `C10` = `eq:conjugateinversestar`
    ((∀ v ∈ S.weight.comp (-((ℓ : ℤ) - 1)),
        S.conj ((inputStar S hℓ).limPlus (S.conj ((inputStar S hℓ).limPlus v))) = v) ∧
      (∀ v ∈ S.weight.comp ((ℓ : ℤ) - 1),
        (inputStar S hℓ).limPlus (S.conj ((inputStar S hℓ).limPlus (S.conj v))) = v)) ∧
    -- `C11`: `φ_± := c ∘ φ^{(∞)}_±`, `φ_⋆ := c ∘ φ^{(∞)}_⋆` are semi-linear isomorphisms
    ((∀ (a : D.carrier) (v : Mi),
        S.conj ((inputPlus S).limPlus (a • v)) = D.conj a • S.conj ((inputPlus S).limPlus v)) ∧
      Set.BijOn (fun v => S.conj ((inputPlus S).limPlus v))
        (S.weight.comp ((ℓ : ℤ) + 1)) (S.weight.comp (-((ℓ : ℤ) + 1))) ∧
      (∀ (a : D.carrier) (v : Mi),
        S.conj ((inputMinus S).limPlus (a • v)) = D.conj a • S.conj ((inputMinus S).limPlus v)) ∧
      Set.BijOn (fun v => S.conj ((inputMinus S).limPlus v))
        (S.weight.comp (-((ℓ : ℤ) + 1))) (S.weight.comp ((ℓ : ℤ) + 1)) ∧
      (∀ (a : D.carrier) (v : Mi),
        S.conj ((inputStar S hℓ).limPlus (a • v))
          = D.conj a • S.conj ((inputStar S hℓ).limPlus v)) ∧
      Set.BijOn (fun v => S.conj ((inputStar S hℓ).limPlus v))
        (S.weight.comp (-((ℓ : ℤ) - 1))) (S.weight.comp (-((ℓ : ℤ) - 1)))) :=
  -- Shift 5: shift 4's residue (`DESIGN-NOTES.md` §10.3) is discharged by `conjStar_limit`,
  -- route 2's induction on `k` at the `M_{ℚ[√-1]}` level.
  varphi_spec_of_conjStar S hℓ (conjStar_limit S hℓ)

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


/-! ### The `E3` bridge: `toEnd` read on a fixed space through two identifications

`stages/S8/DESIGN-NOTES.md` §13.4's obstacle (b): nothing in the tree identified S8's
`StabInput`/`toEnd` layer with the endomorphism-of-`W_+` layer the addendum lives on.  These four
declarations are that bridge, and they carry no `hWp`.
-/

section Bridge

variable (S : RationalSetupOver ℓ E D Mq Mi)

/-- `W_n ≃ M_n`: the component of `ℚ[√-1] ⊗_ℚ M_ℚ` **is** the component of `M_{ℚ[√-1]}`, through
the base change.  @census none (helper: the `E3` bridge) -/
noncomputable def wcEquivComp (n : ℤ) : Wc S n ≃ₗ[D.carrier] S.weight.comp n where
  toFun x := ⟨S.baseChange (x : D.carrier ⊗[E] Mq), x.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)
  invFun y := ⟨S.baseChange.symm (y : Mi), by
    show S.baseChange (S.baseChange.symm (y : Mi)) ∈ S.weight.comp n
    rw [LinearEquiv.apply_symm_apply]; exact y.2⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

@[simp] theorem wcEquivComp_coe (n : ℤ) (x : Wc S n) :
    ((wcEquivComp S n x : S.weight.comp n) : Mi) = S.baseChange (x : D.carrier ⊗[E] Mq) := rfl

@[simp] theorem wcEquivComp_symm_coe (n : ℤ) (y : S.weight.comp n) :
    (((wcEquivComp S n).symm y : Wc S n) : D.carrier ⊗[E] Mq)
      = S.baseChange.symm (y : Mi) := rfl

/-- `W_p ≃ W` through a chosen identification `α : M_p ≃ W` of the component.
@census none (helper: the `E3` bridge) -/
noncomputable def readVia {p : ℤ} {W : Type} [AddCommGroup W] [Module D.carrier W]
    (α : S.weight.comp p ≃ₗ[D.carrier] W) : Wc S p ≃ₗ[D.carrier] W :=
  (wcEquivComp S p).trans α

/-- `(M_m)^τ = M_q` when `q = -m`.  @census none (helper: the `E3` bridge) -/
theorem twist_Wc_eq {m q : ℤ} (hq : (-m : ℤ) = q) : twist D.conj (Wc S m) = Wc S q := by
  rw [twist_Wc, hq]

/-- The identification `W_-^τ ≃ W_+` induced by two identifications of the two components with the
**same** space `W`.  For the `(⋆)` run of §5.2 this is the identification
`eq:limitsquarerootdiagram0` itself uses — `M_{-(ℓ-1)} ≅ V(⋆) ≅ M_{ℓ-1}` — and it exists although
`twist D.conj (Wc S (-(ℓ-1))) = Wc S (ℓ-1) ≠ Wc S (-(ℓ-1))`, which is why `E3` is available for a
run S6's `hWp`-shaped addendum cannot see.  @census none (helper: the `E3` bridge) -/
noncomputable def identVia {p m q : ℤ} {W : Type} [AddCommGroup W] [Module D.carrier W]
    (hq : (-m : ℤ) = q) (α : S.weight.comp p ≃ₗ[D.carrier] W)
    (β : S.weight.comp q ≃ₗ[D.carrier] W) :
    twist D.conj (Wc S m) ≃ₗ[D.carrier] Wc S p :=
  (LinearEquiv.ofEq _ _ (twist_Wc_eq S hq)).trans ((readVia S β).trans (readVia S α).symm)

/-- **The bridge.**  `toEnd S F` restricted to `M_p` and read through `α` on the source and `β` on
the target is the conjugate, by `readVia S α`, of `asEndVia (identVia S hq α β) F`.  Everything the
`E3` engine proves in `End_L(W_+)` therefore transfers to the `V(•)` reading, and conversely.
@census none (helper: the `E3` bridge) -/
theorem toEnd_read {p m q : ℤ} {W : Type} [AddCommGroup W] [Module D.carrier W]
    (hq : (-m : ℤ) = q) (α : S.weight.comp p ≃ₗ[D.carrier] W)
    (β : S.weight.comp q ≃ₗ[D.carrier] W)
    (F : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m)) (x : W) (y : S.weight.comp q)
    (hy : (y : Mi) = toEnd S F ((α.symm x : S.weight.comp p) : Mi)) :
    (β y : W) = readVia S α (asEndVia (identVia S hq α β) F ((readVia S α).symm x)) := by
  have hv : ((α.symm x : S.weight.comp p) : Mi) ∈ S.weight.comp p := (α.symm x).2
  have hpr : projT S p (S.baseChange.symm ((α.symm x : S.weight.comp p) : Mi))
      = (readVia S α).symm x := by
    refine Subtype.ext ?_
    rw [projT_apply, LinearEquiv.apply_symm_apply, S.weight.proj_of_mem_same hv]
    rfl
  have hcancel : ∀ z : W, (wcEquivComp S p) ((readVia S α).symm z) = α.symm z := by
    intro z
    show (wcEquivComp S p) ((wcEquivComp S p).symm (α.symm z)) = α.symm z
    exact (wcEquivComp S p).apply_symm_apply _
  have hRHS : readVia S α (asEndVia (identVia S hq α β) F ((readVia S α).symm x))
      = β ((wcEquivComp S q)
          ((LinearEquiv.ofEq _ _ (twist_Wc_eq S hq)) (F ((readVia S α).symm x)))) := by
    show α ((wcEquivComp S p) ((readVia S α).symm ((readVia S β)
        ((LinearEquiv.ofEq _ _ (twist_Wc_eq S hq)) (F ((readVia S α).symm x)))))) = _
    rw [hcancel, LinearEquiv.apply_symm_apply]
    rfl
  rw [hRHS]
  refine congrArg β (Subtype.ext ?_)
  rw [hy, toEnd_apply, hpr]
  rfl

/-- **The bridge for `Q = φ_-^τ`.**  Read through `α` on `M_p`, `asEndConjVia` is `c ∘ φ_- ∘ c`
with its argument read through `β` on `M_q`.  @census none (helper: the `E3` bridge) -/
theorem asEndConjVia_read {p m q : ℤ} {W : Type} [AddCommGroup W] [Module D.carrier W]
    (hq : (-m : ℤ) = q) (α : S.weight.comp p ≃ₗ[D.carrier] W)
    (β : S.weight.comp q ≃ₗ[D.carrier] W)
    (φm : Wc S m →ₗ[D.carrier] twist D.conj (Wc S p)) (x : W) (y : S.weight.comp p)
    (hy : (y : Mi) = S.conj (toEnd S φm (S.conj ((β.symm x : S.weight.comp q) : Mi)))) :
    readVia S α (asEndConjVia galConj_mul_self (identVia S hq α β) φm ((readVia S α).symm x))
      = α y := by
  have hmem : ((β.symm x : S.weight.comp q) : Mi) ∈ S.weight.comp q := (β.symm x).2
  have hcm : S.conj ((β.symm x : S.weight.comp q) : Mi) ∈ S.weight.comp m := by
    have h := S.conj_comp q _ hmem
    have hqm : (-q : ℤ) = m := by omega
    rwa [hqm] at h
  have hwm : S.baseChange.symm (S.conj ((β.symm x : S.weight.comp q) : Mi)) ∈ Wc S m := by
    show S.baseChange (S.baseChange.symm _) ∈ S.weight.comp m
    rw [LinearEquiv.apply_symm_apply]; exact hcm
  set w : Wc S m := ⟨_, hwm⟩ with hwdef
  have hproj : projT S m
      (S.baseChange.symm (S.conj ((β.symm x : S.weight.comp q) : Mi))) = w := by
    refine Subtype.ext ?_
    rw [projT_apply, LinearEquiv.apply_symm_apply, S.weight.proj_of_mem_same hcm]
  have hesymm : (identVia S hq α β).symm ((readVia S α).symm x)
      = (LinearEquiv.ofEq _ _ (twist_Wc_eq S hq)).symm ((readVia S β).symm x) := by
    show (LinearEquiv.ofEq _ _ (twist_Wc_eq S hq)).symm
        ((readVia S β).symm (readVia S α ((readVia S α).symm x))) = _
    rw [LinearEquiv.apply_symm_apply]
  have htb : twistBack galConj_mul_self
      ((identVia S hq α β).symm ((readVia S α).symm x)) = w := by
    rw [hesymm]
    refine Subtype.ext ?_
    show galoisTwist D.conj
        (S.baseChange.symm ((β.symm x : S.weight.comp q) : Mi)) = _
    rw [galoisTwist_eq_conj S, LinearEquiv.apply_symm_apply]
  have hres : asEndConjVia galConj_mul_self (identVia S hq α β) φm ((readVia S α).symm x)
      = twistBack galConj_mul_self (φm w) := by
    show twistBack galConj_mul_self (φm (twistBack galConj_mul_self
      ((identVia S hq α β).symm ((readVia S α).symm x)))) = _
    rw [htb]
  rw [hres]
  refine congrArg α (Subtype.ext ?_)
  show S.baseChange (galoisTwist D.conj
      ((φm w : twist D.conj (Wc S p)) : D.carrier ⊗[E] Mq)) = (y : Mi)
  rw [galoisTwist_eq_conj S, LinearEquiv.apply_symm_apply, hy, toEnd_apply, hproj]

/-- `toEnd_read` evaluated at an element of `W_p` itself.  @census none (helper: the `E3` bridge) -/
theorem toEnd_read_apply {p m q : ℤ} {W : Type} [AddCommGroup W] [Module D.carrier W]
    (hq : (-m : ℤ) = q) (α : S.weight.comp p ≃ₗ[D.carrier] W)
    (β : S.weight.comp q ≃ₗ[D.carrier] W)
    (F : Wc S p →ₗ[D.carrier] twist D.conj (Wc S m)) (z : Wc S p) (y : S.weight.comp q)
    (hy : (y : Mi) = toEnd S F (S.baseChange (z : D.carrier ⊗[E] Mq))) :
    (β y : W) = readVia S α (asEndVia (identVia S hq α β) F z) := by
  have hz : ((α.symm (readVia S α z) : S.weight.comp p) : Mi)
      = S.baseChange (z : D.carrier ⊗[E] Mq) := by
    show ((α.symm (α (wcEquivComp S p z)) : S.weight.comp p) : Mi) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have h := toEnd_read S hq α β F (readVia S α z) y (by rw [hy, hz])
  rwa [LinearEquiv.symm_apply_apply] at h

/-- `asEndConjVia_read` evaluated at an element of `W_p` itself.
@census none (helper: the `E3` bridge) -/
theorem asEndConjVia_read_apply {p m q : ℤ} {W : Type} [AddCommGroup W] [Module D.carrier W]
    (hq : (-m : ℤ) = q) (α : S.weight.comp p ≃ₗ[D.carrier] W)
    (β : S.weight.comp q ≃ₗ[D.carrier] W)
    (φm : Wc S m →ₗ[D.carrier] twist D.conj (Wc S p)) (z : Wc S p) (y : S.weight.comp p)
    (hy : (y : Mi) = S.conj (toEnd S φm
      (S.conj ((β.symm (readVia S α z) : S.weight.comp q) : Mi)))) :
    readVia S α (asEndConjVia galConj_mul_self (identVia S hq α β) φm z) = α y := by
  have h := asEndConjVia_read S hq α β φm (readVia S α z) y hy
  rwa [LinearEquiv.symm_apply_apply] at h

/-- Pull an endomorphism back along a linear equivalence.  @census none (helper: the `E3` bridge) -/
noncomputable def endConjOf {W₁ W₂ : Type} [AddCommMonoid W₁] [Module D.carrier W₁]
    [AddCommMonoid W₂] [Module D.carrier W₂] (Θ : W₁ ≃ₗ[D.carrier] W₂)
    (A : Module.End D.carrier W₂) : Module.End D.carrier W₁ :=
  Θ.symm.toLinearMap ∘ₗ (A ∘ₗ Θ.toLinearMap)

@[simp] theorem endConjOf_apply {W₁ W₂ : Type} [AddCommMonoid W₁] [Module D.carrier W₁]
    [AddCommMonoid W₂] [Module D.carrier W₂] (Θ : W₁ ≃ₗ[D.carrier] W₂)
    (A : Module.End D.carrier W₂) (z : W₁) : endConjOf Θ A z = Θ.symm (A (Θ z)) := rfl

theorem endConjOf_one {W₁ W₂ : Type} [AddCommMonoid W₁] [Module D.carrier W₁]
    [AddCommMonoid W₂] [Module D.carrier W₂] (Θ : W₁ ≃ₗ[D.carrier] W₂) :
    endConjOf Θ 1 = 1 :=
  LinearMap.ext fun z => Θ.symm_apply_apply z

theorem endConjOf_add {W₁ W₂ : Type} [AddCommMonoid W₁] [Module D.carrier W₁]
    [AddCommMonoid W₂] [Module D.carrier W₂] (Θ : W₁ ≃ₗ[D.carrier] W₂)
    (A B : Module.End D.carrier W₂) :
    endConjOf Θ (A + B) = endConjOf Θ A + endConjOf Θ B :=
  LinearMap.ext fun z => by simp [endConjOf]

theorem endConjOf_injective {W₁ W₂ : Type} [AddCommMonoid W₁] [Module D.carrier W₁]
    [AddCommMonoid W₂] [Module D.carrier W₂] (Θ : W₁ ≃ₗ[D.carrier] W₂) :
    Function.Injective (endConjOf Θ) := by
  intro A B hAB
  refine LinearMap.ext fun y => ?_
  have h := congrArg (fun (f : Module.End D.carrier W₁) => Θ (f (Θ.symm y))) hAB
  simpa using h

/-- Nilpotency transfers along a conjugation by a linear equivalence.
@census none (helper: the `E3` bridge) -/
theorem isNilpotent_of_conj {W₁ W₂ : Type} [AddCommMonoid W₁] [Module D.carrier W₁]
    [AddCommMonoid W₂] [Module D.carrier W₂] (Θ : W₁ ≃ₗ[D.carrier] W₂)
    {A : Module.End D.carrier W₁} {B : Module.End D.carrier W₂}
    (hB : ∀ x, B x = Θ (A (Θ.symm x))) (hA : IsNilpotent A) : IsNilpotent B := by
  obtain ⟨k, hk⟩ := hA
  have hpow : ∀ (j : ℕ) (x : W₂), (B ^ j) x = Θ ((A ^ j) (Θ.symm x)) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
        intro x
        rw [pow_succ, Module.End.mul_apply, ih, hB, Θ.symm_apply_apply, pow_succ,
          Module.End.mul_apply]
  refine ⟨k, ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [hpow, hk]
  simp

end Bridge

/-! ### The TRIVIAL stabilization — when both maps of the input are `𝟏`

`RQ-5.07` is the case `ℓ = 0`, and there `T_± = 𝟏` (`Gelfand/Cyclic.lean`'s `tMinus_zero`: the
Casimir product `∏_{j=0}^{ℓ-2}` is EMPTY and `γ_⋆(0) = 0! = 1`), so both maps of the `(±)`
stabilization inputs are the identity.  The recursion is then constant from step 0 — the
Newton step `½(φ₊ + (φ₋^τ)^{-1})` averages a map with itself — and the limit `φ^{(∞)}_±` is the
identity on its component.  That is the whole content of the source's "at `ℓ = 0` the
stabilizations are trivial", and it is what makes `E_CycSpec`'s cocycle and equivariance
conditions collapse to `c² = 𝟏` and `cX = Yc`.

Stated for a bare `StabInput` with `φ₊ = φ₋ = 𝟏`, not for `ℓ = 0` specifically — a **true
generalization** (`CONVENTIONS.md` §3), and the proof uses nothing else.
`stages/S8/DESIGN-NOTES.md` §20.2. -/

section TrivialStabilization

variable {S : RationalSetupOver ℓ E D Mq Mi}

/-- The `±`-swap of a stabilization input; `C.swap.phpT` is `C.phmT` on the nose.
@census none (helper) -/
noncomputable def StabInput.swap (C : StabInput S) : StabInput S where
  idxPlus := C.idxMinus
  idxMinus := C.idxPlus
  phiPlus := C.phiMinus
  phiMinus := C.phiPlus
  phiPlus_mem := C.phiMinus_mem
  phiMinus_mem := C.phiPlus_mem

variable (C : StabInput S)

/-- With `φ₊ = 𝟏`, `phpT` IS `ofEnd 𝟏`.  @census none (helper) -/
theorem phpT_eq_ofEnd (hp : C.phiPlus = 1)
    (hB : ∀ v ∈ S.weight.comp C.idxPlus, (1 : Module.End D.carrier Mi) v
      ∈ S.weight.comp (-C.idxMinus)) :
    ofEnd S (1 : Module.End D.carrier Mi) hB = C.phpT := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  rw [ofEnd_coe, C.phpT_coe, hp]

/-- With both maps `𝟏`, the junk inverse of `φ₋^τ` is `φ₊` — `c² = 𝟏` is the whole input.
@census none (helper) -/
theorem linInv_tc_phmT_of_one (hp : C.phiPlus = 1) (hm : C.phiMinus = 1)
    (hB : ∀ v ∈ S.weight.comp C.idxPlus, (1 : Module.End D.carrier Mi) v
      ∈ S.weight.comp (-C.idxMinus)) :
    linInv (twistConj galConj_mul_self C.phmT) = C.phpT := by
  have hleft : ∀ v ∈ S.weight.comp (-C.idxMinus),
      (1 : Module.End D.carrier Mi) (S.conj (C.phiMinus (S.conj v))) = v := by
    intro v _; rw [hm]; show S.conj (S.conj v) = v; exact S.conj_involutive v
  have hright : ∀ v ∈ S.weight.comp C.idxPlus,
      S.conj (C.phiMinus (S.conj ((1 : Module.End D.carrier Mi) v))) = v := by
    intro v _; rw [hm]; show S.conj (S.conj v) = v; exact S.conj_involutive v
  rw [linInv_twistConj_phmT C (1 : Module.End D.carrier Mi) hB hleft hright,
    phpT_eq_ofEnd C hp hB]

/-- The Newton step averages a map with itself.  @census none (helper) -/
theorem step_eq_self {U V : Submodule D.carrier (D.carrier ⊗[E] Mq)}
    (f : U →ₗ[D.carrier] twist D.conj V)
    (g : V →ₗ[D.carrier] twist D.conj U)
    (h : linInv (twistConj galConj_mul_self g) = f) :
    stabilizationStep (K := E) two_ne_zero galConj_mul_self f g = f := by
  rw [stabilizationStep_def, h]
  have h2 : f + f = (2 : D.carrier) • f := (two_smul _ f).symm
  rw [h2, smul_smul]
  have hkey : half (two_ne_zero_of_base (L := D.carrier) (two_ne_zero (α := E)))
      * (2 : D.carrier) = 1 := by
    rw [half_eq]
    exact inv_mul_cancel₀ (two_ne_zero_of_base (K := E) two_ne_zero)
  rw [hkey, one_smul]

/-- The recursion is constant.  @census none (helper) -/
theorem seqT_const_of_one (hp : C.phiPlus = 1) (hm : C.phiMinus = 1)
    (hBp : ∀ v ∈ S.weight.comp C.idxPlus, (1 : Module.End D.carrier Mi) v
      ∈ S.weight.comp (-C.idxMinus))
    (hBm : ∀ v ∈ S.weight.comp C.idxMinus, (1 : Module.End D.carrier Mi) v
      ∈ S.weight.comp (-C.idxPlus)) :
    ∀ k, C.seqT k = C.seqT 0 := by
  have h1 : linInv (twistConj galConj_mul_self C.phmT) = C.phpT :=
    linInv_tc_phmT_of_one C hp hm hBp
  have h2 : linInv (twistConj galConj_mul_self C.phpT) = C.phmT :=
    linInv_tc_phmT_of_one C.swap hm hp hBm
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have hE : C.seqT (k + 1)
        = (stabilizationStep (K := E) two_ne_zero galConj_mul_self (C.seqT k).1 (C.seqT k).2,
           stabilizationStep (K := E) two_ne_zero galConj_mul_self (C.seqT k).2 (C.seqT k).1) :=
      rfl
    rw [hE, ih]
    show (stabilizationStep (K := E) two_ne_zero galConj_mul_self C.phpT C.phmT,
          stabilizationStep (K := E) two_ne_zero galConj_mul_self C.phmT C.phpT) = _
    rw [step_eq_self C.phpT C.phmT h1, step_eq_self C.phmT C.phpT h2]
    rfl

/-- **The trivial stabilization**: `φ^{(∞)}_+ = 𝟏` on `W₊`.  @census none (helper) -/
theorem limPlus_eq_of_one (hp : C.phiPlus = 1) (hm : C.phiMinus = 1)
    (hBp : ∀ v ∈ S.weight.comp C.idxPlus, (1 : Module.End D.carrier Mi) v
      ∈ S.weight.comp (-C.idxMinus))
    (hBm : ∀ v ∈ S.weight.comp C.idxMinus, (1 : Module.End D.carrier Mi) v
      ∈ S.weight.comp (-C.idxPlus))
    (v : Mi) (hv : v ∈ S.weight.comp C.idxPlus) : C.limPlus v = v := by
  have hlim : C.limT = C.seqT 0 :=
    eventualValue_eq C.seqT (k₀ := 0) (fun k _ => seqT_const_of_one C hp hm hBp hBm k)
  show toEnd S C.limT.1 v = v
  rw [hlim]
  have hz : toEnd S (C.seqT 0).1 v = C.seqPlus 0 v := rfl
  rw [hz, C.seqPlus_zero_apply v hv, hp]
  rfl

end TrivialStabilization


end RationalQuivers.Gelfand.RationalStructure
