import RationalQuivers.HC.Category
import RationalQuivers.Gelfand.GeneralBaseCategory
import RationalQuivers.Gelfand.Split.Construction
import RationalQuivers.Unipotent.Twist

/-!
# The `R-V2-3` bridges: `HC ℓ E D` and the relocated `G_E`-engine (helper, stage T3)

Ruling `R-V2-3` (WP-4 spike, GO(b) by the **bridge route**, §1.1) accepts the following thin
adapters between the uniform category `HC ℓ E D` of T1 (`def:HClambdaE`, descent presentation) and
the datum the relocated non-split engine of §§5.2–5.3 runs on (`RationalSetupOver`/`HCEObj` over a
quadratic `SqrtNegOneExt`):

* `ImagUnit.sqrtExt` — for `√-1 ∉ E` (equivalently `∃ σ, χ_E(σ) = -1`), `L_E = E(√-1)` as a
  `SqrtNegOneExt` with **the same field** `D.L` (its root `D.i` is no longer a field of the
  structure since v2 T3-a1; it is passed explicitly where needed); its `conj` is every `σ` with
  `χ_E(σ) = -1` (`sqrtExt_conj`), i.e. complex conjugation `c` of `def:sqrtminusone`.
* `HC.setup` — an object `M_E` of `HC ℓ E D` read with `conj := galAct c`, the Galois action of `c`
  on `M_{L_E} = L_E ⊗_E M_E` (`1 ⊗ c` in the tex).
* `HC.toHCEObj`, `HCEObj.toHC` — the same carrier, read in the two presentations; on morphisms the
  identity of the underlying `L_E`-linear maps (`map_gal` for every `σ` ⟺ `map_conj` for `c`).

Nothing here is a second engine or a second carrier (`R-V2-3` §1.1(1)): every construction is the
identity on the underlying modules.  The bridges are an **identification of presentations**
(`R-V2-3` §1.1(4), §5), disclosed in the T3 freeze packet.

@census none (helper module)
-/

namespace RationalQuivers.HC

open RationalQuivers.Gelfand RationalQuivers.Unipotent CategoryTheory
open scoped TensorProduct

variable {E : Type} [Field E] [CharZero E]

namespace ImagUnit

variable (D : ImagUnit E)

/-- **Bridge 1.** For `√-1 ∉ E` (given as `∃ σ ∈ G_E, χ_E(σ) = -1`), `L_E` as a quadratic
`SqrtNegOneExt` on the same field `D.L`.  (Before the v2 amendment T3-a1 the structure also carried
the root, set to `D.i`; it is root-free now, and consumers that need `√-1 ∈ L_E` take
`D.i`, `D.i_mul_i` explicitly.)  @census none (helper; bridge) -/
@[reducible] noncomputable def sqrtExt (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) :
    SqrtNegOneExt E where
  carrier := D.L
  card_gal := D.card_gal_of h

/-- The bridge's `conj` **is** every `σ` with `χ σ = -1`: complex conjugation `c`.
@census none (helper; bridge) -/
theorem sqrtExt_conj (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) {σ : D.L ≃ₐ[E] D.L}
    (hσ : D.chi σ = -1) : (D.sqrtExt h).conj = σ :=
  ((D.sqrtExt h).eq_conj_of_ne_one (D.chi_eq_neg_one_iff_ne_one.mp hσ)).symm

/-- `χ_E(c) = -1` for the bridge's `conj`.  @census none (helper; bridge) -/
theorem chi_sqrtExt_conj (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) :
    D.chi (D.sqrtExt h).conj = -1 :=
  D.chi_eq_neg_one_iff_ne_one.mpr (D.sqrtExt h).conj_ne_one

/-- `c(√-1) = -√-1` for the bridge's `conj` (`ζ = √-1` of Step O-17).  @census none (helper) -/
theorem sqrtExt_conj_i (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) :
    (D.sqrtExt h).conj D.i = -D.i :=
  D.chi_eq_neg_one_iff.mp (D.chi_sqrtExt_conj h)

end ImagUnit

/-- The `(𝔤,K)`-span of `HC/Category` and the graded span of `Split/Construction` are the same
submodule (same definition, two names; `T2` FREEZE §4 item 4).  @census none (helper) -/
theorem gkSpanOver_eq_gkSpanGraded {L M : Type} [Field L] [AddCommGroup M] [Module L M]
    (W : WeightData L M) (S : Set M) : gkSpanOver W S = Gelfand.gkSpanGraded W S := rfl

namespace HC

variable {D : ImagUnit E} {ℓ : ℕ}

/-- `galAct σ` is an involution when `χ σ = -1` (`σ² = 1`).  @census none (helper) -/
theorem galAct_galAct (A : HC ℓ E D) (σ : D.L ≃ₐ[E] D.L) (v : A.carrier) :
    A.galAct σ (A.galAct σ v) = v := by
  simp only [galAct, galActOf_apply, LinearEquiv.symm_apply_apply,
    galoisTwist_galoisTwist (D.mul_self σ), LinearEquiv.apply_symm_apply]

variable (A : HC ℓ E D) (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1)

/-- **Bridge 2.** An object `M_E` of `HC ℓ E D` with `√-1 ∉ E`, read as the relocated engine's
datum over `D.sqrtExt h`: the same `M_E`, `M_{L_E}`, base change and weight data, with
`conj := galAct c` (`1 ⊗ c` on `L_E ⊗_E M_E`).  @census none (helper; bridge) -/
noncomputable def setup : RationalSetupOver ℓ E (D.sqrtExt h) A.form A.carrier where
  baseChange := A.baseChange
  weight := A.weight
  gic := A.gic
  conj := A.galAct (D.sqrtExt h).conj
  conj_smul a v := galActOf_smul _ _ a v
  conj_involutive v := A.galAct_galAct _ v
  conj_baseChange v := galActOf_tmul _ _ v
  conj_comp := (A.compat_neg (D.chi_sqrtExt_conj h)).1
  conj_X := (A.compat_neg (D.chi_sqrtExt_conj h)).2.1
  conj_Y := (A.compat_neg (D.chi_sqrtExt_conj h)).2.2.1
  conj_H := (A.compat_neg (D.chi_sqrtExt_conj h)).2.2.2

/-- The bridge's conjugation is `galAct σ` for **every** `σ` with `χ σ = -1`.
@census none (helper; bridge) -/
theorem setup_conj {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = -1) :
    (A.setup h).conj = A.galAct σ := by
  show A.galAct (D.sqrtExt h).conj = A.galAct σ
  rw [D.sqrtExt_conj h hσ]

theorem setup_weight : (A.setup h).weight = A.weight := rfl

theorem setup_baseChange : (A.setup h).baseChange = A.baseChange := rfl

/-- **Bridge 3a.** `HC ℓ E D → HCEObj ℓ E (D.sqrtExt h)`: the same object, read in the engine's
presentation.  @census none (helper; bridge) -/
noncomputable def toHCEObj : HCEObj ℓ E (D.sqrtExt h) where
  form := A.form
  carrier := A.carrier
  setup := A.setup h
  admissible := A.admissible
  centralCharacter := A.centralCharacter
  fg := A.fg

end HC

variable {D : ImagUnit E} {ℓ : ℕ} {h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1}

/-- `sqrtExt` is reducible, so instance search sees `(D.sqrtExt h).carrier` as `D.L` and misses
`HCEObj.module`; this re-keys it.  @census none (helper; bridge) -/
instance instModuleHCEObjSqrtExt (B : HCEObj ℓ E (D.sqrtExt h)) : Module D.L B.carrier := B.module

/-- On the base change, `c` is the Galois twist `c ⊗ 1` (the engine's `conj_baseChange` and
`conj_smul`, read through the base change).  @census none (helper; bridge) -/
theorem galoisTwist_eq_setupConj {D' : SqrtNegOneExt E} {Mq Mi : Type} [AddCommGroup Mq]
    [Module E Mq] [AddCommGroup Mi] [Module D'.carrier Mi] (S : RationalSetupOver ℓ E D' Mq Mi)
    (x : D'.carrier ⊗[E] Mq) :
    galoisTwist D'.conj x = S.baseChange.symm (S.conj (S.baseChange x)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [galoisTwist_tmul]
    have h1 : S.baseChange (a ⊗ₜ[E] v) = a • S.baseChange ((1 : D'.carrier) ⊗ₜ[E] v) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, S.conj_smul, S.conj_baseChange, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one, LinearEquiv.symm_apply_apply]
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]

/-- On an `HCEObj` over the bridge, the action of `c` induced by the form is the given
conjugation.  @census none (helper; bridge) -/
theorem _root_.RationalQuivers.Gelfand.HCEObj.galActOf_conj (B : HCEObj ℓ E (D.sqrtExt h)) (v : B.carrier) :
    galActOf D B.setup.baseChange (D.sqrtExt h).conj v = B.setup.conj v := by
  rw [galActOf_apply, galoisTwist_eq_setupConj B.setup, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- **Bridge 3b.** `HCEObj ℓ E (D.sqrtExt h) → HC ℓ E D`: the derived action at `c` **is** the given
conjugation, at `1` it is trivial.  @census none (helper; bridge) -/
noncomputable def _root_.RationalQuivers.Gelfand.HCEObj.toHC (B : HCEObj ℓ E (D.sqrtExt h)) : HC ℓ E D where
  form := B.form
  carrier := B.carrier
  baseChange := B.setup.baseChange
  weight := B.setup.weight
  gic := B.setup.gic
  galCompat σ := by
    rcases D.chi_cases σ with hσ | hσ
    · have h1 := D.eq_one_of_chi_one hσ
      subst h1
      refine ⟨fun n v hv => ?_, fun v => ?_, fun _ v => ?_, fun _ v => ?_, fun h' => ?_,
        fun h' => ?_⟩
      · rw [galActOf_one, hσ]; simpa using hv
      · rw [galActOf_one, galActOf_one, hσ]; simp
      · rw [galActOf_one, galActOf_one]
      · rw [galActOf_one, galActOf_one]
      · rw [hσ] at h'; exact absurd h' (by decide)
      · rw [hσ] at h'; exact absurd h' (by decide)
    · rw [← D.sqrtExt_conj h hσ]
      have hc : D.chi (D.sqrtExt h).conj = -1 := D.chi_sqrtExt_conj h
      refine ⟨fun n v hv => ?_, fun v => ?_, fun h' => ?_, fun h' => ?_, fun _ v => ?_,
        fun _ v => ?_⟩
      · rw [HCEObj.galActOf_conj, hc, Units.val_neg, Units.val_one, neg_one_mul]
        exact B.setup.conj_comp n v hv
      · rw [HCEObj.galActOf_conj, HCEObj.galActOf_conj, hc, Units.val_neg, Units.val_one, neg_one_zsmul]
        exact B.setup.conj_H v
      · rw [hc] at h'; exact absurd h' (by decide)
      · rw [hc] at h'; exact absurd h' (by decide)
      · rw [HCEObj.galActOf_conj, HCEObj.galActOf_conj]; exact B.setup.conj_X v
      · rw [HCEObj.galActOf_conj, HCEObj.galActOf_conj]; exact B.setup.conj_Y v
  admissible := B.admissible
  centralCharacter := B.centralCharacter
  fg := B.fg

/-- On `B.toHC`, `galAct σ` for `χ σ = -1` is the given conjugation.  @census none (helper) -/
theorem _root_.RationalQuivers.Gelfand.HCEObj.toHC_galAct_neg (B : HCEObj ℓ E (D.sqrtExt h)) {σ : D.L ≃ₐ[E] D.L}
    (hσ : D.chi σ = -1) (v : B.carrier) : B.toHC.galAct σ v = B.setup.conj v := by
  show galActOf D B.setup.baseChange σ v = _
  rw [← D.sqrtExt_conj h hσ]
  exact HCEObj.galActOf_conj B v

namespace HC

variable (A : HC ℓ E D)

/-- The round trip `HC → HCEObj → HC` is the identity on every field but the proof of `galCompat`
(a `Prop`).  @census none (helper; bridge) -/
theorem toHCEObj_toHC (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) : (A.toHCEObj h).toHC = A := rfl

end HC

/-- The round trip `HCEObj → HC → HCEObj` is the identity: the conjugation of `B.toHC.setup` is
`galActOf c`, which is `B.setup.conj` by `galActOf_conj`.  @census none (helper; bridge) -/
theorem _root_.RationalQuivers.Gelfand.HCEObj.toHC_toHCEObj (B : HCEObj ℓ E (D.sqrtExt h)) : B.toHC.toHCEObj h = B := by
  obtain ⟨form, carrier, ⟨bc, w, gic, conj, cs, ci, cb, cc, cX, cY, cH⟩, adm, cc', fg⟩ := B
  have hconj : galActOf D bc (D.sqrtExt h).conj = conj := by
    ext v
    exact HCEObj.galActOf_conj (⟨form, carrier, ⟨bc, w, gic, conj, cs, ci, cb, cc, cX, cY, cH⟩, adm, cc',
      fg⟩ : HCEObj ℓ E (D.sqrtExt h)) v
  simp only [HC.toHCEObj, HC.setup, HCEObj.toHC, HCEObj.mk.injEq, heq_eq_eq, true_and,
    RationalSetupOver.mk.injEq, hconj]

/-! ### Morphisms -/

namespace HC

variable {A B : HC ℓ E D}

/-- **Bridge 3a on morphisms.** A morphism of `HC ℓ E D` commutes with `c`.  @census none (helper) -/
noncomputable def Hom.toHCEHom (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) (f : A ⟶ B) :
    A.toHCEObj h ⟶ B.toHCEObj h where
  toLinearMap := (f : Hom A B).toLinearMap
  map_H := (f : Hom A B).map_H
  map_X := (f : Hom A B).map_X
  map_Y := (f : Hom A B).map_Y
  map_comp := (f : Hom A B).map_comp
  map_conj v := (f : Hom A B).map_gal _ v

/-- **Bridge 3b on morphisms.** A morphism of `HCEObj`s over the bridge commutes with every
`σ ∈ G_E` (`σ = 1` trivially, `σ = c` by `map_conj`).  @census none (helper) -/
noncomputable def ofHCEHom {A' B' : HCEObj ℓ E (D.sqrtExt h)} (f : A' ⟶ B') : A'.toHC ⟶ B'.toHC where
  toLinearMap := f.toLinearMap
  map_H := f.map_H
  map_X := f.map_X
  map_Y := f.map_Y
  map_comp := f.map_comp
  map_gal σ v := by
    rcases D.chi_cases σ with hσ | hσ
    · rw [HC.galAct_of_chi_one _ hσ, HC.galAct_of_chi_one _ hσ]
    · rw [HCEObj.toHC_galAct_neg _ hσ, HCEObj.toHC_galAct_neg _ hσ]
      exact f.map_conj v

end HC

end RationalQuivers.HC
