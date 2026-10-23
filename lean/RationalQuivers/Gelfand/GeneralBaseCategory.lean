import RationalQuivers.HC.Category
import RationalQuivers.HC.BaseChange
import RationalQuivers.Gelfand.Split.Construction
import RationalQuivers.Gelfand.QuadraticExtension
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Linear.Basic

/-!
# `HC_λ(𝔤,K)_E` for an arbitrary characteristic-zero `E`

Stage **S10**, prerequisites **(i)** and **(iv)** of census row `RQ-5.08` (`rmk:generalbases`);
coordinator ruling `R-S10-1` (adopt the parity cut in `ObjectProperty.FullSubcategory` form, in a
new S10 module) and `R-S10-8` (module set).  Discharges the standing S7 obligation `O-PF-1`
(`R-S7-14`).

## (iv) The parity cut — what S7 disclosed and this module closes

`HC/IntendedModel.lean`'s `HCObjOver ℓ E` carries **one** of the two conditions that slice
`HC_λ(𝔤,K)_E` out of `HC(𝔤,K)_E`: the generalized infinitesimal character `λ = ℓ²` (its `gic`
field).  It does **not** carry the central character `RQ-3.03-C3`, because on the ℂ side that is
defined through the ℂ-only `K`-action; S7 disclosed the gap, one-directionally
(`HCObjOver ℓ E ⊇ HC_λ(𝔤,K)_E`), and named its `E`-generic rendering: `-1₂` acts on `M_n` by
`χ_n(-1₂) = (-1)^n`, so "acts by `(-1)^{ℓ-1}`" is `M_n = ⊥` whenever `n ≢ ℓ - 1 (mod 2)`.

`parity ℓ E` is exactly that condition, written verbatim as `Gelfand/Category.lean:120`
(`HCQiObj.centralCharacter`) writes it over `ℚ[√-1]`, and `HCLambda ℓ E` is the full subcategory it
cuts out.  Per `R-S10-1`, `HC/IntendedModel.lean` is **not** amended and `HCObjOver` keeps its
fields, so S10 needs no S7 freeze exception; `HCObjOver ℓ E` remains the disclosed ambient.  This
mirrors the ℂ side, which is itself a `FullSubcategory` (`HC/Module.lean:1558`).

`HCLambda` is an `abbrev`, so `Category`, `Preadditive` and `Linear E` are mathlib's
`ObjectProperty` instances rather than re-declarations (three `example`s check this; since v2 WP-8
they are in `HC/Category.lean`, with `parity` and `HCLambda`, last note).

## (i) The non-split `E`-form

For `√-1 ∈ E` the split-torus reading is all that is needed and `HCLambda ℓ E` is the category.
For `√-1 ∉ E` the torus is non-split and, exactly as §3.4 does over `ℚ`, an object is presented
through its base change to the quadratic extension together with a descent datum:
`RationalSetupOver ℓ E Mq Mi` is S7's `HC.RationalSetup` with `(ℚ, ℚ[√-1], galConj)` replaced by
`(E, D', D.conj)`, field for field, and `HCEObj ℓ E` / `HCEHom` mirror
`Gelfand/Category.lean`'s `HCQObj` / `HCQHom` with the same four conditions (admissibility, the
central character, finite generation, and morphisms commuting with the conjugations).

*(WP-15 docstring amendment, 2026-10-19, G2-V2II-F05.)* Since the T2-a2 amendment (variant (ii))
`D : SqrtNegOneExt E` is **any** quadratic Galois extension `D'/E` (its carrier); `D' = E(√-1)` with
`√-1 ∉ E` is §3.4's case, and in general `HCEObj ℓ E D` is `HC_λ(𝔤,K_{D'/E})_E` of `def:HClambdaDE`
(the grading `M_n` replaces the `K`-action, `EX-HC`).  Below, `D'` is the carrier of `D`.

`Linear E (HCEObj ℓ E)` — over `E`, not over `D'`: for a scalar `a` of `D'` the map `a • f`
commutes with the conjugations iff `conj a = a`, i.e. iff `a` lies in `E`.  So the hom-spaces are
`E`-modules by construction, which is the right statement (`HC_λ(𝔤,K)_E` is an `E`-linear
category).

## What is deliberately NOT here

In v1 (S10), the equivalence `𝔼_E` at arbitrary `E` was declined-and-carried, decision `D13` / ruling
`R-S10-6`, `PLAN.md` §5 item (vii).  The v2 line proves it (Theorem B, `Gelfand.gelfand_equivalence`,
`Gelfand/Main.lean`).  This module supplies only **categories** and functors that the v2 statements
use; it states no equivalence.

## Main definitions / results

* `RationalQuivers.HC.parity`, `HC.HCLambda` — prerequisite (iv), `RQ-3.03-C3` over general `E`; in
  `HC/Category.lean` since v2 WP-8 (last note), used here.
* `HC.stdHCObjOver_parity`, `HC.stdHCLambda` — the G5.2 witness survives the cut (probe `P7`); in
  `HC/Category.lean` since v2 WP-8.
* `RationalSetupOver`, `HCEObj`, `HCEHom`, `instCategoryHCEObj`, `instPreadditiveHCEObj`,
  `instLinearHCEObj` — prerequisite (i), the non-split `E`-form.
* `hcBaseChange`, `hcBaseChange_self_iso`, `forgetDescent`, `hcBaseChangeNS` — the HC-side base-change
  functors; `trivialRationalSetupOver`, `trivialHCEObj`, `trivialHCEHom` — G5 inhabitants.

*(v2 WP-13, 2026-10-18: module kept in place and assigned to stage T5 by WP-13 option I (stage T2 since
the perimeter amendment T2-a1 of 2026-10-18, `STAGE-MAP.tsv`); its import of the
deleted v1 `Gelfand/Category.lean` and the comparison block `hcLambdaToQi` … `hcLambdaQiEquiv_functor` with
S8's `HCQi ℓ` were removed with the v1 Q-chain. References above to `Gelfand/Category.lean`, `HCQObj` and
`HCQHom` are historical.)*

*(2026-10-21, O-V2-6.)*  Moves of the v2 line that the S10 text above predates.  At v2 WP-8
(`d2a2a47`, 2026-10-17) `parity`, `HCLambda`, the three `example`s, `stdHCObjOver_parity` and
`stdHCLambda` moved from this module to `HC/Category.lean` (namespace `Gelfand` → `HC`), where
`HCObjOver` also lives; v1's `HC/IntendedModel.lean` was archived as `Archive/HC/IntendedModel.lean`,
and v1's `HC/Module.lean` became `HC/Classical.lean`.  S7's `HC.RationalSetup` and
`HC.trivialRationalSetup`, and S8's `Gelfand.trivialWeightData_isFG` and
`Gelfand.trivialWeightData_centralCharacter`, which the docstrings below name as the `ℚ` forms, were
deleted at WP-13 (`9c6b193`).
-/

universe u

namespace RationalQuivers.Gelfand

open RationalQuivers.HC CategoryTheory
open scoped TensorProduct

/-! ## `C4a`, split half: base change between the parity cuts -/

/-- The parity condition is stable under base change: `⊥` base-changes to `⊥`.

@census none (helper) -/
theorem parity_baseChange {ℓ : ℕ} {E : Type u} [Field E] [CharZero E] {E'' : Type u} [Field E'']
    [CharZero E''] [Algebra E E''] {A : HCObjOver.{u} ℓ E} (hA : parity ℓ E A) :
    parity ℓ E'' (A.baseChange (E'' := E'')) := by
  intro n hn
  show (A.weight.comp n).baseChange E'' = ⊥
  rw [hA n hn, Submodule.baseChange_bot]

/-- **`RQ-5.08-C4a`, split → split**: the base-change functor
`HC_λ(𝔤,K)_E → HC_λ(𝔤,K)_{E''}` for an **arbitrary** `E → E''`, `M ↦ E'' ⊗_E M`.  Constructed,
not assumed: this is the HC-side vertical arrow of `C4`'s `ss` square.

@census none (helper; `RQ-5.08-C4`) -/
noncomputable def hcBaseChange (ℓ : ℕ) (E E'' : Type u) [Field E] [CharZero E] [Field E'']
    [CharZero E''] [Algebra E E''] : HCLambda.{u} ℓ E ⥤ HCLambda.{u} ℓ E'' :=
  (parity ℓ E'').lift ((parity ℓ E).ι ⋙ HC.hcBaseChangeObj ℓ E E'')
    (fun A => parity_baseChange A.property)

/-- **Base change along the identity extension is naturally isomorphic to the identity**, on the
parity cut.  The unit isomorphism `RQ-5.08-C4b`'s `ss` square needs on the HC side; it descends
from `HC.hcBaseChangeObj_self_iso` through the full subcategory, since `hcBaseChange` is that
functor lifted.

@census none (helper; `RQ-5.08-C4b`) -/
noncomputable def hcBaseChange_self_iso (ℓ : ℕ) (E : Type u) [Field E] [CharZero E] :
    hcBaseChange ℓ E E ≅ 𝟭 (HCLambda.{u} ℓ E) :=
  CategoryTheory.NatIso.ofComponents
    (fun A => CategoryTheory.ObjectProperty.isoMk (parity ℓ E)
      ((HC.hcBaseChangeObj_self_iso ℓ E).app A.obj))
    (fun {_ _} f => by
      apply CategoryTheory.ObjectProperty.hom_ext
      exact (HC.hcBaseChangeObj_self_iso ℓ E).hom.naturality f.hom)

/-! ## (i) The non-split `E`-form: `HC_λ(𝔤,K)_E` for `√-1 ∉ E` -/

section Form

variable (ℓ : ℕ) (E : Type u) [Field E] [CharZero E] (D : SqrtNegOneExt E)

/-- §3.4's standing setup over an arbitrary characteristic-zero `E` and a quadratic Galois
extension `D'/E` (the carrier of `D`; `D' = E(√-1)` for `√-1 ∉ E` is §3.4's case):
S7's `HC.RationalSetup`, with `(ℚ, ℚ[√-1], galConj)` replaced by `(E, D', D.conj)`.

@census none (helper) -/
structure RationalSetupOver
    (Mq : Type u) [AddCommGroup Mq] [Module E Mq]
    (Mi : Type u) [AddCommGroup Mi] [Module D.carrier Mi] where
  /-- `M_{D'} = D' ⊗_E M_E`: the base change of the `E`-form. -/
  baseChange : (D.carrier ⊗[E] Mq) ≃ₗ[D.carrier] Mi
  /-- the decomposition `M_{D'} = ⊕ M_n` (for `D' = E(√-1)`, `M_n = M_{D'}[χ_n]`), and the action
  of the triple `H, X, Y`. -/
  weight : WeightData D.carrier Mi
  /-- `λ = ℓ²`. -/
  gic : HasGeneralizedInfinitesimalCharacter weight ℓ
  /-- the action of the non-trivial element `c` of `Gal(D'/E)` on `M_{D'}`, additive... -/
  conj : Mi ≃+ Mi
  /-- ... and semilinear over `D.conj`. -/
  conj_smul : ∀ (a : D.carrier) (v : Mi), conj (a • v) = D.conj a • conj v
  /-- it is an involution. -/
  conj_involutive : Function.Involutive conj
  /-- it is the Galois action induced by the `E`-form: it fixes `1 ⊗ v`. -/
  conj_baseChange : ∀ v : Mq, conj (baseChange ((1 : D.carrier) ⊗ₜ[E] v))
    = baseChange ((1 : D.carrier) ⊗ₜ[E] v)
  /-- it sends `M_n` to `M_{-n}`. -/
  conj_comp : ∀ (n : ℤ) (v : Mi), v ∈ weight.comp n → conj v ∈ weight.comp (-n)
  /-- `cX = Y`. -/
  conj_X : ∀ v, conj (weight.X v) = weight.Y (conj v)
  /-- `cY = X`. -/
  conj_Y : ∀ v, conj (weight.Y v) = weight.X (conj v)
  /-- `cH = -H`. -/
  conj_H : ∀ v, conj (weight.H v) = -weight.H (conj v)

/-- **An object of `HC_λ(𝔤,K_{D'/E})_E`** (`def:HClambdaDE`; for `√-1 ∉ E` and `D' = E(√-1)` this
is `HC_λ(𝔤,K)_E`): an `E`-form presented, as §3.4 presents it, through its base change to `D'` with
the induced conjugation, subject to admissibility, the central character and finite generation.

@census none (helper) -/
structure HCEObj : Type (u + 1) where
  /-- the `E`-form `M_E` -/
  form : Type u
  [formAddCommGroup : AddCommGroup form]
  [formModule : Module E form]
  /-- the `D'`-form `M_{D'}` -/
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module D.carrier carrier]
  /-- §3.4's standing setup -/
  setup : RationalSetupOver ℓ E D form carrier
  /-- admissibility -/
  admissible : ∀ n : ℤ, FiniteDimensional D.carrier (setup.weight.comp n)
  /-- the central character -/
  centralCharacter : ∀ n : ℤ, (n - ((ℓ : ℤ) - 1)) % 2 ≠ 0 → setup.weight.comp n = ⊥
  /-- finite generation -/
  fg : setup.weight.IsFG

attribute [instance] HCEObj.formAddCommGroup HCEObj.formModule HCEObj.addCommGroup HCEObj.module

/-- A morphism of `HC_λ(𝔤,K_{D'/E})_E`: a morphism of the `D'`-forms commuting with the
conjugations — exactly the maps that descend to the `E`-forms.

@census none (helper) -/
structure HCEHom {ℓ : ℕ} {E : Type u} [Field E] [CharZero E] {D : SqrtNegOneExt E}
    (A B : HCEObj ℓ E D) where
  /-- the underlying `D'`-linear map -/
  toLinearMap : A.carrier →ₗ[D.carrier] B.carrier
  /-- it commutes with `H` -/
  map_H : ∀ v, toLinearMap (A.setup.weight.H v) = B.setup.weight.H (toLinearMap v)
  /-- it commutes with `X` -/
  map_X : ∀ v, toLinearMap (A.setup.weight.X v) = B.setup.weight.X (toLinearMap v)
  /-- it commutes with `Y` -/
  map_Y : ∀ v, toLinearMap (A.setup.weight.Y v) = B.setup.weight.Y (toLinearMap v)
  /-- it preserves the grading -/
  map_comp : ∀ (n : ℤ) (v : A.carrier), v ∈ A.setup.weight.comp n →
    toLinearMap v ∈ B.setup.weight.comp n
  /-- it commutes with the conjugations -/
  map_conj : ∀ v, toLinearMap (A.setup.conj v) = B.setup.conj (toLinearMap v)

end Form

/-! ### Projections (`rqaudit liveness`: every field is projected by a named declaration) -/

namespace RationalSetupOver

variable {ℓ : ℕ} {E : Type u} [Field E] [CharZero E] {D : SqrtNegOneExt E}
  {Mq : Type u} [AddCommGroup Mq] [Module E Mq]
  {Mi : Type u} [AddCommGroup Mi] [Module D.carrier Mi] (S : RationalSetupOver ℓ E D Mq Mi)

/-- Projection of `baseChange`: the `E`-form really is carried.  @census none (helper) -/
theorem baseChange' (S' : RationalSetupOver ℓ E D Mq Mi) :
    Nonempty ((D.carrier ⊗[E] Mq) ≃ₗ[D.carrier] Mi) := ⟨S'.baseChange⟩

/-- Projection of `gic`.  @census none (helper) -/
theorem gic' : HasGeneralizedInfinitesimalCharacter S.weight ℓ := S.gic

/-- Projection of `conj_smul`.  @census none (helper) -/
theorem conj_smul' (a : D.carrier) (v : Mi) : S.conj (a • v) = D.conj a • S.conj v :=
  S.conj_smul a v

/-- Projection of `conj_involutive`.  @census none (helper) -/
theorem conj_involutive' : Function.Involutive S.conj := S.conj_involutive

/-- Projection of `conj_baseChange`.  @census none (helper) -/
theorem conj_baseChange' (v : Mq) :
    S.conj (S.baseChange ((1 : D.carrier) ⊗ₜ[E] v))
      = S.baseChange ((1 : D.carrier) ⊗ₜ[E] v) :=
  S.conj_baseChange v

/-- Projection of `conj_comp`.  @census none (helper) -/
theorem conj_comp' (n : ℤ) (v : Mi) (hv : v ∈ S.weight.comp n) :
    S.conj v ∈ S.weight.comp (-n) := S.conj_comp n v hv

/-- Projection of `conj_X`.  @census none (helper) -/
theorem conj_X' (v : Mi) : S.conj (S.weight.X v) = S.weight.Y (S.conj v) := S.conj_X v

/-- Projection of `conj_Y`.  @census none (helper) -/
theorem conj_Y' (v : Mi) : S.conj (S.weight.Y v) = S.weight.X (S.conj v) := S.conj_Y v

/-- Projection of `conj_H`.  @census none (helper) -/
theorem conj_H' (v : Mi) : S.conj (S.weight.H v) = -S.weight.H (S.conj v) := S.conj_H v

end RationalSetupOver

namespace HCEObj

variable {ℓ : ℕ} {E : Type u} [Field E] [CharZero E] {D : SqrtNegOneExt E} (A : HCEObj ℓ E D)

/-- Projection of `admissible` (`RQ-3.11-C2`).  @census none (helper) -/
theorem admissible' (n : ℤ) : FiniteDimensional D.carrier (A.setup.weight.comp n) :=
  A.admissible n

/-- Projection of `centralCharacter` (`RQ-3.03-C3`).  @census none (helper) -/
theorem centralCharacter' (n : ℤ) (hn : (n - ((ℓ : ℤ) - 1)) % 2 ≠ 0) :
    A.setup.weight.comp n = ⊥ := A.centralCharacter n hn

/-- Projection of `fg` (`RQ-3.11-C1`).  @census none (helper) -/
theorem fg' : A.setup.weight.IsFG := A.fg

end HCEObj

namespace HCEHom

variable {ℓ : ℕ} {E : Type u} [Field E] [CharZero E] {D : SqrtNegOneExt E} {A B : HCEObj ℓ E D}

@[ext] theorem hom_ext {f g : HCEHom A B} (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f; cases g; simp_all

theorem toLinearMap_injective : Function.Injective (HCEHom.toLinearMap : HCEHom A B → _) :=
  fun _ _ h => hom_ext h

end HCEHom

variable {ℓ : ℕ} {E : Type u} [Field E] [CharZero E] {D : SqrtNegOneExt E}

/-- **`HC_λ(𝔤,K_{D'/E})_E`** as a category.  @census none (helper) -/
noncomputable instance instCategoryHCEObj : Category (HCEObj ℓ E D) where
  Hom A B := HCEHom A B
  id A := ⟨LinearMap.id, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ _ h => h, fun _ => rfl⟩
  comp f g :=
    ⟨g.toLinearMap.comp f.toLinearMap,
      fun v => by simp [f.map_H, g.map_H],
      fun v => by simp [f.map_X, g.map_X],
      fun v => by simp [f.map_Y, g.map_Y],
      fun n v hv => g.map_comp n _ (f.map_comp n v hv),
      fun v => by simp [f.map_conj, g.map_conj]⟩
  id_comp _ := by apply HCEHom.hom_ext; rfl
  comp_id _ := by apply HCEHom.hom_ext; rfl
  assoc _ _ _ := by apply HCEHom.hom_ext; rfl

namespace HCEHom

variable {A B : HCEObj ℓ E D}

noncomputable instance : Zero (HCEHom A B) :=
  ⟨⟨0, fun _ => by simp, fun _ => by simp, fun _ => by simp, fun n v _ => by simp,
    fun _ => by simp⟩⟩

noncomputable instance : Add (HCEHom A B) :=
  ⟨fun f g => ⟨f.toLinearMap + g.toLinearMap,
    fun v => by simp [f.map_H, g.map_H],
    fun v => by simp [f.map_X, g.map_X],
    fun v => by simp [f.map_Y, g.map_Y],
    fun n v hv => by
      simpa using Submodule.add_mem _ (f.map_comp n v hv) (g.map_comp n v hv),
    fun v => by simp [f.map_conj, g.map_conj]⟩⟩

noncomputable instance : Neg (HCEHom A B) :=
  ⟨fun f => ⟨-f.toLinearMap,
    fun v => by simp [f.map_H],
    fun v => by simp [f.map_X],
    fun v => by simp [f.map_Y],
    fun n v hv => by simpa using Submodule.neg_mem _ (f.map_comp n v hv),
    fun v => by simp [f.map_conj]⟩⟩

noncomputable instance : Sub (HCEHom A B) :=
  ⟨fun f g => ⟨f.toLinearMap - g.toLinearMap,
    fun v => by simp [f.map_H, g.map_H],
    fun v => by simp [f.map_X, g.map_X],
    fun v => by simp [f.map_Y, g.map_Y],
    fun n v hv => by
      simpa using Submodule.sub_mem _ (f.map_comp n v hv) (g.map_comp n v hv),
    fun v => by simp [f.map_conj, g.map_conj]⟩⟩

noncomputable instance : SMul ℕ (HCEHom A B) :=
  ⟨fun k f => ⟨k • f.toLinearMap,
    fun v => by simp [f.map_H],
    fun v => by simp [f.map_X],
    fun v => by simp [f.map_Y],
    fun n v hv => by simpa using nsmul_mem (f.map_comp n v hv) k,
    fun v => by simp [f.map_conj]⟩⟩

noncomputable instance : SMul ℤ (HCEHom A B) :=
  ⟨fun k f => ⟨k • f.toLinearMap,
    fun v => by simp [f.map_H],
    fun v => by simp [f.map_X],
    fun v => by simp [f.map_Y],
    fun n v hv => by simpa using zsmul_mem (f.map_comp n v hv) k,
    fun v => by simp [f.map_conj]⟩⟩

/-- Scalar multiplication by `E` (not by `D'`: only the `Gal(D'/E)`-invariant scalars
preserve the compatibility with the conjugations).

@census none (helper) -/
noncomputable instance : SMul E (HCEHom A B) :=
  ⟨fun c f => ⟨(algebraMap E D.carrier c) • f.toLinearMap,
    fun v => by simp [f.map_H],
    fun v => by simp [f.map_X],
    fun v => by simp [f.map_Y],
    fun n v hv => by
      simpa using Submodule.smul_mem _ (algebraMap E D.carrier c) (f.map_comp n v hv),
    fun v => by
      simp only [LinearMap.smul_apply, f.map_conj]
      rw [B.setup.conj_smul, AlgEquiv.commutes]⟩⟩

noncomputable instance instAddCommGroup : AddCommGroup (HCEHom A B) :=
  Function.Injective.addCommGroup HCEHom.toLinearMap toLinearMap_injective rfl
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

@[simp] theorem smul_toLinearMap (c : E) (f : HCEHom A B) :
    (c • f).toLinearMap = (algebraMap E D.carrier c) • f.toLinearMap := rfl

@[simp] theorem zero_toLinearMap : (0 : HCEHom A B).toLinearMap = 0 := rfl

@[simp] theorem add_toLinearMap (f g : HCEHom A B) :
    (f + g).toLinearMap = f.toLinearMap + g.toLinearMap := rfl

noncomputable instance instModule : Module E (HCEHom A B) where
  one_smul f := by
    apply hom_ext; simp only [smul_toLinearMap, map_one, one_smul]
  mul_smul a b f := by
    apply hom_ext; simp only [smul_toLinearMap, map_mul, mul_smul]
  smul_zero a := by
    apply hom_ext; simp only [smul_toLinearMap, zero_toLinearMap, smul_zero]
  smul_add a f g := by
    apply hom_ext; simp only [smul_toLinearMap, add_toLinearMap, smul_add]
  add_smul a b f := by
    apply hom_ext; simp only [smul_toLinearMap, add_toLinearMap, map_add, add_smul]
  zero_smul f := by
    apply hom_ext; simp only [smul_toLinearMap, zero_toLinearMap, map_zero, zero_smul]

@[simp] theorem comp_toLinearMap {C : HCEObj ℓ E D} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).toLinearMap = g.toLinearMap.comp f.toLinearMap := rfl

end HCEHom

/-- `HC_λ(𝔤,K_{D'/E})_E` is **preadditive**.  @census none (helper) -/
noncomputable instance instPreadditiveHCEObj : Preadditive (HCEObj ℓ E D) where
  homGroup A B := (inferInstance : AddCommGroup (HCEHom A B))
  add_comp _ _ _ _ _ _ := by apply HCEHom.hom_ext; exact LinearMap.comp_add _ _ _
  comp_add _ _ _ _ _ _ := by apply HCEHom.hom_ext; exact LinearMap.add_comp _ _ _

/-- `HC_λ(𝔤,K_{D'/E})_E` is **`E`-linear**.  @census none (helper) -/
noncomputable instance instLinearHCEObj : Linear E (HCEObj ℓ E D) where
  homModule A B := (inferInstance : Module E (HCEHom A B))
  smul_comp _ _ _ r f g := by
    apply HCEHom.hom_ext
    refine LinearMap.ext fun v => ?_
    show g.toLinearMap ((algebraMap E D.carrier r) • f.toLinearMap v)
        = (algebraMap E D.carrier r) • g.toLinearMap (f.toLinearMap v)
    exact map_smul _ _ _
  comp_smul _ _ _ f r g := by
    apply HCEHom.hom_ext
    refine LinearMap.ext fun v => ?_
    rfl

/-! ## Forgetting the descent datum: `HC_λ(𝔤,K_{D'/E})_E → HC_λ(𝔤,K)_{D'}` -/

section Forget

variable {ℓ : ℕ} {E : Type u} [Field E] [CharZero E] {D : SqrtNegOneExt E}

/-- An `E`-form, read as an object over its own splitting field: forget the `E`-structure and the
conjugation, keep the weight decomposition.  `HCObjOver.fg` and `WeightData.IsFG` are the same
condition — `HC.gkSpanOver` and `Gelfand.gkSpanGraded` have identical definitions — so `fg`
transfers on the nose.

@census none (helper) -/
def HCEObj.toObjOver (A : HCEObj ℓ E D) : HCObjOver.{u} ℓ D.carrier where
  carrier := A.carrier
  weight := A.setup.weight
  gic := A.setup.gic
  fg := A.fg
  admissible := A.admissible

theorem HCEObj.toObjOver_parity (A : HCEObj ℓ E D) : parity ℓ D.carrier A.toObjOver :=
  A.centralCharacter

variable (ℓ E D) in
/-- **Forgetting the descent datum**, as a functor `HC_λ(𝔤,K_{D'/E})_E ⥤ HC_λ(𝔤,K)_{D'}` (the
split category over the field `D'`).  This is
the left half of `RQ-5.08-C4a`'s `ns` arrow: over a splitting field the `E`-form's Galois datum is
exactly what base change to a field containing `√-1` discards.

@census none (helper; `RQ-5.08-C4`) -/
noncomputable def forgetDescent : HCEObj ℓ E D ⥤ HCLambda.{u} ℓ D.carrier :=
  { obj := fun A => ⟨A.toObjOver, A.toObjOver_parity⟩
    map := fun f =>
      ⟨{ toLinearMap := f.toLinearMap
         map_H := f.map_H
         map_X := f.map_X
         map_Y := f.map_Y }⟩
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

end Forget

/-! ## `RQ-5.08-C4a`, `ns`: the HC-side arrow -/

/-- **`RQ-5.08-C4a`, `ns`, HC side**: `HC_λ(𝔤,K)_E ⥤ HC_λ(𝔤,K)_{E''}` for `√-1 ∉ E`, `√-1 ∈ E''`.
Constructed as the composite of `forgetDescent` (discard the Galois datum, landing over `D'`)
with `hcBaseChange` (tensor up along `D' → E''`); in `RQ-5.08-C4a`'s case `D' = E(√-1)`, which is
how the disclosure below reads (WP-15 docstring amendment, G2-V2II-F05).

*(Disclosure, 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S10, coordinator ruling
`R-FR-9`, final-release WP-16c, on layer-2 finding `V3-02` of `VERIFICATION-REVIEW-2.md`.)* So this
functor is `M_E ↦ E'' ⊗_{E(√-1)} M_{E(√-1)}` on the underlying `E(√-1)`-object, **not** literally
the `M_E ↦ E'' ⊗_E M_E` of `rmk:generalbases` (*Base change*). The two agree by the canonical
isomorphism `E'' ⊗_E M_E ≅ E'' ⊗_{E(√-1)} (E(√-1) ⊗_E M_E)`, which is not stated here as a
theorem. Consequently, in the non-split → split shape of (T1) (`RQ-5.08-C4`, witnessed by
`GF.E_E_baseChange_compat`, since WP-11 `Gelfand.BaseChange.E_E_baseChange_compat` in
`Gelfand/BaseChange/Main.lean`), both vertical functors of the square are stated on the underlying
`E(√-1)`-objects; the quiver-side one is `qBCnsRel`.

@census none (helper; `RQ-5.08-C4`) -/
noncomputable def hcBaseChangeNS (ℓ : ℕ) (E : Type u) [Field E] [CharZero E] (D : SqrtNegOneExt E)
    (E'' : Type u) [Field E''] [CharZero E''] [Algebra D.carrier E''] :
    HCEObj ℓ E D ⥤ HCLambda.{u} ℓ E'' :=
  forgetDescent ℓ E D ⋙ hcBaseChange ℓ D.carrier E''

/-! ## G5 inhabitants for the non-split `E`-form -/

section Witness

variable (E : Type u) [Field E] [CharZero E] (D : SqrtNegOneExt E)

/-- The one-dimensional `WeightData` over a field, concentrated in degree `0`, is finitely
generated as a `(𝔤,K)`-module.  The general-`E` form of `Gelfand.trivialWeightData_isFG`.

@census none (helper) -/
theorem trivialWeightData_isFG_self (F : Type u) [Field F] :
    (trivialWeightData F F).IsFG := by
  refine ⟨{1}, gkSpanGraded_eq_top _ fun N hN _ _ => ?_⟩
  rw [eq_top_iff]
  intro v _
  have h1 : (1 : F) ∈ N := hN (by simp)
  have : v = v • (1 : F) := by simp
  rw [this]
  exact N.smul_mem v h1

/-- The one-dimensional `WeightData` satisfies the `ℓ = 1` central character.  The general-`E`
form of `Gelfand.trivialWeightData_centralCharacter`.

@census none (helper) -/
theorem trivialWeightData_centralCharacter_self (F : Type u) [Field F] (n : ℤ)
    (hn : (n - ((1 : ℕ) - 1 : ℤ)) % 2 ≠ 0) : (trivialWeightData F F).comp n = ⊥ := by
  have h0 : n ≠ 0 := by rintro rfl; simp at hn
  exact topAtZero_ne_zero h0

/-- **G5 inhabitant of `RationalSetupOver`**: the `E`-form `E` of the one-dimensional
`D'`-module, with the Galois involution `D.conj`.  The general-`E` form of S7's
`HC.trivialRationalSetup`.

@census none (G5 inhabitant) -/
noncomputable def trivialRationalSetupOver : RationalSetupOver 1 E D E D.carrier where
  baseChange := TensorProduct.AlgebraTensorModule.rid E (D.carrier) (D.carrier)
  weight := trivialWeightData (D.carrier) (D.carrier)
  gic := by
    refine ⟨1, ?_⟩
    rw [pow_one, trivialWeightData_casimir]
    simp
  conj := D.conj.toAddEquiv
  conj_smul a v := by
    show D.conj (a * v) = D.conj a * D.conj v
    exact map_mul _ _ _
  conj_involutive v := D.conj_conj v
  conj_baseChange v := by
    show D.conj (TensorProduct.AlgebraTensorModule.rid E (D.carrier) (D.carrier)
      ((1 : D.carrier) ⊗ₜ[E] v)) = _
    rw [TensorProduct.AlgebraTensorModule.rid_tmul, ← Algebra.algebraMap_eq_smul_one]
    exact D.conj.commutes v
  conj_comp n v hv := by
    by_cases h : n = 0
    · subst h
      show D.conj v ∈ topAtZero (D.carrier) (D.carrier) (-0)
      rw [neg_zero]
      exact mem_topAtZero_zero _
    · have hv' : v ∈ topAtZero (D.carrier) (D.carrier) n := hv
      rw [topAtZero_ne_zero h, Submodule.mem_bot] at hv'
      subst hv'
      show D.conj 0 ∈ _
      rw [map_zero]
      exact Submodule.zero_mem _
  conj_X v := by
    show D.conj ((0 : Module.End (D.carrier) (D.carrier)) v)
      = (0 : Module.End (D.carrier) (D.carrier)) (D.conj v)
    simp
  conj_Y v := by
    show D.conj ((0 : Module.End (D.carrier) (D.carrier)) v)
      = (0 : Module.End (D.carrier) (D.carrier)) (D.conj v)
    simp
  conj_H v := by
    show D.conj ((0 : Module.End (D.carrier) (D.carrier)) v)
      = -(0 : Module.End (D.carrier) (D.carrier)) (D.conj v)
    simp

/-- **G5 inhabitant of `HCEObj`**: the `E`-form `E` of the one-dimensional module, an object of
`HC_λ(𝔤,K_{D'/E})_E` at `ℓ = 1`, for every quadratic `D'/E`.  Non-degenerate: its carrier is nontrivial
(`trivialHCEObj_nontrivial`).

@census none (G5 inhabitant) -/
noncomputable def trivialHCEObj : HCEObj 1 E D where
  form := E
  carrier := D.carrier
  setup := trivialRationalSetupOver E D
  admissible _ := inferInstance
  centralCharacter := trivialWeightData_centralCharacter_self (D.carrier)
  fg := trivialWeightData_isFG_self (D.carrier)

theorem trivialHCEObj_nontrivial : Nontrivial (trivialHCEObj E D).carrier :=
  inferInstanceAs (Nontrivial D.carrier)

/-- **G5 inhabitant of `HCEHom`**: the identity of the trivial object.  @census none -/
noncomputable def trivialHCEHom : HCEHom (trivialHCEObj E D) (trivialHCEObj E D) :=
  𝟙 (trivialHCEObj E D)

example : Nonempty (HCEObj 1 ℚ SqrtNegOneExt.qi) := ⟨trivialHCEObj ℚ SqrtNegOneExt.qi⟩

end Witness

end RationalQuivers.Gelfand
