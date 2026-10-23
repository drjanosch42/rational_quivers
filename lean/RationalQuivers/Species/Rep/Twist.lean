import RationalQuivers.Quiver.Rep.Basic
import RationalQuivers.Descent.KStructure
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Complex.Module

/-!
# The twisted base change `V ⊗_{E,σ} L`

Supporting material for §2.6 of `latex/rational_quivers.tex`. `RQ2-2.19` – `RQ2-2.23` are all
statements about `V ⊗_{L(v),σ} L`: the base change of a vector space along the embedding of an
intermediate field `E ⊆ L` **twisted by a Galois element** `σ`. `census/NOTATION.md` §2 defines the
twisted tensor product; the tree did not have it (stage S0 built the *untwisted* `L ⊗_K V` with a
semi-linear action, `Descent/KStructure.lean`).

## Finding **S5-F4** — why this is a `structure` and not a type synonym

The obvious construction is mathlib's type-synonym trick, `def Twist E σ := L` with the twisted
`Algebra E (Twist E σ)` registered on the synonym. Stage S5's design notes prescribed exactly that,
**and it is wrong** — measured 2026-08-30, before any of `RQ2-2.19` – `RQ2-2.23` was written.

Everything about the synonym compiles: `Field (Twist E σ)`, the twisted `Algebra`,
`algebraMap E (Twist E σ) a = σ a` **by `rfl`**, `Module L (Twist E σ)`, and the base change
`Twist E σ ⊗[E] V`. But `a • x` for `a : E` does **not** use the twisted action: the elaborated
term is

```
@HSMul.hSMul ↥E (Twist E σ) (Twist E σ) (@instHSMul ↥E (Twist E σ) E.instSMulSubtypeMem) a x
```

— `IntermediateField`'s own **untwisted** `SMul ↥E L`, found straight through the synonym, because a
plain `def` does not stop instance search from seeing `L`. A statement of `RQ2-2.19` – `RQ2-2.23`
written with `•` would then silently assert the **untwisted** base change: it elaborates, it looks
right, it cites the correct clauses, and it says strictly less than the source. That is a
`WEAKENED_OR_PARTIAL` no clause checker can catch.

So `Twist` is a genuine one-field `structure`, which instance search cannot see through, and
**`Twist.smul_def` is the first lemma in the module** with its elaborated form checked
(`CONVENTIONS.md` §3): the `SMul` it names is `Algebra.toSMul … Twist.algebra`, the twisted one.
`Twist.smul_ne_untwisted` is the non-vacuity witness — for a `σ` that moves a point of `E`, the
twisted action really differs from the untwisted one, so the distinction this module exists to
preserve is not empty.

## Main definitions / results
* `RationalQuivers.Twist` — `L` carrying the `E`-algebra structure `a ↦ σ(a)`.
* `RationalQuivers.Twist.smul_def`, `.algebraMap_apply` — the twist, in the signature.
* `RationalQuivers.Twist.smul_ne_untwisted` — the twist is not vacuous.
* `RationalQuivers.Twist.instModuleL`, `.instSMulCommClass` — what makes `Twist E σ ⊗[E] V` an
  `L`-vector space, which is the shape `eq:Leepsilondecomposition` and its successors need.
-/

universe u

namespace RationalQuivers

open scoped TensorProduct

/-- **The twisted scalars `L_σ` over an intermediate field `E`.** A one-field wrapper on `L`,
carrying the `E`-algebra structure in which `a ∈ E` acts as multiplication by `σ(a)` rather than by
`a`. The wrapper is not decoration: see finding **S5-F4** in the module header.

@census none (project definition, `DEF-S5-03`; `census/NOTATION.md` §2's `V ⊗_{K,σ} W`)
-/
structure Twist {K L : Type u} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) (σ : Gal(L/K)) : Type u where
  /-- Wrap an element of `L`. -/
  ofL ::
  /-- The underlying element of `L`. -/
  val : L

namespace Twist

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {E : IntermediateField K L} {σ : Gal(L/K)}

@[simp] theorem val_ofL (a : L) : (ofL a : Twist E σ).val = a := rfl

@[simp] theorem ofL_val (x : Twist E σ) : ofL x.val = x := rfl

theorem val_injective : Function.Injective (Twist.val : Twist E σ → L) :=
  fun x y h => by cases x; cases y; exact congrArg ofL h

/-- `Twist E σ` and `L` are the same type; the field structure is transported along this.

@census none (helper)
-/
def equivL : Twist E σ ≃ L where
  toFun := Twist.val
  invFun := ofL
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instField : Field (Twist E σ) := equivL.field

@[simp] theorem val_mul (x y : Twist E σ) : (x * y).val = x.val * y.val := rfl
@[simp] theorem val_add (x y : Twist E σ) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_one : (1 : Twist E σ).val = 1 := rfl
@[simp] theorem val_zero : (0 : Twist E σ).val = 0 := rfl

/-- **The twisted `E`-algebra structure**: `a ∈ E` acts through `σ`.

@census none (project definition, `DEF-S5-03`)
-/
noncomputable instance algebra : Algebra E (Twist E σ) :=
  RingHom.toAlgebra
    { toFun := fun a => ofL (σ (a : L))
      map_one' := by apply val_injective; simp
      map_mul' := fun a b => by apply val_injective; simp
      map_zero' := by apply val_injective; simp
      map_add' := fun a b => by apply val_injective; simp }

/-! ### `TwistBase` — the base ring, respelled  (finding **S5-F5**)

**Read this before touching the instances below.**  `Twist.algebra` above is the twisted
`E`-algebra structure, and it is *correct*; but it does **not win** instance synthesis.  `Twist E σ`
carries `Module L` (needed to make the base change an `L`-vector space), and `IntermediateField`'s
`SetLike` machinery derives a competing `SMul ↥E X` from *any* `SMul L X` — the **untwisted** one.
So `#synth Module ↥E (Twist E σ)` returns `E.instModuleSubtypeMem` and `Twist E σ ⊗[↥E] W` is
balanced over the wrong action.  That is finding **S5-F5**, and it made `RQ2-2.21` *false* as first
frozen: its defining formula `a ⊗ m ↦ a · φ_σ(m)` is well defined only when `σ` fixes `E`.

This is **S5-F4 recurring in the same file**.  S5-F4 was the same bug for a plain type synonym; the
fix was the `structure` wrapper `Twist` plus a `#check`-verified `smul_def`.  That verification was
valid *when written* — `instSMulL` did not yet exist above it, and instance resolution is
position-dependent within a module.  Adding the `L`-structure later re-created the competitor
*below* `smul_def`, which therefore kept passing while the module as a whole had regressed.

> **The two-guard rule** (accepted into `CONVENTIONS.md` §3).  `smul_def` proves the intended
> action **exists**.  It does not prove it **wins**.  The discriminating test is `#synth`, it must
> be re-run after *any* later instance is added to the same carrier, and — because resolution is
> position-dependent — the guard must sit at the **end of the module**, after every instance.
> Both guards are mandatory; see `§ Guards` at the bottom of this file.

The repair is to respell the *base ring*.  `TwistBase E σ` is a one-field **structure** wrapper of
`↥E` — deliberately not a `def` synonym, since a synonym would leak `↥E`'s instances straight back
in and recreate the very class of bug being fixed (S5-F4's own rule, applied to the base).  Because
it is a structure, no `SetLike` path can reach it, so the twisted
`Module (TwistBase E σ) (Twist E σ)` is the *only* one in scope and cannot be shadowed.

@census none (project definition, `DEF-S5-04`)
-/

/-- The base ring `E`, respelled as a structure so that no `SetLike` instance of `↥E` can reach it.
@census none (project definition, `DEF-S5-04`) -/
structure TwistBase (E : IntermediateField K L) (σ : Gal(L/K)) : Type u where
  /-- Wrap an element of `E`. -/
  ofE ::
  /-- The underlying element of `E`. -/
  val : ↥E

namespace TwistBase

theorem val_injective : Function.Injective (TwistBase.val : TwistBase E σ → ↥E) :=
  fun x y h => by cases x; cases y; exact congrArg ofE h

/-- `TwistBase E σ` and `↥E` are the same type; the field structure is transported along this. -/
def equivE : TwistBase E σ ≃ ↥E where
  toFun := TwistBase.val
  invFun := ofE
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instField : Field (TwistBase E σ) := equivE.field

@[simp] theorem val_mul (x y : TwistBase E σ) : (x * y).val = x.val * y.val := rfl
@[simp] theorem val_add (x y : TwistBase E σ) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_one : (1 : TwistBase E σ).val = 1 := rfl
@[simp] theorem val_zero : (0 : TwistBase E σ).val = 0 := rfl

/-- **G5 inhabitant** (`WORKFLOW.md` §4/G5.1): the respelled base is inhabited — it is a field,
so `1` does it, and `ofE` exhibits the wrapper explicitly.
@census none (G5 inhabitant of `TwistBase`) -/
instance instInhabited : Inhabited (TwistBase E σ) := ⟨ofE 1⟩

/-- Unwrapping, as a ring homomorphism: `TwistBase E σ ≅ ↥E`.  The *untwisted* side — this is how
modules over `E` (such as `W_v`) are read as modules over the respelled base. -/
def toE : TwistBase E σ →+* ↥E where
  toFun := TwistBase.val
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem toE_apply (x : TwistBase E σ) : toE x = x.val := rfl

/-- `K` sits in the respelled base as it does in `E`. -/
noncomputable instance instAlgebraK : Algebra K (TwistBase E σ) :=
  RingHom.toAlgebra
    { toFun := fun c => ofE (algebraMap K ↥E c)
      map_one' := by apply val_injective; simp
      map_mul' := fun a b => by apply val_injective; simp
      map_zero' := by apply val_injective; simp
      map_add' := fun a b => by apply val_injective; simp }

end TwistBase

/-- **The twisted action, on the respelled base.**  `TwistBase E σ` acts on `Twist E σ` through
`σ` — and, unlike the `Algebra E` instance above, this one cannot be shadowed.

@census none (project definition, `DEF-S5-04`)
-/
noncomputable instance algebraBase : Algebra (TwistBase E σ) (Twist E σ) :=
  RingHom.toAlgebra
    { toFun := fun b => ofL (σ ((b.val : ↥E) : L))
      map_one' := by apply val_injective; simp
      map_mul' := fun a b => by apply val_injective; simp
      map_zero' := by apply val_injective; simp
      map_add' := fun a b => by apply val_injective; simp }

/-- The structure map of the twisted algebra is `σ` on the respelled base.  @census none -/
@[simp] theorem algebraMap_base_apply (b : TwistBase E σ) :
    algebraMap (TwistBase E σ) (Twist E σ) b = ofL (σ ((b.val : ↥E) : L)) := rfl

/-- **The twist is not vacuous.**  If `σ` moves a point of `E`, the twisted action differs from the
untwisted one — so `Twist E σ` is genuinely a different `E`-algebra from `L`, and the distinction
this module preserves has content.

@census none (G5 non-degeneracy for `DEF-S5-03`)
-/
theorem smul_base_def (b : TwistBase E σ) (x : Twist E σ) :
    b • x = ofL (σ ((b.val : ↥E) : L) * x.val) := by
  rw [Algebra.smul_def]; rfl

theorem smul_ne_untwisted {a : TwistBase E σ} (ha : σ ((a.val : ↥E) : L) ≠ ((a.val : ↥E) : L)) :
    a • (1 : Twist E σ) ≠ ofL ((a.val : ↥E) : L) := by
  rw [smul_base_def]
  simp only [ne_eq, Twist.ofL.injEq, val_one, mul_one]
  exact ha

/-! ### G5 -/

/-- **G5 inhabitant** (`WORKFLOW.md` §4/G5.1): `Twist E σ` is inhabited — it is a field, so `1`
does it, and `ofL` exhibits the wrapper explicitly.

@census none (G5 inhabitant of `Twist`)
-/
instance instInhabited : Inhabited (Twist E σ) := ⟨ofL 1⟩

/-- **G5 non-degeneracy.**  The twist is not always the identity structure: whenever `Gal(L/K)` is
non-trivial there is a `σ` and an element of `E = ⊤` on which the twisted action differs from the
untwisted one.  Together with `smul_ne_untwisted` this is what rules out the reading in which
`Twist E σ` is just `L` with its usual `E`-structure — the reading that finding **S5-F4** shows a
plain type synonym silently collapses to.

@census none (G5 non-degeneracy for `Twist`)
-/
theorem exists_twist_ne_untwisted [Nontrivial Gal(L/K)] :
    ∃ (σ : Gal(L/K)) (a : TwistBase (⊤ : IntermediateField K L) σ),
      a • (1 : Twist (⊤ : IntermediateField K L) σ)
        ≠ ofL ((a.val : (⊤ : IntermediateField K L)) : L) := by
  obtain ⟨σ, v, hv⟩ := Descent.exists_smul_ne_self (K := K) (L := L)
  exact ⟨σ, TwistBase.ofE ⟨v, IntermediateField.mem_top⟩, smul_ne_untwisted hv⟩

/-! ### The `L`-structure, and what makes `Twist E σ ⊗[E] V` an `L`-vector space -/

/-- `Twist E σ` is an `L`-vector space by multiplication — the *untwisted* side, which is what
carries the `L`-structure of the base change.  @census none (helper) -/
instance instSMulL : SMul L (Twist E σ) := ⟨fun c x => ofL (c * x.val)⟩

@[simp] theorem val_smulL (c : L) (x : Twist E σ) : (c • x).val = c * x.val := rfl

instance instModuleL : Module L (Twist E σ) where
  one_smul _ := by apply val_injective; simp
  mul_smul _ _ _ := by apply val_injective; simp [mul_assoc]
  smul_zero _ := by apply val_injective; simp
  smul_add _ _ _ := by apply val_injective; simp [mul_add]
  add_smul _ _ _ := by apply val_injective; simp [add_mul]
  zero_smul _ := by apply val_injective; simp

/-- The twisted base action and the `L`-action commute, which is what
`TensorProduct.leftModule` needs to put the `L`-structure on `Twist E σ ⊗[TwistBase E σ] V`.
This is the `TwistBase` counterpart of `instSMulCommClass`, and it is the one the census
statements actually use after the **S5-F5** repair.  @census none (helper) -/
noncomputable instance instSMulCommClassBase :
    SMulCommClass (TwistBase E σ) L (Twist E σ) where
  smul_comm b c x := by
    apply val_injective
    rw [smul_base_def, val_smulL, val_smulL, smul_base_def]
    exact mul_left_comm _ _ _

/-- The twisted `E`-action and the `L`-action commute, which is what
`TensorProduct.leftModule` needs to put the `L`-structure on `Twist E σ ⊗[E] V`.

@census none (helper)
-/
instance instSMulCommClass : SMulCommClass E L (Twist E σ) where
  smul_comm a c x := by
    apply val_injective
    simp only [val_smulL]
    exact mul_left_comm _ _ _

/-! ### Untwisting: `Twist E σ ≃ₗ[TwistBase E σ] L`  (engine of `RQ2-2.21`)

The twist is not a *new* vector space — it is `L` with the base action pulled back along `σ`, and
`σ⁻¹` untwists it.  Give `L` the **untwisted** `TwistBase E σ`-action (through `toE`); then
`x ↦ σ⁻¹(x)` is `TwistBase E σ`-linear from `Twist E σ` to `L`, because
`σ⁻¹(σ(b)·a) = b·σ⁻¹(a)` — an identity needing **no** hypothesis relating `σ` to `E`.

This is what turns `RQ2-2.21`'s twisted tensor `Twist L(v) σ ⊗_{TwistBase} W_v` into the untwisted
`L ⊗ W_v` that stage S0's Galois descent computes, so the row's isomorphism becomes the composite

  `Twist ⊗ W_v --untwist--> L ⊗ W_v --descent--> M(v) --φ'_{v,σ}--> M(σv)`,

whose value on `ofL a ⊗ m` is `σ(σ⁻¹ a) · φ'_{v,σ}(m) = a · φ'_{v,σ}(m)` — the source's own formula,
which is why the twist is exactly what makes `RQ2-2.21-C2` well defined.

@census none (helpers for `RQ2-2.21`)
-/

section Untwist

/-- `L` as a `TwistBase E σ`-module, **untwisted** — the target side of the untwisting map.
Safe as a global instance: `TwistBase E σ` is a structure, so this cannot be reached from `↥E`,
and `L` is not a `Twist`, so it cannot compete with `algebraBase`.  @census none (helper) -/
noncomputable instance instModuleBaseL : Module (TwistBase E σ) L :=
  Module.compHom _ ((algebraMap (↥E) L).comp (TwistBase.toE))

@[simp] theorem base_smul_L (b : TwistBase E σ) (a : L) : b • a = ((b.val : ↥E) : L) * a := rfl

/-- The value of a twisted base action, unfolded — the form `RQ2-2.21`'s balance check needs.
@census none (helper) -/
@[simp] theorem val_smulL_base (b : TwistBase E σ) (x : Twist E σ) :
    (b • x).val = σ ((b.val : ↥E) : L) * x.val := congrArg Twist.val (smul_base_def b x)

/-- Untwisting, as a `TwistBase E σ`-linear equivalence: `x ↦ σ⁻¹(x)`.  @census none (helper) -/
noncomputable def untwist : Twist E σ ≃ₗ[TwistBase E σ] L where
  toFun x := σ.symm x.val
  map_add' x y := by simp
  map_smul' b x := by
    have hv : (b • x).val = σ ((b.val : ↥E) : L) * x.val :=
      congrArg Twist.val (smul_base_def b x)
    show σ.symm ((b • x).val) = b • σ.symm x.val
    rw [hv, map_mul, base_smul_L]
    congr 1
    exact AlgEquiv.symm_apply_apply σ _
  invFun a := ofL (σ a)
  left_inv x := by
    show ofL (σ (σ.symm x.val)) = x
    rw [AlgEquiv.apply_symm_apply]
  right_inv a := AlgEquiv.symm_apply_apply σ a

@[simp] theorem untwist_ofL (a : L) :
    (untwist : Twist E σ ≃ₗ[TwistBase E σ] L) (ofL a) = σ.symm a := rfl

@[simp] theorem untwist_symm_apply (a : L) :
    (untwist : Twist E σ ≃ₗ[TwistBase E σ] L).symm a = ofL (σ a) := rfl

/-- Untwisting is `σ⁻¹`-semi-linear for the two `L`-structures; the `σ⁻¹` it introduces is undone
by the `σ` of semi-linearity when `φ'_{v,σ}` is applied, which is what makes the `RQ2-2.21`
composite `L`-linear.  @census none (helper) -/
theorem untwist_smulL (c : L) (x : Twist E σ) :
    (untwist : Twist E σ ≃ₗ[TwistBase E σ] L) (c • x)
      = σ.symm c * untwist x := by
  show σ.symm ((c • x).val) = σ.symm c * σ.symm x.val
  rw [val_smulL, map_mul]

/-! #### Rebasing along `TwistBase.toE`

`Twist E σ ⊗[TwistBase E σ] W --untwist--> L ⊗[TwistBase E σ] W`, but stage S0's descent computes
`L ⊗[↥E] W`.  The two differ only in how the base ring is *spelled* — `TwistBase E σ` and `↥E` are
isomorphic rings and both module structures are pullbacks along `toE` — but they are different
types, so the tensor products are different types too.

Mathlib has no transport of a tensor product along a ring isomorphism of the base: both searches
were negative (identifier: `congrRingEquiv` exists only for `AdicCompletion` and
`LocallyConstant`, neither a tensor product; statement-shaped: nothing of the form
`M ⊗[R] N ≃ M ⊗[S] N` for `R ≃+* S`).  So we build the one instance needed.  It is generic in `W`
and mentions nothing of this development beyond `TwistBase`, so it is a candidate to generalise
later; it is recorded as the `MD-S5-05` unit.

@census none (helper for `RQ2-2.21-C4`)
-/

section Rebase

variable (W : Type u) [AddCommGroup W] [Module (↥E) W] [Module (TwistBase E σ) W]

/-- **No generic instance here, deliberately** (`DESIGN-NOTES` §26).  A blanket
`Module (TwistBase E σ) W` for every `W` with `[Module ↥E W]` would fire for `W := Twist E σ`
itself — which carries an untwisted `Module ↥E` — and compete with `Twist.algebraBase`, recreating
finding **S5-F5** one level up.  It also collides with the explicit binders `RQ2-2.19` carries.  So
`W`'s respelled-base structure is a **hypothesis**, and its compatibility with `↥E`'s is the
explicit `hW` below.  (Measured: adding the blanket instance broke `RQ2-2.19`'s elaboration and
`generalExtensionBil`'s balance proof — the rule earns its keep immediately.)

`L ⊗[TwistBase E σ] W ≃+ L ⊗[↥E] W`: rebasing along the ring isomorphism `toE`.
@census none (helper for `RQ2-2.21-C4`) -/
noncomputable def rebase (hW : ∀ (b : TwistBase E σ) (w : W), b • w = (b.val : ↥E) • w) :
    (L ⊗[TwistBase E σ] W) ≃+ (L ⊗[↥E] W) where
  toFun := TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun w => a ⊗ₜ[↥E] w
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun x y => TensorProduct.tmul_add _ x y }
      map_zero' := by ext w; exact TensorProduct.zero_tmul _ _
      map_add' := fun a b => by ext w; exact TensorProduct.add_tmul _ _ _ }
    (fun b a w => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [hW b w]
      show (((b.val : ↥E)) • a) ⊗ₜ[↥E] w = a ⊗ₜ[↥E] ((b.val : ↥E) • w)
      exact TensorProduct.smul_tmul _ _ _)
  invFun := TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun w => a ⊗ₜ[TwistBase E σ] w
          map_zero' := TensorProduct.tmul_zero _ _
          map_add' := fun x y => TensorProduct.tmul_add _ x y }
      map_zero' := by ext w; exact TensorProduct.zero_tmul _ _
      map_add' := fun a b => by ext w; exact TensorProduct.add_tmul _ _ _ }
    (fun c a w => by
      simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [← hW (TwistBase.ofE c) w]
      show ((TwistBase.ofE c : TwistBase E σ) • a) ⊗ₜ[TwistBase E σ] w
        = a ⊗ₜ[TwistBase E σ] ((TwistBase.ofE c : TwistBase E σ) • w)
      exact TensorProduct.smul_tmul _ _ _)
  left_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a w => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  right_inv x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a w => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  map_add' x y := map_add _ x y

@[simp] theorem rebase_tmul
    (hW : ∀ (b : TwistBase E σ) (w : W), b • w = (b.val : ↥E) • w) (a : L) (w : W) :
    rebase (E := E) (σ := σ) W hW (a ⊗ₜ[TwistBase E σ] w) = a ⊗ₜ[↥E] w := rfl

end Rebase

end Untwist

/-! ### § Guards — the two-guard rule (`CONVENTIONS.md` §3), finding **S5-F5**

These sit at the **end of the module, after every instance**, and that placement is the point.
Instance resolution is position-dependent within a file: the `#check` that certified S5-F4's fix
was written *above* `instSMulL` and kept passing after `instSMulL` re-created the competitor below
it.  A guard placed mid-module certifies only the prefix of the module it can see.

Guard 1 (`smul_base_def`, above) — the intended twisted action **exists**.

Guard 2 (below) — the intended twisted action **wins**.  Each is stated with bare `•`/`⊗` notation,
so elaborating it *runs instance synthesis against the whole module*, and is proved by `rfl`
against the twisted formula.  If a competing instance ever wins again, `rfl` fails and the build
breaks here rather than silently changing what a census statement means.

The negative control is real: the same two lines stated for `↥E` in place of `TwistBase E σ` do
**not** hold — that is precisely finding S5-F5.
-/

section Guards

/-- **Guard 2a**: the synthesized `SMul (TwistBase E σ) (Twist E σ)` is the *twisted* one.

Proved by `rfl`, so it fails loudly if any later instance shadows `Twist.algebraBase`.  Contrast:
the same statement with `↥E` as the base is **false** (S5-F5), because `E.instSMulSubtypeMem` wins
there.

@census none (instance guard, `DEF-S5-04`)
-/
theorem synth_guard_smul (b : TwistBase E σ) (x : Twist E σ) :
    b • x = ofL (σ ((b.val : ↥E) : L) * x.val) := rfl

/-- **Guard 2b**: the synthesized `Module (TwistBase E σ) (Twist E σ)` — the instance a tensor
product `Twist E σ ⊗[TwistBase E σ] W` actually balances over — is the twisted one.

Stated through `algebraMap` so that it pins the `Algebra`, hence the `Module`, hence the tensor.

@census none (instance guard, `DEF-S5-04`)
-/
theorem synth_guard_algebraMap (b : TwistBase E σ) :
    algebraMap (TwistBase E σ) (Twist E σ) b = ofL (σ ((b.val : ↥E) : L)) := rfl

/-- **Guard 2c**: the untwisted reading is genuinely different — the guards above have content.
If `σ` moves `a`, the twisted action does not agree with multiplication by `a`.

@census none (instance guard, `DEF-S5-04`)
-/
theorem synth_guard_nontrivial {a : TwistBase E σ}
    (ha : σ ((a.val : ↥E) : L) ≠ ((a.val : ↥E) : L)) :
    a • (1 : Twist E σ) ≠ ofL ((a.val : ↥E) : L) := smul_ne_untwisted ha

end Guards

end Twist

/-! ## `Twist`'s non-degeneracy, instantiated (G8 cross-model review finding F-M1-R-8)

`FINAL_AUDIT.md` §11.6(a): *"`Twist`'s non-degeneracy is conditional and never instantiated.
`smul_ne_untwisted` is hypothetical on `σ(a) ≠ a` and is never applied at a concrete `(E, σ)` where
that holds, so the tree never exhibits a twist that actually twists — the exact degeneracy S5-F4/F5
exist to exclude."*  `exists_twist_ne_untwisted` above closes half of that (it is unconditional once
`Gal(L/K)` is non-trivial) but is still a family indexed by a hypothesis; this section discharges
the hypothesis at a concrete pair, so that no S5 non-degeneracy claim about `Twist` rests on a
possibly-empty index.  Same pattern as stage S1's `ComplexReal` section (probe **P2**).

The pair is forced to be `E = ⊤`: for `E = ⊥` every `σ ∈ Gal(L/K)` fixes `E` pointwise and the
twist **is** the untwisted structure, which is precisely the collapse S5-F4 records.  Landed by
commission **C-M1-1**, 2026-09-02, as a dated `WORKFLOW.md` F5 amendment of frozen stage S5; no S5
statement changed.
-/

section ComplexTwist

/-- **G5.1, at a concrete twisting pair**: an inhabitant of `Twist ⊤ (·)̄` for `ℂ/ℝ`, the
conjugation twist.  A named `def` whose type is the structure, as G5.1 asks.

@census none (G5.1 inhabitant of `DEF-S5-03`, instantiated)
-/
noncomputable def complexTwistI : Twist (⊤ : IntermediateField ℝ ℂ) Complex.conjAe :=
  Twist.ofL Complex.I

/-- **G5.2 non-degeneracy, unconditionally**: the twist really twists.  For `K = ℝ`, `L = ℂ`,
`E = ⊤` and `σ =` complex conjugation, the twisted action of `i ∈ E` on `1 ∈ Twist E σ` is `−i`,
not `i` — so `Twist E σ` is genuinely a different `E`-algebra from `L`, at a pair that exists.

@census none (G5.2 non-degeneracy witness for `DEF-S5-03`, instantiated)
-/
theorem complexTwist_smul_ne_untwisted :
    (Twist.TwistBase.ofE ⟨Complex.I, IntermediateField.mem_top⟩ :
        Twist.TwistBase (⊤ : IntermediateField ℝ ℂ) Complex.conjAe)
      • (1 : Twist (⊤ : IntermediateField ℝ ℂ) Complex.conjAe)
      ≠ Twist.ofL Complex.I := by
  refine Twist.smul_ne_untwisted ?_
  show (starRingEnd ℂ) Complex.I ≠ Complex.I
  norm_num [Complex.ext_iff]

end ComplexTwist

end RationalQuivers
