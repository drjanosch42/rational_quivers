import RationalQuivers.HC.Category
import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Base change `HC(𝔤,K)_E → HC(𝔤,K)_{E''}`

Stage **S10**, prerequisite **(ii)** of census row `RQ-5.08` (`rmk:generalbases`); coordinator
rulings `R-S10-2` (this half of `O-PF-2` is IN SCOPE **unconditionally**) and `R-S10-8` (module
set).  This is the HC-side vertical arrow of `RQ-5.08-C4`, and it is **constructed**, for an
arbitrary characteristic-zero extension `E → E''`, not assumed.

## What is built, and why it is cheap at this pin

`M_{E''} := E'' ⊗_E M`, with the weight decomposition `M_n ↦ (M_n).baseChange E''`.  The one step
that looked expensive when the stage was scoped — that a base-changed internal direct sum is again
an internal direct sum — is **mathlib's** at this pin:
`DirectSum.IsInternal.baseChange` (`Mathlib/LinearAlgebra/TensorProduct/Decomposition.lean`,
2025), together with `DirectSum.IsInternal.toBaseChange_bijective`, which also delivers
admissibility (`E'' ⊗_E M_n ≃ₗ (M_n).baseChange E''`, and `E'' ⊗_E -` preserves
finite-dimensionality).  The `𝔰𝔩₂`-relations and the generalized infinitesimal character transport
through the **algebra** homomorphism `Module.End.baseChangeHom`, so `casimir` and its nilpotence
are one `map_pow`/`map_sub` away.

The only genuinely new argument is finite generation as a `(𝔤,K)`-module: `1 ⊗ S` generates
`E'' ⊗_E M` when `S` generates `M`.  It is proved by pulling a candidate `(𝔤,K)`-submodule
`N ⊆ E'' ⊗_E M` back along `v ↦ 1 ⊗ v` — for which the homogeneity half needs
`WeightData.proj_baseChange_one_tmul` below, the base-change counterpart of
`WeightData.proj_comm_of_map` (which does not apply, being stated for two weight data over the
*same* field).

## Relation to S7's `O-PF-2`

`HC/IntendedModel.lean`'s `intendedModel` takes its base change as an argument `bc`, labelled
`ASSUMED-IMPORT`.  `bcFamily` below has **exactly** that argument's type, so the model can now be
instantiated with a constructed base change: the `baseChange` half of `O-PF-2` is discharged.  The
other half, `isAbelian`, is `R-S10-2`'s last item and is sequenced after the census row closes; it
is **not** touched here.  Nothing in `HC/IntendedModel.lean` is amended (no S7 freeze exception).

*(2026-10-21, O-V2-6 round 2.)*  The two paragraphs above are the S10 text and describe the v1 tree.
At v2 WP-8 (`d2a2a47`, 2026-10-17, decision D-10) `HC/IntendedModel.lean` was archived as
`Archive/HC/IntendedModel.lean`.  `HC.intendedModel` is there, and so is
`HC.intendedModelWithBaseChange`, the instantiation with `bcFamily`, which was moved there from this
module.  `bcFamily` stayed here.

## Main definitions / results

* `RationalQuivers.HC.WeightData.baseChange` — `E'' ⊗_E M` as a graded `𝔰𝔩₂`-module.
* `WeightData.proj_baseChange_one_tmul`, `WeightData.casimir_baseChange` — the two transport
  lemmas the object-level construction needs.
* `HCObjOver.baseChange`, `HCHomOver.baseChange` — the object and morphism maps.
* `hcBaseChangeObj` — the functor `HC(𝔤,K)_E ⥤ HC(𝔤,K)_{E''}`.
* `bcFamily` — the same, in `intendedModel`'s `bc` shape.

The restriction of `hcBaseChangeObj` to the parity cut `HC_λ(𝔤,K)_E` is
`Gelfand.hcBaseChange` (`Gelfand/GeneralBaseCategory.lean`).  `parity` lived in that module until
v2 WP-8 (`d2a2a47`), which moved it to `HC/Category.lean` as `HC.parity` (2026-10-21 note, O-V2-6
round 2).
-/

universe u

namespace RationalQuivers.HC

open CategoryTheory
open scoped TensorProduct

variable {E : Type u} [Field E] [CharZero E] {E'' : Type u} [Field E''] [CharZero E'']
  [Algebra E E'']
variable {M : Type u} [AddCommGroup M] [Module E M]

/-- A scalar from the base field acts on an `E''`-module through `algebraMap`.  @census none -/
theorem smul_base {N : Type*} [AddCommMonoid N] [Module E N] [Module E'' N]
    [IsScalarTower E E'' N] (r : E) (x : N) :
    r • x = (algebraMap E E'' r) • x := (algebraMap_smul E'' r x).symm

/-! ## Base change of a `WeightData` -/

namespace WeightData

/-- The base change `E'' ⊗_E M` of a graded `𝔰𝔩₂`-module.  @census none (helper) -/
noncomputable def baseChange (W : WeightData E M) : WeightData E'' (E'' ⊗[E] M) where
  comp n := (W.comp n).baseChange E''
  isInternal := W.isInternal.baseChange
  H := LinearMap.baseChange E'' W.H
  X := LinearMap.baseChange E'' W.X
  Y := LinearMap.baseChange E'' W.Y
  H_apply n v hv := by
    obtain ⟨x, rfl⟩ := hv
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
        show LinearMap.baseChange E'' W.H (a ⊗ₜ[E] (m : M)) = (n : E'') • (a ⊗ₜ[E] (m : M))
        rw [LinearMap.baseChange_tmul, W.H_apply n (m : M) m.2, TensorProduct.tmul_smul,
          smul_base (E'' := E'') ((n : E)) (a ⊗ₜ[E] (m : M)), map_intCast]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
  X_mem n v hv := by
    obtain ⟨x, rfl⟩ := hv
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
        exact Submodule.tmul_mem_baseChange_of_mem a (W.X_mem n m m.2)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  Y_mem n v hv := by
    obtain ⟨x, rfl⟩ := hv
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a m =>
        exact Submodule.tmul_mem_baseChange_of_mem a (W.Y_mem n m m.2)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  lie_H_X := by
    have h := congrArg (Module.End.baseChangeHom E E'' M) W.lie_H_X
    simp only [Module.End.baseChangeHom, map_sub, map_mul,
      AlgHom.ofLinearMap_apply, LinearMap.baseChangeHom_apply, LinearMap.baseChange_smul] at h
    rw [h, smul_base (E'' := E'') (2 : E) (LinearMap.baseChange E'' W.X), map_ofNat]
  lie_H_Y := by
    have h := congrArg (Module.End.baseChangeHom E E'' M) W.lie_H_Y
    simp only [Module.End.baseChangeHom, map_sub, map_mul, map_neg,
      AlgHom.ofLinearMap_apply, LinearMap.baseChangeHom_apply, LinearMap.baseChange_smul] at h
    rw [h, smul_base (E'' := E'') (2 : E) (LinearMap.baseChange E'' W.Y), map_ofNat]
  lie_X_Y := by
    have h := congrArg (Module.End.baseChangeHom E E'' M) W.lie_X_Y
    simpa [Module.End.baseChangeHom, LinearMap.baseChange_mul] using h

/-- The projection onto `M_n` commutes with `v ↦ 1 ⊗ v`.  The base-change counterpart of
`WeightData.proj_comm_of_map` (which is stated for two weight data over the *same* field, so it
does not apply here).  @census none (helper) -/
theorem proj_baseChange_one_tmul (W : WeightData E M) (n : ℤ) (v : M) :
    (W.baseChange (E'' := E'')).proj n ((1 : E'') ⊗ₜ[E] v)
      = (1 : E'') ⊗ₜ[E] W.proj n v := by
  classical
  obtain ⟨s, hzero, hsum⟩ := W.exists_sum_proj v
  have h1 : (1 : E'') ⊗ₜ[E] v = ∑ m ∈ s, (1 : E'') ⊗ₜ[E] W.proj m v := by
    conv_lhs => rw [← hsum]
    rw [TensorProduct.tmul_sum]
  rw [h1, map_sum]
  rw [Finset.sum_eq_single n
    (fun m _ hmn => (W.baseChange (E'' := E'')).proj_of_mem_ne
      (Submodule.tmul_mem_baseChange_of_mem (1 : E'') (W.proj_mem m v)) hmn)
    (fun hn => by rw [hzero n hn, TensorProduct.tmul_zero, map_zero])]
  exact (W.baseChange (E'' := E'')).proj_of_mem_same
    (Submodule.tmul_mem_baseChange_of_mem (1 : E'') (W.proj_mem n v))

/-- Base change of the Casimir.  @census none (helper) -/
theorem casimir_baseChange (W : WeightData E M) :
    (W.baseChange (E'' := E'')).casimir
      = (Module.End.baseChangeHom E E'' M) W.casimir := by
  show (W.baseChange (E'' := E'')).H ^ 2 - 2 * (W.baseChange (E'' := E'')).H
      + 4 * ((W.baseChange (E'' := E'')).X * (W.baseChange (E'' := E'')).Y) + 1 = _
  rw [casimir]
  simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
  rfl

end WeightData

/-! ## Base change of an object -/

/-- The base change `E'' ⊗_E M` of an object of `HC(𝔤,K)_E`.  @census none (helper) -/
noncomputable def HCObjOver.baseChange {ℓ : ℕ} (A : HCObjOver.{u} ℓ E) : HCObjOver.{u} ℓ E'' where
  carrier := E'' ⊗[E] A.carrier
  weight := A.weight.baseChange
  gic := by
    obtain ⟨m, hm⟩ := A.gic
    refine ⟨m, ?_⟩
    have key : (A.weight.baseChange (E'' := E'')).casimir
        - (algebraMap ℚ E'' ((ℓ : ℚ) ^ 2)) • (1 : Module.End E'' (E'' ⊗[E] A.carrier))
        = (Module.End.baseChangeHom E E'' A.carrier)
            (A.weight.casimir
              - (algebraMap ℚ E ((ℓ : ℚ) ^ 2)) • (1 : Module.End E A.carrier)) := by
      rw [map_sub, map_smul, map_one, WeightData.casimir_baseChange,
        smul_base (E'' := E'') (algebraMap ℚ E ((ℓ : ℚ) ^ 2))
          (1 : Module.End E'' (E'' ⊗[E] A.carrier)),
        ← IsScalarTower.algebraMap_apply]
    rw [key, ← map_pow, hm, map_zero]
  fg := by
    classical
    obtain ⟨S, hS⟩ := A.fg
    refine ⟨S.image (fun v => (1 : E'') ⊗ₜ[E] v), ?_⟩
    refine le_antisymm le_top (le_sInf ?_)
    rintro N ⟨hSN, hOp, hHom⟩
    -- pull `N` back along `v ↦ 1 ⊗ v`
    set N₀ : Submodule E A.carrier :=
      (N.restrictScalars E).comap (TensorProduct.mk E E'' A.carrier 1) with hN₀
    have hgen : gkSpanOver A.weight (↑S : Set A.carrier) ≤ N₀ := by
      refine sInf_le ⟨?_, ?_, ?_⟩
      · intro v hv
        exact hSN (by simpa using Finset.mem_image_of_mem _ (by exact_mod_cast hv))
      · refine ⟨fun v hv => ?_, fun v hv => ?_, fun v hv => ?_⟩
        · exact hOp.1 _ hv
        · exact hOp.2.1 _ hv
        · exact hOp.2.2 _ hv
      · intro n v hv
        have h2 := hHom n _ hv
        simp only [TensorProduct.mk_apply] at h2 ⊢
        rwa [WeightData.proj_baseChange_one_tmul] at h2
    rw [hS] at hgen
    intro x _
    induction x using TensorProduct.induction_on with
    | zero => exact N.zero_mem
    | tmul a v =>
        have h1 : (1 : E'') ⊗ₜ[E] v ∈ N := hgen (Submodule.mem_top)
        have : a • ((1 : E'') ⊗ₜ[E] v) = a ⊗ₜ[E] v := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [← this]
        exact N.smul_mem a h1
    | add x y hx hy => exact N.add_mem (hx trivial) (hy trivial)
  admissible n := by
    have e : (E'' ⊗[E] (A.weight.comp n)) ≃ₗ[E''] ((A.weight.comp n).baseChange E'') :=
      LinearEquiv.ofBijective ((A.weight.comp n).toBaseChange E'')
        (DirectSum.IsInternal.toBaseChange_bijective (S := E'') A.weight.comp
          A.weight.isInternal n)
    haveI := A.admissible n
    exact e.finiteDimensional

/-! ## Base change of a morphism, and the functor -/

/-- Base change of a morphism of `HC(𝔤,K)_E`.  @census none (helper) -/
noncomputable def HCHomOver.baseChange {ℓ : ℕ} {A B : HCObjOver.{u} ℓ E} (f : HCHomOver A B) :
    HCHomOver (A.baseChange (E'' := E'')) (B.baseChange (E'' := E'')) where
  toLinearMap := LinearMap.baseChange E'' f.toLinearMap
  map_H v := by
    have h : f.toLinearMap ∘ₗ A.weight.H = B.weight.H ∘ₗ f.toLinearMap := LinearMap.ext f.map_H
    have h2 := congrArg (LinearMap.baseChange E'') h
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h2
    exact congrArg (fun g : (E'' ⊗[E] A.carrier) →ₗ[E''] (E'' ⊗[E] B.carrier) => g v) h2
  map_X v := by
    have h : f.toLinearMap ∘ₗ A.weight.X = B.weight.X ∘ₗ f.toLinearMap := LinearMap.ext f.map_X
    have h2 := congrArg (LinearMap.baseChange E'') h
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h2
    exact congrArg (fun g : (E'' ⊗[E] A.carrier) →ₗ[E''] (E'' ⊗[E] B.carrier) => g v) h2
  map_Y v := by
    have h : f.toLinearMap ∘ₗ A.weight.Y = B.weight.Y ∘ₗ f.toLinearMap := LinearMap.ext f.map_Y
    have h2 := congrArg (LinearMap.baseChange E'') h
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h2
    exact congrArg (fun g : (E'' ⊗[E] A.carrier) →ₗ[E''] (E'' ⊗[E] B.carrier) => g v) h2

/-- **Prerequisite (ii)**: the base-change functor `HC(𝔤,K)_E → HC(𝔤,K)_{E''}`, `M ↦ E'' ⊗_E M`.

@census none (helper; `RQ-5.08-C4`'s HC-side vertical arrow) -/
noncomputable def hcBaseChangeObj (ℓ : ℕ) (E E'' : Type u) [Field E] [CharZero E] [Field E'']
    [CharZero E''] [Algebra E E''] : HCObjOver.{u} ℓ E ⥤ HCObjOver.{u} ℓ E'' where
  obj A := A.baseChange
  map f := f.baseChange
  map_id X := by
    apply HCHomOver.hom_ext
    show LinearMap.baseChange E'' (LinearMap.id : X.carrier →ₗ[E] X.carrier)
        = (LinearMap.id : (E'' ⊗[E] X.carrier) →ₗ[E''] (E'' ⊗[E] X.carrier))
    ext x
    simp
  map_comp f g := by
    apply HCHomOver.hom_ext
    show LinearMap.baseChange E'' (g.toLinearMap ∘ₗ f.toLinearMap)
        = (LinearMap.baseChange E'' g.toLinearMap) ∘ₗ (LinearMap.baseChange E'' f.toLinearMap)
    ext x
    simp

/-! ## Base change along the IDENTITY extension is the identity, up to natural isomorphism

`RQ-5.08-C4b`'s `ss` square, and half of its `ns` square, are drawn along `ℚ[√-1] → ℚ[√-1]` — the
**identity** extension, because `R-S10-5b`/`D13` leave no other split square in this tree
(claimant `@divergence` (6), `V-S10D1-2a`).  Base change along it is `E ⊗[E] −`, which is not the
identity functor but is naturally isomorphic to it.  That unit isomorphism is what layer 1's
compiled `square_of_units` needs as input, and it is built here rather than assumed. -/

section SelfBaseChange

variable {E : Type u} [Field E] [CharZero E]

/-- `TensorProduct.lid` intertwines `LinearMap.baseChange` with the map it base-changes.  The one
computational fact every unit isomorphism below rests on.

@census none (helper; `RQ-5.08-C4b`) -/
theorem lid_baseChange {F : Type u} [Field F] {M N : Type u} [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (f : M →ₗ[F] N) (x : F ⊗[F] M) :
    TensorProduct.lid F N (LinearMap.baseChange F f x) = f (TensorProduct.lid F M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp [hx, hy]

/-- The forward half of the unit: `E ⊗_E M → M`, as a morphism of `HC(𝔤,K)_E`.

@census none (helper; `RQ-5.08-C4b`) -/
noncomputable def HCObjOver.selfBaseChangeHom {ℓ : ℕ} (A : HCObjOver.{u} ℓ E) :
    (A.baseChange (E'' := E)) ⟶ A where
  toLinearMap := (TensorProduct.lid E A.carrier).toLinearMap
  map_H v := lid_baseChange (F := E) A.weight.H v
  map_X v := lid_baseChange (F := E) A.weight.X v
  map_Y v := lid_baseChange (F := E) A.weight.Y v

/-- The backward half of the unit: `M → E ⊗_E M`.

@census none (helper; `RQ-5.08-C4b`) -/
noncomputable def HCObjOver.selfBaseChangeInv {ℓ : ℕ} (A : HCObjOver.{u} ℓ E) :
    A ⟶ (A.baseChange (E'' := E)) where
  toLinearMap := (TensorProduct.lid E A.carrier).symm.toLinearMap
  map_H v := by
    have h := lid_baseChange (F := E) A.weight.H ((TensorProduct.lid E A.carrier).symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact (TensorProduct.lid E A.carrier).symm_apply_eq.mpr h.symm
  map_X v := by
    have h := lid_baseChange (F := E) A.weight.X ((TensorProduct.lid E A.carrier).symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact (TensorProduct.lid E A.carrier).symm_apply_eq.mpr h.symm
  map_Y v := by
    have h := lid_baseChange (F := E) A.weight.Y ((TensorProduct.lid E A.carrier).symm v)
    rw [LinearEquiv.apply_symm_apply] at h
    exact (TensorProduct.lid E A.carrier).symm_apply_eq.mpr h.symm

/-- **Base change along the identity extension is naturally isomorphic to the identity functor**,
on `HC(𝔤,K)_E`.

@census none (helper; `RQ-5.08-C4b`) -/
noncomputable def hcBaseChangeObj_self_iso (ℓ : ℕ) (E : Type u) [Field E] [CharZero E] :
    hcBaseChangeObj ℓ E E ≅ 𝟭 (HCObjOver.{u} ℓ E) :=
  CategoryTheory.NatIso.ofComponents
    (fun A =>
      { hom := A.selfBaseChangeHom
        inv := A.selfBaseChangeInv
        hom_inv_id := by
          apply HCHomOver.hom_ext
          ext x
          exact (TensorProduct.lid E A.carrier).symm_apply_apply x
        inv_hom_id := by
          apply HCHomOver.hom_ext
          ext x
          exact (TensorProduct.lid E A.carrier).apply_symm_apply x })
    (fun {A B} f => by
      apply HCHomOver.hom_ext
      ext x
      exact lid_baseChange (F := E) f.toLinearMap x)

end SelfBaseChange

/-- `hcBaseChangeObj` in exactly the shape of `intendedModel`'s `bc` argument (the archived
`HC.intendedModel`, `Archive/HC/IntendedModel.lean`, since v2 WP-8; 2026-10-21 note), so that S7's
conditional model can be instantiated with a **constructed** base change instead of an assumed one
— the partial discharge of `O-PF-2` that `R-S10-2` records.

@census none (helper; discharges the `baseChange` half of `O-PF-2`) -/
noncomputable def bcFamily (ℓ : ℕ) :
    ∀ {E E' : Type u} [Field E] [CharZero E] [Field E'] [CharZero E'] [Algebra E E'],
      HCObjOver.{u} ℓ E ⥤ HCObjOver.{u} ℓ E' :=
  fun {E E'} _ _ _ _ _ => hcBaseChangeObj ℓ E E'

end RationalQuivers.HC
