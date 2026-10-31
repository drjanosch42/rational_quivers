module

public import RationalQuivers.Species.Rep.FunctorH

@[expose] public section

/-!
# `Rep(Γ_K) ≃ Rep(S(Γ_K))` — the paper's second main theorem (§2.6, census `RQ2-2.29`)

Formalizes `thm:species_equivalence`, the stage's summit and the last row of milestone **M1**.

## The pinned-functors standard

Stage S4's verification finding **F-1** established the shape an equivalence claim must take in
this project: an `∃ e : C ≌ D` with **both** `e.functor` and `e.inverse` named, because
`(F).IsEquivalence` says only that `F` is an equivalence for *some* unnamed inverse and lets the
paper's second functor vanish from the statement. Stage S0 set the same shape for `RQ2-1.13`.

Here `F` and `H` are themselves existential at G2 — `F` is `RQ2-2.26`'s, `H` is `RQ2-2.28`'s — so the
pinning is stated as a **universal** over them: *for any* `F` and `H` satisfying their rows'
characterisations, there is an equivalence whose functor is `F` and whose inverse is `H`. That is
the strongest form the standard admits while the two functors are existential, and it is strictly
stronger than `∃ e, True`: it says the paper's own two constructions are the two halves of one
equivalence, which is exactly what `thm:species_equivalence` claims.
-/

universe u

namespace RationalQuivers

open MulAction CategoryTheory

open scoped TensorProduct DirectSum

namespace RationalQuiver

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (Γ : RationalQuiver K L)

/-! ### § Terminal downstream guard (finding **V-S5b-13**)

`Species/Rep/Twist.lean` guards the twisted action at the **end of its own module**;
`Species/Rep/Decomposition.lean` guards it again as an **importer**.  This module is the terminal
node of the stage's import chain — everything `Twist.lean` exports, and everything every
intermediate module adds on top of it, is visible here.  So this is the strongest position from
which to assert that the twisted action still wins, and `CONVENTIONS.md` §3's completed rule asks
for exactly such an example.

Proved by `rfl`, so any instance introduced anywhere in the chain that shadows `Twist.algebraBase`
breaks the build here.

@census none (instance guard, `DEF-S5-04`)
-/

/-- **Terminal guard**: at the end of the whole import chain, the synthesized
`SMul (TwistBase E σ) (Twist E σ)` is still the twisted one.  @census none (instance guard) -/
theorem twistBase_smul_guard_terminal (E : IntermediateField K L) (σ : Gal(L/K))
    (b : Twist.TwistBase E σ) (x : Twist E σ) :
    b • x = Twist.ofL (σ ((b.val : ↥E) : L) * x.val) := rfl

/-- **Terminal guard**, module form: the `Algebra`, hence the `Module`, hence any tensor product
balanced over it.  @census none (instance guard) -/
theorem twistBase_algebraMap_guard_terminal (E : IntermediateField K L) (σ : Gal(L/K))
    (b : Twist.TwistBase E σ) :
    algebraMap (Twist.TwistBase E σ) (Twist E σ) b = Twist.ofL (σ ((b.val : ↥E) : L)) := rfl


/-! ### `RQ2-2.29`'s engine — the descent's `G_v`-equivariance  (G4)

The equivalence is built from Galois descent at each vertex, and the unit has to be a **morphism**
of `Rep(Γ_K)`, whose `rational` field is the conjugation-family law (`§62.18`).  What makes that
law available is that `RQ2-2.21`'s descent is `G_v`-**equivariant**: `φ'_k` on `M(v)` is `k ⊗ 1` on
`L ⊗_{L(v)} M(v)^{G_v}`, for `k ∈ G_v`.

`galLinearStab` is the vertex-indexed sibling of `FunctorH`'s orbit-indexed `galLinearVOF`: `k` read
as an `L(v)`-linear endomorphism of `L`, which exists exactly when `k` fixes `L(v) = L^{G_v}`.

@census none (G4 engine for `RQ2-2.29`)
-/

variable {Γ}

/-- `k ∈ G_v` as an `L(v)`-linear endomorphism of `L`.  @census none (helper) -/
noncomputable def galLinearStab (v : Γ.V) (k : Gal(L/K)) (hk : k • v = v) :
    L →ₗ[↥(stabField K L v)] L where
  toFun := k
  map_add' _ _ := k.map_add _ _
  map_smul' c y := by
    show k ((algebraMap ↥(stabField K L v) L c) • y)
      = (algebraMap ↥(stabField K L v) L c) • k y
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact (IntermediateField.mem_fixedField_iff _ _).mp c.2 k hk

set_option backward.isDefEq.respectTransparency.types false in
/-- **`RQ2-2.21`'s descent is `G_v`-equivariant.**  `φ'_k` on `M(v)` is `k ⊗ 1` on
`L ⊗_{L(v)} M(v)^{G_v}` — because the fixed vectors are fixed and `φ'` is `k`-semi-linear.
@census none (helper for `RQ2-2.29`) -/
theorem vertexDescentEquiv_gal (M : Rep Γ) (v : Γ.V) (k : Gal(L/K)) (hk : k • v = v)
    (z : L ⊗[↥(stabField K L v)] ↥(M.vertexFixed v)) :
    M.φ' k hk (vertexDescentEquiv M v z)
      = vertexDescentEquiv M v (LinearMap.rTensor _ (galLinearStab v k hk) z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a m =>
      rw [vertexDescentEquiv_tmul, Rep.φ'_smul,
        LinearMap.rTensor_tmul, vertexDescentEquiv_tmul]
      congr 1
      exact m.2 ⟨k, hk⟩
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

variable (Γ)


/-! ### `RQ2-2.29`'s unit and counit — built from the two **fixed-point** identifications  (G4)

Per §63.1: the unit goes through `e_fix`, never through `e_obj`.  Both ends are `RQ2-2.21`'s
descent, and the middle is `eF^{-1}` then `eHfix^{-1}`:

```
M(v_i)  ≅  L ⊗_{L_i} M(v_i)^{G}  ≅  L ⊗_{L_i} (F M).W_i  ≅  L ⊗_{L_i} (H(FM))^{G}  ≅  H(FM)(v_i)
```

The counit is the composite of the two hypothesis equivalences, `eF` then `eHfix`, at
`F(H V)`.

`eFL`/`eHfixL` read the hypotheses' `L_iᵐᵒᵖ`-linear equivalences `L_i`-linearly — the two actions
are one action through `RingEquiv.toOpposite`, so the conversion is `AddEquiv.toLinearEquiv` and
one `op`.

@census none (G4 engine for `RQ2-2.29`)
-/

section Summit
variable {Γ}
-- Port v4.35: section-scoped, the `variable` binders below need the pre-v4.35 mvar-type check.
set_option backward.isDefEq.respectTransparency.types false
variable
  (F : CategoryTheory.Functor (FDRep Γ) (EtaleSpecies.Rep Γ.toSpecies))
  (H : CategoryTheory.Functor (EtaleSpecies.Rep Γ.toSpecies) (FDRep Γ))
  (eF : ∀ (M : FDRep Γ) (i : Γ.VertexOrbit),
    (F.obj M).W i ≃ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep i)))
  (eHfix : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
    ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i)) ≃ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] V.W i)

set_option backward.isDefEq.respectTransparency.types false in
/-- `eF` read `L_i`-linearly.  @census none (helper) -/
noncomputable def eFL (M : FDRep Γ) (i : Γ.VertexOrbit) :
    (F.obj M).W i ≃ₗ[Γ.toSpecies.L i] ↥(M.toRep.vertexFixed (Γ.vertexRep i)) :=
  AddEquiv.toLinearEquiv (eF M i).toAddEquiv
    (fun c x => (eF M i).map_smul (MulOpposite.op c) x)

set_option backward.isDefEq.respectTransparency.types false in
/-- `eHfix` read `L_i`-linearly.  @census none (helper) -/
noncomputable def eHfixL (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit) :
    ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i)) ≃ₗ[Γ.toSpecies.L i] V.W i :=
  AddEquiv.toLinearEquiv (eHfix V i).toAddEquiv
    (fun c x => (eHfix V i).map_smul (MulOpposite.op c) x)

set_option backward.isDefEq.respectTransparency.types false in
/-- **The counit's components**: `F(H V)`'s `W_i` is `(H V)`'s fixed points by `eF`, and those are
`V.W i` by `eHfix`.  @census none (helper for `RQ2-2.29`) -/
noncomputable def counitComp (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit) :
    (F.obj (H.obj V)).W i ≃ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] V.W i :=
  (eF (H.obj V) i).trans (eHfix V i)

/-- **The unit at the orbit representative**, routed through `e_fix` (§63.1).
@census none (helper for `RQ2-2.29`) -/
noncomputable def unitRep (M : FDRep Γ) (i : Γ.VertexOrbit) :
    M.toRep.M (Γ.vertexRep i) ≃ₗ[L] (H.obj (F.obj M)).toRep.M (Γ.vertexRep i) :=
  (vertexDescentEquiv M.toRep (Γ.vertexRep i)).symm.trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
        ((eFL F eF M i).symm.trans (eHfixL H eHfix (F.obj M) i).symm)).trans
      (vertexDescentEquiv (H.obj (F.obj M)).toRep (Γ.vertexRep i)))

/-- **The triangle's fixed-point equation** — `rfl`-level, which is the whole point of §63.1's
route.  @census none (helper for `RQ2-2.29`) -/
theorem unit_counit_fixed (M : FDRep Γ) (i : Γ.VertexOrbit) (w : (F.obj M).W i) :
    eHfix (F.obj M) i ((eHfixL H eHfix (F.obj M) i).symm
        ((eFL F eF M i).symm (eF M i w))) = w := by
  show (eHfixL H eHfix (F.obj M) i) ((eHfixL H eHfix (F.obj M) i).symm _) = w
  rw [LinearEquiv.apply_symm_apply]
  exact (eFL F eF M i).symm_apply_apply w

/-- The `rTensor` of `galLinearStab` commutes with anything acting on the other factor.
@census none (helper) -/
theorem rTensor_galLinearStab_comm {v : Γ.V} {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    [Module ↥(stabField K L v) A] [Module ↥(stabField K L v) B]
    (ρ : A ≃ₗ[↥(stabField K L v)] B) (k : Gal(L/K)) (hk : k • v = v)
    (z : L ⊗[↥(stabField K L v)] A) :
    LinearMap.rTensor B (galLinearStab v k hk)
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L) ρ z)
      = TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L) ρ
          (LinearMap.rTensor A (galLinearStab v k hk) z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a x => rfl
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

/-- **The unit commutes with `φ'` on the stabiliser** — which is what makes the vertex family a
conjugation family (§62.18, sixth outing).  Both ends are `vertexDescentEquiv_gal`; the middle
acts on the other tensor factor.  @census none (helper for `RQ2-2.29`) -/
theorem unitRep_gal (M : FDRep Γ) (i : Γ.VertexOrbit) (k : Gal(L/K))
    (hk : k • Γ.vertexRep i = Γ.vertexRep i) (x : M.toRep.M (Γ.vertexRep i)) :
    unitRep F H eF eHfix M i (M.toRep.φ' k hk x)
      = (H.obj (F.obj M)).toRep.φ' k hk (unitRep F H eF eHfix M i x) := by
  obtain ⟨z, rfl⟩ : ∃ z, vertexDescentEquiv M.toRep (Γ.vertexRep i) z = x :=
    ⟨(vertexDescentEquiv M.toRep (Γ.vertexRep i)).symm x,
      LinearEquiv.apply_symm_apply _ _⟩
  rw [vertexDescentEquiv_gal]
  show vertexDescentEquiv (H.obj (F.obj M)).toRep (Γ.vertexRep i)
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L) _
        ((vertexDescentEquiv M.toRep (Γ.vertexRep i)).symm
          (vertexDescentEquiv M.toRep (Γ.vertexRep i)
            (LinearMap.rTensor _ (galLinearStab (Γ.vertexRep i) k hk) z)))) = _
  rw [LinearEquiv.symm_apply_apply]
  show _ = (H.obj (F.obj M)).toRep.φ' k hk
    (vertexDescentEquiv (H.obj (F.obj M)).toRep (Γ.vertexRep i)
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L) _
        ((vertexDescentEquiv M.toRep (Γ.vertexRep i)).symm
          (vertexDescentEquiv M.toRep (Γ.vertexRep i) z))))
  rw [LinearEquiv.symm_apply_apply, vertexDescentEquiv_gal,
    rTensor_galLinearStab_comm]

/-- `φ'`'s inverse is `σ⁻¹`-semi-linear.  @census none (helper) -/
theorem Rep_phi'_symm_smul (M : Rep Γ) (σ : Gal(L/K)) {v w : Γ.V} (h : σ • v = w)
    (a : L) (y : M.M w) :
    (M.φ' σ h).symm (a • y) = σ⁻¹ a • (M.φ' σ h).symm y := by
  refine (M.φ' σ h).injective ?_
  rw [AddEquiv.apply_symm_apply, Rep.φ'_smul, AddEquiv.apply_symm_apply]
  congr 1
  exact (AlgEquiv.apply_symm_apply σ a).symm

/-- **The unit at a vertex**, indexed by the orbit as a *parameter* (`§62.9`) and by a translation
carrying the representative to the vertex.  `unitAt_congr` shows the translation does not matter.
@census none (helper for `RQ2-2.29`) -/
noncomputable def unitAt (M : FDRep Γ) (i : Γ.VertexOrbit) (v : Γ.V)
    (g : Gal(L/K)) (hg : g • Γ.vertexRep i = v) :
    M.toRep.M v →ₗ[L] (H.obj (F.obj M)).toRep.M v where
  toFun x := (H.obj (F.obj M)).toRep.φ' g hg
    (unitRep F H eF eHfix M i ((M.toRep.φ' g hg).symm x))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' c x := by
    show (H.obj (F.obj M)).toRep.φ' g hg
      (unitRep F H eF eHfix M i ((M.toRep.φ' g hg).symm (c • x))) = _
    rw [Rep_phi'_symm_smul, LinearEquiv.map_smul, Rep.φ'_smul]
    show (g (g⁻¹ c)) • _ = _
    rw [show g (g⁻¹ c) = c from congrArg (fun t : Gal(L/K) => t c) (mul_inv_cancel g)]
    rfl

/-- The translation does not matter: two translations to the same vertex differ by `G_{v_i}`, and
`unitRep_gal` absorbs it.  @census none (helper) -/
theorem unitAt_congr (M : FDRep Γ) (i : Γ.VertexOrbit) (v : Γ.V)
    (g g' : Gal(L/K)) (hg : g • Γ.vertexRep i = v) (hg' : g' • Γ.vertexRep i = v)
    (x : M.toRep.M v) :
    unitAt F H eF eHfix M i v g hg x = unitAt F H eF eHfix M i v g' hg' x := by
  have hk : (g'⁻¹ * g) • Γ.vertexRep i = Γ.vertexRep i := by
    rw [mul_smul, hg, ← hg', inv_smul_smul]
  -- `φ'(g')⁻¹ ∘ φ'(g)` is `φ'(g'⁻¹ g)`, which commutes with the unit
  have hcomp : ∀ (N : Rep Γ) (y : N.M (Γ.vertexRep i)),
      (N.φ' g' hg').symm (N.φ' g hg y) = N.φ' (g'⁻¹ * g) hk y := by
    intro N y
    refine (N.φ' g' hg').injective ?_
    rw [AddEquiv.apply_symm_apply,
      N.φ'_comp g' (g'⁻¹ * g) hk hg' (by rw [mul_smul, hk, hg'])]
    exact N.φ'_congr (show g = g' * (g'⁻¹ * g) from by group) hg
      (by rw [mul_smul, hk, hg']) y
  refine (((H.obj (F.obj M)).toRep.φ' g' hg').symm).injective ?_
  show ((H.obj (F.obj M)).toRep.φ' g' hg').symm
      ((H.obj (F.obj M)).toRep.φ' g hg
        (unitRep F H eF eHfix M i ((M.toRep.φ' g hg).symm x)))
    = ((H.obj (F.obj M)).toRep.φ' g' hg').symm
        ((H.obj (F.obj M)).toRep.φ' g' hg'
          (unitRep F H eF eHfix M i ((M.toRep.φ' g' hg').symm x)))
  rw [hcomp, AddEquiv.symm_apply_apply, ← unitRep_gal]
  congr 1
  refine (M.toRep.φ' g' hg').injective ?_
  rw [AddEquiv.apply_symm_apply,
    M.toRep.φ'_comp g' (g'⁻¹ * g) hk hg' (by rw [mul_smul, hk, hg'])]
  rw [← M.toRep.φ'_congr (show g = g' * (g'⁻¹ * g) from by group) hg
    (by rw [mul_smul, hk, hg']) ((M.toRep.φ' g hg).symm x)]
  rw [AddEquiv.apply_symm_apply]

/-- `unitAt` across an equality of orbits — `subst` and `unitAt_congr`.  @census none (helper) -/
theorem unitAt_congr' (M : FDRep Γ) {i i' : Γ.VertexOrbit} (hii : i = i') (v : Γ.V)
    (g g' : Gal(L/K)) (hg : g • Γ.vertexRep i = v) (hg' : g' • Γ.vertexRep i' = v)
    (x : M.toRep.M v) :
    unitAt F H eF eHfix M i v g hg x = unitAt F H eF eHfix M i' v g' hg' x := by
  subst hii
  exact unitAt_congr F H eF eHfix M i v g g' hg hg' x

/-- **The conjugation-family law for the unit** — `Rep.Hom`'s `rational` field, at a fixed orbit.
`g'^{-1} σ g` fixes `v_i`, and `unitRep_gal` absorbs it.  @census none (helper) -/
theorem unitAt_rational (M : FDRep Γ) (i : Γ.VertexOrbit) (v : Γ.V)
    (g g' σ : Gal(L/K)) (hg : g • Γ.vertexRep i = v) (hg' : g' • Γ.vertexRep i = σ • v)
    (m : M.toRep.M v) :
    unitAt F H eF eHfix M i (σ • v) g' hg' (M.toRep.φ' σ rfl m)
      = (H.obj (F.obj M)).toRep.φ' σ rfl (unitAt F H eF eHfix M i v g hg m) := by
  have hk : (g'⁻¹ * σ * g) • Γ.vertexRep i = Γ.vertexRep i := by
    rw [mul_smul, mul_smul, hg, ← hg', inv_smul_smul]
  have hmid : ∀ (N : Rep Γ) (y : N.M (Γ.vertexRep i)),
      (N.φ' g' hg').symm (N.φ' σ (rfl : σ • v = σ • v) (N.φ' g hg y))
        = N.φ' (g'⁻¹ * σ * g) hk y := by
    intro N y
    refine (N.φ' g' hg').injective ?_
    rw [AddEquiv.apply_symm_apply,
      N.φ'_comp σ g hg (rfl : σ • v = σ • v) (by rw [mul_smul, hg]),
      N.φ'_comp g' (g'⁻¹ * σ * g) hk hg' (by rw [mul_smul, hk, hg'])]
    exact N.φ'_congr (show σ * g = g' * (g'⁻¹ * σ * g) from by group)
      (by rw [mul_smul, hg]) (by rw [mul_smul, hk, hg']) y
  show (H.obj (F.obj M)).toRep.φ' g' hg'
      (unitRep F H eF eHfix M i ((M.toRep.φ' g' hg').symm
        (M.toRep.φ' σ (rfl : σ • v = σ • v) m))) = _
  obtain ⟨y, rfl⟩ : ∃ y, M.toRep.φ' g hg y = m :=
    ⟨(M.toRep.φ' g hg).symm m, AddEquiv.apply_symm_apply _ _⟩
  rw [hmid, unitRep_gal]
  show _ = (H.obj (F.obj M)).toRep.φ' σ (rfl : σ • v = σ • v)
    ((H.obj (F.obj M)).toRep.φ' g hg
      (unitRep F H eF eHfix M i ((M.toRep.φ' g hg).symm (M.toRep.φ' g hg y))))
  rw [AddEquiv.symm_apply_apply,
    (H.obj (F.obj M)).toRep.φ'_comp σ g hg (rfl : σ • v = σ • v)
      (by rw [mul_smul, hg]),
    (H.obj (F.obj M)).toRep.φ'_comp g' (g'⁻¹ * σ * g) hk hg'
      (by rw [mul_smul, hk, hg'])]
  exact ((H.obj (F.obj M)).toRep.φ'_congr
    (show σ * g = g' * (g'⁻¹ * σ * g) from by group)
    (by rw [mul_smul, hg]) (by rw [mul_smul, hk, hg']) _).symm

/-! ### The `η`-separation — the surjectivity of a bijection this stage already proved  (G4)

`RQ2-2.29`'s `edge` field needs the `(ε,η)`-sum

```
Σ_η ρ_η(y) · X_η = 0   for all y ∈ L(τ_ε^{-1}e_ε)   ⟹   X_η = 0 for every η
```

which is the linear independence of the embeddings `ρ_η`.  **It is not proved here, and it is not
Dedekind's theorem.**  It is the *surjectivity* of `leEpsilonPreEquiv` — S3's `tensorPi_bijective`
instantiated by `RQ2-2.19` at exactly this coset index (`Decomposition.lean`) — read as a
dual-basis statement: each `η₀` has a preimage of the indicator, and combining the vanishing sum
with its coefficients isolates `X_{η₀}`.

The route matters and is recorded in `CONVENTIONS.md` §6: the author reached first for mathlib's
`linearIndependent_monoidHom` with S0's worked template, which would have re-spelled the
*injectivity* half of a bijection this stage had already proved and consumed twice.  **Rung 1
carries a search obligation.**

@census none (G4 engine for `RQ2-2.29`)
-/

/-- **The `η`-separation.**  If a family `X` is annihilated by every `ρ_η`-weighted sum, it is
zero.  The whole content is `leEpsilonPreEquiv`'s surjectivity.  @census none (helper) -/
theorem eta_separation {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    [Fintype (EdgeChoice.CosetIndex Γ ch)] [DecidableEq (EdgeChoice.CosetIndex Γ ch)]
    {W : Type u} [AddCommGroup W] [Module L W]
    (X : EdgeChoice.CosetIndex Γ ch → W)
    (h : ∀ y : ↥(tauEdgeField ch),
      ∑ η : EdgeChoice.CosetIndex Γ ch, (EdgeChoice.rep Γ ch η ((y : L))) • X η = 0)
    (η₀ : EdgeChoice.CosetIndex Γ ch) : X η₀ = 0 := by
  -- the weighted sum vanishes for every element of the tensor, not just pure ones
  have key : ∀ z : L ⊗[↥(Γ.vertexOrbitField j)] ↥(tauEdgeField ch),
      ∑ η : EdgeChoice.CosetIndex Γ ch, (leEpsilonPreEquiv ch z η) • X η = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        refine Finset.sum_eq_zero fun η _ => ?_
        rw [map_zero]
        show (0 : L) • X η = 0
        rw [zero_smul]
    | tmul a y =>
        calc (∑ η : EdgeChoice.CosetIndex Γ ch,
              (leEpsilonPreEquiv ch (a ⊗ₜ[↥(Γ.vertexOrbitField j)] y) η) • X η)
            = ∑ η : EdgeChoice.CosetIndex Γ ch,
                a • ((EdgeChoice.rep Γ ch η ((y : L))) • X η) :=
              Finset.sum_congr rfl (fun η _ => by
                rw [leEpsilonPreEquiv_tmul, mul_smul])
          _ = a • ∑ η : EdgeChoice.CosetIndex Γ ch,
                (EdgeChoice.rep Γ ch η ((y : L))) • X η := Finset.smul_sum.symm
          _ = 0 := by rw [h y, smul_zero]
    | add p q hp hq =>
        calc (∑ η : EdgeChoice.CosetIndex Γ ch,
              (leEpsilonPreEquiv ch (p + q) η) • X η)
            = ∑ η : EdgeChoice.CosetIndex Γ ch,
                ((leEpsilonPreEquiv ch p η) • X η + (leEpsilonPreEquiv ch q η) • X η) :=
              Finset.sum_congr rfl (fun η _ => by
                rw [map_add]
                show ((leEpsilonPreEquiv ch p + leEpsilonPreEquiv ch q) η) • X η = _
                rw [Pi.add_apply, add_smul])
          _ = 0 := by rw [Finset.sum_add_distrib, hp, hq, add_zero]
  -- the indicator has a preimage; that is the dual basis
  obtain ⟨z, hz⟩ := (leEpsilonPreEquiv ch).surjective
    (Pi.single η₀ (1 : L))
  have hk := key z
  rw [hz] at hk
  have hsingle : (∑ η : EdgeChoice.CosetIndex Γ ch,
      ((Pi.single η₀ (1 : L) : EdgeChoice.CosetIndex Γ ch → L) η) • X η) = X η₀ := by
    refine Eq.trans (Finset.sum_eq_single η₀ (fun η _ hne => ?_) (fun hη =>
      absurd (Finset.mem_univ η₀) hη)) ?_
    · rw [Pi.single_eq_of_ne hne]
      exact zero_smul L (X η)
    · rw [Pi.single_eq_same]
      exact one_smul L (X η₀)
  rw [← hsingle]
  exact hk

/-! ### The unit intertwines the two descents  (G4)

The `edge` field's mathematical input, and the place `hF1` and `hH1` meet.  Both hypotheses pin a
descent against `(F M)`'s **own** structure map `f_{ij}` — `hF1` through `eF`, `hH1` through
`eHfix` — so the unit's fixed-point restriction, which is `eHfix^{-1} ∘ eF^{-1}`, carries one to
the other by cancellation.  Three rewrites and no content beyond that observation.

This is `RQ2-2.28`'s `H2`(a) seen from the other side: there, one descent was pinned and the row
asked what it was; here, two descents are pinned to the same thing and the row asks that they
agree.

@census none (G4 engine for `RQ2-2.29`)
-/

set_option backward.isDefEq.respectTransparency.types false in
/-- The unit on the fixed points: `eF^{-1}` then `eHfix^{-1}`.  @census none (helper) -/
noncomputable def unitFix (M : FDRep Γ) (i : Γ.VertexOrbit) :
    ↥(M.toRep.vertexFixed (Γ.vertexRep i))
      →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep i)) :=
  ((eHfix (F.obj M) i).symm.trans (LinearEquiv.refl _ _)).toLinearMap ∘ₗ
    (eF M i).symm.toLinearMap

set_option backward.isDefEq.respectTransparency.types false in
/-- **The unit intertwines the two descents.**  @census none (helper for `RQ2-2.29`) -/
theorem unitFix_descent (M : FDRep Γ) {i j : Γ.VertexOrbit}
    (chij : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀M : wiiMjL M.toRep i j ≃ₗ[L] wiiMjLpreRhs M.toRep chij)
    (fM : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.toRep.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep j)))
    (hM : IsEdgeDescent M.toRep chij e₀M fM)
    (e₀N : wiiMjL (H.obj (F.obj M)).toRep i j
      ≃ₗ[L] wiiMjLpreRhs (H.obj (F.obj M)).toRep chij)
    (fN : EtaleSpecies.Rep.tensor Γ.toSpecies i j
            ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ]
            ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep j)))
    (hN : IsEdgeDescent (H.obj (F.obj M)).toRep chij e₀N fN)
    (hF1 : ∀ (w : (F.obj M).W i) (m : Γ.toSpecies.M i j),
      eF M j ((F.obj M).f i j (Balanced.mk w m)) = fM (Balanced.mk (eF M i w) m))
    (hH1 : ∀ (w : ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep i)))
        (m : Γ.toSpecies.M i j),
      eHfix (F.obj M) j (fN (Balanced.mk w m))
        = EtaleSpecies.Rep.f' Γ.toSpecies (F.obj M) i j
            (Balanced.mk (eHfix (F.obj M) i w) m))
    (w : ↥(M.toRep.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) :
    fN (Balanced.mk (unitFix F H eF eHfix M i w) m)
      = unitFix F H eF eHfix M j (fM (Balanced.mk w m)) := by
  refine (eHfix (F.obj M) j).injective ?_
  rw [hH1]
  show _ = eHfix (F.obj M) j ((eHfix (F.obj M) j).symm
    ((eF M j).symm (fM (Balanced.mk w m))))
  rw [LinearEquiv.apply_symm_apply]
  refine (eF M j).injective ?_
  rw [LinearEquiv.apply_symm_apply]
  have heh : eHfix (F.obj M) i (unitFix F H eF eHfix M i w) = (eF M i).symm w := by
    show eHfix (F.obj M) i ((eHfix (F.obj M) i).symm ((eF M i).symm w)) = _
    rw [LinearEquiv.apply_symm_apply]
  rw [heh]
  show eF M j ((F.obj M).f i j (Balanced.mk ((eF M i).symm w) m)) = _
  rw [hF1, LinearEquiv.apply_symm_apply]

/-! ### From the descents to the `(ε,η)`-components  (G4)

Steps 1–3 of the `edge` field.  `phiTotal_e0_generator` expands each descent into the `(ε,η)`
double sum; `unitFix_descent` equates the two; and `eta_separation` then separates the `η`-sum once
`m` is chosen supported at a single `ε`.

The `ε`-collapse is free: `phiComp`'s coefficient is `ρ_η(m_ε)`, so a `Pi.single`-shaped `m` kills
every other summand by `map_zero`.  The `η`-separation is a8148a6.

@census none (G4 engine for `RQ2-2.29`)
-/

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Steps 1–2**: applying the unit to `M`'s descent equation gives `N`'s, so the two `(ε,η)`
double sums agree.  @census none (helper) -/
theorem unitFix_sum (M : FDRep Γ) {i j : Γ.VertexOrbit}
    (chij : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (chij ε))]
    (psi : ∀ v : Γ.V, M.toRep.M v →ₗ[L] (H.obj (F.obj M)).toRep.M v)
    (e₀M : wiiMjL M.toRep i j ≃ₗ[L] wiiMjLpreRhs M.toRep chij)
    (fM : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.toRep.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep j)))
    (hM : IsEdgeDescent M.toRep chij e₀M fM)
    (e₀N : wiiMjL (H.obj (F.obj M)).toRep i j
      ≃ₗ[L] wiiMjLpreRhs (H.obj (F.obj M)).toRep chij)
    (fN : EtaleSpecies.Rep.tensor Γ.toSpecies i j
            ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ]
            ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep j)))
    (hN : IsEdgeDescent (H.obj (F.obj M)).toRep chij e₀N fN)
    (hint : ∀ (w : ↥(M.toRep.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j),
      fN (Balanced.mk (unitFix F H eF eHfix M i w) m)
        = unitFix F H eF eHfix M j (fM (Balanced.mk w m)))
    (hfix : ∀ (x : ↥(M.toRep.vertexFixed (Γ.vertexRep j))),
      psi (Γ.vertexRep j) ((x : M.toRep.M (Γ.vertexRep j)))
        = ((unitFix F H eF eHfix M j x : ↥((H.obj (F.obj M)).toRep.vertexFixed
            (Γ.vertexRep j))) : (H.obj (F.obj M)).toRep.M (Γ.vertexRep j)))
    (w : ↥(M.toRep.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) :
    (∑ ε : Γ.EdgeOrbit i j, ∑ η : EdgeChoice.CosetIndex Γ (chij ε),
        ((EdgeChoice.rep Γ (chij ε) η * (chij ε).τ⁻¹) ((m ε : L)))
          • psi (Γ.vertexRep j) (phiComp M.toRep (chij ε) η w))
      = ∑ ε : Γ.EdgeOrbit i j, ∑ η : EdgeChoice.CosetIndex Γ (chij ε),
          ((EdgeChoice.rep Γ (chij ε) η * (chij ε).τ⁻¹) ((m ε : L)))
            • phiComp (H.obj (F.obj M)).toRep (chij ε) η
                (unitFix F H eF eHfix M i w) := by
  have hMval := hM.2 (phiTotal M.toRep chij) (phiTotal_single M.toRep chij)
    (Balanced.mk w m) 1
  have hNval := hN.2 (phiTotal (H.obj (F.obj M)).toRep chij)
    (phiTotal_single (H.obj (F.obj M)).toRep chij)
    (Balanced.mk (unitFix F H eF eHfix M i w) m) 1
  rw [phiTotal_e0_generator M.toRep chij e₀M hM.1 w m 1, one_smul] at hMval
  rw [phiTotal_e0_generator (H.obj (F.obj M)).toRep chij e₀N hN.1
    (unitFix F H eF eHfix M i w) m 1, one_smul] at hNval
  simp only [one_mul] at hMval hNval
  -- the `N`-side sum is `unitFix` of the `M`-side value
  rw [hNval, hint, ← hfix, ← hMval]
  -- and `psi` is `L`-linear, so it passes through both sums termwise
  refine Eq.trans ?_ (map_sum (psi (Γ.vertexRep j)) _ Finset.univ).symm
  refine Finset.sum_congr rfl fun ε _ => ?_
  refine Eq.trans ?_ (map_sum (psi (Γ.vertexRep j)) _ Finset.univ).symm
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [LinearMap.map_smul]

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Step 3**: the `(ε,η)`-components agree.  `Pi.single` collapses the `ε`-sum by `map_zero`,
and `eta_separation` separates the `η`-sum.  @census none (helper for `RQ2-2.29`) -/
theorem unitFix_phiComp (M : FDRep Γ) {i j : Γ.VertexOrbit}
    (chij : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (chij ε))]
    (psi : ∀ v : Γ.V, M.toRep.M v →ₗ[L] (H.obj (F.obj M)).toRep.M v)
    (e₀M : wiiMjL M.toRep i j ≃ₗ[L] wiiMjLpreRhs M.toRep chij)
    (fM : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.toRep.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep j)))
    (hM : IsEdgeDescent M.toRep chij e₀M fM)
    (e₀N : wiiMjL (H.obj (F.obj M)).toRep i j
      ≃ₗ[L] wiiMjLpreRhs (H.obj (F.obj M)).toRep chij)
    (fN : EtaleSpecies.Rep.tensor Γ.toSpecies i j
            ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ]
            ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep j)))
    (hN : IsEdgeDescent (H.obj (F.obj M)).toRep chij e₀N fN)
    (hint : ∀ (w : ↥(M.toRep.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j),
      fN (Balanced.mk (unitFix F H eF eHfix M i w) m)
        = unitFix F H eF eHfix M j (fM (Balanced.mk w m)))
    (hfix : ∀ (x : ↥(M.toRep.vertexFixed (Γ.vertexRep j))),
      psi (Γ.vertexRep j) ((x : M.toRep.M (Γ.vertexRep j)))
        = ((unitFix F H eF eHfix M j x : ↥((H.obj (F.obj M)).toRep.vertexFixed
            (Γ.vertexRep j))) : (H.obj (F.obj M)).toRep.M (Γ.vertexRep j)))
    (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (chij ε))
    (w : ↥(M.toRep.vertexFixed (Γ.vertexRep i))) :
    psi (Γ.vertexRep j) (phiComp M.toRep (chij ε) η w)
      = phiComp (H.obj (F.obj M)).toRep (chij ε) η (unitFix F H eF eHfix M i w) := by
  letI := edgeRightAlgebra ε
  -- the difference family
  set D : EdgeChoice.CosetIndex Γ (chij ε) → (H.obj (F.obj M)).toRep.M (Γ.vertexRep j) :=
    fun η => psi (Γ.vertexRep j) (phiComp M.toRep (chij ε) η w)
      - phiComp (H.obj (F.obj M)).toRep (chij ε) η (unitFix F H eF eHfix M i w) with hD
  have hzero : ∀ y : ↥(tauEdgeField (chij ε)),
      ∑ η' : EdgeChoice.CosetIndex Γ (chij ε),
        (EdgeChoice.rep Γ (chij ε) η' ((y : L))) • D η' = 0 := by
    intro y
    have hsum := unitFix_sum F H eF eHfix M chij psi e₀M fM hM e₀N fN hN hint hfix w
      (Pi.single ε ((tauEdgeAlgEquiv (chij ε)).symm y))
    -- the `ε`-sum collapses: every other component of `Pi.single` is `0`
    have hcollapse : ∀ (N' : Rep Γ)
        (g : ∀ ε' : Γ.EdgeOrbit i j, EdgeChoice.CosetIndex Γ (chij ε') → N'.M (Γ.vertexRep j)),
        (∑ ε' : Γ.EdgeOrbit i j, ∑ η' : EdgeChoice.CosetIndex Γ (chij ε'),
            ((EdgeChoice.rep Γ (chij ε') η' * (chij ε').τ⁻¹)
              (((Pi.single ε ((tauEdgeAlgEquiv (chij ε)).symm y) : Γ.toSpecies.M i j) ε' : L)))
              • g ε' η')
          = ∑ η' : EdgeChoice.CosetIndex Γ (chij ε),
              (EdgeChoice.rep Γ (chij ε) η' ((y : L))) • g ε η' := by
      intro N' g
      refine Eq.trans (Finset.sum_eq_single ε (fun ε' _ hne => ?_)
        (fun hε => absurd (Finset.mem_univ ε) hε)) ?_
      · refine Finset.sum_eq_zero fun η' _ => ?_
        rw [show ((Pi.single ε ((tauEdgeAlgEquiv (chij ε)).symm y) :
            Γ.toSpecies.M i j) ε' : ↥(Γ.edgeOrbitField ε')) = 0 from
          Pi.single_eq_of_ne hne _]
        show ((EdgeChoice.rep Γ (chij ε') η' * (chij ε').τ⁻¹) (0 : L)) • g ε' η' = 0
        rw [map_zero, zero_smul]
      · refine Finset.sum_congr rfl fun η' _ => ?_
        rw [show ((Pi.single ε ((tauEdgeAlgEquiv (chij ε)).symm y) :
            Γ.toSpecies.M i j) ε : ↥(Γ.edgeOrbitField ε))
              = (tauEdgeAlgEquiv (chij ε)).symm y from Pi.single_eq_same _ _]
        have hsc : (EdgeChoice.rep Γ (chij ε) η' * (chij ε).τ⁻¹)
            (((tauEdgeAlgEquiv (chij ε)).symm y : ↥(Γ.edgeOrbitField ε)) : L)
            = EdgeChoice.rep Γ (chij ε) η' ((y : L)) := by
          rw [AlgEquiv.mul_apply]
          congr 1
          show (chij ε).τ⁻¹ ((chij ε).τ ((y : L))) = (y : L)
          exact (chij ε).τ.symm_apply_apply (y : L)
        rw [hsc]
    rw [hcollapse _ (fun ε' η' => psi (Γ.vertexRep j)
        (phiComp M.toRep (chij ε') η' w))] at hsum
    rw [hcollapse _ (fun ε' η' => phiComp (H.obj (F.obj M)).toRep (chij ε') η'
        (unitFix F H eF eHfix M i w))] at hsum
    rw [hD]
    refine Eq.trans (Finset.sum_congr rfl fun η' _ => smul_sub _ _ _) ?_
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have := eta_separation (chij ε) D hzero η
  rw [hD] at this
  exact sub_eq_zero.mp this

/-! ### Step 4 — from `phiComp` to `φEdge`  (G4)

`phiComp = φ'_{ρ_η} ∘ φ_{e_ε} ∘ φ'_{σ_ε}`, so `rational` strips the two outer factors and leaves
the edge maps agreeing on `φ'_{σ_ε}(W_i)`.  Three moves, each with a compiled precedent in
`RQ2-2.28`: **spanning** (`vertexDescentEquiv`'s surjectivity — `W_i` spans `M(v_i)` over `L`),
**`L`-linear extension**, and **clause `RQ2-1.08-C9`** to reach every edge.

@census none (G4 engine for `RQ2-2.29`)
-/

/-- **Step 4a**: the edge maps agree on the fixed vectors, after `rational` strips the two `φ'`s.
@census none (helper) -/
theorem unitFix_edgeRep_fixed (M : FDRep Γ) {i j : Γ.VertexOrbit}
    (ε : Γ.EdgeOrbit i j) (ch : Γ.EdgeChoice ε)
    (psi : ∀ v : Γ.V, M.toRep.M v →ₗ[L] (H.obj (F.obj M)).toRep.M v)
    (hrat : ∀ (σ : Gal(L/K)) (v w : Γ.V) (h : σ • v = w) (x : M.toRep.M v),
      psi w (M.toRep.φ' σ h x)
        = (H.obj (F.obj M)).toRep.φ' σ h (psi v x))
    (hfixi : ∀ (x : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
      psi (Γ.vertexRep i) ((x : M.toRep.M (Γ.vertexRep i)))
        = ((unitFix F H eF eHfix M i x :
            ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep i)))
          : (H.obj (F.obj M)).toRep.M (Γ.vertexRep i)))
    (η : EdgeChoice.CosetIndex Γ ch)
    (hcomp : ∀ (w : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
      psi (Γ.vertexRep j) (phiComp M.toRep ch η w)
        = phiComp (H.obj (F.obj M)).toRep ch η (unitFix F H eF eHfix M i w))
    (w : ↥(M.toRep.vertexFixed (Γ.vertexRep i))) :
    psi (Γ.toRQuiver.target (Γ.edgeRep ε))
        (M.toRep.φEdge' (Γ.edgeRep ε) rfl rfl
          (M.toRep.φ' ch.σ ch.sourceVertex ((w : M.toRep.M (Γ.vertexRep i)))))
      = (H.obj (F.obj M)).toRep.φEdge' (Γ.edgeRep ε) rfl rfl
          (psi (Γ.toRQuiver.source (Γ.edgeRep ε))
            (M.toRep.φ' ch.σ ch.sourceVertex ((w : M.toRep.M (Γ.vertexRep i))))) := by
  have h := hcomp w
  rw [phiComp, phiComp, hrat] at h
  refine ((H.obj (F.obj M)).toRep.φ' (EdgeChoice.rep Γ ch η * ch.τ⁻¹)
    (ch.cosetTarget η)).injective ?_
  rw [h, hrat, hfixi]

/-- **Step 4b**: the edge maps agree everywhere.  `W_i` spans `M(v_i)` over `L`
(`vertexDescentEquiv`'s surjectivity), `φ'_{σ_ε}` carries that spanning set across, and both sides
are `L`-linear.  @census none (helper) -/
theorem unitFix_edgeRep (M : FDRep Γ) {i j : Γ.VertexOrbit}
    (ε : Γ.EdgeOrbit i j) (ch : Γ.EdgeChoice ε)
    (psi : ∀ v : Γ.V, M.toRep.M v →ₗ[L] (H.obj (F.obj M)).toRep.M v)
    (hrat : ∀ (σ : Gal(L/K)) (v w : Γ.V) (h : σ • v = w) (x : M.toRep.M v),
      psi w (M.toRep.φ' σ h x)
        = (H.obj (F.obj M)).toRep.φ' σ h (psi v x))
    (hfixi : ∀ (x : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
      psi (Γ.vertexRep i) ((x : M.toRep.M (Γ.vertexRep i)))
        = ((unitFix F H eF eHfix M i x :
            ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep i)))
          : (H.obj (F.obj M)).toRep.M (Γ.vertexRep i)))
    (η : EdgeChoice.CosetIndex Γ ch)
    (hcomp : ∀ (w : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
      psi (Γ.vertexRep j) (phiComp M.toRep ch η w)
        = phiComp (H.obj (F.obj M)).toRep ch η (unitFix F H eF eHfix M i w))
    (y : M.toRep.M (Γ.toRQuiver.source (Γ.edgeRep ε))) :
    psi (Γ.toRQuiver.target (Γ.edgeRep ε))
        (M.toRep.φEdge' (Γ.edgeRep ε) rfl rfl y)
      = (H.obj (F.obj M)).toRep.φEdge' (Γ.edgeRep ε) rfl rfl
          (psi (Γ.toRQuiver.source (Γ.edgeRep ε)) y) := by
  -- pull `y` back across `φ'_{σ_ε}`, then across the descent
  obtain ⟨x, rfl⟩ : ∃ x, M.toRep.φ' ch.σ ch.sourceVertex x = y :=
    ⟨(M.toRep.φ' ch.σ ch.sourceVertex).symm y, AddEquiv.apply_symm_apply _ _⟩
  obtain ⟨z, rfl⟩ : ∃ z, vertexDescentEquiv M.toRep (Γ.vertexRep i) z = x :=
    ⟨(vertexDescentEquiv M.toRep (Γ.vertexRep i)).symm x,
      LinearEquiv.apply_symm_apply _ _⟩
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero, map_zero, map_zero]
  | tmul a w =>
      rw [vertexDescentEquiv_tmul, Rep.φ'_smul, LinearMap.map_smul, LinearMap.map_smul,
        LinearMap.map_smul, unitFix_edgeRep_fixed F H eF eHfix M ε ch psi hrat hfixi η hcomp w,
        LinearMap.map_smul]
  | add p q hp hq =>
      rw [map_add, map_add, map_add, map_add, map_add, map_add, hp, hq]

/-- Every edge is a translate of its orbit's representative.  Re-derived locally rather than
imported from `FunctorH`: the equivalent helper there is legitimate to use (it is about `Γ.E`
alone) but its name is in `§63.3`'s recorded leak grep, and **a check that has to be read with an
exception list is most of the way back to not being a check**.  Five lines is the right price for
keeping that command literally true.  @census none (helper) -/
theorem exists_smul_edgeRep' {i j : Γ.VertexOrbit} (e : Γ.E)
    (hs : Γ.vertexClass (Γ.toRQuiver.source e) = i)
    (ht : Γ.vertexClass (Γ.toRQuiver.target e) = j) :
    ∃ (ε : Γ.EdgeOrbit i j) (g : Gal(L/K)), g • Γ.edgeRep ε = e := by
  refine ⟨⟦⟨e, hs, ht⟩⟧, ?_⟩
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel Gal(L/K) (Γ.edgeSet i j)) (⟨e, hs, ht⟩)
  refine ⟨g⁻¹, ?_⟩
  show g⁻¹ • ((⟦(⟨e, hs, ht⟩ : Γ.edgeSet i j)⟧.out : Γ.edgeSet i j) : Γ.E) = e
  rw [← congrArg Subtype.val hg]
  show g⁻¹ • (g • e) = e
  rw [inv_smul_smul]

/-- **Step 4c**: the representative case carries to every edge of the orbit, by clause
`RQ2-1.08-C9` on both sides and `rational` in the middle.  @census none (helper) -/
theorem unitFix_edge_of_smul (M : FDRep Γ) {i j : Γ.VertexOrbit}
    (ε : Γ.EdgeOrbit i j) (ch : Γ.EdgeChoice ε)
    (psi : ∀ v : Γ.V, M.toRep.M v →ₗ[L] (H.obj (F.obj M)).toRep.M v)
    (hrat : ∀ (σ : Gal(L/K)) (v w : Γ.V) (h : σ • v = w) (x : M.toRep.M v),
      psi w (M.toRep.φ' σ h x)
        = (H.obj (F.obj M)).toRep.φ' σ h (psi v x))
    (hfixi : ∀ (x : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
      psi (Γ.vertexRep i) ((x : M.toRep.M (Γ.vertexRep i)))
        = ((unitFix F H eF eHfix M i x :
            ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep i)))
          : (H.obj (F.obj M)).toRep.M (Γ.vertexRep i)))
    (η : EdgeChoice.CosetIndex Γ ch)
    (hcomp : ∀ (w : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
      psi (Γ.vertexRep j) (phiComp M.toRep ch η w)
        = phiComp (H.obj (F.obj M)).toRep ch η (unitFix F H eF eHfix M i w))
    (g : Gal(L/K)) (e : Γ.E) (hge : g • Γ.edgeRep ε = e)
    (y : M.toRep.M (Γ.toRQuiver.source e)) :
    psi (Γ.toRQuiver.target e) (M.toRep.φEdge' e rfl rfl y)
      = (H.obj (F.obj M)).toRep.φEdge' e rfl rfl
          (psi (Γ.toRQuiver.source e) y) := by
  have hsrc : g • Γ.toRQuiver.source (Γ.edgeRep ε) = Γ.toRQuiver.source e := by
    rw [← hge, Γ.source_smul]
  have htgt : g • Γ.toRQuiver.target (Γ.edgeRep ε) = Γ.toRQuiver.target e := by
    rw [← hge, Γ.target_smul]
  obtain ⟨x, rfl⟩ : ∃ x, M.toRep.φ' g hsrc x = y :=
    ⟨(M.toRep.φ' g hsrc).symm y, AddEquiv.apply_symm_apply _ _⟩
  rw [M.toRep.φEdge'_φ' g hge rfl rfl rfl rfl hsrc htgt, hrat, hrat,
    unitFix_edgeRep F H eF eHfix M ε ch psi hrat hfixi η hcomp,
    ← (H.obj (F.obj M)).toRep.φEdge'_φ' g hge rfl rfl rfl rfl hsrc htgt]

/-! ### The counit's `comm` axiom  (G4)

`counitComp` is `eF` then `eHfix`, and both hypotheses pin a descent of `H V`'s edge maps against
the *same* `f_{ij}` — `hF1` says `F(H V)`'s structure map is that descent read through `eF`,
`hH1` says `V`'s own `f_{ij}` is that descent read through `eHfix`.  So the composite is the
species-morphism square, and the proof is the two hypotheses back to back.

The mirror of `unitFix_descent` (§d990f0c): there the two descents were pinned to `(F M)`'s `f`
and the unit carried one to the other; here one descent is pinned twice and the counit *is* the
comparison.

@census none (G4 engine for `RQ2-2.29`)
-/

set_option backward.isDefEq.respectTransparency.types false in
/-- **`RQ2-2.17-C5` for the counit** — its `comm` axiom on pure tensors.  @census none (helper) -/
theorem counitComp_comm (V : EtaleSpecies.Rep Γ.toSpecies) {i j : Γ.VertexOrbit}
    (chij : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL (H.obj V).toRep i j ≃ₗ[L] wiiMjLpreRhs (H.obj V).toRep chij)
    (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j
          ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
        →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep j)))
    (hd : IsEdgeDescent (H.obj V).toRep chij e₀ f)
    (hF1 : ∀ (w : (F.obj (H.obj V)).W i) (m : Γ.toSpecies.M i j),
      eF (H.obj V) j ((F.obj (H.obj V)).f i j (Balanced.mk w m))
        = f (Balanced.mk (eF (H.obj V) i w) m))
    (hH1 : ∀ (w : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i)))
        (m : Γ.toSpecies.M i j),
      eHfix V j (f (Balanced.mk w m))
        = EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk (eHfix V i w) m))
    (w : (F.obj (H.obj V)).W i) (m : Γ.toSpecies.M i j) :
    V.f i j (Balanced.mk (counitComp F H eF eHfix V i w) m)
      = counitComp F H eF eHfix V j ((F.obj (H.obj V)).f i j (Balanced.mk w m)) := by
  show _ = eHfix V j (eF (H.obj V) j ((F.obj (H.obj V)).f i j (Balanced.mk w m)))
  rw [hF1, hH1]
  rfl

/-! ### The counit, bundled  (G4)

`counitComp` with its `comm` axiom, as a morphism of `Rep(S(Γ_K))`.  The descent the two
hypotheses are applied to is obtained where every other row obtains one — `wiiMj_baseChange_pre`
for the pinned `e₀`, then `isEdgeDescent_edgeDescentMap`.

@census none (G4 engine for `RQ2-2.29`)
-/

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **The counit as a species morphism.**  @census none (helper for `RQ2-2.29`) -/
noncomputable def counitHom
    (hF1 : ∀ (M : FDRep Γ) (i j : Γ.VertexOrbit)
        (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
        (e₀ : wiiMjL M.toRep i j ≃ₗ[L] wiiMjLpreRhs M.toRep ch)
        (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j
              ↥(M.toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep j))),
      IsEdgeDescent M.toRep ch e₀ f →
      ∀ (w : (F.obj M).W i) (m : Γ.toSpecies.M i j),
        eF M j ((F.obj M).f i j (Balanced.mk w m)) = f (Balanced.mk (eF M i w) m))
    (hH1 : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i j : Γ.VertexOrbit)
        (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
        (e₀ : wiiMjL (H.obj V).toRep i j ≃ₗ[L] wiiMjLpreRhs (H.obj V).toRep ch)
        (fH : EtaleSpecies.Rep.tensor Γ.toSpecies i j
                ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
              →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep j))),
      IsEdgeDescent (H.obj V).toRep ch e₀ fH →
      ∀ (w : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i)))
          (m : Γ.toSpecies.M i j),
        eHfix V j (fH (Balanced.mk w m))
          = EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk (eHfix V i w) m))
    (V : EtaleSpecies.Rep Γ.toSpecies) :
    Species.Rep.Hom (F.obj (H.obj V)) V where
  ψ i := (counitComp F H eF eHfix V i).toLinearMap
  comm i j := by
    classical
    letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
    letI : ∀ ε : Γ.EdgeOrbit i j,
        Fintype (EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε)) :=
      fun ε => @Fintype.ofFinite _ (finite_cosetIndex (EdgeChoice.choose Γ ε))
    obtain ⟨e₀, h₀⟩ := wiiMj_baseChange_pre (H.obj V).toRep i j
      (fun ε : Γ.EdgeOrbit i j => EdgeChoice.choose Γ ε)
    have hd := isEdgeDescent_edgeDescentMap (H.obj V).toRep
      (fun ε : Γ.EdgeOrbit i j => EdgeChoice.choose Γ ε) e₀ h₀
    refine Balanced.hom_ext fun w m => ?_
    exact counitComp_comm F H eF eHfix V _ e₀ _ hd
      (fun w' m' => hF1 (H.obj V) i j _ e₀ _ hd w' m')
      (fun w' m' => hH1 V i j _ e₀ _ hd w' m') w m

/-- `vertexDescentEquiv` sends `1 ⊗ x` to `x`, hence its inverse sends a fixed vector to `1 ⊗ x`.
@census none (helper) -/
theorem vertexDescentEquiv_symm_coe (M : Rep Γ) (v : Γ.V) (x : ↥(M.vertexFixed v)) :
    (vertexDescentEquiv M v).symm ((x : M.M v)) = (1 : L) ⊗ₜ x := by
  refine (vertexDescentEquiv M v).injective ?_
  rw [LinearEquiv.apply_symm_apply, vertexDescentEquiv_tmul, one_smul]

/-- **The unit at the orbit representative agrees with `unitFix` on fixed vectors.**  This is the
bridge between the `L`-linear `unitRep` (which the `rational` field needs) and the `L_iᵐᵒᵖ`-linear
`unitFix` (which the `edge` field's whole chain is stated in).  @census none (helper) -/
theorem unitRep_coe (M : FDRep Γ) (i : Γ.VertexOrbit)
    (x : ↥(M.toRep.vertexFixed (Γ.vertexRep i))) :
    unitRep F H eF eHfix M i ((x : M.toRep.M (Γ.vertexRep i)))
      = ((unitFix F H eF eHfix M i x :
          ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep i)))
        : (H.obj (F.obj M)).toRep.M (Γ.vertexRep i)) := by
  show vertexDescentEquiv (H.obj (F.obj M)).toRep (Γ.vertexRep i)
      (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl L L)
        ((eFL F eF M i).symm.trans (eHfixL H eHfix (F.obj M) i).symm)
        ((vertexDescentEquiv M.toRep (Γ.vertexRep i)).symm ((x : M.toRep.M (Γ.vertexRep i))))) = _
  rw [vertexDescentEquiv_symm_coe]
  show (1 : L) • (((eHfixL H eHfix (F.obj M) i).symm ((eFL F eF M i).symm x) :
      ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep i))) :
      (H.obj (F.obj M)).toRep.M (Γ.vertexRep i)) = _
  rw [one_smul]
  rfl

/-- **The unit's vertex map**, at every vertex: translate to the orbit representative, apply
`unitRep`, translate back.  The conjugation family again (§62.9) — the same shape `H.map`'s `ψ`
needed.  @census none (helper for `RQ2-2.29`) -/
noncomputable def unitPsi (M : FDRep Γ) (v : Γ.V) :
    M.toRep.M v →ₗ[L] (H.obj (F.obj M)).toRep.M v :=
  unitAt F H eF eHfix M (Γ.vertexClass v) v (vertexTrans v) (vertexTrans_spec v)

/-- `Rep.Hom`'s `rational` field for `unitPsi`, in the `φ'` form the edge chain consumes.
@census none (helper) -/
theorem unitPsi_rational (M : FDRep Γ) (σ : Gal(L/K)) (v w : Γ.V) (h : σ • v = w)
    (x : M.toRep.M v) :
    unitPsi F H eF eHfix M w (M.toRep.φ' σ h x)
      = (H.obj (F.obj M)).toRep.φ' σ h (unitPsi F H eF eHfix M v x) := by
  subst h
  have hg' : (σ * vertexTrans v) • Γ.vertexRep (Γ.vertexClass v) = σ • v := by
    rw [mul_smul, vertexTrans_spec]
  show unitAt F H eF eHfix M (Γ.vertexClass (σ • v)) (σ • v)
      (vertexTrans (σ • v)) (vertexTrans_spec (σ • v)) (M.toRep.φ' σ rfl x) = _
  rw [← unitAt_congr' F H eF eHfix M (vertexClass_smul σ v).symm (σ • v)
    (σ * vertexTrans v) (vertexTrans (σ • v)) hg' (vertexTrans_spec (σ • v))]
  exact unitAt_rational F H eF eHfix M (Γ.vertexClass v) v
    (vertexTrans v) (σ * vertexTrans v) σ (vertexTrans_spec v) hg' x

/-- `unitPsi` at the orbit representative is `unitFix` — `unitAt_congr` kills the translation
(it lies in `G_{v_i}`), then `unitRep_coe`.  @census none (helper) -/
theorem unitPsi_fix (M : FDRep Γ) (i : Γ.VertexOrbit)
    (x : ↥(M.toRep.vertexFixed (Γ.vertexRep i))) :
    unitPsi F H eF eHfix M (Γ.vertexRep i) ((x : M.toRep.M (Γ.vertexRep i)))
      = ((unitFix F H eF eHfix M i x :
          ↥((H.obj (F.obj M)).toRep.vertexFixed (Γ.vertexRep i)))
        : (H.obj (F.obj M)).toRep.M (Γ.vertexRep i)) := by
  have hcl : Γ.vertexClass (Γ.vertexRep i) = i := Γ.vertexClass_vertexRep i
  rw [show unitPsi F H eF eHfix M (Γ.vertexRep i) ((x : M.toRep.M (Γ.vertexRep i)))
      = unitAt F H eF eHfix M i (Γ.vertexRep i) 1 (one_smul _ _)
          ((x : M.toRep.M (Γ.vertexRep i))) from
    unitAt_congr' F H eF eHfix M hcl (Γ.vertexRep i) _ 1 _ (one_smul _ _) _]
  show (H.obj (F.obj M)).toRep.φ' 1 (one_smul _ _)
      (unitRep F H eF eHfix M i ((M.toRep.φ' 1 (one_smul _ _)).symm
        ((x : M.toRep.M (Γ.vertexRep i))))) = _
  rw [show (M.toRep.φ' 1 (one_smul _ _)).symm ((x : M.toRep.M (Γ.vertexRep i)))
      = ((x : M.toRep.M (Γ.vertexRep i))) from
    (M.toRep.φ' 1 (one_smul _ _)).symm_apply_eq.mpr (x.2 ⟨1, one_smul _ _⟩).symm]
  rw [unitRep_coe]
  exact (unitFix F H eF eHfix M i x).2 ⟨1, one_smul _ _⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- **The unit, bundled.**  `ψ` is `unitPsi`; `rational` is `unitPsi_rational` read through
`φ'_rfl`; `edge` is the whole `unitFix_*` chain, whose three abstract inputs (`hrat`, `hfixi`,
`hcomp`) are now discharged.  @census none (helper for `RQ2-2.29`) -/
noncomputable def unitHom
    (hF1 : ∀ (M : FDRep Γ) (i j : Γ.VertexOrbit)
        (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
        (e₀ : wiiMjL M.toRep i j ≃ₗ[L] wiiMjLpreRhs M.toRep ch)
        (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j
              ↥(M.toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep j))),
      IsEdgeDescent M.toRep ch e₀ f →
      ∀ (w : (F.obj M).W i) (m : Γ.toSpecies.M i j),
        eF M j ((F.obj M).f i j (Balanced.mk w m)) = f (Balanced.mk (eF M i w) m))
    (hH1 : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i j : Γ.VertexOrbit)
        (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
        (e₀ : wiiMjL (H.obj V).toRep i j ≃ₗ[L] wiiMjLpreRhs (H.obj V).toRep ch)
        (fH : EtaleSpecies.Rep.tensor Γ.toSpecies i j
                ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
              →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep j))),
      IsEdgeDescent (H.obj V).toRep ch e₀ fH →
      ∀ (w : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i)))
          (m : Γ.toSpecies.M i j),
        eHfix V j (fH (Balanced.mk w m))
          = EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk (eHfix V i w) m))
    (M : FDRep Γ) : M ⟶ H.obj (F.obj M) where
  ψ v := unitPsi F H eF eHfix M v
  rational σ v m := by
    rw [← M.toRep.φ'_rfl σ v m,
      ← (H.obj (F.obj M)).toRep.φ'_rfl σ v (unitPsi F H eF eHfix M v m)]
    exact unitPsi_rational F H eF eHfix M σ v (σ • v) rfl m
  edge e m := by
    classical
    obtain ⟨ε, g, hge⟩ := exists_smul_edgeRep'
      (i := Γ.vertexClass (Γ.toRQuiver.source e))
      (j := Γ.vertexClass (Γ.toRQuiver.target e)) e rfl rfl
    letI : Fintype (Γ.EdgeOrbit (Γ.vertexClass (Γ.toRQuiver.source e))
        (Γ.vertexClass (Γ.toRQuiver.target e))) := Fintype.ofFinite _
    letI : ∀ ε' : Γ.EdgeOrbit (Γ.vertexClass (Γ.toRQuiver.source e))
        (Γ.vertexClass (Γ.toRQuiver.target e)),
        Fintype (EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε')) :=
      fun ε' => @Fintype.ofFinite _ (finite_cosetIndex (EdgeChoice.choose Γ ε'))
    obtain ⟨e₀M, h₀M⟩ := wiiMj_baseChange_pre M.toRep
      (Γ.vertexClass (Γ.toRQuiver.source e)) (Γ.vertexClass (Γ.toRQuiver.target e))
      (fun ε' => EdgeChoice.choose Γ ε')
    have hdM := isEdgeDescent_edgeDescentMap M.toRep
      (fun ε' => EdgeChoice.choose Γ ε') e₀M h₀M
    obtain ⟨e₀N, h₀N⟩ := wiiMj_baseChange_pre (H.obj (F.obj M)).toRep
      (Γ.vertexClass (Γ.toRQuiver.source e)) (Γ.vertexClass (Γ.toRQuiver.target e))
      (fun ε' => EdgeChoice.choose Γ ε')
    have hdN := isEdgeDescent_edgeDescentMap (H.obj (F.obj M)).toRep
      (fun ε' => EdgeChoice.choose Γ ε') e₀N h₀N
    have hint := unitFix_descent F H eF eHfix M (fun ε' => EdgeChoice.choose Γ ε')
      e₀M _ hdM e₀N _ hdN
      (fun w' m' => hF1 M _ _ _ e₀M _ hdM w' m')
      (fun w' m' => hH1 (F.obj M) _ _ _ e₀N _ hdN w' m')
    exact unitFix_edge_of_smul F H eF eHfix M ε (EdgeChoice.choose Γ ε)
      (fun v => unitPsi F H eF eHfix M v)
      (fun σ' v' w' h' x' => unitPsi_rational F H eF eHfix M σ' v' w' h' x')
      (fun x' => unitPsi_fix F H eF eHfix M _ x')
      (EdgeChoice.cosetOne (EdgeChoice.choose Γ ε))
      (fun w' => unitFix_phiComp F H eF eHfix M (fun ε' => EdgeChoice.choose Γ ε')
        (fun v => unitPsi F H eF eHfix M v) e₀M _ hdM e₀N _ hdN hint
        (fun x' => unitPsi_fix F H eF eHfix M _ x') ε _ w')
      g e hge m

/-- Two `L`-linear maps out of `M(v)` agreeing on the `G_v`-invariants are equal: the invariants
span after extension of scalars, which is `vertexDescentEquiv`'s surjectivity.  @census none -/
theorem linear_ext_fixed {M N : Rep Γ} (v : Γ.V) (f g : M.M v →ₗ[L] N.M v)
    (h : ∀ x : ↥(M.vertexFixed v), f ((x : M.M v)) = g ((x : M.M v))) (y : M.M v) :
    f y = g y := by
  obtain ⟨t, rfl⟩ := (vertexDescentEquiv M v).surjective y
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a x =>
      rw [vertexDescentEquiv_tmul, LinearMap.map_smul, LinearMap.map_smul, h]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

/-- **Naturality of the unit on the invariants** — `hF2` then `hH3`, the same pair the counit
needed, composed in the other order.  @census none (helper for `RQ2-2.29`) -/
theorem unitFix_naturality
    (hF2 : ∀ (M N : FDRep Γ) (φ : M ⟶ N)
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥(M.toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(N.toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (m : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i m : N.toRep.M (Γ.vertexRep i)))
          = φ.ψ (Γ.vertexRep i) (m : M.toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (w : (F.obj M).W i),
        eF N i ((F.map φ).ψ i w) = ψ' i (eF M i w))
    (hH3 : ∀ (V V' : EtaleSpecies.Rep Γ.toSpecies) (ψ : V ⟶ V')
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥((H.obj V').toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i u : (H.obj V').toRep.M (Γ.vertexRep i)))
          = (H.map ψ).ψ (Γ.vertexRep i) (u : (H.obj V).toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        eHfix V' i (ψ' i u) = ψ.ψ i (eHfix V i u))
    {M N : FDRep Γ} (φ : M ⟶ N) (i : Γ.VertexOrbit)
    (x : ↥(M.toRep.vertexFixed (Γ.vertexRep i))) :
    unitFix F H eF eHfix N i (Rep.Hom.vertexFixedMap φ i x)
      = Rep.Hom.vertexFixedMap (H.map (F.map φ)) i (unitFix F H eF eHfix M i x) := by
  refine (eHfix (F.obj N) i).injective ?_
  rw [hH3 (F.obj M) (F.obj N) (F.map φ)
    (fun i => Rep.Hom.vertexFixedMap (H.map (F.map φ)) i) (fun _ _ => rfl) i]
  show (eHfix (F.obj N) i) ((eHfix (F.obj N) i).symm
      ((eF N i).symm (Rep.Hom.vertexFixedMap φ i x))) = _
  rw [LinearEquiv.apply_symm_apply]
  show _ = (F.map φ).ψ i ((eHfix (F.obj M) i) ((eHfix (F.obj M) i).symm ((eF M i).symm x)))
  rw [LinearEquiv.apply_symm_apply]
  refine (eF N i).injective ?_
  rw [LinearEquiv.apply_symm_apply,
    hF2 M N φ (fun i => Rep.Hom.vertexFixedMap φ i) (fun _ _ => rfl) i ((eF M i).symm x),
    LinearEquiv.apply_symm_apply]

/-- Naturality of the unit at the orbit representative, on **all** of `M(v_i)` — the invariants
determine it (`linear_ext_fixed`).  @census none (helper) -/
theorem unitRep_naturality
    (hF2 : ∀ (M N : FDRep Γ) (φ : M ⟶ N)
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥(M.toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(N.toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (m : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i m : N.toRep.M (Γ.vertexRep i)))
          = φ.ψ (Γ.vertexRep i) (m : M.toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (w : (F.obj M).W i),
        eF N i ((F.map φ).ψ i w) = ψ' i (eF M i w))
    (hH3 : ∀ (V V' : EtaleSpecies.Rep Γ.toSpecies) (ψ : V ⟶ V')
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥((H.obj V').toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i u : (H.obj V').toRep.M (Γ.vertexRep i)))
          = (H.map ψ).ψ (Γ.vertexRep i) (u : (H.obj V).toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        eHfix V' i (ψ' i u) = ψ.ψ i (eHfix V i u))
    {M N : FDRep Γ} (φ : M ⟶ N) (i : Γ.VertexOrbit) (y : M.toRep.M (Γ.vertexRep i)) :
    unitRep F H eF eHfix N i (φ.ψ (Γ.vertexRep i) y)
      = (H.map (F.map φ)).ψ (Γ.vertexRep i) (unitRep F H eF eHfix M i y) := by
  refine linear_ext_fixed (Γ.vertexRep i)
    ((unitRep F H eF eHfix N i).toLinearMap ∘ₗ φ.ψ (Γ.vertexRep i))
    ((H.map (F.map φ)).ψ (Γ.vertexRep i) ∘ₗ (unitRep F H eF eHfix M i).toLinearMap)
    (fun x => ?_) y
  show unitRep F H eF eHfix N i (φ.ψ (Γ.vertexRep i) ((x : M.toRep.M (Γ.vertexRep i))))
    = (H.map (F.map φ)).ψ (Γ.vertexRep i)
        (unitRep F H eF eHfix M i ((x : M.toRep.M (Γ.vertexRep i))))
  rw [show φ.ψ (Γ.vertexRep i) ((x : M.toRep.M (Γ.vertexRep i)))
      = ((Rep.Hom.vertexFixedMap φ i x : ↥(N.toRep.vertexFixed (Γ.vertexRep i)))
        : N.toRep.M (Γ.vertexRep i)) from rfl,
    unitRep_coe, unitRep_coe]
  exact congrArg Subtype.val (unitFix_naturality F H eF eHfix hF2 hH3 φ i x)

/-- **The unit is natural**, at every vertex: conjugate `unitRep_naturality` by the translation.
The conjugation family once more.  @census none (helper for `RQ2-2.29`) -/
theorem unitPsi_naturality
    (hF2 : ∀ (M N : FDRep Γ) (φ : M ⟶ N)
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥(M.toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(N.toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (m : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i m : N.toRep.M (Γ.vertexRep i)))
          = φ.ψ (Γ.vertexRep i) (m : M.toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (w : (F.obj M).W i),
        eF N i ((F.map φ).ψ i w) = ψ' i (eF M i w))
    (hH3 : ∀ (V V' : EtaleSpecies.Rep Γ.toSpecies) (ψ : V ⟶ V')
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥((H.obj V').toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i u : (H.obj V').toRep.M (Γ.vertexRep i)))
          = (H.map ψ).ψ (Γ.vertexRep i) (u : (H.obj V).toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        eHfix V' i (ψ' i u) = ψ.ψ i (eHfix V i u))
    {M N : FDRep Γ} (φ : M ⟶ N) (v : Γ.V) (x : M.toRep.M v) :
    unitPsi F H eF eHfix N v (φ.ψ v x)
      = (H.map (F.map φ)).ψ v (unitPsi F H eF eHfix M v x) := by
  show (H.obj (F.obj N)).toRep.φ' (vertexTrans v) (vertexTrans_spec v)
      (unitRep F H eF eHfix N (Γ.vertexClass v)
        ((N.toRep.φ' (vertexTrans v) (vertexTrans_spec v)).symm (φ.ψ v x))) = _
  rw [show (N.toRep.φ' (vertexTrans v) (vertexTrans_spec v)).symm (φ.ψ v x)
      = φ.ψ (Γ.vertexRep (Γ.vertexClass v))
          ((M.toRep.φ' (vertexTrans v) (vertexTrans_spec v)).symm x) from by
    refine (N.toRep.φ' (vertexTrans v) (vertexTrans_spec v)).injective ?_
    rw [AddEquiv.apply_symm_apply, ← Rep.Hom.rational', AddEquiv.apply_symm_apply]]
  rw [unitRep_naturality F H eF eHfix hF2 hH3 φ]
  exact (Rep.Hom.rational' (H.map (F.map φ)) (vertexTrans v) (vertexTrans_spec v) _).symm

/-- A `Rep.Hom` with bijective components has an inverse `Rep.Hom`: the componentwise inverses
satisfy `edge` and `rational` because the forward map does.  @census none (helper) -/
noncomputable def repHomInv {M N : Rep Γ} (a : Rep.Hom M N)
    (hbij : ∀ v, Function.Bijective (a.ψ v)) : Rep.Hom N M where
  ψ v := (LinearEquiv.ofBijective (a.ψ v) (hbij v)).symm.toLinearMap
  edge e m := by
    refine (hbij (Γ.toRQuiver.target e)).1 ?_
    show a.ψ (Γ.toRQuiver.target e)
        ((LinearEquiv.ofBijective (a.ψ (Γ.toRQuiver.target e)) (hbij _)).symm (N.φEdge e m))
      = a.ψ (Γ.toRQuiver.target e) (M.φEdge e
          ((LinearEquiv.ofBijective (a.ψ (Γ.toRQuiver.source e)) (hbij _)).symm m))
    rw [a.edge]
    exact Eq.trans
      ((LinearEquiv.ofBijective (a.ψ (Γ.toRQuiver.target e)) (hbij _)).apply_symm_apply _)
      (congrArg (N.φEdge e)
        ((LinearEquiv.ofBijective (a.ψ (Γ.toRQuiver.source e)) (hbij _)).apply_symm_apply m)).symm
  rational σ v m := by
    refine (hbij (σ • v)).1 ?_
    show a.ψ (σ • v) ((LinearEquiv.ofBijective (a.ψ (σ • v)) (hbij _)).symm (N.φ σ v m))
      = a.ψ (σ • v) (M.φ σ v ((LinearEquiv.ofBijective (a.ψ v) (hbij v)).symm m))
    rw [a.rational]
    exact Eq.trans ((LinearEquiv.ofBijective (a.ψ (σ • v)) (hbij _)).apply_symm_apply _)
      (congrArg (N.φ σ v) ((LinearEquiv.ofBijective (a.ψ v) (hbij v)).apply_symm_apply m)).symm

/-- The same for `Species.Rep`.  @census none (helper) -/
noncomputable def speciesHomInv {V V' : EtaleSpecies.Rep Γ.toSpecies} (a : V ⟶ V')
    (hbij : ∀ i, Function.Bijective (a.ψ i)) : V' ⟶ V where
  ψ i := (LinearEquiv.ofBijective (a.ψ i) (hbij i)).symm.toLinearMap
  comm i j := by
    have hs : ∀ (k : Γ.VertexOrbit) (y : V'.W k),
        a.ψ k ((LinearEquiv.ofBijective (a.ψ k) (hbij k)).symm y) = y :=
      fun k y => (LinearEquiv.ofBijective (a.ψ k) (hbij k)).apply_symm_apply y
    refine Balanced.hom_ext fun w m => ?_
    show V.f i j (Balanced.mk ((LinearEquiv.ofBijective (a.ψ i) (hbij i)).symm w) m)
      = (LinearEquiv.ofBijective (a.ψ j) (hbij j)).symm (V'.f i j (Balanced.mk w m))
    refine (hbij j).1 ?_
    rw [hs, ← Species.Rep.Hom.comm_mk a i j, hs]

/-- `unitPsi` is bijective: `unitRep` is an equivalence and `φ'` is an isomorphism at both ends.
@census none (helper) -/
theorem unitPsi_bijective (M : FDRep Γ) (v : Γ.V) :
    Function.Bijective (unitPsi F H eF eHfix M v) := by
  have : ∀ x, unitPsi F H eF eHfix M v x
      = (H.obj (F.obj M)).toRep.φ' (vertexTrans v) (vertexTrans_spec v)
          (unitRep F H eF eHfix M (Γ.vertexClass v)
            ((M.toRep.φ' (vertexTrans v) (vertexTrans_spec v)).symm x)) := fun _ => rfl
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · rw [this, this] at hxy
    have h1 := ((H.obj (F.obj M)).toRep.φ' (vertexTrans v) (vertexTrans_spec v)).injective hxy
    have h2 := (unitRep F H eF eHfix M (Γ.vertexClass v)).injective h1
    exact (M.toRep.φ' (vertexTrans v) (vertexTrans_spec v)).symm.injective h2
  · refine ⟨(M.toRep.φ' (vertexTrans v) (vertexTrans_spec v))
      ((unitRep F H eF eHfix M (Γ.vertexClass v)).symm
        (((H.obj (F.obj M)).toRep.φ' (vertexTrans v) (vertexTrans_spec v)).symm z)), ?_⟩
    rw [this, AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply]

/-- `counitComp` is bijective — it is a composite of two equivalences.  @census none (helper) -/
theorem counitHom_bijective (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit) :
    Function.Bijective (counitComp F H eF eHfix V i) :=
  (counitComp F H eF eHfix V i).bijective

/-- **The counit is natural.**  This is the square that finding `S5-F9` was about: it consumes
`hF2` on the `F` side and `hH3` on the `H` side, and the two are used in immediate succession on
the same `ψ' := (H.map ψ).vertexFixedMap`.  With `hH3` absent the second step has no premise —
which is exactly the shape of the gap.  @census none (helper for `RQ2-2.29`) -/
theorem counitComp_naturality
    (hF2 : ∀ (M N : FDRep Γ) (φ : M ⟶ N)
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥(M.toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(N.toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (m : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i m : N.toRep.M (Γ.vertexRep i)))
          = φ.ψ (Γ.vertexRep i) (m : M.toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (w : (F.obj M).W i),
        eF N i ((F.map φ).ψ i w) = ψ' i (eF M i w))
    (hH3 : ∀ (V V' : EtaleSpecies.Rep Γ.toSpecies) (ψ : V ⟶ V')
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥((H.obj V').toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i u : (H.obj V').toRep.M (Γ.vertexRep i)))
          = (H.map ψ).ψ (Γ.vertexRep i) (u : (H.obj V).toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        eHfix V' i (ψ' i u) = ψ.ψ i (eHfix V i u))
    {V V' : EtaleSpecies.Rep Γ.toSpecies} (ψ : V ⟶ V') (i : Γ.VertexOrbit)
    (w : (F.obj (H.obj V)).W i) :
    counitComp F H eF eHfix V' i ((F.map (H.map ψ)).ψ i w)
      = ψ.ψ i (counitComp F H eF eHfix V i w) := by
  show eHfix V' i (eF (H.obj V') i ((F.map (H.map ψ)).ψ i w)) = _
  rw [hF2 (H.obj V) (H.obj V') (H.map ψ)
    (fun i => Rep.Hom.vertexFixedMap (H.map ψ) i) (fun _ _ => rfl) i w]
  exact hH3 V V' ψ (fun i => Rep.Hom.vertexFixedMap (H.map ψ) i) (fun _ _ => rfl) i _

/-! ### Finding **S5-F9** — the countermodel's compiled core  (G4)

`RQ2-2.29` as originally frozen could not be proved, and not for want of effort: **no hypothesis
constrained `H.map`.**  `F.map` occurred exactly once in the statement (inside `hF2`); `H.map`
occurred nowhere.  Since `Equivalence.mk` needs a *natural* isomorphism and the counit's naturality
square reduces — through `hF2` — to a statement about the descended vertex map of `H.map ψ`, the
square could not be verified.

**It was not merely unproved; it was false.**  The two lemmas below are the compilable heart of the
countermodel: `hH1`'s equation is invariant under rescaling `e_fix` by a scalar `c ∈ K`, at one
object, independently of every other hypothesis.  So two families of `e_fix` satisfying all the
hypotheses differ by `c`, and naturality distinguishes them.  (The full modified functor is not
constructed — it is not needed, and the coordinator's protocol asks for the cheap form.)

The docstring's own justification for omitting the `H`-side hypothesis was:

> *`RQ2-2.26-C4` and `RQ2-2.28-C5` — functoriality of `F` and of `H` — are **not** among the
> hypotheses … they are the `map_id`/`map_comp` fields of `CategoryTheory.Functor`, so `F` and `H`
> satisfy them by their types.  Adding them as hypotheses would be adding `True`.*

That is **right about `map_id`/`map_comp` and wrong about `RQ2-2.28-C5`'s other content**: the clause
also says what `H.map` *is*, which is not a functor field and not `True` — it is exactly what `hF2`
imports on the `F` side.  The omission was a **fields-versus-identification conflation**, and the
repair is `hH3`, mirroring `hF2`.

@census none (finding `S5-F9`'s evidence; kept so the reasoning stays checkable)
-/

/-- `K` scales `Balanced.mk` through either factor.  @census none (helper) -/
theorem balanced_mk_smul_K (V : EtaleSpecies.Rep Γ.toSpecies) (i j : Γ.VertexOrbit) (c : K)
    (x : V.W i) (m : Γ.toSpecies.M i j) :
    (Balanced.mk (K := K) (A := Γ.toSpecies.L i) (B := Γ.toSpecies.L j) (c • x) m)
      = c • Balanced.mk (K := K) (A := Γ.toSpecies.L i) (B := Γ.toSpecies.L j) x m := by
  refine Eq.trans (congrArg (fun z => Balanced.mk (K := K) (A := Γ.toSpecies.L i)
      (B := Γ.toSpecies.L j) z m) (V.smul_K_W i c x)) ?_
  refine Eq.trans (Balanced.mk_smul (K := K) (A := Γ.toSpecies.L i) (B := Γ.toSpecies.L j)
    (algebraMap K (Γ.toSpecies.L i) c) x m) ?_
  refine Eq.trans ?_ (Balanced.smul_K_mk (K := K) (A := Γ.toSpecies.L i)
    (B := Γ.toSpecies.L j) c x m).symm
  congr 1
  rw [IsScalarTower.algebraMap_smul (Γ.toSpecies.L i) c m,
    IsScalarTower.algebraMap_smul (Γ.toSpecies.L j)ᵐᵒᵖ c m]

/-- **Finding `S5-F9`, compiled.**  `hH1`'s equation survives rescaling `e_fix` by any `c ∈ K`.
Since `hF2`, `hH2` and `hWK` never mention `e_fix`, a family rescaled at a single object satisfies
every hypothesis of the row as originally frozen — and naturality distinguishes it from the
unrescaled one.  That is why `hH3` is needed.  @census none (`S5-F9` evidence) -/
theorem hH1_rescaled (V : EtaleSpecies.Rep Γ.toSpecies) {i j : Γ.VertexOrbit}
    (eHfix' : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (k : Γ.VertexOrbit),
      ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep k)) →ₗ[(Γ.toSpecies.L k)ᵐᵒᵖ] V.W k)
    (fH : EtaleSpecies.Rep.tensor Γ.toSpecies i j
            ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
          →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep j)))
    (hH1 : ∀ (w : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i)))
        (m : Γ.toSpecies.M i j),
      eHfix' V j (fH (Balanced.mk w m))
        = EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk (eHfix' V i w) m))
    (c : K) (w : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i)))
    (m : Γ.toSpecies.M i j) :
    c • eHfix' V j (fH (Balanced.mk w m))
      = EtaleSpecies.Rep.f' Γ.toSpecies V i j
          (Balanced.mk (c • eHfix' V i w) m) := by
  rw [balanced_mk_smul_K, hH1]
  exact (LinearMap.map_smul_of_tower (EtaleSpecies.Rep.f' Γ.toSpecies V i j) c _).symm

/-- **The unit as a natural isomorphism** `𝟭 ≅ F ⋙ H`.  @census none (helper for `RQ2-2.29`) -/
noncomputable def unitIso (hF1 : ∀ (M : FDRep Γ) (i j : Γ.VertexOrbit)
        (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
        (e₀ : wiiMjL M.toRep i j ≃ₗ[L] wiiMjLpreRhs M.toRep ch)
        (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j
              ↥(M.toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep j))),
      IsEdgeDescent M.toRep ch e₀ f →
      ∀ (w : (F.obj M).W i) (m : Γ.toSpecies.M i j),
        eF M j ((F.obj M).f i j (Balanced.mk w m)) = f (Balanced.mk (eF M i w) m))
    (hH1 : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i j : Γ.VertexOrbit)
        (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
        (e₀ : wiiMjL (H.obj V).toRep i j ≃ₗ[L] wiiMjLpreRhs (H.obj V).toRep ch)
        (fH : EtaleSpecies.Rep.tensor Γ.toSpecies i j
                ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
              →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep j))),
      IsEdgeDescent (H.obj V).toRep ch e₀ fH →
      ∀ (w : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i)))
          (m : Γ.toSpecies.M i j),
        eHfix V j (fH (Balanced.mk w m))
          = EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk (eHfix V i w) m))
    (hF2 : ∀ (M N : FDRep Γ) (φ : M ⟶ N)
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥(M.toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(N.toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (m : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i m : N.toRep.M (Γ.vertexRep i)))
          = φ.ψ (Γ.vertexRep i) (m : M.toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (w : (F.obj M).W i),
        eF N i ((F.map φ).ψ i w) = ψ' i (eF M i w))
    (hH3 : ∀ (V V' : EtaleSpecies.Rep Γ.toSpecies) (ψ : V ⟶ V')
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥((H.obj V').toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i u : (H.obj V').toRep.M (Γ.vertexRep i)))
          = (H.map ψ).ψ (Γ.vertexRep i) (u : (H.obj V).toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        eHfix V' i (ψ' i u) = ψ.ψ i (eHfix V i u)) :
    CategoryTheory.Functor.id (FDRep Γ) ≅ F.comp H :=
  CategoryTheory.NatIso.ofComponents
    (fun M =>
      { hom := unitHom F H eF eHfix hF1 hH1 M
        inv := repHomInv (unitHom F H eF eHfix hF1 hH1 M)
          (unitPsi_bijective F H eF eHfix M)
        hom_inv_id := Rep.Hom.ext (funext fun v => LinearMap.ext fun x =>
          (LinearEquiv.ofBijective _ (unitPsi_bijective F H eF eHfix M v)).symm_apply_apply x)
        inv_hom_id := Rep.Hom.ext (funext fun v => LinearMap.ext fun x =>
          (LinearEquiv.ofBijective _ (unitPsi_bijective F H eF eHfix M v)).apply_symm_apply x) })
    (fun φ => Rep.Hom.ext (funext fun v => LinearMap.ext fun x =>
      unitPsi_naturality F H eF eHfix hF2 hH3 φ v x))

/-- **The counit as a natural isomorphism** `H ⋙ F ≅ 𝟭`.  @census none (helper for `RQ2-2.29`) -/
noncomputable def counitIso (hF1 : ∀ (M : FDRep Γ) (i j : Γ.VertexOrbit)
        (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
        (e₀ : wiiMjL M.toRep i j ≃ₗ[L] wiiMjLpreRhs M.toRep ch)
        (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j
              ↥(M.toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep j))),
      IsEdgeDescent M.toRep ch e₀ f →
      ∀ (w : (F.obj M).W i) (m : Γ.toSpecies.M i j),
        eF M j ((F.obj M).f i j (Balanced.mk w m)) = f (Balanced.mk (eF M i w) m))
    (hH1 : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i j : Γ.VertexOrbit)
        (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
        (e₀ : wiiMjL (H.obj V).toRep i j ≃ₗ[L] wiiMjLpreRhs (H.obj V).toRep ch)
        (fH : EtaleSpecies.Rep.tensor Γ.toSpecies i j
                ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
              →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep j))),
      IsEdgeDescent (H.obj V).toRep ch e₀ fH →
      ∀ (w : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i)))
          (m : Γ.toSpecies.M i j),
        eHfix V j (fH (Balanced.mk w m))
          = EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk (eHfix V i w) m))
    (hF2 : ∀ (M N : FDRep Γ) (φ : M ⟶ N)
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥(M.toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(N.toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (m : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i m : N.toRep.M (Γ.vertexRep i)))
          = φ.ψ (Γ.vertexRep i) (m : M.toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (w : (F.obj M).W i),
        eF N i ((F.map φ).ψ i w) = ψ' i (eF M i w))
    (hH3 : ∀ (V V' : EtaleSpecies.Rep Γ.toSpecies) (ψ : V ⟶ V')
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥((H.obj V').toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i u : (H.obj V').toRep.M (Γ.vertexRep i)))
          = (H.map ψ).ψ (Γ.vertexRep i) (u : (H.obj V).toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        eHfix V' i (ψ' i u) = ψ.ψ i (eHfix V i u)) :
    H.comp F ≅ CategoryTheory.Functor.id (EtaleSpecies.Rep Γ.toSpecies) :=
  CategoryTheory.NatIso.ofComponents
    (fun V =>
      { hom := counitHom F H eF eHfix hF1 hH1 V
        inv := speciesHomInv (counitHom F H eF eHfix hF1 hH1 V)
          (counitHom_bijective F H eF eHfix V)
        hom_inv_id := Species.Rep.Hom.ext (funext fun i => LinearMap.ext fun w =>
          (LinearEquiv.ofBijective _ (counitHom_bijective F H eF eHfix V i)).symm_apply_apply w)
        inv_hom_id := Species.Rep.Hom.ext (funext fun i => LinearMap.ext fun w =>
          (LinearEquiv.ofBijective _ (counitHom_bijective F H eF eHfix V i)).apply_symm_apply w) })
    (fun ψ => Species.Rep.Hom.ext (funext fun i => LinearMap.ext fun w =>
      counitComp_naturality F H eF eHfix hF2 hH3 ψ i w))

end Summit

set_option backward.isDefEq.respectTransparency.types false in
/-- **Theorem `thm:species_equivalence`** (census `RQ2-2.29`) — the paper's second main theorem.

For a `K`-rational quiver `Γ_K` (clause `RQ2-2.29-H1`), the category `Rep(Γ_K)` of
**finite-dimensional** `K`-rational representations is **equivalent** to the category
`Rep(S(Γ_K))` of finite-dimensional representations of the associated `K`-species (clauses
`RQ2-2.29-C1` and `RQ2-2.29-C4`), the equivalence being given by the functors `F` of `RQ2-2.26` and
`H` of `RQ2-2.28`, which are **quasi-inverse**: `F ∘ H ≅ Id` (clause `RQ2-2.29-C2`) and
`H ∘ F ≅ Id` (clause `RQ2-2.29-C3`). On objects the identifications are
`M(v_i)^{G_{v_i}} ⊗_{L_i} L ≅ M(v_i)` and `(W_i ⊗_{L_i} L)^{G_{v_i}} ≅ W_i`, by Galois descent
(clause `RQ2-2.29-C5`, as it read before census r18; see the divergence field).

@census    RQ2-2.29
@source    thm:species_equivalence
@clauses   RQ2-2.29-H1, RQ2-2.29-C1, RQ2-2.29-C2, RQ2-2.29-C3, RQ2-2.29-C4, RQ2-2.29-C5
@imports   none
@divergence JUSTIFIED_REFORMULATION on clauses `RQ2-2.29-C2` and `RQ2-2.29-C3`; WEAKENED_OR_PARTIAL on
clause `RQ2-2.29-C5` (**added 2026-10-03**, docstring-only `R-PROC-4` amendment of frozen S5,
coordinator ruling `R-FR-9`, final-release WP-16b, `MISMATCH-TRIAGE.md` row #8).

`C5` — census r18 re-synced `C5` to the amended **proof** of `thm:species_equivalence`. It now
gives the unit and counit explicitly: the counit `FH(W)_i = W_{i,K} ⊗_K L_i → W_i`, `w ⊗ a ↦ wa`,
an isomorphism carrying the structure maps to the `f_{ij}`; the unit as the inverse of
`HF(M)(v) = W_i ⊗_{L_i,σ} L → M(σ v_i)`, `w ⊗ a ↦ φ_{v_i,σ}(w)·a`, independent of `σ` modulo
`G_{v_i}` and intertwining `eq:varphi2` with the `φ_{v,τ}` and the edge maps. The statement's first
conjunct still asserts the pre-r18 form, two bare `Nonempty` object-level identifications ("naturally
isomorphic by Galois descent"). The explicit maps are the **construction** of the equivalence's
`unitIso`/`counitIso` above (built from `unitHom` and `counitHom`), but the statement does not pin `e.unitIso`/`e.counitIso`
to these formulas. The theorem's own statement (an equivalence with `e.functor = F` and
`e.inverse = H`) is met, and `species_equivalence_tree` makes it unconditional. The gap is in the
proof detail that `C5` transcribes. Pinning the formulas for the tree functors would take about
150–250 lines and is not done (`MISMATCH-TRIAGE.md` §5, optional).

`C2`/`C3` — "`F ∘ H ≅ Id` and `H ∘ F ≅ Id`" are delivered as the **unit and counit isomorphisms of
a `CategoryTheory.Equivalence`** rather than as two free-standing `NatIso`s. That is
`CONVENTIONS.md` §7's explicit instruction ("an *equivalence* in the paper becomes an
`Equivalence`, not a pair of functors plus two `Iso`s stated by hand"), and it is *stronger* than
the pair: an `Equivalence` additionally carries the triangle identity relating them. The two
isomorphisms are then recovered as `e.counitIso` and `e.unitIso`, and the statement names them so
the clauses have mechanical dischargers.

**`C4` is not a conjunct because it is carried by the types.** "Both sides are the categories of
**finite-dimensional** representations" is `FDRep Γ` on the left — whose `finiteDimensional` field
is stage S2's design decision **D7** — and `Species.Rep` on the right, whose `finite_W` field is
clause `RQ2-2.17-C1`. Neither category *has* non-finite-dimensional objects, so there is nothing to
assert; the clause is discharged by the two object types appearing in the equivalence.

The universal quantification over `F` and `H` is the pinned-functors standard adapted to
existential functors; see the module header.

**Finding `V-S5b-4`.**  As first frozen this row imported only the two *identifications* `eF`/`eH`,
not the rows' characterisations, and was refutable twice over: the functor with all structure maps
`0` satisfies `eF` with the same `e` but is not essentially surjective, and `WK V i := ⊥` makes
`eH` hold for the zero functor while the conclusion's first conjunct asserts `0 ≃ V.W i`.  The
hypotheses now carry `RQ2-2.26`'s `C1`/`C2` (as `hF1`/`hF2`), `RQ2-2.28`'s `H2`(a) and `C3` (as
`hH1`/`hH2`), and `IsKRationalStructure` on `WK` (as `hWK`, finding `V-S5b-2`).  Both
counter-instantiations are now excluded: `hF1` pins `F`'s structure maps to the descents, and `hWK`
forbids `WK := ⊥`.

~~`RQ2-2.26-C4` and `RQ2-2.28-C5` — functoriality of `F` and of `H` — are **not** among the
hypotheses, for the same reason `C4` is not among the conclusions: they are the `map_id`/`map_comp`
fields of `CategoryTheory.Functor`, so `F` and `H` satisfy them by their types.  Adding them as
hypotheses would be adding `True`.~~

**Struck through by finding `S5-F9`; `hH3` added.**  The argument above is right about
`map_id`/`map_comp` and wrong about the rest of `RQ2-2.28-C5`, which also says *what `H.map` is*.
That is not a functor field, is not `True`, and is exactly what `hF2` imports on the `F` side —
the omission was a **fields-versus-identification conflation**, and it left the statement
**asymmetric**: `F.map` occurred once (in `hF2`), `H.map` nowhere.

The gap was not cosmetic.  `Equivalence.mk` demands a *natural* isomorphism, and the counit's
naturality square reduces through `hF2` to a claim about the descended vertex map of `H.map ψ`.
With `H.map` unconstrained the row was **false, not merely unproved**: `hH1_rescaled` (above)
compiles the countermodel's core — rescaling `eHfix` at a single object by `c ∈ K` preserves
`hH1`'s equation, while `hF2`, `hH2` and `hWK` never mention `eHfix` at all (design note §63.4
records `eH` and `eHfix` as uncoupled), so every hypothesis survives and every naturality square
through that object gains a factor `c`.  The route-around was measured and is closed: per-`i`
rescaling forces `c_i = c_j` only where `f'` is nonzero, so a global `K^×` freedom remains.

`hH3` repairs it, mirroring `hF2` clause for clause.  It is the same class of formalization-side
pinning hypothesis as `hF1`/`hH1` (precedent: finding `S5-F6`), so the census is untouched and no
author erratum arises — the defect is in this statement layer's universal-over-`F`-and-`H` design,
not in the source.

> **Dated correction, 2026-09-02 (`WORKFLOW.md` §7 / R6; G4 finding `V-S5G4-3`(c)).** This
> paragraph ended "Non-vacuity survives by construction: `hMapHom` (`b1f18a3`, `3265ae4`) already
> proves this project's own `H` satisfies it."  `hMapHom` is a **`def`** — the morphism map of
> `hFunctor` — not a theorem of `hH3`'s shape, so it proved nothing of the sort, and the G4
> verifier was right to refuse the claim.  The witness now exists and is compiled:
> **`hFunctor_hH3`** (`Species/Rep/FunctorH.lean`) discharges `hH3` for `hFunctor`, and
> `species_equivalence_at_tree_functors` / `species_equivalence_tree` (below) apply this row to
> `FFunctor` and `hFunctor` with **every** hypothesis discharged — the second of the two
> unconditionally, the `K`-rational structures coming from `exists_isKRationalStructure` and the
> edge choice from `EdgeChoice.choose`.  Non-vacuity is therefore a compiled fact, not a
> construction-by-inspection.

Corroboration from this docstring's own proof plan, below: it ends *"naturality is the source's
'straightforward verification considering morphisms', which is `RQ2-2.25-C4` and `RQ2-2.28-C5` on
morphisms."*  The plan therefore **names `RQ2-2.28-C5` on morphisms as an input to naturality** in
the same breath the hypothesis paragraph dismissed it as `True`.  The two paragraphs contradicted
each other; `hH3` is the plan's reading made into a binder.

Proof plan (G4), the source's own: on objects, `F(H(W)) ≅ W` is `(W_i ⊗_{L_i} L)^{G_{v_i}} ≅ W_i`
and `H(F(M)) ≅ M` is `M(v_i)^{G_{v_i}} ⊗_{L_i} L ≅ M(v_i)`, both Galois descent (`RQ2-1.13`,
consumed as a proved theorem — the whole point of design decision **D1**); the structure maps are
recovered because `F`'s `f_{ij}` and `H`'s `φ_e` are defined from each other through the same
identification `eq:WiiMjL` / `eq:WiiMjL2`; naturality is the source's "straightforward
verification considering morphisms", which is `RQ2-2.25-C4` and `RQ2-2.28-C5` on morphisms.
-/
theorem species_equivalence
    (F : CategoryTheory.Functor (FDRep Γ) (EtaleSpecies.Rep Γ.toSpecies))
    (H : CategoryTheory.Functor (EtaleSpecies.Rep Γ.toSpecies) (FDRep Γ))
    (WK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit), Submodule K (V.W i))
    (hWK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
      IsKRationalStructure V i (WK V i))
    (eF : ∀ (M : FDRep Γ) (i : Γ.VertexOrbit),
      (F.obj M).W i ≃ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep i)))
    (eH : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (v : Γ.V),
      (H.obj V).toRep.M v ≃ₗ[L] hObj V (WK V) (Γ.vertexClass v))
    (eHfix : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
      ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i)) ≃ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] V.W i)
    -- `RQ2-2.26-C1`: `F`'s structure maps are the descents `f_{ij}`
    (hF1 : ∀ (M : FDRep Γ) (i j : Γ.VertexOrbit)
        (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
        (e₀ : wiiMjL M.toRep i j ≃ₗ[L] wiiMjLpreRhs M.toRep ch)
        (f : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.toRep.vertexFixed (Γ.vertexRep i))
              →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥(M.toRep.vertexFixed (Γ.vertexRep j))),
      IsEdgeDescent M.toRep ch e₀ f →
      ∀ (w : (F.obj M).W i) (m : Γ.toSpecies.M i j),
        eF M j ((F.obj M).f i j (Balanced.mk w m)) = f (Balanced.mk (eF M i w) m))
    -- `RQ2-2.26-C2`: `F`'s morphism map is `RQ2-2.25`'s `ψ_i`
    (hF2 : ∀ (M N : FDRep Γ) (φ : M ⟶ N)
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥(M.toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥(N.toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (m : ↥(M.toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i m : N.toRep.M (Γ.vertexRep i)))
          = φ.ψ (Γ.vertexRep i) (m : M.toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (w : (F.obj M).W i),
        eF N i ((F.map φ).ψ i w) = ψ' i (eF M i w))
    -- `RQ2-2.28-H2`(a): `H`'s edge maps descend to `V`'s own structure map
    (hH1 : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i j : Γ.VertexOrbit)
        (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
        (e₀ : wiiMjL (H.obj V).toRep i j ≃ₗ[L] wiiMjLpreRhs (H.obj V).toRep ch)
        (fH : EtaleSpecies.Rep.tensor Γ.toSpecies i j
                ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
              →ₗ[(Γ.toSpecies.L j)ᵐᵒᵖ] ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep j))),
      IsEdgeDescent (H.obj V).toRep ch e₀ fH →
      ∀ (w : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j),
        eHfix V j (fH (Balanced.mk w m))
          = EtaleSpecies.Rep.f' Γ.toSpecies V i j (Balanced.mk (eHfix V i w) m))
    -- `RQ2-2.28-C3`: the translation acts through `L` alone
    (hH2 : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (v : Γ.V) (η : Gal(L/K)) (hη : η • v = v)
        (a : L) (w : ↥(WK V (Γ.vertexClass v))),
      eH V v ((H.obj V).toRep.φ' η hη ((eH V v).symm (a ⊗ₜ w))) = η a ⊗ₜ w)
    -- `RQ2-2.28-C5`, morphism content: `H`'s morphism map is the base change of `ψ_i`.
    -- Added per finding `S5-F9`; mirrors `hF2` on the `H` side.  Without it nothing in the
    -- statement constrains `H.map`, and `hH1_rescaled` shows the conclusion then fails.
    (hH3 : ∀ (V V' : EtaleSpecies.Rep Γ.toSpecies) (ψ : V ⟶ V')
        (ψ' : ∀ i : Γ.VertexOrbit,
          ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
            →ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] ↥((H.obj V').toRep.vertexFixed (Γ.vertexRep i))),
      (∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        ((ψ' i u : (H.obj V').toRep.M (Γ.vertexRep i)))
          = (H.map ψ).ψ (Γ.vertexRep i) (u : (H.obj V).toRep.M (Γ.vertexRep i))) →
      ∀ (i : Γ.VertexOrbit) (u : ↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))),
        eHfix V' i (ψ' i u) = ψ.ψ i (eHfix V i u)) :
    -- `C5`: the two object-level identifications, by Galois descent
    ((∀ (M : FDRep Γ) (i : Γ.VertexOrbit),
        Nonempty (Balanced K (Γ.toSpecies.L i) L L ↥(M.toRep.vertexFixed (Γ.vertexRep i))
          ≃ₗ[L] M.toRep.M (Γ.vertexRep i))) ∧
      (∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
        Nonempty (↥((H.obj V).toRep.vertexFixed (Γ.vertexRep i))
          ≃ₗ[(Γ.toSpecies.L i)ᵐᵒᵖ] V.W i))) ∧
    -- `C1`, `C2`, `C3`: an equivalence whose functor is `F` and whose inverse is `H`
    ∃ e : CategoryTheory.Equivalence (FDRep Γ) (EtaleSpecies.Rep Γ.toSpecies),
      e.functor = F ∧ e.inverse = H := by
  refine ⟨⟨fun M i => ⟨vertexDescentBalanced M.toRep i⟩, fun V i => ⟨eHfix V i⟩⟩, ?_⟩
  exact ⟨CategoryTheory.Equivalence.mk F H
    (unitIso F H eF eHfix hF1 hH1 hF2 hH3)
    (counitIso F H eF eHfix hF1 hH1 hF2 hH3), rfl, rfl⟩

/-! ### Theorem B at **this tree's own functors** — the G5 non-vacuity witness  (`V-S5G4-3`(c))

`species_equivalence` is universal over `F`, `H`, three identifications and five characterising
hypotheses.  That shape was adjudicated at G2 and is right — it is what makes the row say *which*
functors the equivalence is between rather than merely that some equivalence exists — but it is
**only** as strong as the hypothesis bundle is inhabited, and a vacuous universal passes every
mechanical gate in the battery.  The G4 verifier measured that nothing in the tree applied the row
to anything, and that the docstring's witness for the G4-era binder `hH3` (`hMapHom`) is a `def`,
not a proof.  That is finding `V-S5G4-3`(c).

The two theorems below close it, in the shape the finding asked for.

* `species_equivalence_at_tree_functors` applies `species_equivalence` to `FFunctor` and
  `hFunctor` — the functors `RQ2-2.26` and `RQ2-2.28` construct, i.e. the ones the paper's Theorem B
  is actually about — discharging all eight hypotheses by name:
  `hWK` by the argument, `eF`/`eH` by `LinearEquiv.refl`, `eHfix` by `eFix`,
  `hF1`/`hF2` by `FFunctor_hF1`/`FFunctor_hF2`, `hH1` by `hObjRep_edgeDescent_eq`,
  `hH2` by `hObjRep_phi'_tmul`, and `hH3` by `hFunctor_hH3`.
* `species_equivalence_tree` removes the two remaining choices: the `K`-rational structures come
  from `exists_isKRationalStructure` (`Species/Rep/FunctorH.lean`, G5) and the edge choice from
  `EdgeChoice.choose` (`Species/Rep/Decomposition.lean`, G5).  It is **unconditional**: no
  hypothesis, no free variable but `Γ` itself.  With it, `RQ2-2.29-C1`'s content — an equivalence
  `Rep(Γ_K) ≌ Rep(S(Γ_K))` whose functor is this tree's `F` and whose inverse is this tree's `H` —
  is asserted, not merely conditional.

Neither theorem carries a census id: they are witnesses, and `RQ2-2.29` remains claimed by
`species_equivalence`.  Neither weakens anything: they are instances of the row, so any weakening
of them would be a weakening of the row, and `rqaudit clauses` reads the row.

@census none (G5 non-vacuity witnesses for `RQ2-2.29`; finding `V-S5G4-3`(c))
-/

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Theorem B, instantiated at the tree's own functors.**  `species_equivalence` applied to
`FFunctor` (`RQ2-2.26`) and `hFunctor` (`RQ2-2.28`), with all eight hypotheses discharged by named
theorems of this stage.  The two arguments that remain are genuine data of `H` itself — the family
of `K`-rational structures and the edge choice — not undischarged obligations; `exists_isKRationalStructure`
and `EdgeChoice.choose` inhabit them, which is what `species_equivalence_tree` does below.

@census none (G5 non-vacuity witness for `RQ2-2.29`) -/
theorem species_equivalence_at_tree_functors
    (WK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit), Submodule K (V.W i))
    (hWK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
      IsKRationalStructure V i (WK V i))
    (ch : ∀ (i j : Γ.VertexOrbit) (ε : Γ.EdgeOrbit i j), Γ.EdgeChoice ε) :
    ∃ e : CategoryTheory.Equivalence (FDRep Γ) (EtaleSpecies.Rep Γ.toSpecies),
      e.functor = FFunctor Γ ∧ e.inverse = hFunctor WK hWK ch :=
  (species_equivalence Γ (FFunctor Γ) (hFunctor WK hWK ch) WK hWK
    (fun _ _ => LinearEquiv.refl _ _)
    (fun V v => LinearEquiv.refl L (hObj V (WK V) (Γ.vertexClass v)))
    (fun V i => eFix V (WK V) (hWK V) ch i)
    (fun M i j chij e₀ f hf w m => FFunctor_hF1 Γ M i j chij e₀ f hf w m)
    (fun M N φ ψ' hψ' i w => FFunctor_hF2 Γ M N φ ψ' hψ' i w)
    (fun V i j chij e₀ fH hd w m =>
      hObjRep_edgeDescent_eq V (WK V) (hWK V) ch chij e₀ fH hd w m)
    (fun V v η hη a w => hObjRep_phi'_tmul WK hWK ch V v η hη a w)
    (fun V V' ψ ψ' hψ' i u => hFunctor_hH3 WK hWK ch V V' ψ ψ' hψ' i u)).2

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Theorem B, unconditionally, at the tree's own functors.**  There *are* `K`-rational
structures (`exists_isKRationalStructure`) and there *is* an edge choice (`EdgeChoice.choose`), so
`Rep(Γ_K)` and `Rep(S(Γ_K))` are equivalent through this tree's `F` and `H` with no hypothesis at
all.  This is the declaration `V-S5G4-3`(c) asked for.

@census none (G5 non-vacuity witness for `RQ2-2.29`) -/
theorem species_equivalence_tree :
    ∃ (WK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit), Submodule K (V.W i))
      (hWK : ∀ (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit),
        IsKRationalStructure V i (WK V i))
      (e : CategoryTheory.Equivalence (FDRep Γ) (EtaleSpecies.Rep Γ.toSpecies)),
      e.functor = FFunctor Γ ∧
        e.inverse = hFunctor WK hWK (fun _ _ ε => EdgeChoice.choose Γ ε) := by
  classical
  choose WK hWK using fun (V : EtaleSpecies.Rep Γ.toSpecies) (i : Γ.VertexOrbit) =>
    exists_isKRationalStructure V i
  obtain ⟨e, hF, hH⟩ :=
    species_equivalence_at_tree_functors Γ WK hWK (fun _ _ ε => EdgeChoice.choose Γ ε)
  exact ⟨WK, hWK, e, hF, hH⟩

/-! ### § Stage S5 vacuity probes — the all-trivial interpretations  (G5 item 3, `V-S5G4-3`(a))

`WORKFLOW.md` §4/G5 item 3 asks, for every structure the stage introduces, for an entry that
**attempts the all-trivial interpretation and records whether it type-checks** — if it does, the
definition is too weak to exclude the degenerate model, and the non-degeneracy burden moves onto
named witnesses.  The G4 verifier measured that `Meta/Vacuity.lean` carries no such entry for any
of S5's structures (finding `V-S5G4-3`(a)).

**Placement.** `Meta/` is the instrument owner's file and firewall **F3** bars this stage's
implementer from it; the same collision was resolved twice before by *relocating the probe into
content*, at `Meta/Vacuity.lean` §3.1 (S1's `P6`) and §4.3 (S2's probes 3 and 4).  The probes are
therefore compiled here, in the **terminal module of the stage's import chain**, which is also
where `CONVENTIONS.md` §3's completed guard rule wants a guard to live: downstream of every module
that could perturb the instances they are stated against.  The `Meta/Vacuity.lean` §6 *entry* — the
cross-reference, in the instrument owner's own words — remains owed from the instrument owner, and
is proposed to the coordinator rather than written here.

**What each probe measures, and how to read it.**

| probe | witness | type-checks? | verdict |
|---|---|---|---|
| all-trivial `Species.Rep` (`W i = PUnit`, `f = 0`) | `Species.Rep.allTrivial` | **yes** | *expected, and it must*: the zero object is a legitimate object of an additive category, and `RQ2-2.17` does not exclude it.  The burden is on `Species.Rep.trivialMul`, whose structure map is **bijective** (`trivialMul_f_bijective`, `trivialMul_f_ne_zero`), and on `Species.Rep.ofL`'s `ofL_nontrivial` |
| all-trivial `Species.Rep.Hom` (every component `0`, into the zero object) | `Species.Rep.toAllTrivialHom` | **yes** | *expected*: `Hom`'s `comm` field is vacuous into the zero object.  Paired with `FMap` (`FunctorF`) and `hMapHom` (`FunctorH`), the two non-trivial morphism families the stage builds |
| `IsKRationalStructure` at `WK i := ⊥` | `not_isKRationalStructure_bot` | **no — refuted** | **this is the probe with teeth.**  `⊥` is *not* a `K`-rational structure of a nonzero `W_i`, so the `V-S5b-2` repair (adding `hWK` to `RQ2-2.27`/`RQ2-2.28`/`RQ2-2.29`) really does exclude the degenerate choice that refuted those rows.  Paired with `exists_isKRationalStructure`, so the predicate is inhabited **and** not trivially so |
| `IsEdgeDescent` at `f := 0` | `isEdgeDescent_zero_forces_phi_vanish` | **conditional** | the zero descent forces `Φ ∘ e₀` to vanish on every generator, so `f = 0` satisfies the predicate only in models where `Φ_{ij}` itself is zero: the predicate is not satisfied by the zero map for typing reasons alone.  Paired with `isEdgeDescent_smul`/`isEdgeDescent_le_unpinned`, the `S5-F8` certificate |
| `Twist`, `TwistBase` (the instance-leak degeneracy, `S5-F4`/`S5-F5`) | `twistBase_smul_guard_terminal`, `twistBase_algebraMap_guard_terminal` (above), `twistBase_smul_guard_downstream`, `wiiMjLpreRhs_base_guard` | — | already covered by the `V-S5b-13` guard chain; the degeneracy for a *twisted* structure is the untwisted instance winning synthesis, and that is what those `rfl`s exclude |
| `EdgeChoice` | `EdgeChoice.choose` | — | data, not a predicate; the G5 inhabitant is the choice itself and there is no all-trivial reading to attempt |

@census none (G5 item 3 for stage S5; finding `V-S5G4-3`(a))
-/

/-- **Probe 1 — the all-trivial `Species.Rep`.**  Every `W_i` the zero space, every `f_{ij}` zero.

**It type-checks.**  *Verdict: expected, and it must* — the zero object belongs in the category.
So no theorem of the shape `∀ V : Species.Rep S, P V` may be read as saying anything about a
representation with content; the content-bearing witness is `Species.Rep.trivialMul`.

@census none (G5 vacuity probe for `RQ2-2.17`) -/
def _root_.RationalQuivers.Species.Rep.allTrivial (S : Species K) : Species.Rep S where
  W _ := PUnit.{u+1}
  f _ _ := 0

/-- **Probe 2 — the all-trivial `Species.Rep.Hom`.**  Every component the zero map, into the zero
object.

**It type-checks.**  *Verdict: expected* — `Hom`'s `comm` square commutes trivially when the target
is zero.  The morphism families with content are `FMap` and `hMapHom`.

@census none (G5 vacuity probe for `RQ2-2.17-C4`/`C5`) -/
def _root_.RationalQuivers.Species.Rep.toAllTrivialHom (S : Species K) (V : Species.Rep S) :
    Species.Rep.Hom V (Species.Rep.allTrivial S) where
  ψ _ := 0
  comm _ _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- **Probe 3 — `IsKRationalStructure` at `⊥`, the choice `V-S5b-2` was about.**

**It does not type-check as a proof — the interpretation is *refuted*.**  *Verdict: this is the
probe with content.*  `WK i := ⊥` is the degenerate choice that made `RQ2-2.27`/`RQ2-2.28`/`RQ2-2.29`
false before `hWK` was added (finding `V-S5b-2`); this says the repaired predicate excludes it
outright whenever `W_i ≠ 0`.  Paired with `exists_isKRationalStructure`, which inhabits it.

@census none (G5 vacuity probe for `RQ2-2.27-H2`) -/
theorem not_isKRationalStructure_bot (V : EtaleSpecies.Rep Γ.toSpecies)
    (i : Γ.VertexOrbit) (hnt : Nontrivial (V.W i)) :
    ¬ IsKRationalStructure V i ⊥ := by
  intro h
  have hzero : ∀ t : (Γ.toSpecies.L i) ⊗[K] ↥(⊥ : Submodule K (V.W i)),
      LinearMap.liftBaseChange (Γ.toSpecies.L i)
        (((⊥ : Submodule K (V.W i)).subtype).restrictScalars K) t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]
    | tmul a w =>
        rw [LinearMap.liftBaseChange_tmul]
        show a • ((w : V.W i)) = 0
        rw [(Submodule.mem_bot K).mp w.2, smul_zero]
    | add p q hp hq => rw [map_add, hp, hq, add_zero]
  obtain ⟨x, y, hxy⟩ := hnt
  obtain ⟨t, ht⟩ := h.2 x
  obtain ⟨s, hs⟩ := h.2 y
  exact hxy ((ht.symm.trans (hzero t)).trans ((hzero s).symm.trans hs))

open scoped Classical in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Probe 4 — `IsEdgeDescent` at `f := 0`.**

*Verdict: conditional, and that is the informative answer.*  The zero descent forces `Φ ∘ e₀` to
vanish on every pure tensor, so it satisfies `IsEdgeDescent` only where `Φ_{ij}` — which
`RQ2-2.24-H1` pins componentwise to `a · phiComp` — is itself zero.  The predicate therefore has
content beyond typing: `f = 0` is not a free solution.  Paired with `isEdgeDescent_smul`, the
`S5-F8` counterexample generator, and `isEdgeDescent_le_unpinned`, the repair certificate.

@census none (G5 vacuity probe for `RQ2-2.24-C2`) -/
theorem isEdgeDescent_zero_forces_phi_vanish (M : Rep Γ) {i j : Γ.VertexOrbit}
    (ch : ∀ ε : Γ.EdgeOrbit i j, Γ.EdgeChoice ε)
    (e₀ : wiiMjL M i j ≃ₗ[L] wiiMjLpreRhs M ch)
    (h : IsEdgeDescent M ch e₀ 0)
    (Φ : wiiMjLpreRhs M ch →ₗ[L] M.M (Γ.vertexRep j))
    (hΦ : ∀ (ε : Γ.EdgeOrbit i j) (η : EdgeChoice.CosetIndex Γ (ch ε)) (a : L)
        (m : ↥(M.vertexFixed (Γ.vertexRep i))),
      Φ (DirectSum.lof L _ _ ε (Pi.single η (Twist.ofL a ⊗ₜ m)))
        = a • phiComp M (ch ε) η m)
    (t : EtaleSpecies.Rep.tensor Γ.toSpecies i j ↥(M.vertexFixed (Γ.vertexRep i))) (a : L) :
    Φ (e₀ (Balanced.mk t a)) = 0 := by
  have hd := h.2 Φ hΦ t a
  rw [hd]
  show a • ((0 : ↥(M.vertexFixed (Γ.vertexRep j))) : M.M (Γ.vertexRep j)) = 0
  rw [ZeroMemClass.coe_zero, smul_zero]

/-- **Terminal downstream guard for the non-degenerate G5 inhabitant** (`CONVENTIONS.md` §3's
completed rule; `PROCESS-CHANGELOG` 2026-08-30, "downstream placement").  `Species.Rep.trivialMul`
is defined in `Species/Rep/Basic.lean`, the *first* module of the stage; its non-degeneracy is a
statement about which `Module`/`Balanced` instances synthesis picks for `RepTensor`, and an
in-module check certifies only the prefix above it.  Re-asserted here, at the terminal node of the
whole import chain, where every competing instance the stage introduces exists.  If a later
instance shadows the one `trivialMul` was built against, this breaks.

@census none (guard, `CONVENTIONS.md` §3) -/
example (K' : Type u) [Field K'] :
    ∀ i j, Function.Bijective ((Species.Rep.trivialMul K').f i j) :=
  Species.Rep.trivialMul_f_bijective K'

end RationalQuiver

end RationalQuivers
