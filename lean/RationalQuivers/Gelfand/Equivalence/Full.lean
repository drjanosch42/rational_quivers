module

public import RationalQuivers.Gelfand.Equivalence.Faithful

@[expose] public section

/-!
# fullness of `𝔼_E`, the `ζ`-argument (§5.3, Step O-17)

Engine `E5` (`eq_of_two_forms`, `IsRatMap`, `isRatMap_of_conj`, `eq_zero_of_ratMap_smul`) and the native
`E_E_full`, with `ζ := √-1` (`HC.ImagUnit.zeta`, `c(ζ) = -ζ ≠ 0`); Galois descent of morphisms at the
`EX-HC` boundary.

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Equivalence.lean (§E5, §FullyFaithful)` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.Equivalence.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

*(2026-10-21, O-V2-6 round 2.)*  The carried docstrings below cite `C2` and `C5` by their v1 names
`E_Q_cocycle` and `E_Q_functorial`.  The relocation renamed them `E_E_cocycle`
(`Gelfand/Equivalence/WellDefined.lean`) and `E_E_functorial` (`Gelfand/Equivalence/Functor.lean`),
as the T3 `DECL-ALLOWLIST.tsv` records.

*v2 change.*  Engine `E5` takes `ζ` with `c(ζ) = -ζ ≠ 0` as an argument (v1 used a chosen element
`GF.zeta`); the native proof passes `ζ = √-1`, as the tex does.

@census none (module)
-/

namespace RationalQuivers.Gelfand.Equivalence

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {Dq : SqrtNegOneExt E}
open scoped TensorProduct Classical

variable {ℓ : ℕ}



/-! ### Engine `E5` — the two `ℚ`-forms of `Hom_{ℚ[√-1]}`, and why they coincide

`E1` (`eq_of_eq_on_V3`) and `E4` (`exists_hom_of_edges`) identify
`Hom_{HC_λ(𝔤,K)_{ℚ[√-1]}}(A,B)` with the morphisms of the underlying quiver representations.  `C7`
is over `ℚ`, so from a morphism `u` of `ℚ`-**rational** representations one must additionally
produce `f ∘ c = c ∘ f`.  Reading `u.rational` at `σ = c` and transporting it is **circular**
(`stages/S8/DESIGN-NOTES.md` §15.6): `u.rational` says the restriction commutes with
`φ_{v,c} = c ∘ φ^{(∞)}_v`, not with `c`, and the difference is exactly `HomSpec`, whose proof
consumes `map_conj`.

The source's route, and this one, is instead a comparison of two `ℚ`-forms of the *same*
`ℚ[√-1]`-space `Q := Hom_{HC_λ(𝔤,K)_{ℚ[√-1]}}(A_{ℚ[√-1]},B_{ℚ[√-1]})`:

* `P := {u ∈ Q | c_B ∘ u ∘ c_A = u}` — the fixed points of the semilinear involution `T₁`, i.e.
  `Hom_{HC_λ(𝔤,K)_ℚ}(A,B)`;
* `R := {u ∈ Q | the restriction of u commutes with φ_•}` — the morphisms of `Rep^nil(Γ_ℚ)`.

`P ⊆ R` is `C5` (`E_Q_functorial`).  The source concludes `P = R` from a dimension count: both
sides have `ℚ`-dimension `dim_{ℚ[√-1]} Q` by Galois descent (`RQ-1.16`, `thm:galoisdescent`,
proved in-tree — **no `HYP-04` is consumed**, and `CORRESPONDENCE.md`'s `RQ-5.05` imports cell
stays `none`).  `eq_of_two_forms` below runs that descent **at the single element** rather than on
dimensions, so the count, `Descent/Galois.lean`'s `descentCounit_bijective`, finite-dimensionality
of the `Hom` space and a `Module ℚ` structure on it are all unnecessary; what remains of the
descent is the two facts that make each side a `ℚ`-form, and only `R ∩ √-1·R = 0` has content.
See `stages/S8/DESIGN-NOTES.md` §16.3 for the derivation and for why this is the source's argument
with a step removed, not a different one.
-/

section E5





/-- **Engine `E5` — the `ℚ`-form comparison, in the abstract.**

Let `W` be a `ℚ[√-1]`-vector space, `T` a `c`-semilinear involution of it, `Q ⊆ W` a
`ℚ[√-1]`-subspace stable under `T` (given by its membership predicate, so that no submodule has to
be built), and `R ⊆ Q` an additive subgroup.  Write `P := {w ∈ Q | T w = w}` — the `ℚ`-form of `Q`
cut out by `T`.  If

* `P ⊆ R` (`hPR`), and
* `R ∩ √-1 · R = 0` (`hRi`),

then `R ⊆ P`, i.e. **the two `ℚ`-forms coincide**.

This is the content of the source's dimension count, with the count removed.  The source argues
`dim_ℚ P = dim_{ℚ[√-1]} Q = dim_ℚ R` by Galois descent (`RQ-1.16`, `thm:galoisdescent`) and
concludes `P = R` from `P ⊆ R`; the proof below runs the descent decomposition **at the single
element** instead, so neither `Descent/Galois.lean`'s `descentCounit_bijective` nor
finite-dimensionality nor a `Module ℚ` structure on `W` is needed:

> for `w ∈ R`, `p := w + T w` lies in `P` (hence in `R`), so `T w = p - w ∈ R` and
> `d := w - T w ∈ R`; `q := (√-1)⁻¹ · d` satisfies `T q = q` because `c((√-1)⁻¹) = -(√-1)⁻¹` and
> `T d = -d`, so `q ∈ P ⊆ R`; and `√-1 · q = d ∈ R`.  By `hRi`, `q = 0`, so `d = 0`, i.e.
> `T w = w`.

The decomposition `2w = (w + Tw) + √-1·((√-1)⁻¹(w - Tw))` is exactly the "real and imaginary part"
splitting `W = P ⊕ √-1·P` that makes `P` a `ℚ`-form; `hRi` is exactly the statement that `R` is
one too.  `Q` is carried only so that `hPR` and `hRi` may use it — they are the two places where
the concrete meaning of the forms enters.

@census none (helper; **engine `E5`**) -/
theorem eq_of_two_forms {W : Type*} [AddCommGroup W] [Module Dq.carrier W]
    (T : W → W)
    (hTadd : ∀ x y, T (x + y) = T x + T y)
    (hTsmul : ∀ (a : Dq.carrier) (x : W), T (a • x) = Dq.conj a • T x)
    (hTT : ∀ x, T (T x) = x)
    (Q : W → Prop)
    (hQT : ∀ x, Q x → Q (T x))
    (hQadd : ∀ x y, Q x → Q y → Q (x + y))
    (hQsub : ∀ x y, Q x → Q y → Q (x - y))
    (hQsmul : ∀ (a : Dq.carrier) x, Q x → Q (a • x))
    (R : W → Prop)
    (hRsub : ∀ x y, R x → R y → R (x - y))
    (hPR : ∀ x, Q x → T x = x → R x)
    (ζ : Dq.carrier) (hζ : Dq.conj ζ = -ζ) (hζ0 : ζ ≠ 0)
    (hRi : ∀ x, Q x → R x → R (ζ • x) → x = 0)
    (w : W) (hQw : Q w) (hw : R w) : T w = w := by
  have hTp : T (w + T w) = w + T w := by rw [hTadd, hTT, add_comm]
  have hRp : R (w + T w) := hPR _ (hQadd _ _ hQw (hQT _ hQw)) hTp
  have hRTw : R (T w) := by
    have := hRsub _ _ hRp hw
    simpa using this
  have hRd : R (w - T w) := hRsub _ _ hw hRTw
  set d : W := w - T w with hd
  set q : W := ζ⁻¹ • d with hq
  have hTd : T d = -d := by
    rw [hd, show w - T w = w + (-(1:Dq.carrier)) • T w by rw [neg_one_smul]; abel]
    rw [hTadd, hTsmul, hTT]
    simp
  have hTq : T q = q := by
    rw [hq, hTsmul, hTd, map_inv₀, hζ, inv_neg, neg_smul, smul_neg, neg_neg]
  have hQd : Q d := hQsub _ _ hQw (hQT _ hQw)
  have hQq : Q q := hQsmul _ _ hQd
  have hiq : ζ • q = d := by
    rw [hq, smul_smul, mul_inv_cancel₀ hζ0, one_smul]
  have hq0 : q = 0 := hRi q hQq (hPR _ hQq hTq) (by rw [hiq]; exact hRd)
  have : d = 0 := by rw [← hiq, hq0, smul_zero]
  have := sub_eq_zero.mp this
  exact this.symm

/-- The membership predicate of `Hom_{HC_λ(𝔤,K)_{ℚ[√-1]}}(A_{ℚ[√-1]}, B_{ℚ[√-1]})` inside the
`ℚ[√-1]`-linear maps: `u` commutes with `H`, `X`, `Y` and preserves the weight components.  Carried
as a predicate rather than as a `Submodule` so that engine `E5` can be applied to the ambient space
of linear maps directly.  @census none (helper; engine `E5`) -/
def IsHCMap {A B : HCEObj ℓ E Dq} (u : A.carrier →ₗ[Dq.carrier] B.carrier) : Prop :=
  (∀ v, u (A.setup.weight.H v) = B.setup.weight.H (u v)) ∧
  (∀ v, u (A.setup.weight.X v) = B.setup.weight.X (u v)) ∧
  (∀ v, u (A.setup.weight.Y v) = B.setup.weight.Y (u v)) ∧
  (∀ (n : ℤ) (v : A.carrier), v ∈ A.setup.weight.comp n → u v ∈ B.setup.weight.comp n)

/-- An `IsHCMap` **is** a morphism of `HC_λ(𝔤,K)_{ℚ[√-1]}`.  @census none (helper; engine `E5`) -/
def hcHom {A B : HCEObj ℓ E Dq} {u : A.carrier →ₗ[Dq.carrier] B.carrier} (hu : IsHCMap u) :
    A.toF ⟶ B.toF :=
  ⟨u, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2⟩

/-- The zero map is one.  @census none (helper; engine `E5`) -/
theorem isHCMap_zero {A B : HCEObj ℓ E Dq} : IsHCMap (0 : A.carrier →ₗ[Dq.carrier] B.carrier) :=
  ⟨fun _ => by simp, fun _ => by simp, fun _ => by simp, fun _ _ _ => by simp⟩

/-- `E1` in the form engine `E5` needs it: a morphism of the `ℚ[√-1]`-forms that vanishes on the
three vertex components is zero.  @census none (helper; engine `E5`) -/
theorem eq_zero_of_vanish_on_V3 {A B : HCEObj ℓ E Dq} {u : A.carrier →ₗ[Dq.carrier] B.carrier}
    (hu : IsHCMap u)
    (h0 : ∀ (v : Fin 3) (m : A.carrier), m ∈ A.setup.weight.comp (vtxIdx ℓ v) → u m = 0) :
    u = 0 := by
  have := Split.eq_of_eq_on_V3 (A := A.toF) (B := B.toF) (hcHom hu) (hcHom (isHCMap_zero (A := A) (B := B)))
    (fun v m hm => by
      show u m = (0 : A.carrier →ₗ[Dq.carrier] B.carrier) m
      rw [h0 v m hm, LinearMap.zero_apply])
  exact congrArg Split.HCFHom.toLinearMap this


section Conj
variable {A B : HCEObj ℓ E Dq}

/-- **The first involution**: `T₁(u) := c_B ∘ u ∘ c_A`.  `ℚ[√-1]`-linear because `c` is applied
twice (`galConj_galConj`), and `c`-semilinear as a function of `u`.  Its fixed points are exactly
the morphisms of `HC_λ(𝔤,K)_ℚ` — the `map_conj` field.
@census none (helper; engine `E5`) -/
noncomputable def conjHom (u : A.carrier →ₗ[Dq.carrier] B.carrier) :
    A.carrier →ₗ[Dq.carrier] B.carrier where
  toFun m := B.setup.conj (u (A.setup.conj m))
  map_add' m m' := by simp
  map_smul' a m := by
    show B.setup.conj (u (A.setup.conj (a • m))) = a • B.setup.conj (u (A.setup.conj m))
    rw [A.setup.conj_smul, map_smul, B.setup.conj_smul, Gelfand.RationalStructure.galConj_galConj]

@[simp] theorem conjHom_apply (u : A.carrier →ₗ[Dq.carrier] B.carrier) (m : A.carrier) :
    conjHom u m = B.setup.conj (u (A.setup.conj m)) := rfl

/-- `T₁` is additive.  @census none (helper; engine `E5`) -/
theorem conjHom_add (u u' : A.carrier →ₗ[Dq.carrier] B.carrier) :
    conjHom (u + u') = conjHom u + conjHom u' := by
  ext m; simp

/-- `T₁` is `c`-semilinear: `T₁(a·u) = c(a)·T₁(u)`.  @census none (helper; engine `E5`) -/
theorem conjHom_smul (a : Dq.carrier) (u : A.carrier →ₗ[Dq.carrier] B.carrier) :
    conjHom (a • u) = Dq.conj a • conjHom u := by
  ext m
  show B.setup.conj (a • u (A.setup.conj m)) = Dq.conj a • B.setup.conj (u (A.setup.conj m))
  rw [B.setup.conj_smul]

/-- `T₁` is an involution (`c² = 𝟏` on both sides).  @census none (helper; engine `E5`) -/
theorem conjHom_conjHom (u : A.carrier →ₗ[Dq.carrier] B.carrier) :
    conjHom (conjHom u) = u := by
  ext m
  show B.setup.conj (B.setup.conj (u (A.setup.conj (A.setup.conj m)))) = u m
  rw [A.setup.conj_involutive m, B.setup.conj_involutive]

/-- `T₁` preserves `Q`: `c_B ∘ u ∘ c_A` is again a morphism of the `ℚ[√-1]`-forms, because
`cX = Yc`, `cY = Xc`, `cH = -Hc` and `c(M_n) = M_{-n}` (S7's `RationalSetup`).
@census none (helper; engine `E5`) -/
theorem isHCMap_conjHom {u : A.carrier →ₗ[Dq.carrier] B.carrier} (hu : IsHCMap u) :
    IsHCMap (conjHom u) := by
  obtain ⟨hH, hX, hY, hc⟩ := hu
  refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, fun n m hm => ?_⟩
  · show B.setup.conj (u (A.setup.conj (A.setup.weight.H m)))
      = B.setup.weight.H (B.setup.conj (u (A.setup.conj m)))
    rw [A.setup.conj_H, map_neg, hH, ← neg_eq_iff_eq_neg.mpr (B.setup.conj_H _)]
    simp
  · show B.setup.conj (u (A.setup.conj (A.setup.weight.X m)))
      = B.setup.weight.X (B.setup.conj (u (A.setup.conj m)))
    rw [A.setup.conj_X, hY, B.setup.conj_Y]
  · show B.setup.conj (u (A.setup.conj (A.setup.weight.Y m)))
      = B.setup.weight.Y (B.setup.conj (u (A.setup.conj m)))
    rw [A.setup.conj_Y, hX, B.setup.conj_X]
  · show B.setup.conj (u (A.setup.conj m)) ∈ B.setup.weight.comp n
    have h1 := A.setup.conj_comp n m hm
    have h2 := hc _ _ h1
    have h3 := B.setup.conj_comp _ _ h2
    rwa [neg_neg] at h3

end Conj


section Forms
variable (hℓ : 1 ≤ ℓ) {A B : HCEObj ℓ E Dq}

/-- **The second `ℚ`-form**, `R`: `u`'s restriction to the three vertex components commutes with
the rational structure `φ_{v,c} = c ∘ φ^{(∞)}_v` of `𝔼_ℚ`.  For a morphism `u` of the
`ℚ[√-1]`-forms this says exactly that its restriction is a morphism of `Rep^nil(Γ_ℚ)` — the
`rational` field of `RationalQuiver.Rep.Hom` at `σ = c` (the `σ = 1` clause is vacuous).
@census none (helper; engine `E5`) -/
def IsRatMap (u : A.carrier →ₗ[Dq.carrier] B.carrier) : Prop :=
  ∀ (v : Fin 3) (m : A.carrier), m ∈ A.setup.weight.comp (vtxIdx ℓ v) →
    u (Gelfand.RationalStructure.phiC hℓ A v m) = Gelfand.RationalStructure.phiC hℓ B v (u m)

/-- `R` is an additive subgroup.  @census none (helper; engine `E5`) -/
theorem isRatMap_sub {u u' : A.carrier →ₗ[Dq.carrier] B.carrier}
    (h : IsRatMap hℓ u) (h' : IsRatMap hℓ u') : IsRatMap hℓ (u - u') := by
  intro v m hm
  show u (Gelfand.RationalStructure.phiC hℓ A v m) - u' (Gelfand.RationalStructure.phiC hℓ A v m) = Gelfand.RationalStructure.phiC hℓ B v (u m - u' m)
  rw [h v m hm, h' v m hm]
  show _ = B.setup.conj (Gelfand.RationalStructure.limAt hℓ B v (u m - u' m))
  rw [map_sub, map_sub]
  rfl

/-- **`hRi` for `R`**: `R ∩ √-1·R = 0`.  If `u` and `√-1·u` both commute with `φ_•`, then, since
`φ_{v,c}` is `c`-semilinear, `√-1·u(φ_{v,c} m) = c(√-1)·φ_{v,c}(u m) = -√-1·u(φ_{v,c} m)`, so `u`
kills the image of `φ_{v,c}`; that image is all of `M(c·v)` by the cocycle condition `C2`
(`E_Q_cocycle`), so `u` vanishes on the three vertex components and `E1` finishes.

This is the step that replaces the source's dimension count: it is *why* `R` is a `ℚ`-form, proved
directly instead of through `dim_ℚ R = dim_{ℚ[√-1]} Q`.
@census none (helper; engine `E5`)
@clauses   RQ2-5.12-S-O17 -/
theorem eq_zero_of_ratMap_smul {u : A.carrier →ₗ[Dq.carrier] B.carrier}
    (ζ : Dq.carrier) (hζ : Dq.conj ζ = -ζ) (hζ0 : ζ ≠ 0)
    (hu : IsHCMap u) (h : IsRatMap hℓ u) (hi : IsRatMap hℓ ((ζ • u : A.carrier →ₗ[Dq.carrier] B.carrier))) : u = 0 := by
  have key : ∀ (v : Fin 3) (m : A.carrier), m ∈ A.setup.weight.comp (vtxIdx ℓ v) →
      u (Gelfand.RationalStructure.phiC hℓ A v m) = 0 := by
    intro v m hm
    have h1 := h v m hm
    have h2 := hi v m hm
    rw [show ((ζ • u) : A.carrier →ₗ[Dq.carrier] B.carrier) (Gelfand.RationalStructure.phiC hℓ A v m)
        = ζ • u (Gelfand.RationalStructure.phiC hℓ A v m) from rfl,
      show ((ζ • u) : A.carrier →ₗ[Dq.carrier] B.carrier) m = ζ • u m from rfl,
      Gelfand.RationalStructure.phiC_smul, hζ, ← h1, neg_smul] at h2
    have h5 : (2 : Dq.carrier) • (ζ • u (Gelfand.RationalStructure.phiC hℓ A v m)) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h2]
      exact add_neg_cancel _
    have h6 : ζ • u (Gelfand.RationalStructure.phiC hℓ A v m) = 0 :=
      (smul_eq_zero.mp h5).resolve_left two_ne_zero
    exact (smul_eq_zero.mp h6).resolve_left hζ0
  refine eq_zero_of_vanish_on_V3 hu (fun v m hm => ?_)
  have hs : Gelfand.RationalStructure.phiC hℓ A v m ∈ A.setup.weight.comp (vtxIdx ℓ (RQuiver.gelfandVertexSwap v)) :=
    Gelfand.RationalStructure.phiC_mem hℓ A v m
  have hback : Gelfand.RationalStructure.phiC hℓ A (RQuiver.gelfandVertexSwap v) (Gelfand.RationalStructure.phiC hℓ A v m) = m :=
    E_E_cocycle hℓ A v m hm
  rw [← hback]
  exact key _ _ hs

/-- **`hPR`**: the first `ℚ`-form is contained in the second.  A morphism of the `ℚ[√-1]`-forms
that commutes with `c` is a morphism of `HC_λ(𝔤,K)_ℚ`, hence commutes with the three unipotent
stabilizations by `C5` (`E_Q_functorial`), hence with `φ_{v,c} = c ∘ φ^{(∞)}_v`.  This is the one
place the argument consumes functoriality, and it is the reason the containment goes this way and
not the other.  @census none (helper; engine `E5`) -/
theorem isRatMap_of_conj {u : A.carrier →ₗ[Dq.carrier] B.carrier}
    (hu : IsHCMap u) (hT : conjHom u = u) : IsRatMap hℓ u := by
  have hconj : ∀ m, u (A.setup.conj m) = B.setup.conj (u m) := by
    intro m
    have := congrArg (fun (w : A.carrier →ₗ[Dq.carrier] B.carrier) => w (A.setup.conj m)) hT
    show u (A.setup.conj m) = _
    rw [← this]
    show B.setup.conj (u (A.setup.conj (A.setup.conj m))) = _
    rw [A.setup.conj_involutive m]
  let f : A ⟶ B := ⟨u, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2, hconj⟩
  have hspec : Gelfand.RationalStructure.HomSpec hℓ f := E_E_functorial hℓ A f
  intro v m _
  show u (A.setup.conj (Gelfand.RationalStructure.limAt hℓ A v m)) = B.setup.conj (Gelfand.RationalStructure.limAt hℓ B v (u m))
  rw [hconj, hspec v m]

end Forms



end E5


section FullyFaithful

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2) (hℓ : 1 ≤ ℓ)

/-- **`RQ-5.05-C7`** — `𝔼_ℚ` is **fully faithful**.  The source: a dimension comparison using
`prop:homdescent` (`RQ-1.16`) and its analogue for `(𝔤,K)`-modules (Januszewski18 Prop. 1.1); on
the concrete `HC_λ(𝔤,K)_ℚ` the latter is Galois descent for the Hom space of the `ℚ[√-1]`-forms
under `f ↦ c f c` (module docstring), so no bundle field is consumed.

@census    none (auxiliary; discharges census clause `RQ-5.05-C7`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C7
@imports   none
@divergence none -/
theorem E_Q_full (h : Gelfand.RationalStructure.E_QSpec hcard hℓ) : (E_QFunctor hcard hℓ h).Full := by
  constructor
  intro A B g
  obtain ⟨f, hf⟩ := Split.exists_hom_of_edges (A := A.toF) (B := B.toF) hℓ g.1.ψ
    (fun e m => g.1.edge e m)
  set u : A.carrier →ₗ[Dq.carrier] B.carrier := f.toLinearMap with hu
  have hHC : IsHCMap u := ⟨f.map_H, f.map_X, f.map_Y, f.map_comp⟩
  have hval : ∀ (w : Fin 3) (x : Split.V3 A.qi w),
      (Subtype.val (g.1.ψ w x) : B.carrier) = u (Subtype.val x) :=
    fun w x => congrArg Subtype.val (hf w x).symm
  have hRat : IsRatMap hℓ u := by
    intro v m hm
    have hkey := congrArg Subtype.val (g.1.rational Dq.conj (Gelfand.RationalStructure.vtxQ hcard v) ⟨m, hm⟩)
    show u (A.setup.conj (Gelfand.RationalStructure.limAt hℓ A v m)) = B.setup.conj (Gelfand.RationalStructure.limAt hℓ B v (u m))
    rw [show A.setup.conj (Gelfand.RationalStructure.limAt hℓ A v m) = galAct hℓ A Dq.conj v m from
        (galAct_of_ne hℓ A Gelfand.RationalStructure.galConj_ne_one v m).symm,
      show B.setup.conj (Gelfand.RationalStructure.limAt hℓ B v (u m)) = galAct hℓ B Dq.conj v (u m) from
        (galAct_of_ne hℓ B Gelfand.RationalStructure.galConj_ne_one v (u m)).symm]
    refine Eq.trans ?_ (Eq.trans hkey ?_)
    · exact (hval (Dq.conj • Gelfand.RationalStructure.vtxQ hcard v)
        (E_Q_φ hcard hℓ A (h.1 A) Dq.conj (Gelfand.RationalStructure.vtxQ hcard v) ⟨m, hm⟩)).symm
    · exact congrArg (galAct hℓ B Dq.conj v) (hval v ⟨m, hm⟩)
  have hT : conjHom u = u :=
    eq_of_two_forms conjHom conjHom_add conjHom_smul conjHom_conjHom
      (fun w => IsHCMap w) (fun _ hw => isHCMap_conjHom hw)
      (fun x y hx hy => ⟨fun m => by simp [hx.1, hy.1], fun m => by simp [hx.2.1, hy.2.1],
        fun m => by simp [hx.2.2.1, hy.2.2.1],
        fun n m hm => add_mem (hx.2.2.2 n m hm) (hy.2.2.2 n m hm)⟩)
      (fun x y hx hy => ⟨fun m => by simp [hx.1, hy.1], fun m => by simp [hx.2.1, hy.2.1],
        fun m => by simp [hx.2.2.1, hy.2.2.1],
        fun n m hm => sub_mem (hx.2.2.2 n m hm) (hy.2.2.2 n m hm)⟩)
      (fun a x hx => ⟨fun m => by simp [hx.1], fun m => by simp [hx.2.1],
        fun m => by simp [hx.2.2.1],
        fun n m hm => Submodule.smul_mem _ _ (hx.2.2.2 n m hm)⟩)
      (fun w => IsRatMap hℓ w) (fun _ _ hx hy => isRatMap_sub hℓ hx hy)
      (fun _ hx hTx => isRatMap_of_conj hℓ hx hTx)
      (GF.zeta Dq) (GF.conj_zeta Dq) (GF.zeta_ne_zero Dq)
        (fun _ hx hr hri => eq_zero_of_ratMap_smul hℓ (GF.zeta Dq) (GF.conj_zeta Dq) (GF.zeta_ne_zero Dq) hx hr hri)
      u hHC hRat
  have hconj : ∀ m, u (A.setup.conj m) = B.setup.conj (u m) := by
    intro m
    have := congrArg (fun (w : A.carrier →ₗ[Dq.carrier] B.carrier) => w (A.setup.conj m)) hT
    show u (A.setup.conj m) = _
    rw [← this]
    show B.setup.conj (u (A.setup.conj (A.setup.conj m))) = _
    rw [A.setup.conj_involutive m]
  refine ⟨⟨u, hHC.1, hHC.2.1, hHC.2.2.1, hHC.2.2.2, hconj⟩, ?_⟩
  apply ObjectProperty.hom_ext
  exact RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun m => hf v m)

end FullyFaithful


/-! ### `ζ = √-1` (Step O-17) -/

/-- **`ζ := √-1 ∈ L_E`**, the element of the `ζ`-argument of Step O-17: `c(ζ) = -ζ ≠ 0`.
@census none (helper; Step O-17) -/
noncomputable def _root_.RationalQuivers.HC.ImagUnit.zeta (D : ImagUnit E) : D.L := D.i

theorem _root_.RationalQuivers.HC.ImagUnit.zeta_ne_zero (D : ImagUnit E) : D.zeta ≠ 0 :=
  D.i_ne_zero

/-- `c(ζ) = -ζ`.  @census none (helper; Step O-17) -/
theorem _root_.RationalQuivers.HC.ImagUnit.conj_zeta (D : ImagUnit E)
    (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1) : (D.sqrtExt h).conj D.zeta = -D.zeta :=
  D.sqrtExt_conj_i h

/-! ## The native `𝔼_E` on `HC ℓ E D` (stage T3) -/

section NativeHC

set_option linter.unusedSectionVars false

variable {D : ImagUnit E} (hℓ : 1 ≤ ℓ)

/-- **Fullness**, the `ζ`-argument (Step O-17).  @census none (helper) -/
theorem E_E_full : (E_EGel (D := D) hℓ).Full := by
  constructor
  intro A B g
  obtain ⟨f, hf⟩ := Split.exists_hom_of_edges (A := A.toF) (B := B.toF) hℓ g.1.ψ
    (fun e m => g.1.edge e m)
  set u : A.carrier →ₗ[D.L] B.carrier := f.toLinearMap with hu
  have hval : ∀ (w : Fin 3) (x : Split.V3 A.qi w),
      (Subtype.val (g.1.ψ w x) : B.carrier) = u (Subtype.val x) :=
    fun w x => congrArg Subtype.val (hf w x).symm
  -- the `σ`-compatibility: trivial for `χ σ = 1`, the `ζ`-argument for `χ σ = -1`
  have hgal : ∀ σ m, u (A.galAct σ m) = B.galAct σ (u m) := by
    intro σ m
    rcases D.chi_cases σ with hσ | hσ
    · rw [HC.galAct_of_chi_one _ hσ, HC.galAct_of_chi_one _ hσ]
    set h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1 := ⟨σ, hσ⟩
    have hHC : IsHCMap (A := A.toHCEObj h) (B := B.toHCEObj h) u :=
      ⟨f.map_H, f.map_X, f.map_Y, f.map_comp⟩
    have hRat : IsRatMap hℓ (A := A.toHCEObj h) (B := B.toHCEObj h) u := by
      intro v m hm
      have hkey := congrArg Subtype.val (g.1.rational σ (vtxE D v) ⟨m, hm⟩)
      rw [← Gelfand.RationalStructure.E_E_φ_eq_phiC hℓ A hσ v m]
      erw [← Gelfand.RationalStructure.E_E_φ_eq_phiC hℓ B hσ v (u m)]
      refine Eq.trans ?_ (Eq.trans hkey ?_)
      · exact (hval (σ • vtxE D v) (E_E_φEquiv hℓ A σ v ⟨m, hm⟩)).symm
      · exact congrArg (Gelfand.RationalStructure.E_E_φ hℓ B σ v) (hval v ⟨m, hm⟩)
    have hT : conjHom (A := A.toHCEObj h) (B := B.toHCEObj h) u = u :=
      eq_of_two_forms (conjHom (A := A.toHCEObj h) (B := B.toHCEObj h)) conjHom_add
        conjHom_smul conjHom_conjHom
        (fun w => IsHCMap (A := A.toHCEObj h) (B := B.toHCEObj h) w) (fun _ hw => isHCMap_conjHom hw)
        (fun x y hx hy => ⟨fun m => by simp [hx.1, hy.1], fun m => by simp [hx.2.1, hy.2.1],
          fun m => by simp [hx.2.2.1, hy.2.2.1],
          fun n m hm => add_mem (hx.2.2.2 n m hm) (hy.2.2.2 n m hm)⟩)
        (fun x y hx hy => ⟨fun m => by simp [hx.1, hy.1], fun m => by simp [hx.2.1, hy.2.1],
          fun m => by simp [hx.2.2.1, hy.2.2.1],
          fun n m hm => sub_mem (hx.2.2.2 n m hm) (hy.2.2.2 n m hm)⟩)
        (fun a x hx => ⟨fun m => by simp [hx.1], fun m => by simp [hx.2.1],
          fun m => by simp [hx.2.2.1],
          fun n m hm => Submodule.smul_mem _ _ (hx.2.2.2 n m hm)⟩)
        (fun w => IsRatMap hℓ (A := A.toHCEObj h) (B := B.toHCEObj h) w) (fun _ _ hx hy => isRatMap_sub hℓ hx hy)
        (fun _ hx hTx => isRatMap_of_conj hℓ hx hTx)
        D.zeta (D.conj_zeta h) D.zeta_ne_zero
        (fun _ hx hr hri => eq_zero_of_ratMap_smul hℓ D.zeta (D.conj_zeta h) D.zeta_ne_zero hx hr hri)
        u hHC hRat
    have := congrArg (fun (w : A.carrier →ₗ[D.L] B.carrier) => w ((A.setup h).conj m)) hT
    rw [← A.setup_conj h hσ, ← B.setup_conj h hσ]
    rw [← this]
    show (B.setup h).conj (u ((A.setup h).conj ((A.setup h).conj m))) = _
    rw [(A.setup h).conj_involutive m]
  refine ⟨⟨u, f.map_H, f.map_X, f.map_Y, f.map_comp, hgal⟩, ?_⟩
  apply ObjectProperty.hom_ext
  exact RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun m => hf v m)


end NativeHC

end RationalQuivers.Gelfand.Equivalence
