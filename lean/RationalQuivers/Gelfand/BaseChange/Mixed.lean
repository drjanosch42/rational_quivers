module

public import RationalQuivers.Gelfand.BaseChange.Split

@[expose] public section


/-!
# `𝔼` is compatible with base change: non-split → split (WP-15, T1 case (3))

*Provenance.*  Relocated in stage T4 (WP-11) from `GF/BaseChangeMixed.lean` (v1 `RationalQuivers.Gelfand.GF`) by `workflow/v2/stages/T4/VALIDATION/scripts/relocate_bc.py`: whole file, declarations moved from `GF.x` to `Gelfand.BaseChange.x` (renames in the T4 `DECL-ALLOWLIST.tsv`), references qualified, the imports of v1's `GF/Main`/`GF/Species` cut; statements and proofs otherwise unchanged.  The native statement on `HC ℓ E D`/`𝔼_E` (`prop:basechange`, `RQ2-5.14`) is in `Gelfand/BaseChange/Native.lean`.

Case (3) is `√-1 ∉ E`, `√-1 ∈ E''`.  The declarations below assume neither: `D : SqrtNegOneExt E` is any
quadratic Galois extension `D'/E` (written `E(√-1)` in this file), with an `E`-algebra map
`ι : E(√-1) → E''` (`Algebra D.carrier E''`).

## The identification `E'' ⊗_E Γ_E ≅` split quiver over `E''` (explicit step)

`tensorSplitEquiv`: `E'' ⊗_E E(√-1) ≅ E'' × E''` as `E''`-algebras, `b ⊗ a ↦ (b ι(a), b ι(c a))`.
So for a representation `M` of `Γ_E` (vertex spaces `E(√-1)`-vector spaces `M(v)`, descent datum
`φ_{v,c} : M(v) → M(c v)`), `E'' ⊗_E M(v)` is a module over `E'' × E''` and splits into the two
`E''`-spaces `E'' ⊗_{E(√-1),ι} M(v)` and `E'' ⊗_{E(√-1),ι∘c} M(v)`; `φ_{v,c}` identifies the
second with the first one at `c·v`.  The `E''`-rational representation `E'' ⊗_E M` of the (now
split, `Gal(E''/E'')` being trivial) quiver is therefore determined by the family
`v ↦ E'' ⊗_{E(√-1),ι} M(v)` with the base-changed edge maps — which is `Rep.toSplit E''`, i.e.
S10's `qBCnsRel` (now in `Gelfand/BaseChange/QuiverRel.lean`).  This is the step that justifies taking `qBCnsRel` as the quiver-side `E'' ⊗_E −`
in the mixed case; T1 below is stated for `qBCnsRel`.

## T1, case (3)

`E_bc_mixed_iso`: `𝔼_E ⋙ qBCnsRel ≅ hcBaseChangeNS ⋙ 𝔼_{E''}`.  `𝔼_E(M)` and
`𝔼_{E(√-1)}(E(√-1) ⊗_E M)` have the same vertex family and the same edge maps (they differ only in
the rational structure `φ`, which `Rep.toSplit` forgets), so the square is the core of case (1)
along `ι : E(√-1) → E''`.  It holds for **every** `E(√-1) → E''`.  No declaration in this file assumes
`√-1 ∉ E` except the helper `conj_sqrt_of_noSqrtNegOne`: `tensorSplitEquiv` is root-free since the v2
amendment T4-a1 and has had no `[NoSqrtNegOne E]` binder since T4-a3.
-/

namespace RationalQuivers.Gelfand.BaseChange

/-- For `√-1 ∉ E`, the Galois conjugation of a quadratic `D'/E` negates any square root `s` of `-1`
in `D'` (copied from v1's `GF.conj_sqrt_of_noSqrtNegOne`, `GF/Species.lean`, so that base change does
not import v1's species file).  Since the v2 amendment T4-a1 the root is an explicit argument,
because, since T2-a2 (landed with T4-a1 in `eabed4e`), the
structure `SqrtNegOneExt` no longer carries one.  @census none (helper) -/
theorem conj_sqrt_of_noSqrtNegOne {E : Type} [Field E] [CharZero E] [NoSqrtNegOne E]
    (D : SqrtNegOneExt E) (s : D.carrier) (hs : s * s = -1) : D.conj s = -s := by
  have hsq : D.conj s * D.conj s = s * s := by
    rw [← map_mul, hs, map_neg, map_one]
  have hfac : (D.conj s - s) * (D.conj s + s) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exfalso
    have hfix : ∀ σ : D.carrier ≃ₐ[E] D.carrier, σ s = s := by
      intro σ
      by_cases hσ : σ = 1
      · rw [hσ]; rfl
      · rw [SqrtNegOneExt.eq_conj_of_ne_one D hσ]; exact (sub_eq_zero.mp h)
    obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := E) s).mpr hfix
    apply NoSqrtNegOne.no_sqrt b
    apply (algebraMap E D.carrier).injective
    rw [map_mul, hb, hs, map_neg, map_one]
  · exact eq_neg_of_add_eq_zero_left h

open RationalQuivers.HC RationalQuivers.Gelfand CategoryTheory
open scoped TensorProduct

/-! ## `E'' ⊗_E E(√-1) ≅ E'' × E''` -/

section TensorSplit

variable {E : Type} [Field E] [CharZero E] (D : SqrtNegOneExt E)
variable (E'' : Type) [Field E''] [Algebra E E''] [Algebra D.carrier E'']
  [IsScalarTower E D.carrier E'']

/-- The two `E`-embeddings `E(√-1) → E''`: `ι` and `ι ∘ c`.  @census none (helper; WP-15) -/
noncomputable def twoEmbeddings : D.carrier →ₐ[E] E'' × E'' :=
  AlgHom.prod (IsScalarTower.toAlgHom E D.carrier E'')
    ((IsScalarTower.toAlgHom E D.carrier E'').comp D.conj.toAlgHom)

/-- The comparison map `E'' ⊗_E E(√-1) → E'' × E''`, `b ⊗ a ↦ (b ι(a), b ι(c a))`.
@census none (helper; WP-15) -/
noncomputable def tensorSplitHom : E'' ⊗[E] D.carrier →ₐ[E''] E'' × E'' :=
  Algebra.TensorProduct.lift (Algebra.ofId E'' (E'' × E'')) (twoEmbeddings D E'')
    (fun _ _ => Commute.all _ _)

theorem tensorSplitHom_tmul (b : E'') (a : D.carrier) :
    tensorSplitHom D E'' (b ⊗ₜ[E] a)
      = (b * algebraMap D.carrier E'' a, b * algebraMap D.carrier E'' (D.conj a)) := by
  simp [tensorSplitHom, twoEmbeddings, Algebra.TensorProduct.lift_tmul]

/-- **`E'' ⊗_E E(√-1) ≅ E'' × E''`** as `E''`-algebras, for every quadratic Galois `D'/E` (written
`E(√-1)`) and any `E`-algebra map `ι : E(√-1) → E''`: `b ⊗ a ↦ (b ι(a), b ι(c a))`.  The explicit
identification that makes `E'' ⊗_E Γ_E` split (module docstring).

Since the v2 amendment T4-a1 the proof is root-free: it uses `ζ := GF.zeta D` (`c ζ = -ζ`,
`ζ ≠ 0`), with idempotents `(1 ± ι(ζ)⁻¹ ζ)/2`, so it holds for every quadratic `D'/E`.  The
instance argument `[NoSqrtNegOne E]`, unused since then, was removed by the v2 amendment T4-a3.

@census none (WP-15; T1 case (3), the identification step) -/
noncomputable def tensorSplitEquiv [CharZero E''] :
    E'' ⊗[E] D.carrier ≃ₐ[E''] E'' × E'' :=
  AlgEquiv.ofBijective (tensorSplitHom D E'') (by
    set t : E'' := algebraMap D.carrier E'' (GF.zeta D)
    have ht0 : t ≠ 0 := (map_ne_zero (algebraMap D.carrier E'')).mpr (GF.zeta_ne_zero D)
    have hc : algebraMap D.carrier E'' (D.conj (GF.zeta D)) = -t := by
      rw [GF.conj_zeta, map_neg]
    have hsurj : Function.Surjective (tensorSplitHom D E'') := by
      have h2 : (2 : E'') ≠ 0 := two_ne_zero
      have e1 : tensorSplitHom D E'' ((1 : E'') ⊗ₜ[E] (1 : D.carrier)) = (1, 1) := by
        rw [tensorSplitHom_tmul]; simp
      have e2 : tensorSplitHom D E'' ((1 : E'') ⊗ₜ[E] GF.zeta D) = (t, -t) := by
        rw [tensorSplitHom_tmul, hc]; simp [t]
      have hx : ∃ x, tensorSplitHom D E'' x = (1, 0) := by
        refine ⟨(2 : E'')⁻¹ • ((1 : E'') ⊗ₜ[E] (1 : D.carrier) + t⁻¹ • ((1 : E'') ⊗ₜ[E] GF.zeta D)), ?_⟩
        rw [map_smul, map_add, map_smul, e1, e2]
        ext <;> simp [ht0] <;> field_simp <;> ring
      have hy : ∃ y, tensorSplitHom D E'' y = (0, 1) := by
        refine ⟨(2 : E'')⁻¹ • ((1 : E'') ⊗ₜ[E] (1 : D.carrier) - t⁻¹ • ((1 : E'') ⊗ₜ[E] GF.zeta D)), ?_⟩
        rw [map_smul, map_sub, map_smul, e1, e2]
        ext <;> simp [ht0] <;> field_simp <;> ring
      obtain ⟨x, hx⟩ := hx
      obtain ⟨y, hy⟩ := hy
      rintro ⟨p, q⟩
      refine ⟨p • x + q • y, ?_⟩
      rw [map_add, map_smul, map_smul, hx, hy]
      ext <;> simp
    have hrank : Module.finrank E'' (E'' ⊗[E] D.carrier) = Module.finrank E'' (E'' × E'') := by
      rw [Module.finrank_baseChange, Module.finrank_prod, Module.finrank_self]
      rw [← IsGalois.card_aut_eq_finrank E D.carrier, D.card_gal]
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
      (f := (tensorSplitHom D E'').toLinearMap)).mpr hsurj, hsurj⟩)

end TensorSplit

/-! ## T1, case (3): non-split → split -/

section Mixed

variable (ℓ : ℕ) (E : Type) [Field E] [CharZero E] (D : SqrtNegOneExt E)
variable (E'' : Type) [Field E''] [CharZero E''] [Algebra D.carrier E'']

/-- The square of case (3), in the direction the components are built in.
@census none (helper; WP-15) -/
noncomputable def E_bc_mixed_iso' (hℓ : 1 ≤ ℓ) (h : Gelfand.RationalStructure.E_QSpec D.card_gal hℓ) :
    Gelfand.Equivalence.E_QFunctor D.card_gal hℓ h ⋙ qBCnsRel E D.carrier E'' D.card_gal ≅
      hcBaseChangeNS ℓ E D E'' ⋙ Split.hcLambdaToF E'' ℓ ⋙ Split.E_FNil ℓ hℓ :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk (RepNilRelSplit E'') (bcRepIso E'' hℓ A.toF))
    (fun {A B} f => by
      apply ObjectProperty.hom_ext
      apply RationalQuiver.Rep.Hom.ext
      funext v
      exact bcRepIso_natural E'' ((GF.baseChangeE ℓ E D).map f)
        ((Split.hcLambdaToF E'' ℓ).map ((hcBaseChange ℓ D.carrier E'').map ((forgetDescent ℓ E D).map f)))
        (fun a m => LinearMap.baseChange_tmul _ _ _) v)

/-- **T1, case (3) — `𝔼` commutes with base change, non-split → split** (the case `√-1 ∉ E`,
`√-1 ∈ E''`; the statement assumes neither), for every `ℓ ≥ 1`, every `E`-algebra map
`E(√-1) → E''` and every (equivalently: the unique) `h : E_QSpec`:

  `𝔼_E ⋙ qBCnsRel ≅ hcBaseChangeNS ⋙ 𝔼_{E''}`

as functors `HC_λ(𝔤,K)_E ⥤ Rep^nil_rel(Γ_{E''})`, `Γ_{E''}` the split Gelfand quiver.  The
components are the canonical maps `E'' ⊗_{E(√-1)} M_n → (E'' ⊗_{E(√-1)} M)_n`.  The quiver-side
`E'' ⊗_E −` is `qBCnsRel` by the identification `tensorSplitEquiv`. *(Disclosure, 2026-10-03,
`R-FR-9`, WP-16c, `V3-02`: that identification, like the HC-side one behind `hcBaseChangeNS`, is
not stated as a theorem; this iso does not use `tensorSplitEquiv`.)*

@census none (WP-15; T1 of `BASECHANGE-ANALYSIS.md`, `rmk:generalbases`, base change, case (3)) -/
noncomputable def E_bc_mixed_iso (hℓ : 1 ≤ ℓ) (h : Gelfand.RationalStructure.E_QSpec D.card_gal hℓ) :
    hcBaseChangeNS ℓ E D E'' ⋙ Split.hcLambdaToF E'' ℓ ⋙ Split.E_FNil ℓ hℓ ≅
      Gelfand.Equivalence.E_QFunctor D.card_gal hℓ h ⋙ qBCnsRel E D.carrier E'' D.card_gal :=
  (E_bc_mixed_iso' ℓ E D E'' hℓ h).symm

/-- **T1, case (3), pinned to the equivalences**: there are equivalences whose functors **are**
`𝔼_E` and `𝔼_{E''}`, and the base-change square commutes up to natural isomorphism.

@census none (WP-15; T1, case (3)) -/
theorem E_bc_mixed_compat (hℓ : 1 ≤ ℓ) :
    ∃ (h : Gelfand.RationalStructure.E_QSpec D.card_gal hℓ)
      (e : HCEObj ℓ E D ≌ (repNilRelGel E D.carrier D.card_gal).FullSubcategory)
      (e'' : HCLambda.{0} ℓ E'' ≌ (RepNilRelSplit E'').FullSubcategory),
      e.functor = Gelfand.Equivalence.E_QFunctor D.card_gal hℓ h ∧
      e''.functor = Split.hcLambdaToF E'' ℓ ⋙ Split.E_FNil ℓ hℓ ∧
      Nonempty (hcBaseChangeNS ℓ E D E'' ⋙ e''.functor ≅
        e.functor ⋙ qBCnsRel E D.carrier E'' D.card_gal) := by
  obtain ⟨h, e, he⟩ := Gelfand.EssSurj.E_Q_equivalence (Dq := D) hℓ
  haveI := Split.E_FNil_full (F := E'') ℓ hℓ
  haveI := Split.E_FNil_faithful (F := E'') ℓ hℓ
  haveI := Split.essSurj (L := E'') ℓ hℓ
  haveI : (Split.E_FNil (F := E'') ℓ hℓ).IsEquivalence := { }
  refine ⟨h, e, (Split.hcLambdaFEquiv E'' ℓ).trans (Split.E_FNil (F := E'') ℓ hℓ).asEquivalence,
    he, rfl, ?_⟩
  rw [he]
  exact ⟨E_bc_mixed_iso ℓ E D E'' hℓ h⟩

end Mixed

end RationalQuivers.Gelfand.BaseChange
