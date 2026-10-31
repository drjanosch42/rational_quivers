module

public import RationalQuivers.HC.Category
public import RationalQuivers.Descent.Galois
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Finiteness.Prod

@[expose] public section

/-!
# `HC_λ(𝔤,K)_E` is abelian, for every field `E` of characteristic `0`

`AUTHOR-QUEUE` row `T1-A`, resolved by the author on 2026-10-17, option (a): *formalize*.  The
author's argument:

> Proving abelianness in general is easy: We are a subcategory of `E`-vector spaces, and the vector
> space kernel and cokernel both carry canonical `𝔤,K`-module structures over `E`, and satisfy the
> universal property of the kernel / cokernel.  Moreover, we inherit monomorphisms and epimorphisms
> from vector spaces as well, i.e. an arrow is a mono / epi if and only if its kernel is `0` /
> cokernel is `0`.

This module follows that argument for the descent presentation `HC ℓ E D` of `HC/Category.lean`
(`def:HClambdaE`, `EX-HC`), mirroring `HC.harishChandraCat_abelian` (`HC/Classical.lean`) and the
`ModuleCat` pattern (`Mathlib/Algebra/Category/ModuleCat/Abelian.lean`).

## Contents, in order

1. **Descent of morphisms.**  A morphism `f : A ⟶ B` commutes with every `σ ⊗ 1`, so it maps
   `1 ⊗ M_E` into the `G_E`-fixed vectors of `M_{L_E}`, which are `1 ⊗ B_E` (Galois descent,
   `Descent.descentUnit_bijective`).  This gives the `E`-linear map `f_E : A_E → B_E` of the forms
   with `f = 1 ⊗ f_E` (`Hom.formMap`, `Hom.baseChange_formMap`): the "canonical structure over `E`"
   in the author's sense.
2. **Kernel.**  Carrier `ker f`, form `ker f_E`, base change `L_E ⊗ ker f_E ≅ ker (1 ⊗ f_E) ≅ ker f`
   (flatness of `L_E/E`, mathlib's `LinearMap.tensorKerEquiv`); weight data `WeightData.sub`, Galois
   action the restriction (`kerObj_galAct`).  Finite generation is `HC/Noetherian.lean`'s theorem.
3. **Cokernel.**  Carrier `B_{L_E} / range f`, form `B_E / range f_E`, the base change by right
   exactness (explicit inverse pair); weight data `WeightData.quot`.
4. **Binary products and the zero object**, needed for `HasFiniteProducts`.
5. **Monos and epis**: `f` is mono iff `ker f = 0` iff injective, epi iff `coker f = 0` iff
   surjective (`mono_iff_injective`, `epi_iff_surjective`); every mono is a kernel, every epi a
   cokernel; the `Abelian` instance and `HC.abelian`.
-/

namespace RationalQuivers.HC

open CategoryTheory
open scoped TensorProduct
open RationalQuivers.Unipotent

set_option linter.dupNamespace false

variable {E : Type} [Field E] {D : ImagUnit E}

/-! ## Galois descent for `L_E ⊗_E V`: the fixed vectors are `1 ⊗ V` -/

section Fixed

variable [CharZero E] {V : Type} [AddCommGroup V] [Module E V]

/-- Every `G_E`-fixed vector of `L_E ⊗_E V` is `1 ⊗ v` (`Descent.descentUnit_bijective`, the
surjective half of Galois descent).  @census none (helper) -/
theorem exists_one_tmul_of_galoisTwist_fixed (x : D.L ⊗[E] V)
    (hx : ∀ σ : D.L ≃ₐ[E] D.L, galoisTwist σ x = x) : ∃ v : V, (1 : D.L) ⊗ₜ[E] v = x := by
  obtain ⟨v, hv⟩ := (Descent.descentUnit_bijective E D.L (ModuleCat.of E V)).2 ⟨x, hx⟩
  exact ⟨v, congrArg Subtype.val hv⟩

/-- `v ↦ 1 ⊗ v` is injective (the injective half of Galois descent).  @census none (helper) -/
theorem one_tmul_injective' {v w : V} (h : (1 : D.L) ⊗ₜ[E] v = (1 : D.L) ⊗ₜ[E] w) : v = w :=
  (Descent.descentUnit_bijective E D.L (ModuleCat.of E V)).1 (Subtype.ext h)

omit [CharZero E] in
/-- `σ ⊗ 1` commutes with `1 ⊗ g`.  @census none (helper) -/
theorem galoisTwist_lTensor {W : Type} [AddCommGroup W] [Module E W] (g : V →ₗ[E] W)
    (σ : D.L ≃ₐ[E] D.L) (x : D.L ⊗[E] V) :
    galoisTwist σ (g.lTensor D.L x) = g.lTensor D.L (galoisTwist σ x) := by
  induction x with
  | tmul a v => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end Fixed

/-! ## Weight data: the Casimir on sub-objects, quotients and products -/

namespace WeightData

variable {F : Type} [Field F] [CharZero F] {M : Type} [AddCommGroup M] [Module F M]

omit [CharZero F] in
theorem sub_casimir_coe {W : WeightData F M} {N : Submodule F M} (hst : W.OpStable N)
    (hhom : W.IsHomog N) (v : N) :
    (((sub hst hhom).casimir v : N) : M) = W.casimir v := by
  rw [casimir_apply, casimir_apply]
  simp

/-- The generalized infinitesimal character passes to a stable homogeneous submodule.
@census none (helper) -/
theorem gic_sub {W : WeightData F M} {N : Submodule F M} (hst : W.OpStable N)
    (hhom : W.IsHomog N) {ℓ : ℕ} (h : HasGeneralizedInfinitesimalCharacter W ℓ) :
    HasGeneralizedInfinitesimalCharacter (sub hst hhom) ℓ := by
  obtain ⟨m, hm⟩ := h
  set c : F := algebraMap ℚ F ((ℓ : ℚ) ^ 2)
  have key : ∀ (k : ℕ) (v : N), ((((sub hst hhom).casimir - c • (1 : Module.End F N)) ^ k) v
      : M) = ((W.casimir - c • (1 : Module.End F M)) ^ k) (v : M) := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
        intro v
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
        congr 1
  refine ⟨m, LinearMap.ext fun v => Subtype.ext ?_⟩
  rw [key, hm]
  rfl

/-- The generalized infinitesimal character passes to the quotient.  @census none (helper) -/
theorem gic_quot {W : WeightData F M} {N : Submodule F M} (hst : W.OpStable N)
    (hhom : W.IsHomog N) {ℓ : ℕ} (h : HasGeneralizedInfinitesimalCharacter W ℓ) :
    HasGeneralizedInfinitesimalCharacter (quot hst hhom) ℓ := by
  obtain ⟨m, hm⟩ := h
  set c : F := algebraMap ℚ F ((ℓ : ℚ) ^ 2)
  have hC : ∀ v : M, (quot hst hhom).casimir (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (W.casimir v) := by
    intro v
    rw [casimir_apply, casimir_apply]
    simp
  have key : ∀ (k : ℕ) (v : M), (((quot hst hhom).casimir - c • (1 : Module.End F (M ⧸ N))) ^ k)
      (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (((W.casimir - c • (1 : Module.End F M)) ^ k) v) := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
        intro v
        rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
        have : ((quot hst hhom).casimir - c • (1 : Module.End F (M ⧸ N)))
            (Submodule.Quotient.mk v) =
            Submodule.Quotient.mk ((W.casimir - c • (1 : Module.End F M)) v) := by
          simp [hC]
        rw [this, ih]
  refine ⟨m, LinearMap.ext fun x => ?_⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
  rw [key, hm]
  rfl

/-- The generalized infinitesimal character passes to a binary product.  @census none (helper) -/
theorem gic_prodData {M₂ : Type} [AddCommGroup M₂] [Module F M₂] {W₁ : WeightData F M}
    {W₂ : WeightData F M₂} {ℓ : ℕ} (h₁ : HasGeneralizedInfinitesimalCharacter W₁ ℓ)
    (h₂ : HasGeneralizedInfinitesimalCharacter W₂ ℓ) :
    HasGeneralizedInfinitesimalCharacter (prodData W₁ W₂) ℓ := by
  obtain ⟨m₁, hm₁⟩ := h₁
  obtain ⟨m₂, hm₂⟩ := h₂
  set c : F := algebraMap ℚ F ((ℓ : ℚ) ^ 2)
  have hC : ∀ v : M × M₂, (prodData W₁ W₂).casimir v = (W₁.casimir v.1, W₂.casimir v.2) := by
    intro v
    rw [casimir_apply, casimir_apply, casimir_apply]
    rfl
  have key : ∀ (k : ℕ) (v : M × M₂),
      (((prodData W₁ W₂).casimir - c • (1 : Module.End F (M × M₂))) ^ k) v =
      (((W₁.casimir - c • (1 : Module.End F M)) ^ k) v.1,
        ((W₂.casimir - c • (1 : Module.End F M₂)) ^ k) v.2) := by
    intro k
    induction k with
    | zero => intro v; rfl
    | succ k ih =>
        intro v
        rw [pow_succ, pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
          Module.End.mul_apply, ih]
        congr 1
  refine ⟨m₁ + m₂, LinearMap.ext fun v => ?_⟩
  rw [key, pow_add, pow_add, hm₁, hm₂, zero_mul, mul_zero]
  rfl

end WeightData

/-! ## `gkSpanOver`: the generation lemmas -/

section Span

variable {F : Type} [Field F] {M : Type} [AddCommGroup M] [Module F M]

theorem eq_top_of_gkSpanOver_eq_top {W : WeightData F M} {S : Set M} {P : Submodule F M}
    (h : gkSpanOver W S = ⊤) (hS : S ⊆ (P : Set M)) (hst : W.OpStable P) (hhom : W.IsHomog P) :
    P = ⊤ :=
  top_le_iff.mp (h ▸ sInf_le ⟨hS, hst, hhom⟩)

theorem gkSpanOver_eq_top {W : WeightData F M} {S : Set M}
    (h : ∀ P : Submodule F M, S ⊆ (P : Set M) → W.OpStable P → W.IsHomog P → P = ⊤) :
    gkSpanOver W S = ⊤ :=
  le_antisymm le_top (le_sInf fun _ hQ => (h _ hQ.1 hQ.2.1 hQ.2.2) ▸ le_rfl)

/-- `fg` re-read: generated by finitely many **weight vectors** (the shape
`WeightData.exists_finite_generating_set` consumes).  @census none (helper) -/
theorem exists_homogeneous_generators_of_gkSpanOver {W : WeightData F M} {S : Finset M}
    (hS : gkSpanOver W (↑S : Set M) = ⊤) :
    ∃ T : Finset M, (∀ v ∈ T, ∃ n : ℤ, v ∈ W.comp n) ∧
      ∀ P : Submodule F M, (↑T : Set M) ⊆ (P : Set M) → W.OpStable P → W.IsHomog P → P = ⊤ := by
  classical
  choose sup hzero hsum using W.exists_sum_proj
  refine ⟨S.biUnion (fun s => (sup s).image (fun n => W.proj n s)), ?_, ?_⟩
  · intro v hv
    simp only [Finset.mem_biUnion, Finset.mem_image] at hv
    obtain ⟨s, -, n, -, rfl⟩ := hv
    exact ⟨n, W.proj_mem n s⟩
  · intro P hTP hst hhom
    refine eq_top_of_gkSpanOver_eq_top hS ?_ hst hhom
    intro s hs
    simp only [Finset.mem_coe] at hs
    rw [SetLike.mem_coe, ← hsum s]
    refine sum_mem fun n hn => hTP ?_
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.coe_image,
      Set.mem_image, exists_prop]
    exact ⟨s, hs, n, hn, rfl⟩

/-- A stable homogeneous submodule of a finitely generated admissible weight module is finitely
generated (`HC/Noetherian.lean`, transported along `N.subtype`).  @census none (helper) -/
theorem fg_sub [CharZero F] {W : WeightData F M} (hadm : ∀ n : ℤ, FiniteDimensional F (W.comp n))
    (hfg : ∃ S : Finset M, gkSpanOver W (↑S : Set M) = ⊤) {N : Submodule F M}
    (hst : W.OpStable N) (hhom : W.IsHomog N) :
    ∃ S : Finset N, gkSpanOver (W.sub hst hhom) (↑S : Set N) = ⊤ := by
  classical
  obtain ⟨S₀, hS₀⟩ := hfg
  obtain ⟨T, hTw, hTgen⟩ := exists_homogeneous_generators_of_gkSpanOver hS₀
  obtain ⟨S, hSN, hSgen⟩ :=
    WeightData.exists_finite_generating_set W hadm T hTw hTgen N hst hhom
  have hmem : ∀ x : {a : M // a ∈ S}, (x : M) ∈ N := fun x => hSN x.2
  refine ⟨S.attach.image (fun x : {a : M // a ∈ S} => (⟨(x : M), hmem x⟩ : N)),
    gkSpanOver_eq_top ?_⟩
  intro Q hQS hQst _
  have hPle : N ≤ Q.map N.subtype := by
    refine hSgen (Q.map N.subtype) ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe] at hx
      refine ⟨⟨x, hSN (by simpa using hx)⟩, ?_, rfl⟩
      refine hQS ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩
    · refine ⟨?_, ?_, ?_⟩ <;> rintro v ⟨w, hw, rfl⟩
      · exact ⟨(W.sub hst hhom).H w, hQst.1 w hw, rfl⟩
      · exact ⟨(W.sub hst hhom).X w, hQst.2.1 w hw, rfl⟩
      · exact ⟨(W.sub hst hhom).Y w, hQst.2.2 w hw, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hxy⟩ := hPle x.2
  have : y = x := Subtype.ext hxy
  rwa [← this]

/-- Finite generation passes to the quotient.  @census none (helper) -/
theorem fg_quot {W : WeightData F M} (hfg : ∃ S : Finset M, gkSpanOver W (↑S : Set M) = ⊤)
    {N : Submodule F M} (hst : W.OpStable N) (hhom : W.IsHomog N) :
    ∃ S : Finset (M ⧸ N), gkSpanOver (W.quot hst hhom) (↑S : Set (M ⧸ N)) = ⊤ := by
  classical
  obtain ⟨S, hS⟩ := hfg
  refine ⟨S.image N.mkQ, gkSpanOver_eq_top fun P hSP hst' hhom' => ?_⟩
  have hcomap : Submodule.comap N.mkQ P = ⊤ := by
    refine eq_top_of_gkSpanOver_eq_top hS ?_ ⟨?_, ?_, ?_⟩ ?_
    · intro x hx
      refine hSP ?_
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨x, hx, rfl⟩
    · intro v hv; exact hst'.1 _ hv
    · intro v hv; exact hst'.2.1 _ hv
    · intro v hv; exact hst'.2.2 _ hv
    · intro n v hv
      have h := WeightData.proj_comm_of_map W (W.quot hst hhom) N.mkQ
        (fun m w hw => ⟨w, hw, rfl⟩) n v
      show N.mkQ (W.proj n v) ∈ P
      rw [← h]
      exact hhom' n _ hv
  rw [eq_top_iff]
  intro x _
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
  have : v ∈ Submodule.comap N.mkQ P := by rw [hcomap]; trivial
  exact this

/-- Finite generation passes to binary products.  @census none (helper) -/
theorem fg_prodData {M₂ : Type} [AddCommGroup M₂] [Module F M₂] {W₁ : WeightData F M}
    {W₂ : WeightData F M₂} (h₁ : ∃ S : Finset M, gkSpanOver W₁ (↑S : Set M) = ⊤)
    (h₂ : ∃ S : Finset M₂, gkSpanOver W₂ (↑S : Set M₂) = ⊤) :
    ∃ S : Finset (M × M₂), gkSpanOver (WeightData.prodData W₁ W₂) (↑S : Set (M × M₂)) = ⊤ := by
  classical
  obtain ⟨S₁, hS₁⟩ := h₁
  obtain ⟨S₂, hS₂⟩ := h₂
  refine ⟨S₁.image (LinearMap.inl F M M₂) ∪ S₂.image (LinearMap.inr F M M₂),
    gkSpanOver_eq_top fun P hSP hst hhom => ?_⟩
  have hinl : ∀ (n : ℤ) (v : M), v ∈ W₁.comp n →
      LinearMap.inl F M M₂ v ∈ (WeightData.prodData W₁ W₂).comp n :=
    fun n v hv => ⟨hv, Submodule.zero_mem _⟩
  have hinr : ∀ (n : ℤ) (v : M₂), v ∈ W₂.comp n →
      LinearMap.inr F M M₂ v ∈ (WeightData.prodData W₁ W₂).comp n :=
    fun n v hv => ⟨Submodule.zero_mem _, hv⟩
  have h1 : Submodule.comap (LinearMap.inl F M M₂) P = ⊤ := by
    refine eq_top_of_gkSpanOver_eq_top hS₁ ?_ ⟨?_, ?_, ?_⟩ ?_
    · intro x hx
      refine hSP ?_
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe]
      exact Or.inl ⟨x, hx, rfl⟩
    · intro v hv
      have := hst.1 _ hv
      simpa [WeightData.prodData] using this
    · intro v hv
      have := hst.2.1 _ hv
      simpa [WeightData.prodData] using this
    · intro v hv
      have := hst.2.2 _ hv
      simpa [WeightData.prodData] using this
    · intro n v hv
      show LinearMap.inl F M M₂ (W₁.proj n v) ∈ P
      rw [← WeightData.proj_comm_of_map W₁ _ _ hinl n v]
      exact hhom n _ hv
  have h2 : Submodule.comap (LinearMap.inr F M M₂) P = ⊤ := by
    refine eq_top_of_gkSpanOver_eq_top hS₂ ?_ ⟨?_, ?_, ?_⟩ ?_
    · intro x hx
      refine hSP ?_
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe]
      exact Or.inr ⟨x, hx, rfl⟩
    · intro v hv
      have := hst.1 _ hv
      simpa [WeightData.prodData] using this
    · intro v hv
      have := hst.2.1 _ hv
      simpa [WeightData.prodData] using this
    · intro v hv
      have := hst.2.2 _ hv
      simpa [WeightData.prodData] using this
    · intro n v hv
      show LinearMap.inr F M M₂ (W₂.proj n v) ∈ P
      rw [← WeightData.proj_comm_of_map W₂ _ _ hinr n v]
      exact hhom n _ hv
  rw [eq_top_iff]
  rintro ⟨a, b⟩ -
  have ha : LinearMap.inl F M M₂ a ∈ P := by
    have : a ∈ Submodule.comap (LinearMap.inl F M M₂) P := by rw [h1]; trivial
    exact this
  have hb : LinearMap.inr F M M₂ b ∈ P := by
    have : b ∈ Submodule.comap (LinearMap.inr F M M₂) P := by rw [h2]; trivial
    exact this
  have := add_mem ha hb
  simpa using this

end Span

/-! ## `GalCompat` on sub-objects, quotients and products -/

section Compat

variable {Mi : Type} [AddCommGroup Mi] [Module D.L Mi] {W : WeightData D.L Mi} {g : Mi ≃+ Mi}
  {s : ℤˣ}

theorem GalCompat.sub (hc : GalCompat D W g s) {N : Submodule D.L Mi} (hst : W.OpStable N)
    (hhom : W.IsHomog N) (g' : N ≃+ N) (hg' : ∀ v, (g' v : Mi) = g v) :
    GalCompat D (W.sub hst hhom) g' s where
  comp n v hv := by
    show ((g' v : N) : Mi) ∈ W.comp ((s : ℤ) * n)
    rw [hg']; exact hc.comp n _ hv
  H v := Subtype.ext (by
    rw [hg', WeightData.sub_H_coe, hc.H, Submodule.coe_smul_of_tower, WeightData.sub_H_coe, hg'])
  X_one h v := Subtype.ext (by
    rw [hg', WeightData.sub_X_coe, hc.X_one h, WeightData.sub_X_coe, hg'])
  Y_one h v := Subtype.ext (by
    rw [hg', WeightData.sub_Y_coe, hc.Y_one h, WeightData.sub_Y_coe, hg'])
  X_neg h v := Subtype.ext (by
    rw [hg', WeightData.sub_X_coe, hc.X_neg h, WeightData.sub_Y_coe, hg'])
  Y_neg h v := Subtype.ext (by
    rw [hg', WeightData.sub_Y_coe, hc.Y_neg h, WeightData.sub_X_coe, hg'])

theorem GalCompat.quot (hc : GalCompat D W g s) {N : Submodule D.L Mi} (hst : W.OpStable N)
    (hhom : W.IsHomog N) (g' : (Mi ⧸ N) ≃+ (Mi ⧸ N))
    (hg' : ∀ v, g' (Submodule.Quotient.mk v) = Submodule.Quotient.mk (g v)) :
    GalCompat D (W.quot hst hhom) g' s where
  comp n x hx := by
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨g a, hc.comp n a ha, (hg' a).symm⟩
  H x := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    rw [WeightData.quot_H_mk, hg', hg', WeightData.quot_H_mk, hc.H]
    rfl
  X_one h x := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    rw [WeightData.quot_X_mk, hg', hg', WeightData.quot_X_mk, hc.X_one h]
  Y_one h x := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    rw [WeightData.quot_Y_mk, hg', hg', WeightData.quot_Y_mk, hc.Y_one h]
  X_neg h x := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    rw [WeightData.quot_X_mk, hg', hg', WeightData.quot_Y_mk, hc.X_neg h]
  Y_neg h x := by
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    rw [WeightData.quot_Y_mk, hg', hg', WeightData.quot_X_mk, hc.Y_neg h]

theorem GalCompat.prod {Mi₂ : Type} [AddCommGroup Mi₂] [Module D.L Mi₂] {W₂ : WeightData D.L Mi₂}
    {g₂ : Mi₂ ≃+ Mi₂} (hc : GalCompat D W g s) (hc₂ : GalCompat D W₂ g₂ s)
    (g' : (Mi × Mi₂) ≃+ (Mi × Mi₂)) (hg' : ∀ v, g' v = (g v.1, g₂ v.2)) :
    GalCompat D (WeightData.prodData W W₂) g' s where
  comp n v hv := by
    rw [hg']; exact ⟨hc.comp n _ hv.1, hc₂.comp n _ hv.2⟩
  H v := by
    rw [hg', hg']
    exact Prod.ext (hc.H v.1) (hc₂.H v.2)
  X_one h v := by
    rw [hg', hg']
    exact Prod.ext (hc.X_one h v.1) (hc₂.X_one h v.2)
  Y_one h v := by
    rw [hg', hg']
    exact Prod.ext (hc.Y_one h v.1) (hc₂.Y_one h v.2)
  X_neg h v := by
    rw [hg', hg']
    exact Prod.ext (hc.X_neg h v.1) (hc₂.X_neg h v.2)
  Y_neg h v := by
    rw [hg', hg']
    exact Prod.ext (hc.Y_neg h v.1) (hc₂.Y_neg h v.2)

end Compat

variable [CharZero E]

namespace HC

variable {ℓ : ℕ}

/-! ## 1. Descent of morphisms: `f = 1 ⊗ f_E` -/

/-- The inclusion `M_E → M_{L_E}`, `v ↦ 1 ⊗ v`.  @census none (helper) -/
noncomputable def formIncl (A : HC ℓ E D) (v : A.form) : A.carrier :=
  A.baseChange ((1 : D.L) ⊗ₜ[E] v)

theorem formIncl_apply (A : HC ℓ E D) (v : A.form) :
    A.formIncl v = A.baseChange ((1 : D.L) ⊗ₜ[E] v) := rfl

theorem formIncl_add (A : HC ℓ E D) (v w : A.form) :
    A.formIncl (v + w) = A.formIncl v + A.formIncl w := by
  rw [formIncl_apply, TensorProduct.tmul_add, map_add]; rfl

theorem formIncl_smul (A : HC ℓ E D) (c : E) (v : A.form) :
    A.formIncl (c • v) = algebraMap E D.L c • A.formIncl v := by
  rw [formIncl_apply, TensorProduct.tmul_smul, ← algebraMap_smul D.L c, map_smul]; rfl

theorem formIncl_injective (A : HC ℓ E D) : Function.Injective A.formIncl := fun _ _ h =>
  one_tmul_injective' (D := D) (A.baseChange.injective h)

theorem galAct_apply (A : HC ℓ E D) (σ : D.L ≃ₐ[E] D.L) (v : A.carrier) :
    A.galAct σ v = A.baseChange (galoisTwist σ (A.baseChange.symm v)) := rfl

theorem baseChange_symm_galAct (A : HC ℓ E D) (σ : D.L ≃ₐ[E] D.L) (v : A.carrier) :
    A.baseChange.symm (A.galAct σ v) = galoisTwist σ (A.baseChange.symm v) := by
  rw [galAct_apply, LinearEquiv.symm_apply_apply]

namespace Hom

variable {A B : HC ℓ E D}

/-- `f(1 ⊗ v)` is `G_E`-fixed, hence `1 ⊗ w` for a unique `w ∈ B_E`.  @census none (helper) -/
theorem exists_formMap (f : Hom A B) (v : A.form) :
    ∃ w : B.form, B.formIncl w = f.toLinearMap (A.formIncl v) := by
  obtain ⟨w, hw⟩ := exists_one_tmul_of_galoisTwist_fixed (D := D)
    (B.baseChange.symm (f.toLinearMap (A.formIncl v))) (fun σ => by
      rw [← baseChange_symm_galAct, ← f.map_gal]
      exact congrArg (fun z => B.baseChange.symm (f.toLinearMap z)) (galActOf_tmul _ σ v))
  refine ⟨w, ?_⟩
  rw [formIncl_apply, hw, LinearEquiv.apply_symm_apply]

/-- **The descended map** `f_E : A_E → B_E` of the forms.  @census none (helper) -/
noncomputable def formMap (f : Hom A B) : A.form →ₗ[E] B.form where
  toFun v := (f.exists_formMap v).choose
  map_add' v w := formIncl_injective B (by
    have h1 := (f.exists_formMap (v + w)).choose_spec
    have h2 := (f.exists_formMap v).choose_spec
    have h3 := (f.exists_formMap w).choose_spec
    refine h1.trans ?_
    rw [formIncl_add A v w, map_add, formIncl_add B, h2, h3])
  map_smul' c v := formIncl_injective B (by
    have h1 := (f.exists_formMap (c • v)).choose_spec
    have h2 := (f.exists_formMap v).choose_spec
    refine h1.trans ?_
    rw [RingHom.id_apply, formIncl_smul A c v, map_smul, formIncl_smul B, h2])

theorem formIncl_formMap (f : Hom A B) (v : A.form) :
    B.formIncl (f.formMap v) = f.toLinearMap (A.formIncl v) :=
  (f.exists_formMap v).choose_spec

/-- **`f = 1 ⊗ f_E`**: the morphism is the base change of the descended map.
@census none (helper) -/
theorem baseChange_formMap (f : Hom A B) (x : D.L ⊗[E] A.form) :
    B.baseChange (f.formMap.lTensor D.L x) = f.toLinearMap (A.baseChange x) := by
  induction x with
  | tmul a v =>
      have h1 : (a ⊗ₜ[E] v : D.L ⊗[E] A.form) = a • ((1 : D.L) ⊗ₜ[E] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have h2 : (a ⊗ₜ[E] f.formMap v : D.L ⊗[E] B.form) = a • ((1 : D.L) ⊗ₜ[E] f.formMap v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.lTensor_tmul, h1, h2, map_smul, map_smul, map_smul, ← formIncl_apply A v,
        ← formIncl_apply B (f.formMap v), formIncl_formMap]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem baseChange_symm_toLinearMap (f : Hom A B) (v : A.carrier) :
    B.baseChange.symm (f.toLinearMap v) = f.formMap.lTensor D.L (A.baseChange.symm v) := by
  rw [LinearEquiv.symm_apply_eq, baseChange_formMap, LinearEquiv.apply_symm_apply]

/-- `ker f` is homogeneous.  @census none (helper) -/
theorem isHomog_ker (f : Hom A B) : A.weight.IsHomog (LinearMap.ker f.toLinearMap) := by
  intro n v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have h := WeightData.proj_comm_of_map A.weight B.weight f.toLinearMap f.map_comp n v
  rw [hv, map_zero] at h
  exact h.symm

theorem opStable_ker (f : Hom A B) : A.weight.OpStable (LinearMap.ker f.toLinearMap) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro v hv <;> rw [LinearMap.mem_ker] at hv ⊢
  · rw [f.map_H, hv, map_zero]
  · rw [f.map_X, hv, map_zero]
  · rw [f.map_Y, hv, map_zero]

/-- `range f` is homogeneous.  @census none (helper) -/
theorem isHomog_range (f : Hom A B) : B.weight.IsHomog (LinearMap.range f.toLinearMap) := by
  rintro n v ⟨a, rfl⟩
  exact ⟨A.weight.proj n a,
    (WeightData.proj_comm_of_map A.weight B.weight f.toLinearMap f.map_comp n a).symm⟩

theorem opStable_range (f : Hom A B) : B.weight.OpStable (LinearMap.range f.toLinearMap) := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro v ⟨a, rfl⟩
  · exact ⟨A.weight.H a, f.map_H a⟩
  · exact ⟨A.weight.X a, f.map_X a⟩
  · exact ⟨A.weight.Y a, f.map_Y a⟩

/-- `1 ⊗ f_E` kills `x` iff `f` kills its image in `M_{L_E}`.  @census none (helper) -/
theorem mem_ker_lTensor_iff (f : Hom A B) (x : D.L ⊗[E] A.form) :
    x ∈ LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor D.L D.L f.formMap) ↔
      A.baseChange x ∈ LinearMap.ker f.toLinearMap := by
  rw [LinearMap.mem_ker, LinearMap.mem_ker, TensorProduct.AlgebraTensorModule.coe_lTensor,
    ← baseChange_formMap, LinearEquiv.map_eq_zero_iff]

/-- Left cancellation: a linear map that becomes a morphism after composing with an injective
morphism is a morphism.  The grading condition is entailed (`WeightData.map_comp_of_map_H`).
@census none (helper) -/
def ofInjectiveComp {T : HC ℓ E D} (f : Hom A B) (hinj : Function.Injective f.toLinearMap)
    (k : Hom T B) (l : T.carrier →ₗ[D.L] A.carrier) (hl : ∀ t, f.toLinearMap (l t) = k.toLinearMap t) :
    Hom T A :=
  have hH : ∀ v, l (T.weight.H v) = A.weight.H (l v) :=
    fun v => hinj (by rw [hl, k.map_H, f.map_H, hl])
  { toLinearMap := l
    map_H := hH
    map_X := fun v => hinj (by rw [hl, k.map_X, f.map_X, hl])
    map_Y := fun v => hinj (by rw [hl, k.map_Y, f.map_Y, hl])
    map_comp := fun n v hv => WeightData.map_comp_of_map_H T.weight A.weight l hH n v hv
    map_gal := fun σ v => hinj (by rw [hl, k.map_gal, f.map_gal, hl]) }

/-- Right cancellation: a linear map that becomes a morphism after precomposing with a surjective
morphism is a morphism.  @census none (helper) -/
def ofCompSurjective {T : HC ℓ E D} (f : Hom A B) (hsurj : Function.Surjective f.toLinearMap)
    (k : Hom A T) (l : B.carrier →ₗ[D.L] T.carrier) (hl : ∀ a, l (f.toLinearMap a) = k.toLinearMap a) :
    Hom B T :=
  have hH : ∀ v, l (B.weight.H v) = T.weight.H (l v) := fun v => by
    obtain ⟨a, rfl⟩ := hsurj v
    rw [← f.map_H, hl, hl, k.map_H]
  { toLinearMap := l
    map_H := hH
    map_X := fun v => by
      obtain ⟨a, rfl⟩ := hsurj v
      rw [← f.map_X, hl, hl, k.map_X]
    map_Y := fun v => by
      obtain ⟨a, rfl⟩ := hsurj v
      rw [← f.map_Y, hl, hl, k.map_Y]
    map_comp := fun n v hv => WeightData.map_comp_of_map_H B.weight T.weight l hH n v hv
    map_gal := fun σ v => by
      obtain ⟨a, rfl⟩ := hsurj v
      rw [← f.map_gal, hl, hl, k.map_gal] }

end Hom

theorem hom_ext {A B : HC ℓ E D} {f g : A ⟶ B}
    (h : ∀ v, (f : Hom A B).toLinearMap v = (g : Hom A B).toLinearMap v) : f = g :=
  Hom.ext' (LinearMap.ext h)

@[simp] theorem zero_toLinearMap' {A B : HC ℓ E D} : ((0 : A ⟶ B) : Hom A B).toLinearMap = 0 :=
  rfl

/-! ## Monos are injective, epis are surjective (one direction) -/

theorem mono_of_injective {A B : HC ℓ E D} {f : A ⟶ B}
    (h : Function.Injective (f : Hom A B).toLinearMap) : Mono f :=
  ⟨fun {T} _ _ heq => hom_ext fun v => h
    (congrArg (fun t : T ⟶ B => (t : Hom T B).toLinearMap v) heq)⟩

theorem epi_of_surjective {A B : HC ℓ E D} {f : A ⟶ B}
    (h : Function.Surjective (f : Hom A B).toLinearMap) : Epi f :=
  ⟨fun {T} g₁ g₂ heq => hom_ext fun v => by
    obtain ⟨a, rfl⟩ := h v
    exact congrArg (fun t : A ⟶ T => (t : Hom A T).toLinearMap a) heq⟩

/-! ## 2. Kernels -/

section Kernel

variable {A B : HC ℓ E D} (f : Hom A B)

/-- `ker (1 ⊗ f_E) ≅ ker f` along the base change of `A`.  @census none (helper) -/
noncomputable def kerEquivAux :
    LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor D.L D.L f.formMap) ≃ₗ[D.L]
      LinearMap.ker f.toLinearMap :=
  LinearEquiv.ofBijective
    (A.baseChange.toLinearMap.restrict fun x hx => (f.mem_ker_lTensor_iff x).1 hx)
    ⟨fun x y h => Subtype.ext (A.baseChange.injective (congrArg Subtype.val h)),
      fun w => ⟨⟨A.baseChange.symm w, (f.mem_ker_lTensor_iff _).2 (by simp only [LinearEquiv.apply_symm_apply]; exact w.2)⟩,
        Subtype.ext (by simp [LinearMap.restrict_apply])⟩⟩

/-- **The base change of the kernel**: `L_E ⊗_E ker f_E ≅ ker (1 ⊗ f_E) ≅ ker f`, the first
isomorphism by flatness of `L_E/E` (mathlib's `LinearMap.tensorKerEquiv`).  @census none (helper) -/
noncomputable def kerBaseChange :
    (D.L ⊗[E] LinearMap.ker f.formMap) ≃ₗ[D.L] LinearMap.ker f.toLinearMap :=
  (LinearMap.tensorKerEquiv D.L D.L f.formMap).trans (kerEquivAux f)

theorem coe_kerBaseChange (z : D.L ⊗[E] LinearMap.ker f.formMap) :
    ((kerBaseChange f z : LinearMap.ker f.toLinearMap) : A.carrier) =
      A.baseChange ((LinearMap.ker f.formMap).subtype.lTensor D.L z) := by
  show A.baseChange ((LinearMap.tensorKerEquiv D.L D.L f.formMap z : _) : D.L ⊗[E] A.form) = _
  rw [LinearMap.tensorKerEquiv_apply, LinearMap.tensorKer_coe]

/-- The Galois action on the kernel is the restriction of `A`'s.  @census none (helper) -/
theorem galActOf_kerBaseChange (σ : D.L ≃ₐ[E] D.L) (v : LinearMap.ker f.toLinearMap) :
    ((galActOf D (kerBaseChange f) σ v : LinearMap.ker f.toLinearMap) : A.carrier) =
      A.galAct σ v := by
  have hy : (LinearMap.ker f.formMap).subtype.lTensor D.L ((kerBaseChange f).symm v) =
      A.baseChange.symm v := by
    rw [LinearEquiv.eq_symm_apply, ← coe_kerBaseChange, LinearEquiv.apply_symm_apply]
  rw [galActOf_apply, coe_kerBaseChange, ← galoisTwist_lTensor, hy]
  rfl

/-- **The kernel object** `ker f ∈ HC_λ(𝔤,K)_E`: the vector-space kernel `ker f ⊆ A_{L_E}` with the
induced weight data and Galois action, and `E`-form `ker f_E`.  @census none (helper) -/
noncomputable def kerObj : HC ℓ E D where
  form := LinearMap.ker f.formMap
  carrier := LinearMap.ker f.toLinearMap
  baseChange := kerBaseChange f
  weight := A.weight.sub f.opStable_ker f.isHomog_ker
  gic := WeightData.gic_sub _ _ A.gic
  galCompat σ := (A.galCompat σ).sub _ _ _ (galActOf_kerBaseChange f σ)
  admissible n := by
    haveI := A.admissible n
    let g : ((A.weight.sub f.opStable_ker f.isHomog_ker).comp n) →ₗ[D.L] (A.weight.comp n) :=
      { toFun := fun v => ⟨((v : LinearMap.ker f.toLinearMap) : A.carrier), v.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hinj : Function.Injective g := fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun z : (A.weight.comp n) => (z : A.carrier)) hxy))
    exact FiniteDimensional.of_injective g hinj
  centralCharacter n hn := by
    rw [WeightData.sub_comp, A.centralCharacter n hn, Submodule.comap_bot, Submodule.ker_subtype]
  fg := fg_sub A.admissible A.fg _ _

theorem kerObj_galAct (σ : D.L ≃ₐ[E] D.L) (v : LinearMap.ker f.toLinearMap) :
    (LinearMap.ker f.toLinearMap).subtype ((kerObj f).galAct σ v) =
      A.galAct σ ((LinearMap.ker f.toLinearMap).subtype v) :=
  galActOf_kerBaseChange f σ v

/-- The inclusion `ker f ↪ A`.  @census none (helper) -/
noncomputable def kernelι : kerObj f ⟶ A :=
  (⟨(LinearMap.ker f.toLinearMap).subtype, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ hv => hv, fun σ v => kerObj_galAct f σ v⟩ : Hom (kerObj f) A)

theorem kernelι_comp : kernelι f ≫ (f : A ⟶ B) = 0 :=
  hom_ext fun v => LinearMap.mem_ker.mp v.2

/-- The vector-space kernel satisfies the **universal property of the kernel**.
@census none (helper) -/
noncomputable def kernelIsLimit :
    Limits.IsLimit (Limits.KernelFork.ofι (kernelι f) (kernelι_comp f)) := by
  haveI : Mono (kernelι f) := mono_of_injective Subtype.coe_injective
  refine Limits.KernelFork.IsLimit.ofι' (kernelι f) (kernelι_comp f) (fun {T} k hk => ?_)
  · have hmem : ∀ t, (k : Hom T A).toLinearMap t ∈ LinearMap.ker f.toLinearMap := fun t =>
      LinearMap.mem_ker.mpr (congrArg (fun z : T ⟶ B => (z : Hom T B).toLinearMap t) hk)
    refine ⟨(⟨LinearMap.codRestrict _ (k : Hom T A).toLinearMap hmem,
      fun v => Subtype.ext ((k : Hom T A).map_H v), fun v => Subtype.ext ((k : Hom T A).map_X v),
      fun v => Subtype.ext ((k : Hom T A).map_Y v), fun n v hv => (k : Hom T A).map_comp n v hv,
      fun σ v => Subtype.ext
        (((k : Hom T A).map_gal σ v).trans
          (kerObj_galAct f σ ⟨(k : Hom T A).toLinearMap v, hmem v⟩).symm)⟩ : Hom T (kerObj f)), ?_⟩
    exact hom_ext fun _ => rfl

noncomputable instance : Limits.HasKernels (HC ℓ E D) :=
  ⟨fun f => Limits.HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

end Kernel

/-! ## 3. Cokernels -/

section Cokernel

variable {A B : HC ℓ E D} (f : Hom A B)

/-- `B_{L_E} / range f → L_E ⊗_E (B_E / range f_E)`.  @census none (helper) -/
noncomputable def cokerψ :
    (B.carrier ⧸ LinearMap.range f.toLinearMap) →ₗ[D.L] D.L ⊗[E] (B.form ⧸ LinearMap.range f.formMap) :=
  (LinearMap.range f.toLinearMap).liftQ
    ((TensorProduct.AlgebraTensorModule.lTensor D.L D.L (LinearMap.range f.formMap).mkQ).comp
      B.baseChange.symm.toLinearMap) (by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearEquiv.coe_coe, f.baseChange_symm_toLinearMap,
      TensorProduct.AlgebraTensorModule.coe_lTensor, ← LinearMap.lTensor_comp_apply,
      LinearMap.range_mkQ_comp, LinearMap.lTensor_zero, LinearMap.zero_apply])

theorem cokerψ_mk (w : B.carrier) :
    cokerψ f (Submodule.Quotient.mk w) =
      (LinearMap.range f.formMap).mkQ.lTensor D.L (B.baseChange.symm w) := rfl

theorem cokerψ_bijective : Function.Bijective (cokerψ f) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [cokerψ_mk] at hx
    obtain ⟨z, hz⟩ := (lTensor_exact D.L
      (LinearMap.exact_subtype_mkQ (LinearMap.range f.formMap))
      (Submodule.mkQ_surjective _) (B.baseChange.symm w)).1 hx
    obtain ⟨z', rfl⟩ := LinearMap.lTensor_surjective D.L
      (LinearMap.range_eq_top.mp (LinearMap.range_rangeRestrict f.formMap)) z
    have hcomp : (LinearMap.range f.formMap).subtype ∘ₗ f.formMap.rangeRestrict = f.formMap :=
      LinearMap.ext fun _ => rfl
    rw [← LinearMap.lTensor_comp_apply, hcomp] at hz
    refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨A.baseChange z', ?_⟩
    rw [← f.baseChange_formMap, hz, LinearEquiv.apply_symm_apply]
  · intro y
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective D.L (Submodule.mkQ_surjective _) y
    exact ⟨Submodule.Quotient.mk (B.baseChange x), by
      rw [cokerψ_mk, LinearEquiv.symm_apply_apply]⟩

/-- **The base change of the cokernel**: `L_E ⊗_E (B_E / range f_E) ≅ B_{L_E} / range f`, by right
exactness of `L_E ⊗_E -`.  @census none (helper) -/
noncomputable def cokerBaseChange :
    (D.L ⊗[E] (B.form ⧸ LinearMap.range f.formMap)) ≃ₗ[D.L]
      (B.carrier ⧸ LinearMap.range f.toLinearMap) :=
  (LinearEquiv.ofBijective (cokerψ f) (cokerψ_bijective f)).symm

/-- The Galois action on the cokernel is the one induced by `B`'s.  @census none (helper) -/
theorem galActOf_cokerBaseChange (σ : D.L ≃ₐ[E] D.L) (w : B.carrier) :
    galActOf D (cokerBaseChange f) σ (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (B.galAct σ w) := by
  rw [galActOf_apply, cokerBaseChange, LinearEquiv.symm_symm, LinearEquiv.symm_apply_eq,
    LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, cokerψ_mk, cokerψ_mk,
    baseChange_symm_galAct, galoisTwist_lTensor]

/-- **The cokernel object** `coker f ∈ HC_λ(𝔤,K)_E`: the vector-space cokernel `B_{L_E} / range f`
with the induced weight data and Galois action, and `E`-form `B_E / range f_E`.
@census none (helper) -/
noncomputable def cokerObj : HC ℓ E D where
  form := B.form ⧸ LinearMap.range f.formMap
  carrier := B.carrier ⧸ LinearMap.range f.toLinearMap
  baseChange := cokerBaseChange f
  weight := B.weight.quot f.opStable_range f.isHomog_range
  gic := WeightData.gic_quot _ _ B.gic
  galCompat σ := (B.galCompat σ).quot _ _ _ (galActOf_cokerBaseChange f σ)
  admissible n := by
    haveI := B.admissible n
    have h1 : (B.weight.comp n).FG :=
      (Module.Finite.iff_fg (N := B.weight.comp n)).mp inferInstance
    exact (Module.Finite.iff_fg (N := (B.weight.quot f.opStable_range f.isHomog_range).comp n)).mpr
      (h1.map _)
  centralCharacter n hn := by
    rw [WeightData.quot_comp, B.centralCharacter n hn, Submodule.map_bot]
  fg := fg_quot B.fg _ _

theorem cokerObj_galAct (σ : D.L ≃ₐ[E] D.L) (w : B.carrier) :
    (cokerObj f).galAct σ (Submodule.Quotient.mk w) = Submodule.Quotient.mk (B.galAct σ w) :=
  galActOf_cokerBaseChange f σ w

/-- The projection `B ↠ coker f`.  @census none (helper) -/
noncomputable def cokernelπ : B ⟶ cokerObj f :=
  (⟨(LinearMap.range f.toLinearMap).mkQ, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ v hv => ⟨v, hv, rfl⟩, fun σ v => (cokerObj_galAct f σ v).symm⟩ : Hom B (cokerObj f))

theorem comp_cokernelπ : (f : A ⟶ B) ≫ cokernelπ f = 0 :=
  hom_ext fun v => (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩

/-- The vector-space cokernel satisfies the **universal property of the cokernel**.
@census none (helper) -/
noncomputable def cokernelIsColimit :
    Limits.IsColimit (Limits.CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)) := by
  haveI : Epi (cokernelπ f) := epi_of_surjective (Submodule.mkQ_surjective _)
  refine Limits.CokernelCofork.IsColimit.ofπ' (cokernelπ f) (comp_cokernelπ f)
    (fun {T} k hk => ?_)
  · have hle : LinearMap.range f.toLinearMap ≤ LinearMap.ker (k : Hom B T).toLinearMap := by
      rintro _ ⟨a, rfl⟩
      exact LinearMap.mem_ker.mpr (congrArg (fun z : A ⟶ T => (z : Hom A T).toLinearMap a) hk)
    refine ⟨(⟨(LinearMap.range f.toLinearMap).liftQ (k : Hom B T).toLinearMap hle,
      fun x => ?_, fun x => ?_, fun x => ?_, fun n x hx => ?_, fun σ x => ?_⟩ :
        Hom (cokerObj f) T), ?_⟩
    · obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (k : Hom B T).map_H b
    · obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (k : Hom B T).map_X b
    · obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (k : Hom B T).map_Y b
    · obtain ⟨b, hb, rfl⟩ := hx
      exact (k : Hom B T).map_comp n b hb
    · obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [cokerObj_galAct]
      exact (k : Hom B T).map_gal σ b
    · exact hom_ext fun _ => rfl

noncomputable instance : Limits.HasCokernels (HC ℓ E D) :=
  ⟨fun f => Limits.HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

end Cokernel

/-! ## 4. Binary products and the zero object -/

section Prod

variable (A B : HC ℓ E D)

theorem prodRight_galoisTwist (σ : D.L ≃ₐ[E] D.L) (z : D.L ⊗[E] (A.form × B.form)) :
    TensorProduct.prodRight E D.L D.L A.form B.form (galoisTwist σ z) =
      (galoisTwist σ (TensorProduct.prodRight E D.L D.L A.form B.form z).1,
        galoisTwist σ (TensorProduct.prodRight E D.L D.L A.form B.form z).2) := by
  induction z with
  | tmul a v => simp
  | add x y hx hy => simp only [map_add, hx, hy, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]

/-- `L_E ⊗_E (A_E × B_E) ≅ A_{L_E} × B_{L_E}`.  @census none (helper) -/
noncomputable def prodBaseChange :
    (D.L ⊗[E] (A.form × B.form)) ≃ₗ[D.L] (A.carrier × B.carrier) :=
  (TensorProduct.prodRight E D.L D.L A.form B.form).trans (A.baseChange.prodCongr B.baseChange)

theorem galActOf_prodBaseChange (σ : D.L ≃ₐ[E] D.L) (v : A.carrier × B.carrier) :
    galActOf D (prodBaseChange A B) σ v = (A.galAct σ v.1, B.galAct σ v.2) := by
  rw [galActOf_apply]
  simp only [prodBaseChange, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
    prodRight_galoisTwist, LinearEquiv.apply_symm_apply]
  rfl

/-- **The product object** `A × B`.  @census none (helper) -/
noncomputable def prodObj : HC ℓ E D where
  form := A.form × B.form
  carrier := A.carrier × B.carrier
  baseChange := prodBaseChange A B
  weight := WeightData.prodData A.weight B.weight
  gic := WeightData.gic_prodData A.gic B.gic
  galCompat σ := (A.galCompat σ).prod (B.galCompat σ) _ (galActOf_prodBaseChange A B σ)
  admissible n := by
    haveI := A.admissible n
    haveI := B.admissible n
    exact (Module.Finite.iff_fg (N := (WeightData.prodData A.weight B.weight).comp n)).mpr
      (((Module.Finite.iff_fg (N := A.weight.comp n)).mp inferInstance).prod
        ((Module.Finite.iff_fg (N := B.weight.comp n)).mp inferInstance))
  centralCharacter n hn := by
    rw [WeightData.prodData_comp, A.centralCharacter n hn, B.centralCharacter n hn,
      Submodule.prod_bot]
  fg := fg_prodData A.fg B.fg

theorem prodObj_galAct (σ : D.L ≃ₐ[E] D.L) (v : (prodObj A B).carrier) :
    (prodObj A B).galAct σ v = (A.galAct σ v.1, B.galAct σ v.2) :=
  galActOf_prodBaseChange A B σ v

/-- First projection.  @census none (helper) -/
noncomputable def prodFst : prodObj A B ⟶ A :=
  (⟨LinearMap.fst D.L A.carrier B.carrier, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ hv => hv.1, fun σ v => by rw [prodObj_galAct]; rfl⟩ : Hom (prodObj A B) A)

/-- Second projection.  @census none (helper) -/
noncomputable def prodSnd : prodObj A B ⟶ B :=
  (⟨LinearMap.snd D.L A.carrier B.carrier, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ hv => hv.2, fun σ v => by rw [prodObj_galAct]; rfl⟩ : Hom (prodObj A B) B)

variable {A B} in
/-- The universal map into the product.  @census none (helper) -/
noncomputable def prodLift {T : HC ℓ E D} (f : T ⟶ A) (g : T ⟶ B) : T ⟶ prodObj A B :=
  (⟨(f : Hom T A).toLinearMap.prod (g : Hom T B).toLinearMap,
    fun v => Prod.ext ((f : Hom T A).map_H v) ((g : Hom T B).map_H v),
    fun v => Prod.ext ((f : Hom T A).map_X v) ((g : Hom T B).map_X v),
    fun v => Prod.ext ((f : Hom T A).map_Y v) ((g : Hom T B).map_Y v),
    fun n v hv => ⟨(f : Hom T A).map_comp n v hv, (g : Hom T B).map_comp n v hv⟩,
    fun σ v => by
      rw [prodObj_galAct]
      exact Prod.ext ((f : Hom T A).map_gal σ v) ((g : Hom T B).map_gal σ v)⟩ :
    Hom T (prodObj A B))

/-- The product object is a binary product.  @census none (helper) -/
noncomputable def prodIsLimit :
    Limits.IsLimit (Limits.BinaryFan.mk (prodFst A B) (prodSnd A B)) :=
  Limits.BinaryFan.IsLimit.mk _ (fun f g => prodLift f g) (fun _ _ => hom_ext fun _ => rfl)
    (fun _ _ => hom_ext fun _ => rfl)
    (fun {T} _ _ _ h1 h2 => hom_ext fun v => Prod.ext
      (congrArg (fun t : T ⟶ A => (t : Hom T A).toLinearMap v) h1)
      (congrArg (fun t : T ⟶ B => (t : Hom T B).toLinearMap v) h2))

noncomputable instance : Limits.HasLimit (Limits.pair A B) :=
  Limits.HasLimit.mk ⟨_, prodIsLimit A B⟩

end Prod

noncomputable instance : Limits.HasBinaryProducts (HC ℓ E D) :=
  Limits.hasBinaryProducts_of_hasLimit_pair _

section Zero

instance : Subsingleton (D.L ⊗[E] PUnit.{1}) :=
  ⟨fun x y => by
    have h : ∀ z : D.L ⊗[E] PUnit.{1}, z = 0 := fun z => by
      induction z with
      | tmul a u => rw [Subsingleton.elim u 0, TensorProduct.tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    rw [h x, h y]⟩

variable (ℓ D) in
/-- **The zero object**.  @census none (helper) -/
noncomputable def zeroObj : HC ℓ E D where
  form := PUnit
  carrier := PUnit
  baseChange := LinearEquiv.ofSubsingleton _ _
  weight := trivialWeightData D.L PUnit
  gic := ⟨1, LinearMap.ext fun _ => Subsingleton.elim _ _⟩
  galCompat σ :=
    { comp := fun n v _ => by rw [Subsingleton.elim (galActOf D _ σ v) 0]; exact Submodule.zero_mem _
      H := fun _ => Subsingleton.elim _ _
      X_one := fun _ _ => Subsingleton.elim _ _
      Y_one := fun _ _ => Subsingleton.elim _ _
      X_neg := fun _ _ => Subsingleton.elim _ _
      Y_neg := fun _ _ => Subsingleton.elim _ _ }
  admissible _ := inferInstance
  centralCharacter _ _ := Submodule.eq_bot_of_subsingleton
  fg := ⟨∅, gkSpanOver_eq_top fun _ _ _ _ => Subsingleton.elim _ _⟩

variable (ℓ D) in
theorem isZero_zeroObj : Limits.IsZero (zeroObj D ℓ) := by
  haveI : Subsingleton (zeroObj D ℓ).carrier := inferInstanceAs (Subsingleton PUnit)
  constructor
  · intro Y
    refine ⟨⟨⟨0⟩, fun f => hom_ext fun v => ?_⟩⟩
    rw [Subsingleton.elim v 0, map_zero, map_zero]
  · intro Y
    exact ⟨⟨⟨0⟩, fun f => hom_ext fun v => Subsingleton.elim _ _⟩⟩

instance : Limits.HasZeroObject (HC ℓ E D) := ⟨⟨_, isZero_zeroObj D ℓ⟩⟩

end Zero

noncomputable instance : Limits.HasTerminal (HC ℓ E D) :=
  (isZero_zeroObj D ℓ).isTerminal.hasTerminal

noncomputable instance : Limits.HasFiniteProducts (HC ℓ E D) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-! ## 5. Monos and epis; every mono is a kernel, every epi a cokernel -/

section MonoEpi

variable {A B : HC ℓ E D}

/-- A mono has kernel `0`.  @census none (helper) -/
theorem injective_of_mono (f : A ⟶ B) [Mono f] : Function.Injective (f : Hom A B).toLinearMap := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  have h0 : kernelι (f : Hom A B) = 0 :=
    (cancel_mono f).mp (by rw [kernelι_comp, Limits.zero_comp])
  exact congrArg (fun t : kerObj (f : Hom A B) ⟶ A => (t : Hom _ A).toLinearMap ⟨v, hv⟩) h0

/-- An epi has cokernel `0`.  @census none (helper) -/
theorem surjective_of_epi (f : A ⟶ B) [Epi f] : Function.Surjective (f : Hom A B).toLinearMap := by
  have h0 : cokernelπ (f : Hom A B) = 0 :=
    (cancel_epi f).mp (by rw [comp_cokernelπ, Limits.comp_zero])
  intro b
  have hb : (Submodule.Quotient.mk b : B.carrier ⧸ LinearMap.range (f : Hom A B).toLinearMap) = 0 :=
    congrArg (fun t : B ⟶ cokerObj (f : Hom A B) => (t : Hom B _).toLinearMap b) h0
  exact (Submodule.Quotient.mk_eq_zero _).mp hb

/-- **Monomorphisms are inherited from vector spaces**: `f` is mono iff it is injective.
@census none (helper) -/
theorem mono_iff_injective (f : A ⟶ B) : Mono f ↔ Function.Injective (f : Hom A B).toLinearMap :=
  ⟨fun _ => injective_of_mono f, mono_of_injective⟩

/-- **Epimorphisms are inherited from vector spaces**: `f` is epi iff it is surjective.
@census none (helper) -/
theorem epi_iff_surjective (f : A ⟶ B) : Epi f ↔ Function.Surjective (f : Hom A B).toLinearMap :=
  ⟨fun _ => surjective_of_epi f, epi_of_surjective⟩

/-- The author's form: `f` is mono iff its kernel is `0`.  @census none (helper) -/
theorem mono_iff_ker_eq_bot (f : A ⟶ B) : Mono f ↔ LinearMap.ker (f : Hom A B).toLinearMap = ⊥ := by
  rw [mono_iff_injective, LinearMap.ker_eq_bot]

/-- The author's form: `f` is epi iff its cokernel is `0`.  @census none (helper) -/
theorem epi_iff_range_eq_top (f : A ⟶ B) :
    Epi f ↔ LinearMap.range (f : Hom A B).toLinearMap = ⊤ := by
  rw [epi_iff_surjective, LinearMap.range_eq_top]

/-- A mono is the kernel of its cokernel.  @census none (helper) -/
@[implicit_reducible]
noncomputable def normalMonoOfMono (f : A ⟶ B) [Mono f] : NormalMono f where
  Z := cokerObj (f : Hom A B)
  g := cokernelπ (f : Hom A B)
  w := comp_cokernelπ (f : Hom A B)
  isLimit := by
    refine Limits.KernelFork.IsLimit.ofι' f (comp_cokernelπ (f : Hom A B)) (fun {T} k hk => ?_)
    have hinj := injective_of_mono f
    have hmem : ∀ t, (k : Hom T B).toLinearMap t ∈ LinearMap.range (f : Hom A B).toLinearMap :=
      fun t => (Submodule.Quotient.mk_eq_zero _).mp
        (congrArg (fun z : T ⟶ cokerObj (f : Hom A B) => (z : Hom T _).toLinearMap t) hk)
    set e := LinearEquiv.ofInjective (f : Hom A B).toLinearMap hinj
    set l0 : T.carrier →ₗ[D.L] A.carrier :=
      e.symm.toLinearMap ∘ₗ LinearMap.codRestrict _ (k : Hom T B).toLinearMap hmem with hl0
    have hl : ∀ t, (f : Hom A B).toLinearMap (l0 t) = (k : Hom T B).toLinearMap t := by
      intro t
      have h1 : e (l0 t) = (⟨(k : Hom T B).toLinearMap t, hmem t⟩ :
          LinearMap.range (f : Hom A B).toLinearMap) := by
        rw [hl0]
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply]
        rfl
      exact congrArg Subtype.val h1
    exact ⟨Hom.ofInjectiveComp (f : Hom A B) hinj k l0 hl, hom_ext hl⟩

/-- An epi is the cokernel of its kernel.  @census none (helper) -/
@[implicit_reducible]
noncomputable def normalEpiOfEpi (f : A ⟶ B) [Epi f] : NormalEpi f where
  W := kerObj (f : Hom A B)
  g := kernelι (f : Hom A B)
  w := kernelι_comp (f : Hom A B)
  isColimit := by
    refine Limits.CokernelCofork.IsColimit.ofπ' f (kernelι_comp (f : Hom A B)) (fun {T} k hk => ?_)
    have hsurj := surjective_of_epi f
    have hle : LinearMap.ker (f : Hom A B).toLinearMap ≤ LinearMap.ker (k : Hom A T).toLinearMap :=
      fun v hv => LinearMap.mem_ker.mpr
        (congrArg (fun z : kerObj (f : Hom A B) ⟶ T => (z : Hom _ T).toLinearMap ⟨v, hv⟩) hk)
    set e := LinearMap.quotKerEquivOfSurjective (f : Hom A B).toLinearMap hsurj with he
    set l0 : B.carrier →ₗ[D.L] T.carrier :=
      ((LinearMap.ker (f : Hom A B).toLinearMap).liftQ (k : Hom A T).toLinearMap hle) ∘ₗ
        e.symm.toLinearMap with hl0
    have hl : ∀ a, l0 ((f : Hom A B).toLinearMap a) = (k : Hom A T).toLinearMap a := by
      intro a
      have h1 : e.symm ((f : Hom A B).toLinearMap a) = (Submodule.Quotient.mk a : _ ⧸ _) := by
        rw [LinearEquiv.symm_apply_eq, he]
        exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ hsurj a).symm
      rw [hl0]
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, h1]
      exact Submodule.liftQ_apply _ _ _
    exact ⟨Hom.ofCompSurjective (f : Hom A B) hsurj k l0 hl, hom_ext hl⟩

instance : IsNormalMonoCategory (HC ℓ E D) where
  normalMonoOfMono f := ⟨normalMonoOfMono f⟩

instance : IsNormalEpiCategory (HC ℓ E D) where
  normalEpiOfEpi f := ⟨normalEpiOfEpi f⟩

end MonoEpi

/-! ## The abelian structure -/

/-- The `Abelian` structure on `HC_λ(𝔤,K)_E`, assembled from the pieces above.
@census none (helper) -/
@[implicit_reducible]
noncomputable def abelianStr : Abelian (HC ℓ E D) where

/-- **`HC_λ(𝔤,K)_E` is an abelian category**, for every field `E` of characteristic `0`, every
`ℓ` and every `D : ImagUnit E` (both `√-1 ∈ E` and `√-1 ∉ E`).

The author's argument (`AUTHOR-QUEUE` `T1-A`, 2026-10-17): the vector-space kernel and cokernel of
a morphism carry canonical structures (`kerObj`, `cokerObj`: weight data, Galois action and
`E`-form all induced) and satisfy the universal properties (`kernelIsLimit`,
`cokernelIsColimit`); monomorphisms and epimorphisms are those of vector spaces
(`mono_iff_ker_eq_bot`, `epi_iff_range_eq_top`).

Stated as `Nonempty (Abelian …)` as for `harishChandraCat_abelian`: `Abelian` is a class carrying
data, and `Nonempty` of it is the `Prop` that the structure exists.

@census    none (auxiliary; discharges the "abelian categories" clauses RQ2-0.01-C5, RQ2-0.02-C3 for
  the category side `HC_λ(𝔤,K)_E`)
@source    def:HClambdaE
@imports   none
@divergence none
-/
theorem abelian : Nonempty (Abelian (HC ℓ E D)) := ⟨abelianStr⟩

end HC

end RationalQuivers.HC
