module

public import RationalQuivers.HC.Category

@[expose] public section

/-!
# `HC_λ(𝔤,K)_ℂ` and the classical Harish-Chandra modules (`rmk:HClambdaC`)

Formalizes `rmk:HClambdaC` (census `RQ2-3.15`, stage T4, WP-11c): for `E = ℂ` we have `L_ℂ = ℂ`,
and `def:HClambdaE` gives the full subcategory `HC_λ(𝔤,K)_ℂ` of the category `HC(𝔤,K)` of
Harish-Chandra modules over `ℂ` of `def:hcmodule` (`RQ2-3.11`), cut out by the generalized
infinitesimal character and the central character.

## Contents, in order

1. **The weights determine the `SO(2,ℝ)`-action.**  For a `WeightData ℂ M`, `repOf W` is the
   representation `g ↦ χ_n(g)` on `M_n`; it satisfies the isotypy and differential conditions of
   `HarishChandraModule` (`repOf_isotypic`, `WeightData.differential_of_chiChar`), and every
   Harish-Chandra module's own action is it (`rep_eq_repOf`).
2. **Finite generation and the central character** on both sides: `gkSpan` with the `K`-action
   against `gkSpanOver` with the grading (`gkSpanOver_eq_top_of_hc`, `gkSpan_eq_top_of_gkSpanOver`),
   and `-1₂` acting by `(-1)^{ℓ-1}` against the parity cut `HC.parity` (`parity_of_centralCharacter`,
   `centralCharacter_of_parity`).
3. **The forgetful functor** `forgetRep ℓ : HC.Category ℓ ⥤ HCLambda ℓ ℂ` (forget the
   `SO(2,ℝ)`-action, keep the weights and the triple), **fully faithful**
   (`forgetRep_fullyFaithful`) and essentially surjective, hence the core equivalence
   `hcLambdaComplexEquiv ℓ : HCLambda ℓ ℂ ≌ HC.Category ℓ` whose inverse **is** `forgetRep ℓ`.
4. **The claimant** `hcLambda_complex_equiv ℓ : HC ℓ ℂ ImagUnit.complex ≌ HC.Category ℓ`,
   composing with T1's `HC.lambdaEquiv` (`√-1 ∈ ℂ`); `L_complex` is `L_ℂ = ℂ`; and the composite
   `toHCObj ℓ : HC ℓ ℂ ImagUnit.complex ⥤ HCObj` is fully faithful with essential image the objects
   with generalized infinitesimal character `λ = ℓ²` and central character `(-1)^{ℓ-1}`.
-/

namespace RationalQuivers.HC.ClassicalComparison

open CategoryTheory

/-! ## The weights determine the `SO(2,ℝ)`-action -/

section Rep

variable {M : Type} [AddCommGroup M] [Module ℂ M]

/-- Two linear maps out of a weight module that agree on every `M_n` agree.

@census none (helper) -/
theorem linearMap_ext_of_comp {N : Type} [AddCommGroup N] [Module ℂ N] (W : WeightData ℂ M)
    {f g : M →ₗ[ℂ] N} (h : ∀ (n : ℤ) (v : M), v ∈ W.comp n → f v = g v) : f = g := by
  ext v
  obtain ⟨s, -, hsum⟩ := W.exists_sum_proj v
  rw [← hsum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun n _ => h n _ (W.proj_mem n v)

/-- `M ≃ ⨁_n M_n` sends a vector of `M_n` to the corresponding summand.

@census none (helper) -/
theorem decompEquiv_of_mem (W : WeightData ℂ M) {n : ℤ} {v : M} (hv : v ∈ W.comp n) :
    W.decompEquiv v = DirectSum.lof ℂ ℤ (fun m => W.comp m) n ⟨v, hv⟩ := by
  rw [WeightData.decompEquiv, LinearEquiv.symm_apply_eq]
  simp only [DirectSum.lof_eq_of]
  exact (DirectSum.coeLinearMap_of (fun m => W.comp m) n ⟨v, hv⟩).symm

/-- The operator `g ↦ χ_n(g)` on `M_n`, assembled along `M = ⨁_n M_n`.

@census none (helper) -/
noncomputable def chiEnd (W : WeightData ℂ M) (g : SO2_QStructure ℝ) : Module.End ℂ M :=
  (DirectSum.toModule ℂ ℤ M fun n => chiChar n g • (W.comp n).subtype) ∘ₗ
    W.decompEquiv.toLinearMap

theorem chiEnd_apply_of_mem (W : WeightData ℂ M) (g : SO2_QStructure ℝ) {n : ℤ} {v : M}
    (hv : v ∈ W.comp n) : chiEnd W g v = chiChar n g • v := by
  simp [chiEnd, decompEquiv_of_mem W hv, DirectSum.toModule_lof]

/-- **The `SO(2,ℝ)`-action rebuilt from the weights**: `g` acts on `M_n` by `χ_n(g)`.

@census none (helper) -/
noncomputable def repOf (W : WeightData ℂ M) : Representation ℂ (SO2_QStructure ℝ) M where
  toFun := chiEnd W
  map_one' := linearMap_ext_of_comp W fun n v hv => by
    rw [chiEnd_apply_of_mem W 1 hv, chiChar_one, one_smul]; rfl
  map_mul' g h := linearMap_ext_of_comp W fun n v hv => by
    rw [chiEnd_apply_of_mem W (g * h) hv, Module.End.mul_apply, chiEnd_apply_of_mem W h hv,
      map_smul, chiEnd_apply_of_mem W g hv, chiChar_mul, mul_comm, mul_smul]

theorem repOf_apply_of_mem (W : WeightData ℂ M) (g : SO2_QStructure ℝ) {n : ℤ} {v : M}
    (hv : v ∈ W.comp n) : repOf W g v = chiChar n g • v :=
  chiEnd_apply_of_mem W g hv

/-- `M_n` **is** the `χ_n`-isotypic component of the rebuilt action (`isotypic_of_forward`).

@census none (helper) -/
theorem repOf_isotypic (W : WeightData ℂ M) (n : ℤ) (v : M) :
    v ∈ W.comp n ↔ ∀ g, repOf W g v = chiChar n g • v :=
  ⟨fun hv g => repOf_apply_of_mem W g hv,
    isotypic_of_forward (repOf W) (fun _ _ hv g => repOf_apply_of_mem W g hv) n v⟩

/-- **The weights determine the action**: the `SO(2,ℝ)`-action of a Harish-Chandra module is the
one rebuilt from its weight decomposition.

@census none (helper) -/
theorem rep_eq_repOf (Hm : HarishChandraModule M) :
    Hm.rep = repOf Hm.weight := by
  ext g v
  exact congrArg (· v) (linearMap_ext_of_comp Hm.weight (f := Hm.rep g) (g := repOf Hm.weight g)
    fun n w hw => by rw [(Hm.isotypic' n w).mp hw g, repOf_apply_of_mem _ g hw])

/-- A linear map commuting with `H` intertwines the rebuilt actions: it preserves the weight
spaces (`WeightData.map_comp_of_map_H`), on which both actions are the scalars `χ_n(g)`.

@census none (helper) -/
theorem map_rep_of_map_H {N : Type} [AddCommGroup N] [Module ℂ N] {W : WeightData ℂ M}
    {V : WeightData ℂ N} {rW : Representation ℂ (SO2_QStructure ℝ) M}
    {rV : Representation ℂ (SO2_QStructure ℝ) N}
    (hW : ∀ (n : ℤ) (v : M), v ∈ W.comp n → ∀ g, rW g v = chiChar n g • v)
    (hV : ∀ (n : ℤ) (v : N), v ∈ V.comp n → ∀ g, rV g v = chiChar n g • v)
    (f : M →ₗ[ℂ] N) (hf : ∀ v, f (W.H v) = V.H (f v)) (g : SO2_QStructure ℝ) (v : M) :
    f (rW g v) = rV g (f v) := by
  have := linearMap_ext_of_comp W (f := f ∘ₗ (rW g : Module.End ℂ M))
    (g := (rV g : Module.End ℂ N) ∘ₗ f) fun n w hw => by
      simp only [LinearMap.comp_apply]
      rw [hW n w hw g, map_smul, hV n _ (WeightData.map_comp_of_map_H W V f hf n w hw) g]
  exact congrArg (· v) this

end Rep

/-! ## Finite generation and the central character on both sides -/

section Conditions

variable {M : Type} [AddCommGroup M] [Module ℂ M]

/-- `proj_n ∘ f = f ∘ proj_{n-k}` for an operator `f` shifting the grading by `k` (`k = ±2` for
`X`, `Y`).

@census none (helper) -/
theorem proj_shift (W : WeightData ℂ M) (f : Module.End ℂ M) (k : ℤ)
    (hf : ∀ (m : ℤ) (v : M), v ∈ W.comp m → f v ∈ W.comp (m + k)) (n : ℤ) (v : M) :
    W.proj n (f v) = f (W.proj (n - k) v) := by
  obtain ⟨s, hzero, hsum⟩ := W.exists_sum_proj v
  have h1 : f v = ∑ m ∈ s, f (W.proj m v) := by
    conv_lhs => rw [← hsum]
    rw [map_sum]
  rw [h1, map_sum, Finset.sum_eq_single (n - k)
    (fun m _ hmn => W.proj_of_mem_ne (hf m _ (W.proj_mem m v)) (by omega))
    (fun hn => by rw [hzero _ hn, map_zero, map_zero])]
  have := W.proj_of_mem_same (hf (n - k) _ (W.proj_mem (n - k) v))
  rwa [sub_add_cancel] at this

/-- The largest homogeneous submodule `⨁_n (N ∩ M_n)` of a submodule `N`.

@census none (helper) -/
noncomputable def homogCore (W : WeightData ℂ M) (N : Submodule ℂ M) : Submodule ℂ M where
  carrier := {v | ∀ n, W.proj n v ∈ N}
  add_mem' ha hb n := by rw [map_add]; exact N.add_mem (ha n) (hb n)
  zero_mem' n := by rw [map_zero]; exact N.zero_mem
  smul_mem' c v hv n := by rw [map_smul]; exact N.smul_mem c (hv n)

theorem homogCore_le (W : WeightData ℂ M) (N : Submodule ℂ M) : homogCore W N ≤ N := by
  intro v hv
  obtain ⟨s, -, hsum⟩ := W.exists_sum_proj v
  rw [← hsum]
  exact sum_mem fun n _ => hv n

theorem mem_homogCore_of_mem_comp (W : WeightData ℂ M) {N : Submodule ℂ M} {m : ℤ} {v : M}
    (hv : v ∈ W.comp m) (hN : v ∈ N) : v ∈ homogCore W N := by
  intro n
  by_cases h : m = n
  · subst h; rwa [W.proj_of_mem_same hv]
  · rw [W.proj_of_mem_ne hv h]; exact N.zero_mem

theorem isHomog_homogCore (W : WeightData ℂ M) (N : Submodule ℂ M) :
    W.IsHomog (homogCore W N) :=
  fun n v hv => mem_homogCore_of_mem_comp W (W.proj_mem n v) (hv n)

theorem opStable_homogCore (W : WeightData ℂ M) {N : Submodule ℂ M}
    (hH : ∀ v ∈ N, W.H v ∈ N) (hX : ∀ v ∈ N, W.X v ∈ N) (hY : ∀ v ∈ N, W.Y v ∈ N) :
    W.OpStable (homogCore W N) := by
  refine ⟨fun v hv n => ?_, fun v hv n => ?_, fun v hv n => ?_⟩
  · rw [W.proj_comm_of_graded W.H (WeightData.H_graded W)]; exact hH _ (hv n)
  · rw [proj_shift W W.X 2 W.X_mem]; exact hX _ (hv _)
  · rw [proj_shift W W.Y (-2) (fun m v hv => by simpa [sub_eq_add_neg] using W.Y_mem m v hv)]
    exact hY _ (hv _)

/-- `RQ2-3.11-C1` ⇒ `HCObjOver.fg`: a homogeneous `H,X,Y`-stable submodule is `K`-stable
(`rep_mem_of_isHomog`).

@census none (helper) -/
theorem gkSpanOver_eq_top_of_hc (Hm : HarishChandraModule M) {S : Finset M}
    (hS : gkSpan {Hm.weight.H, Hm.weight.X, Hm.weight.Y}
      (Set.range fun g => (Hm.rep g : Module.End ℂ M)) ↑S = ⊤) :
    gkSpanOver Hm.weight (↑S : Set M) = ⊤ :=
  le_antisymm le_top <| le_sInf fun N ⟨hSN, hst, hhom⟩ =>
    (eq_top_of_gkSpan_eq_top hS hSN (opStable_iff_forall_mem.mp hst)
      (by rintro _ ⟨g, rfl⟩ v hv; exact Hm.rep_mem_of_isHomog hhom g v hv)) ▸ le_rfl

/-- `HCObjOver.fg` ⇒ `RQ2-3.11-C1`, for any `K`-action: generated by the homogeneous components
`T` of the generators, since a `(𝔤,K)`-stable `N ⊇ T` contains the homogeneous `(𝔤,K)`-stable
`homogCore W N ⊇ T`, which is everything.

@census none (helper) -/
theorem gkSpan_eq_top_of_gkSpanOver (W : WeightData ℂ M)
    (rep : Representation ℂ (SO2_QStructure ℝ) M) {S : Finset M}
    (hS : gkSpanOver W (↑S : Set M) = ⊤) :
    ∃ T : Finset M, gkSpan {W.H, W.X, W.Y} (Set.range fun g => (rep g : Module.End ℂ M)) ↑T = ⊤ := by
  classical
  choose sup hzero hsum using W.exists_sum_proj
  refine ⟨S.biUnion (fun s => (sup s).image (fun n => W.proj n s)), gkSpan_eq_top ?_⟩
  intro N hTN hops _
  have hH : ∀ v ∈ N, W.H v ∈ N := hops _ (by simp)
  have hX : ∀ v ∈ N, W.X v ∈ N := hops _ (by simp)
  have hY : ∀ v ∈ N, W.Y v ∈ N := hops _ (by simp)
  have hcore : homogCore W N = ⊤ := by
    refine top_le_iff.mp (hS ▸ sInf_le ⟨?_, opStable_homogCore W hH hX hY, isHomog_homogCore W N⟩)
    intro s hs
    show s ∈ homogCore W N
    rw [← hsum s]
    refine sum_mem fun n hn => mem_homogCore_of_mem_comp W (W.proj_mem n s) (hTN ?_)
    simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.coe_image,
      Set.mem_image, exists_prop]
    exact ⟨s, hs, n, hn, rfl⟩
  exact top_le_iff.mp (hcore ▸ homogCore_le W N)

/-- `χ_n(-1₂) = (-1)^n`.

@census none (helper) -/
theorem chiChar_minusOnePt (n : ℤ) : chiChar n (minusOnePt ℝ) = (-1 : ℂ) ^ n := by
  simp [chiChar, minusOnePt]

/-- `(-1)^n = (-1)^{ℓ-1}` if `n ≡ ℓ - 1 (mod 2)`, and `= -(-1)^{ℓ-1}` otherwise.

@census none (helper) -/
theorem neg_one_zpow_eq (n : ℤ) (ℓ : ℕ) :
    (-1 : ℂ) ^ n = (-1 : ℂ) ^ (n - ((ℓ : ℤ) - 1)) * (-1 : ℂ) ^ ((ℓ : ℤ) - 1) := by
  rw [← zpow_add₀ (neg_ne_zero.mpr one_ne_zero), sub_add_cancel]

/-- The central character `-1₂ ↦ (-1)^{ℓ-1}` ⇒ the parity cut `M_n = 0` for `n ≢ ℓ - 1`.

@census none (helper) -/
theorem parity_of_centralCharacter (Hm : HarishChandraModule M) {ℓ : ℕ}
    (h : Hm.centralCharacter ℓ) (n : ℤ) (hn : (n - ((ℓ : ℤ) - 1)) % 2 ≠ 0) :
    Hm.weight.comp n = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  have hodd : Odd (n - ((ℓ : ℤ) - 1)) := Int.odd_iff.mpr (by omega)
  have h1 := h v
  rw [(Hm.isotypic' n v).mp hv, chiChar_minusOnePt, neg_one_zpow_eq n ℓ, hodd.neg_one_zpow,
    neg_one_mul, neg_smul, neg_eq_iff_add_eq_zero, ← add_smul] at h1
  refine (smul_eq_zero.mp h1).resolve_left ?_
  rw [← two_mul]
  exact mul_ne_zero two_ne_zero (zpow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

/-- The parity cut ⇒ `-1₂` acts by `(-1)^{ℓ-1}`, for any action that is `χ_n` on `M_n`.

@census none (helper) -/
theorem centralCharacter_of_parity {W : WeightData ℂ M} {rep : Representation ℂ (SO2_QStructure ℝ) M}
    (hrep : ∀ (n : ℤ) (v : M), v ∈ W.comp n → ∀ g, rep g v = chiChar n g • v) {ℓ : ℕ}
    (h : ∀ n : ℤ, (n - ((ℓ : ℤ) - 1)) % 2 ≠ 0 → W.comp n = ⊥) (v : M) :
    rep (minusOnePt ℝ) v = ((-1 : ℂ) ^ ((ℓ : ℤ) - 1)) • v := by
  have := linearMap_ext_of_comp W (f := (rep (minusOnePt ℝ) : Module.End ℂ M))
    (g := ((-1 : ℂ) ^ ((ℓ : ℤ) - 1)) • LinearMap.id) fun n w hw => by
      rw [hrep n w hw, chiChar_minusOnePt, LinearMap.smul_apply, LinearMap.id_apply]
      by_cases hn : (n - ((ℓ : ℤ) - 1)) % 2 = 0
      · rw [neg_one_zpow_eq n ℓ, (Int.even_iff.mpr hn).neg_one_zpow, one_mul]
      · rw [h n hn, Submodule.mem_bot] at hw
        rw [hw, smul_zero, smul_zero]
  exact congrArg (· v) this

end Conditions

/-! ## The forgetful functor `HC.Category ℓ ⥤ HCLambda ℓ ℂ` -/

variable (ℓ : ℕ)

/-- The property cutting `HC.Category ℓ` out of `HCObj` (`RQ2-3.03`'s classical clauses `C2`,
`C3`): generalized infinitesimal character `λ = ℓ²` and central character `(-1)^{ℓ-1}`.
`HC.Category ℓ` is its full subcategory by definition.

@census none (helper) -/
abbrev classicalProp : ObjectProperty HCObj.{0} := fun A =>
  HasGeneralizedInfinitesimalCharacter A.str.weight ℓ ∧ A.str.centralCharacter ℓ

example : HC.Category.{0} ℓ = (classicalProp ℓ).FullSubcategory := rfl

variable {ℓ}

/-- The object of `HCLambda ℓ ℂ` underlying an object of `HC.Category ℓ`: forget the
`SO(2,ℝ)`-action, keep the weights and the triple.

@census none (helper) -/
noncomputable def forgetObj (A : (classicalProp ℓ).FullSubcategory) : HCLambda.{0} ℓ ℂ :=
  ⟨{ carrier := A.obj.carrier
     weight := A.obj.str.weight
     gic := A.property.1
     fg := by
       obtain ⟨S, hS⟩ := A.obj.str.fg
       exact ⟨S, gkSpanOver_eq_top_of_hc A.obj.str hS⟩
     admissible := A.obj.str.admissible },
    parity_of_centralCharacter A.obj.str A.property.2⟩

/-- The Harish-Chandra module rebuilt from an object of `HCLambda ℓ ℂ`: the weights, the triple,
and the action `repOf` (`g ↦ χ_n(g)` on `M_n`).

@census none (helper) -/
noncomputable def hcOfLambda (B : HCLambda.{0} ℓ ℂ) : HarishChandraModule B.obj.carrier where
  weight := B.obj.weight
  rep := repOf B.obj.weight
  isotypic := repOf_isotypic B.obj.weight
  differential n v hv := B.obj.weight.differential_of_chiChar n v hv
  fg := by
    obtain ⟨S, hS⟩ := B.obj.fg
    exact gkSpan_eq_top_of_gkSpanOver B.obj.weight _ hS
  admissible := B.obj.admissible

/-- The object of `HC.Category ℓ` rebuilt from an object of `HCLambda ℓ ℂ`.

@census none (helper) -/
noncomputable def ofLambdaObj (B : HCLambda.{0} ℓ ℂ) : HC.Category.{0} ℓ :=
  (⟨⟨B.obj.carrier, hcOfLambda B⟩,
    B.obj.gic, centralCharacter_of_parity (fun _ _ hv g => repOf_apply_of_mem _ g hv) B.property⟩ :
    (classicalProp ℓ).FullSubcategory)

variable (ℓ) in
/-- **The forgetful functor** `HC.Category ℓ ⥤ HCLambda ℓ ℂ`: forget the `SO(2,ℝ)`-action, keep
the weight decomposition and the triple.  On morphisms it forgets `map_rep`.

@census none (helper) -/
noncomputable def forgetRep : HC.Category.{0} ℓ ⥤ HCLambda.{0} ℓ ℂ where
  obj A := forgetObj A
  map f := ObjectProperty.homMk
    ⟨f.hom.toLinearMap, f.hom.map_H, f.hom.map_X, f.hom.map_Y⟩
  map_id _ := rfl
  map_comp _ _ := rfl

theorem forgetRep_faithful : (forgetRep ℓ).Faithful where
  map_injective {A B} f g h := by
    apply ObjectProperty.hom_ext
    exact HCHom.hom_ext (congrArg (fun k => k.hom.toLinearMap) h)

/-- `forgetRep` is **full**: a map commuting with `H, X, Y` commutes with the `SO(2,ℝ)`-actions
(`map_rep_of_map_H`).

@census none (helper) -/
theorem forgetRep_full : (forgetRep ℓ).Full where
  map_surjective {A B} g := by
    refine ⟨ObjectProperty.homMk ⟨g.hom.toLinearMap, g.hom.map_H, g.hom.map_X, g.hom.map_Y,
      map_rep_of_map_H (fun n v hv => (A.obj.str.isotypic' n v).mp hv)
        (fun n v hv => (B.obj.str.isotypic' n v).mp hv) g.hom.toLinearMap g.hom.map_H⟩, rfl⟩

theorem forgetRep_essSurj : (forgetRep ℓ).EssSurj where
  mem_essImage B := ⟨ofLambdaObj B, ⟨Iso.refl _⟩⟩

variable (ℓ) in
/-- **`forgetRep` is fully faithful** — `HC.Category ℓ` is a full subcategory of `HCLambda ℓ ℂ`
along a named functor, not merely equivalent to one.

@census none (helper) -/
noncomputable def forgetRep_fullyFaithful : (forgetRep ℓ).FullyFaithful :=
  haveI := forgetRep_full (ℓ := ℓ)
  haveI := forgetRep_faithful (ℓ := ℓ)
  Functor.FullyFaithful.ofFullyFaithful _

variable (ℓ) in
/-- **The core comparison** `HCLambda ℓ ℂ ≌ HC.Category ℓ`, the inverse of the forgetful functor.

@census none (helper; the core of `RQ2-3.15`) -/
noncomputable def hcLambdaComplexEquiv : HCLambda.{0} ℓ ℂ ≌ HC.Category.{0} ℓ :=
  haveI := forgetRep_full (ℓ := ℓ)
  haveI := forgetRep_faithful (ℓ := ℓ)
  haveI := forgetRep_essSurj (ℓ := ℓ)
  haveI : (forgetRep ℓ).IsEquivalence := { }
  (forgetRep ℓ).asEquivalence.symm

theorem hcLambdaComplexEquiv_inverse : (hcLambdaComplexEquiv ℓ).inverse = forgetRep ℓ := rfl

/-! ## The claimant -/

/-- `RQ2-3.15-C1`: `L_ℂ = ℂ`.  @census none (helper) -/
theorem L_complex : ImagUnit.complex.L = ℂ := rfl

/-- `√-1 ∈ ℂ`.  @census none (helper) -/
theorem complex_sqrt : ∃ a : ℂ, a * a = -1 := ⟨Complex.I, Complex.I_mul_I⟩

variable (ℓ) in
/-- The comparison functor `HC.Category ℓ ⥤ HC ℓ ℂ ImagUnit.complex`: `forgetRep` followed by the
`|G_ℂ| = 1` identification of T1.

@census none (helper) -/
noncomputable def toComplexHC : HC.Category.{0} ℓ ⥤ HC ℓ ℂ ImagUnit.complex :=
  forgetRep ℓ ⋙ (HC.lambdaEquiv (D := ImagUnit.complex) (ℓ := ℓ) complex_sqrt).inverse

/-- **Remark** (`rmk:HClambdaC`).  For `E = ℂ` we have `L_ℂ = ℂ` (`L_complex`), and the category
`HC_λ(𝔤,K)_ℂ` of `def:HClambdaE` (`HC ℓ ℂ ImagUnit.complex`) **is** the full subcategory
`HC.Category ℓ` of the category `HCObj` of Harish-Chandra modules over `ℂ` of `def:hcmodule`, cut
out by the generalized infinitesimal character `λ = ℓ²` and the central character `(-1)^{ℓ-1}`.

Rendered as an equivalence of categories whose inverse is the **named** functor `toComplexHC ℓ`
(`hcLambda_complex_equiv_inverse`), the composite of the fully faithful forgetful functor
`forgetRep ℓ` (`forgetRep_fullyFaithful`) and T1's `HC.lambdaEquiv`; the passage to `HCObj` is
`toHCObj ℓ`, fully faithful (`toHCObj_fullyFaithful`) with essential image exactly the objects with
those two characters (`toHCObj_obj_mem`, `mem_essImage_toHCObj`).

@census    RQ2-3.15
@source    rmk:HClambdaC
@clauses   RQ2-3.15-H1, RQ2-3.15-C1, RQ2-3.15-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION (presentation; the census `notes` of `C2`: an equivalence of
categories is the expected rendering).  `H1` is
the instance `E = ℂ`, `D = ImagUnit.complex`.  `C1` is `L_complex` (`rfl`).  `C2` "is the full
subcategory" is rendered as an equivalence `HC ℓ ℂ ImagUnit.complex ≌ HC.Category ℓ` whose inverse
is a named functor, together with the fully faithful `toHCObj ℓ` into `HCObj` with essential image
the cut; it is not an equality of categories, since `def:HClambdaE`'s objects (descent
presentation, `EX-HC`) and `def:hcmodule`'s objects (an explicit `SO(2,ℝ)`-action) are different
data; a fully faithful functor whose essential image is exactly the cut is the categorical content of
"is the full subcategory".  The `SO(2,ℝ)`-action is recovered from the weights (`repOf`,
`rep_eq_repOf`).  Universe `0`.
-/
noncomputable def hcLambda_complex_equiv : HC ℓ ℂ ImagUnit.complex ≌ HC.Category.{0} ℓ :=
  (HC.lambdaEquiv (D := ImagUnit.complex) (ℓ := ℓ) complex_sqrt).trans (hcLambdaComplexEquiv ℓ)

theorem hcLambda_complex_equiv_inverse :
    (hcLambda_complex_equiv (ℓ := ℓ)).inverse = toComplexHC ℓ := rfl

variable (ℓ) in
/-- `HC_λ(𝔤,K)_ℂ ⥤ HC(𝔤,K)`: the claimant followed by the inclusion of the full subcategory.

@census none (helper) -/
noncomputable def toHCObj : HC ℓ ℂ ImagUnit.complex ⥤ HCObj.{0} :=
  (hcLambda_complex_equiv (ℓ := ℓ)).functor ⋙ (classicalProp ℓ).ι

variable (ℓ) in
/-- `toHCObj ℓ` is fully faithful.  @census none (helper) -/
noncomputable def toHCObj_fullyFaithful : (toHCObj ℓ).FullyFaithful :=
  (hcLambda_complex_equiv (ℓ := ℓ)).fullyFaithfulFunctor.comp
    (classicalProp ℓ).fullyFaithfulι

/-- Every object in the image of `toHCObj ℓ` has generalized infinitesimal character `λ = ℓ²` and
central character `(-1)^{ℓ-1}`.  @census none (helper) -/
theorem toHCObj_obj_mem (X : HC ℓ ℂ ImagUnit.complex) : classicalProp ℓ ((toHCObj ℓ).obj X) :=
  ((hcLambda_complex_equiv (ℓ := ℓ)).functor.obj X : (classicalProp ℓ).FullSubcategory).property

/-- Every Harish-Chandra module with generalized infinitesimal character `λ = ℓ²` and central
character `(-1)^{ℓ-1}` is in the essential image of `toHCObj ℓ`.  @census none (helper) -/
theorem mem_essImage_toHCObj (A : HCObj.{0}) (hA : classicalProp ℓ A) :
    (toHCObj ℓ).essImage A := by
  obtain ⟨X, ⟨e⟩⟩ := (hcLambda_complex_equiv (ℓ := ℓ)).essSurj_functor.mem_essImage
    (⟨A, hA⟩ : (classicalProp ℓ).FullSubcategory)
  exact ⟨X, ⟨(classicalProp ℓ).ι.mapIso e⟩⟩

end RationalQuivers.HC.ClassicalComparison
