import RationalQuivers.HC.Sl2

/-!
# Homogeneous components of a `WeightData`, and its sub- and quotient objects

Infrastructure for `§3.3`'s clause `RQ-3.11-C4` (`HC(𝔤,K)` is abelian, `HC/Module.lean`).  A
`WeightData E M` (`HC/Sl2.lean`) carries the internal direct sum `M = ⨁_{n ∈ ℤ} M_n` as the field
`isInternal`; everything the abelian-category construction needs about that decomposition is
collected here, on `WeightData` alone — no `SO(2)`-action, no finiteness — so that this module sits
*upstream* of `HC/Module.lean`, where `RQ-3.11`'s frozen statement lives.

*(2026-10-21, O-V2-6 round 2.)*  v2 WP-8 (`d2a2a47`, 2026-10-17) renamed `HC/Module.lean` to
`HC/Classical.lean`; `RQ-3.11`'s statement is there as census `RQ2-3.11` (`HC.HarishChandraModule`),
with `HCObj` and `harishChandraCatAbelian`.  The references to `HC/Module.lean` in this module
were written before the rename and are to that file.

## Main definitions / results

* `RationalQuivers.HC.WeightData.proj` — the projection `M → M_n` along the decomposition, with
  `proj_mem`, `proj_of_mem_same`, `proj_of_mem_ne`, `exists_sum_proj` and `proj_comm_of_graded`
  (a grading-preserving operator commutes with every projection).
* `RationalQuivers.HC.WeightData.OpStable` / `IsHomog` — a submodule stable under `H`, `X`, `Y`,
  resp. stable under the projections.  Both are what a `(𝔤,K)`-submodule amounts to once the
  `K`-action is remembered to be the scalar `χ_n` on `M_n` (`HC/Module.lean`).
* `RationalQuivers.HC.WeightData.sub` / `WeightData.quot` — the induced `WeightData` on a
  homogeneous stable submodule and on the quotient by one.
* `RationalQuivers.HC.WeightData.casimir_mem_comp` — `C` preserves `M_n`; **moved here** from
  `HC/Normalization.lean` (unchanged), which is downstream of `HC/Module.lean` and therefore
  cannot serve the abelian-category construction.
* `RationalQuivers.HC.WeightData.casimir_commute_H` — `[C,H] = 0`, the companion of
  `casimir_commute_X`/`casimir_commute_Y`.

## Implementation notes

The projections are built from `DirectSum.IsInternal` **without** a `DirectSum.Decomposition`
instance: `LinearEquiv.ofBijective (DirectSum.coeLinearMap W.comp) W.isInternal` is already a
linear equivalence `⨁_n M_n ≃ₗ M`, and mathlib's `IsInternal.ofBijective_coeLinearMap_of_mem` /
`…_of_mem_ne` are stated for exactly that spelling.  Threading a noncomputable `Decomposition`
instance through every lemma would make the projections' defeq depend on which `letI` was in
scope; this way `WeightData.proj` is one closed term.
-/

universe u v

namespace RationalQuivers.HC

variable {E : Type u} [Field E] {M : Type v} [AddCommGroup M] [Module E M]

namespace WeightData

/-! ## The projections onto the homogeneous components -/

/-- `M ≃ₗ ⨁_{n ∈ ℤ} M_n`, the field `isInternal` read as a linear equivalence.

@census none
-/
noncomputable def decompEquiv (W : WeightData E M) :
    M ≃ₗ[E] DirectSum ℤ (fun n : ℤ => (W.comp n : Submodule E M)) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap W.comp) W.isInternal).symm

/-- The projection `M → M_n` along `M = ⨁_m M_m`, as an endomorphism of `M`.

@census none
-/
noncomputable def proj (W : WeightData E M) (n : ℤ) : Module.End E M where
  toFun v := ((W.decompEquiv v n : W.comp n) : M)
  map_add' a b := by simp
  map_smul' c a := by simp [DirectSum.smul_apply]

@[simp] theorem proj_apply (W : WeightData E M) (n : ℤ) (v : M) :
    W.proj n v = ((W.decompEquiv v n : W.comp n) : M) := rfl

theorem proj_mem (W : WeightData E M) (n : ℤ) (v : M) : W.proj n v ∈ W.comp n :=
  (W.decompEquiv v n).2

theorem proj_of_mem_same (W : WeightData E M) {n : ℤ} {v : M} (hv : v ∈ W.comp n) :
    W.proj n v = v := by
  show ((W.decompEquiv v n : W.comp n) : M) = v
  rw [decompEquiv]
  rw [W.isInternal.ofBijective_coeLinearMap_of_mem hv]

theorem proj_of_mem_ne (W : WeightData E M) {n m : ℤ} {v : M} (hv : v ∈ W.comp n) (hnm : n ≠ m) :
    W.proj m v = 0 := by
  show ((W.decompEquiv v m : W.comp m) : M) = 0
  rw [decompEquiv]
  rw [W.isInternal.ofBijective_coeLinearMap_of_mem_ne hnm hv]
  rfl

/-- Every `v` is the (finite) sum of its homogeneous components.

@census none
-/
theorem exists_sum_proj (W : WeightData E M) (v : M) :
    ∃ s : Finset ℤ, (∀ n, n ∉ s → W.proj n v = 0) ∧ ∑ n ∈ s, W.proj n v = v := by
  classical
  refine ⟨(W.decompEquiv v).support, ?_, ?_⟩
  · intro n hn
    have : W.decompEquiv v n = 0 := DFinsupp.notMem_support_iff.mp hn
    show ((W.decompEquiv v n : W.comp n) : M) = 0
    rw [this]; rfl
  · have hcoe : DirectSum.coeLinearMap W.comp (W.decompEquiv v) = v := by
      show (LinearEquiv.ofBijective (DirectSum.coeLinearMap W.comp) W.isInternal)
        ((LinearEquiv.ofBijective (DirectSum.coeLinearMap W.comp) W.isInternal).symm v) = v
      simp
    rw [DirectSum.coeLinearMap_eq_dfinsuppSum] at hcoe
    calc ∑ n ∈ (W.decompEquiv v).support, W.proj n v
        = DFinsupp.sum (W.decompEquiv v) (fun _ x => (x : M)) := rfl
      _ = v := hcoe

/-- A grading-preserving operator commutes with every projection.

@census none
-/
theorem proj_comm_of_graded (W : WeightData E M) (f : Module.End E M)
    (hf : ∀ (n : ℤ) (v : M), v ∈ W.comp n → f v ∈ W.comp n) (n : ℤ) (v : M) :
    W.proj n (f v) = f (W.proj n v) := by
  obtain ⟨s, hzero, hsum⟩ := W.exists_sum_proj v
  have h1 : f v = ∑ m ∈ s, f (W.proj m v) := by
    conv_lhs => rw [← hsum]
    rw [map_sum]
  rw [h1, map_sum,
    Finset.sum_eq_single n (fun m _ hmn => W.proj_of_mem_ne (hf m _ (W.proj_mem m v)) hmn)
      (fun hn => by rw [hzero n hn, map_zero, map_zero])]
  exact W.proj_of_mem_same (hf n _ (W.proj_mem n v))

/-- A grading-preserving **map between two weight modules** commutes with the projections.  The
`M' = M` case is `proj_comm_of_graded`; the general case is what makes `ker f` and `range f`
homogeneous for a morphism `f` of Harish-Chandra modules (`HC/Module.lean`).

@census none
-/
theorem proj_comm_of_map {M' : Type v} [AddCommGroup M'] [Module E M'] (W : WeightData E M)
    (V : WeightData E M') (f : M →ₗ[E] M')
    (hf : ∀ (n : ℤ) (v : M), v ∈ W.comp n → f v ∈ V.comp n) (n : ℤ) (v : M) :
    V.proj n (f v) = f (W.proj n v) := by
  obtain ⟨s, hzero, hsum⟩ := W.exists_sum_proj v
  have h1 : f v = ∑ m ∈ s, f (W.proj m v) := by
    conv_lhs => rw [← hsum]
    rw [map_sum]
  rw [h1, map_sum,
    Finset.sum_eq_single n (fun m _ hmn => V.proj_of_mem_ne (hf m _ (W.proj_mem m v)) hmn)
      (fun hn => by rw [hzero n hn, map_zero, map_zero])]
  exact V.proj_of_mem_same (hf n _ (W.proj_mem n v))

/-! ## Stable and homogeneous submodules -/

/-- `N` is stable under the three operators of the triple — the `𝔤`-half of being a
`(𝔤,K)`-submodule.

@census none
-/
def OpStable (W : WeightData E M) (N : Submodule E M) : Prop :=
  (∀ v ∈ N, W.H v ∈ N) ∧ (∀ v ∈ N, W.X v ∈ N) ∧ (∀ v ∈ N, W.Y v ∈ N)

/-- `N` contains the homogeneous components of each of its elements.  Together with `OpStable`
this is exactly a `(𝔤,K)`-submodule, since `rep g` acts on `M_n` by the scalar `χ_n(g)`
(`HC/Module.lean`).

@census none
-/
def IsHomog (W : WeightData E M) (N : Submodule E M) : Prop :=
  ∀ (n : ℤ) (v : M), v ∈ N → W.proj n v ∈ N

theorem isHomog_top (W : WeightData E M) : W.IsHomog ⊤ := fun _ _ _ => trivial

theorem opStable_top (W : WeightData E M) : W.OpStable ⊤ :=
  ⟨fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

/-- A homogeneous submodule is the sum of its homogeneous slices: to contain it, a submodule need
only contain every `M_n ⊓ N`.

@census none
-/
theorem IsHomog.le_of_inf_comp_le {W : WeightData E M} {N P : Submodule E M} (hN : W.IsHomog N)
    (h : ∀ n : ℤ, W.comp n ⊓ N ≤ P) : N ≤ P := by
  intro v hv
  obtain ⟨s, -, hsum⟩ := W.exists_sum_proj v
  rw [← hsum]
  exact sum_mem fun n _ => h n ⟨W.proj_mem n v, hN n v hv⟩

/-- The kernel of a grading-preserving operator is homogeneous.

@census none
-/
theorem isHomog_ker_of_graded (W : WeightData E M) (f : Module.End E M)
    (hf : ∀ (n : ℤ) (v : M), v ∈ W.comp n → f v ∈ W.comp n) :
    W.IsHomog (LinearMap.ker f) := by
  intro n v hv
  have : f (W.proj n v) = 0 := by
    rw [← W.proj_comm_of_graded f hf n v, LinearMap.mem_ker.mp hv, map_zero]
  exact LinearMap.mem_ker.mpr this

/-! ## The Casimir preserves the grading, and commutes with `H` -/

/-- `C` preserves `M_n`.  **Moved unchanged** from `HC/Normalization.lean`, which is downstream of
`HC/Module.lean` and so cannot serve `RQ-3.11-C4`'s construction.

@census none
-/
theorem casimir_mem_comp (W : WeightData E M) (n : ℤ) (v : M) (hv : v ∈ W.comp n) :
    W.casimir v ∈ W.comp n := by
  have h1 : W.H v ∈ W.comp n := by
    rw [W.H_apply n v hv]; exact Submodule.smul_mem _ _ hv
  have h2 : W.H (W.H v) ∈ W.comp n := by
    rw [W.H_apply n _ h1]; exact Submodule.smul_mem _ _ h1
  have h3 : W.X (W.Y v) ∈ W.comp n := by
    have hy := W.Y_mem n v hv
    have hx := W.X_mem (n - 2) _ hy
    have he : n - 2 + 2 = n := by ring
    rwa [he] at hx
  rw [W.casimir_apply v]
  exact add_mem (add_mem (sub_mem h2 (Submodule.smul_mem _ _ h1))
    (Submodule.smul_mem _ _ h3)) hv

/-- `[C,H] = 0`; the companion of `casimir_commute_X` and `casimir_commute_Y`.

@census none
-/
theorem casimir_commute_H (W : WeightData E M) : Commute W.casimir W.H := by
  show (W.H ^ 2 - 2 * W.H + 4 * (W.X * W.Y) + 1) * W.H
      = W.H * (W.H ^ 2 - 2 * W.H + 4 * (W.X * W.Y) + 1)
  linear_combination (norm := noncomm_ring) (-4) * W.H_mul_X_numeral * W.Y
    - 4 * W.X * W.H_mul_Y_numeral

/-! ## A projection criterion for `DirectSum.IsInternal`

Each of the three induced decompositions below (submodule, quotient, product) is proved from the
*same* four facts about an explicit family of projections, so the criterion is isolated once.
-/

end WeightData

/-- `DirectSum.IsInternal` from an explicit family of projections.

@census none
-/
theorem isInternal_of_proj {ι : Type*} [DecidableEq ι] {N : Type v} [AddCommGroup N] [Module E N]
    (comp : ι → Submodule E N) (π : ι → Module.End E N)
    (hmem : ∀ (i : ι) (v : N), π i v ∈ comp i)
    (hsame : ∀ (i : ι) (v : N), v ∈ comp i → π i v = v)
    (hne : ∀ (i j : ι) (v : N), v ∈ comp i → i ≠ j → π j v = 0)
    (hsum : ∀ v : N, ∃ s : Finset ι, ∑ i ∈ s, π i v = v) :
    DirectSum.IsInternal comp := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro n
    have key : ∀ w : N, w ∈ (⨆ (m : ι), ⨆ (_ : m ≠ n), comp m) → π n w = 0 := by
      intro w hw
      induction hw using Submodule.iSup_induction' with
      | mem m x hx =>
          by_cases hmn : m = n
          · subst hmn
            rw [iSup_neg (by simp)] at hx
            rw [Submodule.mem_bot] at hx
            rw [hx, map_zero]
          · rw [iSup_pos hmn] at hx
            exact hne m n x hx hmn
      | zero => exact map_zero _
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    rw [Submodule.disjoint_def]
    intro v hv1 hv2
    rw [← hsame n v hv1, key v hv2]
  · rw [eq_top_iff]
    intro v _
    obtain ⟨s, hs⟩ := hsum v
    rw [← hs]
    exact sum_mem fun i _ => Submodule.mem_iSup_of_mem i (hmem i v)

namespace WeightData

/-! ## The `WeightData` on a homogeneous stable submodule -/

variable {W : WeightData E M} {N : Submodule E M}

/-- The `n`-th projection, restricted to a homogeneous submodule.

@census none
-/
noncomputable def subProj (hhom : W.IsHomog N) (n : ℤ) : Module.End E N :=
  (W.proj n).restrict (hhom n)

theorem isInternal_sub (hhom : W.IsHomog N) :
    DirectSum.IsInternal (fun n : ℤ => (W.comp n).comap N.subtype) := by
  classical
  refine isInternal_of_proj _ (subProj hhom) (fun n v => ?_) (fun n v hv => ?_)
    (fun n m v hv hnm => ?_) (fun v => ?_)
  · exact W.proj_mem n (v : M)
  · exact Subtype.ext (W.proj_of_mem_same hv)
  · exact Subtype.ext (W.proj_of_mem_ne hv hnm)
  · obtain ⟨s, -, hsum⟩ := W.exists_sum_proj (v : M)
    refine ⟨s, Subtype.ext ?_⟩
    rw [← hsum]
    exact map_sum N.subtype (fun n => subProj hhom n v) s

/-- The `WeightData` induced on a homogeneous, `H`/`X`/`Y`-stable submodule.

@census none
-/
noncomputable def sub (hst : W.OpStable N) (hhom : W.IsHomog N) : WeightData E N where
  comp n := (W.comp n).comap N.subtype
  isInternal := isInternal_sub hhom
  H := W.H.restrict hst.1
  X := W.X.restrict hst.2.1
  Y := W.Y.restrict hst.2.2
  H_apply n v hv := Subtype.ext (by
    simpa [LinearMap.coe_restrict_apply] using W.H_apply n (v : M) hv)
  X_mem n v hv := by
    show W.X (v : M) ∈ W.comp (n + 2)
    exact W.X_mem n (v : M) hv
  Y_mem n v hv := by
    show W.Y (v : M) ∈ W.comp (n - 2)
    exact W.Y_mem n (v : M) hv
  lie_H_X := by
    ext v
    have := congrArg (fun t : Module.End E M => t (v : M)) W.lie_H_X
    simpa [LinearMap.coe_restrict_apply] using this
  lie_H_Y := by
    ext v
    have := congrArg (fun t : Module.End E M => t (v : M)) W.lie_H_Y
    simpa [LinearMap.coe_restrict_apply] using this
  lie_X_Y := by
    ext v
    have := congrArg (fun t : Module.End E M => t (v : M)) W.lie_X_Y
    simpa [LinearMap.coe_restrict_apply] using this

@[simp] theorem sub_comp (hst : W.OpStable N) (hhom : W.IsHomog N) (n : ℤ) :
    (sub hst hhom).comp n = (W.comp n).comap N.subtype := rfl

@[simp] theorem sub_H_coe (hst : W.OpStable N) (hhom : W.IsHomog N) (v : N) :
    (((sub hst hhom).H v : N) : M) = W.H (v : M) := rfl

@[simp] theorem sub_X_coe (hst : W.OpStable N) (hhom : W.IsHomog N) (v : N) :
    (((sub hst hhom).X v : N) : M) = W.X (v : M) := rfl

@[simp] theorem sub_Y_coe (hst : W.OpStable N) (hhom : W.IsHomog N) (v : N) :
    (((sub hst hhom).Y v : N) : M) = W.Y (v : M) := rfl

/-! ## The `WeightData` on the quotient by a homogeneous stable submodule -/

/-- The `n`-th projection, descended to the quotient by a homogeneous submodule.

@census none
-/
noncomputable def quotProj (hhom : W.IsHomog N) (n : ℤ) : Module.End E (M ⧸ N) :=
  N.mapQ N (W.proj n) (fun v hv => hhom n v hv)

@[simp] theorem quotProj_mk (hhom : W.IsHomog N) (n : ℤ) (v : M) :
    quotProj hhom n (Submodule.Quotient.mk v) = Submodule.Quotient.mk (W.proj n v) := rfl

theorem isInternal_quot (hhom : W.IsHomog N) :
    DirectSum.IsInternal (fun n : ℤ => (W.comp n).map N.mkQ) := by
  classical
  refine isInternal_of_proj _ (quotProj hhom) (fun n x => ?_) (fun n x hx => ?_)
    (fun n m x hx hnm => ?_) (fun x => ?_)
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    exact ⟨W.proj n v, W.proj_mem n v, rfl⟩
  · obtain ⟨a, ha, rfl⟩ := hx
    show Submodule.Quotient.mk (W.proj n a) = _
    rw [W.proj_of_mem_same ha]
    rfl
  · obtain ⟨a, ha, rfl⟩ := hx
    show Submodule.Quotient.mk (W.proj m a) = _
    rw [W.proj_of_mem_ne ha hnm]
    exact Submodule.Quotient.mk_zero N
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    obtain ⟨s, -, hsum⟩ := W.exists_sum_proj v
    refine ⟨s, ?_⟩
    calc ∑ n ∈ s, quotProj hhom n (Submodule.Quotient.mk v)
        = ∑ n ∈ s, N.mkQ (W.proj n v) := Finset.sum_congr rfl fun n _ => rfl
      _ = N.mkQ (∑ n ∈ s, W.proj n v) := (map_sum N.mkQ _ s).symm
      _ = N.mkQ v := by rw [hsum]

/-- The `WeightData` induced on the quotient by a homogeneous, `H`/`X`/`Y`-stable submodule.

@census none
-/
noncomputable def quot (hst : W.OpStable N) (hhom : W.IsHomog N) : WeightData E (M ⧸ N) where
  comp n := (W.comp n).map N.mkQ
  isInternal := isInternal_quot hhom
  H := N.mapQ N W.H (fun v hv => hst.1 v hv)
  X := N.mapQ N W.X (fun v hv => hst.2.1 v hv)
  Y := N.mapQ N W.Y (fun v hv => hst.2.2 v hv)
  H_apply n v hv := by
    obtain ⟨a, ha, rfl⟩ := hv
    show (Submodule.Quotient.mk (W.H a) : M ⧸ N) = (n : E) • (Submodule.Quotient.mk a : M ⧸ N)
    rw [W.H_apply n a ha]
    rfl
  X_mem n v hv := by
    obtain ⟨a, ha, rfl⟩ := hv
    exact ⟨W.X a, W.X_mem n a ha, rfl⟩
  Y_mem n v hv := by
    obtain ⟨a, ha, rfl⟩ := hv
    exact ⟨W.Y a, W.Y_mem n a ha, rfl⟩
  lie_H_X := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    have h := congrArg (fun t : Module.End E M => t v) W.lie_H_X
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply] at h ⊢
    show (Submodule.Quotient.mk (W.H (W.X v)) : M ⧸ N) - (Submodule.Quotient.mk (W.X (W.H v)))
        = (2 : E) • (Submodule.Quotient.mk (W.X v) : M ⧸ N)
    rw [← Submodule.Quotient.mk_sub, h]
    rfl
  lie_H_Y := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    have h := congrArg (fun t : Module.End E M => t v) W.lie_H_Y
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
      LinearMap.neg_apply] at h ⊢
    show (Submodule.Quotient.mk (W.H (W.Y v)) : M ⧸ N) - (Submodule.Quotient.mk (W.Y (W.H v)))
        = -((2 : E) • (Submodule.Quotient.mk (W.Y v) : M ⧸ N))
    rw [← Submodule.Quotient.mk_sub, h]
    rfl
  lie_X_Y := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
    have h := congrArg (fun t : Module.End E M => t v) W.lie_X_Y
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h ⊢
    show (Submodule.Quotient.mk (W.X (W.Y v)) : M ⧸ N) - (Submodule.Quotient.mk (W.Y (W.X v)))
        = (Submodule.Quotient.mk (W.H v) : M ⧸ N)
    rw [← Submodule.Quotient.mk_sub, h]

@[simp] theorem quot_comp (hst : W.OpStable N) (hhom : W.IsHomog N) (n : ℤ) :
    (quot hst hhom).comp n = (W.comp n).map N.mkQ := rfl

@[simp] theorem quot_H_mk (hst : W.OpStable N) (hhom : W.IsHomog N) (v : M) :
    (quot hst hhom).H (Submodule.Quotient.mk v) = Submodule.Quotient.mk (W.H v) := rfl

@[simp] theorem quot_X_mk (hst : W.OpStable N) (hhom : W.IsHomog N) (v : M) :
    (quot hst hhom).X (Submodule.Quotient.mk v) = Submodule.Quotient.mk (W.X v) := rfl

@[simp] theorem quot_Y_mk (hst : W.OpStable N) (hhom : W.IsHomog N) (v : M) :
    (quot hst hhom).Y (Submodule.Quotient.mk v) = Submodule.Quotient.mk (W.Y v) := rfl

/-! ## The `WeightData` on a binary product -/

section Prod

variable {M₁ : Type v} [AddCommGroup M₁] [Module E M₁]
variable {M₂ : Type v} [AddCommGroup M₂] [Module E M₂]

theorem isInternal_prod (W₁ : WeightData E M₁) (W₂ : WeightData E M₂) :
    DirectSum.IsInternal (fun n : ℤ => (W₁.comp n).prod (W₂.comp n)) := by
  classical
  refine isInternal_of_proj _ (fun n => (W₁.proj n).prodMap (W₂.proj n)) (fun n v => ?_)
    (fun n v hv => ?_) (fun n m v hv hnm => ?_) (fun v => ?_)
  · exact ⟨W₁.proj_mem n v.1, W₂.proj_mem n v.2⟩
  · exact Prod.ext (W₁.proj_of_mem_same hv.1) (W₂.proj_of_mem_same hv.2)
  · exact Prod.ext (W₁.proj_of_mem_ne hv.1 hnm) (W₂.proj_of_mem_ne hv.2 hnm)
  · obtain ⟨s₁, hz₁, hs₁⟩ := W₁.exists_sum_proj v.1
    obtain ⟨s₂, hz₂, hs₂⟩ := W₂.exists_sum_proj v.2
    refine ⟨s₁ ∪ s₂, Prod.ext ?_ ?_⟩
    · rw [Prod.fst_sum]
      rw [← Finset.sum_subset (Finset.subset_union_left (s₂ := s₂))
        (fun x _ hx => by simpa using hz₁ x hx)]
      simpa using hs₁
    · rw [Prod.snd_sum]
      rw [← Finset.sum_subset (Finset.subset_union_right (s₁ := s₁))
        (fun x _ hx => by simpa using hz₂ x hx)]
      simpa using hs₂

/-- The `WeightData` on a binary product, componentwise.

@census none
-/
noncomputable def prodData (W₁ : WeightData E M₁) (W₂ : WeightData E M₂) :
    WeightData E (M₁ × M₂) where
  comp n := (W₁.comp n).prod (W₂.comp n)
  isInternal := isInternal_prod W₁ W₂
  H := W₁.H.prodMap W₂.H
  X := W₁.X.prodMap W₂.X
  Y := W₁.Y.prodMap W₂.Y
  H_apply n v hv := Prod.ext (W₁.H_apply n v.1 hv.1) (W₂.H_apply n v.2 hv.2)
  X_mem n v hv := ⟨W₁.X_mem n v.1 hv.1, W₂.X_mem n v.2 hv.2⟩
  Y_mem n v hv := ⟨W₁.Y_mem n v.1 hv.1, W₂.Y_mem n v.2 hv.2⟩
  lie_H_X := by
    refine LinearMap.ext fun v => Prod.ext ?_ ?_
    · have h := congrArg (fun t : Module.End E M₁ => t v.1) W₁.lie_H_X
      simpa [LinearMap.prodMap_apply] using h
    · have h := congrArg (fun t : Module.End E M₂ => t v.2) W₂.lie_H_X
      simpa [LinearMap.prodMap_apply] using h
  lie_H_Y := by
    refine LinearMap.ext fun v => Prod.ext ?_ ?_
    · have h := congrArg (fun t : Module.End E M₁ => t v.1) W₁.lie_H_Y
      simpa [LinearMap.prodMap_apply] using h
    · have h := congrArg (fun t : Module.End E M₂ => t v.2) W₂.lie_H_Y
      simpa [LinearMap.prodMap_apply] using h
  lie_X_Y := by
    refine LinearMap.ext fun v => Prod.ext ?_ ?_
    · have h := congrArg (fun t : Module.End E M₁ => t v.1) W₁.lie_X_Y
      simpa [LinearMap.prodMap_apply] using h
    · have h := congrArg (fun t : Module.End E M₂ => t v.2) W₂.lie_X_Y
      simpa [LinearMap.prodMap_apply] using h

@[simp] theorem prodData_comp (W₁ : WeightData E M₁) (W₂ : WeightData E M₂) (n : ℤ) :
    (prodData W₁ W₂).comp n = (W₁.comp n).prod (W₂.comp n) := rfl

end Prod

end WeightData

end RationalQuivers.HC
