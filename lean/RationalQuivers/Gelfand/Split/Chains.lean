module

public import RationalQuivers.Gelfand.Split.Construction

@[expose] public section

/-!
# The chains of §5.1: faithfulness and fullness of `𝔼_F` (tex §5.1, Steps O-7e…O-7g)

For `j ≠ ±ℓ` the composites `4XY` on `M_{j+1}` and `4YX` on `M_{j-1}` equal
`C − j² = (ℓ² − j²) + nilpotent` (`eq:Xbijective`), so `X : M_{j−1} → M_{j+1}` is bijective, and the
three chains reach every weight component from `M(−)`, `M(⋆)`, `M(+)` (Step O-7e).  Hence a morphism
is determined by its three vertex components (engine `E1`, `eq_of_eq_on_V3`, Step O-7f), and a
compatible triple of component maps extends to a morphism by transport along the chains (engine
`E4`, `exists_hom_of_edges`, Step O-7g).  `E_FNil` is `𝔼_F` corestricted to `Rep^nil` with the
relation; it is faithful and full, so `prop:splitequivalence` reduces to essential surjectivity
(`equivalence_of_essSurj`), which `Split/EssSurj` supplies by the tex's route.

## Provenance (v2 WP-9, stage T2; relocation)
v1's `Gelfand/GeneralField/Construction.lean`, engines `E1`/`E4` and the `Functor2` section without
engine `E11`'s essential surjectivity (deleted, OP-2), moved to the namespace
`RationalQuivers.Gelfand.Split`; `E_Qi*` renamed `E_F*` (plan §6.3).  Docstrings carry their v1
wording: read `ℚ[√-1]` as `F`.
-/

namespace RationalQuivers.Gelfand.Split

open RationalQuivers.HC RationalQuivers.Gelfand

variable {F : Type} [Field F] [CharZero F]

variable {ℓ : ℕ} {Mi : Type} [AddCommGroup Mi] [Module F Mi]


/-! ### Engines `E1` and `E4`

**Moved here from `Gelfand/Equivalence.lean` (2026-09-05, `s8-g4-impl-11`, G4).  Position only —
every statement, docstring and proof below is unchanged** (the same precedent as the `RQ-5.01-C7`
move recorded above, 2026-09-03).  The reason is a proof-order finding, `F-S8-G4-2` (defect class
6, `WORKFLOW.md` §7): `E_F_equivalence` is stated in THIS module and its route — `E1`
(`eq_of_eq_on_V3`) for faithfulness, `E4` (`exists_hom_of_edges`) for fullness — was written in
`Gelfand/Equivalence.lean`, which *imports* this module, so as printed the route was not available
to the statement that needs it.  Both engines are pure `HCFObj F`-level material: they mention
nothing from the `ℚ`-rational layer (`gelfandQ`, `RepNilQ`, `phiC`, `limAt`, `E_Q_*`) and nothing
from `Gelfand/Conjugate.lean` or `Gelfand/Stabilization.lean`, which is why the move type-checks
with no edit.  `Gelfand/Equivalence.lean` kept both through the import.  *(2026-10-21, O-V2-6
round 2: v1's `Gelfand/Equivalence.lean` and `Gelfand/Conjugate.lean`, `Gelfand/Stabilization.lean`
were deleted with the v1 Q-chain at WP-13, `ae9eda9`; today the main line reaches this module
through `Gelfand/RationalStructure/Conjugate.lean`, which imports it.)*

`stages/S8/DESIGN-NOTES.md` §18.3. -/

/-! ### Engine `E1` — the three vertex components generate `M`

`E_QFunctor`'s morphism map is the restriction of a morphism to `M_{-(ℓ+1)}`, `M_{-(ℓ-1)}`,
`M_{ℓ+1}` (`E_Q_hom`'s `ψ`, `V3 A.qi`), so faithfulness (`C6`) is exactly "a morphism determined
on those three components is determined".  The engine is the source's own arithmetic: by
`prop:XY_C_relation` (S7, `RQ-3.04`) `4XY = C − j²·𝟏` on `M_{j+1}` and `4YX = C − j²·𝟏` on
`M_{j-1}`, and `C − j²·𝟏 = (ℓ² − j²)·𝟏 + (C − ℓ²·𝟏)` is a **unit** whenever `j² ≠ ℓ²`, because
`C − ℓ²·𝟏` is nilpotent (the generalized infinitesimal character).  Hence `X : M_{j-1} → M_{j+1}`
and `Y : M_{j+1} → M_{j-1}` are surjective for `j ≠ ±ℓ`, and chaining them reaches every component
of the central character's parity class from one of the three named ones. -/

section E1


/-- `j² ≠ ℓ²` in `ℚ[√-1]` follows from `j² ≠ ℓ²` in `ℤ` (characteristic zero).
@census none (helper) -/
theorem sq_ne_sq_of (j : ℤ) (h : j ^ 2 ≠ (ℓ : ℤ) ^ 2) :
    ((j : F)) ^ 2 ≠ ((ℓ : F)) ^ 2 := by
  intro hc
  apply h
  have hh : (((j ^ 2 : ℤ)) : F) = (((((ℓ : ℤ)) ^ 2 : ℤ)) : F) := by
    push_cast; exact hc
  exact_mod_cast hh




/-- `C − j²·𝟏` is a unit of `End(M)` whenever `j² ≠ ℓ²`: it is `(ℓ² − j²)·𝟏` plus the nilpotent
`C − ℓ²·𝟏`.  @census none (helper) -/
theorem isUnit_casimir_sub {A : HCFObj F ℓ} (j : ℤ)
    (hj : ((j : F)) ^ 2 ≠ ((ℓ : F)) ^ 2) :
    IsUnit (A.weight.casimir
      - (((j : F)) ^ 2) • (1 : Module.End F A.carrier)) := by
  obtain ⟨m, hm⟩ := A.gic
  have hnil : IsNilpotent (A.weight.casimir
      - (((ℓ : F)) ^ 2) • (1 : Module.End F A.carrier)) := by
    refine ⟨m, ?_⟩
    rw [show ((ℓ : F)) ^ 2 = algebraMap ℚ F ((ℓ : ℚ) ^ 2) by
      rw [map_pow, map_natCast]]
    exact hm
  have hc : ((ℓ : F) ^ 2 - (j : F) ^ 2) ≠ 0 := sub_ne_zero_of_ne (Ne.symm hj)
  have hu : IsUnit (((ℓ : F) ^ 2 - (j : F) ^ 2)
      • (1 : Module.End F A.carrier)) :=
    Units.isUnit ⟨_, ((ℓ : F) ^ 2 - (j : F) ^ 2)⁻¹ • 1,
      by rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_mul, one_smul],
      by rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_mul, one_smul]⟩
  have heq : A.weight.casimir - ((j : F) ^ 2) • 1
      = (A.weight.casimir - ((ℓ : F) ^ 2) • 1)
        + (((ℓ : F) ^ 2 - (j : F) ^ 2) • 1) := by
    rw [sub_smul]; abel
  rw [heq]
  exact hnil.isUnit_add_right_of_commute hu (by simp [Commute, SemiconjBy])

/-- **`X : M_{j-1} → M_{j+1}` is surjective for `j² ≠ ℓ²`**, from `4XY = C − j²·𝟏` on `M_{j+1}`
(`RQ-3.04`) and the finite-dimensionality of the component (admissibility).
@census none (helper) -/
theorem exists_X_preimage {A : HCFObj F ℓ} (j : ℤ)
    (hj : ((j : F)) ^ 2 ≠ ((ℓ : F)) ^ 2)
    (w : A.carrier) (hw : w ∈ A.weight.comp (j + 1)) :
    ∃ u, u ∈ A.weight.comp (j - 1) ∧ A.weight.X u = w := by
  haveI := A.admissible (j + 1)
  set T : Module.End F A.carrier :=
    A.weight.casimir - (((j : F)) ^ 2) • 1 with hT
  have hmem : ∀ x ∈ A.weight.comp (j + 1), T x ∈ A.weight.comp (j + 1) := by
    intro x hx
    show A.weight.casimir x - ((j : F) ^ 2) • x ∈ _
    exact Submodule.sub_mem _ (casimir_mem_comp _ _ _ hx) (Submodule.smul_mem _ _ hx)
  have hTu : IsUnit T := isUnit_casimir_sub j hj
  have hinj : Function.Injective (T.restrict hmem) := by
    intro a b hab
    exact Subtype.ext ((Module.End.isUnit_iff T).mp hTu |>.1 (congrArg Subtype.val hab))
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.mp hinj
    ⟨(4 : F) • w, Submodule.smul_mem _ _ hw⟩
  have hv' : T (v : A.carrier) = (4 : F) • w := congrArg Subtype.val hv
  have hkey := A.weight.four_X_Y_apply j (v : A.carrier) v.2
  have h4 : (4 : F) • A.weight.X (A.weight.Y (v : A.carrier))
      = (4 : F) • w := by rw [hkey]; exact hv'
  refine ⟨A.weight.Y (v : A.carrier), ?_, ?_⟩
  · have hmm := A.weight.Y_mem (j + 1) (v : A.carrier) v.2
    rwa [show (j + 1 - 2 : ℤ) = j - 1 by ring] at hmm
  · exact smul_right_injective A.carrier (by norm_num : (4 : F) ≠ 0) h4

/-- **`Y : M_{j+1} → M_{j-1}` is surjective for `j² ≠ ℓ²`**, from `4YX = C − j²·𝟏` on `M_{j-1}`.
@census none (helper) -/
theorem exists_Y_preimage {A : HCFObj F ℓ} (j : ℤ)
    (hj : ((j : F)) ^ 2 ≠ ((ℓ : F)) ^ 2)
    (w : A.carrier) (hw : w ∈ A.weight.comp (j - 1)) :
    ∃ u, u ∈ A.weight.comp (j + 1) ∧ A.weight.Y u = w := by
  haveI := A.admissible (j - 1)
  set T : Module.End F A.carrier :=
    A.weight.casimir - (((j : F)) ^ 2) • 1 with hT
  have hmem : ∀ x ∈ A.weight.comp (j - 1), T x ∈ A.weight.comp (j - 1) := by
    intro x hx
    show A.weight.casimir x - ((j : F) ^ 2) • x ∈ _
    exact Submodule.sub_mem _ (casimir_mem_comp _ _ _ hx) (Submodule.smul_mem _ _ hx)
  have hTu : IsUnit T := isUnit_casimir_sub j hj
  have hinj : Function.Injective (T.restrict hmem) := by
    intro a b hab
    exact Subtype.ext ((Module.End.isUnit_iff T).mp hTu |>.1 (congrArg Subtype.val hab))
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.mp hinj
    ⟨(4 : F) • w, Submodule.smul_mem _ _ hw⟩
  have hv' : T (v : A.carrier) = (4 : F) • w := congrArg Subtype.val hv
  have hmem' : (v : A.carrier) ∈ A.weight.comp (-((-j) + 1)) := by
    rw [show (-((-j) + 1) : ℤ) = j - 1 by ring]; exact v.2
  have hkey := A.weight.four_Y_X_apply (-j) (v : A.carrier) hmem'
  have hcast : ((((-j : ℤ)) : F)) ^ 2 = (((j : ℤ) : F)) ^ 2 := by
    push_cast; ring
  rw [hcast] at hkey
  have h4 : (4 : F) • A.weight.Y (A.weight.X (v : A.carrier))
      = (4 : F) • w := by rw [hkey]; exact hv'
  refine ⟨A.weight.X (v : A.carrier), ?_, ?_⟩
  · have hmm := A.weight.X_mem (j - 1) (v : A.carrier) v.2
    rwa [show (j - 1 + 2 : ℤ) = j + 1 by ring] at hmm
  · exact smul_right_injective A.carrier (by norm_num : (4 : F) ≠ 0) h4

/-- **Engine `E1`.**  A grading-preserving map commuting with `X` and `Y` that vanishes on the
three vertex components `M_{-(ℓ+1)}`, `M_{-(ℓ-1)}`, `M_{ℓ+1}` vanishes on every component: the
central character confines the components to one parity class, and the three chains of
surjectivities reach every member of it.  @census none (helper) -/
theorem vanish_on_comp {A B : HCFObj F ℓ}
    (F : A.carrier →ₗ[F] B.carrier)
    (hX : ∀ v, F (A.weight.X v) = B.weight.X (F v))
    (hY : ∀ v, F (A.weight.Y v) = B.weight.Y (F v))
    (h0 : ∀ (v : Fin 3) (m : A.carrier), m ∈ A.weight.comp (vtxIdx ℓ v) → F m = 0) :
    ∀ (n : ℤ) (m : A.carrier), m ∈ A.weight.comp n → F m = 0 := by
  have hup : ∀ (k : ℕ) (n : ℤ), n = (ℓ : ℤ) + 1 + 2 * (k : ℤ) →
      ∀ m ∈ A.weight.comp n, F m = 0 := by
    intro k
    induction k with
    | zero =>
        intro n hn m hm
        refine h0 2 m ?_
        have hn' : vtxIdx ℓ 2 = n := by show ((ℓ : ℤ) + 1) = n; omega
        rw [hn']; exact hm
    | succ k ih =>
        intro n hn m hm
        obtain ⟨u, hu, rfl⟩ := exists_X_preimage ((ℓ : ℤ) + 2 * (k : ℤ) + 2)
          (sq_ne_sq_of _ (sq_ne_sq_gt _ (by omega))) m
          (by rw [show ((ℓ : ℤ) + 2 * (k : ℤ) + 2 + 1 : ℤ) = n by omega]; exact hm)
        rw [hX, ih ((ℓ : ℤ) + 2 * (k : ℤ) + 2 - 1) (by omega) u hu, map_zero]
  have hdown : ∀ (k : ℕ) (n : ℤ), n = -((ℓ : ℤ) + 1) - 2 * (k : ℤ) →
      ∀ m ∈ A.weight.comp n, F m = 0 := by
    intro k
    induction k with
    | zero =>
        intro n hn m hm
        refine h0 0 m ?_
        have hn' : vtxIdx ℓ 0 = n := by show (-((ℓ : ℤ) + 1)) = n; omega
        rw [hn']; exact hm
    | succ k ih =>
        intro n hn m hm
        obtain ⟨u, hu, rfl⟩ := exists_Y_preimage (-(ℓ : ℤ) - 2 * (k : ℤ) - 2)
          (sq_ne_sq_of _ (sq_ne_sq_lt _ (by omega))) m
          (by rw [show (-(ℓ : ℤ) - 2 * (k : ℤ) - 2 - 1 : ℤ) = n by omega]; exact hm)
        rw [hY, ih (-(ℓ : ℤ) - 2 * (k : ℤ) - 2 + 1) (by omega) u hu, map_zero]
  have hmid : ∀ (k : ℕ) (n : ℤ), n = -((ℓ : ℤ) - 1) + 2 * (k : ℤ) → n ≤ (ℓ : ℤ) - 1 →
      ∀ m ∈ A.weight.comp n, F m = 0 := by
    intro k
    induction k with
    | zero =>
        intro n hn _ m hm
        refine h0 1 m ?_
        have hn' : vtxIdx ℓ 1 = n := by show (-((ℓ : ℤ) - 1)) = n; omega
        rw [hn']; exact hm
    | succ k ih =>
        intro n hn hle m hm
        obtain ⟨u, hu, rfl⟩ := exists_X_preimage (n - 1)
          (sq_ne_sq_of _ (sq_ne_sq_abs _ (by omega) (by omega))) m
          (by rw [show (n - 1 + 1 : ℤ) = n by ring]; exact hm)
        rw [hX, ih (n - 1 - 1) (by omega) (by omega) u hu, map_zero]
  intro n m hm
  by_cases hpar : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · rcases (show (ℓ : ℤ) + 1 ≤ n ∨ n ≤ -((ℓ : ℤ) + 1) ∨ (-((ℓ : ℤ) - 1) ≤ n ∧ n ≤ (ℓ : ℤ) - 1)
        by omega) with hc | hc | hc
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = (ℓ : ℤ) + 1 + 2 * (k : ℤ) :=
        ⟨((n - (ℓ : ℤ) - 1) / 2).toNat, by omega⟩
      exact hup k n hk m hm
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -((ℓ : ℤ) + 1) - 2 * (k : ℤ) :=
        ⟨((-(ℓ : ℤ) - 1 - n) / 2).toNat, by omega⟩
      exact hdown k n hk m hm
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -((ℓ : ℤ) - 1) + 2 * (k : ℤ) :=
        ⟨((n + (ℓ : ℤ) - 1) / 2).toNat, by omega⟩
      exact hmid k n hk hc.2 m hm
  · have hb := A.centralCharacter n hpar
    rw [hb, Submodule.mem_bot] at hm
    rw [hm, map_zero]

/-- **`E1`, as the faithfulness statement**: two morphisms of `HC_λ(𝔤,K)_{ℚ[√-1]}` that agree on
the three vertex components are equal.  @census none (helper)
@clauses   RQ2-5.02-S-O7f -/
theorem eq_of_eq_on_V3 {A B : HCFObj F ℓ} (f g : A ⟶ B)
    (h : ∀ (v : Fin 3) (m : A.carrier), m ∈ A.weight.comp (vtxIdx ℓ v) →
      f.toLinearMap m = g.toLinearMap m) : f = g := by
  refine HCFHom.hom_ext (LinearMap.ext fun m => ?_)
  have hall := vanish_on_comp (f.toLinearMap - g.toLinearMap)
    (fun v => by
      show f.toLinearMap (A.weight.X v) - g.toLinearMap (A.weight.X v)
        = B.weight.X (f.toLinearMap v - g.toLinearMap v)
      rw [f.map_X, g.map_X, map_sub])
    (fun v => by
      show f.toLinearMap (A.weight.Y v) - g.toLinearMap (A.weight.Y v)
        = B.weight.Y (f.toLinearMap v - g.toLinearMap v)
      rw [f.map_Y, g.map_Y, map_sub])
    (fun v m hm => by
      show f.toLinearMap m - g.toLinearMap m = 0
      rw [h v m hm, sub_self])
  obtain ⟨s, -, hsum⟩ := A.weight.exists_sum_proj m
  have hz : (f.toLinearMap - g.toLinearMap) m = 0 := by
    rw [← hsum, map_sum]
    exact Finset.sum_eq_zero fun n _ => hall n _ (A.weight.proj_mem n m)
  have hz' : f.toLinearMap m - g.toLinearMap m = 0 := hz
  exact sub_eq_zero.mp hz'


/-- **`X : M_{j-1} → M_{j+1}` is injective for `j² ≠ ℓ²`** — the companion of
`exists_X_preimage`, from `4YX = C − j²·𝟏` on `M_{j-1}`.  @census none (helper) -/
theorem X_injective_on_comp {A : HCFObj F ℓ} (j : ℤ)
    (hj : ((j : F)) ^ 2 ≠ ((ℓ : F)) ^ 2)
    (u : A.carrier) (hu : u ∈ A.weight.comp (j - 1)) (h0 : A.weight.X u = 0) : u = 0 := by
  have hmem' : u ∈ A.weight.comp (-((-j) + 1)) := by
    rw [show (-((-j) + 1) : ℤ) = j - 1 by ring]; exact hu
  have hkey := A.weight.four_Y_X_apply (-j) u hmem'
  have hcast : ((((-j : ℤ)) : F)) ^ 2 = (((j : ℤ) : F)) ^ 2 := by
    push_cast; ring
  rw [hcast, h0, map_zero, smul_zero] at hkey
  have hTu : IsUnit (A.weight.casimir - (((j : F)) ^ 2) • (1 : Module.End _ A.carrier)) :=
    isUnit_casimir_sub j hj
  refine (Module.End.isUnit_iff _).mp hTu |>.1 ?_
  show A.weight.casimir u - ((j : F) ^ 2) • u
      = A.weight.casimir 0 - ((j : F) ^ 2) • (0 : A.carrier)
  simp [← hkey]

/-- **`Y : M_{j+1} → M_{j-1}` is injective for `j² ≠ ℓ²`**, from `4XY = C − j²·𝟏` on `M_{j+1}`.
@census none (helper) -/
theorem Y_injective_on_comp {A : HCFObj F ℓ} (j : ℤ)
    (hj : ((j : F)) ^ 2 ≠ ((ℓ : F)) ^ 2)
    (u : A.carrier) (hu : u ∈ A.weight.comp (j + 1)) (h0 : A.weight.Y u = 0) : u = 0 := by
  have hkey := A.weight.four_X_Y_apply j u hu
  rw [h0, map_zero, smul_zero] at hkey
  have hTu : IsUnit (A.weight.casimir - (((j : F)) ^ 2) • (1 : Module.End _ A.carrier)) :=
    isUnit_casimir_sub j hj
  refine (Module.End.isUnit_iff _).mp hTu |>.1 ?_
  show A.weight.casimir u - ((j : F) ^ 2) • u
      = A.weight.casimir 0 - ((j : F) ^ 2) • (0 : A.carrier)
  simp [← hkey]

/-- **`X` restricts to a `ℚ[√-1]`-linear isomorphism `M_{j-1} ≅ M_{j+1}` whenever `j² ≠ ℓ²`.**
This strengthens `exists_X_preimage`: `C − j²·𝟏` is a unit on **both** components, so `XY` is
bijective on `M_{j+1}` and `YX` is bijective on `M_{j-1}`, and hence `X` is bijective between
them.  Nothing in this stage consumes it yet; it is the lever the remaining `C7`/`E2` items need
(`stages/S8/DESIGN-NOTES.md` §12.4).  @census none (helper)
@clauses   RQ2-5.13-S-C3 -/
noncomputable def compEquivX {A : HCFObj F ℓ} (j : ℤ)
    (hj : ((j : F)) ^ 2 ≠ ((ℓ : F)) ^ 2) :
    A.weight.comp (j - 1) ≃ₗ[F] A.weight.comp (j + 1) :=
  LinearEquiv.ofBijective
    (A.weight.X.restrict (p := A.weight.comp (j - 1)) (q := A.weight.comp (j + 1))
      (fun x hx => by
        have h := A.weight.X_mem (j - 1) x hx
        rwa [show (j - 1 + 2 : ℤ) = j + 1 by ring] at h))
    ⟨fun a b hab => Subtype.ext (by
        have h : A.weight.X ((a : A.carrier) - (b : A.carrier)) = 0 := by
          rw [map_sub, sub_eq_zero]; exact congrArg Subtype.val hab
        have hz := X_injective_on_comp j hj _ (Submodule.sub_mem _ a.2 b.2) h
        exact sub_eq_zero.mp hz),
      fun w => by
        obtain ⟨u, hu, hux⟩ := exists_X_preimage j hj (w : A.carrier) w.2
        exact ⟨⟨u, hu⟩, Subtype.ext hux⟩⟩

/-- `compEquivX` is `X`.  @census none (helper) -/
theorem compEquivX_val {A : HCFObj F ℓ} (j : ℤ)
    (hj : ((j : F)) ^ 2 ≠ ((ℓ : F)) ^ 2)
    (u : A.weight.comp (j - 1)) : ((compEquivX j hj u : A.weight.comp (j + 1)) : A.carrier)
      = A.weight.X (u : A.carrier) := rfl

end E1

/-! ### Engine `E4` — building a morphism from its three vertex components

`E1` says a morphism of `HC_λ(𝔤,K)_{ℚ[√-1]}` is *determined* by its restriction to the three
vertex components.  `E_Q_full` (`RQ-5.05-C7`) needs the converse: every compatible triple of
component maps *comes from* a morphism.  The lever is `compEquivX` — `X : M_{j-1} ≅ M_{j+1}`
whenever `j² ≠ ℓ²` — which makes each of the three chains

* `M_{ℓ+1} → M_{ℓ+3} → ⋯` (upwards by `X`),
* `M_{-(ℓ+1)} → M_{-(ℓ+3)} → ⋯` (downwards by `X⁻¹`),
* `M_{-(ℓ-1)} → M_{-(ℓ-3)} → ⋯ → M_{ℓ-1}` (across by `X`)

a chain of isomorphisms, so a map on the three base components extends uniquely along them.
`stages/S8/DESIGN-NOTES.md` §15.6 records the route in full.  This section builds the two
type-level tools the extension needs: assembling a linear map out of its components, and the chain
isomorphisms with their values. -/

section E4


/-- A linear map assembled from a family of maps on the homogeneous components.
@census none (helper) -/
noncomputable def ofComponents {A B : HCFObj F ℓ}
    (g : ∀ n : ℤ, A.weight.comp n →ₗ[F] B.carrier) :
    A.carrier →ₗ[F] B.carrier :=
  (DirectSum.toModule F ℤ B.carrier g).comp
    (A.weight.decompEquiv : A.carrier →ₗ[F] _)

/-- `ofComponents g` is `g n` on `M_n`.  @census none (helper) -/
theorem ofComponents_apply {A B : HCFObj F ℓ}
    (g : ∀ n : ℤ, A.weight.comp n →ₗ[F] B.carrier) {n : ℤ} {m : A.carrier}
    (hm : m ∈ A.weight.comp n) : ofComponents g m = g n ⟨m, hm⟩ := by
  show DirectSum.toModule F ℤ B.carrier g (A.weight.decompEquiv m) = _
  rw [decompEquiv_of_mem A.weight hm, ← DirectSum.lof_eq_of (R := F),
    DirectSum.toModule_lof]

/-- One `X`-step as an isomorphism of components, with the two indices given by equations rather
than in `compEquivX`'s normal form.  @census none (helper) -/
noncomputable def stepX {A : HCFObj F ℓ} {a b : ℤ} (hb : b = a + 2)
    (hj : (((a + 1 : ℤ) : F)) ^ 2 ≠ ((ℓ : F)) ^ 2) :
    A.weight.comp a ≃ₗ[F] A.weight.comp b :=
  (LinearEquiv.ofEq _ _ (congrArg A.weight.comp (by omega : a = a + 1 - 1))).trans
    ((compEquivX (a + 1) hj).trans
      (LinearEquiv.ofEq _ _ (congrArg A.weight.comp (by omega : a + 1 + 1 = b))))

/-- `stepX` is `X`.  @census none (helper) -/
theorem stepX_val {A : HCFObj F ℓ} {a b : ℤ} (hb : b = a + 2)
    (hj : (((a + 1 : ℤ) : F)) ^ 2 ≠ ((ℓ : F)) ^ 2)
    (u : A.weight.comp a) :
    ((stepX hb hj u : A.weight.comp b) : A.carrier) = A.weight.X (u : A.carrier) := rfl

/-- The chain of `X`-isomorphisms `M_base ≅ M_{base + 2k}`, for `k ≤ K`, when every intermediate
index `base + 2i + 1` (`i < K`) avoids `±ℓ`.  @census none (helper) -/
noncomputable def chainX (A : HCFObj F ℓ) (base : ℤ) (K : ℕ)
    (hj : ∀ i : ℕ, i < K →
      (((base + 2 * (i : ℤ) + 1 : ℤ) : F)) ^ 2 ≠ ((ℓ : F)) ^ 2) :
    ∀ (k : ℕ), k ≤ K →
      A.weight.comp base ≃ₗ[F] A.weight.comp (base + 2 * (k : ℤ))
  | 0, _ => LinearEquiv.ofEq _ _ (congrArg A.weight.comp (by push_cast; ring))
  | (k + 1), hk =>
      (chainX A base K hj k (by omega)).trans
        (stepX (by push_cast; ring) (hj k (by omega)))

/-- The `k = 0` value of `chainX`.  @census none (helper) -/
theorem chainX_zero_val (A : HCFObj F ℓ) (base : ℤ) (K : ℕ)
    (hj : ∀ i : ℕ, i < K →
      (((base + 2 * (i : ℤ) + 1 : ℤ) : F)) ^ 2 ≠ ((ℓ : F)) ^ 2)
    (hk : 0 ≤ K) (u : A.weight.comp base) :
    ((chainX A base K hj 0 hk u : A.weight.comp (base + 2 * ((0 : ℕ) : ℤ))) : A.carrier)
      = (u : A.carrier) := rfl

/-- The step relation of `chainX`.  @census none (helper) -/
theorem chainX_succ_val (A : HCFObj F ℓ) (base : ℤ) (K : ℕ)
    (hj : ∀ i : ℕ, i < K →
      (((base + 2 * (i : ℤ) + 1 : ℤ) : F)) ^ 2 ≠ ((ℓ : F)) ^ 2)
    (k : ℕ) (hk : k + 1 ≤ K) (u : A.weight.comp base) :
    ((chainX A base K hj (k + 1) hk u : A.weight.comp (base + 2 * ((k + 1 : ℕ) : ℤ)))
        : A.carrier)
      = A.weight.X ((chainX A base K hj k (by omega) u : A.weight.comp (base + 2 * (k : ℤ)))
          : A.carrier) := rfl

/-- **`chainX` is `X^k`.**  Every statement about the chain should be made through this value
lemma rather than through the recursion: the chain built from `base` and the chain built from
`base + 2` differ by a step at the *front*, which the recursion (which appends at the back) does
not see definitionally, whereas the values agree on the nose.  @census none (helper) -/
theorem chainX_val (A : HCFObj F ℓ) (base : ℤ) (K : ℕ)
    (hj : ∀ i : ℕ, i < K →
      (((base + 2 * (i : ℤ) + 1 : ℤ) : F)) ^ 2 ≠ ((ℓ : F)) ^ 2) :
    ∀ (k : ℕ) (hk : k ≤ K) (u : A.weight.comp base),
      ((chainX A base K hj k hk u : A.weight.comp (base + 2 * (k : ℤ))) : A.carrier)
        = (A.weight.X ^ k) (u : A.carrier)
  | 0, _, u => rfl
  | (k + 1), hk, u => by
      rw [chainX_succ_val A base K hj k hk u, chainX_val A base K hj k (by omega) u,
        pow_succ']
      rfl

/-- `X^k` is injective on `M_base` along a chain.  @census none (helper) -/
theorem chainX_injective (A : HCFObj F ℓ) (base : ℤ) (K : ℕ)
    (hj : ∀ i : ℕ, i < K →
      (((base + 2 * (i : ℤ) + 1 : ℤ) : F)) ^ 2 ≠ ((ℓ : F)) ^ 2)
    (k : ℕ) (hk : k ≤ K) {u v : A.carrier} (hu : u ∈ A.weight.comp base)
    (hv : v ∈ A.weight.comp base) (h : (A.weight.X ^ k) u = (A.weight.X ^ k) v) : u = v := by
  have h' : chainX A base K hj k hk ⟨u, hu⟩ = chainX A base K hj k hk ⟨v, hv⟩ := by
    refine Subtype.ext ?_
    rw [chainX_val A base K hj k hk ⟨u, hu⟩, chainX_val A base K hj k hk ⟨v, hv⟩]
    exact h
  exact congrArg Subtype.val ((chainX A base K hj k hk).injective h')

/-- `X^k` is surjective onto `M_{base + 2k}` along a chain.  @census none (helper) -/
theorem chainX_surjective (A : HCFObj F ℓ) (base : ℤ) (K : ℕ)
    (hj : ∀ i : ℕ, i < K →
      (((base + 2 * (i : ℤ) + 1 : ℤ) : F)) ^ 2 ≠ ((ℓ : F)) ^ 2)
    (k : ℕ) (hk : k ≤ K) {w : A.carrier} (hw : w ∈ A.weight.comp (base + 2 * (k : ℤ))) :
    ∃ u : A.carrier, u ∈ A.weight.comp base ∧ (A.weight.X ^ k) u = w := by
  refine ⟨(((chainX A base K hj k hk).symm ⟨w, hw⟩ : A.weight.comp base) : A.carrier),
    ((chainX A base K hj k hk).symm ⟨w, hw⟩).2, ?_⟩
  rw [← chainX_val A base K hj k hk]
  exact congrArg Subtype.val ((chainX A base K hj k hk).apply_symm_apply ⟨w, hw⟩)

/-! #### The three chains of `E4`, and the extension of a compatible triple

The three chains and their index hypotheses.  `hjUp`/`hjDown`/`hjMid` are the "no `±ℓ` in the
interior" side conditions of `compEquivX` for the three regions. -/

/-- The `+` chain's index hypothesis: every interior index exceeds `ℓ`.  @census none (helper) -/
theorem hjUp (K : ℕ) : ∀ i : ℕ, i < K →
    (((((ℓ : ℤ) + 1) + 2 * (i : ℤ) + 1 : ℤ) : F)) ^ 2 ≠ ((ℓ : F)) ^ 2 :=
  fun i _ => sq_ne_sq_of _ (sq_ne_sq_gt _ (by omega))

/-- The `−` chain's index hypothesis: every interior index is below `−ℓ`.  @census none (helper) -/
theorem hjDown (n : ℤ) (K : ℕ) (h : n + 2 * (K : ℤ) = -((ℓ : ℤ) + 1)) : ∀ i : ℕ, i < K →
    (((n + 2 * (i : ℤ) + 1 : ℤ) : F)) ^ 2 ≠ ((ℓ : F)) ^ 2 :=
  fun i hi => sq_ne_sq_of _ (sq_ne_sq_lt _ (by omega))

/-- The `⋆` chain's index hypothesis: every interior index lies strictly between `−ℓ` and `ℓ`.
@census none (helper) -/
theorem hjMid (K : ℕ) (hK : (K : ℤ) ≤ (ℓ : ℤ) - 1) : ∀ i : ℕ, i < K →
    ((((-((ℓ : ℤ) - 1)) + 2 * (i : ℤ) + 1 : ℤ) : F)) ^ 2 ≠ ((ℓ : F)) ^ 2 :=
  fun i hi => sq_ne_sq_of _ (sq_ne_sq_abs _ (by omega) (by omega))

section E4Extend

variable {A B : HCFObj F ℓ}

/-- The `+` region's component map: `X^k ∘ ψ₊ ∘ (X^k)^{-1}` on `M_{ℓ+1+2k}`.
@census none (helper) -/
noncomputable def gUp
    (ψp : A.weight.comp ((ℓ : ℤ) + 1) →ₗ[F] B.weight.comp ((ℓ : ℤ) + 1))
    (k : ℕ) (n : ℤ) (hn : n = (ℓ : ℤ) + 1 + 2 * (k : ℤ)) :
    A.weight.comp n →ₗ[F] B.weight.comp n :=
  (LinearEquiv.ofEq _ _ (congrArg B.weight.comp hn.symm)).toLinearMap ∘ₗ
    (chainX B ((ℓ : ℤ) + 1) k (hjUp k) k le_rfl).toLinearMap ∘ₗ ψp ∘ₗ
      (chainX A ((ℓ : ℤ) + 1) k (hjUp k) k le_rfl).symm.toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ (congrArg A.weight.comp hn)).toLinearMap

/-- `gUp` reads off a chain preimage.  @census none (helper) -/
theorem gUp_val
    (ψp : A.weight.comp ((ℓ : ℤ) + 1) →ₗ[F] B.weight.comp ((ℓ : ℤ) + 1))
    (k : ℕ) (n : ℤ) (hn : n = (ℓ : ℤ) + 1 + 2 * (k : ℤ))
    (u : A.weight.comp ((ℓ : ℤ) + 1)) {m : A.carrier} (hm : m ∈ A.weight.comp n)
    (hmu : (A.weight.X ^ k) (u : A.carrier) = m) :
    ((gUp ψp k n hn ⟨m, hm⟩ : B.weight.comp n) : B.carrier)
      = (B.weight.X ^ k) ((ψp u : B.weight.comp ((ℓ : ℤ) + 1)) : B.carrier) := by
  have hu : chainX A ((ℓ : ℤ) + 1) k (hjUp k) k le_rfl u
      = (LinearEquiv.ofEq _ _ (congrArg A.weight.comp hn)) ⟨m, hm⟩ :=
    Subtype.ext (by rw [chainX_val, hmu]; rfl)
  show Subtype.val ((LinearEquiv.ofEq (B.weight.comp ((ℓ : ℤ) + 1 + 2 * (k : ℤ)))
      (B.weight.comp n) (congrArg B.weight.comp hn.symm))
      (chainX B ((ℓ : ℤ) + 1) k (hjUp k) k le_rfl
        (ψp ((chainX A ((ℓ : ℤ) + 1) k (hjUp k) k le_rfl).symm
          ((LinearEquiv.ofEq (A.weight.comp n) (A.weight.comp ((ℓ : ℤ) + 1 + 2 * (k : ℤ)))
            (congrArg A.weight.comp hn)) ⟨m, hm⟩))))) = _
  rw [← hu, LinearEquiv.symm_apply_apply]
  show ((chainX B ((ℓ : ℤ) + 1) k (hjUp k) k le_rfl (ψp u) :
    B.weight.comp ((ℓ : ℤ) + 1 + 2 * (k : ℤ))) : B.carrier) = _
  rw [chainX_val]

/-- The `−` region's component map: the `X^k`-preimage of `ψ₋` on `M_{-(ℓ+1)-2k}`.
@census none (helper) -/
noncomputable def gDown
    (ψm : A.weight.comp (-((ℓ : ℤ) + 1)) →ₗ[F] B.weight.comp (-((ℓ : ℤ) + 1)))
    (k : ℕ) (n : ℤ) (hn : n + 2 * (k : ℤ) = -((ℓ : ℤ) + 1)) :
    A.weight.comp n →ₗ[F] B.weight.comp n :=
  (chainX B n k (hjDown n k hn) k le_rfl).symm.toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ (congrArg B.weight.comp hn.symm)).toLinearMap ∘ₗ ψm ∘ₗ
      (LinearEquiv.ofEq _ _ (congrArg A.weight.comp hn)).toLinearMap ∘ₗ
      (chainX A n k (hjDown n k hn) k le_rfl).toLinearMap

/-- `gDown` is characterised by `X^k ∘ gDown = ψ₋ ∘ X^k`.  @census none (helper) -/
theorem gDown_val
    (ψm : A.weight.comp (-((ℓ : ℤ) + 1)) →ₗ[F] B.weight.comp (-((ℓ : ℤ) + 1)))
    (k : ℕ) (n : ℤ) (hn : n + 2 * (k : ℤ) = -((ℓ : ℤ) + 1))
    {m : A.carrier} (hm : m ∈ A.weight.comp n)
    (hXm : (A.weight.X ^ k) m ∈ A.weight.comp (-((ℓ : ℤ) + 1))) :
    (B.weight.X ^ k) ((gDown ψm k n hn ⟨m, hm⟩ : B.weight.comp n) : B.carrier)
      = ((ψm ⟨(A.weight.X ^ k) m, hXm⟩ : B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier) := by
  have hA : (LinearEquiv.ofEq _ _ (congrArg A.weight.comp hn))
      (chainX A n k (hjDown n k hn) k le_rfl ⟨m, hm⟩)
      = ⟨(A.weight.X ^ k) m, hXm⟩ := by
    refine Subtype.ext ?_
    show ((chainX A n k (hjDown n k hn) k le_rfl ⟨m, hm⟩ :
      A.weight.comp (n + 2 * (k : ℤ))) : A.carrier) = (A.weight.X ^ k) m
    rw [chainX_val]
  show (B.weight.X ^ k) (Subtype.val
      ((chainX B n k (hjDown n k hn) k le_rfl).symm
        ((LinearEquiv.ofEq (B.weight.comp (-((ℓ : ℤ) + 1))) (B.weight.comp (n + 2 * (k : ℤ)))
              (congrArg B.weight.comp hn.symm))
          (ψm ((LinearEquiv.ofEq (A.weight.comp (n + 2 * (k : ℤ)))
                (A.weight.comp (-((ℓ : ℤ) + 1))) (congrArg A.weight.comp hn))
            (chainX A n k (hjDown n k hn) k le_rfl ⟨m, hm⟩)))))) = _
  rw [hA, ← chainX_val B n k (hjDown n k hn) k le_rfl, LinearEquiv.apply_symm_apply]
  rfl

/-- The `⋆` region's component map: `X^k ∘ ψ_⋆ ∘ (X^k)^{-1}` on `M_{-(ℓ-1)+2k}`, `k ≤ ℓ-1`.
@census none (helper) -/
noncomputable def gMid
    (ψs : A.weight.comp (-((ℓ : ℤ) - 1)) →ₗ[F] B.weight.comp (-((ℓ : ℤ) - 1)))
    (k : ℕ) (hk : (k : ℤ) ≤ (ℓ : ℤ) - 1) (n : ℤ) (hn : n = -((ℓ : ℤ) - 1) + 2 * (k : ℤ)) :
    A.weight.comp n →ₗ[F] B.weight.comp n :=
  (LinearEquiv.ofEq _ _ (congrArg B.weight.comp hn.symm)).toLinearMap ∘ₗ
    (chainX B (-((ℓ : ℤ) - 1)) k (hjMid k hk) k le_rfl).toLinearMap ∘ₗ ψs ∘ₗ
      (chainX A (-((ℓ : ℤ) - 1)) k (hjMid k hk) k le_rfl).symm.toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ (congrArg A.weight.comp hn)).toLinearMap

/-- `gMid` reads off a chain preimage.  @census none (helper) -/
theorem gMid_val
    (ψs : A.weight.comp (-((ℓ : ℤ) - 1)) →ₗ[F] B.weight.comp (-((ℓ : ℤ) - 1)))
    (k : ℕ) (hk : (k : ℤ) ≤ (ℓ : ℤ) - 1) (n : ℤ) (hn : n = -((ℓ : ℤ) - 1) + 2 * (k : ℤ))
    (u : A.weight.comp (-((ℓ : ℤ) - 1))) {m : A.carrier} (hm : m ∈ A.weight.comp n)
    (hmu : (A.weight.X ^ k) (u : A.carrier) = m) :
    ((gMid ψs k hk n hn ⟨m, hm⟩ : B.weight.comp n) : B.carrier)
      = (B.weight.X ^ k) ((ψs u : B.weight.comp (-((ℓ : ℤ) - 1))) : B.carrier) := by
  have hu : chainX A (-((ℓ : ℤ) - 1)) k (hjMid k hk) k le_rfl u
      = (LinearEquiv.ofEq _ _ (congrArg A.weight.comp hn)) ⟨m, hm⟩ :=
    Subtype.ext (by rw [chainX_val, hmu]; rfl)
  show Subtype.val ((LinearEquiv.ofEq (B.weight.comp (-((ℓ : ℤ) - 1) + 2 * (k : ℤ)))
      (B.weight.comp n) (congrArg B.weight.comp hn.symm))
      (chainX B (-((ℓ : ℤ) - 1)) k (hjMid k hk) k le_rfl
        (ψs ((chainX A (-((ℓ : ℤ) - 1)) k (hjMid k hk) k le_rfl).symm
          ((LinearEquiv.ofEq (A.weight.comp n)
            (A.weight.comp (-((ℓ : ℤ) - 1) + 2 * (k : ℤ)))
            (congrArg A.weight.comp hn)) ⟨m, hm⟩))))) = _
  rw [← hu, LinearEquiv.symm_apply_apply]
  show ((chainX B (-((ℓ : ℤ) - 1)) k (hjMid k hk) k le_rfl (ψs u) :
    B.weight.comp (-((ℓ : ℤ) - 1) + 2 * (k : ℤ))) : B.carrier) = _
  rw [chainX_val]

/-- The component map of the extension, by region: `+` for `n ≥ ℓ+1`, `−` for `n ≤ −(ℓ+1)`,
`⋆` in between, and `0` off the central character's parity class (where the component is `⊥`).
@census none (helper) -/
noncomputable def gcomp
    (ψ : ∀ v : Fin 3, A.weight.comp (vtxIdx ℓ v) →ₗ[F] B.weight.comp (vtxIdx ℓ v))
    (n : ℤ) : A.weight.comp n →ₗ[F] B.weight.comp n :=
  if hp : (n - ((ℓ : ℤ) - 1)) % 2 = 0 then
    if h1 : (ℓ : ℤ) + 1 ≤ n then
      gUp (ψ 2) ((n - (ℓ : ℤ) - 1) / 2).toNat n (by omega)
    else if h2 : n ≤ -((ℓ : ℤ) + 1) then
      gDown (ψ 0) ((-((ℓ : ℤ) + 1) - n) / 2).toNat n (by omega)
    else
      gMid (ψ 1) ((n + (ℓ : ℤ) - 1) / 2).toNat (by omega) n (by omega)
  else 0

/-- `gcomp` in the `+` region.  @census none (helper) -/
theorem gcomp_up
    (ψ : ∀ v : Fin 3, A.weight.comp (vtxIdx ℓ v) →ₗ[F] B.weight.comp (vtxIdx ℓ v))
    (k : ℕ) (n : ℤ) (hn : n = (ℓ : ℤ) + 1 + 2 * (k : ℤ)) :
    gcomp ψ n = gUp (ψ 2) k n hn := by
  have hk : ((n - (ℓ : ℤ) - 1) / 2).toNat = k := by omega
  subst hk
  unfold gcomp
  rw [dif_pos (show (n - ((ℓ : ℤ) - 1)) % 2 = 0 by omega),
    dif_pos (show (ℓ : ℤ) + 1 ≤ n by omega)]

/-- `gcomp` in the `−` region.  @census none (helper) -/
theorem gcomp_down
    (ψ : ∀ v : Fin 3, A.weight.comp (vtxIdx ℓ v) →ₗ[F] B.weight.comp (vtxIdx ℓ v))
    (k : ℕ) (n : ℤ) (hn : n + 2 * (k : ℤ) = -((ℓ : ℤ) + 1)) :
    gcomp ψ n = gDown (ψ 0) k n hn := by
  have hk : ((-((ℓ : ℤ) + 1) - n) / 2).toNat = k := by omega
  subst hk
  unfold gcomp
  rw [dif_pos (show (n - ((ℓ : ℤ) - 1)) % 2 = 0 by omega),
    dif_neg (show ¬((ℓ : ℤ) + 1 ≤ n) by omega),
    dif_pos (show n ≤ -((ℓ : ℤ) + 1) by omega)]

/-- `gcomp` in the `⋆` region.  @census none (helper) -/
theorem gcomp_mid
    (ψ : ∀ v : Fin 3, A.weight.comp (vtxIdx ℓ v) →ₗ[F] B.weight.comp (vtxIdx ℓ v))
    (k : ℕ) (hk : (k : ℤ) ≤ (ℓ : ℤ) - 1) (n : ℤ) (hn : n = -((ℓ : ℤ) - 1) + 2 * (k : ℤ)) :
    gcomp ψ n = gMid (ψ 1) k hk n hn := by
  have hk' : ((n + (ℓ : ℤ) - 1) / 2).toNat = k := by omega
  subst hk'
  unfold gcomp
  rw [dif_pos (show (n - ((ℓ : ℤ) - 1)) % 2 = 0 by omega),
    dif_neg (show ¬((ℓ : ℤ) + 1 ≤ n) by omega),
    dif_neg (show ¬(n ≤ -((ℓ : ℤ) + 1)) by omega)]

/-- **The extension of a compatible triple**, as a linear map on the carrier.
@census none (helper) -/
noncomputable def extendMap
    (ψ : ∀ v : Fin 3, A.weight.comp (vtxIdx ℓ v) →ₗ[F] B.weight.comp (vtxIdx ℓ v)) :
    A.carrier →ₗ[F] B.carrier :=
  ofComponents (fun n => (B.weight.comp n).subtype ∘ₗ gcomp ψ n)

/-- `extendMap` on a homogeneous element.  @census none (helper) -/
theorem extendMap_apply
    (ψ : ∀ v : Fin 3, A.weight.comp (vtxIdx ℓ v) →ₗ[F] B.weight.comp (vtxIdx ℓ v))
    {n : ℤ} {m : A.carrier} (hm : m ∈ A.weight.comp n) :
    extendMap ψ m = ((gcomp ψ n ⟨m, hm⟩ : B.weight.comp n) : B.carrier) :=
  ofComponents_apply _ hm

/-- `extendMap` preserves the grading.  @census none (helper) -/
theorem extendMap_mem
    (ψ : ∀ v : Fin 3, A.weight.comp (vtxIdx ℓ v) →ₗ[F] B.weight.comp (vtxIdx ℓ v))
    (n : ℤ) (m : A.carrier) (hm : m ∈ A.weight.comp n) :
    extendMap ψ m ∈ B.weight.comp n := by
  rw [extendMap_apply ψ hm]
  exact Subtype.property _

/-- **The data engine `E4` extends**: a triple of maps on the three vertex components, compatible
with the four edges of `ex:gelfand` in the *cleared* form — `a₋` and `b₋` are `X` and `Y` at the
`−` wall, and `b₊`/`a₊` are the `X^ℓ`/`Y` form of `φ_{b₊} = X X⋆` and `φ_{a₊} = X⋆^{-1}Y` with the
normalisation `X⋆ = γ⋆^{-1}X^{ℓ-1}` cleared, so that no `StarInverses` datum appears.
@census none (helper) -/
structure ExtData {ℓ : ℕ} (A B : HCFObj F ℓ) where
  /-- the three component maps -/
  ψ : ∀ v : Fin 3, A.weight.comp (vtxIdx ℓ v) →ₗ[F] B.weight.comp (vtxIdx ℓ v)
  /-- `a₋`: `ψ_⋆ ∘ X = X ∘ ψ_-` on `M_{-(ℓ+1)}` -/
  edgeAm : ∀ (m : A.carrier) (hm : m ∈ A.weight.comp (-((ℓ : ℤ) + 1)))
      (h : A.weight.X m ∈ A.weight.comp (-((ℓ : ℤ) - 1))),
    ((ψ 1 ⟨A.weight.X m, h⟩ : B.weight.comp (-((ℓ : ℤ) - 1))) : B.carrier)
      = B.weight.X ((ψ 0 ⟨m, hm⟩ : B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier)
  /-- `b₋`: `ψ_- ∘ Y = Y ∘ ψ_⋆` on `M_{-(ℓ-1)}` -/
  edgeBm : ∀ (m : A.carrier) (hm : m ∈ A.weight.comp (-((ℓ : ℤ) - 1)))
      (h : A.weight.Y m ∈ A.weight.comp (-((ℓ : ℤ) + 1))),
    ((ψ 0 ⟨A.weight.Y m, h⟩ : B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier)
      = B.weight.Y ((ψ 1 ⟨m, hm⟩ : B.weight.comp (-((ℓ : ℤ) - 1))) : B.carrier)
  /-- `b₊` cleared: `ψ_+ ∘ X^ℓ = X^ℓ ∘ ψ_⋆` on `M_{-(ℓ-1)}` -/
  edgeBp : ∀ (u : A.weight.comp (-((ℓ : ℤ) - 1)))
      (h : A.weight.X ((A.weight.X ^ (ℓ - 1)) (u : A.carrier)) ∈ A.weight.comp ((ℓ : ℤ) + 1)),
    ((ψ 2 ⟨A.weight.X ((A.weight.X ^ (ℓ - 1)) (u : A.carrier)), h⟩ :
        B.weight.comp ((ℓ : ℤ) + 1)) : B.carrier)
      = B.weight.X ((B.weight.X ^ (ℓ - 1))
          ((ψ 1 u : B.weight.comp (-((ℓ : ℤ) - 1))) : B.carrier))
  /-- `a₊` cleared: if `X^{ℓ-1}u = Y m` then `X^{ℓ-1}(ψ_⋆ u) = Y (ψ_+ m)` -/
  edgeAp : ∀ (m : A.weight.comp ((ℓ : ℤ) + 1)) (u : A.weight.comp (-((ℓ : ℤ) - 1))),
    (A.weight.X ^ (ℓ - 1)) (u : A.carrier) = A.weight.Y (m : A.carrier) →
      (B.weight.X ^ (ℓ - 1)) ((ψ 1 u : B.weight.comp (-((ℓ : ℤ) - 1))) : B.carrier)
        = B.weight.Y ((ψ 2 m : B.weight.comp ((ℓ : ℤ) + 1)) : B.carrier)

namespace ExtData

variable {A B : HCFObj F ℓ} (d : ExtData A B)

/-- The extension of `d`, as a linear map.  @census none (helper) -/
noncomputable def map : A.carrier →ₗ[F] B.carrier := extendMap d.ψ

theorem map_mem (n : ℤ) (m : A.carrier) (hm : m ∈ A.weight.comp n) :
    d.map m ∈ B.weight.comp n := extendMap_mem d.ψ n m hm

/-- The value of the extension in the `+` region.  @census none (helper) -/
theorem map_up (k : ℕ) (n : ℤ) (hn : n = (ℓ : ℤ) + 1 + 2 * (k : ℤ))
    (u : A.weight.comp ((ℓ : ℤ) + 1)) {m : A.carrier} (hm : m ∈ A.weight.comp n)
    (hmu : (A.weight.X ^ k) (u : A.carrier) = m) :
    d.map m = (B.weight.X ^ k) ((d.ψ 2 u : B.weight.comp ((ℓ : ℤ) + 1)) : B.carrier) := by
  rw [ExtData.map, extendMap_apply d.ψ hm, gcomp_up d.ψ k n hn]
  exact gUp_val (d.ψ 2) k n hn u hm hmu

/-- The value of the extension in the `⋆` region.  @census none (helper) -/
theorem map_mid (k : ℕ) (hk : (k : ℤ) ≤ (ℓ : ℤ) - 1) (n : ℤ)
    (hn : n = -((ℓ : ℤ) - 1) + 2 * (k : ℤ))
    (u : A.weight.comp (-((ℓ : ℤ) - 1))) {m : A.carrier} (hm : m ∈ A.weight.comp n)
    (hmu : (A.weight.X ^ k) (u : A.carrier) = m) :
    d.map m = (B.weight.X ^ k) ((d.ψ 1 u : B.weight.comp (-((ℓ : ℤ) - 1))) : B.carrier) := by
  rw [ExtData.map, extendMap_apply d.ψ hm, gcomp_mid d.ψ k hk n hn]
  exact gMid_val (d.ψ 1) k hk n hn u hm hmu

/-- The characterisation of the extension in the `−` region.  @census none (helper) -/
theorem map_down (k : ℕ) (n : ℤ) (hn : n + 2 * (k : ℤ) = -((ℓ : ℤ) + 1))
    {m : A.carrier} (hm : m ∈ A.weight.comp n)
    (hXm : (A.weight.X ^ k) m ∈ A.weight.comp (-((ℓ : ℤ) + 1))) :
    (B.weight.X ^ k) (d.map m)
      = ((d.ψ 0 ⟨(A.weight.X ^ k) m, hXm⟩ : B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier) := by
  rw [ExtData.map, extendMap_apply d.ψ hm, gcomp_down d.ψ k n hn]
  exact gDown_val (d.ψ 0) k n hn hm hXm

/-- **The extension commutes with `X`.**  Inside each of the three chains this is the definition;
at the two `X`-walls it is the edge equations `a₋` and `b₊`.  @census none (helper) -/
theorem map_X_comp (hℓ : 1 ≤ ℓ) (n : ℤ) (m : A.carrier) (hm : m ∈ A.weight.comp n) :
    d.map (A.weight.X m) = B.weight.X (d.map m) := by
  have hXm : A.weight.X m ∈ A.weight.comp (n + 2) := A.weight.X_mem n m hm
  by_cases hp : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · rcases (show (ℓ : ℤ) + 1 ≤ n ∨ n ≤ -((ℓ : ℤ) + 3) ∨ n = -((ℓ : ℤ) + 1) ∨
        (-((ℓ : ℤ) - 1) ≤ n ∧ n ≤ (ℓ : ℤ) - 3) ∨ n = (ℓ : ℤ) - 1 by omega) with h | h | h | h | h
    · -- `+` chain interior
      set k : ℕ := ((n - (ℓ : ℤ) - 1) / 2).toNat with hkdef
      have hnk : n = (ℓ : ℤ) + 1 + 2 * (k : ℤ) := by omega
      obtain ⟨u, hu, hmu⟩ := chainX_surjective A ((ℓ : ℤ) + 1) k (hjUp k) k le_rfl (hnk ▸ hm)
      have hmu' : (A.weight.X ^ (k + 1)) u = A.weight.X m := by
        rw [pow_succ', Module.End.mul_apply, hmu]
      rw [d.map_up k n hnk ⟨u, hu⟩ hm hmu,
        d.map_up (k + 1) (n + 2) (by push_cast; omega) ⟨u, hu⟩ hXm hmu', pow_succ',
        Module.End.mul_apply]
    · -- `−` chain interior
      obtain ⟨j, hnj⟩ : ∃ j : ℕ, n + 2 + 2 * (j : ℤ) = -((ℓ : ℤ) + 1) :=
        ⟨((-((ℓ : ℤ) + 3) - n) / 2).toNat, by omega⟩
      have hnk : n + 2 * ((j + 1 : ℕ) : ℤ) = -((ℓ : ℤ) + 1) := by push_cast; omega
      have hXjX : (A.weight.X ^ j) (A.weight.X m) = (A.weight.X ^ (j + 1)) m := by
        rw [← Module.End.mul_apply, ← pow_succ]
      have hmem1 : (A.weight.X ^ (j + 1)) m ∈ A.weight.comp (-((ℓ : ℤ) + 1)) := by
        have hv := chainX_val A n (j + 1) (hjDown n (j + 1) hnk) (j + 1) le_rfl ⟨m, hm⟩
        have hp2 := (chainX A n (j + 1) (hjDown n (j + 1) hnk) (j + 1) le_rfl ⟨m, hm⟩).2
        rw [hv, hnk] at hp2
        exact hp2
      have hmem2 : (A.weight.X ^ j) (A.weight.X m) ∈ A.weight.comp (-((ℓ : ℤ) + 1)) := by
        rw [hXjX]; exact hmem1
      have h1 := d.map_down (j + 1) n hnk hm hmem1
      have h2 := d.map_down j (n + 2) hnj hXm hmem2
      have h3 : (B.weight.X ^ j) (B.weight.X (d.map m)) = (B.weight.X ^ (j + 1)) (d.map m) := by
        rw [← Module.End.mul_apply, ← pow_succ]
      refine chainX_injective B (n + 2) j (hjDown (n + 2) j hnj) j le_rfl
        (d.map_mem (n + 2) _ hXm) (B.weight.X_mem n _ (d.map_mem n m hm)) ?_
      rw [h2, h3, h1]
      exact congrArg (fun x => ((d.ψ 0 x : B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier))
        (Subtype.ext hXjX)
    · -- the `a₋` wall
      subst h
      have h0 : (A.weight.X ^ (0 : ℕ)) m = m := by simp
      have hmem0 : (A.weight.X ^ (0 : ℕ)) m ∈ A.weight.comp (-((ℓ : ℤ) + 1)) := by
        rw [h0]; exact hm
      have h1 := d.map_down 0 (-((ℓ : ℤ) + 1)) (by push_cast; ring) hm hmem0
      have hXmem : A.weight.X m ∈ A.weight.comp (-((ℓ : ℤ) - 1)) := by
        have h' := hXm; rwa [show -((ℓ : ℤ) + 1) + 2 = -((ℓ : ℤ) - 1) by ring] at h'
      have h2 := d.map_mid 0 (by push_cast; omega) (-((ℓ : ℤ) + 1) + 2)
        (by push_cast; ring) ⟨A.weight.X m, hXmem⟩ hXm (by simp)
      have hdm : d.map m = ((d.ψ 0 ⟨m, hm⟩ : B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier) := by
        calc d.map m = (B.weight.X ^ (0 : ℕ)) (d.map m) := by rw [pow_zero]; rfl
          _ = ((d.ψ 0 ⟨(A.weight.X ^ (0 : ℕ)) m, hmem0⟩ :
              B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier) := h1
          _ = _ := congrArg (fun x => ((d.ψ 0 x : B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier))
              (Subtype.ext h0)
      rw [h2, pow_zero, Module.End.one_apply, hdm]
      exact d.edgeAm m hm hXmem
    · -- `⋆` chain interior
      set k : ℕ := ((n + (ℓ : ℤ) - 1) / 2).toNat with hkdef
      have hnk : n = -((ℓ : ℤ) - 1) + 2 * (k : ℤ) := by omega
      have hk : (k : ℤ) ≤ (ℓ : ℤ) - 1 := by omega
      have hk' : ((k + 1 : ℕ) : ℤ) ≤ (ℓ : ℤ) - 1 := by push_cast; omega
      obtain ⟨u, hu, hmu⟩ :=
        chainX_surjective A (-((ℓ : ℤ) - 1)) k (hjMid k hk) k le_rfl (hnk ▸ hm)
      have hmu' : (A.weight.X ^ (k + 1)) u = A.weight.X m := by
        rw [pow_succ', Module.End.mul_apply, hmu]
      rw [d.map_mid k hk n hnk ⟨u, hu⟩ hm hmu,
        d.map_mid (k + 1) hk' (n + 2) (by push_cast; omega) ⟨u, hu⟩ hXm hmu', pow_succ',
        Module.End.mul_apply]
    · -- the `b₊` wall
      subst h
      have hle : ((ℓ - 1 : ℕ) : ℤ) ≤ (ℓ : ℤ) - 1 := by omega
      have hnk : (ℓ : ℤ) - 1 = -((ℓ : ℤ) - 1) + 2 * ((ℓ - 1 : ℕ) : ℤ) := by omega
      obtain ⟨u, hu, hmu⟩ := chainX_surjective A (-((ℓ : ℤ) - 1)) (ℓ - 1)
        (hjMid (ℓ - 1) hle) (ℓ - 1) le_rfl (hnk ▸ hm)
      have hXmp : A.weight.X m ∈ A.weight.comp ((ℓ : ℤ) + 1) := by
        have h' := hXm; rwa [show (ℓ : ℤ) - 1 + 2 = (ℓ : ℤ) + 1 by ring] at h'
      have hXmem : A.weight.X ((A.weight.X ^ (ℓ - 1)) u) ∈ A.weight.comp ((ℓ : ℤ) + 1) := by
        rw [hmu]; exact hXmp
      have h2 := d.map_up 0 ((ℓ : ℤ) - 1 + 2) (by push_cast; omega)
        ⟨A.weight.X m, hXmp⟩ hXm (by simp)
      have hsub : ((d.ψ 2 ⟨A.weight.X m, hXmp⟩ : B.weight.comp ((ℓ : ℤ) + 1)) : B.carrier)
          = ((d.ψ 2 ⟨A.weight.X ((A.weight.X ^ (ℓ - 1)) (u : A.carrier)), hXmem⟩ :
              B.weight.comp ((ℓ : ℤ) + 1)) : B.carrier) :=
        congrArg (fun x => ((d.ψ 2 x : B.weight.comp ((ℓ : ℤ) + 1)) : B.carrier))
          (Subtype.ext (congrArg A.weight.X hmu.symm))
      rw [h2, pow_zero, Module.End.one_apply,
        d.map_mid (ℓ - 1) hle ((ℓ : ℤ) - 1) hnk ⟨u, hu⟩ hm hmu]
      exact hsub.trans (d.edgeBp ⟨u, hu⟩ hXmem)
  · -- off the parity class the component is `⊥`
    have hbot := A.centralCharacter n hp
    rw [hbot, Submodule.mem_bot] at hm
    rw [hm]
    simp

end ExtData

/-- Two linear maps agreeing on every homogeneous component agree.  @census none (helper) -/
theorem eq_of_comp {A B : HCFObj F ℓ} (f g : A.carrier →ₗ[F] B.carrier)
    (h : ∀ (n : ℤ) (m : A.carrier), m ∈ A.weight.comp n → f m = g m) (v : A.carrier) :
    f v = g v := by
  obtain ⟨s, -, hsum⟩ := A.weight.exists_sum_proj v
  rw [← hsum]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun n _ => h n _ (A.weight.proj_mem n v)

namespace ExtData

variable {A B : HCFObj F ℓ} (d : ExtData A B)

/-- The extension commutes with `X`.  @census none (helper) -/
theorem map_X (hℓ : 1 ≤ ℓ) (v : A.carrier) : d.map (A.weight.X v) = B.weight.X (d.map v) :=
  eq_of_comp (d.map.comp A.weight.X) (B.weight.X.comp d.map)
    (fun n m hm => d.map_X_comp hℓ n m hm) v

/-- The extension commutes with every power of `X`.  @census none (helper) -/
theorem map_pow_X_eq (hℓ : 1 ≤ ℓ) (k : ℕ) (v : A.carrier) :
    d.map ((A.weight.X ^ k) v) = (B.weight.X ^ k) (d.map v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, d.map_X hℓ, ih]

/-- `C` commutes with every power of `X`.  @census none (helper) -/
theorem casimir_pow_X {A : HCFObj F ℓ} (k : ℕ) (v : A.carrier) :
    A.weight.casimir ((A.weight.X ^ k) v) = (A.weight.X ^ k) (A.weight.casimir v) := by
  have h := (A.weight.casimir_commute_X.pow_right k).eq
  have h' := congrArg (fun f : Module.End F A.carrier => f v) h
  simpa [Module.End.mul_apply] using h'

/-- The extension commutes with `H`: it preserves the grading and `H` is a scalar there.
@census none (helper) -/
theorem map_H (v : A.carrier) : d.map (A.weight.H v) = B.weight.H (d.map v) := by
  refine eq_of_comp (d.map.comp A.weight.H) (B.weight.H.comp d.map) (fun n m hm => ?_) v
  show d.map (A.weight.H m) = B.weight.H (d.map m)
  rw [A.weight.H_apply n m hm, map_smul, B.weight.H_apply n _ (d.map_mem n m hm)]

/-- The `a₊` wall of `Y`-equivariance — the edge equation `edgeAp`.  @census none (helper) -/
theorem map_Y_wall_plus (hℓ : 1 ≤ ℓ) (m : A.carrier) (hm : m ∈ A.weight.comp ((ℓ : ℤ) + 1)) :
    d.map (A.weight.Y m) = B.weight.Y (d.map m) := by
  have hYm : A.weight.Y m ∈ A.weight.comp ((ℓ : ℤ) - 1) := by
    have h := A.weight.Y_mem _ m hm
    rwa [show (ℓ : ℤ) + 1 - 2 = (ℓ : ℤ) - 1 by ring] at h
  have hle : ((ℓ - 1 : ℕ) : ℤ) ≤ (ℓ : ℤ) - 1 := by omega
  have hnk : (ℓ : ℤ) - 1 = -((ℓ : ℤ) - 1) + 2 * ((ℓ - 1 : ℕ) : ℤ) := by omega
  obtain ⟨u, hu, hmu⟩ := chainX_surjective A (-((ℓ : ℤ) - 1)) (ℓ - 1)
    (hjMid (ℓ - 1) hle) (ℓ - 1) le_rfl (hnk ▸ hYm)
  rw [d.map_mid (ℓ - 1) hle ((ℓ : ℤ) - 1) hnk ⟨u, hu⟩ hYm hmu,
    d.map_up 0 ((ℓ : ℤ) + 1) (by push_cast; omega) ⟨m, hm⟩ hm (by simp), pow_zero,
    Module.End.one_apply]
  exact d.edgeAp ⟨m, hm⟩ ⟨u, hu⟩ hmu

/-- The `b₋` wall of `Y`-equivariance — the edge equation `edgeBm`.  @census none (helper) -/
theorem map_Y_wall_minus (hℓ : 1 ≤ ℓ) (m : A.carrier)
    (hm : m ∈ A.weight.comp (-((ℓ : ℤ) - 1))) :
    d.map (A.weight.Y m) = B.weight.Y (d.map m) := by
  have hYm : A.weight.Y m ∈ A.weight.comp (-((ℓ : ℤ) + 1)) := by
    have h := A.weight.Y_mem _ m hm
    rwa [show -((ℓ : ℤ) - 1) - 2 = -((ℓ : ℤ) + 1) by ring] at h
  have h0 : (A.weight.X ^ (0 : ℕ)) (A.weight.Y m) = A.weight.Y m := by simp
  have hmem0 : (A.weight.X ^ (0 : ℕ)) (A.weight.Y m) ∈ A.weight.comp (-((ℓ : ℤ) + 1)) := by
    rw [h0]; exact hYm
  have h1 : d.map (A.weight.Y m)
      = ((d.ψ 0 ⟨A.weight.Y m, hYm⟩ : B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier) := by
    calc d.map (A.weight.Y m) = (B.weight.X ^ (0 : ℕ)) (d.map (A.weight.Y m)) := by
          rw [pow_zero]; rfl
      _ = ((d.ψ 0 ⟨(A.weight.X ^ (0 : ℕ)) (A.weight.Y m), hmem0⟩ :
            B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier) :=
          d.map_down 0 (-((ℓ : ℤ) + 1)) (by push_cast; ring) hYm hmem0
      _ = _ := congrArg (fun x => ((d.ψ 0 x : B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier))
          (Subtype.ext h0)
  rw [h1, d.map_mid 0 (by push_cast; omega) (-((ℓ : ℤ) - 1)) (by push_cast; ring)
    ⟨m, hm⟩ hm (by simp), pow_zero, Module.End.one_apply]
  exact d.edgeBm m hm hYm

/-- `C`-equivariance at the `+` vertex: `C = ℓ² + 4·φ_{b₊}φ_{a₊}` there.
@census none (helper) -/
theorem map_casimir_plus (hℓ : 1 ≤ ℓ) (m : A.carrier) (hm : m ∈ A.weight.comp ((ℓ : ℤ) + 1)) :
    d.map (A.weight.casimir m) = B.weight.casimir (d.map m) := by
  have hA := A.weight.four_X_Y_apply (ℓ : ℤ) m hm
  have hB := B.weight.four_X_Y_apply (ℓ : ℤ) (d.map m) (d.map_mem _ m hm)
  have hYX : d.map (A.weight.X (A.weight.Y m)) = B.weight.X (B.weight.Y (d.map m)) := by
    rw [d.map_X hℓ, d.map_Y_wall_plus hℓ m hm]
  have e1 : A.weight.casimir m
      = (4 : F) • A.weight.X (A.weight.Y m) + ((((ℓ : ℤ)) : F) ^ 2) • m := by
    rw [hA]; abel
  rw [e1, map_add, map_smul, map_smul, hYX, hB]
  abel

/-- `C`-equivariance at the `−` vertex: `C = ℓ² + 4·φ_{b₋}φ_{a₋}` there.
@census none (helper) -/
theorem map_casimir_minus (hℓ : 1 ≤ ℓ) (m : A.carrier)
    (hm : m ∈ A.weight.comp (-((ℓ : ℤ) + 1))) :
    d.map (A.weight.casimir m) = B.weight.casimir (d.map m) := by
  have hA := A.weight.four_Y_X_apply (ℓ : ℤ) m hm
  have hB := B.weight.four_Y_X_apply (ℓ : ℤ) (d.map m) (d.map_mem _ m hm)
  have hXmem : A.weight.X m ∈ A.weight.comp (-((ℓ : ℤ) - 1)) := by
    have h := A.weight.X_mem _ m hm
    rwa [show -((ℓ : ℤ) + 1) + 2 = -((ℓ : ℤ) - 1) by ring] at h
  have hXY : d.map (A.weight.Y (A.weight.X m)) = B.weight.Y (B.weight.X (d.map m)) := by
    rw [d.map_Y_wall_minus hℓ _ hXmem, d.map_X hℓ]
  have e1 : A.weight.casimir m
      = (4 : F) • A.weight.Y (A.weight.X m) + ((((ℓ : ℤ)) : F) ^ 2) • m := by
    rw [hA]; abel
  rw [e1, map_add, map_smul, map_smul, hXY, hB]
  abel

/-- `C`-equivariance at the `⋆` vertex: `C = ℓ² + 4·φ_{a₋}φ_{b₋}` there.
@census none (helper) -/
theorem map_casimir_star (hℓ : 1 ≤ ℓ) (m : A.carrier)
    (hm : m ∈ A.weight.comp (-((ℓ : ℤ) - 1))) :
    d.map (A.weight.casimir m) = B.weight.casimir (d.map m) := by
  have hm' : m ∈ A.weight.comp (-(ℓ : ℤ) + 1) := by
    rwa [show -(ℓ : ℤ) + 1 = -((ℓ : ℤ) - 1) by ring]
  have hA := A.weight.four_X_Y_apply (-(ℓ : ℤ)) m hm'
  have hB := B.weight.four_X_Y_apply (-(ℓ : ℤ)) (d.map m) (by
    have := d.map_mem _ m hm
    rwa [show -((ℓ : ℤ) - 1) = -(ℓ : ℤ) + 1 by ring] at this)
  have hYX : d.map (A.weight.X (A.weight.Y m)) = B.weight.X (B.weight.Y (d.map m)) := by
    rw [d.map_X hℓ, d.map_Y_wall_minus hℓ m hm]
  have e1 : A.weight.casimir m
      = (4 : F) • A.weight.X (A.weight.Y m)
        + ((((-(ℓ : ℤ)) : ℤ) : F) ^ 2) • m := by
    rw [hA]; abel
  rw [e1, map_add, map_smul, map_smul, hYX, hB]
  abel

/-- **`C`-equivariance everywhere**, propagated along the three `X`-chains from the three vertex
components (`casimir_commute_X`).  @census none (helper) -/
theorem map_casimir_comp (hℓ : 1 ≤ ℓ) (n : ℤ) (m : A.carrier) (hm : m ∈ A.weight.comp n) :
    d.map (A.weight.casimir m) = B.weight.casimir (d.map m) := by
  by_cases hp : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · rcases (show (ℓ : ℤ) + 1 ≤ n ∨ n ≤ -((ℓ : ℤ) + 1) ∨
        (-((ℓ : ℤ) - 1) ≤ n ∧ n ≤ (ℓ : ℤ) - 1) by omega) with h | h | h
    · set k : ℕ := ((n - (ℓ : ℤ) - 1) / 2).toNat with hkdef
      have hnk : n = (ℓ : ℤ) + 1 + 2 * (k : ℤ) := by omega
      obtain ⟨u, hu, hmu⟩ := chainX_surjective A ((ℓ : ℤ) + 1) k (hjUp k) k le_rfl (hnk ▸ hm)
      calc d.map (A.weight.casimir m)
          = d.map (A.weight.casimir ((A.weight.X ^ k) u)) := by rw [hmu]
        _ = d.map ((A.weight.X ^ k) (A.weight.casimir u)) := by rw [casimir_pow_X]
        _ = (B.weight.X ^ k) (d.map (A.weight.casimir u)) := d.map_pow_X_eq hℓ _ _
        _ = (B.weight.X ^ k) (B.weight.casimir (d.map u)) := by
            rw [d.map_casimir_plus hℓ u hu]
        _ = B.weight.casimir ((B.weight.X ^ k) (d.map u)) := (casimir_pow_X k _).symm
        _ = B.weight.casimir (d.map ((A.weight.X ^ k) u)) := by rw [d.map_pow_X_eq hℓ]
        _ = B.weight.casimir (d.map m) := by rw [hmu]
    · set k : ℕ := ((-((ℓ : ℤ) + 1) - n) / 2).toNat with hkdef
      have hnk : n + 2 * (k : ℤ) = -((ℓ : ℤ) + 1) := by omega
      have hXmem : (A.weight.X ^ k) m ∈ A.weight.comp (-((ℓ : ℤ) + 1)) := by
        have hv := chainX_val A n k (hjDown n k hnk) k le_rfl ⟨m, hm⟩
        have hp2 := (chainX A n k (hjDown n k hnk) k le_rfl ⟨m, hm⟩).2
        rw [hv, hnk] at hp2
        exact hp2
      refine chainX_injective B n k (hjDown n k hnk) k le_rfl
        (d.map_mem n _ (casimir_mem_comp A.weight n m hm))
        (casimir_mem_comp B.weight n _ (d.map_mem n m hm)) ?_
      calc (B.weight.X ^ k) (d.map (A.weight.casimir m))
          = d.map ((A.weight.X ^ k) (A.weight.casimir m)) := (d.map_pow_X_eq hℓ k _).symm
        _ = d.map (A.weight.casimir ((A.weight.X ^ k) m)) := by rw [casimir_pow_X]
        _ = B.weight.casimir (d.map ((A.weight.X ^ k) m)) := d.map_casimir_minus hℓ _ hXmem
        _ = B.weight.casimir ((B.weight.X ^ k) (d.map m)) := by rw [d.map_pow_X_eq hℓ]
        _ = (B.weight.X ^ k) (B.weight.casimir (d.map m)) := casimir_pow_X k _
    · set k : ℕ := ((n + (ℓ : ℤ) - 1) / 2).toNat with hkdef
      have hnk : n = -((ℓ : ℤ) - 1) + 2 * (k : ℤ) := by omega
      have hk : (k : ℤ) ≤ (ℓ : ℤ) - 1 := by omega
      obtain ⟨u, hu, hmu⟩ :=
        chainX_surjective A (-((ℓ : ℤ) - 1)) k (hjMid k hk) k le_rfl (hnk ▸ hm)
      calc d.map (A.weight.casimir m)
          = d.map (A.weight.casimir ((A.weight.X ^ k) u)) := by rw [hmu]
        _ = d.map ((A.weight.X ^ k) (A.weight.casimir u)) := by rw [casimir_pow_X]
        _ = (B.weight.X ^ k) (d.map (A.weight.casimir u)) := d.map_pow_X_eq hℓ _ _
        _ = (B.weight.X ^ k) (B.weight.casimir (d.map u)) := by
            rw [d.map_casimir_star hℓ u hu]
        _ = B.weight.casimir ((B.weight.X ^ k) (d.map u)) := (casimir_pow_X k _).symm
        _ = B.weight.casimir (d.map ((A.weight.X ^ k) u)) := by rw [d.map_pow_X_eq hℓ]
        _ = B.weight.casimir (d.map m) := by rw [hmu]
  · have hbot := A.centralCharacter n hp
    rw [hbot, Submodule.mem_bot] at hm
    rw [hm]
    simp

/-- `C`-equivariance, globally.  @census none (helper) -/
theorem map_casimir (hℓ : 1 ≤ ℓ) (v : A.carrier) :
    d.map (A.weight.casimir v) = B.weight.casimir (d.map v) :=
  eq_of_comp (d.map.comp A.weight.casimir) (B.weight.casimir.comp d.map)
    (fun n m hm => d.map_casimir_comp hℓ n m hm) v

/-- **The extension commutes with `Y`.**  Away from the two `Y`-walls this is `4XY = C − j²` plus
`X`- and `C`-equivariance and the injectivity of `X` off `±ℓ`; at the walls it is `edgeAp` and
`edgeBm`.  @census none (helper) -/
theorem map_Y_comp (hℓ : 1 ≤ ℓ) (n : ℤ) (m : A.carrier) (hm : m ∈ A.weight.comp n) :
    d.map (A.weight.Y m) = B.weight.Y (d.map m) := by
  by_cases hp : (n - ((ℓ : ℤ) - 1)) % 2 = 0
  · by_cases h1 : n = (ℓ : ℤ) + 1
    · subst h1; exact d.map_Y_wall_plus hℓ m hm
    · by_cases h2 : n = -((ℓ : ℤ) - 1)
      · subst h2; exact d.map_Y_wall_minus hℓ m hm
      · have hj : ((n - 1) : ℤ) ^ 2 ≠ ((ℓ : ℤ)) ^ 2 := by
          intro hc
          have hfac : (n - 1 - (ℓ : ℤ)) * (n - 1 + (ℓ : ℤ)) = 0 := by linear_combination hc
          rcases mul_eq_zero.mp hfac with hh | hh
          · exact h1 (by omega)
          · exact h2 (by omega)
        have hjq := sq_ne_sq_of (F := F) (n - 1) hj
        have hm' : m ∈ A.weight.comp ((n - 1) + 1) := by rwa [show n - 1 + 1 = n by ring]
        have hA := A.weight.four_X_Y_apply (n - 1) m hm'
        have hB := B.weight.four_X_Y_apply (n - 1) (d.map m) (by
          have hmm := d.map_mem n m hm
          rwa [show n - 1 + 1 = n by ring])
        have hYmem : A.weight.Y m ∈ A.weight.comp (n - 2) := A.weight.Y_mem n m hm
        have e4 : (4 : F) • B.weight.X (d.map (A.weight.Y m))
            = (4 : F) • B.weight.X (B.weight.Y (d.map m)) := by
          calc (4 : F) • B.weight.X (d.map (A.weight.Y m))
              = (4 : F) • d.map (A.weight.X (A.weight.Y m)) := by rw [d.map_X hℓ]
            _ = d.map ((4 : F) • A.weight.X (A.weight.Y m)) := (map_smul _ _ _).symm
            _ = d.map (A.weight.casimir m - (((n - 1 : ℤ) : F) ^ 2) • m) := by rw [hA]
            _ = B.weight.casimir (d.map m)
                  - (((n - 1 : ℤ) : F) ^ 2) • d.map m := by
                rw [map_sub, map_smul, d.map_casimir hℓ]
            _ = (4 : F) • B.weight.X (B.weight.Y (d.map m)) := hB.symm
        have e5 : B.weight.X (d.map (A.weight.Y m)) = B.weight.X (B.weight.Y (d.map m)) :=
          smul_right_injective B.carrier (by norm_num : (4 : F) ≠ 0) e4
        have h0 : B.weight.X (d.map (A.weight.Y m) - B.weight.Y (d.map m)) = 0 := by
          rw [map_sub, e5, sub_self]
        have hmem : d.map (A.weight.Y m) - B.weight.Y (d.map m) ∈ B.weight.comp (n - 1 - 1) := by
          rw [show n - 1 - 1 = n - 2 by ring]
          exact Submodule.sub_mem _ (d.map_mem _ _ hYmem) (B.weight.Y_mem n _ (d.map_mem n m hm))
        exact sub_eq_zero.mp (X_injective_on_comp (A := B) (n - 1) hjq _ hmem h0)
  · have hbot := A.centralCharacter n hp
    rw [hbot, Submodule.mem_bot] at hm
    rw [hm]
    simp

/-- The extension commutes with `Y`, globally.  @census none (helper) -/
theorem map_Y (hℓ : 1 ≤ ℓ) (v : A.carrier) : d.map (A.weight.Y v) = B.weight.Y (d.map v) :=
  eq_of_comp (d.map.comp A.weight.Y) (B.weight.Y.comp d.map)
    (fun n m hm => d.map_Y_comp hℓ n m hm) v

/-- **Engine `E4`**: a compatible triple of component maps *is* the restriction of a morphism of
`HC_λ(𝔤,K)_{ℚ[√-1]}`.  @census none (helper) -/
noncomputable def hom (hℓ : 1 ≤ ℓ) : A ⟶ B where
  toLinearMap := d.map
  map_H := d.map_H
  map_X := d.map_X hℓ
  map_Y := d.map_Y hℓ
  map_comp := d.map_mem

/-- `E4`'s morphism restricts to `ψ` at the `−` vertex.  @census none (helper) -/
theorem map_at_minus (m : A.carrier) (hm : m ∈ A.weight.comp (-((ℓ : ℤ) + 1))) :
    d.map m = ((d.ψ 0 ⟨m, hm⟩ : B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier) := by
  have h0 : (A.weight.X ^ (0 : ℕ)) m = m := by simp
  have hmem0 : (A.weight.X ^ (0 : ℕ)) m ∈ A.weight.comp (-((ℓ : ℤ) + 1)) := by
    rw [h0]; exact hm
  calc d.map m = (B.weight.X ^ (0 : ℕ)) (d.map m) := by rw [pow_zero]; rfl
    _ = ((d.ψ 0 ⟨(A.weight.X ^ (0 : ℕ)) m, hmem0⟩ :
          B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier) :=
        d.map_down 0 (-((ℓ : ℤ) + 1)) (by push_cast; ring) hm hmem0
    _ = _ := congrArg (fun x => ((d.ψ 0 x : B.weight.comp (-((ℓ : ℤ) + 1))) : B.carrier))
        (Subtype.ext h0)

/-- `E4`'s morphism restricts to `ψ` at the `⋆` vertex.  @census none (helper) -/
theorem map_at_star (hℓ : 1 ≤ ℓ) (m : A.carrier) (hm : m ∈ A.weight.comp (-((ℓ : ℤ) - 1))) :
    d.map m = ((d.ψ 1 ⟨m, hm⟩ : B.weight.comp (-((ℓ : ℤ) - 1))) : B.carrier) := by
  rw [d.map_mid 0 (by push_cast; omega) (-((ℓ : ℤ) - 1)) (by push_cast; ring) ⟨m, hm⟩ hm
    (by simp), pow_zero, Module.End.one_apply]
  rfl

/-- `E4`'s morphism restricts to `ψ` at the `+` vertex.  @census none (helper) -/
theorem map_at_plus (hℓ : 1 ≤ ℓ) (m : A.carrier) (hm : m ∈ A.weight.comp ((ℓ : ℤ) + 1)) :
    d.map m = ((d.ψ 2 ⟨m, hm⟩ : B.weight.comp ((ℓ : ℤ) + 1)) : B.carrier) := by
  rw [d.map_up 0 ((ℓ : ℤ) + 1) (by push_cast; omega) ⟨m, hm⟩ hm (by simp), pow_zero,
    Module.End.one_apply]
  rfl

/-- **`E4`, as the fullness statement**: `E_F_map_ψ` of the extension is the given triple.
@census none (helper) -/
theorem hom_psi (hℓ : 1 ≤ ℓ) (v : Fin 3) (m : A.weight.comp (vtxIdx ℓ v)) :
    E_F_map_ψ ℓ (d.hom hℓ) v m = d.ψ v m := by
  refine Subtype.ext ?_
  show d.map (m : A.carrier) = _
  fin_cases v
  · exact d.map_at_minus (m : A.carrier) m.2
  · exact d.map_at_star hℓ (m : A.carrier) m.2
  · exact d.map_at_plus hℓ (m : A.carrier) m.2

/-- **`E4`'s input, from a morphism of quiver representations.**  A triple commuting with the four
maps `φ_{a₋}, φ_{b₋}, φ_{a₊}, φ_{b₊}` of `E_F_edge` is `ExtData`: the `±` walls are `X` and `Y`
verbatim, and the `⋆`-side edges are the same after clearing the normalisation `X⋆ = γ⋆⁻¹X^{ℓ-1}`
and its chosen inverse `X⋆⁻¹` (`γ⋆ ≠ 0`, `gammaStarF_ne_zero`).  @census none (helper) -/
noncomputable def ofEdges {A B : HCFObj F ℓ} (hℓ : 1 ≤ ℓ)
    (ψ : ∀ v : Fin 3, A.weight.comp (vtxIdx ℓ v) →ₗ[F] B.weight.comp (vtxIdx ℓ v))
    (hedge : ∀ (e : Fin 4) (m : V3 A.setup (RQuiver.gelfand.source e)),
      ψ (RQuiver.gelfand.target e) (E_F_edge A.setup (A.setup.starInverses hℓ) hℓ e m)
        = E_F_edge B.setup (B.setup.starInverses hℓ) hℓ e (ψ (RQuiver.gelfand.source e) m)) :
    ExtData A B where
  ψ := ψ
  edgeAm m hm h := congrArg Subtype.val (hedge 0 ⟨m, hm⟩)
  edgeBm m hm h := congrArg Subtype.val (hedge 1 ⟨m, hm⟩)
  edgeBp u h := by
    have hγ : gammaStarF F ℓ ≠ 0 := gammaStarF_ne_zero ℓ
    have hAv : A.weight.X ((xStar A.setup) (u : A.carrier))
        = (gammaStarF F ℓ)⁻¹ • A.weight.X ((A.weight.X ^ (ℓ - 1)) (u : A.carrier)) := by
      show A.weight.X ((gammaStarF F ℓ)⁻¹ • (A.weight.X ^ (ℓ - 1)) (u : A.carrier)) = _
      rw [map_smul]
    have h3 : ψ 2 (E_F_edge A.setup (A.setup.starInverses hℓ) hℓ 3 u)
        = E_F_edge B.setup (B.setup.starInverses hℓ) hℓ 3 (ψ 1 u) := hedge 3 u
    have hEq : (E_F_edge A.setup (A.setup.starInverses hℓ) hℓ 3 u :
          A.weight.comp (vtxIdx ℓ 2))
        = (gammaStarF F ℓ)⁻¹ • (⟨A.weight.X ((A.weight.X ^ (ℓ - 1)) (u : A.carrier)), h⟩ :
            A.weight.comp (vtxIdx ℓ 2)) := Subtype.ext hAv
    have hLv : ((ψ 2 (E_F_edge A.setup (A.setup.starInverses hℓ) hℓ 3 u) :
          B.weight.comp (vtxIdx ℓ 2)) : B.carrier)
        = (gammaStarF F ℓ)⁻¹ • ((ψ 2 ⟨A.weight.X ((A.weight.X ^ (ℓ - 1)) (u : A.carrier)), h⟩ :
            B.weight.comp (vtxIdx ℓ 2)) : B.carrier) := by
      rw [hEq]
      exact congrArg Subtype.val (LinearMap.map_smul _ _ _)
    have hRv : ((E_F_edge B.setup (B.setup.starInverses hℓ) hℓ 3 (ψ 1 u) :
          B.weight.comp (vtxIdx ℓ 2)) : B.carrier)
        = (gammaStarF F ℓ)⁻¹ • B.weight.X ((B.weight.X ^ (ℓ - 1))
            ((ψ 1 u : B.weight.comp (vtxIdx ℓ 1)) : B.carrier)) := by
      show B.weight.X ((gammaStarF F ℓ)⁻¹ • (B.weight.X ^ (ℓ - 1)) _) = _
      rw [map_smul]
      rfl
    have hfin : (gammaStarF F ℓ)⁻¹ •
          ((ψ 2 ⟨A.weight.X ((A.weight.X ^ (ℓ - 1)) (u : A.carrier)), h⟩ :
            B.weight.comp (vtxIdx ℓ 2)) : B.carrier)
        = (gammaStarF F ℓ)⁻¹ • B.weight.X ((B.weight.X ^ (ℓ - 1))
            ((ψ 1 u : B.weight.comp (vtxIdx ℓ 1)) : B.carrier)) := by
      rw [← hLv, ← hRv]
      exact congrArg Subtype.val h3
    exact smul_right_injective B.carrier (inv_ne_zero hγ) hfin
  edgeAp m u hmu := by
    have hγ : gammaStarF F ℓ ≠ 0 := gammaStarF_ne_zero ℓ
    have hYm : A.weight.Y (m : A.carrier) ∈ A.weight.comp ((ℓ : ℤ) - 1) :=
      y_mem (Q := A.setup) (m := (ℓ : ℤ) + 1) (by ring) m.2
    have hYmB : B.weight.Y ((ψ 2 m : B.weight.comp (vtxIdx ℓ 2)) : B.carrier)
        ∈ B.weight.comp ((ℓ : ℤ) - 1) :=
      y_mem (Q := B.setup) (m := (ℓ : ℤ) + 1) (by ring) (ψ 2 m).2
    have hclear : ∀ (C : HCFObj F ℓ) (z : C.carrier), z ∈ C.weight.comp ((ℓ : ℤ) - 1) →
        (C.weight.X ^ (ℓ - 1)) ((C.setup.starInverses hℓ).xStarInv z) = gammaStarF F ℓ • z := by
      intro C z hz
      have hx : (gammaStarF F ℓ)⁻¹ • (C.weight.X ^ (ℓ - 1))
          ((C.setup.starInverses hℓ).xStarInv z) = z :=
        xStar_xStarInv C.setup (C.setup.starInverses hℓ) z hz
      calc (C.weight.X ^ (ℓ - 1)) ((C.setup.starInverses hℓ).xStarInv z)
          = gammaStarF F ℓ • ((gammaStarF F ℓ)⁻¹ • (C.weight.X ^ (ℓ - 1))
              ((C.setup.starInverses hℓ).xStarInv z)) := by
            rw [smul_smul, mul_inv_cancel₀ hγ, one_smul]
        _ = gammaStarF F ℓ • z := by rw [hx]
    have hmem1 : (A.setup.starInverses hℓ).xStarInv (A.weight.Y (m : A.carrier))
        ∈ A.weight.comp (-((ℓ : ℤ) - 1)) :=
      StarInverses.xStarInv_mem (A.setup.starInverses hℓ) hYm
    have hu : (A.setup.starInverses hℓ).xStarInv (A.weight.Y (m : A.carrier))
        = gammaStarF F ℓ • (u : A.carrier) := by
      refine chainX_injective A (-((ℓ : ℤ) - 1)) (ℓ - 1) (hjMid (ℓ - 1) (by omega)) (ℓ - 1)
        le_rfl hmem1 (Submodule.smul_mem _ _ u.2) ?_
      rw [hclear A _ hYm, map_smul, hmu]
    have hEq : (E_F_edge A.setup (A.setup.starInverses hℓ) hℓ 2 m :
        A.weight.comp (vtxIdx ℓ 1)) = gammaStarF F ℓ • u := Subtype.ext hu
    have h2 : ψ 1 (E_F_edge A.setup (A.setup.starInverses hℓ) hℓ 2 m)
        = E_F_edge B.setup (B.setup.starInverses hℓ) hℓ 2 (ψ 2 m) := hedge 2 m
    have hLv : ((ψ 1 (E_F_edge A.setup (A.setup.starInverses hℓ) hℓ 2 m) :
          B.weight.comp (vtxIdx ℓ 1)) : B.carrier)
        = gammaStarF F ℓ • ((ψ 1 u : B.weight.comp (vtxIdx ℓ 1)) : B.carrier) := by
      rw [hEq]
      exact congrArg Subtype.val (LinearMap.map_smul _ _ _)
    have hRv : ((E_F_edge B.setup (B.setup.starInverses hℓ) hℓ 2 (ψ 2 m) :
          B.weight.comp (vtxIdx ℓ 1)) : B.carrier)
        = (B.setup.starInverses hℓ).xStarInv
            (B.weight.Y ((ψ 2 m : B.weight.comp (vtxIdx ℓ 2)) : B.carrier)) := rfl
    have hfin : gammaStarF F ℓ • ((ψ 1 u : B.weight.comp (vtxIdx ℓ 1)) : B.carrier)
        = (B.setup.starInverses hℓ).xStarInv
            (B.weight.Y ((ψ 2 m : B.weight.comp (vtxIdx ℓ 2)) : B.carrier)) := by
      rw [← hLv, ← hRv]
      exact congrArg Subtype.val h2
    have h5 := congrArg (fun z => (B.weight.X ^ (ℓ - 1)) z) hfin
    simp only [map_smul] at h5
    rw [hclear B _ hYmB] at h5
    exact smul_right_injective B.carrier hγ h5

end ExtData

/-- **Engine `E4`, packaged: `𝔼_{ℚ[√-1]}` is full on morphisms.**  Every triple of maps on the
three vertex components commuting with the four edges of `ex:gelfand` is the restriction of a
morphism of `HC_λ(𝔤,K)_{ℚ[√-1]}` — the converse of `E1`'s `eq_of_eq_on_V3`, and the surjectivity
half that `RQ-5.02` (the split case) and `RQ-5.05-C7` (through Galois descent for `Hom`) both need.

@census none (helper; engine `E4`)
@clauses   RQ2-5.02-S-O7g, RQ2-5.24-S-TW1 -/
theorem exists_hom_of_edges {A B : HCFObj F ℓ} (hℓ : 1 ≤ ℓ)
    (ψ : ∀ v : Fin 3, A.weight.comp (vtxIdx ℓ v) →ₗ[F] B.weight.comp (vtxIdx ℓ v))
    (hedge : ∀ (e : Fin 4) (m : V3 A.setup (RQuiver.gelfand.source e)),
      ψ (RQuiver.gelfand.target e) (E_F_edge A.setup (A.setup.starInverses hℓ) hℓ e m)
        = E_F_edge B.setup (B.setup.starInverses hℓ) hℓ e (ψ (RQuiver.gelfand.source e) m)) :
    ∃ f : A ⟶ B, ∀ (v : Fin 3) (m : A.weight.comp (vtxIdx ℓ v)),
      E_F_map_ψ ℓ f v m = ψ v m :=
  ⟨(ExtData.ofEdges hℓ ψ hedge).hom hℓ,
    fun v m => (ExtData.ofEdges hℓ ψ hedge).hom_psi hℓ v m⟩

end E4Extend

end E4

section Functor2

open CategoryTheory

variable (ℓ) (hℓ : 1 ≤ ℓ)


/-! ### `RQ-5.02` — the lifted functor, its fullness and its faithfulness

`E_F` lands in `Rep^nil` with the relation (`E_F_isNilpotent`, `E_F_rep_relation`), so it
factors through the full subcategory; the factorisation `E_FNil` is what `E_F_equivalence`
has to exhibit as an equivalence, and `E_FNil_ι` is the pin, `rfl`.  `E1` and `E4` give the
two fully-faithfulness halves outright, so **the whole residue of `RQ-5.02` is essential
surjectivity** — `E_F_equivalence_of_essSurj` isolates exactly that hypothesis.
`stages/S8/DESIGN-NOTES.md` §18.3. -/

/-- `𝔼_{ℚ[√-1]}(M)` is nilpotent and satisfies `ex:gelfand`'s relation (`RQ-5.01-C7`, `C8`).
@census none (helper) -/
theorem E_F_obj_mem (A : HCFObj F ℓ) : RepNilRelSplit F (E_F_obj ℓ hℓ A) :=
  ⟨E_F_isNilpotent A.setup (A.setup.starInverses hℓ) hℓ,
    E_F_rep_relation A.setup (A.setup.starInverses hℓ) hℓ⟩

/-- **`𝔼_{ℚ[√-1]}` into `Rep^nil` with the relation** — `E_F` corestricted to the full
subcategory `E_F_equivalence`'s target is.  @census none (helper) -/
noncomputable def E_FNil : HCF F ℓ ⥤ (RepNilRelSplit F).FullSubcategory :=
  ObjectProperty.lift _ (E_F (F := F) ℓ hℓ) (E_F_obj_mem ℓ hℓ)

/-- The corestriction is a corestriction, on the nose.  @census none (helper) -/
theorem E_FNil_ι :
    E_FNil (F := F) ℓ hℓ ⋙ (RepNilRelSplit F).ι = E_F (F := F) ℓ hℓ := rfl

/-- **`RQ-5.02`, faithfulness** — `E1`: a morphism of `HC_λ(𝔤,K)_{ℚ[√-1]}` is determined by its
restrictions to the three vertex components.  @census none (helper) -/
theorem E_FNil_faithful : (E_FNil (F := F) ℓ hℓ).Faithful := by
  constructor
  intro A B f g hfg
  refine eq_of_eq_on_V3 f g (fun v m hm => ?_)
  have h1 : (E_F_map ℓ hℓ f).ψ = (E_F_map ℓ hℓ g).ψ :=
    congrArg (fun (u : (E_FNil (F := F) ℓ hℓ).obj A ⟶ (E_FNil (F := F) ℓ hℓ).obj B) => u.hom.ψ) hfg
  exact congrArg (fun (T : V3 A.setup v →ₗ[F] V3 B.setup v) =>
    ((T ⟨m, hm⟩ : V3 B.setup v) : B.carrier)) (congrFun h1 v)

/-- **`RQ-5.02`, fullness** — `E4`: every compatible triple of component maps comes from a
morphism.  @census none (helper) -/
theorem E_FNil_full : (E_FNil (F := F) ℓ hℓ).Full := by
  constructor
  intro A B u
  obtain ⟨f, hf⟩ := exists_hom_of_edges (A := A) (B := B) hℓ u.hom.ψ (fun e m => u.hom.edge e m)
  refine ⟨f, ?_⟩
  apply ObjectProperty.hom_ext
  exact RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun m => hf v m)

/-- **`RQ-5.02` reduced to essential surjectivity.**  Given that every nilpotent
finite-dimensional `ℚ[√-1]`-rational representation of the Gelfand quiver satisfying the relation
is isomorphic to some `𝔼_{ℚ[√-1]}(M)`, the equivalence follows: `Functor.asEquivalence`'s functor
**is** `E_FNil` by `rfl`, and `E_FNil ⋙ ι = E_F` is `rfl` too, so the pin
`RQ-2.29` uses holds on the nose.  @census none (helper) -/
theorem equivalence_of_essSurj (hE : (E_FNil (F := F) ℓ hℓ).EssSurj) :
    ∃ e : HCF F ℓ ≌ (RepNilRelSplit F).FullSubcategory,
      e.functor ⋙ (RepNilRelSplit F).ι = E_F (F := F) ℓ hℓ := by
  haveI := E_FNil_full (F := F) ℓ hℓ
  haveI := E_FNil_faithful (F := F) ℓ hℓ
  haveI := hE
  haveI : (E_FNil (F := F) ℓ hℓ).IsEquivalence := { }
  exact ⟨(E_FNil (F := F) ℓ hℓ).asEquivalence, rfl⟩

end Functor2

end RationalQuivers.Gelfand.Split
