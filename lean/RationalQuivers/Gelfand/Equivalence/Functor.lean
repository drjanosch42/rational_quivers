module

public import RationalQuivers.Gelfand.Equivalence.WellDefined

@[expose] public section

/-!
# functoriality of `𝔼_E` (§5.3, Step O-15)

`E_E_functorial` (`rmk:stabilizationaddenda`(i): morphisms commute with the stabilizations), the
engine functor `E_QFunctor`, and the native functor `E_EGel : HC ℓ E D ⥤ Rep^nil(Γ_E)` (`ℓ ≥ 1`).

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Equivalence.lean (§Functor, §Clauses)` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.Equivalence.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

*(2026-10-21, O-V2-6 round 2.)*  The helper `E_Q_spec` bundles `C1` and `C5`, which the
parenthesis of its `@census` field names by their v1 names `E_Q_wellDefined` and `E_Q_functorial`.
The relocation renamed them `E_E_wellDefined` and `E_E_functorial`, as the T3 `DECL-ALLOWLIST.tsv`
records.

@census none (module)
-/

namespace RationalQuivers.Gelfand.Equivalence

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {Dq : SqrtNegOneExt E}
open scoped TensorProduct Classical

variable {ℓ : ℕ}

/-! ### `𝔼_ℚ` on morphisms, and as a functor -/

section Functor

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2) (hℓ : 1 ≤ ℓ)

/-- `𝔼_ℚ(f)`: the restrictions of a morphism to the three vertex spaces, a morphism of rational
representations by the edge compatibility of `𝔼_{ℚ[√-1]}(f)` and the functoriality of the limits
(`HomSpec`, clause `C5`).  @census none (helper) -/
noncomputable def E_Q_hom {A B : HCEObj ℓ E Dq} (hA : Gelfand.RationalStructure.ObjSpec hcard hℓ A) (hB : Gelfand.RationalStructure.ObjSpec hcard hℓ B)
    (f : A ⟶ B)
    (hf : Gelfand.RationalStructure.HomSpec hℓ f) :
    RationalQuiver.Rep.Hom (E_Q_rep hcard hℓ A hA) (E_Q_rep hcard hℓ B hB) where
  ψ v := Split.E_F_map_ψ ℓ ((GF.baseChangeE ℓ E Dq).map f) v
  edge e m := Split.E_F_map_edge ℓ hℓ ((GF.baseChangeE ℓ E Dq).map f) e m
  rational σ v m := by
    obtain ⟨m, hm⟩ := m
    refine Subtype.ext ?_
    show f.toLinearMap (galAct hℓ A σ v m) = galAct hℓ B σ v (f.toLinearMap m)
    by_cases hσ : σ = 1
    · subst hσ; rw [galAct_one hℓ A v, galAct_one hℓ B v]
    · rw [galAct_of_ne hℓ A hσ v, galAct_of_ne hℓ B hσ v]
      show f.toLinearMap (A.setup.conj (Gelfand.RationalStructure.limAt hℓ A v m)) = B.setup.conj (Gelfand.RationalStructure.limAt hℓ B v (f.toLinearMap m))
      rw [f.map_conj, hf v m]

/-- **`𝔼_ℚ` as a functor** `HC_λ(𝔤,K)_ℚ ⥤ Rep^nil(Γ_ℚ)` — the assignment of
`thm:EEQQequivalence`, given its specification (`E_QSpec`: `C1`, `C2`, `C4`, `C5` and
`RQ-5.01-C7`/`C8`).  Its object map is `E_Q_rep`, its morphism map `E_Q_hom`; functoriality is
componentwise `rfl`, as restriction is functorial.

@census    none (auxiliary; the functor of `RQ-5.05`, clauses `RQ-5.05-C1`, `RQ-5.05-C5`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C5
@imports   none
@divergence none -/
noncomputable def E_QFunctor (h : Gelfand.RationalStructure.E_QSpec hcard hℓ) : HCEObj ℓ E Dq ⥤ Gelfand.RationalStructure.RepNilQ hcard where
  obj A := E_Q_obj hcard hℓ A (h.1 A)
  map f := ⟨E_Q_hom hcard hℓ (h.1 _) (h.1 _) f (h.2 _ _ f)⟩
  map_id A := by
    apply ObjectProperty.hom_ext
    exact RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)

end Functor

section Clauses

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)
variable (hℓ : 1 ≤ ℓ) (A : HCEObj ℓ E Dq)

/-- **`RQ-5.05-C5`** — `𝔼_ℚ` is **functorial**: a morphism of Harish-Chandra modules commutes with
the three unipotent stabilizations (`HomSpec`), hence induces a morphism of the rational
representations.  The source: "follows inductively from the recursive process of unipotent
stabilization using the commutative diagrams `eq:normalizedcomparison`,
`eq:conjugatenormalizedcomparison`, `eq:firstiteration` and in the limit case `eq:limitdiagram`."

@census    none (auxiliary; discharges census clause `RQ-5.05-C5`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C5
@imports   none
@divergence none
@clauses   RQ2-5.12-S-O15 -/
theorem E_E_functorial {B : HCEObj ℓ E Dq} (f : A ⟶ B) : Gelfand.RationalStructure.HomSpec hℓ f := by
  -- `lim_natural` (`Gelfand/RationalStructure/Stabilization.lean`; v1's
  -- `Gelfand/Stabilization.lean`, deleted at WP-13; 2026-10-21 note, O-V2-6 round 2) at each of
  -- the three runs, plus `toEnd_apply_proj`
  -- + `WeightData.proj_comm_of_map` to pass from the component statement to `HomSpec`'s `∀ m`.
  -- The intertwining data at `k = 0` is `map_tMinus` (`f` commutes with the Casimir, hence with
  -- `T₋`) and `map_xStar` (`f` commutes with `X`, hence with `X⋆`).
  have key : ∀ (CA : Gelfand.RationalStructure.StabInput A.setup) (CB : Gelfand.RationalStructure.StabInput B.setup), CB.idxPlus = CA.idxPlus →
      (∀ u ∈ A.setup.weight.comp CA.idxPlus,
         f.toLinearMap (CA.limPlus u) = CB.limPlus (f.toLinearMap u)) →
      ∀ m : A.carrier, f.toLinearMap (CA.limPlus m) = CB.limPlus (f.toLinearMap m) := by
    intro CA CB hidx hnat m
    have h1 : CA.limPlus m = CA.limPlus (A.setup.weight.proj CA.idxPlus m) :=
      Gelfand.RationalStructure.toEnd_apply_proj (CA.limT).1 m
    have h2 : CB.limPlus (f.toLinearMap m)
        = CB.limPlus (B.setup.weight.proj CB.idxPlus (f.toLinearMap m)) :=
      Gelfand.RationalStructure.toEnd_apply_proj (CB.limT).1 _
    have h3 : B.setup.weight.proj CB.idxPlus (f.toLinearMap m)
        = f.toLinearMap (A.setup.weight.proj CA.idxPlus m) := by
      rw [hidx]
      exact HC.WeightData.proj_comm_of_map A.setup.weight B.setup.weight f.toLinearMap
        (fun n v hv => f.map_comp n v hv) CA.idxPlus m
    rw [h1, h2, h3, hnat _ (A.setup.weight.proj_mem CA.idxPlus m)]
  have htM : ∀ v : A.carrier,
      f.toLinearMap (Split.tMinus A.setup.toQiSetup v) = Split.tMinus B.setup.toQiSetup (f.toLinearMap v) :=
    Gelfand.RationalStructure.map_tMinus f.toLinearMap f.map_H f.map_X f.map_Y
  have hxS : ∀ v : A.carrier,
      f.toLinearMap (Split.xStar A.setup.toQiSetup v) = Split.xStar B.setup.toQiSetup (f.toLinearMap v) :=
    Gelfand.RationalStructure.map_xStar f.toLinearMap f.map_X
  obtain ⟨hpPA, hmPA, nPA, hnilPA, hnPA⟩ := Gelfand.RationalStructure.stab_prereq A.setup hℓ (Gelfand.RationalStructure.inputPlus A.setup) (by simp)
  obtain ⟨hpMA, hmMA, nMA, hnilMA, hnMA⟩ := Gelfand.RationalStructure.stab_prereq A.setup hℓ (Gelfand.RationalStructure.inputMinus A.setup) (by simp)
  obtain ⟨hpSA, hmSA, nSA, hnilSA, hnSA⟩ := Gelfand.RationalStructure.stab_prereq A.setup hℓ (Gelfand.RationalStructure.inputStar A.setup hℓ) (by simp)
  obtain ⟨hpPB, hmPB, nPB, hnilPB, hnPB⟩ := Gelfand.RationalStructure.stab_prereq B.setup hℓ (Gelfand.RationalStructure.inputPlus B.setup) (by simp)
  obtain ⟨hpMB, hmMB, nMB, hnilMB, hnMB⟩ := Gelfand.RationalStructure.stab_prereq B.setup hℓ (Gelfand.RationalStructure.inputMinus B.setup) (by simp)
  obtain ⟨hpSB, hmSB, nSB, hnilSB, hnSB⟩ := Gelfand.RationalStructure.stab_prereq B.setup hℓ (Gelfand.RationalStructure.inputStar B.setup hℓ) (by simp)
  intro v
  fin_cases v
  · exact key (Gelfand.RationalStructure.inputMinus A.setup) (Gelfand.RationalStructure.inputMinus B.setup) rfl
      (Gelfand.RationalStructure.lim_natural _ _ f.toLinearMap f.map_comp f.map_conj rfl rfl
        (fun u _ => htM u) (fun _ _ => rfl) hpMA hmMA hnilMA hnMA hpMB hmMB hnilMB hnMB)
  · exact key (Gelfand.RationalStructure.inputStar A.setup hℓ) (Gelfand.RationalStructure.inputStar B.setup hℓ) rfl
      (Gelfand.RationalStructure.lim_natural _ _ f.toLinearMap f.map_comp f.map_conj rfl rfl
        (fun u _ => hxS u) (fun u _ => hxS u) hpSA hmSA hnilSA hnSA hpSB hmSB hnilSB hnSB)
  · exact key (Gelfand.RationalStructure.inputPlus A.setup) (Gelfand.RationalStructure.inputPlus B.setup) rfl
      (Gelfand.RationalStructure.lim_natural _ _ f.toLinearMap f.map_comp f.map_conj rfl rfl
        (fun _ _ => rfl) (fun u _ => htM u) hpPA hmPA hnilPA hnPA hpPB hmPB hnilPB hnPB)

/-- The joint specification holds — `C1` and `C5` together, in the form `E_QFunctor` consumes.
@census none (helper; `E_Q_wellDefined` and `E_Q_functorial` bundled) -/
theorem E_Q_spec : Gelfand.RationalStructure.E_QSpec hcard hℓ :=
  ⟨fun A => E_E_wellDefined hcard hℓ A, fun A _ f => E_E_functorial hℓ A f⟩


end Clauses


/-! ## The native `𝔼_E` on `HC ℓ E D` (stage T3) -/

section NativeHC

set_option linter.unusedSectionVars false

variable {D : ImagUnit E} (hℓ : 1 ≤ ℓ)

/-- The limits commute with morphisms (Step O-15, `rmk:stabilizationaddenda`(i)).
@census none (helper) -/
theorem limAt_natural {A B : HC ℓ E D} (f : A ⟶ B) (h : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1)
    (v : Fin 3) (m : A.carrier) :
    (f : HC.Hom A B).toLinearMap (Gelfand.RationalStructure.limAtHC A h hℓ v m) = Gelfand.RationalStructure.limAtHC B h hℓ v ((f : HC.Hom A B).toLinearMap m) := by
  rw [Gelfand.RationalStructure.limAtHC_eq, Gelfand.RationalStructure.limAtHC_eq]
  exact E_E_functorial hℓ (A.toHCEObj h) (HC.Hom.toHCEHom h f) v m

/-- `𝔼_E(f)`: the restrictions to the three vertex spaces.  @census none (helper) -/
noncomputable def E_E_hom {A B : HC ℓ E D} (f : A ⟶ B) :
    RationalQuiver.Rep.Hom (E_E_rep hℓ A) (E_E_rep hℓ B) where
  ψ v := Split.E_F_map_ψ ℓ (HC.Hom.toF f) v
  edge e m := Split.E_F_map_edge ℓ hℓ (HC.Hom.toF f) e m
  rational σ v m := by
    obtain ⟨m, hm⟩ := m
    refine Subtype.ext ?_
    show (f : HC.Hom A B).toLinearMap (Gelfand.RationalStructure.E_E_φ hℓ A σ v m) = Gelfand.RationalStructure.E_E_φ hℓ B σ v ((f : HC.Hom A B).toLinearMap m)
    rcases D.chi_cases σ with hσ | hσ
    · rw [Gelfand.RationalStructure.E_E_φ_of_one hℓ A hσ v, Gelfand.RationalStructure.E_E_φ_of_one hℓ B hσ v]
    · rw [Gelfand.RationalStructure.E_E_φ_of_neg hℓ A hσ v, Gelfand.RationalStructure.E_E_φ_of_neg hℓ B hσ v,
        (f : HC.Hom A B).map_gal,
        limAt_natural hℓ f _ v]

/-- **`𝔼_E`, `ℓ ≥ 1`**, as a functor.  @census none (helper) -/
noncomputable def E_EGel : HC ℓ E D ⥤ (RepNilGel D).FullSubcategory where
  obj A := E_E_obj hℓ A
  map f := ⟨E_E_hom hℓ f⟩
  map_id A := by
    apply ObjectProperty.hom_ext
    exact RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)


end NativeHC

end RationalQuivers.Gelfand.Equivalence
