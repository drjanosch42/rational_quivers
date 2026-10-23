import RationalQuivers.Gelfand.Equivalence.Functor

/-!
# faithfulness of `𝔼_E` (§5.3, Step O-16)

`E_E_faithful`: a morphism is determined by its restrictions to the three vertices (Step O-7f, base
change faithful).

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Equivalence.lean (§FullyFaithful)` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.Equivalence.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

@census none (module)
-/

namespace RationalQuivers.Gelfand.Equivalence

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {Dq : SqrtNegOneExt E}
open scoped TensorProduct Classical

variable {ℓ : ℕ}

/-! ### `C6`/`C7`: full faithfulness -/

section FullyFaithful

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2) (hℓ : 1 ≤ ℓ)

/-- **`RQ-5.05-C6`** — `𝔼_ℚ` is **faithful** (repair `V-S8-6`: about the functor, not a restatement
of Hom-descent).  The source: via the 2-commutative square, the equivalence over `ℚ[√-1]`
(`RQ-5.02`), and faithfulness of the two vertical base-change functors.

@census    none (auxiliary; discharges census clause `RQ-5.05-C6`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C6
@imports   none
@divergence none -/
theorem E_Q_faithful (h : Gelfand.RationalStructure.E_QSpec hcard hℓ) : (E_QFunctor hcard hℓ h).Faithful := by
  constructor
  intro A B f g hfg
  have hV : ∀ (v : Fin 3) (m : A.carrier), m ∈ A.setup.weight.comp (vtxIdx ℓ v) →
      f.toLinearMap m = g.toLinearMap m := by
    intro v m hm
    have h1 : (E_Q_hom hcard hℓ (h.1 A) (h.1 B) f (h.2 _ _ f)).ψ
        = (E_Q_hom hcard hℓ (h.1 A) (h.1 B) g (h.2 _ _ g)).ψ :=
      congrArg (fun (u : (E_QFunctor hcard hℓ h).obj A ⟶ (E_QFunctor hcard hℓ h).obj B) =>
        u.hom.ψ) hfg
    exact congrArg (fun (T : Split.V3 A.qi v →ₗ[Dq.carrier] Split.V3 B.qi v) =>
      ((T ⟨m, hm⟩ : Split.V3 B.qi v) : B.carrier)) (congrFun h1 v)
  exact HCEHom.hom_ext (congrArg Split.HCFHom.toLinearMap
    (Split.eq_of_eq_on_V3 (A := A.toF) (B := B.toF) ((GF.baseChangeE ℓ E Dq).map f) ((GF.baseChangeE ℓ E Dq).map g) hV))


end FullyFaithful


/-! ## The native `𝔼_E` on `HC ℓ E D` (stage T3) -/

section NativeHC

set_option linter.unusedSectionVars false

variable {D : ImagUnit E} (hℓ : 1 ≤ ℓ)

/-- **Faithfulness** (Step O-16).  @census none (helper)
@clauses   RQ2-5.12-S-O16 -/
theorem E_E_faithful : (E_EGel (D := D) hℓ).Faithful := by
  constructor
  intro A B f g hfg
  have hV : ∀ (v : Fin 3) (m : A.carrier), m ∈ A.weight.comp (vtxIdx ℓ v) →
      (f : HC.Hom A B).toLinearMap m = (g : HC.Hom A B).toLinearMap m := by
    intro v m hm
    have h1 : (E_E_hom hℓ f).ψ = (E_E_hom hℓ g).ψ :=
      congrArg (fun (u : (E_EGel hℓ).obj A ⟶ (E_EGel hℓ).obj B) => u.hom.ψ) hfg
    exact congrArg (fun (T : Split.V3 A.qi v →ₗ[D.L] Split.V3 B.qi v) =>
      ((T ⟨m, hm⟩ : Split.V3 B.qi v) : B.carrier)) (congrFun h1 v)
  exact HC.Hom.ext' (congrArg Split.HCFHom.toLinearMap
    (Split.eq_of_eq_on_V3 (A := A.toF) (B := B.toF) (HC.Hom.toF f) (HC.Hom.toF g) hV))


end NativeHC

end RationalQuivers.Gelfand.Equivalence
