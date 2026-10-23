import RationalQuivers.Gelfand.EssSurj.Construction

/-!
# essential surjectivity, the rational structure on `M` (§5.3, Step O-19)

`φ_c^M` (`essConj`, `eq:varphicj`), Galois descent `M_E := M^{φ_c^M}` (`essForm`, `essBaseChange`,
`essRationalSetup`), the pins, `essSurj_exists`; native: `toHC`, the descended module as an object of
`HC ℓ E D` (`EX-HC`: the submodule clause is definitional in the descent presentation).

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Equivalence.lean (§E2Form, §E2Pins, `essSurj_exists`)` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.EssSurj.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

@census none (module)
-/

namespace RationalQuivers.Gelfand.EssSurj

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {Dq : SqrtNegOneExt E}
open scoped TensorProduct Classical

variable {ℓ : ℕ}

section EssSurj

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2) (hℓ : 1 ≤ ℓ)

/-! ### Engine `E2`, step 6 — the `ℚ`-form, by Galois descent

Residue item 6 of `stages/S8/DESIGN-NOTES.md` §16.4, second half.  This is the one place in the
construction where S0's `Descent/Galois.lean` is actually needed: `RationalSetup.baseChange` asks
for an isomorphism `ℚ[√-1] ⊗_ℚ M_ℚ ≃ M`, and the only `M_ℚ` available is the fixed-point space of
`c`, so the content is `thm:galoisdescent`'s counit being bijective (`descentCounit_bijective`,
`RQ-1.16`).

Three instances have to be installed by hand, exactly as §16.3 predicted, because `Module ℚ M` is
NOT synthesizable at the pin from `[AddCommGroup M] [Module E[√-1] M]`: the `ℚ`-module structure
(`Module.compHom` along `ℚ → ℚ[√-1]`), the `IsScalarTower`, and the `Gal(ℚ[√-1]/ℚ)`-action.  The
last follows `galAct`'s `hcard` pattern: the group has order two, so an action is a choice of
involution, and `essConj` is it.  Continuity — the other half of `Descent.KStructure` — is free
here because `ℚ[√-1]/ℚ` is finite (`KStructure.of_finiteDimensional`, clause `RQ-1.16-C5`).
-/

section E2Form

variable (V : Gelfand.RationalStructure.RepNilQ hcard)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

/-- The action of `σ ∈ Gal(ℚ[√-1]/ℚ)` on `M`: the identity for `σ = 1`, `c` otherwise.
@census none (helper; engine `E2`) -/
noncomputable def essGalSMul (ℓ : ℕ) (σ : Dq.carrier ≃ₐ[E] Dq.carrier)
    (v : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ :=
  if σ = 1 then v else essConj hcard V ℓ v

/-- @census none (helper; engine `E2`) -/
theorem essGalSMul_one (ℓ : ℕ) (v : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) :
    essGalSMul hcard V ℓ 1 v = v := by
  simp [essGalSMul]

/-- @census none (helper; engine `E2`) -/
theorem essGalSMul_of_ne (ℓ : ℕ) {σ : Dq.carrier ≃ₐ[E] Dq.carrier} (hσ : σ ≠ 1)
    (v : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) : essGalSMul hcard V ℓ σ v = essConj hcard V ℓ v := by
  simp [essGalSMul, hσ]

/-- `Gal(ℚ[√-1]/ℚ)` acts on `M` by additive automorphisms.  @census none (helper; engine `E2`) -/
noncomputable def essGalAction (ℓ : ℕ) :
    DistribMulAction (Dq.carrier ≃ₐ[E] Dq.carrier) (Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) where
  smul σ v := essGalSMul hcard V ℓ σ v
  one_smul v := essGalSMul_one hcard V ℓ v
  mul_smul σ τ v := by
    show essGalSMul hcard V ℓ (σ * τ) v
      = essGalSMul hcard V ℓ σ (essGalSMul hcard V ℓ τ v)
    by_cases hσ : σ = 1
    · subst hσ; rw [one_mul, essGalSMul_one]
    · by_cases hτ : τ = 1
      · subst hτ; rw [mul_one, essGalSMul_one]
      · rw [Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ, Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hτ, Gelfand.RationalStructure.galConj_mul_self,
          essGalSMul_one, essGalSMul_of_ne hcard V ℓ Gelfand.RationalStructure.galConj_ne_one,
          essGalSMul_of_ne hcard V ℓ Gelfand.RationalStructure.galConj_ne_one, essConj_involutive hcard V ℓ v]
  smul_zero σ := by
    show essGalSMul hcard V ℓ σ 0 = 0
    by_cases hσ : σ = 1
    · subst hσ; rw [essGalSMul_one]
    · rw [essGalSMul_of_ne hcard V ℓ hσ, map_zero]
  smul_add σ v w := by
    show essGalSMul hcard V ℓ σ (v + w)
      = essGalSMul hcard V ℓ σ v + essGalSMul hcard V ℓ σ w
    by_cases hσ : σ = 1
    · subst hσ; rw [essGalSMul_one, essGalSMul_one, essGalSMul_one]
    · rw [essGalSMul_of_ne hcard V ℓ hσ, essGalSMul_of_ne hcard V ℓ hσ,
        essGalSMul_of_ne hcard V ℓ hσ, map_add]

/-- The action is semi-linear — this is `essConj_smul`.  @census none (helper; engine `E2`) -/
theorem essIsSemilinearAction (ℓ : ℕ) :
    letI := essGalAction hcard V ℓ
    Descent.IsSemilinearAction E Dq.carrier (Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) := by
  letI := essGalAction hcard V ℓ
  refine ⟨fun σ a v => ?_⟩
  show essGalSMul hcard V ℓ σ (a • v) = σ a • essGalSMul hcard V ℓ σ v
  by_cases hσ : σ = 1
  · subst hσ; rw [essGalSMul_one, essGalSMul_one]; rfl
  · rw [essGalSMul_of_ne hcard V ℓ hσ, essGalSMul_of_ne hcard V ℓ hσ, essConj_smul,
      Gelfand.RationalStructure.eq_galConj_of_ne_one hcard hσ]

/-- `M` carries a `ℚ`-structure: semi-linearity plus continuity, the latter free because
`ℚ[√-1]/ℚ` is finite (`RQ-1.16-C5`).  @census none (helper; engine `E2`) -/
theorem essKStructure (ℓ : ℕ) :
    letI := essGalAction hcard V ℓ
    Descent.KStructure E Dq.carrier (Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) := by
  letI := essGalAction hcard V ℓ
  letI := essIsSemilinearAction hcard V ℓ
  infer_instance

/-- `M` as an object of S0's category `Descent.VecK ℚ ℚ[√-1]`.  The `ℚ`-vector space structure is
`Module.compHom` along `ℚ → ℚ[√-1]`, carried as a field (S0's discipline: never a global
instance).  @census none (helper; engine `E2`) -/
noncomputable def essVecK (ℓ : ℕ) : Descent.VecK E Dq.carrier :=
  letI : Module E (Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) := Module.compHom _ (algebraMap E Dq.carrier)
  letI : IsScalarTower E Dq.carrier (Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) := ⟨fun c a x => by
    show ((c • a) • x : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) = algebraMap E Dq.carrier c • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩
  letI := essGalAction hcard V ℓ
  { carrier := Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ
    isKStructure := essKStructure hcard V ℓ }

/-- @census none (helper; engine `E2`) -/
theorem essVecK_smul (ℓ : ℕ) (σ : Dq.carrier ≃ₐ[E] Dq.carrier)
    (v : (essVecK hcard V ℓ).carrier) :
    σ • v = essGalSMul hcard V ℓ σ v := rfl

/-- **The `ℚ`-form `M_ℚ`**: the fixed points of `c`.  @census none (helper; engine `E2`) -/
noncomputable def essForm (ℓ : ℕ) : Submodule E (essVecK hcard V ℓ).carrier :=
  Descent.fixedPoints E Dq.carrier (essVecK hcard V ℓ)

/-- **`M = ℚ[√-1] ⊗_ℚ M_ℚ`** — `thm:galoisdescent` (`RQ-1.16`) for the constructed module.
@census none (helper; engine `E2`) -/
noncomputable def essBaseChange (ℓ : ℕ) :
    (Dq.carrier ⊗[E] ↥(essForm hcard V ℓ)) ≃ₗ[Dq.carrier] Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ :=
  LinearEquiv.ofBijective (Descent.descentCounit E Dq.carrier (essVecK hcard V ℓ))
    (Descent.descentCounit_bijective E Dq.carrier (essVecK hcard V ℓ))

/-- **`c` fixes `1 ⊗ v`** (`RationalSetup.conj_baseChange`): by construction, since `M_ℚ` IS the
fixed-point space.  @census none (helper; engine `E2`) -/
theorem essConj_baseChange (ℓ : ℕ) (v : ↥(essForm hcard V ℓ)) :
    essConj hcard V ℓ (essBaseChange hcard V ℓ ((1 : Dq.carrier) ⊗ₜ[E] v))
      = essBaseChange hcard V ℓ ((1 : Dq.carrier) ⊗ₜ[E] v) := by
  have hb : essBaseChange hcard V ℓ ((1 : Dq.carrier) ⊗ₜ[E] v)
      = (v.1 : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) := by
    show (1 : Dq.carrier) • (v.1 : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) = _
    rw [one_smul]
  have hfix := v.2 Dq.conj
  rw [essVecK_smul, essGalSMul_of_ne hcard V ℓ Gelfand.RationalStructure.galConj_ne_one] at hfix
  rw [hb]
  exact hfix

/-- **The `RationalSetup` of the constructed module** — `EssSurjData.setup`.
@census none (helper; engine `E2`) -/
noncomputable def essRationalSetup :
    RationalSetupOver ℓ E Dq ↥(essForm hcard V ℓ) (Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) where
  baseChange := essBaseChange hcard V ℓ
  weight := Split.essWeight hℓ (Gelfand.RationalStructure.toSplitW hcard V)
  gic := Split.essGIC hℓ (Gelfand.RationalStructure.toSplitW hcard V)
  conj := essConj hcard V ℓ
  conj_smul := essConj_smul hcard V ℓ
  conj_involutive := essConj_involutive hcard V ℓ
  conj_baseChange := essConj_baseChange hcard V ℓ
  conj_comp := essConj_comp hcard V ℓ
  conj_X := essConj_X hcard hℓ V
  conj_Y := essConj_Y hcard hℓ V
  conj_H := essConj_H hcard V ℓ

end E2Form

/-! ### Engine `E2`, step 7 — the pins

Residue item 7 of `stages/S8/DESIGN-NOTES.md` §16.4.  §16.4 predicted that each pin "should be
`rfl` or one `ofEq` rewrite *provided* step 1's isos are used as the identification"; what it is,
measured, is one application of a single **pin engine** `essPin_gen` whose four inputs are

* which injection the source component is the range of (`hreg₁`) and which the target is (`hreg₂`);
* how the operator acts on a summand (`hTlof`: `T (lof n b) = lof m ⟨A ↑b, _⟩`);
* how the ambient operator `A` reads through the two injections (`hG`: `A (f₁ y) = f₂ (G y)`).

The point of the transport-free design is exactly that `hTlof` and `hG` are the ONLY content: no
pin needs a type transport, and the only degree transport anywhere is `essLof_congr` on the index
(`(j-1)+2 = j+1` and the like), never on a fibre type.
-/

section E2Pins

variable (V : Gelfand.RationalStructure.RepNilQ hcard)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

variable {W : Type} [AddCommGroup W] [Module Dq.carrier W]

/-! #### The fifteen pins, one application of `essPin_gen` each -/

/-- `c`'s summand rule.  @census none (helper; engine `E2`) -/
theorem essConj_lof_pin {n m : ℤ} (hm : -n = m) (b : Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ n)
    (hb : essConjAmb hcard V (b : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)) ∈ Split.essRegion (Gelfand.RationalStructure.toSplitW hcard V) ℓ m) :
    essConj hcard V ℓ (DirectSum.lof Dq.carrier ℤ (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) n b)
      = DirectSum.lof Dq.carrier ℤ (Split.EssFib (Gelfand.RationalStructure.toSplitW hcard V) ℓ) m
          ⟨essConjAmb hcard V (b : Split.EssTriple (Gelfand.RationalStructure.toSplitW hcard V)), hb⟩ := by
  rw [essConj_lof]
  exact Split.essLof_congr (Gelfand.RationalStructure.toSplitW hcard V) hm _ _ rfl

/-- **`C16`, `c` on the `+` region**.  @census none (helper; engine `E2`) -/
theorem essPin_conj_plus (n : ℤ) (h1 : (ℓ : ℤ) + 1 ≤ n) (h2 : (n - ((ℓ : ℤ) + 1)) % 2 = 0)
    (v : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) (hv : v ∈ Split.essComp (Gelfand.RationalStructure.toSplitW hcard V) ℓ n) :
    essConj hcard V ℓ v
      = (((Split.essIsoMinus (Gelfand.RationalStructure.toSplitW hcard V) (by omega) (by omega : -n ≤ -((ℓ : ℤ) + 1))).symm
          (Vphi hcard V 2 (Split.essIsoPlus (Gelfand.RationalStructure.toSplitW hcard V) (by omega) h1 ⟨v, hv⟩))
              : ↥(Split.essComp (Gelfand.RationalStructure.toSplitW hcard V) ℓ (-n))) : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) :=
  Split.essPin_gen (Gelfand.RationalStructure.toSplitW hcard V) ℓ (Split.essIotaPlus (Gelfand.RationalStructure.toSplitW hcard V)) (Split.essIotaPlus_inj (Gelfand.RationalStructure.toSplitW hcard V))
    (Split.essRegion_plus (Gelfand.RationalStructure.toSplitW hcard V) (by omega) h1)
    (Split.essIotaMinus (Gelfand.RationalStructure.toSplitW hcard V)) (Split.essIotaMinus_inj (Gelfand.RationalStructure.toSplitW hcard V))
    (Split.essRegion_minus (Gelfand.RationalStructure.toSplitW hcard V) (by omega) (by omega))
    _ rfl _ rfl (essConj hcard V ℓ) (essConjAmb hcard V)
    (fun b hb => essConj_lof_pin hcard V (by ring) b hb)
    (fun y => Vphi hcard V 2 y)
    (fun y => essConjAmb_iotaPlus hcard V y)
    v hv

/-- **`C16`, `c` on the `⋆` region**.  @census none (helper; engine `E2`) -/
theorem essPin_conj_star (n : ℤ) (h1 : -((ℓ : ℤ) - 1) ≤ n) (h2 : n ≤ (ℓ : ℤ) - 1)
    (h3 : (n - ((ℓ : ℤ) + 1)) % 2 = 0)
    (v : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) (hv : v ∈ Split.essComp (Gelfand.RationalStructure.toSplitW hcard V) ℓ n) :
    essConj hcard V ℓ v
      = (((Split.essIsoStar (Gelfand.RationalStructure.toSplitW hcard V) (by omega) (by omega) (by omega)).symm
          (Vphi hcard V 1 (Split.essIsoStar (Gelfand.RationalStructure.toSplitW hcard V) (by omega) h1 h2 ⟨v, hv⟩))
              : ↥(Split.essComp (Gelfand.RationalStructure.toSplitW hcard V) ℓ (-n))) : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) :=
  Split.essPin_gen (Gelfand.RationalStructure.toSplitW hcard V) ℓ (Split.essIotaStar (Gelfand.RationalStructure.toSplitW hcard V)) (Split.essIotaStar_inj (Gelfand.RationalStructure.toSplitW hcard V))
    (Split.essRegion_star (Gelfand.RationalStructure.toSplitW hcard V) (by omega) h1 h2)
    (Split.essIotaStar (Gelfand.RationalStructure.toSplitW hcard V)) (Split.essIotaStar_inj (Gelfand.RationalStructure.toSplitW hcard V))
    (Split.essRegion_star (Gelfand.RationalStructure.toSplitW hcard V) (by omega) (by omega) (by omega))
    _ rfl _ rfl (essConj hcard V ℓ) (essConjAmb hcard V)
    (fun b hb => essConj_lof_pin hcard V (by ring) b hb)
    (fun y => Vphi hcard V 1 y)
    (fun y => essConjAmb_iotaStar hcard V y)
    v hv

/-- **`C16`, `c` on the `−` region**.  @census none (helper; engine `E2`) -/
theorem essPin_conj_minus (n : ℤ) (h1 : n ≤ -((ℓ : ℤ) + 1)) (h2 : (n - ((ℓ : ℤ) + 1)) % 2 = 0)
    (v : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) (hv : v ∈ Split.essComp (Gelfand.RationalStructure.toSplitW hcard V) ℓ n) :
    essConj hcard V ℓ v
      = (((Split.essIsoPlus (Gelfand.RationalStructure.toSplitW hcard V) (by omega) (by omega : (ℓ : ℤ) + 1 ≤ -n)).symm
          (Vphi hcard V 0 (Split.essIsoMinus (Gelfand.RationalStructure.toSplitW hcard V) (by omega) h1 ⟨v, hv⟩))
              : ↥(Split.essComp (Gelfand.RationalStructure.toSplitW hcard V) ℓ (-n))) : Split.EssCarrier (Gelfand.RationalStructure.toSplitW hcard V) ℓ) :=
  Split.essPin_gen (Gelfand.RationalStructure.toSplitW hcard V) ℓ (Split.essIotaMinus (Gelfand.RationalStructure.toSplitW hcard V)) (Split.essIotaMinus_inj (Gelfand.RationalStructure.toSplitW hcard V))
    (Split.essRegion_minus (Gelfand.RationalStructure.toSplitW hcard V) (by omega) h1)
    (Split.essIotaPlus (Gelfand.RationalStructure.toSplitW hcard V)) (Split.essIotaPlus_inj (Gelfand.RationalStructure.toSplitW hcard V))
    (Split.essRegion_plus (Gelfand.RationalStructure.toSplitW hcard V) (by omega) (by omega))
    _ rfl _ rfl (essConj hcard V ℓ) (essConjAmb hcard V)
    (fun b hb => essConj_lof_pin hcard V (by ring) b hb)
    (fun y => Vphi hcard V 0 y)
    (fun y => essConjAmb_iotaMinus hcard V y)
    v hv

end E2Pins





/-- **`RQ-5.05-C9`, `C13`, `C15`, `C16` — the construction exists**: for every nilpotent
finite-dimensional `ℚ`-rational representation `(V, φ_•)` of `Γ_ℚ` with the relation, the
displayed formulas define a `ℚ`-rational Harish-Chandra module with generalized infinitesimal
character `λ = ℓ²` — i.e. an inhabitant of the pinned `EssSurjData`.  `C15` is the content:
`4[X,Y]|_{M_{j+1}} = 4(j+1)·𝟏` is `WeightData.lie_X_Y`, the `H`-action is `H_apply`, and the
tautological `[H,2X] = 4X`, `[H,2Y] = -4Y` are `lie_H_X`/`lie_H_Y`; the `ℚ`-structure is the
`RationalSetup`'s `conj` with `eq:Xconjugation`/`eq:Yconjugation` as its `conj_X`/`conj_Y`.

@census    none (auxiliary; discharges census clauses `RQ-5.05-C9`, `RQ-5.05-C13`, `RQ-5.05-C15`, `RQ-5.05-C16`)
@source    thm:EEQQequivalence
(clauses of the frozen original:)   RQ-5.05-C9, RQ-5.05-C13, RQ-5.05-C15, RQ-5.05-C16
@imports   none
@divergence none -/
theorem essSurj_exists (V : Gelfand.RationalStructure.RepNilQ hcard) : Nonempty (EssSurjData hcard hℓ V) :=
  ⟨{ toSplitEssSurjData := Split.splitData hℓ (Gelfand.RationalStructure.toSplitW hcard V)
     form := ↥(essForm hcard V ℓ)
     baseChange := essBaseChange hcard V ℓ
     conj := essConj hcard V ℓ
     conj_smul := essConj_smul hcard V ℓ
     conj_involutive := essConj_involutive hcard V ℓ
     conj_baseChange := essConj_baseChange hcard V ℓ
     conj_comp := essConj_comp hcard V ℓ
     conj_X := essConj_X hcard hℓ V
     conj_Y := essConj_Y hcard hℓ V
     conj_H := essConj_H hcard V ℓ
     conj_plus := fun n h1 h2 v hv => essPin_conj_plus hcard V n h1 h2 v hv
     conj_star := fun n h1 h2 h3 v hv => essPin_conj_star hcard V n h1 h2 h3 v hv
     conj_minus := fun n h1 h2 v hv => essPin_conj_minus hcard V n h1 h2 v hv }⟩


end EssSurj


/-! ## Step O-19 on `HC ℓ E D`: the descended module `M_E` -/

section NativeHC

variable {D : ImagUnit E} {hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1} {hℓ : 1 ≤ ℓ}
  {V : Gelfand.RationalStructure.RepNilQ (Dq := D.sqrtExt hc) (D.sqrtExt hc).card_gal}

/-- **Step O-19**: the module `M` constructed from `(V, φ_•)`, with its rational structure
`φ_c^M = Σ_j φ_c^{(j)}` (`eq:varphicj`, `essConj`), descended to the object `M_E := M^{φ_c^M}` of
`HC_λ(𝔤,K)_E = HC ℓ E D` (Galois descent, `essForm`/`essBaseChange`; the `(𝔤_E,K_E)`-submodule clause
is definitional in the descent presentation, `EX-HC`).  @census none (helper; Step O-19) -/
noncomputable def toHC (Dd : EssSurjData (D.sqrtExt hc).card_gal hℓ V) : HC ℓ E D :=
  Dd.toHCQObj.toHC

/-- On `M_E`, the Galois action of `c` is `φ_c^M`.  @census none (helper; Step O-19) -/
theorem toHC_galAct (Dd : EssSurjData (D.sqrtExt hc).card_gal hℓ V) {σ : D.L ≃ₐ[E] D.L}
    (hσ : D.chi σ = -1) (v : Dd.carrier) : (toHC Dd).galAct σ v = Dd.conj v :=
  HCEObj.toHC_galAct_neg Dd.toHCQObj hσ v

end NativeHC

end RationalQuivers.Gelfand.EssSurj
