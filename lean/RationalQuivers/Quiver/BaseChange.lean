module

public import RationalQuivers.Quiver.Comap

@[expose] public section

/-!
# Base change of `K`-rational quivers

Formalizes Definition `def:quiverbasechange` of §1.2 of `latex/rational_quivers.tex`
(census `RQ2-1.05`).

## Main definitions / results
* `RationalQuivers.galRestrict` — the inclusion `Gal(L/E') ↪ Gal(L/K)` for an intermediate field
  `L/E'/K`, i.e. `AlgEquiv.restrictScalars` packaged as a group homomorphism.
* `RationalQuivers.continuous_galRestrict` — it is continuous for the Krull topologies. This is the
  fact that makes the restricted action of `def:quiverbasechange` continuous again
  (clause `RQ2-1.05-C2`); mathlib does not have it (`ledger/MATHLIB-DECISIONS.tsv` row `MD-S1-03`).
* `RationalQuivers.RationalQuiver.baseChange` — Definition `def:quiverbasechange` (census
  `RQ2-1.05`), as a functor `{K-rational quivers} ⥤ {E'-rational quivers}`.

**Correction, 2026-08-29 — census r5 (`census-v1.2`) closes AN-19.** ATTESTATION **AN-19** asked
whether the finiteness in `def:quiverbasechange` was intended, recording that `RQ2-1.11` and
`RQ2-1.12` quantified over *arbitrary* intermediate fields. The author has since answered by adding
an explicit "`E'/K` finite" hypothesis clause to `RQ2-1.11` and `RQ2-1.12`, so finiteness is now
uniform across `RQ2-1.05`, `RQ2-1.11` and `RQ2-1.12`. Consequences: `RQ2-1.05-H2` is **unchanged** and
`baseChange` still carries it, and stage S2 carries finiteness of its own accord, so the
finiteness-free variant this file once provided (`baseChangeOfIntermediate`) served nothing and was
removed on 2026-08-29 — see `workflow/stages/S1/DESIGN-NOTES.md`. This banner supersedes, in place,
every earlier sentence in this file that said S2 needs a finiteness-free form
(`WORKFLOW.md` §7, R6).

## Implementation notes

The source writes the intermediate field as `E`, colliding with the edge set of `Γ`; the census
writes it `E'` throughout (ATTESTATION **AN-11**). We follow the census and call it `E'`.
-/

universe u

namespace RationalQuivers

open CategoryTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- The inclusion `Gal(L/E') ↪ Gal(L/K)` attached to an intermediate field `L/E'/K`, namely
`AlgEquiv.restrictScalars K` as a group homomorphism. The source describes `Gal(L/E')` as a
subgroup of `Gal(L/K)` "endowed with the subspace topology"; `galRestrict` is that inclusion, and
`isOpenEmbedding_galRestrict` records that for `E'/K` finite the Krull topology of `Gal(L/E')`
*is* the subspace topology.

@census none (helper for `RQ2-1.05`, `RQ2-1.06`, `RQ2-1.07`)
-/
def galRestrict (E' : IntermediateField K L) : Gal(L/E') →* Gal(L/K) where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `galRestrict` does not change the underlying map of an automorphism. @census none (helper) -/
@[simp]
lemma galRestrict_apply (E' : IntermediateField K L) (σ : Gal(L/E')) (x : L) :
    galRestrict K L E' σ x = σ x := rfl

/-- `galRestrict` is injective: an automorphism of `L` is determined by its underlying map.

@census none (helper)
-/
theorem injective_galRestrict (E' : IntermediateField K L) :
    Function.Injective (galRestrict K L E') :=
  AlgEquiv.restrictScalars_injective K

/-- The image of `Gal(L/E')` in `Gal(L/K)` is the fixing subgroup of `E'`.

@census none (helper)
-/
theorem range_galRestrict (E' : IntermediateField K L) :
    (galRestrict K L E').range = E'.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ.commutes ⟨x, hx⟩
  · intro hσ
    refine ⟨IntermediateField.fixingSubgroupEquiv E' ⟨σ, hσ⟩, ?_⟩
    exact AlgEquiv.ext fun _ => rfl

/-- **The continuity of `def:quiverbasechange`.** `galRestrict` is continuous for the Krull
topologies on `Gal(L/E')` and `Gal(L/K)`. The source asserts exactly this ("the restricted action
`ρ|_{Gal(L/E)}` is again continuous, `Gal(L/E)` being endowed with the subspace topology"), which
is clause `RQ2-1.05-C2`. mathlib has `IntermediateField.fixingSubgroup_isOpen` but no statement
comparing `krullTopology E' L` with `krullTopology K L`
(`ledger/MATHLIB-DECISIONS.tsv` row `MD-S1-03`).

@census none (helper: clause RQ2-1.05-C2)
-/
theorem continuous_galRestrict (E' : IntermediateField K L) [FiniteDimensional K E'] :
    Continuous (galRestrict K L E') := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨F, hFfin, hFsub⟩ := hN
  haveI := hFfin
  rw [krullTopology_mem_nhds_one_iff]
  set h : E' ≤ F ⊔ E' := le_sup_right with hdef
  haveI : Module.Finite K ↥(IntermediateField.extendScalars h) :=
    (inferInstance : Module.Finite K ↥(F ⊔ E'))
  refine ⟨IntermediateField.extendScalars h, ?_, ?_⟩
  · exact Module.Finite.of_restrictScalars_finite K ↥E' ↥(IntermediateField.extendScalars h)
  · intro σ hσ
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
    apply hFsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact hσ x ((le_sup_left : F ≤ F ⊔ E') hx)

/-- For `E'/K` **finite**, `galRestrict` is moreover an open map, so `Gal(L/E')` carries exactly
the subspace topology of the open subgroup `E'.fixingSubgroup ≤ Gal(L/K)`. This is what makes the
induced action of `def:quiverrestriction` continuous (clause `RQ2-1.06-C5`), and it is where the
finiteness hypothesis `RQ2-1.06-H2` is used.

@census none (helper: clause RQ2-1.06-C5)
-/
theorem isOpenMap_galRestrict (E' : IntermediateField K L) [FiniteDimensional K E'] :
    IsOpenMap (galRestrict K L E') := by
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨u, huU, rfl⟩
  -- `U` is a neighbourhood of `u`, so `u⁻¹ U` is a neighbourhood of `1`, hence contains a basic
  -- open subgroup `F'.fixingSubgroup` with `F'/E'` finite.
  have hmem : (fun y : Gal(L/E') => u * y) ⁻¹' U ∈ nhds (1 : Gal(L/E')) := by
    have h := hU.mem_nhds huU
    rw [← map_mul_left_nhds_one u, Filter.mem_map] at h
    exact h
  rw [krullTopology_mem_nhds_one_iff] at hmem
  obtain ⟨F', hF'fin, hF'sub⟩ := hmem
  haveI := hF'fin
  -- `F'` is finite over `K` too: this is where `[FiniteDimensional K E']`, i.e. clause
  -- `RQ2-1.06-H2`, is consumed.
  haveI : FiniteDimensional K (F'.restrictScalars K) := FiniteDimensional.trans K ↥E' ↥F'
  -- The image of the basic open subgroup is the fixing subgroup of `F'` read over `K`.
  have himg : galRestrict K L E' '' (F'.fixingSubgroup : Set Gal(L/E'))
      = ((F'.restrictScalars K).fixingSubgroup : Set Gal(L/K)) := by
    ext σ
    simp only [Set.mem_image, SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      intro x hx
      exact hτ x hx
    · intro hσ
      have hσE : σ ∈ E'.fixingSubgroup := by
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact hσ x (F'.algebraMap_mem ⟨x, hx⟩)
      rw [← range_galRestrict] at hσE
      obtain ⟨τ, rfl⟩ := hσE
      exact ⟨τ, fun x hx => hσ x hx, rfl⟩
  refine ⟨(fun y : Gal(L/K) => galRestrict K L E' u * y) ''
      ((F'.restrictScalars K).fixingSubgroup : Set Gal(L/K)), ?_, ?_, ?_⟩
  · rintro _ ⟨σ, hσ, rfl⟩
    rw [← himg] at hσ
    obtain ⟨τ, hτ, rfl⟩ := hσ
    exact ⟨u * τ, hF'sub hτ, by rw [map_mul]⟩
  · exact isOpenMap_mul_left _ _ (IntermediateField.fixingSubgroup_isOpen (F'.restrictScalars K))
  · exact ⟨1, one_mem _, by simp⟩

/-- For `E'/K` finite the index `[Gal(L/K) : Gal(L/E')]` equals `[E' : K]`, in particular it is
finite. This is what makes the vertex and edge sets of `res_{E'/K} Γ_{E'}` finite, i.e. what makes
the restriction a quiver at all (`RQ2-1.01-H1`, `RQ2-1.01-H2` for `RQ2-1.06`).

@census none (helper: clause RQ2-1.06-C5)
-/
theorem finiteIndex_range_galRestrict (E' : IntermediateField K L) [FiniteDimensional K E'] :
    (galRestrict K L E').range.FiniteIndex := by
  rw [range_galRestrict]
  refine ⟨?_⟩
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index L E']
  exact (Module.finrank_pos (R := K) (M := E')).ne'

namespace RationalQuiver

/-- **Definition 1.5** (`def:quiverbasechange`).
For any quiver `Γ_K = (Γ, ρ)` whose rational structure is given by an action of `Gal(L/K)`, and any
intermediate field `L/E'/K` with `E'/K` **finite**, the *base change* of `Γ_K` to `E'` is the
`E'`-rational quiver

`Γ_{E'} = E' ⊗_K Γ_K := (Γ, ρ|_{Gal(L/E')})`.

The restricted action is again continuous, `Gal(L/E')` carrying the subspace topology, so `Γ_{E'}`
really is an `E'`-rational quiver.

@census    RQ2-1.05
@source    def:quiverbasechange
@clauses   RQ2-1.05-H1, RQ2-1.05-H2, RQ2-1.05-H3, RQ2-1.05-C1, RQ2-1.05-C2
@imports   none
@divergence none. Clause `RQ2-1.05-H1` is the argument `E' : IntermediateField K L`; clause
`RQ2-1.05-H2` is the instance argument `[FiniteDimensional K E']`, and it is **load-bearing**: the
proof of `continuous_galRestrict` obtains continuity from the compositum `F ⊔ E'` being finite over
`K`, so without it clause `RQ2-1.05-C2` — that `Γ_{E'}` is again an `E'`-rational quiver — is not
available. (An earlier revision of this docstring said the construction did not consume the
hypothesis; that was true only while continuity was an unproved `sorry`, and is retracted here.
ATTESTATION **AN-19** raised the finiteness as an author question; census r5 / `census-v1.2`
answers it by adding the same hypothesis to `RQ2-1.11` and `RQ2-1.12`, so `RQ2-1.05-H2` stands
unchanged and is now uniform with them.) Clause `RQ2-1.05-C1` is the definitional equalities
`baseChange_obj_toRQuiver` and `baseChange_obj_ρ`; clause `RQ2-1.05-C2` is the *type* of the result,
`RationalQuiver E' L`, whose two smoothness fields are supplied by `continuous_galRestrict`.
Presenting base change as a functor rather than as an operation on objects adds the action on
morphisms, which `prop:quiverrestrictionbasechangeadjunction` (`RQ2-1.07`) requires and which the
source's phrase "restriction and base change … form adjoint pairs of *functors*" (Introduction)
asks for.
-/
def baseChange (E' : IntermediateField K L) [FiniteDimensional K E'] :
    RationalQuiver K L ⥤ RationalQuiver (E' : Type u) L :=
  comapFunctor (galRestrict K L E') (continuous_galRestrict K L E')

/-- Clause `RQ2-1.05-C1`, first half: the base change has the *same* underlying classical quiver
`Γ = (V,E,s,t)`.

@census none (helper: clause RQ2-1.05-C1)
-/
@[simp]
theorem baseChange_obj_toRQuiver (E' : IntermediateField K L) [FiniteDimensional K E']
    (Γ : RationalQuiver K L) :
    ((baseChange K L E').obj Γ).toRQuiver = Γ.toRQuiver := rfl

/-- Clause `RQ2-1.05-C1`, second half: the rational structure of `E' ⊗_K Γ_K` is `ρ` restricted to
`Gal(L/E')`.

@census none (helper: clause RQ2-1.05-C1)
-/
@[simp]
theorem baseChange_obj_ρ (E' : IntermediateField K L) [FiniteDimensional K E']
    (Γ : RationalQuiver K L) (σ : Gal(L/E')) :
    ((baseChange K L E').obj Γ).ρ σ = Γ.ρ (galRestrict K L E' σ) := rfl

end RationalQuiver

end RationalQuivers
