module

public import RationalQuivers.Quiver.Comap
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

/-!
# Inflation to the absolute Galois group, and the finite-quotient factorization

Formalizes the remark following `def:splitrationalquivers` in §1.2 of
`latex/rational_quivers.tex` (census `RQ2-1.20`), the remark that reconciles
`def:rationalquivers` (stated for one `Gal(L/K)`) with `def:rationalquiverhom` (stated for
`Gal(K^sep/K)`) — ATTESTATION **AN-10**.

## Main definitions / results
* `RationalQuivers.galInflate` — `Gal(K^sep/K) ↠ Gal(L/K)`, i.e. `AlgEquiv.restrictNormalHom`.
* `RationalQuivers.RationalQuiver.inflate` — the `K^sep`-form of a `K`-rational quiver
  (clause `RQ2-1.20-C2`).
* `RationalQuivers.RationalQuiver.homEquivInflate` — inflation does not change the hom-sets. This
  is the bridge that makes `RationalQuiver.Hom` (stated over `Gal(L/K)`) equal to
  `def:rationalquiverhom` (stated over `Gal(K^sep/K)`), i.e. clause `RQ2-1.04-H2`.
* `RationalQuivers.RationalQuiver.factorsThroughFinite` — the remark itself (census `RQ2-1.20`).
-/

universe u

namespace RationalQuivers

open CategoryTheory

variable (K L M : Type u) [Field K] [Field L] [Field M]
variable [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
variable [IsGalois K L] [IsGalois K M]

/-- The inflation homomorphism `Gal(M/K) →* Gal(L/K)` for a tower `M/L/K` with `L/K` Galois; this
is mathlib's `AlgEquiv.restrictNormalHom`. Taking `M = K^sep` this is the map that presents
`Gal(L/K)` as a quotient of the absolute Galois group (clause `RQ2-1.20-C1`).

@census none (helper for `RQ2-1.20`)
-/
noncomputable def galInflate : Gal(M/K) →* Gal(L/K) :=
  AlgEquiv.restrictNormalHom L

/-- Clause `RQ2-1.20-C1`: `Gal(L/K)` really is a quotient of `Gal(M/K)` — the inflation map is
surjective. This is mathlib's `AlgEquiv.restrictNormalHom_surjective`.

@census none (helper: clause RQ2-1.20-C1)
-/
theorem surjective_galInflate : Function.Surjective (galInflate K L M) :=
  AlgEquiv.restrictNormalHom_surjective (F := K) (E := M) (K₁ := L)

/-- Clause `RQ2-1.20-C2`: the inflation map is continuous, so a continuous `Gal(L/K)`-action pulls
back to a continuous `Gal(K^sep/K)`-action.

**Correction, 2026-08-29.** `ledger/MATHLIB-DECISIONS.tsv` row `MD-S1-04` originally called this a
mathlib gap on the strength of a grep for `restrictNormalHomContinuous`, the spelling used in the
module docstring of `Mathlib/FieldTheory/Galois/Profinite.lean`. The declaration exists under a
different name, `InfiniteGalois.restrictNormalHom_continuous`. It is stated only for
`L : IntermediateField k K`, whereas `RQ2-1.20` (following the source, which fixes an abstract
Galois extension `L/K` and *then* embeds it in `K^sep`) has `L` as a field with
`[Algebra L M] [IsScalarTower K L M]`. Discharging this sorry is therefore transport of mathlib's
lemma along `L ≃ₐ[K] (IsScalarTower.toAlgHom K L M).fieldRange`, not new mathematics. See row
`MD-S1-12`.

@census none (helper: clause RQ2-1.20-C2)
-/
theorem continuous_galInflate : Continuous (galInflate K L M) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨F, hFfin, hFsub⟩ := hN
  haveI := hFfin
  rw [krullTopology_mem_nhds_one_iff]
  -- Push the basic open `F.fixingSubgroup` of `Gal(L/K)` forward to the copy of `F` inside `M`.
  refine ⟨F.map (IsScalarTower.toAlgHom K L M), ?_, ?_⟩
  · exact LinearEquiv.finiteDimensional
      (IntermediateField.equivMap F (IsScalarTower.toAlgHom K L M)).toLinearEquiv
  · intro σ hσ
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ
    apply hFsub
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hmem : algebraMap L M x ∈ F.map (IsScalarTower.toAlgHom K L M) := ⟨x, hx, rfl⟩
    have hfix := hσ _ hmem
    have hcom : algebraMap L M ((galInflate K L M) σ x) = σ (algebraMap L M x) :=
      AlgEquiv.restrictNormal_commutes σ L x
    apply (algebraMap L M).injective
    rw [hcom]
    exact hfix

namespace RationalQuiver

variable {K L M}

/-- Clause `RQ2-1.20-C2`: every `K`-rational structure with respect to `L/K` arises from a
*continuous* `Gal(K^sep/K)`-action on `V` and on `E`, namely its inflation.

@census none (helper: clause RQ2-1.20-C2)
-/
noncomputable def inflate (Γ : RationalQuiver K L) : RationalQuiver K M :=
  Γ.comap (galInflate K L M) (continuous_galInflate K L M)

/-- Inflation keeps the underlying classical quiver. @census none (helper) -/
@[simp]
lemma inflate_toRQuiver (Γ : RationalQuiver K L) :
    (inflate (M := M) Γ).toRQuiver = Γ.toRQuiver := rfl

/-- **The bridge of ATTESTATION AN-10 / clause `RQ2-1.04-H2`.**
Because inflation is along a *surjection*, a homomorphism of the underlying quivers commutes with
the two `Gal(L/K)`-actions if and only if it commutes with the two inflated `Gal(K^sep/K)`-actions.
Hence `RationalQuiver.Hom`, stated over `Gal(L/K)` in `Quiver/Hom.lean`, is literally the hom-set
of `def:rationalquiverhom`, which is stated over `Gal(K^sep/K)`.

@census none (helper: clause RQ2-1.04-H2; the AN-10 bridge)
-/
noncomputable def homEquivInflate (Γ Γ' : RationalQuiver K L) :
    (Γ ⟶ Γ') ≃ (inflate (M := M) Γ ⟶ inflate (M := M) Γ') where
  toFun φ :=
    { toRQuiverHom := φ.toRQuiverHom
      equivariant_V := fun σ v => φ.equivariant_V (galInflate K L M σ) v
      equivariant_E := fun σ e => φ.equivariant_E (galInflate K L M σ) e }
  invFun ψ :=
    { toRQuiverHom := ψ.toRQuiverHom
      equivariant_V := fun σ v => by
        obtain ⟨τ, rfl⟩ := surjective_galInflate K L M σ
        exact ψ.equivariant_V τ v
      equivariant_E := fun σ e => by
        obtain ⟨τ, rfl⟩ := surjective_galInflate K L M σ
        exact ψ.equivariant_E τ e }
  left_inv _ := rfl
  right_inv _ := rfl

variable (K L M)

/-- **Remark 1.20** (unlabelled in the source; census `RQ2-1.20`).
Let `K^sep` be a separable algebraic closure of `K`. Then any Galois group `Gal(L/K)` occurring in
`def:rationalquivers` may be (non-canonically) regarded as a quotient of `Gal(K^sep/K)`; therefore
all actions in `def:rationalquivers` arise from *continuous* `Gal(K^sep/K)`-actions on `E` and `V`.
Since `E` and `V` are finite, any `K`-rational structure on `Γ` factors through a finite quotient
`Gal(K^sep/K) → Gal(L₀/K)` with `L₀/K` a finite Galois extension; hence `L/K` may be assumed
finite without loss of generality.

@census    RQ2-1.20
@source    rmk:finitequotient
@clauses   RQ2-1.20-H1, RQ2-1.20-H2, RQ2-1.20-C1, RQ2-1.20-C2, RQ2-1.20-C3, RQ2-1.20-C4
@imports   none
@divergence none. Clause `RQ2-1.20-H1` is `[IsSepClosure K M]`: `M` is a separable algebraic
closure of `K`. Clause `RQ2-1.20-H2` (finiteness of `V` and `E`) is carried by `RQuiver` itself
(`RQ2-1.01-H1`, `RQ2-1.01-H2`); it is what makes the kernel below open, being a finite intersection
of the open stabilizers of `RQ2-1.02-C2`/`C3`. The "non-canonically" of the source is the
hypothesis that `L` is *given* as a subextension of `M` (`[Algebra L M] [IsScalarTower K L M]`) —
no canonical such embedding is claimed. Conjunct 1 is clause `RQ2-1.20-C1`; conjunct 2 together
with `RationalQuiver.inflate` is clause `RQ2-1.20-C2`; conjunct 3 is clause `RQ2-1.20-C3`, the
factorization through `Gal(L₀/K)` with `L₀/K` finite Galois (equivalently: `ρ` kills the fixing
subgroup of a finite normal `L₀`, so it factors through `Gal(L/K)/Gal(L/L₀) ≅ Gal(L₀/K)`);
conjunct 4 is clause `RQ2-1.20-C4`, that the acting group may be replaced by a finite one, stated as
"the kernel of `ρ` is open of finite index", which by the Galois correspondence is exactly the
assertion that the whole structure is defined over a finite Galois subextension.
**S1 G4 finding C-2.** Conjunct 3 as stated in Lean produces `FiniteDimensional K L₀ ∧
Normal K L₀`, where clause `RQ2-1.20-C3` says "finite **Galois**"; the two agree here and the
statement is not weaker, because separability descends to subextensions — `IsGalois K L` gives
`Algebra.IsSeparable K L`, hence `Algebra.IsSeparable K L₀` for the intermediate field `L₀`, and
`Normal K L₀` together with that separability *is* `IsGalois K L₀`.
-/
theorem factorsThroughFinite [IsSepClosure K M] (Γ : RationalQuiver K L) :
    Function.Surjective (galInflate K L M) ∧
    Continuous (galInflate K L M) ∧
    (∃ L₀ : IntermediateField K L, FiniteDimensional K L₀ ∧ Normal K L₀ ∧
      L₀.fixingSubgroup ≤ Γ.ρ.ker) ∧
    (IsOpen (Γ.ρ.ker : Set Gal(L/K)) ∧ Γ.ρ.ker.FiniteIndex) := by
  -- Clause C1 and C2 are the surjectivity and continuity of the inflation map.
  have hopen : IsOpen ((Γ.ρ.ker : Subgroup Gal(L/K)) : Set Gal(L/K)) := Γ.isOpen_ker_ρ
  refine ⟨surjective_galInflate K L M, continuous_galInflate K L M, ?_, hopen, ?_⟩
  · -- Clause C3: an open subgroup is a neighbourhood of `1`, so by the Krull basis it contains
    -- the fixing subgroup of a finite *normal* `L₀/K` — which is the finite Galois quotient
    -- `Gal(K^sep/K) → Gal(L₀/K)` the source names.
    have hmem : ((Γ.ρ.ker : Subgroup Gal(L/K)) : Set Gal(L/K)) ∈ nhds (1 : Gal(L/K)) :=
      hopen.mem_nhds (one_mem _)
    rw [krullTopology_mem_nhds_one_iff_of_normal] at hmem
    obtain ⟨L₀, hfin, hnorm, hsub⟩ := hmem
    exact ⟨L₀, hfin, hnorm, hsub⟩
  · -- Clause C4: `Gal(L/K)` is compact (profinite), so an open subgroup has finite index —
    -- i.e. the rational structure is defined over a finite Galois subextension.
    haveI : Finite (Gal(L/K) ⧸ (Γ.ρ.ker : Subgroup Gal(L/K))) :=
      Subgroup.quotient_finite_of_isOpen _ hopen
    exact Subgroup.finiteIndex_of_finite_quotient

end RationalQuiver

end RationalQuivers
