module

public import RationalQuivers.Species.AntiEquivalence
public import RationalQuivers.Quiver.BaseChange

@[expose] public section

/-!
# General base change of `K`-rational quivers

Formalizes Definition `def:quiverbasechangegeneral` and Lemma `lem:quiverbasechangecompat` at the
end of §2.3 of `latex/rational_quivers.tex` (v2 census `RQ2-2.39`, `RQ2-2.40`). Work package
WP-7b of the v2 line.

## Main definitions / results
* `RationalQuivers.EtaleSpecies.exists_isSplitBy` — every étale species over a field `F` has a
  finite Galois splitting field (the §2.3 standing hypothesis is always satisfiable); the
  non-vacuity witness for `RQ2-2.39`.
* `RationalQuivers.RationalQuiver.baseChangeGeneral` — Definition `def:quiverbasechangegeneral`
  (census `RQ2-2.39`): `N ⊗_K Γ_K := Γ_N(S(Γ_K) ⊗_K N)` for an **arbitrary** extension `N/K`.
* `RationalQuivers.RationalQuiver.exists_isSplitBy_baseChange` — for every `Γ_K` and every `N/K`
  the splitting field that `baseChangeGeneral` takes as an argument exists.
* `RationalQuivers.RationalQuiver.baseChange_isSplitBy` — for an intermediate field `L/E'/K` with
  `L/K` finite, `L` itself splits `S(Γ_K) ⊗_K E'`.
* `RationalQuivers.RationalQuiver.baseChangeGeneral_iso_baseChange` — Lemma
  `lem:quiverbasechangecompat` (census `RQ2-2.40`), as an explicit isomorphism of `E'`-rational
  quivers between the general base change and the base change `RationalQuiver.baseChange` of
  `def:quiverbasechange` (`RQ2-1.05`).

## Implementation notes

**Reuse.** The isomorphism is assembled from two existing pieces of `Species/AntiEquivalence.lean`
and nothing else: the base-change comparison `EtaleSpecies.bcQuiverHom` (an isomorphism by
`EtaleSpecies.bcQuiverHom_isIso`), `Γ_{E'}(S ⊗_K E') ⟶ E' ⊗_K Γ_K(S)`, built there for the
quiver-side proof of `RQ2-2.08-C1`; and the unit `RationalQuiver.unitApp : Γ_K ⟶ Γ_K(S(Γ_K))` of the
anti-equivalence `RQ2-2.13` (an isomorphism by `RationalQuiver.unitApp_isIso`). The composite

`Γ_{E'}(S(Γ_K) ⊗_K E') ≅ E' ⊗_K Γ_K(S(Γ_K)) ≅ E' ⊗_K Γ_K`

is the second iso followed by `RationalQuiver.baseChange` applied to the inverse of the unit. On
vertices it sends `(k, α : L'_k → L)` to the vertex of `Γ_K` whose embedding `L_{π(k)} → L` is
`α ∘ (L_{π(k)} → N ⊗_K L_{π(k)} ↠ L'_k)`; nothing in it is chosen beyond what the definitions
of `S(Γ_K)` (orbit representatives) and of `S ⊗_K E'` (the decomposition
`eq:speciesvertexdecomposition`) already choose.

**Splitting fields.** `Γ_N(−)` (`EtaleSpecies.toRationalQuiver`, `RQ2-2.12`) is built over an
explicit finite Galois splitting field, the §2.3 standing hypothesis `EtaleSpecies.IsSplitBy`;
`baseChangeGeneral` therefore takes one as an argument, and `exists_isSplitBy_baseChange` shows
that the argument can always be supplied.
-/

universe u

namespace RationalQuivers

open CategoryTheory

namespace EtaleSpecies

/-! ### Existence of a finite Galois splitting field -/

section Exists

variable {F : Type u} [Field F]

/-- Distinct monic irreducible polynomials over a field are coprime.

@census none (helper for RQ2-2.39: non-vacuity)
-/
theorem isCoprime_of_irreducible_monic {p q : Polynomial F} (hp : Irreducible p)
    (hq : Irreducible q) (hpm : p.Monic) (hqm : q.Monic) (hne : p ≠ q) : IsCoprime p q := by
  refine (hp.coprime_iff_not_dvd).mpr fun hdvd => hne ?_
  exact Polynomial.eq_of_monic_of_associated hpm hqm
    (associated_of_dvd_dvd hdvd (hp.dvd_symm hq hdvd))

/-- A finite separable field extension `E/F` has a primitive element, whose minimal polynomial is
separable, irreducible and monic (the data `exists_isSplitBy` collects).

@census none (helper for RQ2-2.39: non-vacuity)
-/
theorem exists_primitive_minpoly (E : Type u) [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] :
    ∃ θ : E, IntermediateField.adjoin F {θ} = ⊤ ∧ (minpoly F θ).Separable ∧
      Irreducible (minpoly F θ) ∧ (minpoly F θ).Monic := by
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element F E
  have hint : IsIntegral F θ := Algebra.IsIntegral.isIntegral θ
  exact ⟨θ, hθ, Algebra.IsSeparable.isSeparable F θ, minpoly.irreducible hint, minpoly.monic hint⟩

/-- **Every étale `F`-species has a finite Galois splitting field.** Take the splitting field of
the product of the (pairwise distinct) minimal polynomials of primitive elements of the vertex
fields `L_i` and of the field factors of the edge algebras `{}_iM_j`. It is Galois because that
product is separable; each `L_i` and each field factor of `{}_iM_j` embeds into it because the
minimal polynomial of its primitive element splits there; and an `F`-algebra embedding into the
normal extension, resp. into a finite product of copies of it, is what `SplitAlg.splits_of_embedding`
and `SplitAlg.splits_of_pi_injective` turn into the two splitting fields of `IsSplitBy`.

@census none (helper for RQ2-2.39: non-vacuity witness of the splitting-field argument)
-/
theorem exists_isSplitBy (T : EtaleSpecies.{u} F) :
    ∃ (L' : Type u) (_ : Field L') (_ : Algebra F L'), T.IsSplitBy L' := by
  classical
  -- the field factors of the edge algebras
  let D : ∀ p : T.I × T.I, VertexSplitting F (T.M p.1 p.2) :=
    fun p => VertexSplitting.choose F (T.M p.1 p.2)
  -- the fields whose primitive elements we collect
  let Ω : Type u := T.I ⊕ (Σ p : T.I × T.I, (D p).J)
  haveI : Finite Ω := inferInstanceAs (Finite (T.I ⊕ (Σ p : T.I × T.I, (D p).J)))
  letI : Fintype Ω := Fintype.ofFinite Ω
  let E : Ω → Type u := fun ω => Sum.elim (fun i => T.L i) (fun c => (D c.1).F c.2) ω
  letI hEf : ∀ ω, Field (E ω) := fun ω => by
    cases ω with
    | inl i => exact (inferInstance : Field (T.L i))
    | inr c => exact (inferInstance : Field ((D c.1).F c.2))
  letI hEa : ∀ ω, Algebra F (E ω) := fun ω => by
    cases ω with
    | inl i => exact (inferInstance : Algebra F (T.L i))
    | inr c => exact (inferInstance : Algebra F ((D c.1).F c.2))
  have hEfin : ∀ ω, FiniteDimensional F (E ω) := fun ω => by
    cases ω with
    | inl i => exact (inferInstance : FiniteDimensional F (T.L i))
    | inr c => exact (inferInstance : FiniteDimensional F ((D c.1).F c.2))
  have hEsep : ∀ ω, Algebra.IsSeparable F (E ω) := fun ω => by
    cases ω with
    | inl i => exact (inferInstance : Algebra.IsSeparable F (T.L i))
    | inr c => exact (inferInstance : Algebra.IsSeparable F ((D c.1).F c.2))
  have hprim : ∀ ω, ∃ θ : E ω, IntermediateField.adjoin F {θ} = ⊤ ∧ (minpoly F θ).Separable ∧
      Irreducible (minpoly F θ) ∧ (minpoly F θ).Monic := fun ω => by
    haveI := hEfin ω
    haveI := hEsep ω
    exact exists_primitive_minpoly (E ω)
  choose θ hθtop hθsep hθirr hθmon using hprim
  let s : Finset (Polynomial F) := Finset.image (fun ω => minpoly F (θ ω)) Finset.univ
  let P : Polynomial F := ∏ q ∈ s, q
  have hmem : ∀ q ∈ s, ∃ ω, minpoly F (θ ω) = q := fun q hq => by
    obtain ⟨ω, -, hω⟩ := Finset.mem_image.mp hq
    exact ⟨ω, hω⟩
  have hsep : P.Separable := by
    refine Polynomial.separable_prod' (f := id) ?_ ?_
    · intro x hx y hy hxy
      obtain ⟨ω, rfl⟩ := hmem x hx
      obtain ⟨ω', rfl⟩ := hmem y hy
      exact isCoprime_of_irreducible_monic (hθirr ω) (hθirr ω') (hθmon ω) (hθmon ω') hxy
    · intro x hx
      obtain ⟨ω, rfl⟩ := hmem x hx
      exact hθsep ω
  have hP0 : P ≠ 0 := hsep.ne_zero
  haveI : IsGalois F P.SplittingField := IsGalois.of_separable_splitting_field hsep
  haveI : Normal F P.SplittingField := IsGalois.to_normal
  -- each collected field embeds into the splitting field
  have hemb : ∀ ω, Nonempty (E ω →ₐ[F] P.SplittingField) := fun ω => by
    refine IntermediateField.nonempty_algHom_of_adjoin_splits (S := {θ ω}) ?_ (hθtop ω)
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    haveI := hEfin ω
    refine ⟨Algebra.IsIntegral.isIntegral _, ?_⟩
    have hdvd : minpoly F (θ ω) ∣ P :=
      Finset.dvd_prod_of_mem (f := id) (Finset.mem_image_of_mem _ (Finset.mem_univ ω))
    exact Polynomial.Splits.of_dvd (Polynomial.SplittingField.splits P)
      (Polynomial.map_ne_zero hP0) (Polynomial.map_dvd _ hdvd)
  refine ⟨P.SplittingField, inferInstance, inferInstance, ?_⟩
  exact
    { galois := inferInstance
      findim := inferInstance
      splits_L := fun i x => SplitAlg.splits_of_embedding (hemb (Sum.inl i)).some x
      splits_M := fun i j x => by
        let τ : ∀ e : (D (i, j)).J, (D (i, j)).F e →ₐ[F] P.SplittingField :=
          fun e => (hemb (Sum.inr ⟨(i, j), e⟩)).some
        refine SplitAlg.splits_of_pi_injective
          (Pi.algHom F (fun _ : (D (i, j)).J => P.SplittingField) fun e =>
            (τ e).comp ((Pi.evalAlgHom F (D (i, j)).F e).comp (D (i, j)).equiv.toAlgHom)) ?_ x
        intro a b hab
        have h : ∀ e, τ e ((D (i, j)).equiv a e) = τ e ((D (i, j)).equiv b e) :=
          fun e => congrFun hab e
        exact (D (i, j)).equiv.injective (funext fun e => (τ e).injective (h e)) }

end Exists

end EtaleSpecies

namespace RationalQuiver

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-! ### Definition `def:quiverbasechangegeneral` -/

/-- **Definition** (`def:quiverbasechangegeneral`, general base change).
For a `K`-rational quiver `Γ_K` and an **arbitrary** field extension `N/K`, the *base change* of
`Γ_K` to `N` is the `N`-rational quiver

`N ⊗_K Γ_K := Γ_N(S(Γ_K) ⊗_K N)`

associated (`thm:KrationalquiveretaleKspeciesantiequivalence`) to the base change
`S(Γ_K) ⊗_K N` (`def:basechangeforspecies`) of the étale `K`-species `S(Γ_K)`.

@census    RQ2-2.39
@source    def:quiverbasechangegeneral
@clauses   RQ2-2.39-H1, RQ2-2.39-H2, RQ2-2.39-C1, RQ2-2.39-C2, RQ2-2.39-C3
@imports   none
@divergence JUSTIFIED_REFORMULATION (splitting field as an argument). `Γ_N(−)` of `RQ2-2.12`
(`EtaleSpecies.toRationalQuiver`) is built over an explicit splitting field — the §2.3 standing
hypothesis "let `L` be a splitting field … we may assume `L/N` finite and Galois", carried as
`EtaleSpecies.IsSplitBy` — so the definition takes a field `L'` over `N` and a proof
`hL' : (S(Γ_K) ⊗_K N).IsSplitBy L'` as arguments; the result lives in `RationalQuiver N L'`.
This is the same reformulation already recorded for `RQ2-2.12`. The argument is never vacuous:
`exists_isSplitBy_baseChange` produces an `L'` for **every** `Γ_K` and **every** `N/K` (the
splitting field of the minimal polynomials of primitive elements of the vertex fields and of the
field factors of the edge algebras), and the source's independence of the choice of `L'` is the
isomorphism-invariance of `Γ_N(−)` under change of splitting field, which is not restated here.
Clause `RQ2-2.39-H1` is the argument `Γ : RationalQuiver K L` (for some Galois `L/K`, finite or
not); clause `RQ2-2.39-H2` is the argument `N` with only `[Field N] [Algebra K N]`: no finiteness,
algebraicity, or embedding into `L` is assumed. Clause `RQ2-2.39-C1` is `Γ.toSpecies.baseChange N`
(`RQ2-2.09`, `RQ2-2.05`), an `EtaleSpecies N`; clause `RQ2-2.39-C2` is the body; clause
`RQ2-2.39-C3` is the name. Note that `S(Γ_K) ⊗_K N` involves the choice of the decomposition
`eq:speciesvertexdecomposition` (`VertexSplitting.choose`), as in the source.
-/
noncomputable def baseChangeGeneral (Γ : RationalQuiver K L) (N : Type u) [Field N] [Algebra K N]
    (L' : Type u) [Field L'] [Algebra N L'] (hL' : (Γ.toSpecies.baseChange N).IsSplitBy L') :
    RationalQuiver N L' :=
  (Γ.toSpecies.baseChange N).toRationalQuiver L' hL'

/-- **Non-vacuity of `baseChangeGeneral`.** For every `K`-rational quiver `Γ_K` and every field
extension `N/K` there is a finite Galois extension `L'/N` splitting `S(Γ_K) ⊗_K N`, i.e. an
admissible argument for `baseChangeGeneral`.

@census none (helper: G5 non-vacuity witness for RQ2-2.39)
-/
theorem exists_isSplitBy_baseChange (Γ : RationalQuiver K L) (N : Type u) [Field N]
    [Algebra K N] :
    ∃ (L' : Type u) (_ : Field L') (_ : Algebra N L'), (Γ.toSpecies.baseChange N).IsSplitBy L' :=
  (Γ.toSpecies.baseChange N).exists_isSplitBy

/-! ### Lemma `lem:quiverbasechangecompat` -/

variable [FiniteDimensional K L]

/-- For an intermediate field `L/E'/K` (with `L/K` finite Galois), `L` itself splits
`S(Γ_K) ⊗_K E'`; so `L` is an admissible splitting field for `baseChangeGeneral Γ E'`, and the
general base change can be compared with `def:quiverbasechange` inside `RationalQuiver E' L`.
This is `EtaleSpecies.baseChange_isSplitBy` applied to `RationalQuiver.toSpecies_isSplitBy`.

@census none (helper for RQ2-2.40; also a concrete G5 inhabitant of RQ2-2.39's argument)
-/
theorem baseChange_isSplitBy (Γ : RationalQuiver K L) (E' : IntermediateField K L) :
    (Γ.toSpecies.baseChange (E' : Type u)).IsSplitBy L :=
  Γ.toSpecies.baseChange_isSplitBy (E' : Type u) Γ.toSpecies_isSplitBy

/-- **Lemma** (`lem:quiverbasechangecompat`).
Let `Γ_K` be a `K`-rational quiver with respect to a Galois extension `L/K`, and let `L/E'/K` be an
intermediate field with `E'/K` finite. Then the base change `E' ⊗_K Γ_K` in the sense of
`def:quiverbasechangegeneral` is canonically isomorphic to the base change `E' ⊗_K Γ_K` in the
sense of `def:quiverbasechange`.

The isomorphism is the composite of the base-change comparison
`Γ_{E'}(S(Γ_K) ⊗_K E') ≅ E' ⊗_K Γ_K(S(Γ_K))` (`EtaleSpecies.bcQuiverHom`) with `E' ⊗_K −` applied
to the inverse of the anti-equivalence unit `Γ_K ≅ Γ_K(S(Γ_K))` (`RationalQuiver.unitApp`).

@census    RQ2-2.40
@source    lem:quiverbasechangecompat
@clauses   RQ2-2.40-H1, RQ2-2.40-H2, RQ2-2.40-C1, RQ2-2.40-C2
@imports   none
@divergence WEAKENED_OR_PARTIAL on clauses `RQ2-2.40-H1`, `RQ2-2.40-C1`, `RQ2-2.40-C2` (summary,
G2 review 2026-10-17: `H1` finite `L/K`; `C1` the general base change is compared only over the
splitting field `L` itself — independence of the choice of splitting field `L'` is not stated; `C2`
canonical as explicit data, naturality in `Γ_K` not stated). On `H1`: `L/K` is assumed **finite** Galois
(`[FiniteDimensional K L]`), whereas the source allows any Galois `L/K`. The restriction is forced by
the Lean form of `Γ_K(−)` (`RQ2-2.12`), which needs a *finite* Galois splitting field: the unit
`Γ_K ≅ Γ_K(S(Γ_K))` of `RQ2-2.13` is only available over a finite `L`
(`RationalQuiver.toSpecies_isSplitBy`). For infinite `L/K` the statement reduces to the finite case
through the finite quotient of `rmk:finitequotient` (`RQ2-1.20`), but that reduction is not
formalized here. Clause `RQ2-2.40-H2` is `E' : IntermediateField K L` with
`[FiniteDimensional K E']` (as for `RationalQuiver.baseChange`, `RQ2-1.05`). Clause `RQ2-2.40-C1`
is the type: an isomorphism in the category `RationalQuiver E' L` of `E'`-rational quivers, with the
general base change taken over the splitting field `L` (any proof `h` of `L` splitting
`S(Γ_K) ⊗_K E'` is accepted; `baseChange_isSplitBy` supplies one). Clause `RQ2-2.40-C2`
("canonically") is met by giving the isomorphism as **data**, a `def` built only from the canonical
maps of the comparison and the unit (restriction of embeddings along `L_i → E' ⊗_K L_i ↠ L'_k` on
vertices, and along `{}_iM_j → E' ⊗_K {}_iM_j → {}_kM'_l` on edges), rather than as a bare
`Nonempty`; its only choices are those already made in defining `S(Γ_K)` and `S(Γ_K) ⊗_K E'`.
Naturality in `Γ_K` is not stated.
-/
noncomputable def baseChangeGeneral_iso_baseChange (Γ : RationalQuiver K L)
    (E' : IntermediateField K L) [FiniteDimensional K E']
    (h : (Γ.toSpecies.baseChange (E' : Type u)).IsSplitBy L) :
    Γ.baseChangeGeneral (E' : Type u) L h ≅ (RationalQuiver.baseChange K L E').obj Γ :=
  @asIso _ _ _ _ (EtaleSpecies.bcQuiverHom Γ.toSpecies E' Γ.toSpecies_isSplitBy h)
      (EtaleSpecies.bcQuiverHom_isIso Γ.toSpecies E' Γ.toSpecies_isSplitBy h) ≪≫
    (RationalQuiver.baseChange K L E').mapIso (@asIso _ _ _ _ Γ.unitApp Γ.unitApp_isIso).symm

/-- The forward map of `baseChangeGeneral_iso_baseChange`, spelled out: the base-change comparison
followed by `E' ⊗_K −` of the inverse of the unit.

@census none (helper: explicit form of clause RQ2-2.40-C2)
-/
theorem baseChangeGeneral_iso_baseChange_hom (Γ : RationalQuiver K L)
    (E' : IntermediateField K L) [FiniteDimensional K E']
    (h : (Γ.toSpecies.baseChange (E' : Type u)).IsSplitBy L) :
    (Γ.baseChangeGeneral_iso_baseChange E' h).hom
      = EtaleSpecies.bcQuiverHom Γ.toSpecies E' Γ.toSpecies_isSplitBy h ≫
          (RationalQuiver.baseChange K L E').map
            (@asIso _ _ _ _ Γ.unitApp Γ.unitApp_isIso).inv := rfl

/-- **G5 inhabitant for `RQ2-2.40`.** With the splitting proof of `baseChange_isSplitBy`, the
isomorphism is available for every `Γ_K` and every finite intermediate `E'`.

@census none (helper: G5 inhabitant for RQ2-2.40)
-/
noncomputable def baseChangeGeneral_iso_baseChange' (Γ : RationalQuiver K L)
    (E' : IntermediateField K L) [FiniteDimensional K E'] :
    Γ.baseChangeGeneral (E' : Type u) L (Γ.baseChange_isSplitBy E') ≅
      (RationalQuiver.baseChange K L E').obj Γ :=
  Γ.baseChangeGeneral_iso_baseChange E' (Γ.baseChange_isSplitBy E')

end RationalQuiver

end RationalQuivers
