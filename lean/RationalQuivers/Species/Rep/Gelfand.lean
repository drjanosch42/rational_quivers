import RationalQuivers.Species.Examples
import RationalQuivers.Species.ToQuiver
import RationalQuivers.Species.Orbits
import RationalQuivers.Quiver.Rep.Nilpotent

/-!
# `ex:gelfand` — the `K`-rational Gelfand quiver and its étale species (census `RQ2-2.16`)

Formalizes Example `ex:gelfand` of §2.4 of `latex/rational_quivers.tex`.  The row was
**re-sequenced from S4 to S5** by coordinator ruling of 2026-08-30, because clause `RQ2-2.16-C3`
is a statement about `RationalQuiver.Rep` (stage S2) and `S2 → S5` is an edge of the stage DAG
while `S2 → S4` is not.  See `workflow/stages/S4/DESIGN-NOTES.md` §3.1 and the section note in
`Species/Examples.lean`, which is the handover this module discharges.

## Main definitions / results
* `RationalQuivers.Examples.gelfand_rationalStructure` — census `RQ2-2.16`: the `G`-action, its
  compatibility with the relation, the four fixed-field computations, the index set `I`, the
  associated étale species with its bimodules, the `c`-twist, and the `RQ2-2.13` reconstruction.
* `RationalQuivers.Examples.gelfandTwist` — the explicit `K`-rational representation of the
  Gelfand quiver on which the relation `a₋b₋ = a₊b₊` **fails**.
* `RationalQuivers.Examples.gelfand_relation_conjugate` — what `G`-equivariance *does* give:
  the two composites are `c`-**conjugate**.
* `RationalQuivers.Examples.gelfand_relation_not_consequence` — **finding S5-F1** (closed
  2026-08-30 by a source repair): `gelfandTwist` refuted the literal reading of `RQ2-2.16-C3`
  **as that clause read before census r7**.  Since r7 `C3` states the `φ_⋆`-conjugacy, which
  `gelfand_relation_conjugate` claims directly, and this witness discharges the NEW clause
  `RQ2-2.16-C11` — the source's own express disclaimer — which is what its `@clauses` cell cites.
  (Re-tensed 2026-09-12, the seven-errata amendment's close-out round, `V-ERR-7`.)
* `RationalQuivers.Examples.gelfandNilTwist`,
  `RationalQuivers.Examples.gelfandNilTwist_isNilpotent`,
  `RationalQuivers.Examples.gelfand_relation_not_consequence_nil` — the coordinator-mandated
  probe (2026-08-30) of the **nilpotent** reading of the then-`RQ2-2.16-C3`, and its refutation;
  the nilpotent witness for `RQ2-2.16-C11` since r7.  (Re-tensed 2026-09-12, `V-ERR-7`.)

## Finding **S5-F1** — **CLOSED 2026-08-30 by a source repair** (census r7, `census-v1.4`); its
three downstream sites closed 2026-09-11 and this section re-tensed 2026-09-12 (rounds 4, 5 and the
amendment's close-out round)

> **Dated banner (`WORKFLOW.md` R6 / §7 sweep).** Stage S5 found that `ex:gelfand`'s sentence
> *"the relation is a consequence of `G`-equivariance and hence may be dropped when considering
> representations over `ℚ`"* is **false**, in every reading tried. The author accepted the finding
> and an editor repaired the source; census r7 re-cut this row's clause set accordingly. The
> corrected remark now prints the conjugacy identity, the `G`-stability of the relation set, the
> "only one of the two need be imposed" consequence, and an express disclaimer. **What this module
> asserted as a refutation of the source is now a direct claim of the corrected clauses** — the
> `JUSTIFIED_REFORMULATION` that stood on `RQ2-2.16-C3` is gone, and the two counterexamples now
> discharge `RQ2-2.16-C11`, the disclaimer, rather than contradicting `C3`.
>
> *(Dated note, 2026-10-03, `R-FR-9`, final-release WP-16b, stale item R7.)* The banner describes
> the source at census r7. Census r18 (FA-05 / A-1) replaced the "only one of the two need be
> imposed" consequence by the descent criterion: the relation holds iff `φ_{a₋}φ_{b₋}` commutes with
> `φ_{⋆,c}`, i.e. is `K`-rational (clause `RQ2-2.16-C10`, the second conjunct of
> `gelfand_relation_iff_transpose`). Later quotations of the retired phrase in this module docstring
> are records of r7–r17.

The mathematics is unchanged and is recorded here because the clause texts are terse.

*What equivariance gives.*  `eq:koecheractiononrep` at `e = a₋` and at `e = b₋`, for the
non-trivial `c ∈ G`, reads

```
φ_{a₊} ∘ φ_{−,c} = φ_{⋆,c} ∘ φ_{a₋}        φ_{b₊} ∘ φ_{⋆,c} = φ_{−,c} ∘ φ_{b₋}
```

whence `φ_{a₊}φ_{b₊}φ_{⋆,c} = φ_{a₊}φ_{−,c}φ_{b₋} = φ_{⋆,c}φ_{a₋}φ_{b₋}`, i.e.

```
φ_{a₊}φ_{b₊} = φ_{⋆,c} ∘ (φ_{a₋}φ_{b₋}) ∘ φ_{⋆,c}⁻¹ .
```

That is `gelfand_relation_conjugate`, and it is now exactly what clause `RQ2-2.16-C3` states.

*Why the relation is strictly stronger — clause `RQ2-2.16-C11`.*  `G_⋆ = G`, so `M(⋆)` carries a
semi-linear `G`-action and descends to the `K`-form `M(⋆)^G` by `thm:galoisdescent`;
`End_L(M(⋆))` correspondingly carries the Galois action `A ↦ φ_{⋆,c} A φ_{⋆,c}⁻¹`, whose fixed
points are the endomorphisms **defined over `K`**.  The relation therefore says exactly that
`φ_{a₋}φ_{b₋}` is defined over `K` — a condition *on the representation*.  Nothing forces it: the
vertex stabilizers at `±` are trivial (`stabilizer_gelfandVertex_eq_bot`), so the edge maps on the
`−` side are unconstrained and `c` only *determines* the `+` side from them.

*The two witnesses.*  `gelfandTwist α` is `Rep.constL` with the `Gal(L/K)`-equivariant scalar
family `t = (a₋ ↦ α, b₋ ↦ 1, a₊ ↦ c α, b₊ ↦ 1)`; its composites are multiplication by `α` and by
`c α`.  `gelfandNilTwist α` is two-dimensional at every vertex and **nilpotent**, and its
composites still differ — so the disclaimer holds in the nilpotent subcategory too, which is the
reading §2.4's context suggests.  Both are `def`s with no `sorry`.  Together they discharge `C11`.

*Where the erratum went.*  Author-approved and applied; `ATTESTATION.md` **AN-33** carries the
adjudication, and `stages/S5/DESIGN-NOTES.md` §2 keeps the origin diagnosis (the species-side
collapse `ℚ[i] ⊗ ℚ[i] ≅ ℚ[i] × ℚ[i]` makes the relation *look* redundant, which shows only that it
is not needed to *define* the species).

*The last of the three sites, closed 2026-09-11; its rendering completed 2026-09-12, rounds 4–5.*  `AN-33`'s main finding was repaired in
`ex:gelfand` itself at census r7, but three downstream sites kept the withdrawn "the relation may
be dropped" reading: the abstract, the introduction, and §5.3's species corollary
(`AN-33(iii)`).  On **2026-09-11** the paper's author ruled `AN-33(iii)` — **option (b)**, against
the resolution dossier's recommendation of option (a) (`workflow/reports/AUTHOR-QUEUE.md`, the
`AUTHOR RULING, 2026-09-11` block; `latex/` edit `388f0f8`).  §2.5 now **defines relations for a
`K`-species intrinsically** (`def:speciesrelations`, census `RQ2-2.36`) and
`ex:gelfandspeciesrelation` names the single species-side relation `R_Gelfand = ℚ·√-1` (census
`RQ2-2.37`); §5.3's corollary is stated against `Rep^nil(S(Γ_ℚ), R_Gelfand)`, and the abstract's
"superfluous" and the introduction's "need not be equipped with a relation" are gone, replaced by
"only one of the two `c`-conjugate relations need be imposed".  **`RQ2-2.36` is rendered** in this
stage, in `Species/Rep/Relations.lean` (round 3, 2026-09-11).  **Re-tensed 2026-09-12** (round 4,
`R-PROC-4`): `RQ2-2.37`'s clauses `C1` and `C2` — the identification `{}_⋆M_p ≅ ℚ[√-1]` and
`R_Gelfand` itself — are rendered in this stage too, in `Species/Rep/GelfandRelation.lean`.
**Re-tensed again 2026-09-12** (round 5, `R-PROC-4`, coordinator ruling `R-ERR-5`): clause `C3`,
`eq:gelfandspeciescomposite`, and clause `C4` are rendered in the same module
(`GelfandRelation.exists_beta`, `satisfies_RGelfand_iff_relation`, `satisfies_RGelfand_iff_pair`,
`RGelfand_genuine`), `RQ2-2.37` is **claimed** there — by `satisfies_RGelfand_iff_relation`, whose `@clauses` cell cites
`RQ2-2.37-C3`, the module's other declarations citing `C1`, `C2` and `C4` (sharpened 2026-09-12,
the amendment's close-out round: this sentence read *"with all four clauses cited"*, which
over-stated the claimant's own cell) — and the
coincidence theorem `GelfandRelation.repNilRel_RGelfand_iff` let S8's `Gelfand/Corollaries.lean`
state `RQ-5.06-C1` against the **intrinsic** `Species.RepNilRel … R_Gelfand`
(`species_equivalence_intrinsic`); the transported `RepNilRelSpeciesGelfand` was kept there as a
lemma.  *(2026-10-21, O-V2-6 round 2: v1's `Gelfand/Corollaries.lean` was deleted with the v1
Q-chain at WP-13, `ae9eda9`.  On the v2 line `RQ2-5.06`'s claimant is
`Gelfand.Species.species_equivalence_intrinsic` in `Gelfand/Species/Rational.lean`, stated against
the intrinsic target; the coincidence theorem reaches it through
`Gelfand.Species.repNilRel_RE_iff`.)*  (Superseded round-4 wording: *"clause `C3` … is still not
rendered, so `RQ2-2.37` is
claimed by no declaration and S8's `Gelfand/Corollaries.lean` keeps the transported
`RepNilRelSpeciesGelfand` as `RQ-5.06-C1`'s target"*; superseded round-3 wording: *"`RQ2-2.37` —
`R_Gelfand` itself and `eq:gelfandspeciescomposite` — is not yet rendered"*.)

The two witnesses below are untouched by the ruling and gained a second consumer: through `F` they
were what v1's `Gelfand.relation_not_omittable` (census clause `RQ-5.06-C2`, the sentence the
option-(b) edit added after §5.3's corollary) turned into a nilpotent `S(Γ_ℚ)`-representation
outside the corollary's target.  *(2026-10-21, O-V2-6 round 2: that declaration was deleted with
the v1 Q-chain at WP-13, `ae9eda9`; on the v2 line `Gelfand.Species.relation_not_omittable`
(`Gelfand/Species/Equivalence.lean`, clause `RQ2-5.16-C7`) does the same with `gelfandNilTwist`
over every `E ∌ √-1`.)*

## Implementation notes
The quadratic extension is arbitrary (`Nat.card Gal(L/K) = 2`), following `MD-S4-03` and the
`RQ2-2.14`/`RQ2-2.15` convention, so that stage S8 consumes one and the same object; the source's
`ℚ[√-1]/ℚ` is the instance `K = ℚ`, and `ℂ/ℝ` is the in-tree inhabitant
(`RationalQuivers.card_gal_complex_real`).
-/

namespace RationalQuivers

open RationalQuiver RQuiver MulAction

namespace Examples

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

/-! ### `RQ2-2.13`'s reconstruction, in the form the example rows consume

These are **general** lemmas, not Gelfand-specific: they say that the étale species of a rational
quiver reconstructs that quiver's vertex and edge sets.  They live here because `RQ2-2.16-C8` is
their first consumer and because stage S4's `AntiEquivalence.lean` is frozen (byte-untouched since
`stage-S4-v1`); adding to it would fork `main`'s copy from the tag's for no mathematical gain.

**Carried obligation for close-out.**  Their natural long-term home is S4's module.  Relocation is
DEFERRED to a sanctioned move at S9 if the examples stage wants them upstream; recorded here so the
close-out inherits the debt rather than discovering it.

The commutative-algebra core — a maximal ideal of a finite product of fields is the kernel of a
projection — is **not** built here: it is `EtaleSpecies.maximalSpectrum_pi`, which stage S4 already
proved for `RQ2-2.12`'s `Specm` computations.  Only the injectivity half is new, and it is one
`Pi.single` witness.

@census none (`RQ2-2.13`'s object content, consumed forward by the example rows)
-/

section Reconstruction

variable {ι : Type} [Finite ι] {F : ι → Type} [∀ e, Field (F e)] [∀ e, Algebra K (F e)]

/-- Distinct projections of a finite product of fields have distinct kernels: `Pi.single e 1` lies
in the kernel of every other projection and not in its own.  @census none (helper) -/
theorem ker_evalAlgHom_injective :
    Function.Injective (fun e : ι => RingHom.ker (Pi.evalAlgHom K F e)) := by
  classical
  intro e e' hee
  have hee' : RingHom.ker (Pi.evalAlgHom K F e) = RingHom.ker (Pi.evalAlgHom K F e') := hee
  by_contra hne
  have h1 : (Pi.single e' (1 : F e') : ∀ e, F e) ∈ RingHom.ker (Pi.evalAlgHom K F e) := by
    simp [RingHom.mem_ker, Pi.single_apply, Ne.symm hne]
  rw [hee'] at h1
  have h2 : (Pi.evalAlgHom K F e') (Pi.single e' (1 : F e')) = 1 := by simp
  rw [RingHom.mem_ker, h2] at h1
  exact one_ne_zero h1

/-- The kernel of a projection is maximal: the quotient is the field `F e`.
@census none (helper) -/
theorem ker_evalAlgHom_isMaximal (e : ι) :
    (RingHom.ker (Pi.evalAlgHom K F e)).IsMaximal := by
  classical
  exact RingHom.ker_isMaximal_of_surjective (Pi.evalAlgHom K F e).toRingHom
    (fun a => ⟨Pi.single e a, by simp⟩)

/-- **The maximal spectrum of a finite product of fields is its index set.**  Surjectivity is stage
S4's `maximalSpectrum_pi`; injectivity is `ker_evalAlgHom_injective`.
@census none (helper for `RQ2-2.13`'s reconstruction) -/
noncomputable def maximalSpectrumPiEquiv : MaximalSpectrum (∀ e, F e) ≃ ι := by
  classical
  refine Equiv.ofBijective (fun m => (EtaleSpecies.maximalSpectrum_pi (K := K) m).choose) ?_
  constructor
  · intro m m' hmm
    have hmm' : (EtaleSpecies.maximalSpectrum_pi (K := K) m).choose
        = (EtaleSpecies.maximalSpectrum_pi (K := K) m').choose := hmm
    refine MaximalSpectrum.ext ?_
    rw [(EtaleSpecies.maximalSpectrum_pi (K := K) m).choose_spec,
      (EtaleSpecies.maximalSpectrum_pi (K := K) m').choose_spec, hmm']
  · intro e
    refine ⟨⟨RingHom.ker (Pi.evalAlgHom K F e),
      ker_evalAlgHom_isMaximal (K := K) (F := F) e⟩, ?_⟩
    refine ker_evalAlgHom_injective (K := K) (F := F) ?_
    exact ((EtaleSpecies.maximalSpectrum_pi (K := K)
      (⟨RingHom.ker (Pi.evalAlgHom K F e),
        ker_evalAlgHom_isMaximal (K := K) (F := F) e⟩)).choose_spec).symm


variable {X : Type} [MulAction Gal(L/K) X]

/-- `σ` and `τ` translate `x` the same way **exactly** when they agree on `L(x)`.  One direction is
`smul_eq_of_stabField_apply_eq`; the other is the Galois correspondence
`fixingSubgroup (L^{G_x}) = G_x`.  @census none (helper) -/
theorem smul_eq_iff_stabField_apply_eq (x : X)
    (hx : IsOpen ((stabilizer Gal(L/K) x : Subgroup Gal(L/K)) : Set Gal(L/K)))
    (σ τ : Gal(L/K)) :
    σ • x = τ • x ↔ ∀ α : stabField K L x, σ (α : L) = τ (α : L) := by
  refine ⟨fun hst α => ?_, smul_eq_of_stabField_apply_eq hx⟩
  have hcl : IsClosed ((stabilizer Gal(L/K) x : Subgroup Gal(L/K)) : Set Gal(L/K)) :=
    Subgroup.isClosed_of_isOpen _ hx
  have h1 : (stabField K L x).fixingSubgroup = stabilizer Gal(L/K) x :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨stabilizer Gal(L/K) x, hcl⟩
  have hmem : τ⁻¹ * σ ∈ stabilizer Gal(L/K) x := by
    rw [mem_stabilizer_iff, mul_smul, hst, inv_smul_smul]
  rw [← h1, IntermediateField.mem_fixingSubgroup_iff] at hmem
  have h2 : (τ⁻¹ * σ) (α : L) = (α : L) := hmem (α : L) α.2
  rw [AlgEquiv.mul_apply] at h2
  calc σ (α : L) = τ (τ⁻¹ (σ (α : L))) := by
        rw [show τ (τ⁻¹ (σ (α : L))) = (τ * τ⁻¹) (σ (α : L)) from rfl, mul_inv_cancel]
        rfl
  _ = τ (α : L) := by rw [h2]

/-- **`RQ2-2.13-C4`'s content**: `σ ↦ σ|_{L(x)}` identifies the orbit of `x` with `Hom_K(L(x), L)`.
Transitivity is `exists_galois_comp_eq`; the fibres are single points by
`smul_eq_iff_stabField_apply_eq`.  @census none (helper for the reconstruction) -/
noncomputable def stabFieldHomEquivOrbit (x : X)
    (hx : IsOpen ((stabilizer Gal(L/K) x : Subgroup Gal(L/K)) : Set Gal(L/K))) :
    (stabField K L x →ₐ[K] L) ≃ orbit Gal(L/K) x := by
  classical
  have hext : ∀ φ : stabField K L x →ₐ[K] L, ∃ σ : Gal(L/K),
      (σ : L →ₐ[K] L).comp (IntermediateField.val (stabField K L x)) = φ :=
    fun φ => EtaleSpecies.exists_galois_comp_eq L (stabField K L x)
      (IntermediateField.val (stabField K L x)) φ
  refine Equiv.ofBijective (fun φ => ⟨(hext φ).choose • x, ⟨(hext φ).choose, rfl⟩⟩) ?_
  constructor
  · intro φ ψ hpq
    have hs : (hext φ).choose • x = (hext ψ).choose • x := congrArg Subtype.val hpq
    have hagree := (smul_eq_iff_stabField_apply_eq K L x hx _ _).mp hs
    rw [← (hext φ).choose_spec, ← (hext ψ).choose_spec]
    exact AlgHom.ext fun α => hagree α
  · rintro ⟨y, σ, rfl⟩
    refine ⟨(σ : L →ₐ[K] L).comp (IntermediateField.val (stabField K L x)), ?_⟩
    refine Subtype.ext ?_
    refine (smul_eq_iff_stabField_apply_eq K L x hx _ _).mpr fun α => ?_
    exact congrArg (fun g : stabField K L x →ₐ[K] L => g α)
      (hext ((σ : L →ₐ[K] L).comp (IntermediateField.val (stabField K L x)))).choose_spec


/-- **`RQ2-2.13`'s reconstruction on vertices**: the étale species of a rational quiver has `Γ.V`
as its vertex set.  `Σ` over the orbits, fibrewise `stabFieldHomEquivOrbit`, then mathlib's
orbit decomposition.  @census none (`RQ2-2.13`'s object content, consumed forward) -/
noncomputable def vertexSetEquivV (Γ : RationalQuiver K L) :
    EtaleSpecies.vertexSet Γ.toSpecies L ≃ Γ.V :=
  (Equiv.sigmaCongrRight (fun i : Γ.VertexOrbit =>
      stabFieldHomEquivOrbit K L (Γ.vertexRep i) (Γ.isOpen_stabilizer_V _))).trans
    (MulAction.selfEquivSigmaOrbits Gal(L/K) Γ.V).symm


/-- **Edge reconstruction, step 1**: `Specm {}_iM_j` is the set of edge orbits from `i` to `j`.
Immediate from `maximalSpectrumPiEquiv`, because `Γ.edgeAlgebra i j` IS the product
`∀ ε : Γ.EdgeOrbit i j, L(e_ε)`.  @census none (helper) -/
noncomputable def edgeSpectrumEquiv (Γ : RationalQuiver K L) (i j : Γ.VertexOrbit) :
    MaximalSpectrum (Γ.toSpecies.M i j) ≃ Γ.EdgeOrbit i j :=
  maximalSpectrumPiEquiv (K := K) (ι := Γ.EdgeOrbit i j)
    (F := fun ε : Γ.EdgeOrbit i j => (Γ.edgeOrbitField ε : Type))


/-- **Edge reconstruction, step 2**: the residue field at `ε` is the `ε`-th factor.  The maximal
ideal IS the kernel of the `ε`-th projection (`maximalSpectrum_pi`), and that projection is
surjective, so the quotient is the factor.  @census none (helper) -/
noncomputable def residueFieldEquiv (Γ : RationalQuiver K L) (i j : Γ.VertexOrbit)
    (m : MaximalSpectrum (Γ.toSpecies.M i j)) :
    EtaleSpecies.residueField Γ.toSpecies ⟨(i, j), m⟩
      ≃ₐ[K] (Γ.edgeOrbitField (edgeSpectrumEquiv K L Γ i j m)) := by
  classical
  have hker : m.asIdeal = RingHom.ker (Pi.evalAlgHom K
      (fun ε : Γ.EdgeOrbit i j => (Γ.edgeOrbitField ε : Type))
      (edgeSpectrumEquiv K L Γ i j m)) :=
    (EtaleSpecies.maximalSpectrum_pi (K := K) m).choose_spec
  have hsurj : Function.Surjective (Pi.evalAlgHom K
      (fun ε : Γ.EdgeOrbit i j => (Γ.edgeOrbitField ε : Type))
      (edgeSpectrumEquiv K L Γ i j m)) := fun a => ⟨Pi.single _ a, by simp⟩
  have hk1 : RingHom.ker (Γ.toSpecies.residueMap ⟨(i, j), m⟩) = m.asIdeal := Ideal.mk_ker
  exact ((Ideal.quotientKerAlgEquivOfSurjective
      (EtaleSpecies.residueMap_surjective Γ.toSpecies ⟨(i, j), m⟩)).symm.trans
    ((Ideal.quotientEquivAlgOfEq K (hk1.trans hker)).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurj)))


/-- Precomposition with a `K`-algebra isomorphism.  @census none (helper) -/
def algHomCongrLeft {A B : Type} [Field A] [Field B] [Algebra K A] [Algebra K B]
    (e : A ≃ₐ[K] B) : (A →ₐ[K] L) ≃ (B →ₐ[K] L) where
  toFun φ := φ.comp e.symm.toAlgHom
  invFun ψ := ψ.comp e.toAlgHom
  left_inv φ := by ext a; simp
  right_inv ψ := by ext b; simp

/-- Every edge lies in exactly one `E_{ij}`: `E` is the total space of the fibration by the pair of
endpoint classes.  @census none (helper) -/
def edgePartitionEquiv (Γ : RationalQuiver K L) :
    (Σ p : Γ.VertexOrbit × Γ.VertexOrbit, Γ.edgeSet p.1 p.2) ≃ Γ.E :=
  (Equiv.sigmaCongrRight (fun p : Γ.VertexOrbit × Γ.VertexOrbit =>
      Equiv.subtypeEquivRight (fun e : Γ.E => by
        constructor
        · rintro ⟨h1, h2⟩
          exact Prod.ext h1 h2
        · intro hp
          exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩))).trans
    (Equiv.sigmaFiberEquiv (fun e : Γ.E =>
      (Γ.vertexClass (Γ.toRQuiver.source e), Γ.vertexClass (Γ.toRQuiver.target e))))

/-- The orbit of a point of a `G`-stable subset is the orbit of the point.  @census none -/
noncomputable def orbitCoeEquiv (Γ : RationalQuiver K L) {i j : Γ.VertexOrbit}
    (x : Γ.edgeSet i j) : orbit Gal(L/K) x ≃ orbit Gal(L/K) ((x : Γ.E)) := by
  refine Equiv.ofBijective (fun y => ⟨((y : Γ.edgeSet i j) : Γ.E), ?_⟩) ?_
  · obtain ⟨y, σ, hσ⟩ := y
    exact ⟨σ, congrArg Subtype.val hσ⟩
  · constructor
    · intro y y' hyy
      have h1 : (((y : Γ.edgeSet i j) : Γ.E)) = (((y' : Γ.edgeSet i j) : Γ.E)) :=
        congrArg (fun z : orbit Gal(L/K) ((x : Γ.E)) => (z : Γ.E)) hyy
      exact Subtype.ext (Subtype.ext h1)
    · rintro ⟨z, σ, hσ⟩
      exact ⟨⟨σ • x, ⟨σ, rfl⟩⟩, Subtype.ext hσ⟩

/-- **Edge reconstruction, step 3**: the fibre of `E(S(Γ))` over the index pair `(i,j)` is
`E_{ij}`.  @census none (helper) -/
noncomputable def edgeFiberEquiv (Γ : RationalQuiver K L) (i j : Γ.VertexOrbit) :
    (Σ m : MaximalSpectrum (Γ.toSpecies.M i j),
        (EtaleSpecies.residueField Γ.toSpecies ⟨(i, j), m⟩ →ₐ[K] L)) ≃ Γ.edgeSet i j :=
  (Equiv.sigmaCongr (edgeSpectrumEquiv K L Γ i j)
      (fun m => algHomCongrLeft K L (residueFieldEquiv K L Γ i j m))).trans
    ((Equiv.sigmaCongrRight (fun ε : Γ.EdgeOrbit i j =>
        (stabFieldHomEquivOrbit K L (Γ.edgeRep ε) (Γ.isOpen_stabilizer_E _)).trans
          (orbitCoeEquiv K L Γ (Quotient.out ε)).symm)).trans
      (MulAction.selfEquivSigmaOrbits Gal(L/K) (Γ.edgeSet i j)).symm)

/-- **`RQ2-2.13`'s reconstruction on edges**: the étale species of a rational quiver has `Γ.E` as
its edge set.  @census none (`RQ2-2.13`'s object content, consumed forward) -/
noncomputable def edgeSetEquivE (Γ : RationalQuiver K L) :
    EtaleSpecies.edgeSet Γ.toSpecies L ≃ Γ.E :=
  (Equiv.sigmaAssoc (fun p : Γ.VertexOrbit × Γ.VertexOrbit =>
      fun m : MaximalSpectrum (Γ.toSpecies.M p.1 p.2) =>
        (EtaleSpecies.residueField Γ.toSpecies ⟨p, m⟩ →ₐ[K] L))).trans
    ((Equiv.sigmaCongrRight (fun p : Γ.VertexOrbit × Γ.VertexOrbit =>
        edgeFiberEquiv K L Γ p.1 p.2)).trans
      (edgePartitionEquiv K L Γ))

end Reconstruction

/-! ### The relation of `ex:gelfand`, read in a representation -/

/-- The vertex `⋆` of the `K`-rational Gelfand quiver.  @census none (helper) -/
noncomputable def gelfandStar (h : Nat.card Gal(L/K) = 2) : (gelfandOfCardTwo K L h).V :=
  gelfandVertex K L h 1

/-- The length-two loop `a₋b₋` at `⋆`, as a path of the `K`-rational Gelfand quiver.  This is
S1's `RQuiver.pathMinus`, retyped; the underlying classical quiver is the same object.

@census none (helper for `RQ2-2.16-H2`)
-/
noncomputable def gelfandPathMinus (h : Nat.card Gal(L/K) = 2) :
    Quiver.Path (gelfandStar K L h) (gelfandStar K L h) := RQuiver.pathMinus

/-- The length-two loop `a₊b₊` at `⋆`.  @census none (helper for `RQ2-2.16-H2`) -/
noncomputable def gelfandPathPlus (h : Nat.card Gal(L/K) = 2) :
    Quiver.Path (gelfandStar K L h) (gelfandStar K L h) := RQuiver.pathPlus

/-- **The relation `a₋b₋ = a₊b₊` holds in the representation `M`.**

Post-r7 wording (finding **V-S5b-8**).  Before census r7, `RQ2-2.16-C3` claimed this relation was
*automatic*; the source defect **S5-F1** showed it is not, and r7 restated `C3` as the
`φ_⋆`-**conjugacy** of the two path maps (`gelfand_relation_conjugate`).  This predicate is now the
subject of the **disclaimer** clause `C11` (`gelfand_relation_not_consequence`, `…_nil`) — the
source's own express disclaimer, which those two witnesses *establish* rather than contradict —
rather than of an automatic-holding claim.  (Re-worded 2026-09-12, the seven-errata amendment's
close-out round, `V-ERR-7`: it read *"the refutation clauses `C11`"*, which the census row's own
`@divergence` cell at the foot of this file contradicts.)

@census none (helper: the subject of clauses `RQ2-2.16-H2`, `RQ2-2.16-C2`, `RQ2-2.16-C3`)
-/
def SatisfiesGelfandRelation (h : Nat.card Gal(L/K) = 2) (M : Rep (gelfandOfCardTwo K L h)) :
    Prop :=
  M.pathMap (gelfandPathMinus K L h) = M.pathMap (gelfandPathPlus K L h)

/-! ### The witness for finding **S5-F1** -/

omit [IsGalois K L] [FiniteDimensional K L] in
/-- The order-two Galois group of a quadratic extension is generated by an involution.

@census none (helper)
-/
theorem gal_sq_eq_one (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) : z * z = 1 := by
  obtain ⟨w, hw, hu⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
  by_contra hne
  have h1 : z * z = w := hu _ hne
  have h2 : z = w := hu _ hz
  rw [h2] at h1
  exact hz (by rw [h2]; simpa [h1] using (mul_right_cancel (b := w) (by rw [h1, one_mul])))

/-- **The witness of finding S5-F1.**  The `K`-rational representation of the Gelfand quiver with
`M(v) = L` at every vertex, `φ_{v,σ} = σ`, and edge maps multiplication by

  `a₋ ↦ α`,  `b₋ ↦ 1`,  `a₊ ↦ c α`,  `b₊ ↦ 1`.

The family of scalars is `Gal(L/K)`-equivariant — `c` exchanges `a₋ ↔ a₊` and `b₋ ↔ b₊` and
`c² = 1` — so this really is an object of `Rep(Γ_K)`; the proof is here, complete, and is the
load-bearing half of the finding.  Its two relation composites are multiplication by `α` and by
`c α`.

@census none (the witness for clause `RQ2-2.16-C11`; it refuted the pre-r7 `RQ2-2.16-C3` —
re-worded 2026-09-12, `V-ERR2b-7`)
-/
noncomputable def gelfandTwist (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) (α : L) :
    Rep (gelfandOfCardTwo K L h) :=
  Rep.constL (gelfandOfCardTwo K L h) (![α, 1, z α, 1]) (by
    intro σ e
    by_cases hσ : σ = 1
    · subst hσ; simp
    · have hρ := gelfandOfCardTwo_rho_apply K L h hσ
      obtain ⟨w, hw, hu⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
      have hzz : σ = z := by rw [hu σ hσ, ← hu z hz]
      subst hzz
      have hmove : σ • e = RQuiver.gelfandEdgeSwap e := by
        show (RQuiver.Aut.toPermE _ ((gelfandOfCardTwo K L h).ρ σ)) e = _
        rw [hρ]; rfl
      have hz2 : σ (σ α) = α := by
        have hs := gal_sq_eq_one K L h hσ
        calc σ (σ α) = (σ * σ) α := rfl
        _ = α := by rw [hs]; rfl
      rw [hmove]
      have key : ∀ f : Fin 4, ![α, 1, σ α, 1] (RQuiver.gelfandEdgeSwap f)
          = σ (![α, 1, σ α, 1] f) := by
        intro f
        fin_cases f <;> simp [RQuiver.gelfandEdgeSwap, hz2]
      exact key e)

/-- The vertex `⋆` is fixed by the `±`-swap: `c ⋆ = ⋆`, which is clause `RQ2-2.16-C1`'s
`c(⋆) = ⋆` read on the `K`-rational quiver.  It is what lets `φ_{⋆,c}` be an automorphism of
`M(⋆)` rather than a map between two different fibres, and hence what makes the conjugacy
statement below type-check without a transport.

@census none (helper for `RQ2-2.16-C1`)
-/
theorem gelfand_smul_star (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) :
    z • gelfandStar K L h = gelfandStar K L h := by
  have hρ := gelfandOfCardTwo_rho_apply K L h hz
  show (RQuiver.Aut.toPermV _ ((gelfandOfCardTwo K L h).ρ z)) (1 : Fin 3) = _
  rw [hρ]; rfl

/-- The edges of the `K`-rational Gelfand quiver, by index.  @census none (helper) -/
noncomputable def gelfandEdge (h : Nat.card Gal(L/K) = 2) (n : Fin 4) :
    (gelfandOfCardTwo K L h).E := n

/-- The non-trivial Galois element acts on edges by the `±`-swap.  @census none (helper) -/
theorem gelfand_smul_edge (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (n : Fin 4) : z • gelfandEdge K L h n = gelfandEdge K L h (RQuiver.gelfandEdgeSwap n) := by
  have hρ := gelfandOfCardTwo_rho_apply K L h hz
  show (RQuiver.Aut.toPermE _ ((gelfandOfCardTwo K L h).ρ z)) n = _
  rw [hρ]; rfl

/-- The non-trivial Galois element acts on vertices by the `±`-swap.  @census none (helper) -/
theorem gelfand_smul_vertex (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (n : Fin 3) : z • gelfandVertex K L h n
      = gelfandVertex K L h (RQuiver.gelfandVertexSwap n) := by
  have hρ := gelfandOfCardTwo_rho_apply K L h hz
  show (RQuiver.Aut.toPermV _ ((gelfandOfCardTwo K L h).ρ z)) n = _
  rw [hρ]; rfl

/-- The `a₋b₋` composite, resolved into its two edge maps.  Stated because
`M.pathMap (gelfandPathMinus …) x = φ_{a₋}(φ_{b₋} x)` is **not** `rfl` (`pathCompose`'s match does
not reduce through the composite even though each half does), and because unfolding
`RQuiver.pathMinus` produces a term at the WRONG quiver instance.  @census none (helper) -/
theorem gelfand_pathMap_minus (h : Nat.card Gal(L/K) = 2)
    (M : Rep (gelfandOfCardTwo K L h)) (m : M.M (gelfandStar K L h)) :
    M.pathMap (gelfandPathMinus K L h) m
      = M.φEdge' (gelfandEdge K L h 0) rfl rfl
          (M.φEdge' (gelfandEdge K L h 1) rfl rfl m) := by
  have hcons : gelfandPathMinus K L h
      = (Quiver.Path.nil.cons (⟨gelfandEdge K L h 1, rfl, rfl⟩ :
          Quiver.Hom (gelfandStar K L h) (gelfandVertex K L h 0))).cons
        (⟨gelfandEdge K L h 0, rfl, rfl⟩ :
          Quiver.Hom (gelfandVertex K L h 0) (gelfandStar K L h)) := rfl
  rw [hcons, Rep.pathMap_cons, Rep.pathMap_cons, Rep.pathMap_nil]
  rfl

/-- The `a₊b₊` composite, resolved.  @census none (helper) -/
theorem gelfand_pathMap_plus (h : Nat.card Gal(L/K) = 2)
    (M : Rep (gelfandOfCardTwo K L h)) (m : M.M (gelfandStar K L h)) :
    M.pathMap (gelfandPathPlus K L h) m
      = M.φEdge' (gelfandEdge K L h 2) rfl rfl
          (M.φEdge' (gelfandEdge K L h 3) rfl rfl m) := by
  have hcons : gelfandPathPlus K L h
      = (Quiver.Path.nil.cons (⟨gelfandEdge K L h 3, rfl, rfl⟩ :
          Quiver.Hom (gelfandStar K L h) (gelfandVertex K L h 2))).cons
        (⟨gelfandEdge K L h 2, rfl, rfl⟩ :
          Quiver.Hom (gelfandVertex K L h 2) (gelfandStar K L h)) := rfl
  rw [hcons, Rep.pathMap_cons, Rep.pathMap_cons, Rep.pathMap_nil]
  rfl

/-- **Clause `RQ2-2.16-C3`** (as corrected by census r7).  For every `K`-rational representation of
the Gelfand quiver with the `ex:gelfand` structure, `G`-equivariance shows that the two composites
of the relation are **conjugate under the semi-linear automorphism `φ_{⋆,c}` of `M(⋆)`**:
`φ_{a₊}φ_{b₊} = φ_{⋆,c} ∘ (φ_{a₋}φ_{b₋}) ∘ φ_{⋆,c}⁻¹`, stated below in the transport-free form
`φ_{⋆,c} ∘ (a₋b₋) = (a₊b₊) ∘ φ_{⋆,c}`.

This is the strongest consequence of equivariance — clause `RQ2-2.16-C11`, discharged by
`gelfand_relation_not_consequence`, is that it is strictly weaker than the relation itself.

@census none (clause witness for `RQ2-2.16-C3`)
@clauses   RQ2-2.16-C3
-/
theorem gelfand_relation_conjugate (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (M : Rep (gelfandOfCardTwo K L h)) (m : M.M (gelfandStar K L h)) :
    M.φ' z (gelfand_smul_star K L h hz) (M.pathMap (gelfandPathMinus K L h) m)
      = M.pathMap (gelfandPathPlus K L h) (M.φ' z (gelfand_smul_star K L h hz) m) := by
  have hstar : z • gelfandStar K L h = gelfandStar K L h := gelfand_smul_star K L h hz
  have hminus : z • gelfandVertex K L h 0 = gelfandVertex K L h 2 :=
    gelfand_smul_vertex K L h hz 0
  -- `b₋ ↦ b₊` and `a₋ ↦ a₊`
  have hbe : z • gelfandEdge K L h 1 = gelfandEdge K L h 3 := gelfand_smul_edge K L h hz 1
  have hae : z • gelfandEdge K L h 0 = gelfandEdge K L h 2 := gelfand_smul_edge K L h hz 0
  -- the eight source/target readings, each `rfl` but needed with their statements
  have s1 : (gelfandOfCardTwo K L h).toRQuiver.source (gelfandEdge K L h 1)
      = gelfandStar K L h := rfl
  have t1 : (gelfandOfCardTwo K L h).toRQuiver.target (gelfandEdge K L h 1)
      = gelfandVertex K L h 0 := rfl
  have s3 : (gelfandOfCardTwo K L h).toRQuiver.source (gelfandEdge K L h 3)
      = gelfandStar K L h := rfl
  have t3 : (gelfandOfCardTwo K L h).toRQuiver.target (gelfandEdge K L h 3)
      = gelfandVertex K L h 2 := rfl
  have s0 : (gelfandOfCardTwo K L h).toRQuiver.source (gelfandEdge K L h 0)
      = gelfandVertex K L h 0 := rfl
  have t0 : (gelfandOfCardTwo K L h).toRQuiver.target (gelfandEdge K L h 0)
      = gelfandStar K L h := rfl
  have s2 : (gelfandOfCardTwo K L h).toRQuiver.source (gelfandEdge K L h 2)
      = gelfandVertex K L h 2 := rfl
  have t2 : (gelfandOfCardTwo K L h).toRQuiver.target (gelfandEdge K L h 2)
      = gelfandStar K L h := rfl
  have hconsM : gelfandPathMinus K L h
      = (Quiver.Path.nil.cons (⟨gelfandEdge K L h 1, rfl, rfl⟩ :
          Quiver.Hom (gelfandStar K L h) (gelfandVertex K L h 0))).cons
        (⟨gelfandEdge K L h 0, rfl, rfl⟩ :
          Quiver.Hom (gelfandVertex K L h 0) (gelfandStar K L h)) := rfl
  have hconsP : gelfandPathPlus K L h
      = (Quiver.Path.nil.cons (⟨gelfandEdge K L h 3, rfl, rfl⟩ :
          Quiver.Hom (gelfandStar K L h) (gelfandVertex K L h 2))).cons
        (⟨gelfandEdge K L h 2, rfl, rfl⟩ :
          Quiver.Hom (gelfandVertex K L h 2) (gelfandStar K L h)) := rfl
  have harrow : ∀ (a b : (gelfandOfCardTwo K L h).V) (g : Quiver.Hom a b) (x : M.M a),
      M.arrowMap g x = M.φEdge' g.1 g.2.1 g.2.2 x := fun _ _ _ _ => rfl
  rw [hconsM, hconsP, Rep.pathMap_cons, Rep.pathMap_cons, Rep.pathMap_nil,
    Rep.pathMap_cons, Rep.pathMap_cons, Rep.pathMap_nil]
  simp only [LinearMap.comp_apply, LinearMap.id_apply, harrow]
  rw [M.φEdge'_φ' z hbe s1 t1 s3 t3 hstar hminus m,
    M.φEdge'_φ' z hae s0 t0 s2 t2 hminus hstar
      (M.φEdge' (gelfandEdge K L h 1) s1 t1 m)]

/-- **Finding S5-F1**, closed 2026-08-30 by a source repair: `RQ2-2.16-C3` **as it was printed
before census r7** was false.  There is a `K`-rational representation of the `ex:gelfand` quiver —
namely `gelfandTwist α` for any `α` moved by the non-trivial `c` — in which the relation
`a₋b₋ = a₊b₊` fails.  So the relation is *not* a consequence of `G`-equivariance and may *not* be
dropped when considering representations over `K`; that sentence is what the corrected remark's own
disclaimer `RQ2-2.16-C11` now says, and it is the clause this theorem establishes (`@clauses`
below).  (Re-tensed 2026-09-12, the seven-errata amendment's close-out round, `V-ERR-7`: the
heading read *"clause `RQ2-2.16-C3` as printed is **false**"*, of a clause that since r7 states the
`φ_⋆`-conjugacy this file proves at `gelfand_relation_conjugate`.)

Both composites are multiplication on `L`, by `α` and by `c α` respectively.

@census none (clause witness for `RQ2-2.16-C11`; see finding **S5-F1** in the module header)
@clauses   RQ2-2.16-C11
-/
theorem gelfand_relation_not_consequence (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (α : L) (hα : z α ≠ α) :
    ¬ SatisfiesGelfandRelation K L h (gelfandTwist K L h hz α) := by
  intro hrel
  refine hα ?_
  have h1 := LinearMap.congr_fun hrel (1 : L)
  rw [gelfand_pathMap_minus, gelfand_pathMap_plus] at h1
  -- the two composites are multiplication by `α` and by `c α`
  have hm : ∀ (n : Fin 4) (x : L),
      (gelfandTwist K L h hz α).φEdge' (gelfandEdge K L h n) rfl rfl x
        = ![α, 1, z α, 1] n * x := fun _ _ => rfl
  rw [hm, hm, hm, hm] at h1
  simp only [gelfandEdge, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, mul_one, one_mul] at h1
  exact h1.symm

/-- The refuting witness exists: for a non-trivial quadratic extension there really is an `α` with
`c α ≠ α`, so `gelfand_relation_not_consequence` is not vacuous.

@census none (non-vacuity of finding **S5-F1**)
-/
theorem exists_gelfand_relation_failure (h : Nat.card Gal(L/K) = 2) :
    ∃ (z : Gal(L/K)) (hz : z ≠ 1) (α : L),
      ¬ SatisfiesGelfandRelation K L h (gelfandTwist K L h hz α) := by
  obtain ⟨w, hw, _⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
  obtain ⟨α, hα⟩ : ∃ α : L, w α ≠ α := by
    by_contra hc
    push_neg at hc
    exact hw (AlgEquiv.ext hc)
  exact ⟨w, hw, α, gelfand_relation_not_consequence K L h hw α hα⟩


/-! ### The **nilpotent** witness (coordinator-mandated probe, 2026-08-30)

The coordinator ruled that the general witness `gelfandTwist` does not by itself close the
then-`RQ2-2.16-C3`: its loop composite is multiplication by `α`, which is **invertible**, so
`gelfandTwist α ∉ Rep^nil(Γ_K)` — and §2.4's context (the corollary feeding the `HC` equivalence,
whose objects are the *nilpotent* representations) makes "representations" plausibly mean
`Rep^nil`.  The probe's answer was **outcome (a): a nilpotent counterexample exists**, so the
withdrawn claim failed in that reading too.  Since census r7 the two witnesses discharge
`RQ2-2.16-C11` — the corrected remark's own disclaimer — in both readings.  (Re-tensed 2026-09-12,
the seven-errata amendment's close-out round, `V-ERR-7`.)

The witness `gelfandNilTwist α` is two-dimensional at every vertex.  With `A(x,y) = (x,0)` and
`B_β(x,y) = (β y, 0)`:

| edge | map |
|---|---|
| `a₋` | `A` |
| `b₋` | `B_α` |
| `a₊` | `A`   (`= c·A`, since `A` is defined over `K`) |
| `b₊` | `B_{cα}` (`= c·B_α`) |

*Nilpotent.*  `B_β ∘ A = 0` for every `β`, so **every** length-two composite that begins and ends
at a `±` vertex is zero; a path of length `≥ 3` alternates `⋆, ±, ⋆, ±` and therefore contains such
a block.  Hence every composite along a path of length `≥ 3` vanishes and the representation is
nilpotent (`Rep.IsNilpotent`, `DEF-S2-04`) with `n = 3`.  The two loop composites are themselves
nilpotent: `A ∘ B_β` has square `A ∘ (B_β ∘ A) ∘ B_β = 0`.

*Still a counterexample.*  `A ∘ B_α (x,y) = (α y, 0)` and `A ∘ B_{cα} (x,y) = ((cα) y, 0)`, which
differ for every `α ∉ K`.  Equivalently: `M(⋆) = L²` descends to the `K`-form `K²` and the loop
composite is the matrix `[[0,α],[0,0]]`, which lies in `End_K(K²)` only when `α ∈ K`.

So nilpotency did **not** rescue the withdrawn claim (the pre-r7 `RQ2-2.16-C3`): `c`-conjugacy plus
nilpotency plus descent at `⋆` still fails to force equality, and the extra condition really is "the loop composite is defined
over `K`", which no reading of "representation" supplies.
-/

/-- The entrywise Galois action on `L × L`, the semi-linear structure map of the nilpotent
witness.  @census none (helper) -/
def galPair (σ : Gal(L/K)) : (L × L) ≃+ (L × L) :=
  (Rep.galAddEquiv σ).prodCongr (Rep.galAddEquiv σ)

omit [IsGalois K L] [FiniteDimensional K L] in
@[simp] theorem galPair_apply (σ : Gal(L/K)) (m : L × L) :
    galPair K L σ m = (σ m.1, σ m.2) := rfl

/-- `A : (x,y) ↦ (x,0)`, the edge map of `a_±`.  It is defined over `K`, which is why `c` fixes
it.  @census none (helper) -/
def matA (L : Type) [Field L] : (L × L) →ₗ[L] (L × L) := LinearMap.prod (LinearMap.fst L L L) 0

/-- `B_β : (x,y) ↦ (β y, 0)`, the edge map of `b_±`.  `c` carries `B_β` to `B_{cβ}`.
@census none (helper) -/
def matB (L : Type) [Field L] (β : L) : (L × L) →ₗ[L] (L × L) :=
  LinearMap.prod (β • LinearMap.snd L L L) 0

@[simp] theorem matA_apply (L : Type) [Field L] (m : L × L) : matA L m = (m.1, 0) := rfl

@[simp] theorem matB_apply (L : Type) [Field L] (β : L) (m : L × L) :
    matB L β m = (β * m.2, 0) := rfl

/-- **The nilpotent witness of finding S5-F1.**  The `K`-rational representation of the Gelfand
quiver with `M(v) = L × L` at every vertex, `φ_{v,σ} = σ` entrywise, and edge maps
`a_± ↦ A`, `b₋ ↦ B_α`, `b₊ ↦ B_{cα}` in the notation of the section note above.

As for `gelfandTwist`, the `Gal(L/K)`-equivariance of the edge family is discharged here, with no
`sorry`: `c` fixes `A` (defined over `K`) and exchanges `B_α ↔ B_{cα}`, and `c² = 1`.  Unlike
`gelfandTwist`, this representation is **nilpotent** — see `gelfandNilTwist_isNilpotent`.

@census none (the nilpotent witness for clause `RQ2-2.16-C11`; it refuted the pre-r7
`RQ2-2.16-C3` — re-worded 2026-09-12, `V-ERR2b-7`)
-/
noncomputable def gelfandNilTwist (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (α : L) : Rep (gelfandOfCardTwo K L h) where
  M _ := L × L
  φ σ _ := galPair K L σ
  semilinear σ v a m := by simp [Algebra.smul_def]
  cocycle σ τ v m := by rw [mul_smul]; simp
  smooth x := isOpen_discrete _
  φEdge e := ![matA L, matB L α, matA L, matB L (z α)] e
  edge_equivariance σ e m m' hh := by
    have hm' : m' = galPair K L σ m := by
      simpa [Sigma.mk.injEq, eq_comm] using congrArg (fun y : (w : _) × (L × L) => y.2) hh
    rw [(gelfandOfCardTwo K L h).target_smul σ e]
    subst hm'
    refine congrArg (Sigma.mk _) ?_
    by_cases hσ : σ = 1
    · subst hσ; simp
    · have hρ := gelfandOfCardTwo_rho_apply K L h hσ
      obtain ⟨w, hw, hu⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
      have hzz : σ = z := by rw [hu σ hσ, ← hu z hz]
      subst hzz
      have hmove : σ • e = RQuiver.gelfandEdgeSwap e := by
        show (RQuiver.Aut.toPermE _ ((gelfandOfCardTwo K L h).ρ σ)) e = _
        rw [hρ]; rfl
      have hz2 : σ (σ α) = α := by
        have hs := gal_sq_eq_one K L h hσ
        calc σ (σ α) = (σ * σ) α := rfl
        _ = α := by rw [hs]; rfl
      rw [hmove]
      have key : ∀ f : Fin 4,
          (![matA L, matB L α, matA L, matB L (σ α)] (RQuiver.gelfandEdgeSwap f))
              (galPair K L σ m)
            = galPair K L σ ((![matA L, matB L α, matA L, matB L (σ α)] f) m) := by
        intro f
        fin_cases f <;> simp [RQuiver.gelfandEdgeSwap, hz2]
      exact key e

/-! #### Nilpotency of `gelfandNilTwist`

`A` is **idempotent**, not nilpotent, so nilpotency is not a fact about the individual edge maps.
It comes from the quiver's forced alternation together with `B ∘ A = 0`:

* every edge map lands in `L × 0` (`gelfandNil_flat`);
* every `B` kills `L × 0` (`gelfandNil_star_kills`), and the `B`s are exactly the edges out of `⋆`;
* an edge whose target is **not** `⋆` is a `B` (`gelfandNil_edge_dichotomy`) — the `A`s all point
  at `⋆`.

So along a path of length `≥ 2` the composite is already `0` unless it ends at `⋆`, and if it does
end at `⋆` the next arrow is a `B` and kills it.  Either way length `3` vanishes, with no
induction deeper than destructuring the last two arrows.
-/

/-- Transport in a **constant** family is the identity; `gelfandNilTwist` has `M v = L × L` for
every `v`, so every `famCast` in a path composite is inert.  @census none (helper) -/
theorem famCast_const_apply {V : Type} {T : Type} [AddCommGroup T] [Module L T]
    {v w : V} (hvw : v = w) (x : T) :
    RationalQuiver.famCast (L := L) (fun _ : V => T) hvw x = x := by
  subst hvw; rfl

/-- Every edge map of `gelfandNilTwist` lands in `L × 0`.  @census none (helper) -/
theorem gelfandNil_flat (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) (α : L)
    (n : Fin 4) (m : L × L) :
    ((gelfandNilTwist K L h hz α).φEdge (gelfandEdge K L h n) m).2 = 0 := by
  show (![matA L, matB L α, matA L, matB L (z α)] n m).2 = 0
  fin_cases n <;> simp [matA, matB]

/-- The edges out of `⋆` are the `B`s, and they kill `L × 0`.  The case split is done on the raw
`Fin 4` index, where `decide` applies — at the projected type `(gelfandOfCardTwo …).E` it does not,
because the goal still mentions `K`, `L` and `h`.  @census none (helper) -/
theorem gelfandNil_star_kills (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) (α : L)
    (n : Fin 4)
    (he : (gelfandOfCardTwo K L h).toRQuiver.source (gelfandEdge K L h n) = gelfandStar K L h)
    (m : L × L) (hm : m.2 = 0) :
    (gelfandNilTwist K L h hz α).φEdge (gelfandEdge K L h n) m = 0 := by
  have key : ∀ k : Fin 4, (![0, 1, 2, 1] k : Fin 3) = 1 → k = 1 ∨ k = 3 := by decide
  have hm' : m = (m.1, 0) := Prod.ext rfl hm
  have hshow : ∀ k : Fin 4, (gelfandNilTwist K L h hz α).φEdge (gelfandEdge K L h k) m
      = ![matA L, matB L α, matA L, matB L (z α)] k m := fun _ => rfl
  rw [hshow]
  rcases key n he with hk | hk <;> subst hk <;> rw [hm']
  · show matB L α (m.1, 0) = 0
    exact Prod.ext (by simp [matB]) rfl
  · show matB L (z α) (m.1, 0) = 0
    exact Prod.ext (by simp [matB]) rfl

/-- An edge whose target is not `⋆` has source `⋆`: the `A`s all point at `⋆`.
@census none (helper) -/
theorem gelfandNil_edge_dichotomy (h : Nat.card Gal(L/K) = 2) (n : Fin 4)
    (he : (gelfandOfCardTwo K L h).toRQuiver.target (gelfandEdge K L h n) ≠ gelfandStar K L h) :
    (gelfandOfCardTwo K L h).toRQuiver.source (gelfandEdge K L h n) = gelfandStar K L h := by
  have key : ∀ k : Fin 4, (![1, 0, 1, 2] k : Fin 3) ≠ 1 → (![0, 1, 2, 1] k : Fin 3) = 1 := by
    decide
  exact key n he



/-- The nilpotent witness is finite-dimensional at every vertex, so it really is an object of
`Rep(Γ_K)` (`RQ2-1.10`) and hence a candidate member of `Rep^nil(Γ_K)`.

@census none (helper for finding **S5-F1**, nilpotent half)
-/
theorem gelfandNilTwist_finiteDimensional (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (α : L) (v : (gelfandOfCardTwo K L h).V) :
    FiniteDimensional L ((gelfandNilTwist K L h hz α).M v) :=
  inferInstanceAs (FiniteDimensional L (L × L))


/-- The inverse transport in a constant family is also inert.  @census none (helper) -/
theorem famCast_const_symm_apply {V : Type} {T : Type} [AddCommGroup T] [Module L T]
    {v w : V} (hvw : v = w) (x : T) :
    (RationalQuiver.famCast (L := L) (fun _ : V => T) hvw).symm x = x := by
  subst hvw; rfl

/-- The arrow map of `gelfandNilTwist` is just its edge map: all fibres are `L × L`, so both
transports are inert.  @census none (helper) -/
theorem gelfandNil_arrowMap (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) (α : L)
    {a b : (gelfandOfCardTwo K L h).V} (g : a ⟶ b) (x : L × L) :
    (gelfandNilTwist K L h hz α).arrowMap g x
      = (gelfandNilTwist K L h hz α).φEdge (gelfandEdge K L h g.1) x := by
  obtain ⟨e, hs, ht⟩ := g
  subst hs
  subst ht
  rfl

/-- Every path composite of length `≥ 1` lands in `L × 0`.  No induction: only the last arrow
matters.  @census none (helper) -/
theorem gelfandNil_pathFlat (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) (α : L)
    {a b : (gelfandOfCardTwo K L h).V} (r : Quiver.Path a b) (hr : 1 ≤ r.length) (m : L × L) :
    ((gelfandNilTwist K L h hz α).pathMap r m).2 = 0 := by
  cases r with
  | nil => simp at hr
  | cons r' g =>
      rw [Rep.pathMap_cons]
      show ((gelfandNilTwist K L h hz α).arrowMap g _).2 = 0
      rw [gelfandNil_arrowMap]
      exact gelfandNil_flat K L h hz α g.1 _

/-- **The probe's answer, half one.**  The witness is **nilpotent** in the sense of `DEF-S2-04`
(`Rep.IsNilpotent`): every composite of edge maps along a path of length `≥ 3` is zero, because
`B_β ∘ A = 0` kills every `± → ⋆ → ±` block and every such path contains one.

@census none (helper for finding **S5-F1**, nilpotent half)
@clauses   RQ2-2.16-C11
-/
theorem gelfandNilTwist_isNilpotent (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (α : L) : (gelfandNilTwist K L h hz α).IsNilpotent := by
  refine ⟨3, fun a b p hp => LinearMap.ext fun m => ?_⟩
  show (gelfandNilTwist K L h hz α).pathMap p m = 0
  cases p with
  | nil => simp at hp
  | cons q g3 =>
    cases q with
    | nil => simp [Quiver.Path.length] at hp
    | cons r g2 =>
      have hr : 1 ≤ r.length := by
        simp only [Quiver.Path.length] at hp
        omega
      rw [Rep.pathMap_cons, Rep.pathMap_cons]
      simp only [LinearMap.comp_apply]
      by_cases hst : (gelfandOfCardTwo K L h).toRQuiver.source (gelfandEdge K L h g2.1)
          = gelfandStar K L h
      · -- `g₂` is a `B`: it kills the flat output of `r`
        have h0 : (gelfandNilTwist K L h hz α).arrowMap g2
            ((gelfandNilTwist K L h hz α).pathMap r m) = 0 := by
          rw [gelfandNil_arrowMap]
          exact gelfandNil_star_kills K L h hz α g2.1 hst _
            (gelfandNil_pathFlat K L h hz α r hr m)
        rw [h0, map_zero]
      · -- `g₂` is an `A`, so it points at `⋆`, so `g₃` is a `B` and kills `g₂`'s flat output
        have htgt : (gelfandOfCardTwo K L h).toRQuiver.target (gelfandEdge K L h g2.1)
            = gelfandStar K L h := by
          by_contra hc
          exact hst (gelfandNil_edge_dichotomy K L h g2.1 hc)
        have hs3 : (gelfandOfCardTwo K L h).toRQuiver.source (gelfandEdge K L h g3.1)
            = gelfandStar K L h := by
          have e1 : (gelfandOfCardTwo K L h).toRQuiver.source (gelfandEdge K L h g3.1)
              = (gelfandOfCardTwo K L h).toRQuiver.target (gelfandEdge K L h g2.1) := by
            show (gelfandOfCardTwo K L h).toRQuiver.source g3.1
              = (gelfandOfCardTwo K L h).toRQuiver.target g2.1
            rw [g3.2.1, g2.2.2]
          rw [e1, htgt]
        rw [gelfandNil_arrowMap]
        refine gelfandNil_star_kills K L h hz α g3.1 hs3 _ ?_
        rw [gelfandNil_arrowMap]
        exact gelfandNil_flat K L h hz α g2.1 _

/-- **The probe's answer, half two — finding S5-F1 held in the nilpotent reading.**  Even inside
`Rep^nil(Γ_K)`, the relation `a₋b₋ = a₊b₊` is not a consequence of `G`-equivariance: the two loop
composites of `gelfandNilTwist α` are `(x,y) ↦ (α y, 0)` and `(x,y) ↦ ((cα) y, 0)`, which differ
for every `α ∉ K`.  So the **withdrawn** claim (the pre-r7 `RQ2-2.16-C3`) was false in the narrowed
reading as well, and there is no reading of "representations over `K`" under which it held; what
holds inside `Rep^nil(Γ_K)` too is `RQ2-2.16-C11`, which this theorem establishes.  (Re-tensed
2026-09-12, the seven-errata amendment's close-out round, `V-ERR-7`.)

@census none (clause witness for `RQ2-2.16-C11` in the `Rep^nil` reading; finding **S5-F1**)
@clauses   RQ2-2.16-C11
-/
theorem gelfand_relation_not_consequence_nil (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)}
    (hz : z ≠ 1) (α : L) (hα : z α ≠ α) :
    ¬ SatisfiesGelfandRelation K L h (gelfandNilTwist K L h hz α) := by
  intro hrel
  refine hα ?_
  have h1 := LinearMap.congr_fun hrel ((0, 1) : L × L)
  rw [gelfand_pathMap_minus, gelfand_pathMap_plus] at h1
  have hm : ∀ (n : Fin 4) (x : L × L),
      (gelfandNilTwist K L h hz α).φEdge' (gelfandEdge K L h n) rfl rfl x
        = ![matA L, matB L α, matA L, matB L (z α)] n x := fun _ _ => rfl
  rw [hm, hm, hm, hm] at h1
  -- both composites are `A ∘ B`, so they read off `α` and `c α` from `(0,1)`
  have h2 : ((α * 1, (0 : L)) : L × L) = ((z α * 1, (0 : L)) : L × L) := h1
  have h3 := congrArg Prod.fst h2
  simp only [mul_one] at h3
  exact h3.symm

/-! ### Clauses `RQ2-2.16-C9` and `-C10` (census r7) -/

/-- **Clause `RQ2-2.16-C9`.**  `c` carries the relation `a₋b₋ = a₊b₊` to `a₊b₊ = a₋b₋`,
interchanging its two sides, so the **set** of relations is stable under the `G`-action.  This is
what "compatible with the relation" (clause `RQ2-2.16-C2`) means, and it is strictly weaker than the
claim the superseded `C3` carried.

The two halves are S1's: `RQuiver.onRelation_gelfandSwap` is the interchange on the ordered pair,
`RQuiver.onRelation_gelfandSwap_image` the stability of the set; `gelfandOfCardTwo_rho_apply`
transports them from `Aut(Q_Gelfand)` to the `Gal(L/K)`-action of `ex:gelfand`.

*(Amended 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S5, coordinator ruling
`R-FR-9`, final-release WP-16b, `MISMATCH-TRIAGE.md` row #13.)* The census text of `C9` (r18) has two
more sentences. "As equations the two members are trivially equivalent" is the `eq_comm` first
conjunct of `gelfand_relation_iff_transpose` below. "In the path algebra `r := a₋b₋ − a₊b₊`
satisfies `c(r) = −r`, so the ideal generated by `r` is `G`-stable" is **not formalized**: the tree
has no path algebra (relations are pairs of paths, S1's `RQuiver.Relation`). The divergence field
of the census row `gelfand_rationalStructure` records this.

@census none (clause witness for `RQ2-2.16-C9`)
@clauses   RQ2-2.16-C9
-/
theorem gelfand_relationSet_stable (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) :
    RQuiver.Aut.onRelation ((gelfandOfCardTwo K L h).ρ z) RQuiver.gelfandRelation
        = RQuiver.gelfandRelationSwap ∧
      (fun r => RQuiver.Aut.onRelation ((gelfandOfCardTwo K L h).ρ z) r) ''
          RQuiver.gelfandRelationSet = RQuiver.gelfandRelationSet := by
  rw [gelfandOfCardTwo_rho_apply K L h hz]
  exact ⟨RQuiver.onRelation_gelfandSwap, RQuiver.onRelation_gelfandSwap_image⟩

/-- **The transpose relation** `a₊b₊ = a₋b₋`, the other member of the `c`-conjugate pair.

@census none (helper for `RQ2-2.16-C10`)
-/
def SatisfiesGelfandRelationSwap (h : Nat.card Gal(L/K) = 2)
    (M : Rep (gelfandOfCardTwo K L h)) : Prop :=
  M.pathMap (gelfandPathPlus K L h) = M.pathMap (gelfandPathMinus K L h)

/-- **Clause `RQ2-2.16-C10`** (the descent criterion).  A representation satisfies
`a₋b₋ = a₊b₊` **iff** the `L`-linear endomorphism `φ_{a₋}φ_{b₋}` of `M(⋆)` commutes with
`φ_{⋆,c}`, i.e. is `K`-rational.  That is the **second** conjunct.

By `C3` the two composites are `φ_{⋆,c}`-conjugate. So the relation holds iff the `⋆`-composite
commutes with `φ_{⋆,c}`, i.e. iff `φ_{a₋}φ_{b₋} ∈ End_L(M(⋆))` is fixed by the semi-linear
`c`-action. Read the other way, this is why `C11` holds: nothing in equivariance supplies that
condition.

The **first** conjunct, `Rel ↔ RelSwap`, is the symmetry of equality. It discharges `C9`'s "as
equations the two members are trivially equivalent", and nothing more.

*(Amended 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S5, coordinator ruling
`R-FR-9`, final-release WP-16b, stale item R7.)* Until this amendment the docstring presented `C10`
as "imposing either one of the pair of `c`-conjugate relations imposes the other, so only one of the
two need be imposed", with the first conjunct as its "literal reading". That sentence was retired
from the source by census r18 (FA-05 / A-1). `C10` is now the descent criterion stated above, and
the first conjunct no longer answers it. **Not stated**: the clause's last sentence, that (since
`G_⋆ = G`) by `thm:galoisdescent` the commuting endomorphism is the base change of a `K`-linear
endomorphism of `M(⋆)^G`. It is one application of S0's `galoisDescent` to `M(⋆)`, and the tree does
not state it for this composite.

@census none (clause witness for `RQ2-2.16-C10`)
@clauses   RQ2-2.16-C10
-/
theorem gelfand_relation_iff_transpose (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (M : Rep (gelfandOfCardTwo K L h)) :
    (SatisfiesGelfandRelation K L h M ↔ SatisfiesGelfandRelationSwap K L h M) ∧
      (SatisfiesGelfandRelation K L h M ↔
        ∀ m : M.M (gelfandStar K L h),
          M.φ' z (gelfand_smul_star K L h hz) (M.pathMap (gelfandPathMinus K L h) m)
            = M.pathMap (gelfandPathMinus K L h)
                (M.φ' z (gelfand_smul_star K L h hz) m)) := by
  refine ⟨eq_comm, ⟨fun hrel m => ?_, fun hcomm => ?_⟩⟩
  · -- `C3` turns the `⋆`-composite into the `+`-composite, and the relation turns it back
    rw [gelfand_relation_conjugate K L h hz M m, hrel]
  · -- conversely, `φ_{⋆,c}` is a bijection, so testing on its image tests everywhere
    refine LinearMap.ext fun x => ?_
    obtain ⟨m, rfl⟩ := (M.φ' z (gelfand_smul_star K L h hz)).surjective x
    rw [← hcomm m, gelfand_relation_conjugate K L h hz M m]

/-! ### The census row -/

/-- **Clause `RQ2-2.16-C8`**, vertex half: the reconstructed vertex set has three elements.
@census none (clause witness for `RQ2-2.16-C8`) -/
theorem gelfand_vertexSet_card (h : Nat.card Gal(L/K) = 2) :
    Nat.card (EtaleSpecies.vertexSet (gelfandOfCardTwo K L h).toSpecies L) = 3 := by
  rw [Nat.card_congr (vertexSetEquivV K L (gelfandOfCardTwo K L h))]
  show Nat.card (Fin 3) = 3
  simp

/-- **Clause `RQ2-2.16-C8`**, edge half: the reconstructed edge set has four elements.
@census none (clause witness for `RQ2-2.16-C8`) -/
theorem gelfand_edgeSet_card (h : Nat.card Gal(L/K) = 2) :
    Nat.card (EtaleSpecies.edgeSet (gelfandOfCardTwo K L h).toSpecies L) = 4 := by
  rw [Nat.card_congr (edgeSetEquivE K L (gelfandOfCardTwo K L h))]
  show Nat.card (Fin 4) = 4
  simp

/-! ### Orbit and stabilizer data for the census row -/

/-- **Clause `RQ2-2.16-C5`**: every edge stabilizer is trivial — the `±`-swap is fixed-point-free
on the four arrows.  @census none (clause witness for `RQ2-2.16-C5`) -/
theorem gelfand_stabilizer_E (h : Nat.card Gal(L/K) = 2) (e : (gelfandOfCardTwo K L h).E) :
    stabilizer Gal(L/K) e = ⊥ := by
  ext σ
  simp only [Subgroup.mem_bot, mem_stabilizer_iff]
  refine ⟨fun hσ => ?_, by rintro rfl; exact one_smul _ _⟩
  by_contra hne
  have hsw : σ • e = RQuiver.gelfandEdgeSwap e := gelfand_smul_edge K L h hne e
  rw [hsw] at hσ
  have hdec : ∀ a : Fin 4, RQuiver.gelfandEdgeSwap a ≠ a := by decide
  exact hdec e hσ

/-- Every edge orbit field is `L`: the stabilizers are trivial.
@census none (clause witness for `RQ2-2.16-C5`) -/
theorem gelfand_edgeOrbitField (h : Nat.card Gal(L/K) = 2)
    {i j : (gelfandOfCardTwo K L h).VertexOrbit}
    (ε : (gelfandOfCardTwo K L h).EdgeOrbit i j) :
    (gelfandOfCardTwo K L h).edgeOrbitField ε = ⊤ :=
  stabField_eq_top_of_stabilizer_eq_bot (gelfand_stabilizer_E K L h _)

/-- **Clause `RQ2-2.16-C6`**, first half: `I = {{⋆},{±}}` has exactly two elements.  The unique
class other than `{⋆}` is `{±}`: `2` is in `0`'s orbit and `1` is not.
@census none (clause witness for `RQ2-2.16-C6`) -/
theorem gelfand_vertexOrbit_card (h : Nat.card Gal(L/K) = 2) :
    Nat.card (gelfandOfCardTwo K L h).VertexOrbit = 2 := by
  refine (Nat.card_eq_two_iff'
    ((gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 1))).mpr ?_
  refine ⟨(gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 0),
    fun hc => gelfand_vertexClass_star_ne K L h hc.symm, ?_⟩
  have key : ∀ n : Fin 3,
      (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h n)
          ≠ (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 1) →
        (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h n)
          = (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 0) := by
    intro n
    fin_cases n
    · exact fun _ => rfl
    · exact fun hc => absurd rfl hc
    · exact fun _ => gelfand_vertexClass_two K L h
  exact Quotient.ind fun v => key v

/-- **Example** (`ex:gelfand`, census `RQ2-2.16`).

The Gelfand quiver `Q_Gelfand` — vertices `−`, `⋆`, `+`, arrows `a_± : ± → ⋆`, `b_± : ⋆ → ±`,
relation `a₋b₋ = a₊b₊` (clause `RQ2-2.16-H2`: S1's `RQuiver.gelfand` with
`RQuiver.gelfandRelationSet`) — endowed with the action `c(±) = ∓`, `c(⋆) = ⋆`,
`c(a_±) = a_∓`, `c(b_±) = b_∓` of the non-trivial element of a quadratic Galois group
(clause `RQ2-2.16-H1`).  The conjuncts are, in order:

* `C1` — the action is the `±`-swap `RQuiver.gelfandSwap`;
* `C2` — it is compatible with the relation set, hence defines a `K`-structure;
* `C4` — `G(±) = {+,−}` and `G(⋆) = {⋆}` (equivalently: the stabilizers are `⊥` at `±` and `⊤` at
  `⋆`, and the two vertex orbits are distinct), so `L(⋆) = K` and `L(±) = L`;
* `C5` — `L(a_±) = L(b_±) = L`: every edge stabilizer is trivial;
* `C6` — `I = {{⋆},{±}}` has exactly two elements, `L_{{⋆}} = K` and `L_{{±}} = L` (the vertex
  orbit fields), and every edge orbit field is `L`; the "natural bimodule structures" are **not**
  stated (see the divergence field);
* `C7` — **listed, not stated** (see the divergence field);
* `C8` — the reconstruction of `RQ2-2.13` gives `V = Hom_K(L_{{⋆}},L) ⊔ Hom_K(L_{{±}},L)`
  of cardinality `3` and `E` of cardinality `4 = |G| + |G|`, with `s` and `t` by precomposition.

Clauses `RQ2-2.16-C3`, `-C9`, `-C10` and `-C11` are not conjuncts here: each is discharged by its
own named declaration above (`gelfand_relation_conjugate`, `gelfand_relationSet_stable`,
`gelfand_relation_iff_transpose`, and the pair `gelfand_relation_not_consequence` /
`…_nil`), because each is a statement about **representations** or about the relation set rather
than about the quiver's fields and orbits, which is what this theorem collects.

@census    RQ2-2.16
@source    ex:gelfand
@clauses   RQ2-2.16-H1, RQ2-2.16-H2, RQ2-2.16-C1, RQ2-2.16-C2, RQ2-2.16-C4, RQ2-2.16-C5, RQ2-2.16-C6,
           RQ2-2.16-C7, RQ2-2.16-C8
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.16-H1`; WEAKENED_OR_PARTIAL on clauses
`RQ2-2.16-C6`, `RQ2-2.16-C7` and `RQ2-2.16-C9`. **The partial disclosures were added 2026-10-03**
(docstring-only `R-PROC-4` amendment of frozen S5, coordinator ruling `R-FR-9`, final-release WP-16b,
`MISMATCH-TRIAGE.md` rows #11–#13; FA-45 on the census side, the docstring disclosure owed as
FA-47). Until then this field said "on clause `RQ2-2.16-H1` only".

`C6` — the vertex orbit fields (`L(⋆) = K`, `L(±) = L`) and the edge orbit fields (`= L`) are
stated. The sentence that both bimodules "carry the natural structures" is not. Which structure is
"natural" depends on the chosen edge representatives, in the same way as `RQ2-2.15`'s twist (see
`cyclic_species`'s divergence field). The Lean pins no representatives.

`C7` — "the `c`-twisted bimodule structures give isomorphic `K`-species" is cited in the `@clauses`
line above but **stated nowhere** in the tree. It would need the twisted species and an isomorphism
of étale `K`-species, about 100–150 lines (`MISMATCH-TRIAGE.md` §1 row #12), for a one-sentence
remark that nothing downstream uses. The citation is kept so that the clause stays visibly bound to
this row. It is a disclosure, not a discharge.

`C9` — `gelfand_relationSet_stable` states the interchange and the set stability, and the `eq_comm`
conjunct of `gelfand_relation_iff_transpose` states "trivially equivalent". The path-algebra
parenthetical (`c(r) = −r` for `r = a₋b₋ − a₊b₊`, so `(r)` is `G`-stable) is not formalized, because
the tree has no path algebra.

`H1` — the quadratic extension is arbitrary rather than `ℚ[√-1]/ℚ`, exactly as for `RQ2-2.14` and
`RQ2-2.15` and for the same reason recorded in `MD-S4-03`: the source's own §2.4 preamble licenses
"any other quadratic extension `L/K`", and stage S8 must consume one and the same object.

**The `C3` divergence is gone** (census r7, `census-v1.4`).  It read, until 2026-08-30, that the
clause *as printed* was refuted and was therefore discharged by a true-consequence theorem plus two
counterexamples rather than by a direct claim.  The author accepted finding **S5-F1** and the
source was repaired: `C3` now states the `φ_{⋆,c}`-conjugacy, which `gelfand_relation_conjugate`
claims **directly**; the `G`-stability of the relation set and the "only one need be imposed"
consequence are the new `C9`/`C10`, claimed directly by `gelfand_relationSet_stable` and
`gelfand_relation_iff_transpose` *(2026-10-03, `R-FR-9`: since census r18 `C10` is the descent
criterion, the second conjunct of `gelfand_relation_iff_transpose`; "only one need be imposed" is no
longer printed)*; and the two counterexamples now discharge the new `C11`, the
source's own express disclaimer, which they establish rather than contradict.  Nothing about the
Lean changed — only what the source says, and hence which clause each declaration answers.
-/
theorem gelfand_rationalStructure (h : Nat.card Gal(L/K) = 2) (z : Gal(L/K)) (hz : z ≠ 1) :
    (gelfandOfCardTwo K L h).ρ z = RQuiver.gelfandSwap ∧
      (fun r => RQuiver.Aut.onRelation ((gelfandOfCardTwo K L h).ρ z) r) ''
          RQuiver.gelfandRelationSet = RQuiver.gelfandRelationSet ∧
      (∀ n : Fin 3, n ≠ 1 → stabilizer Gal(L/K) (gelfandVertex K L h n) = ⊥) ∧
      stabilizer Gal(L/K) (gelfandVertex K L h 1) = ⊤ ∧
      (gelfandOfCardTwo K L h).vertexOrbitField
          ((gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 1)) = ⊥ ∧
      (gelfandOfCardTwo K L h).vertexOrbitField
          ((gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 0)) = ⊤ ∧
      (∀ e : (gelfandOfCardTwo K L h).E, stabilizer Gal(L/K) e = ⊥) ∧
      Nat.card (gelfandOfCardTwo K L h).VertexOrbit = 2 ∧
      (∀ (i j : (gelfandOfCardTwo K L h).VertexOrbit)
          (ε : (gelfandOfCardTwo K L h).EdgeOrbit i j),
        (gelfandOfCardTwo K L h).edgeOrbitField ε = ⊤) ∧
      (∀ i : (gelfandOfCardTwo K L h).VertexOrbit,
        Nonempty ((gelfandOfCardTwo K L h).edgeSet i i) → False) ∧
      Nat.card (EtaleSpecies.vertexSet (gelfandOfCardTwo K L h).toSpecies L) = 3 ∧
      Nat.card (EtaleSpecies.edgeSet (gelfandOfCardTwo K L h).toSpecies L) = 4 :=
  ⟨gelfandOfCardTwo_rho_apply K L h hz,
    (gelfand_relationSet_stable K L h hz).2,
    stabilizer_gelfandVertex_eq_bot K L h,
    stabilizer_gelfandVertex_star K L h,
    gelfand_vertexOrbitField_star K L h,
    gelfand_vertexOrbitField_pm K L h,
    gelfand_stabilizer_E K L h,
    gelfand_vertexOrbit_card K L h,
    fun _ _ ε => gelfand_edgeOrbitField K L h ε,
    fun i hne => (gelfand_edgeSet_diag_isEmpty K L h i).false hne.some,
    gelfand_vertexSet_card K L h,
    gelfand_edgeSet_card K L h⟩

end Examples

end RationalQuivers
