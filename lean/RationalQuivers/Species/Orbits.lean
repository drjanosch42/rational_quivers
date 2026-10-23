import RationalQuivers.Species.Etale
import RationalQuivers.Quiver.Basic
import RationalQuivers.Quiver.Models
import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Artinian.Module

/-!
# The vertex and edge `Gal(L/K)`-sets of an étale `K`-species, and their orbits

Formalizes the first half of §2.3 of `latex/rational_quivers.tex`: the two `Gal(L/K)`-sets `V` and
`E` attached to an étale `K`-species `S` over a splitting field `L`, and the two propositions
`prop:Viorbits` (census `RQ2-2.10`) and `prop:iMjorbits` (census `RQ2-2.11`) identifying the fibres of
the canonical maps `π : V → I` and `p : E → 𝓘` with the `Gal(L/K)`-orbits. Stage **S4**.

## Main definitions / results
* `RationalQuivers.EtaleSpecies.IsSplitBy` — the §2.3 standing hypothesis: `L` is a splitting field
  for the finitely many `L_i/K` and for the finite étale commutative `K`-algebras `{}_iM_j`, and
  `L/K` is finite Galois (clauses `RQ2-2.10-H1`, `RQ2-2.11-Hs1`, `RQ2-2.12-H2`).
* `RationalQuivers.EtaleSpecies.embAction` — the left `Gal(L/K)`-action on `K`-embeddings into `L`
  by postcomposition. mathlib has no such action (`ledger/MATHLIB-DECISIONS.tsv` `MD-S4-01`).
* `RationalQuivers.EtaleSpecies.vertexSet` (`V`), `.vertexProj` (`π`) — clauses `RQ2-2.10-H2`,
  `RQ2-2.10-C1`.
* `RationalQuivers.EtaleSpecies.vertex_fiber_eq_orbit` — `prop:Viorbits` (census `RQ2-2.10`).
* `RationalQuivers.EtaleSpecies.edgeIndexSet` (`𝓘`), `.residueField` (`L_ε`), `.edgeSet` (`E`),
  `.edgeProj` (`p`) — clauses `RQ2-2.11-H1`, `RQ2-2.11-C1`.
* `RationalQuivers.EtaleSpecies.edge_fiber_eq_orbit` — `prop:iMjorbits` (census `RQ2-2.11`).

## Implementation notes

**The standing hypothesis is an explicit argument.** The §2.3 preamble — "Let `L` denote a splitting
field for the collection of the finitely many separable extensions `L_i/K` … and the finite étale
commutative `K`-algebras `{}_iM_j` … We may assume that `L/K` is finite and Galois with Galois group
`G = Gal(L/K)`" — scopes `RQ2-2.10` through `RQ2-2.13` and is load-bearing (clause `RQ2-2.11-Hs1`: the
fibre/orbit bijection is false without it). `CONVENTIONS.md` §3 forbids carrying such a hypothesis
in an instance binder, which Lean silently prunes from any declaration that does not mention it;
we therefore bundle it as the `Prop`-valued structure `IsSplitBy` and pass it as an **explicit
argument** to every statement it scopes. The `IsGalois`/`FiniteDimensional` instances are recovered
from it with `haveI`.

**"Splits over `L`" is stated for elements.** For a finite `K`-algebra `A`, "`L` splits `A`" is
rendered as "for every `x ∈ A` the minimal polynomial of `x` over `K` splits in `L`", which is
mathlib's own hypothesis shape in `AlgHom.natCard_of_splits` — the lemma that turns this into the
count `#Hom_K(L_i,L) = [L_i : K]` that `RQ2-2.10` needs. For a finite étale `A = ∏_ε L_ε` it is
equivalent to `A ⊗_K L ≅ ∏ L`, the form the source states.

**`Specm` and residue fields.** `Specm {}_iM_j` is mathlib's `MaximalSpectrum`, and
`L_ε := {}_iM_j/ε` is the quotient ring; it is a *field* because `ε` is maximal
(`Ideal.Quotient.field`, which mathlib deliberately keeps out of the instance graph, so it is
introduced locally where needed). `Hom_K(L_ε, L)` needs only the `K`-algebra structure of the
quotient, which is an instance, so the edge set is defined without that local field instance.
-/

universe u

namespace RationalQuivers

open MulAction

namespace EtaleSpecies

variable {K : Type u} [Field K] (S : EtaleSpecies.{u} K) (L : Type u) [Field L] [Algebra K L]

/-! ### The §2.3 standing hypothesis -/

/-- **Clauses `RQ2-2.10-H1`, `RQ2-2.11-Hs1`, `RQ2-2.12-H2`** (the §2.3 standing hypothesis).
`L` is a splitting field for the finitely many separable extensions `L_i/K` and for the finite
étale commutative `K`-algebras `{}_iM_j`, and — the source's "we may assume" — `L/K` is **finite**
and **Galois**.

@census none (the §2.3 standing hypothesis, carried as an explicit argument; see the module header)
-/
structure IsSplitBy : Prop where
  /-- `L/K` is Galois. -/
  [galois : IsGalois K L]
  /-- `L/K` is finite: the source's "we may assume that `L/K` is finite and Galois". -/
  [findim : FiniteDimensional K L]
  /-- `L` splits every vertex field `L_i`. -/
  splits_L : ∀ (i : S.I) (x : S.L i), (Polynomial.map (algebraMap K L) (minpoly K x)).Splits
  /-- `L` splits every edge algebra `{}_iM_j`. -/
  splits_M : ∀ (i j : S.I) (x : S.M i j), (Polynomial.map (algebraMap K L) (minpoly K x)).Splits

/-! #### First consumers of the two `IsSplitBy` fields (`WORKFLOW.md` G5.4: no dead field) -/

/-- The arithmetic content of `IsSplitBy` on the vertex side: because `L` splits `L_i/K` and
`L_i/K` is finite separable, the number of `K`-embeddings `L_i → L` is exactly `[L_i : K]`. This is
the step that makes every fibre of `π` **nonempty** in `RQ2-2.10`, and it is the first consumer of
the field `splits_L`.

@census none (helper: the counting half of `RQ2-2.10-C2`)
-/
theorem card_emb_vertexField (hL : S.IsSplitBy L) (i : S.I) :
    Nat.card (S.L i →ₐ[K] L) = Module.finrank K (S.L i) :=
  AlgHom.natCard_of_splits K (S.L i) L (hL.splits_L i)

/-- The edge-side content of `IsSplitBy`, in the form the `RQ2-2.11` proof calls it: every element
of the finite étale algebra `{}_iM_j` has its minimal polynomial split by `L`, hence so does every
element of every residue field `L_ε = {}_iM_j/ε` (whose minimal polynomial divides that of any
lift). First consumer of the field `splits_M`.

@census none (helper for `RQ2-2.11-C2`)
-/
theorem splits_minpoly_edgeAlgebra (hL : S.IsSplitBy L) (i j : S.I) (x : S.M i j) :
    (Polynomial.map (algebraMap K L) (minpoly K x)).Splits :=
  hL.splits_M i j x

/-! #### Inhabitant (`WORKFLOW.md` G5) -/

/-- **G5 inhabitant, non-degenerate.** The one-node étale `ℝ`-species `L_⋆ = {}_⋆M_⋆ = ℂ`
(stage S3's `EtaleSpecies.complexLoop`, its `IsSplit`-refuting witness) is split by `L = ℂ`:
`ℂ/ℝ` is finite Galois and `ℂ` is algebraically closed, so it splits every minimal polynomial.
This is a **non-degenerate** witness in the sense of G5.2: the species is *not* a split species
(`EtaleSpecies.complexLoop_not_isSplit`) and `L ≠ K`, so the hypothesis is not inhabited only in
the trivial case `L = K` where every clause of §2.3 collapses.

@census none (G5 inhabitant for `EtaleSpecies.IsSplitBy`)
-/
theorem complexLoop_isSplitBy : (EtaleSpecies.complexLoop).IsSplitBy ℂ := by
  haveI := RationalQuivers.isGalois_real_complex
  exact { splits_L := fun _ _ => IsAlgClosed.splits_codomain _
          splits_M := fun _ _ _ => IsAlgClosed.splits_codomain _ }

/-! ### The `Gal(L/K)`-action on embeddings -/

/-- The canonical **left** action of `Gal(L/K)` on the `K`-embeddings of a `K`-algebra into `L`, by
postcomposition: `σ • φ = σ ∘ φ`. This is the action the source calls "canonical" on both `V` and
`E`; mathlib has no `MulAction` packaging it (`ledger/MATHLIB-DECISIONS.tsv` `MD-S4-01`).

@census none (helper: the `G`-action of clauses `RQ2-2.10-H2` and `RQ2-2.11-H1`)
-/
instance embAction (A : Type u) [CommRing A] [Algebra K A] : MulAction Gal(L/K) (A →ₐ[K] L) where
  smul σ f := ((σ : L ≃ₐ[K] L) : L →ₐ[K] L).comp f
  one_smul _ := AlgHom.ext fun _ => rfl
  mul_smul _ _ _ := AlgHom.ext fun _ => rfl

@[simp] theorem emb_smul_apply {A : Type u} [CommRing A] [Algebra K A] (σ : Gal(L/K))
    (f : A →ₐ[K] L) (a : A) : (σ • f) a = σ (f a) := rfl

/-! ### `V` and `π` (`prop:Viorbits`, census `RQ2-2.10`) -/

/-- **Clause `RQ2-2.10-H2`** (also `RQ2-2.12-C1`). `V := ⨆_{i ∈ I} Hom_K(L_i, L)`, a left
`Gal(L/K)`-set.

@census none (clause witness for `RQ2-2.10-H2`, `RQ2-2.12-C1`)
-/
def vertexSet : Type u := Σ i : S.I, (S.L i →ₐ[K] L)

instance : MulAction Gal(L/K) (S.vertexSet L) where
  smul σ v := ⟨v.1, σ • v.2⟩
  one_smul v := congrArg (Sigma.mk v.1) (one_smul _ v.2)
  mul_smul σ τ v := congrArg (Sigma.mk v.1) (mul_smul σ τ v.2)

@[simp] theorem vertexSet_smul_fst (σ : Gal(L/K)) (v : S.vertexSet L) :
    (σ • v).1 = v.1 := rfl

/-- **Clause `RQ2-2.10-C1`.** `π : V → I`, `σ ↦ i` if `σ ∈ Hom_K(L_i, L)`.

@census none (clause witness for `RQ2-2.10-C1`)
-/
def vertexProj : S.vertexSet L → S.I := Sigma.fst

/-- `π` is constant on `Gal(L/K)`-orbits, so it descends to the orbit set. -/
def vertexOrbitProj : orbitRel.Quotient Gal(L/K) (S.vertexSet L) → S.I :=
  Quotient.lift (S.vertexProj L) fun _ _ h => by
    obtain ⟨σ, rfl⟩ := mem_orbit_iff.mp h
    rfl

/-- **The transitivity of `MD-S4-01`, proved.** Any two `K`-embeddings of a field `E` into a
Galois extension `L/K` differ by an element of `Gal(L/K)`. mathlib has every ingredient but not
this statement (`ledger/MATHLIB-DECISIONS.tsv` `MD-S4-01`); the proof is the standard one: the two
images are intermediate fields of `L/K`, the induced isomorphism between them lifts to an
automorphism of `L` because `L/K` is normal (`AlgEquiv.liftNormal`), and that automorphism carries
the first embedding to the second.

@census none (helper: the transitivity half of `RQ2-2.10-C2` and `RQ2-2.11-C2`)
-/
theorem exists_galois_comp_eq [IsGalois K L] (E : Type u) [Field E] [Algebra K E]
    (φ ψ : E →ₐ[K] L) : ∃ σ : Gal(L/K), (σ : L →ₐ[K] L).comp φ = ψ := by
  haveI : Normal K L := IsGalois.to_normal
  let φ' : E ≃ₐ[K] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  let ψ' : E ≃ₐ[K] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  let χ : (φ.fieldRange : IntermediateField K L) ≃ₐ[K] (ψ.fieldRange : IntermediateField K L) :=
    φ'.symm.trans ψ'
  refine ⟨χ.liftNormal L, AlgHom.ext fun a => ?_⟩
  have h := AlgEquiv.liftNormal_commutes χ L (φ' a)
  have h1 : (algebraMap (φ.fieldRange : IntermediateField K L) L) (φ' a) = φ a := rfl
  have h2 : χ (φ' a) = ψ' a := by
    show ψ' (φ'.symm (φ' a)) = ψ' a
    rw [AlgEquiv.symm_apply_apply]
  rw [h1, h2] at h
  exact h

/-- **Proposition** (`prop:Viorbits`, census `RQ2-2.10`).
The fibres of the canonical map `π : V → I`, `σ ↦ i` if `σ ∈ Hom_K(L_i,L)`, are in canonical
bijection with the `Gal(L/K)`-orbits in `V`; equivalently, each `Hom_K(L_i,L)` is a single
`G`-orbit.

@census    RQ2-2.10
@source    prop:Viorbits
@clauses   RQ2-2.10-H1, RQ2-2.10-H2, RQ2-2.10-C1, RQ2-2.10-C2
@imports   none
@divergence none. "The fibres of `π` are in canonical bijection with the `G`-orbits in `V`" is
rendered as: the map `G\V → I` that `π` induces on the orbit set is a bijection. That is the same
statement — a fibre of `π` equals a single orbit iff the induced map is injective (no two orbits in
one fibre) and surjective (no empty fibre) — and it is the form that exhibits the bijection as
*canonical*, namely as the one induced by `π` itself rather than as an unrelated choice. The
census's own equivalent reading ("each `Hom_K(L_i,L)` is a single `G`-orbit") is the separate
statement `vertexFiber_single_orbit`. Clause `RQ2-2.10-H1` is the explicit argument `hL`.

Proof plan (G4). *Surjectivity*: `Hom_K(L_i,L)` is nonempty because `L_i/K` is finite separable and
`L` splits it — `AlgHom.natCard_of_splits` computes `#Hom_K(L_i,L) = [L_i : K] ≥ 1`.
*Injectivity*: two embeddings `φ, ψ : L_i → L` with the same source index differ by an element of
`Gal(L/K)`: `φ` and `ψ` have `K`-isomorphic images inside the normal extension `L`, so
`ψ ∘ φ⁻¹ : φ(L_i) → L` extends to an automorphism of `L` by `AlgEquiv.liftNormal`
(`AlgHom.fieldRange`, `AlgEquiv.ofInjectiveField`), and that automorphism carries `φ` to `ψ`.
mathlib has the ingredients but not this transitivity statement (`MD-S4-01`).
-/
theorem vertex_fiber_eq_orbit (hL : S.IsSplitBy L) :
    Function.Bijective (S.vertexOrbitProj L) := by
  haveI := hL.galois
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | _ v =>
      induction b using Quotient.inductionOn with
      | _ w =>
        obtain ⟨i, φ⟩ := v
        obtain ⟨j, ψ⟩ := w
        have hij : i = j := hab
        subst hij
        obtain ⟨σ, hσ⟩ := exists_galois_comp_eq L (S.L i) ψ φ
        exact Quotient.sound ⟨σ, Sigma.ext rfl (heq_of_eq hσ)⟩
  · intro i
    haveI := hL.findim
    have hcard : Nat.card (S.L i →ₐ[K] L) = Module.finrank K (S.L i) :=
      AlgHom.natCard_of_splits K (S.L i) L (hL.splits_L i)
    have hpos : 0 < Module.finrank K (S.L i) := Module.finrank_pos
    have hne : Nat.card (S.L i →ₐ[K] L) ≠ 0 := by rw [hcard]; omega
    obtain ⟨φ⟩ := (Nat.card_ne_zero.mp hne).1
    exact ⟨Quotient.mk _ ⟨i, φ⟩, rfl⟩

/-- **Clause `RQ2-2.10-C2`, the census's equivalent form.** Each fibre `Hom_K(L_i,L)` of `π` is a
single `Gal(L/K)`-orbit: it is nonempty, and any two of its elements differ by an element of `G`.

@census none (clause witness for `RQ2-2.10-C2`)
-/
theorem vertexFiber_single_orbit (hL : S.IsSplitBy L) (i : S.I) :
    Nonempty (S.L i →ₐ[K] L) ∧ ∀ φ ψ : S.L i →ₐ[K] L, ∃ σ : Gal(L/K), σ • φ = ψ := by
  haveI := hL.galois
  haveI := hL.findim
  refine ⟨?_, fun φ ψ => exists_galois_comp_eq L (S.L i) φ ψ⟩
  have hcard : Nat.card (S.L i →ₐ[K] L) = Module.finrank K (S.L i) :=
    AlgHom.natCard_of_splits K (S.L i) L (hL.splits_L i)
  have hpos : 0 < Module.finrank K (S.L i) := Module.finrank_pos
  have hne : Nat.card (S.L i →ₐ[K] L) ≠ 0 := by rw [hcard]; omega
  exact (Nat.card_ne_zero.mp hne).1

/-! ### `E` and `p` (`prop:iMjorbits`, census `RQ2-2.11`) -/

/-- `𝓘 = ⨆_{i,j ∈ I} Specm {}_iM_j`, the target of the edge fibre map `p`.

@census none (clause witness for `RQ2-2.11-C1`)
-/
def edgeIndexSet : Type u := Σ p : S.I × S.I, MaximalSpectrum (S.M p.1 p.2)

/-- The residue field `L_ε = {}_iM_j/ε` **with its field and `K`-algebra structure bundled**, in
the pattern `VertexSplitting` sets for a chosen decomposition and `RationalQuiver.galois` for a
standing hypothesis (coordinator ruling of 2026-08-30 on the stop recorded in
`workflow/stages/S4/DESIGN-NOTES.md` §8.2, option (b)).

`ε` is maximal by construction — it is a point of `MaximalSpectrum` — so `L_ε` *is* a field, but
mathlib deliberately keeps `Ideal.Quotient.field` out of the instance graph. Registering it directly
on a bare `def` gave the type **two** ring structures whose `Algebra`/`Module` paths instance search
could not reconcile (measured: `Finite (L_ε →ₐ[K] L)` stopped synthesizing, and inside proofs the
kernel rejected the generated auxiliaries). Bundling removes the competition at the root: the
carrier is a *field of this structure*, so the only `Field` and `Algebra` instances on it are these
two projections, and `L_ε` stays canonically **the quotient** — no embedding is chosen, which is the
torsor trap `RQ2-2.12-C3`'s `ι`-quantification exists to avoid.

@census none (clause witness for `RQ2-2.11-H1`)
-/
structure ResidueFieldData (S : EtaleSpecies.{u} K) (c : S.edgeIndexSet) : Type (u + 1) where
  /-- The underlying field `L_ε`. -/
  carrier : Type u
  /-- `L_ε` is a field, `ε` being a maximal ideal. -/
  [field : Field carrier]
  /-- `L_ε` is a `K`-algebra. -/
  [algebra : Algebra K carrier]
  /-- The quotient map `{}_iM_j → L_ε`. -/
  proj : S.M c.1.1 c.1.2 →ₐ[K] carrier
  /-- The quotient map is surjective. -/
  surjective_proj : Function.Surjective proj

attribute [instance] ResidueFieldData.field ResidueFieldData.algebra

/-- The canonical residue-field datum at `ε`: the quotient `{}_iM_j/ε` itself. -/
noncomputable def residueData (c : S.edgeIndexSet) : ResidueFieldData S c :=
  letI : Field (S.M c.1.1 c.1.2 ⧸ c.2.asIdeal) := Ideal.Quotient.field c.2.asIdeal
  letI : Algebra K (S.M c.1.1 c.1.2 ⧸ c.2.asIdeal) :=
    RingHom.toAlgebra ((Ideal.Quotient.mk c.2.asIdeal).comp (algebraMap K (S.M c.1.1 c.1.2)))
  { carrier := S.M c.1.1 c.1.2 ⧸ c.2.asIdeal
    proj :=
      { toFun := Ideal.Quotient.mk c.2.asIdeal
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl
        commutes' := fun _ => rfl }
    surjective_proj := Ideal.Quotient.mk_surjective }

/-- `L_ε := {}_iM_j/ε`, the residue field of the finite étale algebra `{}_iM_j` at a maximal ideal.
An `abbrev` for the bundle's carrier, so that the bundled instances are the ones instance search
finds.

@census none (clause witness for `RQ2-2.11-H1`)
-/
abbrev residueField (c : S.edgeIndexSet) : Type u := (S.residueData c).carrier

/-- The quotient map `{}_iM_j → L_ε`. -/
noncomputable def residueMap (c : S.edgeIndexSet) : S.M c.1.1 c.1.2 →ₐ[K] S.residueField c :=
  (S.residueData c).proj

theorem residueMap_surjective (c : S.edgeIndexSet) : Function.Surjective (S.residueMap c) :=
  (S.residueData c).surjective_proj

/-- **Clause `RQ2-2.11-H1`.** `E := ⨆_{i,j ∈ I} ⨆_{ε ∈ Specm {}_iM_j} Hom_K(L_ε, L)`, with its
canonical left `Gal(L/K)`-action.

@census none (clause witness for `RQ2-2.11-H1`, `RQ2-2.12-C4`)
-/
noncomputable def edgeSet : Type u := Σ c : S.edgeIndexSet, (S.residueField c →ₐ[K] L)

noncomputable instance : MulAction Gal(L/K) (S.edgeSet L) where
  smul σ e := ⟨e.1, σ • e.2⟩
  one_smul e := congrArg (Sigma.mk e.1) (one_smul _ e.2)
  mul_smul σ τ e := congrArg (Sigma.mk e.1) (mul_smul σ τ e.2)

@[simp] theorem edgeSet_smul_fst (σ : Gal(L/K)) (e : S.edgeSet L) : (σ • e).1 = e.1 := rfl

/-- **Clause `RQ2-2.11-C1`.** `p : E → 𝓘`, `σ ↦ ε` if `σ ∈ Hom_K(L_ε, L)`.

@census none (clause witness for `RQ2-2.11-C1`)
-/
noncomputable def edgeProj : S.edgeSet L → S.edgeIndexSet := Sigma.fst

/-- `p` is constant on `Gal(L/K)`-orbits, so it descends to the orbit set. -/
noncomputable def edgeOrbitProj : orbitRel.Quotient Gal(L/K) (S.edgeSet L) → S.edgeIndexSet :=
  Quotient.lift (S.edgeProj L) fun _ _ h => by
    obtain ⟨σ, rfl⟩ := mem_orbit_iff.mp h
    rfl

/-- Every element of a residue field `L_ε = {}_iM_j/ε` has its minimal polynomial split by `L`:
lift it to `{}_iM_j`, where `IsSplitBy` applies, and note that the minimal polynomial of the image
divides that of the lift.

@census none (helper for `RQ2-2.11-C2`)
-/
theorem splits_minpoly_residueField (hL : S.IsSplitBy L) (c : S.edgeIndexSet)
    (x : S.residueField c) : (Polynomial.map (algebraMap K L) (minpoly K x)).Splits := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := c.2.asIdeal) x
  have hdvd : minpoly K (Ideal.Quotient.mk c.2.asIdeal a) ∣ minpoly K a := by
    refine minpoly.dvd K _ ?_
    have h : (Polynomial.aeval (Ideal.Quotient.mk c.2.asIdeal a)) (minpoly K a)
        = Ideal.Quotient.mk c.2.asIdeal ((Polynomial.aeval a) (minpoly K a)) := by
      simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, map_sum]
    rw [h, minpoly.aeval, map_zero]
  refine Polynomial.Splits.of_dvd (hL.splits_M c.1.1 c.1.2 a) ?_ (Polynomial.map_dvd _ hdvd)
  exact Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral a))

/-- The residue field `L_ε` is a **finite** `K`-algebra: it is a quotient of the finite étale
algebra `{}_iM_j`.

@census none (helper for `RQ2-2.11-C2`)
-/
noncomputable instance finite_residueField' (c : S.edgeIndexSet) :
    Module.Finite K (S.residueField c) :=
  Module.Finite.of_surjective (S.residueMap c).toLinearMap (S.residueMap_surjective c)

/-- **Proposition** (`prop:iMjorbits`, census `RQ2-2.11`).
The fibres of the canonical map `p : E → 𝓘 = ⨆_{i,j} Specm {}_iM_j`, `σ ↦ ε` if
`σ ∈ Hom_K(L_ε,L)`, are in canonical bijection with the `Gal(L/K)`-orbits in `E`.

@census    RQ2-2.11
@source    prop:iMjorbits
@clauses   RQ2-2.11-Hs1, RQ2-2.11-H1, RQ2-2.11-C1, RQ2-2.11-C2
@imports   none
@divergence none. As for `RQ2-2.10`, "the fibres of `p` are in canonical bijection with the
`G`-orbits in `E`" is the bijectivity of the map `G\E → 𝓘` induced by `p` itself. Clause
`RQ2-2.11-Hs1` — the §2.3 standing hypothesis, which the census records only on this row and whose
absence would make the statement false — is the explicit argument `hL`.

Proof plan (G4). The residue field `L_ε = {}_iM_j/ε` is a finite separable extension of `K`
(a quotient of a finite étale `K`-algebra: `Algebra.Etale.iff_exists_algEquiv_prod` presents
`{}_iM_j` as a finite product of finite separable extensions and the residue fields are its
factors), and `hL.splits_M` says `L` splits it. So the argument of `RQ2-2.10` applies verbatim to
each `Hom_K(L_ε, L)`: nonempty by the degree count, a single orbit by the extension/lifting
argument.
-/
theorem edge_fiber_eq_orbit (hL : S.IsSplitBy L) :
    Function.Bijective (S.edgeOrbitProj L) := by
  haveI := hL.galois
  haveI := hL.findim
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | _ v =>
      induction b using Quotient.inductionOn with
      | _ w =>
        obtain ⟨c, φ⟩ := v
        obtain ⟨d, ψ⟩ := w
        have hcd : c = d := hab
        subst hcd
        obtain ⟨σ, hσ⟩ := exists_galois_comp_eq L (S.residueField c) ψ φ
        exact Quotient.sound ⟨σ, Sigma.ext rfl (heq_of_eq hσ)⟩
  · intro c
    obtain ⟨φ⟩ := IntermediateField.nonempty_algHom_of_adjoin_splits
      (F := K) (E := S.residueField c) (K := L) (S := (Set.univ : Set (S.residueField c)))
      (fun x _ => ⟨Algebra.IsIntegral.isIntegral x, S.splits_minpoly_residueField L hL c x⟩)
      (IntermediateField.adjoin_univ K _)
    exact ⟨Quotient.mk _ ⟨c, φ⟩, rfl⟩

/-! ## G5 witnesses for `ResidueFieldData` (G8 cross-model review finding F-M1-R-2)

`EtaleSpecies.ResidueFieldData` was one of the eight structures the G8 cross-model review found
carrying **no G5 item-(3) all-trivial entry anywhere** (`workflow/audit/M1/FINAL_AUDIT.md` §11.7).
Landed by commission **C-M1-1**, 2026-09-02, as a dated `WORKFLOW.md` F5 amendment of frozen stage
S4; no S4 statement changed.  The `Meta/Vacuity.lean` §5 registry entry citing these declarations
is owed to the **instrument owner** (F3).

**What the probe measures, and the finding it produces.**  `ResidueFieldData S c` asks for a
field, a surjective `K`-algebra map onto it from `{}_iM_j`, and **nothing tying either to `c`**.
So the bundle is inhabited for *every* `c` by any surjective field quotient of `{}_iM_j` — in
particular, when `{}_iM_j` is already a field, by that field with `proj = id`.  Both witnesses
below are of that shape.

*Verdict: expected, and not a defect.*  The bundle exists to carry the `Field`/`Algebra` instances
that mathlib deliberately keeps out of the instance graph for `Ideal.Quotient` (the diagnosis in
`residueData`'s docstring and S4 `DESIGN-NOTES.md` §8.2); it is a **carrier for the canonical
datum** `residueData`, which *is* the quotient at `c`, and no statement in the tree quantifies over
an arbitrary `ResidueFieldData` (measured: `residueField`/`residueMap` are `abbrev`/`def`s of
`residueData`'s projections, and every consumer goes through those).  Were a theorem ever to
quantify over the bundle, the missing `RingHom.ker proj = c.2.asIdeal` field would become a real
weakening, and this probe is the record of that.
-/

/-- The unique edge index of the one-node species `ℝ ⊂ ℂ`: the pair `(⋆, ⋆)` together with the
only maximal ideal of the field `{}_⋆M_⋆ = ℂ`.  @census none (helper for the G5 witness) -/
noncomputable def complexLoopEdgeIndex : complexLoop.edgeIndexSet :=
  ⟨⟨PUnit.unit, PUnit.unit⟩,
    ⟨(⊥ : Ideal ℂ), (Ideal.bot_isMaximal : (⊥ : Ideal ℂ).IsMaximal)⟩⟩

/-- **G5.2 (`ResidueFieldData`): a user-written, non-degenerate inhabitant.**  For the one-node
species `ℝ ⊂ ℂ` the residue field at the unique edge index is `ℂ` itself, a **proper** extension
of the base field.  Written out (rather than taken as `complexLoop.residueData _`) so that the
declaration's type is the structure; `EtaleSpecies.residueData` is the canonical datum and this is
its value up to the identification `ℂ/⊥ ≅ ℂ`.

@census none (G5.2 non-degenerate inhabitant of `ResidueFieldData`)
-/
noncomputable def complexLoopResidueData :
    ResidueFieldData complexLoop complexLoopEdgeIndex where
  carrier := ℂ
  proj := AlgHom.id ℝ ℂ
  surjective_proj := Function.surjective_id

/-- **G5.2 non-degeneracy** (`ResidueFieldData`, first criterion): the residue field is of degree
`2` over `K`, so `L_ε` is not forced to be `K` — which is what makes `RQ2-2.11`'s edge set
`⊔_ε Hom_K(L_ε, L)` bigger than `𝓘` and the fibre/orbit statement non-trivial.

@census none (G5.2 non-degeneracy witness for `ResidueFieldData`)
-/
theorem complexLoopResidueData_finrank :
    Module.finrank ℝ complexLoopResidueData.carrier = 2 :=
  Complex.finrank_real_complex

/-- **G5.2 non-degeneracy** (`ResidueFieldData`, second criterion): the structure map
`K → L_ε` is not bijective, i.e. the residue field is not the base field in disguise.

@census none (G5.2 non-degeneracy witness for `ResidueFieldData`)
-/
theorem complexLoopResidueData_not_trivial :
    ¬ Function.Bijective (algebraMap ℝ complexLoopResidueData.carrier) := by
  rintro ⟨-, hs⟩
  obtain ⟨x, hx⟩ := hs Complex.I
  have hx' : (algebraMap ℝ ℂ) x = Complex.I := hx
  have := congrArg Complex.im hx'
  simp at this

/-- The unique edge index of the split one-node species on `K`.
@census none (helper for the G5.3 probe) -/
noncomputable def trivialEdgeIndex (K : Type u) [Field K] :
    (EtaleSpecies.trivial K).edgeIndexSet :=
  ⟨⟨PUnit.unit, PUnit.unit⟩,
    ⟨(⊥ : Ideal K), (Ideal.bot_isMaximal : (⊥ : Ideal K).IsMaximal)⟩⟩

/-- **G5.3 probe (`ResidueFieldData`): the all-trivial interpretation** — residue field `= K`,
quotient map the identity, on the split one-node species.

**It type-checks.**  So `ResidueFieldData` does not exclude the degenerate model `L_ε = K`; see
the section header for the verdict and for the sharper reading (the bundle records no
compatibility with `c` at all).

@census none (G5.3 all-trivial probe for `ResidueFieldData`)
-/
noncomputable def trivialResidueData (K : Type u) [Field K] :
    ResidueFieldData (EtaleSpecies.trivial K) (trivialEdgeIndex K) where
  carrier := K
  proj := AlgHom.id K K
  surjective_proj := Function.surjective_id

end EtaleSpecies

end RationalQuivers
