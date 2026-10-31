module

public import RationalQuivers.Species.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-!
# Étale `K`-species

Formalizes the second and third definitions of §2.1 of `latex/rational_quivers.tex`
(census `RQ2-2.02`, `RQ2-2.03`).

## Main definitions / results
* `RationalQuivers.EtaleSpecies` — an étale `K`-species (census `RQ2-2.02`).
* `RationalQuivers.EtaleSpecies.toSpecies` — the underlying `K`-species; this is the Lean form of
  clause `RQ2-2.02-H1` ("`S` is a `K`-species").
* `RationalQuivers.EtaleSpecies.IsSplit` — Definition of a *split* étale `K`-species
  (census `RQ2-2.03`).
* `RationalQuivers.EtaleSpecies.ofFiniteSeparable` — the one-node étale species on a finite
  separable extension `L/K` (G5 inhabitant), and `EtaleSpecies.complexLoop`, the **non-split**
  witness `ℂ/ℝ` demanded by `WORKFLOW.md` G5.2.
* `RationalQuivers.surjective_algebraMap_of_bialgebra` — the obstruction that forces the
  `@divergence` recorded on `EtaleSpecies`; see the implementation note. Its scope is the
  **non-split** case; a split species' `∏_ε K` really is a `K`-bialgebra (finding V-8).
* `RationalQuivers.EtaleSpecies.gelfandShadow` — the `ℝ`/`ℂ` shadow of `ex:gelfand`: two vertices,
  `L_⋆ = ℝ ≠ ℂ = L_±`, and `left ≠ right` provably (finding V-4.1).
* `RationalQuivers.EtaleSpecies.complexEdge` — a species satisfying `IsSplit`'s *first* conjunct and
  refuting its *second* (finding V-4.2).

## Implementation notes

**The word "bialgebra" (defect report, see `workflow/stages/S3/DESIGN-NOTES.md`).** The source
asks that `{}_iM_j` be "a commutative `L_i,L_j`-bialgebra which is finite étale as `K`-algebra". A
`Bialgebra R A` in the standard (and mathlib's) sense carries a counit `A →ₐ[R] R`. The theorem
`RationalQuivers.surjective_algebraMap_of_bialgebra` below proves, from mathlib's definition, that
a field `A` which is a bialgebra over a subfield `K` must satisfy `A = K`. Consequently reading
"bialgebra" as a genuine bialgebra structure — over `K`, over `L_i`, or over `L_j` — is **not
satisfiable on the paper's non-split examples**: in `ex:gelfand`, `{}_{⋆}M_{±} = ℚ[√-1]` while
`L_{⋆} = ℚ`, and in `S(Γ_K)` the summands `L(e) = L^{G_e}` are field extensions that properly
contain `L(s(e))` and `L(t(e))` in general.

**Scope, as required by verification finding V-8.** The obstruction needs `{}_iM_j` to be a
*field*, and that is exactly the non-split situation. A **split** étale species has
`{}_iM_j = ∏_ε K`, which is not a field once `|ε| > 1` and which genuinely **is** a `K`-bialgebra
(functions on a finite monoid, `Δ(f)(x,y) = f(xy)`, `ε(f) = f(1)`), so the literal reading is
consistent there — and only there. This is enough for the ruling, because the paper's theorems are
about the non-split case, but the claim must not be stated more broadly than that. The same
qualification is on `surjective_algebraMap_of_bialgebra`, on `EtaleSpecies`'s `@divergence` and in
`stages/S3/DESIGN-NOTES.md` §1.

The reading that *is* satisfiable, and is the one every use in §2.1–§2.4 actually makes, is
"bi-algebra" = **algebra over the two rings `L_i` and `L_j` simultaneously** — the paper derives
exactly this from the diagram `L(s(e)) ↪ L(e) ↩ L(t(e))` (`eq:edgediagram`), the split condition
`{}_iM_j = ∏_ε K` is an isomorphism of algebras, `eq:etalebialgebradecomposition` is described as
holding "as `L_i,L`-bialgebra" (i.e. compatibly with two base rings), and §2.3 reconstructs the
quiver from `Specm {}_iM_j` and the two structure embeddings, never from a comultiplication. We
therefore carry the two structure maps `left`/`right` and record the divergence. This is a fidelity
question the implementer may not settle alone; it is reported to the coordinator as a G2 finding.

**Not `extends Species`.** Clause `RQ2-2.02-H1` says an étale `K`-species *is* a `K`-species. We
discharge it with the definition `EtaleSpecies.toSpecies` rather than with `extends Species K`: the
underlying bimodule of an étale species is the *ring* `{}_iM_j` acting on itself through `left` and
`right`, so an `extends` would have to identify the `AddCommGroup`/`Module` fields of the parent
with those coming from `CommRing (M i j)`, i.e. state equalities between instances and transport
across them. `toSpecies` computes the parent from the child instead — no transport, and the
resulting `Species` is definitionally the intended one.
-/

universe u

namespace RationalQuivers

open scoped MulOpposite

/-- If a field `A` carries a bialgebra structure over a subfield `K`, then `K = A`.

The counit of a bialgebra is a `K`-algebra map `A →ₐ[K] K`; a ring map out of a field into a
nonzero ring is injective, and it is a retraction of `algebraMap K A`, so `algebraMap K A` is
surjective.

**Scope of this obstruction (finding V-8 of the G2 verification).** The hypothesis `[Field A]` is
essential and the statement is *not* "no `{}_iM_j` can be a bialgebra". A **split** étale species
has `{}_iM_j = ∏_ε K`, which is not a field when `|ε| > 1` and which genuinely **is** a
`K`-bialgebra (the functions on a finite monoid, `Δ(f)(x,y) = f(xy)`, `ε(f) = f(1)`), so the split
case survives the literal reading untouched. What this lemma rules out is the literal reading on
the **non-split** cases, where `{}_iM_j` is a proper field extension: `ex:gelfand`'s
`{}_{⋆}M_{±} = ℚ[√-1]` over `L_{⋆} = ℚ`, and in general `S(Γ_K)`'s summands `L(e) = L^{G_e}` over
`L(s(e))`, `L(t(e))`. That is what would make the definition vacuous where it matters.

@census none (evidence for the `@divergence` recorded on `EtaleSpecies`)
-/
theorem surjective_algebraMap_of_bialgebra (K A : Type u) [Field K] [Field A] [Bialgebra K A] :
    Function.Surjective (algebraMap K A) := fun a => by
  refine ⟨Bialgebra.counitAlgHom K A a, ?_⟩
  have h : Function.Injective (Bialgebra.counitAlgHom K A) :=
    (Bialgebra.counitAlgHom K A).toRingHom.injective
  exact h (by simp [AlgHom.commutes])

/-- **Definition** (Étale `K`-species; unlabelled in the source, census `RQ2-2.02`).
An *étale `K`-species* is a `K`-species `S = (L_i, {}_iM_j)_{i,j ∈ I}` in which each `L_i` is a
finite separable extension of `K`, and each `{}_iM_j` is a commutative algebra over both `L_i` and
`L_j` (through the two structure maps `left` and `right`, which agree on `K`) that is finite étale
as a `K`-algebra.

That this data really is a `K`-species in the sense of `RQ2-2.01` — clause `RQ2-2.02-H1` — is the
definition `EtaleSpecies.toSpecies`.

@census    RQ2-2.02
@source    def:etalekspecies
@clauses   RQ2-2.02-H1, RQ2-2.02-C1, RQ2-2.02-C2, RQ2-2.02-C3, RQ2-2.02-C4
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.02-C3`. The source asks for an
"`L_i,L_j`-bialgebra"; we render this as "commutative `K`-algebra with two `K`-algebra structure
maps `left : L_i → {}_iM_j` and `right : L_j → {}_iM_j`", i.e. as a *bi*-algebra in the sense of a
simultaneous algebra over two base rings, and not as a mathlib `Bialgebra` (an algebra with a
compatible coalgebra structure). Argument: `surjective_algebraMap_of_bialgebra` (proved above from
mathlib's `Bialgebra`) shows that a field which is a `Bialgebra` over a subfield equals that
subfield, so the literal reading makes the definition uninhabited on the paper's own examples
(`ex:gelfand`: `{}_{⋆}M_{±} = ℚ[√-1]` over `L_{⋆} = ℚ`; `ex:twoloops`, `ex:cyclic` likewise; and
`S(Γ_K)`'s summands `L(e) = L^{G_e}` properly contain `L(s(e))`, `L(t(e))` in general), which would
make every downstream theorem vacuous — the defect class this process exists to prevent. The
argument is deliberately restricted to the non-split case: a **split** species' `{}_iM_j = ∏_ε K`
*is* a genuine `K`-bialgebra (functions on a finite monoid), so the literal reading is consistent
there and only there. See the scope note on `surjective_algebraMap_of_bialgebra`. The
reformulated reading is the one used everywhere in §2.1–§2.4: `eq:edgediagram` produces precisely a
pair of field embeddings, the split condition of `RQ2-2.03` is an algebra isomorphism, and the
reconstruction of §2.3 uses `Specm {}_iM_j` with the two structure embeddings and no
comultiplication. Escalated to the coordinator as a G2 fidelity finding.
-/
structure EtaleSpecies (K : Type u) [Field K] : Type (u + 1) where
  /-- The index set `I`. -/
  I : Type u
  /-- Clause `RQ2-2.02-H1` (inherited from `RQ2-2.01-H1`): the index set is finite. -/
  [finite_I : Finite I]
  /-- The fields `L_i`. -/
  L : I → Type u
  /-- Clause `RQ2-2.02-C1`: each `L_i` is a field (not merely a division ring). -/
  [field_L : ∀ i, Field (L i)]
  /-- Clause `RQ2-2.02-C1`: each `L_i` is an extension of `K`. -/
  [algebra_L : ∀ i, Algebra K (L i)]
  /-- Clause `RQ2-2.02-C1`: each `L_i/K` is **finite**. -/
  [finite_L : ∀ i, Module.Finite K (L i)]
  /-- Clause `RQ2-2.02-C1`: each `L_i/K` is **separable**. -/
  [separable_L : ∀ i, Algebra.IsSeparable K (L i)]
  /-- The algebras `{}_iM_j`. -/
  M : I → I → Type u
  /-- Clause `RQ2-2.02-C2`: each `{}_iM_j` is **commutative**. -/
  [commRing_M : ∀ i j, CommRing (M i j)]
  /-- Each `{}_iM_j` is a `K`-algebra. -/
  [algebra_M : ∀ i j, Algebra K (M i j)]
  /-- Clause `RQ2-2.02-C4`: each `{}_iM_j` is **finite étale** as a `K`-algebra. Over a field,
  mathlib's `Algebra.Etale` already entails module-finiteness; see `EtaleSpecies.finite_M`. -/
  [etale_M : ∀ i j, Algebra.Etale K (M i j)]
  /-- Clause `RQ2-2.02-C3`: the left structure map `L_i → {}_iM_j`, giving `{}_iM_j` its
  `L_i`-algebra (hence `L_i`-module) structure. -/
  left : ∀ i j, L i →ₐ[K] M i j
  /-- Clause `RQ2-2.02-C3`: the right structure map `L_j → {}_iM_j`, giving `{}_iM_j` its
  `L_j`-algebra (hence right `L_j`-module) structure. -/
  right : ∀ i j, L j →ₐ[K] M i j

attribute [instance] EtaleSpecies.finite_I EtaleSpecies.field_L EtaleSpecies.algebra_L
  EtaleSpecies.finite_L EtaleSpecies.separable_L EtaleSpecies.commRing_M
  EtaleSpecies.algebra_M EtaleSpecies.etale_M

namespace EtaleSpecies

variable {K : Type u} [Field K] (S : EtaleSpecies K)

/-- Clause `RQ2-2.02-C4`, the *finite* half of "finite étale": over a field, an étale algebra is a
finite module. (mathlib: `Algebra.FormallyUnramified.finite_of_free`.)

@census none (clause witness for `RQ2-2.02-C4`)
-/
instance finite_M (i j : S.I) : Module.Finite K (S.M i j) :=
  Algebra.FormallyUnramified.finite_of_free K (S.M i j)

/-- The left `L_i`-module structure on `{}_iM_j`, induced by `S.left`. -/
instance moduleLeft (i j : S.I) : Module (S.L i) (S.M i j) :=
  Module.compHom (S.M i j) (S.left i j).toRingHom

/-- The right `L_j`-module structure on `{}_iM_j`, induced by `S.right`; as everything in sight is
commutative it is presented, following mathlib, as a left `(L j)ᵐᵒᵖ`-module. -/
instance moduleRight (i j : S.I) : Module (S.L j)ᵐᵒᵖ (S.M i j) :=
  Module.compHom (S.M i j)
    (((S.right i j).toRingHom).comp (RingEquiv.toOpposite (S.L j)).symm.toRingHom)

lemma smul_left_def (i j : S.I) (a : S.L i) (m : S.M i j) : a • m = S.left i j a * m := rfl

lemma smul_right_def (i j : S.I) (b : (S.L j)ᵐᵒᵖ) (m : S.M i j) :
    b • m = S.right i j b.unop * m := rfl

instance isScalarTower_M (i j : S.I) : IsScalarTower K (S.L i) (S.M i j) :=
  ⟨fun c a m => by
    simp only [smul_left_def, Algebra.smul_def, map_mul, AlgHom.commutes, mul_assoc]⟩

/-- **Clause `RQ2-2.02-H1`.** An étale `K`-species *is* a `K`-species: the fields `L_i` are in
particular division rings with `K` central, and `{}_iM_j`, acting on itself through `left` and
`right`, is an `L_i,L_j`-bimodule whose two `K`-structures agree and which is finite over `K`.

@census none (clause witness for `RQ2-2.02-H1`; `RQ2-2.01` itself is claimed by `Species`)
-/
def toSpecies : Species K where
  I := S.I
  L := S.L
  M := S.M
  smul_comm_M := fun i j a b m => by
    simp only [smul_left_def, smul_right_def]
    ring
  smul_K_agree := fun i j c m => by
    simp only [smul_right_def, Algebra.smul_def, MulOpposite.unop_op, AlgHom.commutes]
  finite_K_M := fun i j => S.finite_M i j

/-- **Definition** (Split étale `K`-species; unlabelled in the source, census `RQ2-2.03`).
An étale `K`-species `S` is *split* if for all `i, j ∈ I` we have `K ≅ L_i` and
`{}_iM_j = ∏_ε K` as `K`-algebras.

`K ≅ L_i` is rendered as bijectivity of the structure map `algebraMap K (L i)`, which for fields is
exactly the existence of a `K`-algebra isomorphism `K ≃ₐ[K] L i`.

@census    RQ2-2.03
@source    def:splitetalespecies
@clauses   RQ2-2.03-H1, RQ2-2.03-H2, RQ2-2.03-C1, RQ2-2.03-C2
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.03-C2`, inherited from the `@divergence` of
`EtaleSpecies`: "`∏_ε K` as `K`-bialgebras" becomes "`∏_ε K` as `K`-algebras", for the reason
recorded there. Nothing else is changed: the index set `ε` is existentially quantified and required
finite, exactly as the product in the source is finite.
-/
def IsSplit : Prop :=
  (∀ i, Function.Bijective (algebraMap K (S.L i))) ∧
    ∀ i j, ∃ (ε : Type u) (_ : Finite ε), Nonempty (S.M i j ≃ₐ[K] (ε → K))

/-! ### Inhabitants (`WORKFLOW.md` G5) -/

/-- The one-node étale `K`-species attached to a finite separable extension `L/K`, with
`{}_0M_0 = L` acting on itself. For `L = K` this is the (split) trivial species; for `L ≠ K` it is
**not** split, which is the non-degenerate inhabitant `WORKFLOW.md` G5.2 asks for.

@census none (G5 inhabitant for `EtaleSpecies`)
-/
def ofFiniteSeparable (K L : Type u) [Field K] [Field L] [Algebra K L] [Module.Finite K L]
    [Algebra.IsSeparable K L] : EtaleSpecies K where
  I := PUnit
  L := fun _ => L
  M := fun _ _ => L
  etale_M := fun _ _ =>
    ⟨Algebra.FormallyEtale.of_isSeparable K L, Algebra.FinitePresentation.of_finiteType.mp
      inferInstance⟩
  left := fun _ _ => AlgHom.id K L
  right := fun _ _ => AlgHom.id K L

/-- The split one-node étale `K`-species on `K` itself.

@census none (G5 inhabitant: a *split* étale species)
-/
def trivial (K : Type u) [Field K] : EtaleSpecies K := ofFiniteSeparable K K

theorem trivial_isSplit (K : Type u) [Field K] : (trivial K).IsSplit := by
  refine ⟨fun _ => ?_, fun _ _ => ⟨PUnit, inferInstance, ⟨?_⟩⟩⟩
  · exact ⟨fun a b h => h, fun a => ⟨a, rfl⟩⟩
  · exact (AlgEquiv.funUnique K PUnit K).symm

/-- **G5.2 non-degenerate inhabitant.** The one-node étale `ℝ`-species with `L = ℂ`. It is
**not split**: `ℝ → ℂ` is not surjective. The source itself offers `Gal(ℂ/ℝ)` as an alternative to
`Gal(ℚ[√-1]/ℚ)` for its examples (§2.4 preamble); the census rows `ex:twoloops`/`ex:gelfand`
themselves belong to stage S4 and are not claimed here.

@census none (G5.2 non-split inhabitant for `EtaleSpecies`)
-/
noncomputable def complexLoop : EtaleSpecies ℝ := ofFiniteSeparable ℝ ℂ

theorem complexLoop_not_isSplit : ¬ complexLoop.IsSplit := by
  rintro ⟨h, -⟩
  obtain ⟨x, hx⟩ := (h PUnit.unit).2 Complex.I
  have hx' : (algebraMap ℝ ℂ) x = Complex.I := hx
  have := congrArg Complex.im hx'
  simp at this


/-! ### G5.2 content witnesses for the two-sided structure (verification finding V-4)

`complexLoop` is one-vertex with `left = right = id`, so it exercises neither the two-sidedness that
finding S3-F1's reformulation introduced nor the second conjunct of `IsSplit`. The two witnesses
below close both gaps, with no forward dependency on any later stage.
-/

/-- **G5.2 witness (V-4.1): the `ℝ`/`ℂ` shadow of `ex:gelfand`.**
Two vertices `I = Bool` (`false = ⋆`, `true = ±`) with **different** vertex fields
`L_⋆ = ℝ`, `L_± = ℂ`, and edge algebras `ℂ` throughout. The structure maps are genuinely two-sided:
at `(⋆, ±)` the left map is `ℝ ↪ ℂ` while the right map is defined on `ℂ`, and at `(±, ±)` the left
map is the identity while the right map is complex conjugation, so `left ≠ right` is a *checkable
proposition* here (`gelfandShadow_left_ne_right`) and not merely a difference of source types.

This is the shadow the source itself licenses ("one may also choose `G = Gal(ℂ/ℝ)`", §2.4 preamble)
of the `ex:gelfand` species `ℚ = L_{⋆} ⇄ L_{±} = ℚ[√-1]`. Two deliberate deviations, since this is
a G5 witness and **not** a claim on census row `RQ2-2.16` (which is stage S4's): the loop entries
`M_{⋆⋆}`, `M_{±±}` are `ℂ` rather than the zero ring that the loop-free Gelfand quiver would give,
and the right map at `(±,±)` is conjugation, which is `ex:cyclic`'s twist rather than
`ex:gelfand`'s. Both choices exist only to make the two-sidedness observable as a proved statement.

@census none (G5.2 witness for the two-sided structure of `RQ2-2.02-C3`)
-/
noncomputable def gelfandShadow : EtaleSpecies ℝ where
  I := Bool
  L := fun b => bif b then ℂ else ℝ
  field_L := fun b => by cases b; exacts [inferInstanceAs (Field ℝ), inferInstanceAs (Field ℂ)]
  algebra_L := fun b => by
    cases b; exacts [inferInstanceAs (Algebra ℝ ℝ), inferInstanceAs (Algebra ℝ ℂ)]
  finite_L := fun b => by
    cases b; exacts [inferInstanceAs (Module.Finite ℝ ℝ), inferInstanceAs (Module.Finite ℝ ℂ)]
  separable_L := fun b => by
    cases b
    exacts [inferInstanceAs (Algebra.IsSeparable ℝ ℝ), inferInstanceAs (Algebra.IsSeparable ℝ ℂ)]
  M := fun _ _ => ℂ
  etale_M := fun _ _ =>
    ⟨Algebra.FormallyEtale.of_isSeparable ℝ ℂ, Algebra.FinitePresentation.of_finiteType.mp
      inferInstance⟩
  left := fun b _ => by cases b; exacts [Algebra.ofId ℝ ℂ, AlgHom.id ℝ ℂ]
  right := fun _ b' => by cases b'; exacts [Algebra.ofId ℝ ℂ, Complex.conjAe.toAlgHom]

/-- The two structure maps of `gelfandShadow` are **different** at `(±, ±)`: the left one is the
identity of `ℂ` and the right one is complex conjugation. This is what shows the reformulated
clause `RQ2-2.02-C3` has content — an `EtaleSpecies` in which `left` and `right` could be collapsed
into one datum would not distinguish them.

@census none (G5.2 witness, V-4.1)
-/
theorem gelfandShadow_left_ne_right :
    gelfandShadow.left true true ≠ gelfandShadow.right true true := by
  intro h
  have h2 : (Complex.I : ℂ) = (starRingEnd ℂ) Complex.I := congrArg (fun f => f Complex.I) h
  norm_num [Complex.ext_iff] at h2

set_option backward.isDefEq.respectTransparency.types false in
/-- `gelfandShadow`'s two vertices carry genuinely different fields: `K ≅ L_⋆` … -/
theorem gelfandShadow_vertex_star : Function.Bijective (algebraMap ℝ (gelfandShadow.L false)) :=
  ⟨fun _ _ h => h, fun a => ⟨a, rfl⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- … but `K ≇ L_±`. Together with `gelfandShadow_vertex_star` this exhibits a species with
`L_i ≠ L_j`, which no earlier in-tree model did.

@census none (G5.2 witness, V-4.1)
-/
theorem gelfandShadow_vertex_pm : ¬ Function.Bijective (algebraMap ℝ (gelfandShadow.L true)) := by
  rintro ⟨-, hs⟩
  obtain ⟨x, hx⟩ := hs Complex.I
  have hx' : (algebraMap ℝ ℂ) x = Complex.I := hx
  have := congrArg Complex.im hx'
  simp at this

theorem gelfandShadow_not_isSplit : ¬ gelfandShadow.IsSplit := fun h =>
  gelfandShadow_vertex_pm (h.1 true)

/-- **G5.2 witness (V-4.2): `IsSplit`'s second conjunct is refutable.**
One vertex with `L = ℝ = K`, so the *first* conjunct of `IsSplit` holds
(`complexEdge_vertices_split`), and edge algebra `ℂ`, which is **not** a product of copies of `ℝ`,
so the *second* fails. Before this witness, `complexLoop_not_isSplit` refuted only the first
conjunct, and an `IsSplit` that had silently dropped its `{}_iM_j = ∏_ε K` requirement would have
passed every check in the tree.

@census none (G5.2 witness for `RQ2-2.03-C2`)
-/
noncomputable def complexEdge : EtaleSpecies ℝ where
  I := PUnit
  L := fun _ => ℝ
  M := fun _ _ => ℂ
  etale_M := fun _ _ =>
    ⟨Algebra.FormallyEtale.of_isSeparable ℝ ℂ, Algebra.FinitePresentation.of_finiteType.mp
      inferInstance⟩
  left := fun _ _ => Algebra.ofId ℝ ℂ
  right := fun _ _ => Algebra.ofId ℝ ℂ

/-- Clause `RQ2-2.03-C1` **holds** for `complexEdge`. -/
theorem complexEdge_vertices_split :
    ∀ i, Function.Bijective (algebraMap ℝ (complexEdge.L i)) :=
  fun _ => ⟨fun _ _ h => h, fun a => ⟨a, rfl⟩⟩

/-- … yet `complexEdge` is not split, because clause `RQ2-2.03-C2` fails: `ℂ` is not isomorphic to
any `ε → ℝ`. If it were, `ε` would have exactly two elements by a rank count, and `ε → ℝ` would
then have zero divisors while `ℂ` does not.

@census none (G5.2 witness for `RQ2-2.03-C2`)
-/
theorem complexEdge_not_isSplit : ¬ complexEdge.IsSplit := by
  rintro ⟨-, hM⟩
  obtain ⟨ε, hε, ⟨e⟩⟩ := hM PUnit.unit PUnit.unit
  classical
  letI := Fintype.ofFinite ε
  have e' : ℂ ≃ₐ[ℝ] (ε → ℝ) := e
  have hrank : Module.finrank ℝ (ε → ℝ) = 2 := by
    rw [← e'.toLinearEquiv.finrank_eq]; exact Complex.finrank_real_complex
  rw [Module.finrank_fintype_fun_eq_card] at hrank
  obtain ⟨a, b, hab⟩ : ∃ a b : ε, a ≠ b := Fintype.exists_pair_of_one_lt_card (by omega)
  have h0 : (Pi.single a (1:ℝ) : ε → ℝ) * (Pi.single b (1:ℝ) : ε → ℝ) = 0 := by
    funext c
    by_cases hc : c = a
    · subst hc; simp [Ne.symm hab]
    · simp [Pi.single_apply, hc]
  have hz : e'.symm (Pi.single a (1:ℝ) : ε → ℝ) * e'.symm (Pi.single b (1:ℝ) : ε → ℝ) = 0 := by
    rw [← map_mul, h0, map_zero]
  have key : ∀ c : ε, e'.symm (Pi.single c (1:ℝ) : ε → ℝ) ≠ 0 := by
    intro c hc
    have h1 : (Pi.single c (1:ℝ) : ε → ℝ) = 0 := by
      have h2 := congrArg e' hc
      rwa [e'.apply_symm_apply, map_zero] at h2
    have h3 := congrFun h1 c
    simp at h3
  rcases mul_eq_zero.1 hz with h | h
  · exact key a h
  · exact key b h

instance (K : Type u) [Field K] : Nonempty (EtaleSpecies K) := ⟨trivial K⟩

end EtaleSpecies

end RationalQuivers
