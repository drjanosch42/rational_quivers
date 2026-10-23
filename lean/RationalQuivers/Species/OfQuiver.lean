import RationalQuivers.Quiver.Basic
import RationalQuivers.Species.Etale
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Etale.Pi

/-!
# The étale `K`-species `S(Γ_K)` associated to a `K`-rational quiver

Formalizes §2.2 of `latex/rational_quivers.tex` (census `RQ2-2.09`). Stage **S4**.

## Main definitions / results
* `RationalQuivers.stabField` — `L(x) = L^{G_x}`, the fixed field of the stabilizer of a point of
  any `Gal(L/K)`-set; the paper's `L(v)` and `L(e)` are its two instances
  (`eq:abusivedefinitionofLv`, `eq:abusivedefinitionofLe`).
* `RationalQuivers.finiteDimensional_stabField` — clauses `RQ2-2.09-C10`/`C11`: an **open**
  stabilizer makes `L^{G_x}/K` **finite**, also for infinite `L/K`. This is what renders
  `S(Γ_K)` étale.
* `RationalQuivers.stabField_map_smul`, `.stabField_apply_eq_of_smul_eq`,
  `RationalQuivers.stabFieldEquivOrbit` — clauses `RQ2-2.09-C3`/`C5`: `L(x)` depends on the orbit
  only, up to a *canonical* `K`-isomorphism.
* `RationalQuivers.RationalQuiver.vertexOrbitField` (`L_i`), `.edgeSet` (`E_{ij}`),
  `.edgeOrbitField` (`L(e_ε)`), `.edgeAlgebraLeft`/`.edgeAlgebraRight` (`eq:edgediagram`) — the
  ingredients of clauses `C1`–`C7`.
* `RationalQuivers.RationalQuiver.toSpecies` — `S(Γ_K)` (census `RQ2-2.09`).

## Implementation notes

**`L_i` for a fixed representative.** The source fixes a representative `v_i ∈ i` for each orbit
`i ∈ I = G\V` and puts `L_i := L(v_i)`. We take `v_i := Quotient.out i`, which is exactly "a fixed
representative, chosen once" — the same use of choice the source makes. What makes this harmless is
clause `C3`: for any two points of one orbit the two fixed fields are canonically `K`-isomorphic
(`stabFieldEquivOrbit`), and the isomorphism does not depend on the group element realising the
orbit relation (`stabField_apply_eq_of_smul_eq`). Both are stated here.

**`⊕` versus `∏`.** Clause `C7` reads `{}_iM_j := ⊕_{ε ∈ G\E_{ij}} L(e_ε)`. The index set
`G\E_{ij}` is finite (`E` is finite by `RQ2-1.01-H2`), and over a finite index set the direct sum and
the direct product of the summands coincide; we use the `∏` form (`∀ ε, …`) because it is the form
that carries the `CommRing`/`Algebra`/`Algebra.Etale` instances mathlib provides
(`Algebra.FormallyEtale.instPi`). This is the same `⊕ → ∏` reformulation stage S3 recorded for
`RQ2-2.33` (`EtaleSpecies.moduleDecomposition`), and it is disclosed again in the `@divergence` of
`toSpecies`.

**The two structure maps.** `{}_iM_j` is not merely an abelian group here: the paper's
`eq:edgediagram` `L(s(e)) ⊆ L(e) ⊇ L(t(e))` is what makes `L(e)` an `L_i,L_j`-bimodule, and stage
S3's `EtaleSpecies` carries exactly that data as the two `K`-algebra maps `left`/`right` (see its
`@divergence`). We build them componentwise: on the `ε`-component, `left` is the composite
`L_i ≃ L(s(e_ε)) ⊆ L(e_ε)` of the canonical orbit isomorphism with the `eq:edgediagram` inclusion,
and `right` is the same with `t` in place of `s`.
-/

universe u

namespace RationalQuivers

open MulAction

/-! ### `L(x) = L^{G_x}` for a point of a `Gal(L/K)`-set -/

section StabField

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {X : Type u} [MulAction Gal(L/K) X]

/-- `L(x) := L^{G_x}`, the fixed field of the stabilizer of `x`. For a vertex this is the source's
`L(v)` (`eq:abusivedefinitionofLv`) and for an edge its `L(e)` (`eq:abusivedefinitionofLe`).

@census none (helper: the field `L(v)`/`L(e)` of clauses `RQ2-2.09-C2`, `RQ2-2.09-C4`)
-/
def stabField (x : X) : IntermediateField K L :=
  IntermediateField.fixedField (stabilizer Gal(L/K) x)

variable {K L}

/-- **Clauses `RQ2-2.09-C10` and `RQ2-2.09-C11`.** Since the `Gal(L/K)`-action on the discrete set
`X` is continuous, the stabilizer `G_x` is an **open** subgroup, and then `L(x) = L^{G_x}` is a
**finite** extension of `K` — *also for infinite `L/K`*. Applied to `X = V` this is `C10`, applied
to `X = E` it is `C11`, and `C11` is precisely what makes `S(Γ_K)` étale (clause `C8`).

Proof plan (G4). An open subgroup of a topological group is closed
(`Subgroup.isClosed_of_isOpen`; `Gal(L/K)` is a topological group for the Krull topology). For a
closed subgroup `H ≤ Gal(L/K)` of a Galois extension, `InfiniteGalois.fixingSubgroup_fixedField`
gives `(fixedField H).fixingSubgroup = H`, so the hypothesis says exactly that
`(fixedField (stabilizer x)).fixingSubgroup` is open, and `InfiniteGalois.isOpen_iff_finite` turns
that into `FiniteDimensional K (fixedField (stabilizer x))`. No new mathematics; this is the
open-stabilizer form of the continuity convention (`census/NOTATION.md` §12).

@census none (clause witness for `RQ2-2.09-C10`, `RQ2-2.09-C11`)
-/
theorem finiteDimensional_stabField (x : X)
    (hx : IsOpen ((stabilizer Gal(L/K) x : Subgroup Gal(L/K)) : Set Gal(L/K))) :
    FiniteDimensional K (stabField K L x) := by
  have hcl : IsClosed ((stabilizer Gal(L/K) x : Subgroup Gal(L/K)) : Set Gal(L/K)) :=
    Subgroup.isClosed_of_isOpen _ hx
  have h1 : (stabField K L x).fixingSubgroup = stabilizer Gal(L/K) x :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨stabilizer Gal(L/K) x, hcl⟩
  rw [← InfiniteGalois.isOpen_iff_finite, h1]
  exact hx

/-- **Clause `RQ2-2.09-C3`, engine.** Translating a point by `σ` translates its field by `σ`:
`σ (L^{G_x}) = L^{G_{σx}}`. Equivalently the conjugacy class of `G_x` is an invariant of the orbit,
which is how the source states it.

Proof plan (G4): `G_{σx} = σ G_x σ⁻¹` (`MulAction.stabilizer_smul_eq_stabilizer_map_conj` or
directly), and `σ (L^H) = L^{σHσ⁻¹}` by unfolding both fixed fields.

@census none (clause witness for `RQ2-2.09-C3`)
-/
theorem mem_stabilizer_smul_iff (σ : Gal(L/K)) (x : X) (g : Gal(L/K)) :
    g ∈ stabilizer Gal(L/K) (σ • x) ↔ σ⁻¹ * g * σ ∈ stabilizer Gal(L/K) x := by
  simp only [mem_stabilizer_iff, mul_smul]
  constructor
  · intro h; rw [h]; simp [← mul_smul]
  · intro h
    have := congrArg (fun y => σ • y) h
    simpa [← mul_smul] using this

theorem stabField_map_smul (σ : Gal(L/K)) (x : X) :
    IntermediateField.map (σ : L →ₐ[K] L) (stabField K L x) = stabField K L (σ • x) := by
  ext y
  simp only [IntermediateField.mem_map, stabField, IntermediateField.mem_fixedField_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩ g hg
    have h1 : σ⁻¹ * g * σ ∈ stabilizer Gal(L/K) x := (mem_stabilizer_smul_iff σ x g).mp hg
    have h2 : σ ((σ⁻¹ * g * σ) z) = σ z := congrArg σ (hz _ h1)
    simpa [AlgEquiv.mul_apply] using h2
  · intro hy
    refine ⟨σ⁻¹ y, fun g hg => ?_, by simp⟩
    have h1 : σ * g * σ⁻¹ ∈ stabilizer Gal(L/K) (σ • x) := by
      rw [mem_stabilizer_smul_iff σ x]
      group
      simpa using hg
    have h2 : (σ⁻¹ : Gal(L/K)) ((σ * g * σ⁻¹) y) = (σ⁻¹ : Gal(L/K)) y :=
      congrArg (fun z => (σ⁻¹ : Gal(L/K)) z) (hy _ h1)
    simpa [AlgEquiv.mul_apply] using h2

/-- **Clauses `RQ2-2.09-C3` and `RQ2-2.09-C5`, canonicity.** The isomorphism `L(x) ≅ L(y)` attached
to an orbit relation does not depend on the group element realising it: if `σ • x = τ • x` then
`σ` and `τ` agree on all of `L(x)`. This is what upgrades "unique up to `K`-isomorphism" to a
*canonical* identification, and it is also what makes the structure maps of `toSpecies`
well defined.

Proof plan (G4): `σ • x = τ • x` gives `τ⁻¹σ ∈ G_x`, and every element of `L(x) = L^{G_x}` is fixed
by `τ⁻¹σ`, i.e. `σ α = τ α`.

@census none (clause witness for `RQ2-2.09-C3`, `RQ2-2.09-C5`)
-/
theorem stabField_apply_eq_of_smul_eq {σ τ : Gal(L/K)} {x : X} (h : σ • x = τ • x)
    (α : stabField K L x) : σ (α : L) = τ (α : L) := by
  have hmem : τ⁻¹ * σ ∈ stabilizer Gal(L/K) x := by
    rw [mem_stabilizer_iff, mul_smul, h, ← mul_smul, inv_mul_cancel, one_smul]
  have hfix := (IntermediateField.mem_fixedField_iff _ _).mp α.2 _ hmem
  have h2 : τ ((τ⁻¹ * σ) (α : L)) = τ (α : L) := congrArg τ hfix
  rw [AlgEquiv.mul_apply] at h2
  simpa using h2

/-- **The converse of `stabField_apply_eq_of_smul_eq`.** If two Galois elements agree on all of
`L(x) = L^{G_x}` then they move `x` the same way. This is where Galois theory proper enters: it is
`InfiniteGalois.fixingSubgroup_fixedField` for the *closed* subgroup `G_x` (closed because the
action on the discrete set `X` is continuous, so `G_x` is open). Together the two lemmas say that
`σ ↦ σ|_{L(x)}` identifies `G/G_x` with `Hom_K(L(x),L)`, which is the content of clause
`RQ2-2.13-C4`.

@census none (helper for clause `RQ2-2.13-C4`)
-/
theorem smul_eq_of_stabField_apply_eq {σ τ : Gal(L/K)} {x : X}
    (hx : IsOpen ((stabilizer Gal(L/K) x : Subgroup Gal(L/K)) : Set Gal(L/K)))
    (h : ∀ α : stabField K L x, σ (α : L) = τ (α : L)) : σ • x = τ • x := by
  have hcl : IsClosed ((stabilizer Gal(L/K) x : Subgroup Gal(L/K)) : Set Gal(L/K)) :=
    Subgroup.isClosed_of_isOpen _ hx
  have h1 : (stabField K L x).fixingSubgroup = stabilizer Gal(L/K) x :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨stabilizer Gal(L/K) x, hcl⟩
  have hmem : τ⁻¹ * σ ∈ (stabField K L x).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    show (τ⁻¹ * σ) y = y
    rw [AlgEquiv.mul_apply, h ⟨y, hy⟩]
    exact τ.symm_apply_apply y
  rw [h1, mem_stabilizer_iff] at hmem
  calc σ • x = (τ * (τ⁻¹ * σ)) • x := by group
    _ = τ • ((τ⁻¹ * σ) • x) := mul_smul _ _ _
    _ = τ • x := by rw [hmem]


/-- The canonical `K`-isomorphism `L(x) ≅ L(σ • x)` induced by `σ`. -/
noncomputable def stabFieldEquivSmul (σ : Gal(L/K)) (x : X) :
    stabField K L x ≃ₐ[K] stabField K L (σ • x) :=
  (IntermediateField.intermediateFieldMap σ (stabField K L x)).trans
    (IntermediateField.equivOfEq (stabField_map_smul σ x))

/-- **Clause `RQ2-2.09-C3`.** For `y` in the orbit of `x`, the canonical `K`-isomorphism
`L(x) ≅ L(y)`: the isomorphism class of `L(x)` depends only on the orbit `Gx`. By
`stabField_apply_eq_of_smul_eq` the underlying map does not depend on the group element chosen to
realise `y ∈ Gx`, so this really is *the* canonical identification and not merely *an*
isomorphism.

@census none (clause witness for `RQ2-2.09-C3`)
-/
noncomputable def stabFieldEquivOrbit {x y : X} (h : y ∈ orbit Gal(L/K) x) :
    stabField K L x ≃ₐ[K] stabField K L y :=
  (stabFieldEquivSmul (mem_orbit_iff.mp h).choose x).trans
    (IntermediateField.equivOfEq (by rw [(mem_orbit_iff.mp h).choose_spec]))

/-- If `y`'s stabilizer is contained in `x`'s, then `L(x) ⊆ L(y)`. Applied to `y = e`,
`x = s(e)` (resp. `t(e)`) this is the source's `eq:edgediagram`.

@census none (clause witness for `RQ2-2.09-C4`)
-/
theorem stabField_le_of_stabilizer_le {x y : X}
    (h : stabilizer Gal(L/K) y ≤ stabilizer Gal(L/K) x) : stabField K L x ≤ stabField K L y :=
  IntermediateField.fixedField_le h

/-- `L(x)` is finite étale over `K` as soon as the stabilizer of `x` is open: it is a finite
separable extension. This is clause `RQ2-2.09-C11`'s "…is precisely what renders `S(Γ_K)` étale".

@census none (clause witness for `RQ2-2.09-C11`)
-/
theorem etale_stabField (x : X)
    (hx : IsOpen ((stabilizer Gal(L/K) x : Subgroup Gal(L/K)) : Set Gal(L/K))) :
    Algebra.Etale K (stabField K L x) := by
  haveI := finiteDimensional_stabField x hx
  exact ⟨Algebra.FormallyEtale.of_isSeparable K _,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- A trivial stabilizer is an orbit invariant (stabilizers along an orbit are conjugate).

@census none (helper)
-/
theorem stabilizer_eq_bot_of_mem_orbit {x y : X} (hxy : y ∈ orbit Gal(L/K) x)
    (hx : stabilizer Gal(L/K) x = ⊥) : stabilizer Gal(L/K) y = ⊥ := by
  obtain ⟨σ, rfl⟩ := mem_orbit_iff.mp hxy
  ext g
  simp only [Subgroup.mem_bot]
  rw [mem_stabilizer_smul_iff σ x g, hx, Subgroup.mem_bot]
  constructor
  · intro hg
    have hcong : g = σ * (σ⁻¹ * g * σ) * σ⁻¹ := by group
    rw [hcong, hg]; group
  · rintro rfl; group

/-- A full stabilizer is an orbit invariant.

@census none (helper)
-/
theorem stabilizer_eq_top_of_mem_orbit {x y : X} (hxy : y ∈ orbit Gal(L/K) x)
    (hx : stabilizer Gal(L/K) x = ⊤) : stabilizer Gal(L/K) y = ⊤ := by
  obtain ⟨σ, rfl⟩ := mem_orbit_iff.mp hxy
  ext g
  simp only [Subgroup.mem_top, iff_true]
  rw [mem_stabilizer_smul_iff σ x g, hx]
  exact Subgroup.mem_top _

/-- `L(x) = ⊤` exactly when `x` has trivial stabilizer. -/
theorem stabField_eq_top_of_stabilizer_eq_bot {x : X} (hx : stabilizer Gal(L/K) x = ⊥) :
    stabField K L x = ⊤ := by
  rw [stabField, hx]
  exact IntermediateField.fixedField_bot

/-- **The evaluation law for the canonical translations.** `stabFieldEquivOrbit h` is, on
underlying elements of `L`, application of *the* group element that `h` provides. Together with
`stabField_apply_eq_of_smul_eq` (which says the choice does not matter) this is the whole working
API for the canonical identifications: every equation between them reduces to an equation between
group elements acting on one point.

@census none (helper: the working form of clauses `RQ2-2.09-C3`/`C5`)
-/
theorem stabFieldEquivOrbit_coe {x y : X} (h : y ∈ orbit Gal(L/K) x) (a : stabField K L x) :
    ((stabFieldEquivOrbit h a : stabField K L y) : L)
      = (mem_orbit_iff.mp h).choose (a : L) := rfl

/-- The same for the translation by a named `σ`. -/
theorem stabFieldEquivSmul_coe (σ : Gal(L/K)) (x : X) (a : stabField K L x) :
    ((stabFieldEquivSmul σ x a : stabField K L (σ • x)) : L) = σ (a : L) := rfl

/-! ### Splitting of minimal polynomials inside `L` -/

/-- Every element of an intermediate field of the Galois extension `L/K` has its minimal
polynomial split by `L`: `L/K` is normal. This is the vertex half of "`S(Γ_K)` is split by `L`".

@census none (helper for `RQ2-2.13-H1`)
-/
theorem splits_minpoly_intermediateField (E : IntermediateField K L) (x : E) :
    (Polynomial.map (algebraMap K L) (minpoly K x)).Splits := by
  have h : minpoly K (algebraMap E L x) = minpoly K x :=
    minpoly.algebraMap_eq (algebraMap E L).injective x
  rw [← h]
  exact Normal.splits IsGalois.to_normal _

/-- The same for a finite **product** of intermediate fields: the minimal polynomial of a tuple
divides the product of the components' minimal polynomials, each of which splits in `L`. This is
the edge half of "`S(Γ_K)` is split by `L`", since `{}_iM_j` is such a product.

@census none (helper for `RQ2-2.13-H1`)
-/
theorem splits_minpoly_pi [FiniteDimensional K L] {J : Type u} [Finite J]
    (E : J → IntermediateField K L) (m : ∀ j, E j) :
    (Polynomial.map (algebraMap K L) (minpoly K m)).Splits := by
  haveI := Fintype.ofFinite J
  have key : (Polynomial.aeval m) (∏ j : J, minpoly K (m j)) = 0 := by
    funext j
    have hc : (Polynomial.aeval m) (∏ j : J, minpoly K (m j)) j
        = Polynomial.aeval (m j) (∏ j' : J, minpoly K (m j')) := by
      simp [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    rw [hc, map_prod, Finset.prod_eq_zero (Finset.mem_univ j) (minpoly.aeval K (m j))]
    rfl
  have hdvd : minpoly K m ∣ ∏ j : J, minpoly K (m j) := minpoly.dvd K m key
  refine Polynomial.Splits.of_dvd ?_ ?_ (Polynomial.map_dvd _ hdvd)
  · rw [Polynomial.map_prod]
    exact Polynomial.splits_prod fun j _ => splits_minpoly_intermediateField (E j) (m j)
  · rw [Polynomial.map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ =>
      Polynomial.map_ne_zero (minpoly.ne_zero_of_finite K (m j))

end StabField

/-! ### `I = G\V`, `E_{ij}` and `{}_iM_j` -/

namespace RationalQuiver

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  (Γ : RationalQuiver K L)

/-- **Clause `RQ2-2.09-C1`.** `I := G\V`, the set of `Gal(L/K)`-orbits of vertices.

@census none (clause witness for `RQ2-2.09-C1`)
-/
abbrev VertexOrbit : Type u := orbitRel.Quotient Gal(L/K) Γ.V

/-- The orbit `Gv ∈ I` of a vertex. -/
abbrev vertexClass (v : Γ.V) : Γ.VertexOrbit := Quotient.mk (orbitRel Gal(L/K) Γ.V) v

/-- **Clause `RQ2-2.09-C2`.** `L_i := L(v_i)` for the fixed representative `v_i := Quotient.out i`
of the orbit `i`.

@census none (clause witness for `RQ2-2.09-C2`)
-/
noncomputable def vertexRep (i : Γ.VertexOrbit) : Γ.V := Quotient.out i

@[simp] theorem vertexClass_vertexRep (i : Γ.VertexOrbit) :
    Γ.vertexClass (Γ.vertexRep i) = i := Quotient.out_eq i

noncomputable def vertexOrbitField (i : Γ.VertexOrbit) : IntermediateField K L :=
  stabField K L (Γ.vertexRep i)

/-- **Clause `RQ2-2.09-C6`.** `E_{ij} = {e ∈ E : s(e) ∈ i, t(e) ∈ j}`.

@census none (clause witness for `RQ2-2.09-C6`)
-/
def edgeSet (i j : Γ.VertexOrbit) : Set Γ.E :=
  {e | Γ.vertexClass (Γ.toRQuiver.source e) = i ∧ Γ.vertexClass (Γ.toRQuiver.target e) = j}

/-- `E_{ij}` is a `Gal(L/K)`-stable subset of `E`: `s` and `t` are equivariant
(`eq:stgaloisequivariance`) and orbits are `G`-stable, so the two defining conditions are. -/
instance mulActionEdgeSet (i j : Γ.VertexOrbit) : MulAction Gal(L/K) (Γ.edgeSet i j) where
  smul σ e := ⟨σ • (e : Γ.E), by
    refine ⟨?_, ?_⟩
    · rw [Γ.source_smul]
      exact (Quotient.sound (mem_orbit _ σ)).trans e.2.1
    · rw [Γ.target_smul]
      exact (Quotient.sound (mem_orbit _ σ)).trans e.2.2⟩
  one_smul e := Subtype.ext (one_smul _ _)
  mul_smul σ τ e := Subtype.ext (mul_smul _ _ _)

@[simp] theorem coe_smul_edgeSet {i j : Γ.VertexOrbit} (σ : Gal(L/K)) (e : Γ.edgeSet i j) :
    ((σ • e : Γ.edgeSet i j) : Γ.E) = σ • (e : Γ.E) := rfl

/-- `G\E_{ij}`, the set of edge orbits from `i` to `j` — the index set of the direct sum in clause
`RQ2-2.09-C7`.

@census none (clause witness for `RQ2-2.09-C7`)
-/
abbrev EdgeOrbit (i j : Γ.VertexOrbit) : Type u := orbitRel.Quotient Gal(L/K) (Γ.edgeSet i j)

/-- `L(e_ε)` for the fixed representative `e_ε := Quotient.out ε` of the edge orbit `ε`. -/
noncomputable def edgeRep {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) : Γ.E :=
  ((Quotient.out ε : Γ.edgeSet i j) : Γ.E)

theorem vertexClass_source_edgeRep {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    Γ.vertexClass (Γ.toRQuiver.source (Γ.edgeRep ε)) = i := (Quotient.out ε).2.1

theorem vertexClass_target_edgeRep {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    Γ.vertexClass (Γ.toRQuiver.target (Γ.edgeRep ε)) = j := (Quotient.out ε).2.2

/-- The source of the chosen representative of an edge orbit `ε ⊆ E_{ij}` lies in the vertex orbit
`i`, hence in the orbit of the chosen representative `v_i`. -/
theorem source_edgeRep_mem_orbit {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    Γ.toRQuiver.source (Γ.edgeRep ε) ∈ orbit Gal(L/K) (Γ.vertexRep i) :=
  Quotient.exact ((Γ.vertexClass_source_edgeRep ε).trans (Γ.vertexClass_vertexRep i).symm)

/-- The target of the chosen representative of an edge orbit `ε ⊆ E_{ij}` lies in the vertex orbit
`j`. -/
theorem target_edgeRep_mem_orbit {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    Γ.toRQuiver.target (Γ.edgeRep ε) ∈ orbit Gal(L/K) (Γ.vertexRep j) :=
  Quotient.exact ((Γ.vertexClass_target_edgeRep ε).trans (Γ.vertexClass_vertexRep j).symm)

noncomputable def edgeOrbitField {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    IntermediateField K L :=
  stabField K L (Γ.edgeRep ε)

/-- The stabilizer of an edge is contained in the stabilizer of its source: this is the left half of
`eq:edgediagram`, `L(s(e)) ⊆ L(e)`.

@census none (clause witness for `RQ2-2.09-C4`)
-/
theorem stabilizer_le_source (e : Γ.E) :
    stabilizer Gal(L/K) e ≤ stabilizer Gal(L/K) (Γ.toRQuiver.source e) := by
  intro σ hσ
  rw [mem_stabilizer_iff] at hσ ⊢
  rw [← Γ.source_smul, hσ]

/-- The stabilizer of an edge is contained in the stabilizer of its target: the right half of
`eq:edgediagram`, `L(t(e)) ⊆ L(e)`.

@census none (clause witness for `RQ2-2.09-C4`)
-/
theorem stabilizer_le_target (e : Γ.E) :
    stabilizer Gal(L/K) e ≤ stabilizer Gal(L/K) (Γ.toRQuiver.target e) := by
  intro σ hσ
  rw [mem_stabilizer_iff] at hσ ⊢
  rw [← Γ.target_smul, hσ]

/-- `eq:edgediagram`, left half, at the quiver level: `L(s(e)) ⊆ L(e)`.

@census none (clause witness for `RQ2-2.09-C4`)
-/
theorem stabField_source_le (e : Γ.E) :
    stabField K L (Γ.toRQuiver.source e) ≤ stabField K L e :=
  IntermediateField.fixedField_le (Γ.stabilizer_le_source e)

/-- `eq:edgediagram`, right half, at the quiver level: `L(t(e)) ⊆ L(e)`.

@census none (clause witness for `RQ2-2.09-C4`)
-/
theorem stabField_target_le (e : Γ.E) :
    stabField K L (Γ.toRQuiver.target e) ≤ stabField K L e :=
  IntermediateField.fixedField_le (Γ.stabilizer_le_target e)

/-- **Clause `RQ2-2.09-C4`, left half.** The structure map `L_i → L(e_ε)` of the `ε`-component of
`{}_iM_j`: the canonical orbit isomorphism `L_i = L(v_i) ≅ L(s(e_ε))` followed by the
`eq:edgediagram` inclusion `L(s(e_ε)) ⊆ L(e_ε)`.

@census none (clause witness for `RQ2-2.09-C4`)
-/
noncomputable def edgeComponentLeft {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    Γ.vertexOrbitField i →ₐ[K] Γ.edgeOrbitField ε :=
  (IntermediateField.inclusion (Γ.stabField_source_le (Γ.edgeRep ε))).comp
    (stabFieldEquivOrbit (Γ.source_edgeRep_mem_orbit ε)).toAlgHom

/-- **Clause `RQ2-2.09-C4`, right half.** The structure map `L_j → L(e_ε)`.

@census none (clause witness for `RQ2-2.09-C4`)
-/
noncomputable def edgeComponentRight {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j) :
    Γ.vertexOrbitField j →ₐ[K] Γ.edgeOrbitField ε :=
  (IntermediateField.inclusion (Γ.stabField_target_le (Γ.edgeRep ε))).comp
    (stabFieldEquivOrbit (Γ.target_edgeRep_mem_orbit ε)).toAlgHom

/-- The value of the left structure map in `L`: the chosen group element carrying `v_i` to
`s(e_ε)`, applied to the argument. The `edgeComponentLeft` analogue of `stabFieldEquivOrbit_coe`.

@census none (helper for `RQ2-2.09-C4`; used by the `§2.4` examples)
-/
theorem edgeComponentLeft_coe {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (α : Γ.vertexOrbitField i) :
    ((Γ.edgeComponentLeft ε α : Γ.edgeOrbitField ε) : L)
      = (mem_orbit_iff.mp (Γ.source_edgeRep_mem_orbit ε)).choose (α : L) := by
  have h : Γ.edgeComponentLeft ε α
      = IntermediateField.inclusion (Γ.stabField_source_le (Γ.edgeRep ε))
          (stabFieldEquivOrbit (Γ.source_edgeRep_mem_orbit ε) α) := rfl
  rw [h, IntermediateField.coe_inclusion, stabFieldEquivOrbit_coe]

/-- The right-hand analogue of `edgeComponentLeft_coe`.

@census none (helper for `RQ2-2.09-C4`; used by the `§2.4` examples)
-/
theorem edgeComponentRight_coe {i j : Γ.VertexOrbit} (ε : Γ.EdgeOrbit i j)
    (α : Γ.vertexOrbitField j) :
    ((Γ.edgeComponentRight ε α : Γ.edgeOrbitField ε) : L)
      = (mem_orbit_iff.mp (Γ.target_edgeRep_mem_orbit ε)).choose (α : L) := by
  have h : Γ.edgeComponentRight ε α
      = IntermediateField.inclusion (Γ.stabField_target_le (Γ.edgeRep ε))
          (stabFieldEquivOrbit (Γ.target_edgeRep_mem_orbit ε) α) := rfl
  rw [h, IntermediateField.coe_inclusion, stabFieldEquivOrbit_coe]

/-- Every vertex lies in the orbit of the chosen representative of its own orbit. -/
theorem mem_orbit_vertexRep (v : Γ.V) :
    v ∈ orbit Gal(L/K) (Γ.vertexRep (Γ.vertexClass v)) :=
  Quotient.exact (Γ.vertexClass_vertexRep (Γ.vertexClass v)).symm

/-- The edge form of `mem_orbit_vertexRep`, pushed from the subtype `E_{ij}` to `E`. -/
theorem mem_orbit_edgeRep {i j : Γ.VertexOrbit} (x : Γ.edgeSet i j) :
    (x : Γ.E) ∈ orbit Gal(L/K) (Γ.edgeRep (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet i j)) x)) := by
  obtain ⟨σ, hσ⟩ := mem_orbit_iff.mp
    (Quotient.exact (Quotient.out_eq (Quotient.mk (orbitRel Gal(L/K) (Γ.edgeSet i j)) x)).symm)
  exact mem_orbit_iff.mpr ⟨σ, congrArg Subtype.val hσ⟩

/-- **Clause `RQ2-2.09-C7`.** `{}_iM_j := ⊕_{ε ∈ G\E_{ij}} L(e_ε)`, realised as the product over the
finite index set `G\E_{ij}` (see the module header on `⊕` versus `∏`).

@census none (clause witness for `RQ2-2.09-C7`)
-/
abbrev edgeAlgebra (i j : Γ.VertexOrbit) : Type u := ∀ ε : Γ.EdgeOrbit i j, Γ.edgeOrbitField ε

/-- **Definition** (the étale `K`-species associated to a `K`-rational quiver; unlabelled in the
source, census `RQ2-2.09`).
For `Γ_K = (Γ, ρ)` with `Γ = (V,E,s,t)` and `G = Gal(L/K)`: `I := G\V`; `L_i := L(v_i) = L^{G_{v_i}}`
for the fixed representative `v_i ∈ i`; `E_{ij} := {e ∈ E : s(e) ∈ i, t(e) ∈ j}`;
`{}_iM_j := ⊕_{ε ∈ G\E_{ij}} L(e_ε)` with the `L_i,L_j`-bimodule structure of `eq:edgediagram`.
`S(Γ_K) := (L_i, {}_iM_j)_{i,j ∈ I}` is an **étale** `K`-species: the vertex and edge stabilizers
are open (continuity of the action), hence the fields `L(v)`, `L(e)` are finite over `K`.

@census    RQ2-2.09
@source    def:speciesofquiver
@clauses   RQ2-2.09-H1, RQ2-2.09-C1, RQ2-2.09-C2, RQ2-2.09-C3, RQ2-2.09-C4, RQ2-2.09-C5, RQ2-2.09-C6,
           RQ2-2.09-C7, RQ2-2.09-C8, RQ2-2.09-C10, RQ2-2.09-C11
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.09-C7`: the direct sum `⊕_{ε ∈ G\E_{ij}}` is
realised as the product `∀ ε : G\E_{ij}`, which is the same object because `G\E_{ij}` is finite
(`E` is finite, `RQ2-1.01-H2`); the product form is the one carrying mathlib's `CommRing`,
`Algebra` and `Algebra.Etale` instances. This is the same `⊕ → ∏` reformulation stage S3 recorded
on `RQ2-2.33`. Everything else is literal: `I` is the orbit quotient (`C1`), `L_i` is the fixed
field at the chosen representative (`C2`), and the two structure maps of `EtaleSpecies` are the
`eq:edgediagram` composites (`C4`), so the "bimodule" of the source is the two-sided algebra
structure whose reading is the one stage S3 recorded on `RQ2-2.02`. Clauses `C3` and `C5`
(independence of the representative, with the bimodule structure) are the separate statements
`stabField_map_smul`, `stabField_apply_eq_of_smul_eq`, `stabFieldEquivOrbit` and
`stabField_map_smul_edgeDiagram`; `C10`/`C11` are `finiteDimensional_stabField`.
-/
noncomputable def toSpecies : EtaleSpecies.{u} K where
  I := Γ.VertexOrbit
  L := fun i => Γ.vertexOrbitField i
  finite_L := fun i => finiteDimensional_stabField _ (Γ.isOpen_stabilizer_V _)
  M := fun i j => Γ.edgeAlgebra i j
  etale_M := fun i j => by
    haveI : ∀ ε : Γ.EdgeOrbit i j, Algebra.Etale K (Γ.edgeOrbitField ε) := fun ε =>
      etale_stabField _ (Γ.isOpen_stabilizer_E _)
    infer_instance
  left := fun i j => Pi.algHom K _ fun ε => Γ.edgeComponentLeft ε
  right := fun i j => Pi.algHom K _ fun ε => Γ.edgeComponentRight ε

/-- **Clause `RQ2-2.09-C5`.** Replacing an edge `e` by a Galois conjugate `σe` replaces the whole
diagram `eq:edgediagram`

`L(s(e)) ⊆ L(e) ⊇ L(t(e))`

by its image under `σ`, which is `L(s(σe)) ⊆ L(σe) ⊇ L(t(σe))`: the isomorphism class of `L(e)`
**together with its `L_i,L_j`-bimodule structure** does not depend on the representative chosen in
the Galois orbit of `e`. The three equations below say exactly that, and the compatibility of the
two structure maps with the isomorphism is then automatic, because all six fields are subfields of
the *same* `L` and the isomorphism is the restriction of the *same* map `σ : L → L`: an inclusion
of subfields is carried to an inclusion of subfields by any field automorphism.

Proof plan (G4): all three are `stabField_map_smul` at the point in question, composed with the
equivariance `eq:stgaloisequivariance` of `s` and `t` (`RationalQuiver.source_smul`,
`.target_smul`) to move `σ •` across the structure maps.

@census none (clause witness for `RQ2-2.09-C5`)
-/
theorem stabField_map_smul_edgeDiagram (σ : Gal(L/K)) (e : Γ.E) :
    IntermediateField.map (σ : L →ₐ[K] L) (stabField K L e) = stabField K L (σ • e) ∧
      IntermediateField.map (σ : L →ₐ[K] L) (stabField K L (Γ.toRQuiver.source e))
          = stabField K L (Γ.toRQuiver.source (σ • e)) ∧
        IntermediateField.map (σ : L →ₐ[K] L) (stabField K L (Γ.toRQuiver.target e))
          = stabField K L (Γ.toRQuiver.target (σ • e)) :=
  ⟨stabField_map_smul σ e,
    (stabField_map_smul σ (Γ.toRQuiver.source e)).trans (by rw [Γ.source_smul]),
    (stabField_map_smul σ (Γ.toRQuiver.target e)).trans (by rw [Γ.target_smul])⟩

end RationalQuiver

end RationalQuivers
