module

public import RationalQuivers.Quiver.Rep.Basic
public import RationalQuivers.Quiver.Models
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/-!
# The category `Rep(Γ_K)` of finite-dimensional rational representations

Formalizes the second half of §1.3 of `latex/rational_quivers.tex` (census `RQ2-1.10`, first half;
the nilpotent full subcategory `Rep^nil(Γ_K)` is `Quiver/Rep/Nilpotent.lean`).

## Main definitions / results
* `RationalQuivers.RationalQuiver.FDRep` — a **finite-dimensional** `K`-rational representation:
  a `Rep` together with finite-dimensionality of every `M(v)` over `L`, carried as an object
  field (design decision **D7**, `workflow/PLAN.md`).
* `RationalQuivers.RationalQuiver.FDRep.instCategory` — `Rep(Γ_K)` as a mathlib
  `CategoryTheory.Category` (census `RQ2-1.10`).
* **Added 2026-09-02 (commission C-M1-1, `WORKFLOW.md` F5 amendment of frozen S2; G8 cross-model
  review findings F-M1-R-2 / F-M1-R-8).** `RationalQuiver.Rep.scalarHom` (with `…_ne_id`,
  `…_ψ_ne_zero`) — the first concrete non-identity morphism of rational representations in the
  tree, and `RationalQuivers.constLOneTwo` its unconditional instantiation at `ex:gelfand` over
  `ℂ/ℝ`; `RationalQuiver.Rep.trivialRep` and `RationalQuiver.FDRep.trivialFDRep` — the G5 item-(3)
  all-trivial probes for `RQ2-1.08`/`RQ2-1.10`, in content;
  `RationalQuivers.exists_edge_compat_not_rational` — the sharp probe showing `RQ2-1.09`'s
  `rational` field is **not** implied by `ψ` + `edge`.

## Implementation notes
**D7.**  Finite-dimensionality is an object *field*, not a side condition on theorems: the source
says "`Rep(Γ_K)` is the category of **finite-dimensional** `K`-rational representations", so a
category whose objects were arbitrary representations would be a different — and strictly larger —
category, which clause `RQ2-1.10-C1` forbids.

Finite-dimensionality is over `L`, one `M(v)` at a time.  Since `V` is finite (clause
`RQ2-1.01-H1`) this is equivalent to finite-dimensionality of `⊔_v M(v)`, and — via Galois descent
(`RQ2-1.13`) — to finite-dimensionality of the `K`-form `M_K`; the source uses the three
interchangeably.
-/

universe u

namespace RationalQuivers

namespace RationalQuiver

open CategoryTheory

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- A **finite-dimensional** `K`-rational representation of `Γ_K`: the objects of `Rep(Γ_K)`.
Finite-dimensionality of each `M(v)` over `L` is an object field (design decision **D7**).

@census none (helper: the object type of `RQ2-1.10`)
-/
structure FDRep (Γ : RationalQuiver K L) : Type (u + 1) extends Rep Γ where
  /-- Clause `RQ2-1.10-C1`: each `M(v)` is a finite-dimensional `L`-vector space. -/
  finiteDimensional : ∀ v : Γ.V, FiniteDimensional L (toRep.M v)

attribute [instance] FDRep.finiteDimensional

namespace FDRep

variable {Γ : RationalQuiver K L}

/-- **Definition** (unlabelled, §1.3 of the source; census `RQ2-1.10`).

For a `K`-rational quiver `Γ_K` (clause `RQ2-1.10-H1`), `Rep(Γ_K)` is the category of
**finite-dimensional** `K`-rational representations of `Γ_K` (clause `RQ2-1.10-C1`), with the
homomorphisms of `def:rationalrepresentationhom` (census `RQ2-1.09`) as morphisms.

The full subcategory `Rep^nil(Γ_K)` of finite-dimensional **nilpotent** representations
(clauses `RQ2-1.10-C2`, `RQ2-1.10-C3`) is `RationalQuiver.RepNil` in
`Quiver/Rep/Nilpotent.lean`; it is built with mathlib's `ObjectProperty.FullSubcategory`, so its
fullness (clause `RQ2-1.10-C3`) is mathlib's `ObjectProperty.ι`-fullness and not a private
restatement.

@census    RQ2-1.10
@source    def:repcategories
@clauses   RQ2-1.10-H1, RQ2-1.10-C1, RQ2-1.10-C2, RQ2-1.10-C3
@imports   none
@divergence none.  Finite-dimensionality (clause `RQ2-1.10-C1`) is an object field of `FDRep`
per design decision **D7**, so it cannot be dropped by any downstream construction; the source's
"category of finite-dimensional representations" is `FDRep Γ` with this instance.
-/
instance instCategory (Γ : RationalQuiver K L) : Category.{u, u + 1} (FDRep Γ) where
  Hom M N := Rep.Hom M.toRep N.toRep
  id M := Rep.Hom.id M.toRep
  comp f g := f.comp g
  id_comp _ := by apply Rep.Hom.ext; rfl
  comp_id _ := by apply Rep.Hom.ext; rfl
  assoc _ _ _ := by apply Rep.Hom.ext; rfl

/-- The identity morphism of `Rep(Γ_K)` has identity components.  @census none (helper) -/
@[simp]
theorem id_ψ (M : FDRep Γ) (v : Γ.V) : (𝟙 M : Rep.Hom M.toRep M.toRep).ψ v = LinearMap.id := rfl

/-- Composition in `Rep(Γ_K)` is componentwise.  @census none (helper) -/
@[simp]
theorem comp_ψ {M N P : FDRep Γ} (f : M ⟶ N) (g : N ⟶ P) (v : Γ.V) :
    (f ≫ g).ψ v = g.ψ v ∘ₗ f.ψ v := rfl

/-- **G5 non-vacuity** (`WORKFLOW.md` §4/G5): the tautological representation `M(v) = L` with
identity edge maps is a finite-dimensional `K`-rational representation, so `Rep(Γ_K)` is
inhabited, and by `Rep.constLOne_φEdge_ne_zero` it is not the zero object.

@census none (helper: G5 inhabitant of `RQ2-1.10`)
-/
def constLOne (Γ : RationalQuiver K L) : FDRep Γ where
  toRep := Rep.constLOne Γ
  finiteDimensional _ := inferInstanceAs (FiniteDimensional L L)

/-- **G5 non-vacuity**: the tautological representation with zero edge maps, the inhabitant of
`Rep^nil(Γ_K)`.

@census none (helper: G5 inhabitant of `RQ2-1.10`)
-/
def constLZero (Γ : RationalQuiver K L) : FDRep Γ where
  toRep := Rep.constLZero Γ
  finiteDimensional _ := inferInstanceAs (FiniteDimensional L L)

end FDRep
/-! ## G5 witnesses for the two S2 structures the G8 cross-model review found uncovered

**Provenance.** `workflow/audit/M1/FINAL_AUDIT.md` §11.7, finding **F-M1-R-2** (cross-model
review, 2026-09-02): `RationalQuiver.Rep.Hom` (census `RQ2-1.09`) and
`RationalQuiver.FDRep` (census `RQ2-1.10`) carried **no G5 item-(3) all-trivial entry anywhere**,
and F-M1-R-8 records that no concrete non-identity morphism of rational representations existed in
the tree — `Rep.Hom.id` and `Rep.Hom.comp` were the only closed inhabitants.  Landed by commission
**C-M1-1**, 2026-09-02, as a dated `WORKFLOW.md` F5 amendment of frozen stage S2; no S2 statement
changed.  The `Meta/Vacuity.lean` §4 registry entries citing these declarations are owed to the
**instrument owner** (F3).

Why here and not in `Meta/Vacuity.lean`: a G5.2 witness is implementer-side content, and that
file's own scope note forbids it carrying one; the §3.1/P6 relocation is the precedent.
-/

namespace Rep

variable {Γ : RationalQuiver K L}

/-- **G5.2 (`Rep.Hom`, census `RQ2-1.09`): the `K`-scalar endomorphism of *any* rational
representation.**  Multiplication by `algebraMap K L a` is `L`-linear on each fibre, commutes with
the edge maps because those are `L`-linear, and satisfies the `rational` field because `σ` fixes
the image of `K` (`AlgEquiv.commutes`) — which is exactly where the hypothesis "`a` comes from the
base field" is used.  For `a ∉ K` the same family satisfies `edge` and **fails** `rational`
(`RationalQuivers.exists_edge_compat_not_rational` below), so this is a sharp witness: the
`rational` field is not implied by the other two.

@census none (G5.2 non-degenerate inhabitant of `RQ2-1.09`'s `Rep.Hom`)
-/
def scalarHom (M : Rep Γ) (a : K) : Rep.Hom M M where
  ψ _ := (algebraMap K L a) • LinearMap.id
  edge e m := by
    show (algebraMap K L a) • (M.φEdge e m) = M.φEdge e ((algebraMap K L a) • m)
    rw [map_smul]
  rational σ v m := by
    show (algebraMap K L a) • (M.φ σ v m) = M.φ σ v ((algebraMap K L a) • m)
    rw [M.semilinear, AlgEquiv.commutes]

/-- The components of `scalarHom`, on elements.  @census none (helper) -/
@[simp] theorem scalarHom_ψ_apply (M : Rep Γ) (a : K) (v : Γ.V) (m : M.M v) :
    (scalarHom M a).ψ v m = (algebraMap K L a) • m := rfl

/-- **G5.2 non-degeneracy** (`RQ2-1.09`, first criterion): for `a ≠ 1` and a fibre with more than
one point, the scalar endomorphism is **not** the identity — so `Rep.Hom` has closed inhabitants
other than `Hom.id`/`Hom.comp`, which is finding F-M1-R-8's gap for `RQ2-1.09`.

@census none (G5.2 non-degeneracy witness for `RQ2-1.09`)
-/
theorem scalarHom_ne_id (M : Rep Γ) {a : K} (v : Γ.V)
    (hM : Nontrivial (M.M v)) (ha : a ≠ 1) : scalarHom M a ≠ Rep.Hom.id M := by
  obtain ⟨m, hm⟩ := @exists_ne _ hM 0
  intro h
  have h0 : ((algebraMap K L) a) • m = m := by
    have := congrArg (fun f => Rep.Hom.ψ f v m) h
    simpa using this
  have h2 : (((algebraMap K L) a) - 1) • m = 0 := by
    rw [sub_smul, h0, one_smul, sub_self]
  by_cases hc : ((algebraMap K L) a) - 1 = 0
  · refine ha ((algebraMap K L).injective ?_)
    rw [map_one]
    exact sub_eq_zero.mp hc
  · refine hm ?_
    have h3 := congrArg (fun x => (((algebraMap K L) a) - 1)⁻¹ • x) h2
    simpa [smul_smul, inv_mul_cancel₀ hc] using h3

/-- **G5.2 non-degeneracy** (`RQ2-1.09`, second criterion): for `a ≠ 0` the scalar endomorphism is
**not** the zero morphism, so the inhabitant is not the degenerate one either.

@census none (G5.2 non-degeneracy witness for `RQ2-1.09`)
-/
theorem scalarHom_ψ_ne_zero (M : Rep Γ) {a : K} (v : Γ.V)
    (hM : Nontrivial (M.M v)) (ha : a ≠ 0) : (scalarHom M a).ψ v ≠ 0 := by
  obtain ⟨m, hm⟩ := @exists_ne _ hM 0
  intro h
  refine hm ?_
  have h0 : ((algebraMap K L) a) • m = 0 := by
    have := congrArg (fun f : M.M v →ₗ[L] M.M v => f m) h
    simpa using this
  have ha' : (algebraMap K L) a ≠ 0 := by
    simpa using (map_ne_zero_iff (algebraMap K L) (algebraMap K L).injective).mpr ha
  have h3 := congrArg (fun x => ((algebraMap K L) a)⁻¹ • x) h0
  simpa [smul_smul, inv_mul_cancel₀ ha'] using h3

/-- The fibres of the tautological representation are non-trivial.  Stated so that the
non-degeneracy lemmas above can be instantiated without unfolding `constL`.

@census none (helper) -/
theorem constLOne_nontrivial (Γ : RationalQuiver K L) (v : Γ.V) :
    Nontrivial ((constLOne Γ).M v) := inferInstanceAs (Nontrivial L)

/-- **G5.3 probe (`Rep`, in content): the all-trivial interpretation of
`def:rationalrepresentations`** — every fibre the zero space, every semi-linear map the identity,
every edge map zero.

**It type-checks.**  So `Rep`'s fields do not exclude the all-zero model.  *Verdict: expected, and
not a defect* — `Rep(Γ_K)` is a category of representations and must have a zero object; the
finding is only that non-degeneracy has to come from an inhabitant, and it does (`constLOne`,
`constL_nontrivial`, `constLOne_φEdge_ne_zero`).

This is the **content copy** of `Meta/Vacuity.lean` §4.1's `zeroRep`, landed here because
`FDRep`'s own item-(3) probe (`FDRep.trivialFDRep` below) needs a `Rep` to extend and `Meta/` is
never imported by content (`CONVENTIONS.md` §1).  The two are independent measurements of the same
fact; neither is a G5.2 witness.

@census none (G5.3 all-trivial probe for `RQ2-1.08`, prerequisite of the `RQ2-1.10` probe)
-/
def trivialRep (Γ : RationalQuiver K L) : Rep Γ where
  M _ := PUnit
  φ _ _ := AddEquiv.refl _
  semilinear _ _ _ _ := rfl
  cocycle σ τ v m := by rw [mul_smul]
  smooth x := by
    haveI := Γ.galois
    obtain ⟨v, m⟩ := x
    have hset : {σ : Gal(L/K) |
        (⟨σ • v, AddEquiv.refl PUnit m⟩ : (w : Γ.V) × PUnit) = ⟨v, m⟩}
        = ((MulAction.stabilizer Gal(L/K) v : Subgroup Gal(L/K)) : Set Gal(L/K)) := by
      ext σ
      simp [Sigma.mk.injEq, MulAction.mem_stabilizer_iff, eq_comm]
    rw [hset]
    exact Γ.isOpen_stabilizer_V v
  φEdge _ := 0
  edge_equivariance σ e m m' _ := by
    haveI := Γ.galois
    rw [Γ.target_smul σ e]

end Rep

namespace FDRep

/-- **G5.3 probe (`FDRep`, census `RQ2-1.10`): the all-trivial interpretation.**  The all-zero
representation is finite-dimensional, so it is an object of `Rep(Γ_K)`.

**It type-checks.**  So the `finiteDimensional` field does not exclude the degenerate model
either.  *Verdict: expected, and not a defect* — the zero object of `Rep(Γ_K)` is finite
dimensional, and design decision **D7** puts finite-dimensionality on the object precisely so that
it cannot be *dropped*, not so that it excludes zero.  The separation that matters is
`trivialFDRep_subsingleton` versus `constLOne_nontrivial` below.

@census none (G5.3 all-trivial probe for `RQ2-1.10`)
-/
def trivialFDRep (Γ : RationalQuiver K L) : FDRep Γ where
  toRep := Rep.trivialRep Γ
  finiteDimensional _ := inferInstanceAs (FiniteDimensional L PUnit)

/-- The all-trivial object of `Rep(Γ_K)` has one-point fibres … @census none (G5.3 probe) -/
theorem trivialFDRep_subsingleton (Γ : RationalQuiver K L) (v : Γ.V) :
    Subsingleton ((trivialFDRep Γ).toRep.M v) := inferInstanceAs (Subsingleton PUnit)

/-- … and the G5.2 inhabitant `constLOne` does not: the two are genuinely different objects of
`Rep(Γ_K)`, which is what makes `RQ2-1.10`'s category non-degenerate.

@census none (G5.2 non-degeneracy witness for `RQ2-1.10`)
-/
theorem constLOne_nontrivial (Γ : RationalQuiver K L) (v : Γ.V) :
    Nontrivial ((constLOne Γ).toRep.M v) := inferInstanceAs (Nontrivial L)

end FDRep

end RationalQuiver

/-! ### The S2 witnesses at a concrete non-split quiver (`ex:gelfand` over `ℂ/ℝ`)

The lemmas above are conditional families; this section discharges their hypotheses at the
source's own example, so that no non-degeneracy claim for `RQ2-1.09`/`RQ2-1.10` rests on a family
that might be empty.  Same pattern as stage S1's `ComplexReal` section (probe **P2**).
-/

section ComplexRealRep

open RationalQuiver

/-- **G5.2, unconditionally**: a concrete non-identity, non-zero endomorphism of a rational
representation of the **non-split** `ex:gelfand` quiver over `ℂ/ℝ` — multiplication by `2 ∈ ℝ`.

@census none (G5.2 non-degenerate inhabitant of `RQ2-1.09`, instantiated)
-/
noncomputable def constLOneTwo : Rep.Hom (Rep.constLOne gelfandComplexReal)
    (Rep.constLOne gelfandComplexReal) :=
  Rep.scalarHom (Rep.constLOne gelfandComplexReal) (2 : ℝ)

/-- **G5.2 non-degeneracy, unconditionally**: it is not the identity.

@census none (G5.2 non-degeneracy witness for `RQ2-1.09`, instantiated)
-/
theorem constLOneTwo_ne_id :
    constLOneTwo ≠ Rep.Hom.id (Rep.constLOne gelfandComplexReal) :=
  Rep.scalarHom_ne_id _ (0 : RQuiver.gelfand.V)
    (Rep.constLOne_nontrivial gelfandComplexReal (0 : RQuiver.gelfand.V)) (by norm_num)

/-- **G5.2 non-degeneracy, unconditionally**: it is not the zero morphism.

@census none (G5.2 non-degeneracy witness for `RQ2-1.09`, instantiated)
-/
theorem constLOneTwo_ψ_ne_zero :
    constLOneTwo.ψ (0 : RQuiver.gelfand.V) ≠ 0 :=
  Rep.scalarHom_ψ_ne_zero (a := (2 : ℝ)) (Rep.constLOne gelfandComplexReal)
    (0 : RQuiver.gelfand.V)
    (Rep.constLOne_nontrivial gelfandComplexReal (0 : RQuiver.gelfand.V)) (by norm_num)

/-- **G5.3, the sharp probe for `RQ2-1.09`: the `rational` field is not implied by the other two.**
Multiplication by `i ∈ ℂ` on every fibre of the tautological representation of `ex:gelfand` over
`ℂ/ℝ` is `ℂ`-linear and commutes with the edge maps — it satisfies `Rep.Hom`'s `ψ` and `edge`
fields — but it does **not** satisfy `rational`: at `σ =` complex conjugation and `m = 1` the two
sides are `i` and `−i`.

So `RQ2-1.09`'s clause `RQ2-1.09-C2` (`eq:koecheractiononrephom`) is not redundant: dropping it
would enlarge `Hom_{Rep(Γ_K)}` strictly.  This is the one probe in the S2 group that is *not* an
"expected, not a defect" record — it is positive evidence that a field carries content, of the
kind `WORKFLOW.md` G5.4 (liveness) asks for and a `Subsingleton` argument cannot give.

@census none (G5.3 sharp probe for `RQ2-1.09`)
-/
theorem exists_edge_compat_not_rational :
    ∃ ψ : ∀ v : gelfandComplexReal.V,
        (Rep.constLOne gelfandComplexReal).M v →ₗ[ℂ] (Rep.constLOne gelfandComplexReal).M v,
      (∀ (e : gelfandComplexReal.E)
          (m : (Rep.constLOne gelfandComplexReal).M (gelfandComplexReal.toRQuiver.source e)),
          ψ (gelfandComplexReal.toRQuiver.target e)
              ((Rep.constLOne gelfandComplexReal).φEdge e m)
            = (Rep.constLOne gelfandComplexReal).φEdge e
                (ψ (gelfandComplexReal.toRQuiver.source e) m)) ∧
      ¬ (∀ (σ : Gal(ℂ/ℝ)) (v : gelfandComplexReal.V)
            (m : (Rep.constLOne gelfandComplexReal).M v),
          ψ (σ • v) ((Rep.constLOne gelfandComplexReal).φ σ v m)
            = (Rep.constLOne gelfandComplexReal).φ σ v (ψ v m)) := by
  refine ⟨fun _ => Complex.I • LinearMap.id, ?_, ?_⟩
  · intro e m
    show Complex.I • ((Rep.constLOne gelfandComplexReal).φEdge e m)
      = (Rep.constLOne gelfandComplexReal).φEdge e (Complex.I • m)
    rw [map_smul]
  · intro h
    have h0 := h Complex.conjAe (0 : RQuiver.gelfand.V) (1 : ℂ)
    have h1 : Complex.I * (Complex.conjAe (1 : ℂ)) = Complex.conjAe (Complex.I * (1 : ℂ)) := h0
    norm_num [Complex.ext_iff] at h1

end ComplexRealRep

end RationalQuivers

