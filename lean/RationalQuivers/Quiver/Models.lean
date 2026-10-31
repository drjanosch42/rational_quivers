module

public import RationalQuivers.Quiver.GaloisSet
public import RationalQuivers.Quiver.Hom
public import RationalQuivers.Quiver.Relations
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-!
# Concrete models (gate G5)

Inhabitants of every structure introduced in `RationalQuivers/Quiver/` — `WORKFLOW.md` G5 requires
a concrete inhabitant in the same commit as the definition, and a **non-degenerate** one where
degeneracy is a live risk (for `RationalQuiver` the degenerate model is the split one, `ρ = 1`).

## Main definitions / results
* `RationalQuivers.RQuiver.oneLoop`, `.twoLoops`, `.cyclic`, `.gelfand` — the classical quivers of
  `ex:twoloops`, `ex:cyclic` and `ex:gelfand`.
* `RationalQuivers.RQuiver.gelfandSwap` — the `±`-swap in `Aut(Q_Gelfand)`, a **non-trivial**
  inhabitant of `RQuiver.Aut`.
* `RationalQuivers.RationalQuiver.split` — the degenerate (split) rational structure, `ρ = 1`.
* `RationalQuivers.RationalQuiver.gelfandOfCardTwo` — the `ℚ`-rational Gelfand quiver of
  `ex:gelfand`, for any quadratic Galois extension `L/K` (the source: "we choose
  `G = Gal(ℚ[√-1]/ℚ)`, but one may also choose `G = Gal(ℂ/ℝ)` or any other quadratic extension
  `L/K` for that matter"). This is the **non-degenerate** inhabitant required by G5.2 and is
  consumed unchanged by stage S8.
* `RationalQuivers.RationalQuiver.gelfandOfCardTwo_not_isSplit`, `…_exists_smul_ne_self_V`,
  `…_exists_smul_ne_self_E` — the **non-degeneracy proofs** (G5 witnesses, S1 G4 probe **P1**):
  the rational structure is not `1`, and the `±`-swap really moves a vertex and an edge.
* `RationalQuivers.RQuiver.pathMinus`, `.pathPlus`, `.gelfandRelation`, `.gelfandRelationSet` —
  the Gelfand quiver's relation `a₋b₋ = a₊b₊` of `ex:gelfand` as a pair of parallel length-two
  paths at `⋆`, with the action of the `±`-swap on it computed
  (`RQuiver.onRelation_gelfandSwap_image`) — the API the `RQ2-1.19` non-degeneracy probe needs.
* `RationalQuivers.isGalois_real_complex`, `RationalQuivers.card_gal_complex_real`,
  `RationalQuivers.gelfandComplexReal` — the **concrete instantiation** at `L/K = ℂ/ℝ`
  (S1 G4 probe **P2**): the hypothesis `Nat.card Gal(L/K) = 2` is discharged, so the
  non-degenerate family above is not a conditional family with an empty index.
* `RationalQuivers.diagramEquiv_symm_not_isSplit` — the `RQ2-1.23` non-triviality witness
  (S1 G4 probe **P6**): carrying the non-split `ex:gelfand` model through `diagramEquiv` and back
  returns a non-split rational quiver, so the equivalence does not quietly forget the Galois action.

* **Added 2026-09-02 (commission C-M1-1, `WORKFLOW.md` F5 amendment of frozen S1; G8 cross-model
  review findings F-M1-R-2 / F-M1-R-8).** G5 witnesses and all-trivial probes for the four S1
  structures that carried none: `RQuiver.gelfandSwapHom`, `.cyclicToGelfand` (with
  `…_onV_injective`, `…_onV_not_surjective`) and the probe `RQuiver.toOneLoop` for `RQuiver.Hom`;
  `RationalQuivers.gelfandComplexRealSwapHom` (with `…_ne_id`) and the probe `splitCollapseHom`
  for `RationalQuiver.Hom` (census `RQ2-1.04`) — the first concrete non-identity morphism of
  `K`-rational quivers in the tree; `gelfandVertexGaloisSet`, `.gelfandEdgeGaloisSet` (with
  `…_card`, `…_act_ne_id`) and the probe `trivialGaloisSet` for `GaloisSet` — its first inhabitant
  of any kind; `gelfandGaloisSetDiagram` (with `…_edges_act_ne_id`, `…_source_ne_target`) and the
  probe `trivialGaloisSetDiagram` for `GaloisSetDiagram`.

## Implementation notes
* The non-degeneracy proofs (G5, S1 `G4-VERIFICATION.md` §7 observation 1, probes P1/P2) are
  *additions*: no statement above them changed.  `ℂ/ℝ` is used rather than the source's
  `ℚ[√-1]/ℚ` because mathlib supplies the whole chain off the shelf — `Complex.isAlgClosed`
  (fundamental theorem of algebra) gives `IsAlgClosure ℝ ℂ`, hence `IsAlgClosure.isGalois`
  (`CharZero ℝ`), and `IsGalois.card_aut_eq_finrank` with `Complex.finrank_real_complex` gives
  `Nat.card Gal(ℂ/ℝ) = 2`.  The source explicitly sanctions the substitution ("one may also choose
  `G = Gal(ℂ/ℝ)` or any other quadratic extension `L/K` for that matter").
-/

universe u

namespace RationalQuivers

open CategoryTheory

namespace RQuiver

/-- The one-loop quiver `♦` with a single loop `a` (the quiver restricted in `ex:twoloops`).

@census none (G5 inhabitant of `RQuiver`)
-/
@[reducible] def oneLoop : RQuiver.{0} where
  V := Fin 1
  E := Fin 1
  source := ![0]
  target := ![0]
  finite_V := inferInstance
  finite_E := inferInstance

/-- The disconnected two-loop quiver `−  +` with loops `a₋`, `a₊` (the answer of `ex:twoloops`).

@census none (G5 inhabitant of `RQuiver`)
-/
@[reducible] def twoLoops : RQuiver.{0} where
  V := Fin 2
  E := Fin 2
  source := ![0, 1]
  target := ![0, 1]
  finite_V := inferInstance
  finite_E := inferInstance

/-- The cyclic quiver `Q_cyclic` of `ex:cyclic`: vertices `−`(=0), `+`(=1), arrows `a : − → +`
(=0) and `b : + → −` (=1).

@census none (G5 inhabitant of `RQuiver`)
-/
@[reducible] def cyclic : RQuiver.{0} where
  V := Fin 2
  E := Fin 2
  source := ![0, 1]
  target := ![1, 0]
  finite_V := inferInstance
  finite_E := inferInstance

/-- The Gelfand quiver `Q_Gelfand` of `ex:gelfand`: vertices `−`(=0), `⋆`(=1), `+`(=2) and arrows
`a₋ : − → ⋆` (=0), `b₋ : ⋆ → −` (=1), `a₊ : + → ⋆` (=2), `b₊ : ⋆ → +` (=3).

@census none (G5 inhabitant of `RQuiver`; the non-degenerate model required by G5.2)
-/
@[reducible] def gelfand : RQuiver.{0} where
  V := Fin 3
  E := Fin 4
  source := ![0, 1, 2, 1]
  target := ![1, 0, 1, 2]
  finite_V := inferInstance
  finite_E := inferInstance

/-- The `±`-swap on the vertices of the Gelfand quiver: `c(±) = ∓`, `c(⋆) = ⋆`.

@census none (helper for the G5 inhabitant)
-/
@[reducible] def gelfandVertexSwap : Equiv.Perm (Fin 3) where
  toFun := ![2, 1, 0]
  invFun := ![2, 1, 0]
  left_inv := by decide
  right_inv := by decide

/-- The `±`-swap on the edges of the Gelfand quiver: `c(a_±) = a_∓`, `c(b_±) = b_∓`.

@census none (helper for the G5 inhabitant)
-/
@[reducible] def gelfandEdgeSwap : Equiv.Perm (Fin 4) where
  toFun := ![2, 3, 0, 1]
  invFun := ![2, 3, 0, 1]
  left_inv := by decide
  right_inv := by decide

/-- The `±`-swap `c` of `ex:gelfand` as an automorphism of the Gelfand quiver. A **non-trivial**
inhabitant of `RQuiver.Aut`, as G5.2 requires.

@census none (G5 inhabitant of `RQuiver.Aut`)
-/
@[reducible] def gelfandSwap : RQuiver.Aut gelfand := CategoryTheory.Aut.of
  { hom :=
      { onV := gelfandVertexSwap
        onE := gelfandEdgeSwap
        onV_source := by decide
        onV_target := by decide }
    inv :=
      { onV := gelfandVertexSwap
        onE := gelfandEdgeSwap
        onV_source := by decide
        onV_target := by decide }
    hom_inv_id := by
      refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)
    inv_hom_id := by
      refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide) }

/-- The `±`-swap is an involution: `c² = 1`.

@census none (helper for the G5 inhabitant)
-/
theorem gelfandSwap_mul_self : gelfandSwap * gelfandSwap = 1 := by
  refine RQuiver.Aut.ext ?_
  refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)

/-- The `±`-swap is not the identity: the Gelfand quiver really does carry a non-trivial
`Aut(Γ)`-element, so the rational structure built from it is not split.

@census none (helper: non-degeneracy evidence for G5.2)
-/
theorem gelfandSwap_ne_one : gelfandSwap ≠ 1 := by
  intro h
  have : gelfandSwap.hom.onV 0 = (1 : RQuiver.Aut gelfand).hom.onV 0 := by rw [h]
  revert this
  decide

/-- The `±`-swap moves the vertex `−` (`= 0`) to `+` (`= 2`): the computational core of the
non-degeneracy witness `RationalQuiver.gelfandOfCardTwo_exists_smul_ne_self_V`.

@census none (helper: non-degeneracy evidence for G5.2)
-/
theorem toPermV_gelfandSwap_zero : (Aut.toPermV gelfand gelfandSwap) 0 = 2 := by decide

/-- The `±`-swap moves the edge `a₋` (`= 0`) to `a₊` (`= 2`): the computational core of the
non-degeneracy witness `RationalQuiver.gelfandOfCardTwo_exists_smul_ne_self_E`.

@census none (helper: non-degeneracy evidence for G5.2)
-/
theorem toPermE_gelfandSwap_zero : (Aut.toPermE gelfand gelfandSwap) 0 = 2 := by decide

/-! ### The Gelfand relation `a₋ b₋ = a₊ b₊` (`ex:gelfand`, census `RQ2-1.19`)

The source's Gelfand quiver carries one relation: the two length-two loops at `⋆`, one through `−`
and one through `+`, are equal.  The declarations below name those two paths, package them as a
`Relation`, and compute the `±`-swap's action on them — the API a non-degeneracy probe for
`RQ2-1.19` needs, and the only concrete `Relation` in the tree.

**Elaboration note.** `gelfand` is `@[reducible]`, so `gelfand.V` unfolds to `Fin 3` before
instance search runs and `RQuiver.instQuiverV` is no longer found by unification.  The arrows and
paths therefore name the instance explicitly (`@Quiver.Hom gelfand.V (instQuiverV gelfand) …`, and
`letI` in the path bodies).  A `local instance` for `Quiver gelfand.V` was rejected instead: it
would be an instance on `Fin 3`, which mathlib can already give a `Quiver` structure via
`Preorder`, and `CONVENTIONS.md` §5 forbids shadowing a mathlib instance.
-/

/-- The arrow `a₋ : − → ⋆` of the Gelfand quiver (edge `0`). @census none (helper) -/
def aMinus : @_root_.Quiver.Hom gelfand.V (instQuiverV gelfand) 0 1 := ⟨0, rfl, rfl⟩

/-- The arrow `b₋ : ⋆ → −` of the Gelfand quiver (edge `1`). @census none (helper) -/
def bMinus : @_root_.Quiver.Hom gelfand.V (instQuiverV gelfand) 1 0 := ⟨1, rfl, rfl⟩

/-- The arrow `a₊ : + → ⋆` of the Gelfand quiver (edge `2`). @census none (helper) -/
def aPlus : @_root_.Quiver.Hom gelfand.V (instQuiverV gelfand) 2 1 := ⟨2, rfl, rfl⟩

/-- The arrow `b₊ : ⋆ → +` of the Gelfand quiver (edge `3`). @census none (helper) -/
def bPlus : @_root_.Quiver.Hom gelfand.V (instQuiverV gelfand) 1 2 := ⟨3, rfl, rfl⟩

/-- The length-two loop `a₋ b₋` at `⋆`, through the vertex `−`.

@census none (helper for `RQ2-1.19`; `ex:gelfand`)
-/
def pathMinus : @_root_.Quiver.Path gelfand.V (instQuiverV gelfand) 1 1 :=
  letI := instQuiverV gelfand
  (_root_.Quiver.Path.nil.cons bMinus).cons aMinus

/-- The length-two loop `a₊ b₊` at `⋆`, through the vertex `+`.

@census none (helper for `RQ2-1.19`; `ex:gelfand`)
-/
def pathPlus : @_root_.Quiver.Path gelfand.V (instQuiverV gelfand) 1 1 :=
  letI := instQuiverV gelfand
  (_root_.Quiver.Path.nil.cons bPlus).cons aPlus

/-- The two loops are **distinct** paths: they pass through different vertices (`−` versus `+`),
so the Gelfand relation is not the trivial equation `p = p`.

@census none (helper for `RQ2-1.19`: the relation is non-degenerate)
-/
theorem pathMinus_ne_pathPlus : pathMinus ≠ pathPlus := by
  intro h
  rw [pathMinus, pathPlus] at h
  injection h with h1 h2 h3 h4
  exact absurd h1 (by decide)

/-- **`ex:gelfand`'s relation** `a₋ b₋ = a₊ b₊`, as an ordered pair of parallel paths at `⋆`.

@census none (G5 inhabitant of `RQuiver.Relation`; `ex:gelfand`)
-/
def gelfandRelation : Relation gelfand := ⟨(1, 1), pathMinus, pathPlus⟩

/-- The same relation written the other way round, `a₊ b₊ = a₋ b₋`.  It is a *different* element of
`Relation gelfand` (`Relation` is an **ordered** pair, `gelfandRelation_ne_gelfandRelationSwap`),
which is exactly why the relation *set* of `ex:gelfand` must contain both: the `±`-swap exchanges
them.

@census none (helper for `RQ2-1.19`)
-/
def gelfandRelationSwap : Relation gelfand := ⟨(1, 1), pathPlus, pathMinus⟩

/-- The two orderings are distinct elements of `Relation gelfand`.

@census none (helper for `RQ2-1.19`: the swap really moves the relation)
-/
theorem gelfandRelation_ne_gelfandRelationSwap : gelfandRelation ≠ gelfandRelationSwap := by
  intro h
  rw [gelfandRelation, gelfandRelationSwap] at h
  injection h with h1 h2
  exact pathMinus_ne_pathPlus (congrArg Prod.fst h2)

/-- The `±`-swap carries the Gelfand relation to its transpose: `c · (a₋b₋ = a₊b₊)` is
`(a₊b₊ = a₋b₋)`.  Both `onV` and the two transported paths are computed by `rfl`.

@census none (helper for `RQ2-1.19`)
-/
theorem onRelation_gelfandSwap :
    Aut.onRelation gelfandSwap gelfandRelation = gelfandRelationSwap := rfl

/-- …and back. @census none (helper for `RQ2-1.19`) -/
theorem onRelation_gelfandSwap_swap :
    Aut.onRelation gelfandSwap gelfandRelationSwap = gelfandRelation := rfl

/-- **The relation set of `ex:gelfand`**: `{a₋b₋ = a₊b₊}` in both orderings.  The two-element set
is forced: `Relation` is an ordered pair and the `±`-swap exchanges the orderings, so no one-element
set of relations is stable under the Gelfand quiver's rational structure.

@census none (G5 inhabitant of the relation-set argument of `RQ2-1.19`)
-/
def gelfandRelationSet : Set (Relation gelfand) := {gelfandRelation, gelfandRelationSwap}

/-- **The `±`-swap permutes the Gelfand relation set.**  This is the whole content of the
`RelationsCompat` condition (`RQ2-1.19`) for `ex:gelfand` at the level of `Aut(Γ)`; a probe has only
to compose it with `gelfandOfCardTwo_rho_apply`.

@census none (helper for `RQ2-1.19`: `RelationsCompat` evidence for `ex:gelfand`)
-/
theorem onRelation_gelfandSwap_image :
    (fun r => Aut.onRelation gelfandSwap r) '' gelfandRelationSet = gelfandRelationSet := by
  ext r
  simp only [gelfandRelationSet, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨s, (rfl | rfl), rfl⟩
    · exact Or.inr onRelation_gelfandSwap
    · exact Or.inl onRelation_gelfandSwap_swap
  · rintro (rfl | rfl)
    · exact ⟨gelfandRelationSwap, Or.inr rfl, onRelation_gelfandSwap_swap⟩
    · exact ⟨gelfandRelation, Or.inl rfl, onRelation_gelfandSwap⟩

end RQuiver

/-- A group of order two acts through any chosen involution. Used to turn the `±`-swap of
`ex:gelfand` into a rational structure over an arbitrary quadratic Galois extension.

@census none (helper for the G5 inhabitant)
-/
noncomputable def MonoidHom.ofInvolutionOfCardTwo {G H : Type*} [Group G] [Group H]
    (hG : Nat.card G = 2) (a : H) (ha : a * a = 1) : G →* H :=
  letI := Classical.decEq G
  { toFun := fun g => if g = 1 then 1 else a
    map_one' := by simp
    map_mul' := by
      obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : G)).mp hG
      have hzz : z * z = 1 := by
        have h2 := pow_card_eq_one' (G := G) (x := z)
        rwa [hG, pow_two] at h2
      intro x y
      by_cases hx : x = 1
      · subst hx; simp
      by_cases hy : y = 1
      · subst hy; simp
      have hxz : x = z := huniq x hx
      have hyz : y = z := huniq y hy
      have hxy : x * y = 1 := by rw [hxz, hyz]; exact hzz
      rw [if_pos hxy, if_neg hx, if_neg hy, ha] }

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]

namespace RationalQuiver

/-- The **split** (constant) rational structure on any classical quiver: `ρ = 1`. This is the
*degenerate* inhabitant; G5.2 additionally requires a non-degenerate one, supplied by
`gelfandOfCardTwo`.

@census none (G5 inhabitant of `RationalQuiver`; inhabitant of `IsSplit`)
-/
def split (Γ : RQuiver.{0}) : RationalQuiver K L where
  toRQuiver := Γ
  ρ := 1
  smooth_V := by
    intro v
    have h : {σ : Gal(L/K) | (((RQuiver.Aut.toPermV Γ).comp 1) σ) v = v} = Set.univ := by
      ext σ; simp
    rw [h]; exact isOpen_univ
  smooth_E := by
    intro e
    have h : {σ : Gal(L/K) | (((RQuiver.Aut.toPermE Γ).comp 1) σ) e = e} = Set.univ := by
      ext σ; simp
    rw [h]; exact isOpen_univ

/-- The split rational structure is split: an inhabitant witnessing that `IsSplit` is not empty.

@census none (G5 inhabitant of `IsSplit`)
-/
theorem split_isSplit (Γ : RQuiver.{0}) : (split K L Γ).IsSplit := rfl

/-- **`ex:gelfand`.** The `ℚ`-rational Gelfand quiver: the Gelfand quiver `Q_Gelfand` with the
non-trivial element `c` of a quadratic Galois group acting by the `±`-swap,
`c(±) = ∓`, `c(⋆) = ⋆`, `c(a_±) = a_∓`, `c(b_±) = b_∓`. This is the **non-degenerate** G5.2
inhabitant of `RationalQuiver`: by `gelfandSwap_ne_one` its rational structure is not trivial, so
it is not split. Continuity is vacuous because `L/K` is finite: mathlib's
`krullTopology_discreteTopology_of_finiteDimensional` makes `Gal(L/K)` discrete, which is exactly
the source's "for finite `L/K` this is no condition" (`census/NOTATION.md` §3).

@census none (G5.2 non-degenerate inhabitant of `RationalQuiver`; `ex:gelfand`, consumed by S8)
-/
noncomputable def gelfandOfCardTwo [FiniteDimensional K L] (h : Nat.card Gal(L/K) = 2) :
    RationalQuiver K L where
  toRQuiver := RQuiver.gelfand
  ρ := MonoidHom.ofInvolutionOfCardTwo h RQuiver.gelfandSwap RQuiver.gelfandSwap_mul_self
  smooth_V := IsSmooth.of_discreteTopology _
  smooth_E := IsSmooth.of_discreteTopology _

/-- The rational structure of `gelfandOfCardTwo` sends the non-trivial element of the order-two
Galois group to the `±`-swap.  (The `if` of `MonoidHom.ofInvolutionOfCardTwo`, evaluated.)

@census none (helper for the G5.2 non-degeneracy proof)
-/
theorem gelfandOfCardTwo_rho_apply [FiniteDimensional K L] (h : Nat.card Gal(L/K) = 2)
    {z : Gal(L/K)} (hz : z ≠ 1) : (gelfandOfCardTwo K L h).ρ z = RQuiver.gelfandSwap := by
  letI := Classical.decEq Gal(L/K)
  have hr : (gelfandOfCardTwo K L h).ρ z = if z = 1 then 1 else RQuiver.gelfandSwap := rfl
  rw [hr, if_neg hz]

/-- **G5 non-degeneracy** (S1 `G4-VERIFICATION.md` §7 probe **P1**): the `ℚ`-rational Gelfand
quiver is **not split**, `ρ ≠ 1`.  This is the step the tree was missing: `gelfandSwap_ne_one` is
a fact about `Aut Γ`, and turning it into `ρ ≠ 1` needs the *second* element of the order-two
Galois group, supplied here by `Nat.card_eq_two_iff'`.

@census none (G5.2: the non-degenerate inhabitant is proved non-degenerate)
-/
theorem gelfandOfCardTwo_not_isSplit [FiniteDimensional K L] (h : Nat.card Gal(L/K) = 2) :
    ¬ (gelfandOfCardTwo K L h).IsSplit := by
  obtain ⟨z, hz, -⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
  intro hsplit
  refine RQuiver.gelfandSwap_ne_one ?_
  rw [← gelfandOfCardTwo_rho_apply K L h hz, show (gelfandOfCardTwo K L h).ρ = 1 from hsplit]
  rfl

/-- **G5 non-degeneracy** (probe **P1**, vertex half): the Galois action on the vertices of the
`ℚ`-rational Gelfand quiver genuinely moves a vertex — `σ • (−) = (+)` for `σ ≠ 1`.

@census none (G5.2 non-degeneracy witness)
-/
theorem gelfandOfCardTwo_exists_smul_ne_self_V [FiniteDimensional K L]
    (h : Nat.card Gal(L/K) = 2) :
    ∃ (σ : Gal(L/K)) (v : (gelfandOfCardTwo K L h).V), σ • v ≠ v := by
  obtain ⟨z, hz, -⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
  refine ⟨z, show (gelfandOfCardTwo K L h).V from (0 : Fin 3), ?_⟩
  have hs : (z • (show (gelfandOfCardTwo K L h).V from (0 : Fin 3)))
      = (RQuiver.Aut.toPermV RQuiver.gelfand) ((gelfandOfCardTwo K L h).ρ z) 0 := rfl
  rw [hs, gelfandOfCardTwo_rho_apply K L h hz, RQuiver.toPermV_gelfandSwap_zero]
  exact (by decide : (2 : Fin 3) ≠ (0 : Fin 3))

/-- **G5 non-degeneracy** (probe **P1**, edge half): the Galois action on the edges genuinely
moves an edge — `σ • a₋ = a₊` for `σ ≠ 1`.

@census none (G5.2 non-degeneracy witness)
-/
theorem gelfandOfCardTwo_exists_smul_ne_self_E [FiniteDimensional K L]
    (h : Nat.card Gal(L/K) = 2) :
    ∃ (σ : Gal(L/K)) (e : (gelfandOfCardTwo K L h).E), σ • e ≠ e := by
  obtain ⟨z, hz, -⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
  refine ⟨z, show (gelfandOfCardTwo K L h).E from (0 : Fin 4), ?_⟩
  have hs : (z • (show (gelfandOfCardTwo K L h).E from (0 : Fin 4)))
      = (RQuiver.Aut.toPermE RQuiver.gelfand) ((gelfandOfCardTwo K L h).ρ z) 0 := rfl
  rw [hs, gelfandOfCardTwo_rho_apply K L h hz, RQuiver.toPermE_gelfandSwap_zero]
  exact (by decide : (2 : Fin 4) ≠ (0 : Fin 4))

end RationalQuiver

section ComplexReal

/-!
### The concrete quadratic extension `ℂ/ℝ` (G5, S1 probe **P2**)

`gelfandOfCardTwo` is a *family* indexed by a hypothesis, `Nat.card Gal(L/K) = 2`; until that
hypothesis is discharged at a concrete `(K, L)` the family could be empty and the non-degeneracy
proofs above vacuous.  This section discharges it.
-/

/-- `ℂ/ℝ` is a Galois extension.  Not registered as an instance: it is `IsAlgClosure.isGalois`
applied to `IsAlgClosure ℝ ℂ`, which mathlib does not itself register (it registers only
`IsAlgClosed.instIsAlgClosure F F`), and adding a global instance for mathlib's own types is
outside this file's remit (`CONVENTIONS.md` §5).  Use it with `haveI`.

@census none (G5 witness: concrete instantiation, S1 probe P2)
-/
theorem isGalois_real_complex : IsGalois ℝ ℂ :=
  haveI : IsAlgClosure ℝ ℂ := ⟨inferInstance, inferInstance⟩
  inferInstance

/-- `#Gal(ℂ/ℝ) = 2`: the concrete quadratic Galois group the source offers as an alternative to
`Gal(ℚ[√-1]/ℚ)`.  Discharges the hypothesis of `gelfandOfCardTwo` (S1 probe **P2**).

@census none (G5 witness: concrete instantiation, S1 probe P2)
-/
theorem card_gal_complex_real : Nat.card Gal(ℂ/ℝ) = 2 := by
  haveI := isGalois_real_complex
  rw [IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex]

/-- **`ex:gelfand` over `ℝ`**: the Gelfand quiver with `Gal(ℂ/ℝ) = ⟨complex conjugation⟩` acting
by the `±`-swap.  An *unconditional* non-degenerate inhabitant of `RationalQuiver`.

@census none (G5.2 non-degenerate inhabitant, instantiated)
-/
noncomputable def gelfandComplexReal : RationalQuiver ℝ ℂ :=
  haveI := isGalois_real_complex
  RationalQuiver.gelfandOfCardTwo ℝ ℂ card_gal_complex_real

/-- **G5 non-degeneracy, unconditionally**: `gelfandComplexReal` is not split.  Together with
`RationalQuiver.split_isSplit` this shows `IsSplit` separates two genuinely different rational
structures on the same classical quiver, which is what `WORKFLOW.md` G5.3 asks of the definition.

@census none (G5.2/G5.3 witness: probes P1 + P2 combined)
-/
theorem gelfandComplexReal_not_isSplit : ¬ gelfandComplexReal.IsSplit :=
  haveI := isGalois_real_complex
  RationalQuiver.gelfandOfCardTwo_not_isSplit ℝ ℂ card_gal_complex_real

/-- **G5 non-degeneracy, unconditionally** (vertex half of probe **P1**): complex conjugation
moves the vertex `−` of `gelfandComplexReal` to `+`.

@census none (G5.2 witness)
-/
theorem gelfandComplexReal_exists_smul_ne_self_V :
    ∃ (σ : Gal(ℂ/ℝ)) (v : gelfandComplexReal.V), σ • v ≠ v :=
  haveI := isGalois_real_complex
  RationalQuiver.gelfandOfCardTwo_exists_smul_ne_self_V ℝ ℂ card_gal_complex_real

/-- **G5 non-degeneracy, unconditionally** (edge half of probe **P1**): complex conjugation moves
the edge `a₋` of `gelfandComplexReal` to `a₊`.

@census none (G5.2 witness)
-/
theorem gelfandComplexReal_exists_smul_ne_self_E :
    ∃ (σ : Gal(ℂ/ℝ)) (e : gelfandComplexReal.E), σ • e ≠ e :=
  haveI := isGalois_real_complex
  RationalQuiver.gelfandOfCardTwo_exists_smul_ne_self_E ℝ ℂ card_gal_complex_real

open RationalQuiver

/-- **P6 (`RQ2-1.23` non-triviality).** Carrying the non-split `ex:gelfand` model through
`diagramEquiv` and back returns a non-split rational quiver — i.e. the equivalence of `RQ2-1.23`
does not quietly forget the Galois action, which is the one way an "equivalence" between the two
presentations could be vacuous.

Relocated **verbatim** from `RationalQuivers/Meta/Vacuity.lean` §3.1, where it was parked pending
this move (coordinator ruling, 2026-08-30); only the `open RationalQuiver` above is new, standing
in for that file's section-level `open RationalQuivers.RationalQuiver`.  It is a **witness**, not a probe: G5
witnesses are implementer-side content, and `rqaudit models` counts nothing in the `Meta.Vacuity`
namespace, so it did no work where it sat.  `Meta/Vacuity.lean` now cites this declaration instead
of carrying a copy.

@census none (G5.2/G5.3 witness: S1 G4 probe P6, `RQ2-1.23`)
-/
theorem diagramEquiv_symm_not_isSplit :
    letI := RationalQuivers.isGalois_real_complex
    ¬ ((diagramEquiv ℝ ℂ).symm ((diagramEquiv ℝ ℂ) RationalQuivers.gelfandComplexReal)).IsSplit := by
  letI := RationalQuivers.isGalois_real_complex
  rw [Equiv.symm_apply_apply]
  exact RationalQuivers.gelfandComplexReal_not_isSplit

end ComplexReal

/-! ## G5 witnesses for the four S1 structures the G8 cross-model review found uncovered

**Provenance.** `workflow/audit/M1/FINAL_AUDIT.md` §11.7, findings **F-M1-R-2** and **F-M1-R-8**
(cross-model review, 2026-09-02): four structures introduced by stage S1 — `RQuiver.Hom`,
`RationalQuiver.Hom`, `GaloisSet`, `GaloisSetDiagram` — had **no G5 item-(3) all-trivial entry
anywhere**, and `GaloisSet` had no item-(1) inhabitant of any kind (`rqaudit models` credited it
to the two elaborator-generated field projections `GaloisSetDiagram.vertices`/`.edges`, which is
the instrument hole F-M1-R-3 reports).  F-M1-R-8 adds that **no concrete non-identity morphism of
rational quivers** existed in the tree at all: the only closed inhabitants of
`RationalQuiver.Hom` were `Hom.id` and `Hom.comp`, everything else being parametric in an
arbitrary given morphism.  Landed by commission **C-M1-1**, 2026-09-02, as a dated `WORKFLOW.md`
F5 amendment of frozen stage S1; no S1 statement changed.

**Where these live and why.**  A G5.2 non-degenerate witness is implementer-side *content*
(`Meta/Vacuity.lean`'s own scope note, and the §3.1 precedent that relocated probe P6 out of that
file), so both the witnesses and the all-trivial probes they are separated from sit here, beside
the models they are built on.  The `Meta/Vacuity.lean` registry entries that cite them are owed to
the **instrument owner** (F3: this commission may not edit `Meta/`).

**How to read a probe.**  A probe that compiles is a *finding*, not a success: it records that the
definition alone does not exclude the degenerate model.  The judgement is written next to it.
-/

section CarriedG5

namespace RQuiver

/-- **G5.2 (`RQuiver.Hom`): a concrete non-identity endomorphism.**  The `±`-swap `c` of
`ex:gelfand`, as a morphism of classical quivers in its own right rather than as the `hom`
projection of the automorphism `gelfandSwap`.  Written out so that the declaration's *type* is
`RQuiver.Hom`, which is what a G5 inhabitant has to be (`FINAL_AUDIT.md` §11.7/F-M1-R-3: an
elaborator-generated projection is not an inhabitant).

@census none (G5.2 non-degenerate inhabitant of `RQuiver.Hom`)
-/
def gelfandSwapHom : RQuiver.Hom gelfand gelfand where
  onV := gelfandVertexSwap
  onE := gelfandEdgeSwap
  onV_source := by decide
  onV_target := by decide

/-- **G5.2 non-degeneracy**: the swap morphism is **not** the identity of `Q_Gelfand`, so
`RQuiver.Hom` is inhabited by something other than `Hom.id`/`Hom.comp`.

@census none (G5.2 non-degeneracy witness for `RQuiver.Hom`)
-/
theorem gelfandSwapHom_ne_id : gelfandSwapHom ≠ 𝟙 gelfand := by
  intro h
  have : gelfandSwapHom.onV 0 = (𝟙 gelfand : RQuiver.Hom gelfand gelfand).onV 0 := by rw [h]
  revert this
  decide

/-- **G5.2 (`RQuiver.Hom`): a concrete morphism between two *different* quivers.**  The cyclic
quiver of `ex:cyclic` sits inside the Gelfand quiver of `ex:gelfand` as its `−` half:
`− ↦ −`, `⋆ ↦ ⋆`, `a ↦ a₋`, `b ↦ b₋`.  This exhibits a `RQuiver.Hom` that is neither an
endomorphism nor an isomorphism, so the hom-sets of `RQuiver` are not merely automorphism groups.

@census none (G5.2 non-degenerate inhabitant of `RQuiver.Hom`)
-/
def cyclicToGelfand : RQuiver.Hom cyclic gelfand where
  onV := ![0, 1]
  onE := ![0, 1]
  onV_source := by decide
  onV_target := by decide

/-- **G5.2 non-degeneracy**: the embedding of `ex:cyclic` into `ex:gelfand` is injective on
vertices …

@census none (G5.2 non-degeneracy witness for `RQuiver.Hom`)
-/
theorem cyclicToGelfand_onV_injective : Function.Injective cyclicToGelfand.onV := by decide

/-- … and **not** surjective (the vertex `+` is missed), so it is a proper embedding and not an
isomorphism in disguise.

@census none (G5.2 non-degeneracy witness for `RQuiver.Hom`)
-/
theorem cyclicToGelfand_onV_not_surjective : ¬ Function.Surjective cyclicToGelfand.onV := by
  intro h
  obtain ⟨x, hx⟩ := h 2
  revert hx
  revert x
  decide

/-- **G5.3 probe (`RQuiver.Hom`): the all-trivial interpretation.**  Every classical quiver maps to
the one-vertex one-loop quiver by the total collapse `V → 1`, `E → 1`; the two compatibility
fields are discharged by `Subsingleton` alone.

**It type-checks.**  So `RQuiver.Hom`'s fields do not by themselves exclude the degenerate model
in which a morphism forgets all of the quiver's shape.

*Verdict: expected, and not a defect.*  `Hom` is the hom-set of a category of quivers, and a
category of quivers in which the terminal object had no morphisms into it would be the surprising
thing (`oneLoop` **is** terminal in `RQuiver`).  What the probe establishes is the negative half
G5.3 asks to be recorded: nothing in `Hom`'s fields is non-vacuous by construction, so every
non-degeneracy claim about a morphism of quivers has to come from an inhabitant — and it does,
`gelfandSwapHom` (non-identity) and `cyclicToGelfand` (a proper embedding) above.

@census none (G5.3 all-trivial probe for `RQuiver.Hom`)
-/
def toOneLoop (Γ : RQuiver.{0}) : RQuiver.Hom Γ oneLoop where
  onV := fun _ => 0
  onE := fun _ => 0
  onV_source := fun _ => Subsingleton.elim _ _
  onV_target := fun _ => Subsingleton.elim _ _

/-- The `±`-swap commutes with itself on vertices.  Stated over `gelfand.V` (which is
`@[reducible]`, hence `Fin 3` to `decide`) so that the equivariance of
`gelfandComplexRealSwapHom` is a `decide` on the model rather than on an opaque projection.

@census none (helper for the `RationalQuiver.Hom` witness)
-/
theorem toPermV_gelfandSwap_comm (v : gelfand.V) :
    gelfandSwap.hom.onV ((Aut.toPermV gelfand gelfandSwap) v)
      = (Aut.toPermV gelfand gelfandSwap) (gelfandSwap.hom.onV v) := by
  revert v; decide

/-- The `±`-swap commutes with itself on edges.

@census none (helper for the `RationalQuiver.Hom` witness)
-/
theorem toPermE_gelfandSwap_comm (e : gelfand.E) :
    gelfandSwap.hom.onE ((Aut.toPermE gelfand gelfandSwap) e)
      = (Aut.toPermE gelfand gelfandSwap) (gelfandSwap.hom.onE e) := by
  revert e; decide

end RQuiver

/-- **G5.2 (`RationalQuiver.Hom`, census `RQ2-1.04`): the first concrete non-identity morphism of
`K`-rational quivers in the tree** (finding **F-M1-R-8**).  The `±`-swap `c` is itself
`Gal(ℂ/ℝ)`-equivariant for the `ex:gelfand` rational structure — the rational structure *is* the
swap — so it is a morphism `gelfandComplexReal ⟶ gelfandComplexReal` over a **non-split** object,
which is what makes the two `equivariant_*` fields do real work: they are discharged at a `σ` for
which `ρ σ ≠ 1`, not vacuously at `ρ = 1`.

@census none (G5.2 non-degenerate inhabitant of `RQ2-1.04`'s `RationalQuiver.Hom`)
-/
noncomputable def gelfandComplexRealSwapHom :
    RationalQuiver.Hom gelfandComplexReal gelfandComplexReal :=
  haveI := isGalois_real_complex
  { toRQuiverHom := RQuiver.gelfandSwap.hom
    equivariant_V := by
      intro σ v
      show RQuiver.gelfandSwap.hom.onV
          ((RQuiver.Aut.toPermV RQuiver.gelfand) (gelfandComplexReal.ρ σ) v)
        = (RQuiver.Aut.toPermV RQuiver.gelfand) (gelfandComplexReal.ρ σ)
            (RQuiver.gelfandSwap.hom.onV v)
      by_cases hσ : σ = 1
      · subst hσ
        rw [show gelfandComplexReal.ρ 1 = 1 from map_one _]
        rfl
      · rw [show gelfandComplexReal.ρ σ = RQuiver.gelfandSwap from
          RationalQuiver.gelfandOfCardTwo_rho_apply ℝ ℂ card_gal_complex_real hσ]
        exact RQuiver.toPermV_gelfandSwap_comm v
    equivariant_E := by
      intro σ e
      show RQuiver.gelfandSwap.hom.onE
          ((RQuiver.Aut.toPermE RQuiver.gelfand) (gelfandComplexReal.ρ σ) e)
        = (RQuiver.Aut.toPermE RQuiver.gelfand) (gelfandComplexReal.ρ σ)
            (RQuiver.gelfandSwap.hom.onE e)
      by_cases hσ : σ = 1
      · subst hσ
        rw [show gelfandComplexReal.ρ 1 = 1 from map_one _]
        rfl
      · rw [show gelfandComplexReal.ρ σ = RQuiver.gelfandSwap from
          RationalQuiver.gelfandOfCardTwo_rho_apply ℝ ℂ card_gal_complex_real hσ]
        exact RQuiver.toPermE_gelfandSwap_comm e }

/-- The swap morphism moves the vertex `−` to `+`.

@census none (helper: the computational core of the non-degeneracy proof)
-/
theorem gelfandComplexRealSwapHom_onV_zero :
    gelfandComplexRealSwapHom.toRQuiverHom.onV (0 : RQuiver.gelfand.V)
      = (2 : RQuiver.gelfand.V) := by
  show RQuiver.gelfandSwap.hom.onV (0 : RQuiver.gelfand.V) = (2 : RQuiver.gelfand.V)
  decide

/-- **G5.2 non-degeneracy** (`RQ2-1.04`): the swap morphism is not the identity of
`gelfandComplexReal`.  Together with `gelfandComplexRealSwapHom` this closes F-M1-R-8's first gap:
`RationalQuiver.Hom` now has a closed inhabitant that is neither `Hom.id` nor a `Hom.comp` of
identities, on the source's own example.

@census none (G5.2 non-degeneracy witness for `RQ2-1.04`)
-/
theorem gelfandComplexRealSwapHom_ne_id :
    gelfandComplexRealSwapHom ≠ RationalQuiver.Hom.id gelfandComplexReal := by
  intro h
  have h0 := gelfandComplexRealSwapHom_onV_zero
  rw [h] at h0
  revert h0
  show ¬ ((0 : RQuiver.gelfand.V) = (2 : RQuiver.gelfand.V))
  decide

/-- **P4 (relations non-degeneracy, `RQ2-1.19`).** The `ex:gelfand` rational structure over `ℂ/ℝ`
*respects* the Gelfand relation set: every `σ ∈ Gal(ℂ/ℝ)` permutes `{a₋b₋ = a₊b₊}` (in both
orderings). This is the composition content's `onRelation_gelfandSwap_image` docstring invites,
and it is what makes `RelationsCompat` non-vacuous on the paper's own example.

Two cases. The `σ = 1` case is one line via `RQuiver.Aut.onRelation_one`/`…_one_eq_id` (path
induction over the identity prefunctor). The two-element set is forced, not a modelling choice:
`Relation` is an *ordered* pair of paths and the `±`-swap transposes it, so no one-element set of
relations is stable (author's note on the content lemmas).

**Relocated from `Meta/Vacuity.lean` §3.2, 2026-09-05 (`G3(instrument, commission 7)`,
`workflow/ledger/OBLIGATIONS.md` C-M1-1 "Owed to the instrument owner" item 5) — statement and
proof unchanged, placed here rather than literally "beside `gelfandRelationSet`" because
`gelfandComplexReal` (this theorem's subject) is not yet declared at that point in the file
(`gelfandRelationSet` lives inside `namespace RQuiver`, which closes before `gelfandComplexReal` is
defined); same precedent as §3.1's P6 relocation.

@census none (G5.2 non-degeneracy witness for `RQ2-1.19`, probe P4)
-/
theorem gelfandComplexReal_relationsCompat :
    letI := isGalois_real_complex
    gelfandComplexReal.RelationsCompat RQuiver.gelfandRelationSet := by
  letI := isGalois_real_complex
  intro σ
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, RQuiver.Aut.onRelation_one_eq_id]
    exact Set.image_id _
  · rw [show gelfandComplexReal.ρ σ = RQuiver.gelfandSwap from
      RationalQuiver.gelfandOfCardTwo_rho_apply ℝ ℂ card_gal_complex_real hσ]
    exact RQuiver.onRelation_gelfandSwap_image

/-- **G5.3 probe (`RationalQuiver.Hom`): the all-trivial interpretation.**  Over the *split*
rational structures (`ρ = 1`) the two `equivariant_*` fields are satisfied by any morphism of the
underlying classical quivers whatsoever — here the total collapse of `Q_Gelfand` onto the
one-vertex one-loop quiver.

**It type-checks.**  So `RationalQuiver.Hom`'s equivariance fields are vacuous on split objects,
and `Hom(Γ_K, Γ'_K)` for split `Γ_K, Γ'_K` is exactly the classical hom-set.

*Verdict: expected, and not a defect* — it is `def:splitrationalquivers`'s whole point that a split
`K`-rational quiver *is* a classical quiver, and `RationalQuiver.split_isSplit` records the same
fact on objects.  What it establishes is that the equivariance fields can only be exercised by a
**non-split** witness, which is what `gelfandComplexRealSwapHom` above is.

@census none (G5.3 all-trivial probe for `RQ2-1.04`)
-/
def splitCollapseHom :
    RationalQuiver.Hom (RationalQuiver.split K L RQuiver.gelfand)
      (RationalQuiver.split K L RQuiver.oneLoop) where
  toRQuiverHom := RQuiver.toOneLoop RQuiver.gelfand
  equivariant_V _ _ := Subsingleton.elim (α := Fin 1) _ _
  equivariant_E _ _ := Subsingleton.elim (α := Fin 1) _ _

/-- **G5.1/G5.2 (`GaloisSet`): the first inhabitant of `GaloisSet` in the tree** (finding
**F-M1-R-2**; before this the only occurrences of the type in `lean/` were as the two fields of
`GaloisSetDiagram`, which `rqaudit models` wrongly credited as inhabitants — F-M1-R-3).  The
vertex set of the `ex:gelfand` model over `ℂ/ℝ`, with its `Gal(ℂ/ℝ)`-action.

@census none (G5.1/G5.2 inhabitant of `GaloisSet`)
-/
noncomputable def gelfandVertexGaloisSet : GaloisSet ℝ ℂ where
  galois := isGalois_real_complex
  carrier := RQuiver.gelfand.V
  finite := inferInstance
  act := (RQuiver.Aut.toPermV RQuiver.gelfand).comp gelfandComplexReal.ρ
  smooth := gelfandComplexReal.smooth_V

/-- The edge set of the same model, as a `GaloisSet`.

@census none (G5.1/G5.2 inhabitant of `GaloisSet`)
-/
noncomputable def gelfandEdgeGaloisSet : GaloisSet ℝ ℂ where
  galois := isGalois_real_complex
  carrier := RQuiver.gelfand.E
  finite := inferInstance
  act := (RQuiver.Aut.toPermE RQuiver.gelfand).comp gelfandComplexReal.ρ
  smooth := gelfandComplexReal.smooth_E

/-- **G5.2 non-degeneracy** (`GaloisSet`, first criterion): the carrier is **non-empty** — three
points, the vertices of `Q_Gelfand`.  A `GaloisSet` with empty carrier would satisfy every field
vacuously.

@census none (G5.2 non-degeneracy witness for `GaloisSet`)
-/
theorem gelfandVertexGaloisSet_card : Nat.card gelfandVertexGaloisSet.carrier = 3 := by
  show Nat.card (Fin 3) = 3
  simp

/-- **G5.2 non-degeneracy** (`GaloisSet`, second criterion): the action is **not trivial** —
complex conjugation moves the vertex `−` to `+`.  This is the field `act` doing work: a `GaloisSet`
whose only inhabitants had `act = 1` would not distinguish the category of `Gal(L/K)`-sets from the
category of finite sets, which is exactly the collapse `RQ2-1.23`'s reformulation must avoid.

@census none (G5.2 non-degeneracy witness for `GaloisSet`)
-/
theorem gelfandVertexGaloisSet_act_ne_id :
    ∃ (σ : Gal(ℂ/ℝ)) (x : gelfandVertexGaloisSet.carrier),
      gelfandVertexGaloisSet.act σ x ≠ x :=
  gelfandComplexReal_exists_smul_ne_self_V

/-- The same on edges.

@census none (G5.2 non-degeneracy witness for `GaloisSet`)
-/
theorem gelfandEdgeGaloisSet_act_ne_id :
    ∃ (σ : Gal(ℂ/ℝ)) (x : gelfandEdgeGaloisSet.carrier),
      gelfandEdgeGaloisSet.act σ x ≠ x :=
  gelfandComplexReal_exists_smul_ne_self_E

/-- **G5.3 probe (`GaloisSet`): the all-trivial interpretation.**  One point, trivial action,
smoothness by `Subsingleton`.

**It type-checks.**  So `GaloisSet` alone does not exclude the degenerate model — as it should
not: it is the object type of a category of finite continuous `Gal(L/K)`-sets, and the one-point
set is its terminal object.  What the probe records is that the *pair*
(`trivialGaloisSet`, `gelfandVertexGaloisSet`) separates a trivial action from a non-trivial one
inside one and the same definition, which is the content `RQ2-1.23` needs.

@census none (G5.3 all-trivial probe for `GaloisSet`)
-/
noncomputable def trivialGaloisSet : GaloisSet ℝ ℂ where
  galois := isGalois_real_complex
  carrier := PUnit
  finite := inferInstance
  act := 1
  smooth := fun _ => by
    convert isOpen_univ
    ext σ
    simp

/-- **G5.1/G5.2 (`GaloisSetDiagram`): a user-written inhabitant** (finding **F-M1-R-2**).  The
`ex:gelfand` model read as the diagram `E ⇉ V` of finite continuous `Gal(ℂ/ℝ)`-sets that
`RQ2-1.23` says a `K`-rational quiver *is*.  Written out from the two `GaloisSet`s above rather
than obtained as `toDiagram gelfandComplexReal`, so that the declaration's type is the structure
itself; `RationalQuiver.toDiagram_bijective` says the two agree.

@census none (G5.1/G5.2 inhabitant of `GaloisSetDiagram`)
-/
noncomputable def gelfandGaloisSetDiagram : GaloisSetDiagram ℝ ℂ :=
  haveI := isGalois_real_complex
  { vertices := gelfandVertexGaloisSet
    edges := gelfandEdgeGaloisSet
    source := RQuiver.gelfand.source
    target := RQuiver.gelfand.target
    source_equivariant := fun σ e => gelfandComplexReal.source_smul σ e
    target_equivariant := fun σ e => gelfandComplexReal.target_smul σ e }

/-- **G5.2 non-degeneracy** (`GaloisSetDiagram`, first criterion): the diagram's edge action is
non-trivial, so the two `*_equivariant` fields are not vacuous.

@census none (G5.2 non-degeneracy witness for `GaloisSetDiagram`)
-/
theorem gelfandGaloisSetDiagram_edges_act_ne_id :
    ∃ (σ : Gal(ℂ/ℝ)) (x : gelfandGaloisSetDiagram.edges.carrier),
      gelfandGaloisSetDiagram.edges.act σ x ≠ x :=
  gelfandEdgeGaloisSet_act_ne_id

/-- **G5.2 non-degeneracy** (`GaloisSetDiagram`, second criterion): `s ≠ t`, so the diagram is a
genuine `E ⇉ V` and not a single map counted twice — the degenerate reading in which the two
fields carry the same datum.

@census none (G5.2 non-degeneracy witness for `GaloisSetDiagram`)
-/
theorem gelfandGaloisSetDiagram_source_ne_target :
    gelfandGaloisSetDiagram.source ≠ gelfandGaloisSetDiagram.target := by
  intro h
  have h0 : RQuiver.gelfand.source (0 : RQuiver.gelfand.E)
      = RQuiver.gelfand.target (0 : RQuiver.gelfand.E) := by
    exact congrFun h (0 : RQuiver.gelfand.E)
  revert h0
  decide

/-- **G5.3 probe (`GaloisSetDiagram`): the all-trivial interpretation.**  One vertex, one edge,
trivial action, `s = t`.

**It type-checks.**  So `GaloisSetDiagram` does not exclude the degenerate model, and the
bijection `RQ2-1.23` asserts is a bijection between two types both of which contain a degenerate
point — which is precisely why `diagramEquiv_symm_not_isSplit` (probe **P6**) is needed: it shows
the bijection does not send the *non*-degenerate model to a degenerate one.

@census none (G5.3 all-trivial probe for `GaloisSetDiagram`)
-/
noncomputable def trivialGaloisSetDiagram : GaloisSetDiagram ℝ ℂ where
  vertices := trivialGaloisSet
  edges := trivialGaloisSet
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  source_equivariant := fun _ _ => rfl
  target_equivariant := fun _ _ => rfl

end CarriedG5

end RationalQuivers
