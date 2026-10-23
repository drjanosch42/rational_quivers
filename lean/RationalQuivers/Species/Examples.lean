import RationalQuivers.Species.OfQuiver
import RationalQuivers.Species.Hom
import RationalQuivers.Quiver.Models
import RationalQuivers.Quiver.Restriction
import RationalQuivers.Quiver.BaseChange
import RationalQuivers.Quiver.Relations

/-!
# The three worked examples of §2.4

Formalizes `ex:twoloops` and `ex:cyclic` (census `RQ2-2.14`, `RQ2-2.15`). Stage **S4**.
`ex:gelfand` (census `RQ2-2.16`) was **re-sequenced to stage S5** by coordinator ruling of
2026-08-30; see the section note below.

## Main definitions / results
* `RationalQuivers.RQuiver.twoLoopsSwap`, `.cyclicSwap` — the `±`-swap on the two-loop and the
  cyclic quiver (`RQuiver.gelfandSwap` is stage S1's).
* `RationalQuivers.RationalQuiver.twoLoopsOfCardTwo`, `.cyclicOfCardTwo` — the two quivers with
  their rational structure; `ex:gelfand`'s quiver is stage S1's `gelfandOfCardTwo`, reused
  unchanged (S8 consumes it).
* `RationalQuivers.Examples.twoLoops_species`, `.cyclic_species` — census `RQ2-2.14`, `RQ2-2.15`.
  `RQ2-2.16` (`ex:gelfand`) is **stage S5's**, re-sequenced; see the section note below.
* `RationalQuivers.Examples.PrintedHom`, `.printedHom_isEmpty_of_gelfand_to_point`,
  `.printedHom_onI_not_unique` — the two witnesses for finding **S4-F1**, the permanent
  justification for the amended morphism direction of `RQ2-2.04` (`Species/Hom.lean`).
* `RationalQuivers.Examples.twoLoops_baseChange_offDiagonal_subsingleton` — the second
  counterexample of stage S3's finding **S3-F2**, handed over in `stages/S3/DESIGN-NOTES.md` §2 and
  `ledger/MATHLIB-DECISIONS.tsv` `MD-S3-08`: it needs `S(−)`, which is `RQ2-2.09`, an S4 row.

## Implementation notes

**Which quadratic extension.** The census rows say `G = Gal(ℚ[√-1]/ℚ)`; the source's own §2.4
preamble says in the same breath "but one may also choose `G = Gal(ℂ/ℝ)` or **any other quadratic
extension `L/K` for that matter**". We state the three examples for an arbitrary quadratic Galois
extension — `[IsGalois K L]`, `[FiniteDimensional K L]`, `Nat.card Gal(L/K) = 2` — which is the
generality the source licenses and which stage S1 already used for `gelfandOfCardTwo`; `ℂ/ℝ` is the
concrete inhabitant in the tree (`RationalQuivers.card_gal_complex_real`). See the `@divergence`
fields, and `ledger/MATHLIB-DECISIONS.tsv` `MD-S4-03` for why `ℚ[√-1]` itself is not the
instantiation used at this mathlib pin.

**Why the statements are stable under the choice of orbit representatives.** `L_i` is
`stabField` at `Quotient.out i`, a *chosen* representative, so a statement naming a particular
vertex would depend on that choice. Every clause below is phrased so that it does not: the vertex
fields are computed as `⊤` or `⊥` (which is representative-independent), and the twist of
`ex:cyclic` is stated as `right = c ∘ left`, which holds for *either* representative because
`c² = 1`.
-/

universe u

namespace RationalQuivers

open MulAction CategoryTheory

namespace RQuiver

/-- The `±`-swap on the two-loop quiver of `ex:twoloops`: `c(±) = ∓`, `c(a_±) = a_∓`.

@census none (clause witness for `RQ2-2.14-C2`)
-/
@[reducible] def twoLoopsSwapPerm : Equiv.Perm (Fin 2) where
  toFun := ![1, 0]
  invFun := ![1, 0]
  left_inv := by decide
  right_inv := by decide

/-- The `±`-swap of `ex:twoloops` as an automorphism of the two-loop quiver.

@census none (clause witness for `RQ2-2.14-C2`)
-/
@[reducible] def twoLoopsSwap : RQuiver.Aut twoLoops where
  hom := { onV := twoLoopsSwapPerm, onE := twoLoopsSwapPerm,
           onV_source := by decide, onV_target := by decide }
  inv := { onV := twoLoopsSwapPerm, onE := twoLoopsSwapPerm,
           onV_source := by decide, onV_target := by decide }
  hom_inv_id := by refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)
  inv_hom_id := by refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)

theorem twoLoopsSwap_mul_self : twoLoopsSwap * twoLoopsSwap = 1 := by
  refine CategoryTheory.Aut.ext ?_
  refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)

theorem twoLoopsSwap_ne_one : twoLoopsSwap ≠ 1 := by
  intro h
  have : twoLoopsSwap.hom.onV 0 = (1 : RQuiver.Aut twoLoops).hom.onV 0 := by rw [h]
  revert this; decide

/-- The action of `ex:cyclic`: `c(±) = ∓`, `c(a) = b`, `c(b) = a`, as an automorphism of the
cyclic quiver.

@census none (clause witness for `RQ2-2.15-C2`)
-/
@[reducible] def cyclicSwap : RQuiver.Aut cyclic where
  hom := { onV := twoLoopsSwapPerm, onE := twoLoopsSwapPerm,
           onV_source := by decide, onV_target := by decide }
  inv := { onV := twoLoopsSwapPerm, onE := twoLoopsSwapPerm,
           onV_source := by decide, onV_target := by decide }
  hom_inv_id := by refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)
  inv_hom_id := by refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)

theorem cyclicSwap_mul_self : cyclicSwap * cyclicSwap = 1 := by
  refine CategoryTheory.Aut.ext ?_
  refine Hom.ext ?_ ?_ <;> (funext x; revert x; decide)

theorem cyclicSwap_ne_one : cyclicSwap ≠ 1 := by
  intro h
  have : cyclicSwap.hom.onV 0 = (1 : RQuiver.Aut cyclic).hom.onV 0 := by rw [h]
  revert this; decide

end RQuiver

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

namespace RationalQuiver

/-- **`ex:twoloops`.** The disconnected two-loop quiver with the `±`-swap as its `K`-rational
structure.

@census none (clause witness for `RQ2-2.14-C1`, `RQ2-2.14-C2`)
-/
noncomputable def twoLoopsOfCardTwo (h : Nat.card Gal(L/K) = 2) : RationalQuiver K L where
  toRQuiver := RQuiver.twoLoops
  ρ := MonoidHom.ofInvolutionOfCardTwo h RQuiver.twoLoopsSwap RQuiver.twoLoopsSwap_mul_self
  smooth_V := IsSmooth.of_discreteTopology _
  smooth_E := IsSmooth.of_discreteTopology _

/-- **`ex:cyclic`.** The cyclic quiver with `c(±) = ∓`, `ca = b`, `cb = a`.

@census none (clause witness for `RQ2-2.15-C1`, `RQ2-2.15-C2`)
-/
noncomputable def cyclicOfCardTwo (h : Nat.card Gal(L/K) = 2) : RationalQuiver K L where
  toRQuiver := RQuiver.cyclic
  ρ := MonoidHom.ofInvolutionOfCardTwo h RQuiver.cyclicSwap RQuiver.cyclicSwap_mul_self
  smooth_V := IsSmooth.of_discreteTopology _
  smooth_E := IsSmooth.of_discreteTopology _

/-- The one-loop quiver, regarded as a quiver over `L` itself (`⊤ ⊆ L`) — the object whose
restriction along `L/K` `ex:twoloops` computes. Its rational structure is necessarily split, since
`Gal(L/⊤)` is trivial.

@census none (clause witness for `RQ2-2.14-C1`)
-/
noncomputable def oneLoopOverTop : RationalQuiver ↥(⊤ : IntermediateField K L) L :=
  RationalQuiver.split _ L RQuiver.oneLoop

end RationalQuiver

namespace Examples

open RationalQuiver

/-! ### `ex:twoloops` (census `RQ2-2.14`) -/

/-! ### Computations for `ex:twoloops` and `ex:cyclic`

Both quivers carry the same underlying `Gal(L/K)`-set data: `V = E = Fin 2` with the non-trivial
element acting by the swap `![1,0]`. So the orbit and stabilizer computations are the same for the
two, and each is a two-line `decide` once `ρ z` has been evaluated (the `if` of
`MonoidHom.ofInvolutionOfCardTwo`). They differ only in `s`/`t` — equal for `ex:twoloops`, swapped
for `ex:cyclic` — which is exactly the difference between the two conclusions about the species:
the structure maps agree in the first case and differ by `c` in the second.
-/

theorem twoLoops_rho_apply (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) :
    (twoLoopsOfCardTwo K L h).ρ z = RQuiver.twoLoopsSwap := by
  letI := Classical.decEq Gal(L/K)
  have hr : (twoLoopsOfCardTwo K L h).ρ z = if z = 1 then 1 else RQuiver.twoLoopsSwap := rfl
  rw [hr, if_neg hz]

theorem twoLoops_smul_V (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (v : (twoLoopsOfCardTwo K L h).V) : z • v = RQuiver.twoLoopsSwapPerm v := by
  show (RQuiver.Aut.toPermV _ ((twoLoopsOfCardTwo K L h).ρ z)) v = _
  rw [twoLoops_rho_apply K L h hz]; rfl

theorem twoLoops_smul_E (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (e : (twoLoopsOfCardTwo K L h).E) : z • e = RQuiver.twoLoopsSwapPerm e := by
  show (RQuiver.Aut.toPermE _ ((twoLoopsOfCardTwo K L h).ρ z)) e = _
  rw [twoLoops_rho_apply K L h hz]; rfl

theorem twoLoops_orbit_V (h : Nat.card Gal(L/K) = 2) (v w : (twoLoopsOfCardTwo K L h).V) :
    w ∈ orbit Gal(L/K) v := by
  obtain ⟨z, hz, -⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
  by_cases hvw : w = v
  · subst hvw; exact mem_orbit_self w
  · refine ⟨z, ?_⟩
    show z • v = w
    rw [twoLoops_smul_V K L h hz]
    have hdec : ∀ a b : Fin 2, b ≠ a → RQuiver.twoLoopsSwapPerm a = b := by decide
    exact hdec v w hvw

theorem twoLoops_stabilizer_V (h : Nat.card Gal(L/K) = 2) (v : (twoLoopsOfCardTwo K L h).V) :
    stabilizer Gal(L/K) v = ⊥ := by
  ext σ
  simp only [Subgroup.mem_bot, mem_stabilizer_iff]
  refine ⟨fun hσ => ?_, by rintro rfl; exact one_smul _ _⟩
  by_contra hne
  rw [twoLoops_smul_V K L h hne] at hσ
  have hdec : ∀ a : Fin 2, RQuiver.twoLoopsSwapPerm a ≠ a := by decide
  exact hdec v hσ

theorem twoLoops_orbit_E (h : Nat.card Gal(L/K) = 2) (e f : (twoLoopsOfCardTwo K L h).E) :
    f ∈ orbit Gal(L/K) e := by
  obtain ⟨z, hz, -⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
  by_cases hef : f = e
  · subst hef; exact mem_orbit_self f
  · refine ⟨z, ?_⟩
    show z • e = f
    rw [twoLoops_smul_E K L h hz]
    have hdec : ∀ a b : Fin 2, b ≠ a → RQuiver.twoLoopsSwapPerm a = b := by decide
    exact hdec e f hef

theorem twoLoops_stabilizer_E (h : Nat.card Gal(L/K) = 2) (e : (twoLoopsOfCardTwo K L h).E) :
    stabilizer Gal(L/K) e = ⊥ := by
  ext σ
  simp only [Subgroup.mem_bot, mem_stabilizer_iff]
  refine ⟨fun hσ => ?_, by rintro rfl; exact one_smul _ _⟩
  by_contra hne
  rw [twoLoops_smul_E K L h hne] at hσ
  have hdec : ∀ a : Fin 2, RQuiver.twoLoopsSwapPerm a ≠ a := by decide
  exact hdec e hσ

instance twoLoops_vertexOrbit_subsingleton (h : Nat.card Gal(L/K) = 2) :
    Subsingleton (twoLoopsOfCardTwo K L h).VertexOrbit := by
  constructor
  refine Quotient.ind fun a => Quotient.ind fun b => ?_
  exact Quotient.sound (twoLoops_orbit_V K L h b a)

theorem twoLoops_vertexOrbit_card (h : Nat.card Gal(L/K) = 2) :
    Nat.card (twoLoopsOfCardTwo K L h).VertexOrbit = 1 := by
  haveI : Nonempty (twoLoopsOfCardTwo K L h).VertexOrbit :=
    ⟨(twoLoopsOfCardTwo K L h).vertexClass (0 : Fin 2)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨twoLoops_vertexOrbit_subsingleton K L h, inferInstance⟩

theorem twoLoops_vertexOrbitField (h : Nat.card Gal(L/K) = 2)
    (i : (twoLoopsOfCardTwo K L h).VertexOrbit) :
    (twoLoopsOfCardTwo K L h).vertexOrbitField i = ⊤ :=
  stabField_eq_top_of_stabilizer_eq_bot (twoLoops_stabilizer_V K L h _)

theorem twoLoops_edgeOrbitField (h : Nat.card Gal(L/K) = 2)
    {i j : (twoLoopsOfCardTwo K L h).VertexOrbit}
    (ε : (twoLoopsOfCardTwo K L h).EdgeOrbit i j) :
    (twoLoopsOfCardTwo K L h).edgeOrbitField ε = ⊤ :=
  stabField_eq_top_of_stabilizer_eq_bot (twoLoops_stabilizer_E K L h _)

theorem twoLoops_edgeComponent_heq (h : Nat.card Gal(L/K) = 2)
    (i j : (twoLoopsOfCardTwo K L h).VertexOrbit)
    (ε : (twoLoopsOfCardTwo K L h).EdgeOrbit i j) :
    HEq ((twoLoopsOfCardTwo K L h).edgeComponentLeft ε)
        ((twoLoopsOfCardTwo K L h).edgeComponentRight ε) := by
  have hij : i = j := Subsingleton.elim i j
  cases hij
  rfl

theorem cyclic_rho_apply (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) :
    (cyclicOfCardTwo K L h).ρ z = RQuiver.cyclicSwap := by
  letI := Classical.decEq Gal(L/K)
  have hr : (cyclicOfCardTwo K L h).ρ z = if z = 1 then 1 else RQuiver.cyclicSwap := rfl
  rw [hr, if_neg hz]

theorem cyclic_smul_V (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (v : (cyclicOfCardTwo K L h).V) : z • v = RQuiver.twoLoopsSwapPerm v := by
  show (RQuiver.Aut.toPermV _ ((cyclicOfCardTwo K L h).ρ z)) v = _
  rw [cyclic_rho_apply K L h hz]; rfl

theorem cyclic_smul_E (h : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (e : (cyclicOfCardTwo K L h).E) : z • e = RQuiver.twoLoopsSwapPerm e := by
  show (RQuiver.Aut.toPermE _ ((cyclicOfCardTwo K L h).ρ z)) e = _
  rw [cyclic_rho_apply K L h hz]; rfl

theorem cyclic_orbit_V (h : Nat.card Gal(L/K) = 2) (v w : (cyclicOfCardTwo K L h).V) :
    w ∈ orbit Gal(L/K) v := by
  obtain ⟨z, hz, -⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
  by_cases hvw : w = v
  · subst hvw; exact mem_orbit_self w
  · refine ⟨z, ?_⟩
    show z • v = w
    rw [cyclic_smul_V K L h hz]
    have hdec : ∀ a b : Fin 2, b ≠ a → RQuiver.twoLoopsSwapPerm a = b := by decide
    exact hdec v w hvw

theorem cyclic_orbit_E (h : Nat.card Gal(L/K) = 2) (e f : (cyclicOfCardTwo K L h).E) :
    f ∈ orbit Gal(L/K) e := by
  obtain ⟨z, hz, -⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
  by_cases hef : f = e
  · subst hef; exact mem_orbit_self f
  · refine ⟨z, ?_⟩
    show z • e = f
    rw [cyclic_smul_E K L h hz]
    have hdec : ∀ a b : Fin 2, b ≠ a → RQuiver.twoLoopsSwapPerm a = b := by decide
    exact hdec e f hef

theorem cyclic_stabilizer_V (h : Nat.card Gal(L/K) = 2) (v : (cyclicOfCardTwo K L h).V) :
    stabilizer Gal(L/K) v = ⊥ := by
  ext σ
  simp only [Subgroup.mem_bot, mem_stabilizer_iff]
  refine ⟨fun hσ => ?_, by rintro rfl; exact one_smul _ _⟩
  by_contra hne
  rw [cyclic_smul_V K L h hne] at hσ
  have hdec : ∀ a : Fin 2, RQuiver.twoLoopsSwapPerm a ≠ a := by decide
  exact hdec v hσ

theorem cyclic_stabilizer_E (h : Nat.card Gal(L/K) = 2) (e : (cyclicOfCardTwo K L h).E) :
    stabilizer Gal(L/K) e = ⊥ := by
  ext σ
  simp only [Subgroup.mem_bot, mem_stabilizer_iff]
  refine ⟨fun hσ => ?_, by rintro rfl; exact one_smul _ _⟩
  by_contra hne
  rw [cyclic_smul_E K L h hne] at hσ
  have hdec : ∀ a : Fin 2, RQuiver.twoLoopsSwapPerm a ≠ a := by decide
  exact hdec e hσ

instance cyclic_vertexOrbit_subsingleton (h : Nat.card Gal(L/K) = 2) :
    Subsingleton (cyclicOfCardTwo K L h).VertexOrbit := by
  constructor
  refine Quotient.ind fun a => Quotient.ind fun b => ?_
  exact Quotient.sound (cyclic_orbit_V K L h b a)

theorem cyclic_vertexOrbit_card (h : Nat.card Gal(L/K) = 2) :
    Nat.card (cyclicOfCardTwo K L h).VertexOrbit = 1 := by
  haveI : Nonempty (cyclicOfCardTwo K L h).VertexOrbit :=
    ⟨(cyclicOfCardTwo K L h).vertexClass (0 : Fin 2)⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨cyclic_vertexOrbit_subsingleton K L h, inferInstance⟩

theorem cyclic_edgeOrbitField (h : Nat.card Gal(L/K) = 2)
    {i j : (cyclicOfCardTwo K L h).VertexOrbit}
    (ε : (cyclicOfCardTwo K L h).EdgeOrbit i j) :
    (cyclicOfCardTwo K L h).edgeOrbitField ε = ⊤ :=
  stabField_eq_top_of_stabilizer_eq_bot (cyclic_stabilizer_E K L h _)

theorem cyclic_twist (h : Nat.card Gal(L/K) = 2) (z : Gal(L/K)) (hz : z ≠ 1)
    (i : (cyclicOfCardTwo K L h).VertexOrbit)
    (ε : (cyclicOfCardTwo K L h).EdgeOrbit i i)
    (α : (cyclicOfCardTwo K L h).vertexOrbitField i) :
    (((cyclicOfCardTwo K L h).edgeComponentRight ε α : L))
      = z (((cyclicOfCardTwo K L h).edgeComponentLeft ε α : L)) := by
  have hst : (cyclicOfCardTwo K L h).toRQuiver.target ((cyclicOfCardTwo K L h).edgeRep ε)
      = z • (cyclicOfCardTwo K L h).toRQuiver.source ((cyclicOfCardTwo K L h).edgeRep ε) := by
    rw [cyclic_smul_V K L h hz]
    have hdec : ∀ a : Fin 2, (RQuiver.cyclic.target a)
        = RQuiver.twoLoopsSwapPerm (RQuiver.cyclic.source a) := by decide
    exact hdec ((cyclicOfCardTwo K L h).edgeRep ε)
  have es := (mem_orbit_iff.mp ((cyclicOfCardTwo K L h).source_edgeRep_mem_orbit ε)).choose_spec
  have et := (mem_orbit_iff.mp ((cyclicOfCardTwo K L h).target_edgeRep_mem_orbit ε)).choose_spec
  have key : (mem_orbit_iff.mp ((cyclicOfCardTwo K L h).target_edgeRep_mem_orbit ε)).choose
        • (cyclicOfCardTwo K L h).vertexRep i
      = (z * (mem_orbit_iff.mp
          ((cyclicOfCardTwo K L h).source_edgeRep_mem_orbit ε)).choose)
        • (cyclicOfCardTwo K L h).vertexRep i := by
    rw [et, mul_smul, es, hst]
  rw [edgeComponentRight_coe, edgeComponentLeft_coe]
  simpa [AlgEquiv.mul_apply] using stabField_apply_eq_of_smul_eq key α

/-! ### `ex:twoloops`, clause `RQ2-2.14-C1`: the restriction *is* the two-loop quiver

`res_{L/K}` of the one-loop quiver over `⊤` is `Gal(L/K) ×_{Gal(L/⊤)} (Fin 1)`. `Gal(L/⊤)` is
**trivial** (an `⊤`-algebra automorphism of `L` fixes every element, `⊤` being all of `L`), so the
induced set is a copy of `Gal(L/K)` acting on itself by translation; with `|Gal(L/K)| = 2` that is
`Fin 2` with the swap, which is exactly `ex:twoloops`. The isomorphism is built explicitly below —
`indToFin2` in one direction, `fin2ToInd` in the other — because the statement asks for the
isomorphism, not merely for equal cardinalities.

Two Lean notes. (i) `indToFin2` is defined for an arbitrary `Gal(L/⊤)`-set `X`, so that the *same*
function serves for `V` and for `E`: `(oneLoopOverTop K L).V` and `.E` are both `Fin 1` but are not
the same expression, and the `MulAction` instances differ. (ii) Everything about the `Gal(L/K)`
action is routed through `twoLoopsAct`, a bare function `Fin 2 → Fin 2`, because writing
`σ • (n : Γ.V)` with an ascription unfolds `Γ.V` and loses the `MulAction` instance — the same
transparency hazard recorded in `DESIGN-NOTES.md` §12.
-/

section RestrictionIso

variable {X : Type} [MulAction Gal(L/↥(⊤ : IntermediateField K L)) X]

instance subsingleton_galTop : Subsingleton Gal(L/↥(⊤ : IntermediateField K L)) := by
  constructor
  intro σ τ
  refine AlgEquiv.ext fun x => ?_
  have hx : x = algebraMap ↥(⊤ : IntermediateField K L) L ⟨x, IntermediateField.mem_top⟩ := rfl
  rw [hx, AlgEquiv.commutes, AlgEquiv.commutes]

variable {X : Type} [MulAction Gal(L/↥(⊤ : IntermediateField K L)) X]

noncomputable def indToFin2 : InducedSet (galRestrict K L ⊤) X → Fin 2 := by
  letI := Classical.decEq Gal(L/K)
  refine Quotient.lift (fun p => if p.1 = 1 then (0 : Fin 2) else 1) ?_
  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨hh, hb⟩
  rw [Prod.mk.injEq] at hb
  obtain ⟨rfl, rfl⟩ := hb
  have hone : (galRestrict K L ⊤) hh⁻¹ = 1 := by
    rw [Subsingleton.elim hh⁻¹ (1 : Gal(L/↥(⊤ : IntermediateField K L))), map_one]
  simp [hone]

theorem indToFin2_one (x : X) : indToFin2 K L (InducedSet.mk _ 1 x) = 0 := by
  letI := Classical.decEq Gal(L/K)
  show (if (1 : Gal(L/K)) = 1 then (0 : Fin 2) else 1) = 0
  rw [if_pos rfl]

theorem indToFin2_ne {a : Gal(L/K)} (ha : a ≠ 1) (x : X) :
    indToFin2 K L (InducedSet.mk _ a x) = 1 := by
  letI := Classical.decEq Gal(L/K)
  show (if a = 1 then (0 : Fin 2) else 1) = 1
  rw [if_neg ha]

/-- The chosen non-trivial element of the order-two Galois group. -/
noncomputable def cardTwoGen (h : Nat.card Gal(L/K) = 2) : Gal(L/K) :=
  ((Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h).choose

theorem cardTwoGen_ne_one (h : Nat.card Gal(L/K) = 2) : cardTwoGen K L h ≠ 1 :=
  ((Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h).choose_spec.1

theorem eq_one_or_cardTwoGen (h : Nat.card Gal(L/K) = 2) (g : Gal(L/K)) :
    g = 1 ∨ g = cardTwoGen K L h := by
  by_cases hg : g = 1
  · exact Or.inl hg
  · exact Or.inr (((Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h).choose_spec.2 g hg)

theorem cardTwoGen_mul_self (h : Nat.card Gal(L/K) = 2) :
    cardTwoGen K L h * cardTwoGen K L h = 1 := by
  have h2 := pow_card_eq_one' (G := Gal(L/K)) (x := cardTwoGen K L h)
  rwa [h, pow_two] at h2

noncomputable def fin2ToInd (h : Nat.card Gal(L/K) = 2) (x₀ : X) :
    Fin 2 → InducedSet (galRestrict K L ⊤) X :=
  fun n => InducedSet.mk _ (if n = 0 then 1 else cardTwoGen K L h) x₀

theorem indToFin2_fin2ToInd (h : Nat.card Gal(L/K) = 2) (x₀ : X) (n : Fin 2) :
    indToFin2 K L (fin2ToInd K L h x₀ n) = n := by
  fin_cases n
  · show indToFin2 K L (InducedSet.mk _ (if (0 : Fin 2) = 0 then 1 else cardTwoGen K L h) x₀) = 0
    rw [if_pos rfl, indToFin2_one]
  · show indToFin2 K L (InducedSet.mk _ (if (1 : Fin 2) = 0 then 1 else cardTwoGen K L h) x₀) = 1
    rw [if_neg (by decide), indToFin2_ne K L (cardTwoGen_ne_one K L h)]

theorem fin2ToInd_indToFin2 [Subsingleton X] (h : Nat.card Gal(L/K) = 2) (x₀ : X)
    (q : InducedSet (galRestrict K L ⊤) X) :
    fin2ToInd K L h x₀ (indToFin2 K L q) = q := by
  refine Quotient.inductionOn q ?_
  rintro ⟨a, x⟩
  have hx : x = x₀ := Subsingleton.elim x _
  subst hx
  rcases eq_one_or_cardTwoGen K L h a with rfl | rfl
  · rw [show (Quotient.mk _ ((1 : Gal(L/K)), x))
        = InducedSet.mk (galRestrict K L ⊤) 1 x from rfl, indToFin2_one]
    show InducedSet.mk _ (if (0 : Fin 2) = 0 then 1 else cardTwoGen K L h) x = _
    rw [if_pos rfl]
  · rw [show (Quotient.mk _ ((cardTwoGen K L h), x))
        = InducedSet.mk (galRestrict K L ⊤) (cardTwoGen K L h) x from rfl,
      indToFin2_ne K L (cardTwoGen_ne_one K L h)]
    show InducedSet.mk _ (if (1 : Fin 2) = 0 then 1 else cardTwoGen K L h) x = _
    rw [if_neg (by decide)]


/-- The unique vertex of the one-loop quiver, in its own vertex type. -/
def oneLoopVertex : (oneLoopOverTop K L).V := (0 : Fin 1)

/-- The unique edge of the one-loop quiver, in its own edge type. -/
def oneLoopEdge : (oneLoopOverTop K L).E := (0 : Fin 1)

instance : Subsingleton (oneLoopOverTop K L).V := (inferInstance : Subsingleton (Fin 1))
instance : Subsingleton (oneLoopOverTop K L).E := (inferInstance : Subsingleton (Fin 1))

noncomputable def resToTwoLoopsV (h : Nat.card Gal(L/K) = 2) :
    ((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).V
      → (twoLoopsOfCardTwo K L h).V := indToFin2 K L

noncomputable def resToTwoLoopsE (h : Nat.card Gal(L/K) = 2) :
    ((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).E
      → (twoLoopsOfCardTwo K L h).E := indToFin2 K L

noncomputable def twoLoopsToResV (h : Nat.card Gal(L/K) = 2) :
    (twoLoopsOfCardTwo K L h).V
      → ((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).V :=
  fin2ToInd K L h (oneLoopVertex K L)

noncomputable def twoLoopsToResE (h : Nat.card Gal(L/K) = 2) :
    (twoLoopsOfCardTwo K L h).E
      → ((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).E :=
  fin2ToInd K L h (oneLoopEdge K L)

/-- The action of `Gal(L/K)` on `Fin 2` through the swap, written as a bare function so that both
sides of the equivariance computation can be compared without any `MulAction` instance in play. -/
noncomputable def twoLoopsAct (σ : Gal(L/K)) : Fin 2 → Fin 2 := by
  letI := Classical.decEq Gal(L/K)
  exact if σ = 1 then id else RQuiver.twoLoopsSwapPerm

theorem twoLoopsAct_one : twoLoopsAct K L 1 = id := by
  letI := Classical.decEq Gal(L/K)
  show (if (1 : Gal(L/K)) = 1 then id else RQuiver.twoLoopsSwapPerm) = id
  rw [if_pos rfl]

theorem twoLoopsAct_ne {σ : Gal(L/K)} (hσ : σ ≠ 1) :
    twoLoopsAct K L σ = RQuiver.twoLoopsSwapPerm := by
  letI := Classical.decEq Gal(L/K)
  show (if σ = 1 then id else RQuiver.twoLoopsSwapPerm) = _
  rw [if_neg hσ]

theorem indToFin2_permHom (h : Nat.card Gal(L/K) = 2) (σ : Gal(L/K))
    (q : InducedSet (galRestrict K L ⊤) X) :
    indToFin2 K L (InducedSet.permHom (galRestrict K L ⊤) X σ q)
      = twoLoopsAct K L σ (indToFin2 K L q) := by
  refine Quotient.inductionOn q ?_
  rintro ⟨a, x⟩
  have hq : (Quotient.mk _ (a, x) : InducedSet (galRestrict K L ⊤) X)
      = InducedSet.mk (galRestrict K L ⊤) a x := rfl
  have hp : InducedSet.permHom (galRestrict K L ⊤) X σ (InducedSet.mk _ a x)
      = InducedSet.mk (galRestrict K L ⊤) (σ * a) x := rfl
  rw [hq, hp]
  rcases eq_one_or_cardTwoGen K L h σ with rfl | rfl
  · rw [one_mul, twoLoopsAct_one]; rfl
  · rw [twoLoopsAct_ne K L (cardTwoGen_ne_one K L h)]
    rcases eq_one_or_cardTwoGen K L h a with rfl | rfl
    · rw [mul_one, indToFin2_ne K L (cardTwoGen_ne_one K L h), indToFin2_one]
      rfl
    · rw [cardTwoGen_mul_self, indToFin2_one, indToFin2_ne K L (cardTwoGen_ne_one K L h)]
      rfl

theorem twoLoops_smul_eq_act (h : Nat.card Gal(L/K) = 2) (σ : Gal(L/K))
    (n : (twoLoopsOfCardTwo K L h).V) : σ • n = twoLoopsAct K L σ n := by
  by_cases hσ : σ = 1
  · subst hσ; rw [one_smul, twoLoopsAct_one]; rfl
  · rw [twoLoops_smul_V K L h hσ, twoLoopsAct_ne K L hσ]

theorem twoLoops_smulE_eq_act (h : Nat.card Gal(L/K) = 2) (σ : Gal(L/K))
    (n : (twoLoopsOfCardTwo K L h).E) : σ • n = twoLoopsAct K L σ n := by
  by_cases hσ : σ = 1
  · subst hσ; rw [one_smul, twoLoopsAct_one]; rfl
  · rw [twoLoops_smul_E K L h hσ, twoLoopsAct_ne K L hσ]

theorem resToTwoLoopsV_equivariant (h : Nat.card Gal(L/K) = 2) (σ : Gal(L/K))
    (q : ((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).V) :
    resToTwoLoopsV K L h (σ • q) = σ • resToTwoLoopsV K L h q :=
  (indToFin2_permHom K L h σ q).trans (twoLoops_smul_eq_act K L h σ _).symm

theorem resToTwoLoopsE_equivariant (h : Nat.card Gal(L/K) = 2) (σ : Gal(L/K))
    (q : ((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).E) :
    resToTwoLoopsE K L h (σ • q) = σ • resToTwoLoopsE K L h q :=
  (indToFin2_permHom K L h σ q).trans (twoLoops_smulE_eq_act K L h σ _).symm

theorem twoLoops_source_id (h : Nat.card Gal(L/K) = 2) (n : (twoLoopsOfCardTwo K L h).V) :
    (twoLoopsOfCardTwo K L h).toRQuiver.source n = n :=
  (by decide : ∀ m : Fin 2, RQuiver.twoLoops.source m = m) n

theorem twoLoops_target_id (h : Nat.card Gal(L/K) = 2) (n : (twoLoopsOfCardTwo K L h).V) :
    (twoLoopsOfCardTwo K L h).toRQuiver.target n = n :=
  (by decide : ∀ m : Fin 2, RQuiver.twoLoops.target m = m) n

theorem indToFin2_mk_eq {Y : Type} [MulAction Gal(L/↥(⊤ : IntermediateField K L)) Y]
    (a : Gal(L/K)) (x : X) (y : Y) :
    indToFin2 K L (InducedSet.mk (galRestrict K L ⊤) a x)
      = indToFin2 K L (InducedSet.mk (galRestrict K L ⊤) a y) := by
  letI := Classical.decEq Gal(L/K)
  show (if a = 1 then (0 : Fin 2) else 1) = (if a = 1 then (0 : Fin 2) else 1)
  rfl

theorem resToTwoLoops_source (h : Nat.card Gal(L/K) = 2)
    (e : ((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).E) :
    resToTwoLoopsV K L h
        (((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).toRQuiver.source e)
      = (twoLoopsOfCardTwo K L h).toRQuiver.source (resToTwoLoopsE K L h e) := by
  rw [twoLoops_source_id]
  refine Quotient.inductionOn e ?_
  rintro ⟨a, x⟩
  exact indToFin2_mk_eq K L a _ x

theorem resToTwoLoops_target (h : Nat.card Gal(L/K) = 2)
    (e : ((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).E) :
    resToTwoLoopsV K L h
        (((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).toRQuiver.target e)
      = (twoLoopsOfCardTwo K L h).toRQuiver.target (resToTwoLoopsE K L h e) := by
  rw [twoLoops_target_id]
  refine Quotient.inductionOn e ?_
  rintro ⟨a, x⟩
  exact indToFin2_mk_eq K L a _ x

theorem twoLoopsToRes_source (h : Nat.card Gal(L/K) = 2) (n : (twoLoopsOfCardTwo K L h).E) :
    twoLoopsToResV K L h ((twoLoopsOfCardTwo K L h).toRQuiver.source n)
      = ((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).toRQuiver.source
          (twoLoopsToResE K L h n) := by
  rw [twoLoops_source_id]
  rfl

theorem twoLoopsToRes_target (h : Nat.card Gal(L/K) = 2) (n : (twoLoopsOfCardTwo K L h).E) :
    twoLoopsToResV K L h ((twoLoopsOfCardTwo K L h).toRQuiver.target n)
      = ((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)).toRQuiver.target
          (twoLoopsToResE K L h n) := by
  rw [twoLoops_target_id]
  rfl

theorem twoLoopsToResV_equivariant (h : Nat.card Gal(L/K) = 2) (σ : Gal(L/K))
    (n : (twoLoopsOfCardTwo K L h).V) :
    twoLoopsToResV K L h (σ • n) = σ • twoLoopsToResV K L h n := by
  have h1 : resToTwoLoopsV K L h (twoLoopsToResV K L h n) = n :=
    indToFin2_fin2ToInd K L h _ n
  conv_lhs => rw [← h1]
  rw [← resToTwoLoopsV_equivariant K L h σ (twoLoopsToResV K L h n)]
  exact fin2ToInd_indToFin2 K L h _ _

theorem twoLoopsToResE_equivariant (h : Nat.card Gal(L/K) = 2) (σ : Gal(L/K))
    (n : (twoLoopsOfCardTwo K L h).E) :
    twoLoopsToResE K L h (σ • n) = σ • twoLoopsToResE K L h n := by
  have h1 : resToTwoLoopsE K L h (twoLoopsToResE K L h n) = n :=
    indToFin2_fin2ToInd K L h _ n
  conv_lhs => rw [← h1]
  rw [← resToTwoLoopsE_equivariant K L h σ (twoLoopsToResE K L h n)]
  exact fin2ToInd_indToFin2 K L h _ _

noncomputable def twoLoopsRestrictionIso (h : Nat.card Gal(L/K) = 2) :
    (RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L) ≅ twoLoopsOfCardTwo K L h where
  hom :=
    { toRQuiverHom :=
        { onV := resToTwoLoopsV K L h
          onE := resToTwoLoopsE K L h
          onV_source := resToTwoLoops_source K L h
          onV_target := resToTwoLoops_target K L h }
      equivariant_V := resToTwoLoopsV_equivariant K L h
      equivariant_E := resToTwoLoopsE_equivariant K L h }
  inv :=
    { toRQuiverHom :=
        { onV := twoLoopsToResV K L h
          onE := twoLoopsToResE K L h
          onV_source := twoLoopsToRes_source K L h
          onV_target := twoLoopsToRes_target K L h }
      equivariant_V := twoLoopsToResV_equivariant K L h
      equivariant_E := twoLoopsToResE_equivariant K L h }
  hom_inv_id := by
    refine RationalQuiver.Hom.ext (RQuiver.Hom.ext ?_ ?_)
    · exact funext fun q => fin2ToInd_indToFin2 K L h _ q
    · exact funext fun q => fin2ToInd_indToFin2 K L h _ q
  inv_hom_id := by
    refine RationalQuiver.Hom.ext (RQuiver.Hom.ext ?_ ?_)
    · exact funext fun n => indToFin2_fin2ToInd K L h _ n
    · exact funext fun n => indToFin2_fin2ToInd K L h _ n

end RestrictionIso

/-- **Example** (`ex:twoloops`, census `RQ2-2.14`).
The restriction to `K` of the one-vertex one-loop quiver along the quadratic extension `L/K` is the
disconnected two-loop quiver with vertices `±` and loops `a_±`, on which the non-trivial element
`c` acts by `c(±) = ∓`, `c(a_±) = a_∓`; `{+,-}` is a single orbit, `{a_+,a_-}` is a single orbit,
all vertex and edge stabilizers are trivial, and the associated étale `K`-species has the single
node `L_{{±}} = L` — `I` has exactly **one** element, stated explicitly under verification finding
C-5 rather than left to be re-derived — with `{}_{{±}}M_{{±}} = L` carrying the **canonical**
bimodule structure: the two structure maps agree, which is "left and right multiplication".

@census    RQ2-2.14
@source    ex:twoloops
@clauses   RQ2-2.14-H1, RQ2-2.14-C1, RQ2-2.14-C2, RQ2-2.14-C3, RQ2-2.14-C4, RQ2-2.14-C5
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.14-H1`. The census's `G = Gal(ℚ[√-1]/ℚ)` is
generalised to an arbitrary quadratic Galois extension `L/K` (`Nat.card Gal(L/K) = 2`), which is
exactly what the source's own §2.4 preamble licenses ("one may also choose `G = Gal(ℂ/ℝ)` or any
other quadratic extension `L/K` for that matter"); the `ℚ[√-1]` case is the instance `K = ℚ`,
`L = ℚ[√-1]` of this statement, and `ℂ/ℝ` is the inhabitant in the tree
(`RationalQuivers.card_gal_complex_real`). Nothing else is reformulated: `C1` is the isomorphism of
`K`-rational quivers between the restriction and the two-loop quiver, `C2` the value of `ρ` at the
non-trivial element, `C3`/`C4` the orbit and stabilizer computations, and `C5` the two conclusions
about the associated species — one node whose field is all of `L`, and equal left and right
structure maps.

Proof plan (G4). `C1`: `restriction`'s vertex set is `Gal(L/K) ×_{Gal(L/⊤)} Fin 1`, and
`Gal(L/⊤)` is trivial, so `InducedSet.mkOut_bijective` identifies it with `Gal(L/K)`, a two-element
set on which `Gal(L/K)` acts simply transitively — the swap. `C3`/`C4`: the action of the
order-two group is the swap, which is fixed-point-free on `Fin 2`, so each orbit is everything and
each stabilizer is `⊥`. `C5`: `stabField` at a point with trivial stabilizer is
`fixedField ⊥ = ⊤` (`IntermediateField.fixedField_bot`), and both structure maps are then the
canonical translation `stabFieldEquivOrbit`, which for a loop has the same source and target.
-/
theorem twoLoops_species (h : Nat.card Gal(L/K) = 2) :
    Nonempty ((RationalQuiver.restriction K L ⊤).obj (oneLoopOverTop K L)
        ≅ twoLoopsOfCardTwo K L h) ∧
      (∀ z : Gal(L/K), z ≠ 1 → (twoLoopsOfCardTwo K L h).ρ z = RQuiver.twoLoopsSwap) ∧
      (∀ v w : (twoLoopsOfCardTwo K L h).V, w ∈ orbit Gal(L/K) v) ∧
      (∀ e f : (twoLoopsOfCardTwo K L h).E, f ∈ orbit Gal(L/K) e) ∧
      (∀ v : (twoLoopsOfCardTwo K L h).V, stabilizer Gal(L/K) v = ⊥) ∧
      (∀ e : (twoLoopsOfCardTwo K L h).E, stabilizer Gal(L/K) e = ⊥) ∧
      Nat.card (twoLoopsOfCardTwo K L h).VertexOrbit = 1 ∧
      (∀ i : (twoLoopsOfCardTwo K L h).VertexOrbit,
        (twoLoopsOfCardTwo K L h).vertexOrbitField i = ⊤) ∧
      (∀ (i j : (twoLoopsOfCardTwo K L h).VertexOrbit)
          (ε : (twoLoopsOfCardTwo K L h).EdgeOrbit i j),
        (twoLoopsOfCardTwo K L h).edgeOrbitField ε = ⊤ ∧
          HEq ((twoLoopsOfCardTwo K L h).edgeComponentLeft ε)
              ((twoLoopsOfCardTwo K L h).edgeComponentRight ε)) := by
  refine ⟨?_, fun z hz => twoLoops_rho_apply K L h hz, twoLoops_orbit_V K L h,
    twoLoops_orbit_E K L h, twoLoops_stabilizer_V K L h, twoLoops_stabilizer_E K L h,
    twoLoops_vertexOrbit_card K L h, twoLoops_vertexOrbitField K L h,
    fun i j ε => ⟨twoLoops_edgeOrbitField K L h ε, twoLoops_edgeComponent_heq K L h i j ε⟩⟩
  exact ⟨twoLoopsRestrictionIso K L h⟩

/-! ### `ex:cyclic` (census `RQ2-2.15`) -/

/-- **Example** (`ex:cyclic`, census `RQ2-2.15`).
The cyclic quiver `Q_cyclic` with vertices `±` and arrows `a : − → +`, `b : + → −`, endowed with
`c(±) = ∓`, `ca = b`, `cb = a`: `{+,-}` and `{a,b}` are single orbits, `I = {{±}}`, all stabilizers
are trivial, and the associated étale `K`-species has the single node `L` with
`{}_{{±}}M_{{±}} = L` carrying the **twisted** bimodule structure — one side acts through `c`
(complex conjugation in the source's `ℚ[√-1]` case) and the other by the standard action. The twist
is the last conjunct: the right structure map is the left one followed by `c`.

@census    RQ2-2.15
@source    ex:cyclic
@clauses   RQ2-2.15-H1, RQ2-2.15-C1, RQ2-2.15-C2, RQ2-2.15-C3, RQ2-2.15-C4, RQ2-2.15-C5
@imports   none
@divergence JUSTIFIED_REFORMULATION on clause `RQ2-2.15-H1`; WEAKENED_OR_PARTIAL on the statement's
representative-specific content (clauses `RQ2-2.15-C4`, `RQ2-2.15-C5`). `H1`: the quadratic extension
is arbitrary, exactly as in `RQ2-2.14` and for the same reason (the source's §2.4 preamble).
**Rewritten 2026-10-03** (docstring-only `R-PROC-4` amendment of frozen S4, coordinator ruling
`R-FR-9`, final-release WP-16b, `MISMATCH-TRIAGE.md` rows #9/#10) against the amended source.
That source fixes the representatives `v_{{±}} = −` and `e_{{a,b}} = a`, reads off `s(a) = −`,
`t(a) = + = c(−)`, hence `σ_{{a,b}} = 1` and `τ_{{a,b}} = c` in `eq:endsofedgetranslations`, and
describes `ℚ[√-1]^twisted` as the field with left structure map the identity and right structure
map `c`. It adds that other representatives give an isomorphic species. The Lean states the
**representative-free invariant** of that computation. For whatever representatives
`Quotient.out` picks, the edge algebra is `L` (`edgeOrbitField ε = ⊤`) and the right structure map
is the left one followed by `z ≠ 1`: `right = z ∘ left`. At the printed representatives this is
`left = id`, `right = c`, exactly as printed. At the mirrored ones (`v = +`) it is the same twist
with the roles exchanged. **Not stated**: the literal values `σ_{{a,b}} = 1`, `τ_{{a,b}} = c` at the
printed representatives (the Lean does not pin the representatives); and the sentence "choosing
other representatives yields an isomorphic species", which the Lean makes moot by stating only the
representative-independent form, without proving an isomorphism between two choices. The text this
paragraph replaces justified `C4` by the twisted tensor product `ℚ[√-1] ⊗_{ℚ[√-1],τ} ℚ[√-1]`, which
the amended source no longer prints. No content beyond the two items above is dropped: `C3`, `C5`'s
structure-map description, and the twist are the last two conjuncts.

Proof plan (G4): as for `RQ2-2.14`, except that the chosen edge representative `e_ε` has
`s(e_ε) ≠ t(e_ε)` — the two ends lie in the same orbit but differ by `c` — so the two canonical
translations `stabFieldEquivOrbit` differ by `c`. `c² = 1` is what makes the conclusion independent
of which vertex `Quotient.out` picked.
-/
theorem cyclic_species (h : Nat.card Gal(L/K) = 2) (z : Gal(L/K)) (hz : z ≠ 1) :
    (cyclicOfCardTwo K L h).ρ z = RQuiver.cyclicSwap ∧
      (∀ v w : (cyclicOfCardTwo K L h).V, w ∈ orbit Gal(L/K) v) ∧
      (∀ e f : (cyclicOfCardTwo K L h).E, f ∈ orbit Gal(L/K) e) ∧
      Nat.card (cyclicOfCardTwo K L h).VertexOrbit = 1 ∧
      (∀ v : (cyclicOfCardTwo K L h).V, stabilizer Gal(L/K) v = ⊥) ∧
      (∀ e : (cyclicOfCardTwo K L h).E, stabilizer Gal(L/K) e = ⊥) ∧
      (∀ i j : (cyclicOfCardTwo K L h).VertexOrbit, i = j) ∧
      (∀ (i : (cyclicOfCardTwo K L h).VertexOrbit)
          (ε : (cyclicOfCardTwo K L h).EdgeOrbit i i),
        (cyclicOfCardTwo K L h).edgeOrbitField ε = ⊤ ∧
          ∀ α : (cyclicOfCardTwo K L h).vertexOrbitField i,
            (((cyclicOfCardTwo K L h).edgeComponentRight ε α : L))
              = z (((cyclicOfCardTwo K L h).edgeComponentLeft ε α : L))) :=
  ⟨cyclic_rho_apply K L h hz, cyclic_orbit_V K L h, cyclic_orbit_E K L h,
    cyclic_vertexOrbit_card K L h, cyclic_stabilizer_V K L h, cyclic_stabilizer_E K L h,
    fun i j => Subsingleton.elim i j,
    fun i ε => ⟨cyclic_edgeOrbitField K L h ε, cyclic_twist K L h z hz i ε⟩⟩

/-! ### `ex:gelfand` (census `RQ2-2.16`) — **RE-SEQUENCED TO STAGE S5**, 2026-08-30

Coordinator ruling of 2026-08-30: `RQ2-2.16` moves from S4 to **S5**, which has `S2` as a
predecessor in the `PLAN.md` §2 stage DAG. Nothing is relocated — S4 never typed the row, so S5
types it fresh; this note is the handover, and `STAGE-MAP.tsv`'s `census RQ2-2.16` row is the
instrument owner's to update.

**Why.** Clause `RQ2-2.16-C3` — "the relation is a consequence of `G`-equivariance and hence may be
dropped when considering **representations** over `K`" — is a statement about
`RationalQuivers.RationalQuiver.Rep`, which is stage **S2**. `S2` is not a predecessor of `S4`
(the edges into `S4` are `S1 → S4` and `S3 → S4`), so stating `C3` here produced 11
`STAGE-FORWARD`/`STAGE-FORWARD-DECL` violations of `rqaudit deps --no-forward` (measured), and
dropping `C3` was not an option either: its `if_missing` is `WEAKENED_OR_PARTIAL`. Adding an
`S2 → S4` edge mid-flight was ruled the worse surgery.

**Handover note for S5, and it is load-bearing.** For a `K`-rational representation `M` of the
Gelfand quiver with the `ex:gelfand` action, `eq:koecheractiononrep` gives

`φ_{a₊} ∘ φ_{b₊} = φ_{⋆,c} ∘ (φ_{a₋} ∘ φ_{b₋}) ∘ φ_{⋆,c}⁻¹`,

i.e. the two composites named in the relation `a₋b₋ = a₊b₊` are `c`-**conjugate**. The relation
asserts that they are **equal**, i.e. that `φ_{a₋}φ_{b₋} ∈ End(M(⋆))` is fixed by the semi-linear
`c`-action — that it is defined over `K`. The S4 implementer could not derive that from
`G`-equivariance alone. Two readings survive and S5 has the machinery to adjudicate between them:

1. the `K`-rationality does real work — `φ_{⋆,c}` is a semi-linear involution and `M(⋆)` descends
   to `M(⋆)^{c}` by `thm:galoisdescent`, so the claim may be that the composite, being built from
   the descended data, is automatically `c`-invariant; or
2. the literal reading is a **defect of the source**, and the relation is *not* a consequence of
   equivariance for arbitrary `K`-rational representations.

Whichever it is, `WORKFLOW.md`'s stop protocol applies: if S5's proof attempt produces a
counterexample, that is a fidelity finding (defect class 1) to be adjudicated, never silently
weakened. Recorded before any proof was attempted, per `workflow/stages/S4/DESIGN-NOTES.md` §3.

**What S4 leaves behind for S5, unchanged and reusable.** The `ex:gelfand` quiver itself is stage
S1's `RationalQuiver.gelfandOfCardTwo` with `RQuiver.gelfandRelationSet`; its `±`-swap, the two
parallel length-two paths of the relation and the action of the swap on them
(`RQuiver.onRelation_gelfandSwap_image`) are all in `Quiver/Models.lean` and
`Quiver/Relations.lean`. The two examples below (`RQ2-2.14`, `RQ2-2.15`) are stated over an arbitrary
quadratic Galois extension for the reason `MD-S4-03` records, and `RQ2-2.16` should follow the same
convention so that S8 consumes one and the same object.
-/

/-! ### The two witnesses for finding **S4-F1** (`RQ2-2.04`'s morphism direction)

These are the permanent in-tree justification for the `@divergence` recorded on `RQ2-2.04`
(`Species/Hom.lean`), landed here in an S4-owned module at the coordinator's direction and in the
pattern stage S3 used for finding S3-F2 (`literal_baseChange_structureMaps_ne` and friends): the
refuted object is defined locally, and theorems about the **source's own examples** show it cannot
serve.

`PrintedHom` below is `RQ2-2.04` **exactly as printed** — index map and algebra maps running the
same way. The two objects are the source's own: `Γ₂` is the `ex:gelfand` quiver (vertices `−`, `⋆`,
`+` with `c` swapping `±` and fixing `⋆`) and `Γ₁` is the one-vertex quiver with the split
structure. The quiver morphism `f : Γ₂ → Γ₁` collapsing everything to the point is `Gal(L/K)`-
equivariant, so `S(−)` must send it *somewhere*, and:

* in the **contravariant** reading the theorem asserts, it would have to be a printed-shape
  morphism `S(Γ₂) → S(Γ₁)`, and there is **none** — the `±`-orbit's field is all of `L`, the
  point's field is `K`, and there is no `K`-algebra map `L → K`
  (`printedHom_isEmpty_of_gelfand_to_point`);
* in the **covariant** reading it would be a printed-shape morphism `S(Γ₁) → S(Γ₂)`, and there are
  **two**, differing already on the index map and with genuinely different field components
  (`K → L` versus `K → K`), because a printed-shape index map here is a *section* of the orbit map
  (`printedHom_onI_not_unique`).

With the amended direction the same `f` has exactly one image, canonically: the orbit map together
with the fixed-field inclusions.
-/

/-- `RQ2-2.04` **as printed**: a map `ι : I → Ĩ` of index sets *together with* algebra maps
`L_i → L̃_{ι(i)}` and `{}_iM_j → {}_{ι(i)}M̃_{ι(j)}` running the same way. This is the shape stage
S3 implemented and which finding S4-F1 showed cannot carry `RQ2-2.13`'s functors; it is kept here,
and only here, as the object the two witness theorems refute.

@census none (evidence for the `@divergence` on `RQ2-2.04`, finding S4-F1)
-/
structure PrintedHom (S T : EtaleSpecies.{0} K) : Type where
  /-- The index map, in the printed direction. -/
  onI : S.I → T.I
  /-- The vertex-field maps, running along `onI` as printed. -/
  onL : ∀ i, S.L i →ₐ[K] T.L (onI i)
  /-- The edge-algebra maps, as printed. -/
  onM : ∀ i j, S.M i j →ₐ[K] T.M (onI i) (onI j)
  /-- Compatibility with the left structure maps. -/
  compat_left : ∀ i j, (onM i j).comp (S.left i j) = (T.left (onI i) (onI j)).comp (onL i)
  /-- Compatibility with the right structure maps. -/
  compat_right : ∀ i j, (onM i j).comp (S.right i j) = (T.right (onI i) (onI j)).comp (onL j)

/-- The printed shape is **not** empty in general — the identity has it. (G5 inhabitant; the point
of the two theorems below is that it is empty, or non-canonical, exactly where `RQ2-2.13` needs it.)

@census none (G5 inhabitant for `PrintedHom`)
-/
def PrintedHom.id (S : EtaleSpecies.{0} K) : PrintedHom K S S where
  onI := fun i => i
  onL := fun i => AlgHom.id K (S.L i)
  onM := fun i j => AlgHom.id K (S.M i j)
  compat_left := fun _ _ => rfl
  compat_right := fun _ _ => rfl

/-- The two commuting squares of a printed-shape morphism, on elements. Recorded so that the
`compat_left`/`compat_right` fields of the replica are *used* and not merely declared
(`WORKFLOW.md` G5.4), and because this is the form in which the witness proofs consume them.

@census none (helper for the S4-F1 witnesses)
-/
theorem PrintedHom.compat_apply {S T : EtaleSpecies.{0} K} (f : PrintedHom K S T) (i j : S.I) :
    (∀ a : S.L i, f.onM i j (S.left i j a) = T.left (f.onI i) (f.onI j) (f.onL i a)) ∧
      ∀ b : S.L j, f.onM i j (S.right i j b) = T.right (f.onI i) (f.onI j) (f.onL j b) :=
  ⟨fun a => congrArg (fun g => g a) (f.compat_left i j),
   fun b => congrArg (fun g => g b) (f.compat_right i j)⟩

/-- The vertices of the Gelfand quiver, named in its own vertex type: `−`(=0), `⋆`(=1), `+`(=2). -/
noncomputable def gelfandVertex (h : Nat.card Gal(L/K) = 2) (n : Fin 3) :
    (gelfandOfCardTwo K L h).V := n

/-- The vertex stabilizers of `ex:gelfand` at `±` are **trivial** (clause `RQ2-2.16-C4`'s content,
proved here because the S4-F1 witnesses need it).

@census none (helper for the S4-F1 witnesses)
-/
theorem stabilizer_gelfandVertex_eq_bot (h : Nat.card Gal(L/K) = 2) (n : Fin 3) (hn : n ≠ 1) :
    stabilizer Gal(L/K) (gelfandVertex K L h n) = ⊥ := by
  ext σ
  simp only [Subgroup.mem_bot, mem_stabilizer_iff]
  refine ⟨fun hσ => ?_, by rintro rfl; exact one_smul _ _⟩
  by_contra hne
  have hr := RationalQuiver.gelfandOfCardTwo_rho_apply K L h hne
  have hmove : σ • gelfandVertex K L h n
      = gelfandVertex K L h (RQuiver.gelfandVertexSwap n) := by
    show (RQuiver.Aut.toPermV _ ((gelfandOfCardTwo K L h).ρ σ)) n = _
    rw [hr]; rfl
  rw [hσ] at hmove
  have hswap : ∀ m : Fin 3, m ≠ 1 → RQuiver.gelfandVertexSwap m ≠ m := by decide
  exact hswap n hn (congrArg (fun x => (x : Fin 3)) hmove.symm)

/-- The vertex stabilizer of `ex:gelfand` at `⋆` is **everything**: `c` fixes `⋆`.

@census none (helper for the S4-F1 witnesses)
-/
theorem stabilizer_gelfandVertex_star (h : Nat.card Gal(L/K) = 2) :
    stabilizer Gal(L/K) (gelfandVertex K L h 1) = ⊤ := by
  ext σ
  simp only [Subgroup.mem_top, iff_true, mem_stabilizer_iff]
  by_cases hne : σ = 1
  · rw [hne]; exact one_smul _ _
  · have hr := RationalQuiver.gelfandOfCardTwo_rho_apply K L h hne
    show (RQuiver.Aut.toPermV _ ((gelfandOfCardTwo K L h).ρ σ)) (1 : Fin 3) = _
    rw [hr]; rfl

/-- `L(±) = L`: the vertex field of the `±`-orbit is all of `L` (clause `RQ2-2.16-C4`).

@census none (helper for the S4-F1 witnesses)
-/
theorem gelfand_vertexOrbitField_pm (h : Nat.card Gal(L/K) = 2) :
    (gelfandOfCardTwo K L h).vertexOrbitField
        ((gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 0)) = ⊤ := by
  refine stabField_eq_top_of_stabilizer_eq_bot ?_
  refine stabilizer_eq_bot_of_mem_orbit ?_
    (stabilizer_gelfandVertex_eq_bot K L h 0 (by decide))
  exact MulAction.mem_orbit_symm.mp
    ((gelfandOfCardTwo K L h).mem_orbit_vertexRep (gelfandVertex K L h 0))

/-- Every vertex of a **split** quiver has full stabilizer: `ρ = 1`.

@census none (helper for the S4-F1 witnesses)
-/
theorem split_stabilizer_top (Γ : RQuiver.{0}) (v : (RationalQuiver.split K L Γ).V) :
    stabilizer Gal(L/K) v = ⊤ := by
  ext σ
  simp only [Subgroup.mem_top, iff_true, mem_stabilizer_iff]
  show (RQuiver.Aut.toPermV Γ ((RationalQuiver.split K L Γ).ρ σ)) v = v
  rfl

/-- Hence every vertex field of a split quiver's species is `K` (i.e. `⊥ ⊆ L`).

@census none (helper for the S4-F1 witnesses)
-/
theorem split_vertexOrbitField (Γ : RQuiver.{0})
    (i : (RationalQuiver.split K L Γ).VertexOrbit) :
    (RationalQuiver.split K L Γ).vertexOrbitField i = ⊥ := by
  show stabField K L _ = ⊥
  rw [stabField, split_stabilizer_top K L Γ _]
  exact IsGalois.fixedField_top

/-- The `⋆`-orbit and the `±`-orbit of `ex:gelfand` are **different** orbits.

@census none (helper for the S4-F1 witnesses)
-/
theorem gelfand_vertexClass_star_ne (h : Nat.card Gal(L/K) = 2) :
    (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 1)
      ≠ (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 0) := by
  intro heq
  obtain ⟨σ, hσ⟩ := mem_orbit_iff.mp (Quotient.exact heq)
  by_cases hne : σ = 1
  · rw [hne, one_smul] at hσ
    have h01 : (0 : Fin 3) = (1 : Fin 3) := hσ
    exact absurd h01 (by decide)
  · have hr := gelfandOfCardTwo_rho_apply K L h hne
    have hmove : σ • gelfandVertex K L h 0
        = gelfandVertex K L h (RQuiver.gelfandVertexSwap 0) := by
      show (RQuiver.Aut.toPermV _ ((gelfandOfCardTwo K L h).ρ σ)) (0 : Fin 3) = _
      rw [hr]; rfl
    rw [hmove] at hσ
    have h21 : (RQuiver.gelfandVertexSwap 0 : Fin 3) = (1 : Fin 3) := hσ
    exact absurd h21 (by decide)

/-- `+` and `−` are in one orbit: `c` swaps them.

@census none (helper for the S4-F1 witnesses)
-/
theorem gelfand_vertexClass_two (h : Nat.card Gal(L/K) = 2) :
    (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 2)
      = (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 0) := by
  obtain ⟨σ, hσ, -⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
  have hr := gelfandOfCardTwo_rho_apply K L h hσ
  refine Quotient.sound ⟨σ, ?_⟩
  show (RQuiver.Aut.toPermV _ ((gelfandOfCardTwo K L h).ρ σ)) (0 : Fin 3) = _
  rw [hr]; rfl

/-- `L(⋆) = K`: the `⋆` vertex is fixed, so its field is the base field (clause `RQ2-2.16-C4`).

@census none (helper for the S4-F1 witnesses)
-/
theorem gelfand_vertexOrbitField_star (h : Nat.card Gal(L/K) = 2) :
    (gelfandOfCardTwo K L h).vertexOrbitField
        ((gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 1)) = ⊥ := by
  show stabField K L _ = ⊥
  rw [stabField, stabilizer_eq_top_of_mem_orbit
    (MulAction.mem_orbit_symm.mp
      ((gelfandOfCardTwo K L h).mem_orbit_vertexRep (gelfandVertex K L h 1)))
    (stabilizer_gelfandVertex_star K L h)]
  exact IsGalois.fixedField_top

/-- **Every arrow of the Gelfand quiver has exactly one end at `⋆`**, so no arrow runs from a vertex
orbit to itself: `E_{ii} = ∅` for both orbits. This is what makes the two competing printed-shape
morphisms of `printedHom_onI_not_unique` constructible — their edge component lands in the empty
product.

@census none (helper for the S4-F1 witnesses)
-/
theorem gelfand_edgeSet_diag_isEmpty (h : Nat.card Gal(L/K) = 2)
    (i : (gelfandOfCardTwo K L h).VertexOrbit) :
    IsEmpty ((gelfandOfCardTwo K L h).edgeSet i i) := by
  refine ⟨fun e => ?_⟩
  obtain ⟨e, hs, ht⟩ := e
  have hne := gelfand_vertexClass_star_ne K L h
  have hother : ∀ n : Fin 3, n ≠ 1 →
      (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h n)
        = (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 0) := by
    intro n hn
    have hn3 : n = 0 ∨ n = 2 := by revert hn; revert n; decide
    rcases hn3 with rfl | rfl
    · rfl
    · exact gelfand_vertexClass_two K L h
  have hends : ∀ f : Fin 4,
      ((RQuiver.gelfand.source f = 1 ∧ RQuiver.gelfand.target f ≠ 1) ∨
        (RQuiver.gelfand.target f = 1 ∧ RQuiver.gelfand.source f ≠ 1)) := by decide
  rcases hends e with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : (gelfandOfCardTwo K L h).toRQuiver.source e = gelfandVertex K L h 1 := h1
    refine hne ?_
    calc (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 1)
        = (gelfandOfCardTwo K L h).vertexClass
            ((gelfandOfCardTwo K L h).toRQuiver.source e) := by rw [h1']
      _ = i := hs
      _ = (gelfandOfCardTwo K L h).vertexClass
            ((gelfandOfCardTwo K L h).toRQuiver.target e) := ht.symm
      _ = _ := hother _ h2
  · have h1' : (gelfandOfCardTwo K L h).toRQuiver.target e = gelfandVertex K L h 1 := h1
    refine hne ?_
    calc (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 1)
        = (gelfandOfCardTwo K L h).vertexClass
            ((gelfandOfCardTwo K L h).toRQuiver.target e) := by rw [h1']
      _ = i := ht
      _ = (gelfandOfCardTwo K L h).vertexClass
            ((gelfandOfCardTwo K L h).toRQuiver.source e) := hs.symm
      _ = _ := hother _ h2

/-- Consequently the diagonal edge algebras of `S(Q_Gelfand)` are trivial rings. -/
theorem gelfand_edgeAlgebra_diag_subsingleton (h : Nat.card Gal(L/K) = 2)
    (i : (gelfandOfCardTwo K L h).VertexOrbit) :
    Subsingleton ((gelfandOfCardTwo K L h).toSpecies.M i i) := by
  haveI : IsEmpty ((gelfandOfCardTwo K L h).EdgeOrbit i i) := by
    haveI := gelfand_edgeSet_diag_isEmpty K L h i
    exact Quotient.instIsEmpty
  exact inferInstanceAs (Subsingleton (∀ ε : (gelfandOfCardTwo K L h).EdgeOrbit i i,
    ((gelfandOfCardTwo K L h).edgeOrbitField ε : Type)))

/-- The unique `K`-algebra map into a trivial ring. -/
def algHomToSubsingleton (A B : Type) [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
    [Subsingleton B] : A →ₐ[K] B where
  toFun := fun _ => 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _
  commutes' _ := Subsingleton.elim _ _

/-- A printed-shape morphism from the one-vertex split quiver's species into `S(Q_Gelfand)`, sending
the single index to a **chosen** orbit `i₀`. The existence of this family for *every* `i₀` is the
non-canonicity of `printedHom_onI_not_unique`.

@census none (evidence for the `@divergence` on `RQ2-2.04`, finding S4-F1)
-/
noncomputable def constPrintedHom (h : Nat.card Gal(L/K) = 2)
    (i₀ : (gelfandOfCardTwo K L h).VertexOrbit) :
    PrintedHom K ((RationalQuiver.split K L RQuiver.oneLoop).toSpecies)
      ((gelfandOfCardTwo K L h).toSpecies) where
  onI := fun _ => i₀
  onL := fun i => IntermediateField.inclusion
    (by rw [split_vertexOrbitField K L RQuiver.oneLoop i]; exact bot_le)
  onM := fun _ _ =>
    haveI := gelfand_edgeAlgebra_diag_subsingleton K L h i₀
    algHomToSubsingleton K _ _
  compat_left := fun _ _ =>
    haveI := gelfand_edgeAlgebra_diag_subsingleton K L h i₀
    AlgHom.ext fun _ => Subsingleton.elim _ _
  compat_right := fun _ _ =>
    haveI := gelfand_edgeAlgebra_diag_subsingleton K L h i₀
    AlgHom.ext fun _ => Subsingleton.elim _ _

/-- **Witness 1 for finding S4-F1** (the contravariant reading fails: the printed shape is
*uninhabited* where the functor needs it).
There is no printed-shape morphism from `S(Q_Gelfand)` to the species of the one-vertex split
quiver. Such a morphism would have to carry the vertex field of the `±`-orbit — which is
`L^{G_±} = L^{1} = L`, of degree 2 over `K` — into the vertex field of the point, which is
`L^{Gal(L/K)} = K`; and there is no `K`-algebra map out of `L` into `K`, since a `K`-algebra map of
fields is injective and `[L : K] = 2 > 1 = [K : K]`.

Proof plan (G4): `stabField` at a vertex with trivial stabilizer is `fixedField ⊥ = ⊤`
(`IntermediateField.fixedField_bot`) and at a vertex fixed by everything is `fixedField ⊤ = ⊥`;
`IsGalois.card_aut_eq_finrank` turns `Nat.card Gal(L/K) = 2` into `finrank K L = 2`; an
`AlgHom` of fields is injective, so it would force `finrank K L ≤ 1`.

**Verification finding C-2: DISCHARGED (2026-08-30).** This theorem and `printedHom_onI_not_unique`
carry the justification for a *sanctioned departure from the printed source*, so C-2 asked that they
head the G4 list rather than remain promises. **Both are now proved**, so the amendment's evidence
is a pair of theorems about the source's own `ex:gelfand` quiver.

@census none (evidence for the `@divergence` on `RQ2-2.04`, finding S4-F1)
-/
theorem printedHom_isEmpty_of_gelfand_to_point (h : Nat.card Gal(L/K) = 2) :
    IsEmpty (PrintedHom K ((gelfandOfCardTwo K L h).toSpecies)
      ((RationalQuiver.split K L RQuiver.oneLoop).toSpecies)) := by
  refine ⟨fun f => ?_⟩
  set i := (gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 0) with hi
  -- the source field is all of `L`, of degree 2 over `K`
  have hsrc : Module.finrank K ((gelfandOfCardTwo K L h).toSpecies.L i) = 2 := by
    have h1 : Module.finrank K ((gelfandOfCardTwo K L h).toSpecies.L i)
        = Module.finrank K ((⊤ : IntermediateField K L) : Type) :=
      congrArg (fun E : IntermediateField K L => Module.finrank K (E : Type))
        (gelfand_vertexOrbitField_pm K L h)
    rw [h1, (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finrank_eq,
      ← IsGalois.card_aut_eq_finrank K L, h]
  -- the target field is `K`, of degree 1
  have htgt : Module.finrank K ((RationalQuiver.split K L RQuiver.oneLoop).toSpecies.L
      (f.onI i)) = 1 := by
    have h2 : Module.finrank K ((RationalQuiver.split K L RQuiver.oneLoop).toSpecies.L (f.onI i))
        = Module.finrank K ((⊥ : IntermediateField K L) : Type) :=
      congrArg (fun E : IntermediateField K L => Module.finrank K (E : Type))
        (split_vertexOrbitField K L RQuiver.oneLoop (f.onI i))
    rw [h2, IntermediateField.finrank_bot]
  -- but `f.onL i` is an injective `K`-linear map between them
  have hinj : Function.Injective (f.onL i) := (f.onL i).toRingHom.injective
  have hle := LinearMap.finrank_le_finrank_of_injective (f := (f.onL i).toLinearMap) hinj
  rw [hsrc, htgt] at hle
  omega

/-- **Witness 2 for finding S4-F1** (the covariant reading fails: the printed shape is inhabited
but *not canonical*).
In the other direction there are at least **two** printed-shape morphisms, differing already on the
index map: a printed-shape index map out of the one-point index set of `S(Γ₁)` is exactly a choice
of one of the two orbits of `Q_Gelfand`, and the two choices have genuinely different field
components — the `±`-orbit contributes `K → L` and the `⋆`-orbit `K → K`. So `S(−)` on morphisms
would depend on a choice, and could not be functorial.

Proof plan (G4), sharpened by the machinery `printedHom_isEmpty_of_gelfand_to_point` now provides:
both morphisms have `onL` the inclusion of `⊥` (the split source's vertex field,
`split_vertexOrbitField`) into the target's, which is `⊤` for the `±`-orbit
(`gelfand_vertexOrbitField_pm`) and `⊥` for the `⋆`-orbit; the index maps are distinguished by
those two fields, which differ because `finrank K L = 2`. The remaining ingredient is the `onM`
component: it must land in `{}_{±}M_{±}` resp. `{}_{⋆}M_{⋆}`, and **both are the empty product** —
every arrow of the Gelfand quiver has exactly one end at `⋆` — so both are subsingleton rings and
the component is forced. Formalising that needs `IsEmpty (edgeSet i i)` for the two diagonal pairs,
which reduces to `vertexClass ⋆ ≠ vertexClass ±` (available: the orbit of `0` is `{0,2}`) plus a
four-case check on the arrows.

**Verification finding C-2: DISCHARGED (2026-08-30)** — see the note on
`printedHom_isEmpty_of_gelfand_to_point`. The two morphisms are `constPrintedHom` at the `±`- and
the `⋆`-orbit; what makes them constructible is that both diagonal edge algebras of `S(Q_Gelfand)`
are trivial rings (`gelfand_edgeAlgebra_diag_subsingleton`), every arrow of the Gelfand quiver
having exactly one end at `⋆`.

@census none (evidence for the `@divergence` on `RQ2-2.04`, finding S4-F1)
-/
theorem printedHom_onI_not_unique (h : Nat.card Gal(L/K) = 2) :
    ∃ h₁ h₂ : PrintedHom K ((RationalQuiver.split K L RQuiver.oneLoop).toSpecies)
        ((gelfandOfCardTwo K L h).toSpecies),
      h₁.onI ≠ h₂.onI ∧
        ∀ i, (gelfandOfCardTwo K L h).vertexOrbitField (h₁.onI i) = ⊤ ∧
          (gelfandOfCardTwo K L h).vertexOrbitField (h₂.onI i) = ⊥ := by
  refine ⟨constPrintedHom K L h ((gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 0)),
    constPrintedHom K L h ((gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 1)),
    ?_, fun i => ⟨gelfand_vertexOrbitField_pm K L h, gelfand_vertexOrbitField_star K L h⟩⟩
  intro hcontra
  exact gelfand_vertexClass_star_ne K L h
    (congrFun hcontra ((RationalQuiver.split K L RQuiver.oneLoop).vertexClass
      (show (RationalQuiver.split K L RQuiver.oneLoop).V from (0 : Fin 1)))).symm

/-! ### `ex:twoloops` as the second counterexample of finding S3-F2 -/

/-! ### The trivial action after base change to `⊤`

`baseChange K L ⊤` restricts the Galois action along `Gal(L/⊤) → Gal(L/K)`, and `Gal(L/⊤)` is
**trivial** (`subsingleton_galTop`), so the base-changed quiver carries the trivial action however
non-trivial the original was. That is the whole content of the `MD-S3-08` counterexample: the
orbits become singletons, so `S(Γ_N)` has one node per vertex, and the off-diagonal edge algebras
are empty products.
-/

theorem baseChangeTop_smul_V (Γ : RationalQuiver K L)
    (σ : Gal(L/↥(⊤ : IntermediateField K L))) (v : ((RationalQuiver.baseChange K L ⊤).obj Γ).V) :
    σ • v = v := by
  rw [Subsingleton.elim σ 1, one_smul]

theorem baseChangeTop_smul_E (Γ : RationalQuiver K L)
    (σ : Gal(L/↥(⊤ : IntermediateField K L))) (e : ((RationalQuiver.baseChange K L ⊤).obj Γ).E) :
    σ • e = e := by
  rw [Subsingleton.elim σ 1, one_smul]

theorem baseChangeTop_vertexClass_bijective (Γ : RationalQuiver K L) :
    Function.Bijective
      (((RationalQuiver.baseChange K L ⊤).obj Γ).vertexClass) := by
  constructor
  · intro v w hvw
    obtain ⟨σ, hσ⟩ := mem_orbit_iff.mp (Quotient.exact hvw)
    rw [baseChangeTop_smul_V K L Γ σ w] at hσ
    exact hσ.symm
  · exact Quotient.mk_surjective


/-- **Handover from stage S3** (`stages/S3/DESIGN-NOTES.md` §2, `MD-S3-08`): the second
counterexample to the *printed* base-change formula of `def:basechangeforspecies` (clause
`RQ2-2.05-C5`), which stage S3 could not formalize because it needs `S(−)` — census `RQ2-2.09`, an
S4 row, so a theorem about it in S3 would have been a forward stage dependency.

The comparison the source's own proof of `prop:speciesrestrictionbasechangeadjunction` requires is
`S(Γ_K) ⊗_K N` versus `S(Γ_N)`. Take `Γ_K` = `ex:twoloops` and `N = L`. Base change of a quiver
(`def:quiverbasechange`) leaves `(V,E,s,t)` untouched and only restricts the Galois action, so
`Γ_N` carries the **trivial** action: its species `S(Γ_N)` has **two** nodes, and the two
off-diagonal edge algebras are **trivial** — that is this theorem — because `E_{+-} = ∅`: the two
loops sit at `+` and at `−`. The printed formula instead gives
`{}_{+}M'_{-} = L'_+ ⊗_{L} L ⊗_{L} L'_- ≅ L ≠ 0`. The two disagree, which is what finding S3-F2
claims; the corrected (implemented) formula gives `0` here, matching `S(Γ_N)`.

@census none (evidence for the `@divergence` on `RQ2-2.05`, finding S3-F2; the row itself is S3's)
-/
theorem twoLoops_baseChange_offDiagonal_subsingleton (h : Nat.card Gal(L/K) = 2)
    (i j : ((RationalQuiver.baseChange K L ⊤).obj (twoLoopsOfCardTwo K L h)).VertexOrbit)
    (hij : i ≠ j) :
    Subsingleton
      (((RationalQuiver.baseChange K L ⊤).obj (twoLoopsOfCardTwo K L h)).edgeAlgebra i j) := by
  haveI : IsEmpty
      (((RationalQuiver.baseChange K L ⊤).obj (twoLoopsOfCardTwo K L h)).EdgeOrbit i j) := by
    constructor
    intro ε
    obtain ⟨e, -⟩ := Quotient.exists_rep ε
    exact hij (e.2.1.symm.trans e.2.2)
  haveI := Pi.uniqueOfIsEmpty
    (fun ε : ((RationalQuiver.baseChange K L ⊤).obj (twoLoopsOfCardTwo K L h)).EdgeOrbit i j =>
      (((RationalQuiver.baseChange K L ⊤).obj (twoLoopsOfCardTwo K L h)).edgeOrbitField ε :
        Type))
  infer_instance

/-- The companion half of the comparison: the base-changed two-loop quiver really does have **two**
vertex orbits (the action is trivial after base change), so the off-diagonal entries above are not
vacuous. Together with `twoLoops_baseChange_offDiagonal_subsingleton` this is the `ex:twoloops`
counterexample of `MD-S3-08`.

@census none (evidence for the `@divergence` on `RQ2-2.05`, finding S3-F2)
-/
theorem twoLoops_baseChange_two_orbits (h : Nat.card Gal(L/K) = 2) :
    Nat.card ((RationalQuiver.baseChange K L ⊤).obj (twoLoopsOfCardTwo K L h)).VertexOrbit = 2 := by
  rw [← Nat.card_eq_of_bijective _
    (baseChangeTop_vertexClass_bijective K L (twoLoopsOfCardTwo K L h))]
  have hV : Nat.card ((RationalQuiver.baseChange K L ⊤).obj (twoLoopsOfCardTwo K L h)).V
      = Nat.card (Fin 2) := rfl
  rw [hV]
  simp

/-! ### G5 witnesses for `PrintedHom` (G8 cross-model review finding F-M1-R-2)

`Examples.PrintedHom` was one of the eight structures the review found carrying **no G5 item-(3)
all-trivial entry anywhere** (`workflow/audit/M1/FINAL_AUDIT.md` §11.7).  Landed by commission
**C-M1-1**, 2026-09-02, as a dated `WORKFLOW.md` F5 amendment of frozen stage S4; no S4 statement
changed.  The `Meta/Vacuity.lean` registry entry citing these declarations is owed to the
**instrument owner** (F3).
-/

/-- **G5.3 probe (`PrintedHom`): the all-trivial interpretation** — source and target both the
split one-node species on `K`, every component the identity.

**It type-checks.**  So the printed morphism shape is *not* empty as a shape: what
`printedHom_isEmpty_of_gelfand_to_point` refutes is the printed shape **at `ex:gelfand`**, and
what `printedHom_onI_not_unique` refutes is its **canonicity** there.  Recording the probe is what
keeps those two theorems from being misread as "the printed definition does not type-check": it
does, and finding **S4-F1** is a statement about the source's own examples, not about elaboration.

@census none (G5.3 all-trivial probe for `PrintedHom`, finding S4-F1's evidence)
-/
def trivialPrintedHom : PrintedHom K (EtaleSpecies.trivial K) (EtaleSpecies.trivial K) :=
  PrintedHom.id K (EtaleSpecies.trivial K)

/-- **G5.2 non-degeneracy** (`PrintedHom`): between one fixed pair of species the printed shape has
**at least two distinct** inhabitants — `constPrintedHom` at the `±`-orbit and at the `⋆`-orbit.
So `PrintedHom` is not a subsingleton, which is the degenerate reading in which "the printed shape
is inhabited" would carry no information; and it is the element-level form of
`printedHom_onI_not_unique`, whose conclusion is about the components rather than about the two
morphisms themselves.

@census none (G5.2 non-degeneracy witness for `PrintedHom`, finding S4-F1's evidence)
-/
theorem constPrintedHom_ne (h : Nat.card Gal(L/K) = 2) :
    constPrintedHom K L h ((gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 0))
      ≠ constPrintedHom K L h ((gelfandOfCardTwo K L h).vertexClass (gelfandVertex K L h 1)) := by
  intro hc
  refine gelfand_vertexClass_star_ne K L h ?_
  have hI := congrArg PrintedHom.onI hc
  exact (congrFun hI ((RationalQuiver.split K L RQuiver.oneLoop).vertexClass
      (show (RationalQuiver.split K L RQuiver.oneLoop).V from (0 : Fin 1)))).symm

end Examples

/-! ## Concrete non-identity morphisms of étale species (G8 review finding F-M1-R-8)

`FINAL_AUDIT.md` §11.6(a)/§11.7 measured that **no concrete non-identity morphism of étale species
existed in the tree**: `EtaleSpecies.Hom.id` and `.comp` were the only closed inhabitants of
`EtaleSpecies.Hom`, every other producer (a functor's `map` field, the anti-equivalence's unit and
counit) being parametric in an arbitrary given morphism.  That is a live G5 item-(2) risk exactly
because finding **S4-F1** is a finding *about the morphism definition*: the definition whose index
direction was amended had no concrete non-trivial witness.

Landed by commission **C-M1-1**, 2026-09-02, in this **S4** module rather than in `Species/Hom.lean`
(stage S3) so that frozen S3 is not amended; `Species/Hom.lean` is imported, not edited.  Both
witnesses use the S3 models `EtaleSpecies.trivial` and `EtaleSpecies.complexLoop`, which are the
one-node species on `K` and on `ℂ ⊃ ℝ`.

Recall the amended direction (`RQ2-2.04`, finding S4-F1): a morphism `S ⟶ T` carries `onI : T.I →
S.I` **against** the arrow, with `onL t : S.L (onI t) →ₐ[K] T.L t` and `onM` along it.
-/

namespace EtaleSpecies

/-- **G5.2 (`EtaleSpecies.Hom`, census `RQ2-2.04`): a concrete non-identity endomorphism.**
Complex conjugation on the one-node species `ℝ ⊂ ℂ`, acting simultaneously on the vertex field and
on the edge algebra.  The two `compat_*` fields hold because both structure maps of `complexLoop`
are the identity of `ℂ`, so the square commutes on the nose.

@census none (G5.2 non-degenerate inhabitant of `RQ2-2.04`'s `EtaleSpecies.Hom`)
-/
noncomputable def complexLoopConj : EtaleSpecies.Hom complexLoop complexLoop where
  onI := fun i => i
  onL := fun _ => Complex.conjAe.toAlgHom
  onM := fun _ _ => Complex.conjAe.toAlgHom
  compat_left := fun _ _ => rfl
  compat_right := fun _ _ => rfl

/-- **G5.2 non-degeneracy** (`RQ2-2.04`): conjugation is **not** the identity morphism, so
`EtaleSpecies.Hom` has a closed inhabitant that is neither `Hom.id` nor a composite of identities
— finding F-M1-R-8's gap for `RQ2-2.04`.

@census none (G5.2 non-degeneracy witness for `RQ2-2.04`)
-/
theorem complexLoopConj_ne_id : complexLoopConj ≠ EtaleSpecies.Hom.id complexLoop := by
  intro h
  have h0 : complexLoopConj.onL PUnit.unit Complex.I
      = (EtaleSpecies.Hom.id complexLoop).onL PUnit.unit Complex.I := by rw [h]
  have h1 : (starRingEnd ℂ) Complex.I = Complex.I := h0
  norm_num [Complex.ext_iff] at h1

/-- **G5.2 (`EtaleSpecies.Hom`): a concrete morphism between two *different* species** — the split
one-node `ℝ`-species into the one-node `ℝ ⊂ ℂ` species, by `ℝ ↪ ℂ` on both the vertex field and
the edge algebra.  This exhibits a `Hom` that is not an endomorphism at all.

@census none (G5.2 non-degenerate inhabitant of `RQ2-2.04`)
-/
noncomputable def trivialToComplexLoop : EtaleSpecies.Hom (EtaleSpecies.trivial ℝ) complexLoop where
  onI := fun i => i
  onL := fun _ => Algebra.ofId ℝ ℂ
  onM := fun _ _ => Algebra.ofId ℝ ℂ
  compat_left := fun _ _ => rfl
  compat_right := fun _ _ => rfl

/-- **G5.2 non-degeneracy** (`RQ2-2.04`): its vertex-field component is not surjective, so it is not
an isomorphism — the hom-sets of `EtaleSpecies` are not groupoids, and the non-split witness
`complexLoop` really is *reached from* the split one.

@census none (G5.2 non-degeneracy witness for `RQ2-2.04`)
-/
theorem trivialToComplexLoop_onL_not_surjective :
    ¬ Function.Surjective (trivialToComplexLoop.onL PUnit.unit) := by
  intro hs
  obtain ⟨x, hx⟩ := hs Complex.I
  have hx' : (algebraMap ℝ ℂ) x = Complex.I := hx
  have := congrArg Complex.im hx'
  simp at this

end EtaleSpecies

end RationalQuivers
