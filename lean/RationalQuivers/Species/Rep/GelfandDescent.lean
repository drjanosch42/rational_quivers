import RationalQuivers.Species.Rep.Equivalence
import RationalQuivers.Species.Rep.Gelfand

/-!
# The descent formula for `S(Γ_K)`'s structure maps (§2.5, the support of `RQ2-2.37`)

Stage **S5**.  Added 2026-09-12 by coordinator ruling **`R-ERR-4`** (round-4 errata brief) as an
`R-PROC-4` amendment of the frozen stage.

## Why this module exists

Everything here was **proved in S9** (`Examples/Basic.lean`, the `SpeciesG4` section, 2026-09-07)
and is *about* S5: the general descent formula for a structure map `f_{ij}` of `S(Γ)`, and the two
structure maps of the Gelfand species `S(Γ_K)` written out at a general representation.  S9 needed
them for §6's five `…_speciesRep_eq` statements; `RQ2-2.37`'s clause `C3`
(`eq:gelfandspeciescomposite`) needs exactly the same three facts, and `RQ2-2.37` is an S5 row.
Since S9 is downstream of S5 and S8, neither could consume them where they were
(`stages/S5/DESIGN-NOTES.md` §71.5).  `R-ERR-4` relocates the minimal import-closure here.

Two things change in the lift, and nothing else does:

* the statements are **generalised from `ℚ ⊆ ℚ[√-1]` to an arbitrary quadratic Galois extension**
  `K ⊆ L` with `Nat.card Gal(L/K) = 2`.  That is forced, not chosen: `ℚ[√-1]` is S8's `Qi`
  (`Gelfand/GaloisFacts.lean`) and `Γ_ℚ` is S8's `gelfandQ` (v1's; since WP-10 the quiver is
  `Gelfand.RationalStructure.gelfandQ`, over every `E`; 2026-10-21 note, O-V2-6 round 2), so an S5
  module cannot mention either.
  The generic Gelfand quiver is S1's `RationalQuiver.gelfandOfCardTwo` and every orbit, stabilizer
  and edge-field fact it needs is already in S5's own `Species/Rep/Gelfand.lean` and S4's
  `Species/Examples.lean`;
* the `Unique`/`Fintype` instances on the two edge orbits, which S9 carries as instances at `Γ_ℚ`,
  are **instance-implicit arguments** here, so that S9's instantiations are the ones its own
  statements use.

`Examples/Basic.lean` keeps every relocated name, with its type unchanged, as a thin alias.

## Main results

* `edgeDescentOf_generator` — `f_{ij}(w ⊗ m) = ∑_ε ∑_η (η τ_ε⁻¹)(m_ε) · Φ_{ε,η}(w)`.
* `edgeDescentOf_uniqueOrbit` — the same when `E_{ij}` is a single orbit.
* `f_star_pm_generator` — `f_{{⋆}{±}}(w ⊗ m) = τ⁻¹(m) · Φ(w)`: one orbit, one coset.
* `f_pm_star_generator` — `f_{{±}{⋆}}(w ⊗ m) = τ⁻¹(m) · u + c(τ⁻¹(m)) · φ_{⋆,c}(u)`, the two
  Galois terms that are `eq:gelfandspeciescomposite`'s shape.
-/

namespace RationalQuivers

namespace GelfandDescent

open RationalQuiver RQuiver MulAction

/-! ## The general descent formula -/

section General

open scoped Classical

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {Γ : RationalQuiver K L}

/-- **The descent formula on a generator.**  `f_{ij}(w ⊗ m) = ∑_ε ∑_η (ητ_ε⁻¹)(m_ε)·Φ_{ε,η}(w)`,
read inside `M(v_j)`. 
@census none (helper; R-ERR-4 relocation) -/
theorem edgeDescentOf_generator (M : Rep Γ) (i j : Γ.VertexOrbit)
    [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε))]
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) :
    ((edgeDescentOf M i j (Balanced.mk w m) : M.M (Γ.vertexRep j)))
      = ∑ ε : Γ.EdgeOrbit i j, ∑ η : EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε),
          ((EdgeChoice.rep Γ (EdgeChoice.choose Γ ε) η * (EdgeChoice.choose Γ ε).τ⁻¹)
              ((m ε : L))) • phiComp M (EdgeChoice.choose Γ ε) η w := by
  have hM := isEdgeDescent_edgeDescentOf M i j
  have hval := hM.2 (phiTotal M (fun ε : Γ.EdgeOrbit i j => EdgeChoice.choose Γ ε))
    (phiTotal_single M _) (Balanced.mk w m) 1
  rw [phiTotal_e0_generator M _ _ hM.1 w m 1, one_smul] at hval
  rw [← hval]
  exact Finset.sum_congr rfl fun ε _ => Finset.sum_congr rfl fun η _ => by rw [one_mul]

/-- If every edge map of `M` vanishes, so does every descended structure map. 
@census none (helper; R-ERR-4 relocation) -/
theorem edgeDescentOf_eq_zero_of_edges (M : Rep Γ) (i j : Γ.VertexOrbit)
    (hzero : ∀ e : Γ.E, M.φEdge e = 0) : edgeDescentOf M i j = 0 := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j,
      Fintype (EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε)) :=
    fun ε => @Fintype.ofFinite _ (finite_cosetIndex (EdgeChoice.choose Γ ε))
  refine Balanced.hom_ext fun w m => ?_
  refine Subtype.ext ?_
  show ((edgeDescentOf M i j (Balanced.mk w m) : M.M (Γ.vertexRep j))) = _
  rw [edgeDescentOf_generator M i j w m]
  refine (Finset.sum_eq_zero fun ε _ => Finset.sum_eq_zero fun η _ => ?_).trans ?_
  · have hpc : phiComp M (EdgeChoice.choose Γ ε) η w = 0 := by
      show M.φ' _ (EdgeChoice.cosetTarget (EdgeChoice.choose Γ ε) η)
        (M.φEdge' (Γ.edgeRep ε) rfl rfl
          (M.φ' _ (EdgeChoice.sourceVertex (EdgeChoice.choose Γ ε)) (w : M.M _))) = 0
      rw [Rep.φEdge'_rfl, hzero]
      show M.φ' _ _ (0 : M.M _) = 0
      exact map_zero _
    rw [hpc, smul_zero]
  · rfl

/-- If every edge **from `i` to `j`** vanishes, so does `f_{ij}`. 
@census none (helper; R-ERR-4 relocation) -/
theorem edgeDescentOf_eq_zero_of_edgeSet (M : Rep Γ) (i j : Γ.VertexOrbit)
    (hzero : ∀ e : Γ.edgeSet i j, M.φEdge (e : Γ.E) = 0) : edgeDescentOf M i j = 0 := by
  classical
  letI : Fintype (Γ.EdgeOrbit i j) := Fintype.ofFinite _
  letI : ∀ ε : Γ.EdgeOrbit i j,
      Fintype (EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε)) :=
    fun ε => @Fintype.ofFinite _ (finite_cosetIndex (EdgeChoice.choose Γ ε))
  refine Balanced.hom_ext fun w m => ?_
  refine Subtype.ext ?_
  show ((edgeDescentOf M i j (Balanced.mk w m) : M.M (Γ.vertexRep j))) = _
  rw [edgeDescentOf_generator M i j w m]
  refine (Finset.sum_eq_zero fun ε _ => Finset.sum_eq_zero fun η _ => ?_).trans ?_
  · have hpc : phiComp M (EdgeChoice.choose Γ ε) η w = 0 := by
      show M.φ' _ (EdgeChoice.cosetTarget (EdgeChoice.choose Γ ε) η)
        (M.φEdge' (Γ.edgeRep ε) rfl rfl
          (M.φ' _ (EdgeChoice.sourceVertex (EdgeChoice.choose Γ ε)) (w : M.M _))) = 0
      rw [Rep.φEdge'_rfl, show M.φEdge (Γ.edgeRep ε) = 0 from hzero (Quotient.out ε)]
      show M.φ' _ _ (0 : M.M _) = 0
      exact map_zero _
    rw [hpc, smul_zero]
  · rfl

/-- When the target vertex has trivial stabilizer, the coset system is a point. 
@census none (helper; R-ERR-4 relocation) -/
theorem rep_eq_one {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    (h : MulAction.stabilizer Gal(L/K) (Γ.vertexRep j) = ⊥)
    (η : EdgeChoice.CosetIndex Γ ch) : EdgeChoice.rep Γ ch η = 1 := by
  have hx : EdgeChoice.rep Γ ch η ∈ MulAction.stabilizer Gal(L/K) (Γ.vertexRep j) :=
    (Quotient.out η).2
  rw [h] at hx
  exact Subgroup.mem_bot.mp hx

/-- `cosetIndex_subsingleton`.  @census none (helper; R-ERR-4 relocation) -/
theorem cosetIndex_subsingleton {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j} (ch : Γ.EdgeChoice ε)
    (h : MulAction.stabilizer Gal(L/K) (Γ.vertexRep j) = ⊥) :
    Subsingleton (EdgeChoice.CosetIndex Γ ch) := by
  haveI : Subsingleton ↥(MulAction.stabilizer Gal(L/K) (Γ.vertexRep j)) := by
    rw [h]; infer_instance
  exact ⟨Quotient.ind fun a => Quotient.ind fun b => congrArg _ (Subsingleton.elim a b)⟩

/-- The descent formula when there is exactly one edge orbit from `i` to `j`. 
@census none (helper; R-ERR-4 relocation) -/
theorem edgeDescentOf_uniqueOrbit (M : Rep Γ) (i j : Γ.VertexOrbit)
    [Unique (Γ.EdgeOrbit i j)] [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε))]
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (m : Γ.toSpecies.M i j) :
    ((edgeDescentOf M i j (Balanced.mk w m) : M.M (Γ.vertexRep j)))
      = ∑ η : EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)),
          ((EdgeChoice.rep Γ (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)) η
              * (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).τ⁻¹)
            ((m default : L))) • phiComp M (EdgeChoice.choose Γ default) η w := by
  rw [edgeDescentOf_generator M i j w m]
  exact Finset.sum_eq_single default (fun b _ hb => absurd (Subsingleton.elim b default) hb)
    (fun hb => absurd (Finset.mem_univ (default : Γ.EdgeOrbit i j)) hb)

/-- `phiComp_eq`.  @census none (helper; R-ERR-4 relocation) -/
theorem phiComp_eq (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) :
    phiComp M ch η w
      = M.φ' (EdgeChoice.rep Γ ch η * ch.τ⁻¹) (ch.cosetTarget η)
        (M.φEdge (Γ.edgeRep ε) (M.φ' ch.σ ch.sourceVertex (w : M.M (Γ.vertexRep i)))) := rfl

/-- `Φ_{ε,η}` is injective as soon as the edge map is: the two other factors are bijections. 
@census none (helper; R-ERR-4 relocation) -/
theorem phiComp_ne_zero (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (w : ↥(M.vertexFixed (Γ.vertexRep i))) (hw : (w : M.M (Γ.vertexRep i)) ≠ 0)
    (hinj : Function.Injective (M.φEdge (Γ.edgeRep ε))) : phiComp M ch η w ≠ 0 := by
  rw [phiComp_eq]
  intro h
  have h1 := (AddEquiv.map_eq_zero_iff
    (M.φ' (EdgeChoice.rep Γ ch η * ch.τ⁻¹) (ch.cosetTarget η))).mp h
  have h2 : M.φ' ch.σ ch.sourceVertex (w : M.M (Γ.vertexRep i)) = 0 :=
    hinj (by rw [h1, map_zero])
  exact hw ((AddEquiv.map_eq_zero_iff (M.φ' ch.σ ch.sourceVertex)).mp h2)

/-- `Φ_{ε,η}` split as `φ_{rep η} ∘ φ_{τ⁻¹} ∘ φ_e ∘ φ_σ`. 
@census none (helper; R-ERR-4 relocation) -/
theorem phiComp_split (M : Rep Γ) {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε) (η : EdgeChoice.CosetIndex Γ ch)
    (w : ↥(M.vertexFixed (Γ.vertexRep i)))
    (hst : EdgeChoice.rep Γ ch η • Γ.vertexRep j = Γ.vertexRep j) :
    phiComp M ch η w
      = M.φ' (EdgeChoice.rep Γ ch η) hst
          (M.φ' ch.τ⁻¹ ch.inv_smul_target
            (M.φEdge (Γ.edgeRep ε) (M.φ' ch.σ ch.sourceVertex (w : M.M (Γ.vertexRep i))))) := by
  rw [phiComp_eq]
  exact (M.φ'_comp _ _ ch.inv_smul_target hst (ch.cosetTarget η) _).symm

end General


section GalUniv

open scoped Classical

/-- Every element of a Galois group of order two is `1` or `z`.  @census none (helper) -/
theorem gal_univ_of_card_two {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [Fintype Gal(L/K)] (hcard : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1) :
    (Finset.univ : Finset Gal(L/K)) = {1, z} := by
  classical
  ext σ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  by_cases hσ : σ = 1
  · exact Or.inl hσ
  · refine Or.inr ?_
    obtain ⟨w, -, hu⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp hcard
    rw [hu σ hσ, ← hu z hz]

end GalUniv

/-! ## The Gelfand quiver `Γ_K` of a quadratic Galois extension

Everything below is `Examples/Basic.lean`'s `SpeciesG4` material with `ℚ ⊆ ℚ[√-1]` replaced by an
arbitrary `K ⊆ L` with `Nat.card Gal(L/K) = 2`.  The quiver is S1's `gelfandOfCardTwo`; its
orbit, stabilizer and edge-field facts are S4's (`Species/Examples.lean`) and S5's own
(`Species/Rep/Gelfand.lean`).
-/

section Gelfand

open scoped Classical

open Examples

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
  (h : Nat.card Gal(L/K) = 2)

/-- `Γ_K`, the `K`-rational Gelfand quiver.  @census none (helper) -/
noncomputable abbrev GΓ : RationalQuiver K L := gelfandOfCardTwo K L h

/-- The node `{⋆}` of the étale `K`-species `S(Γ_K)`.  @census none (helper) -/
noncomputable abbrev starNode : (GΓ K L h).toSpecies.I :=
  (GΓ K L h).vertexClass (gelfandVertex K L h 1)

/-- The node `{+,−}` of the étale `K`-species `S(Γ_K)`.  @census none (helper) -/
noncomputable abbrev pmNode : (GΓ K L h).toSpecies.I :=
  (GΓ K L h).vertexClass (gelfandVertex K L h 0)

/-- `star_ne_pm`.  @census none (helper; R-ERR-4 relocation) -/
theorem star_ne_pm : (starNode K L h) ≠ pmNode K L h :=
  gelfand_vertexClass_star_ne K L h

/-- `vertexClass_0`.  @census none (helper; R-ERR-4 relocation) -/
theorem vertexClass_0 : (GΓ K L h).vertexClass (gelfandVertex K L h 0) = pmNode K L h := rfl
/-- `vertexClass_1`.  @census none (helper; R-ERR-4 relocation) -/
theorem vertexClass_1 : (GΓ K L h).vertexClass (gelfandVertex K L h 1) = starNode K L h := rfl
/-- `vertexClass_2`.  @census none (helper; R-ERR-4 relocation) -/
theorem vertexClass_2 : (GΓ K L h).vertexClass (gelfandVertex K L h 2) = pmNode K L h :=
  gelfand_vertexClass_two K L h

/-- `fin4_cases`.  @census none (helper; R-ERR-4 relocation) -/
theorem fin4_cases : ∀ e : Fin 4, e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by decide

/-- `edgeSet_star_pm`.  @census none (helper; R-ERR-4 relocation) -/
theorem edgeSet_star_pm (e : (GΓ K L h).edgeSet (starNode K L h) (pmNode K L h)) :
    (e : (GΓ K L h).E) = gelfandEdge K L h 1 ∨ (e : (GΓ K L h).E) = gelfandEdge K L h 3 := by
  obtain ⟨e, hs, ht⟩ := e
  rcases fin4_cases e with rfl | rfl | rfl | rfl
  · exact absurd (by rw [← hs]; exact vertexClass_0 K L h) (star_ne_pm K L h)
  · exact Or.inl rfl
  · exact absurd (by rw [← hs]; exact vertexClass_2 K L h) (star_ne_pm K L h)
  · exact Or.inr rfl

/-- `edgeSet_pm_star`.  @census none (helper; R-ERR-4 relocation) -/
theorem edgeSet_pm_star (e : (GΓ K L h).edgeSet (pmNode K L h) (starNode K L h)) :
    (e : (GΓ K L h).E) = gelfandEdge K L h 0 ∨ (e : (GΓ K L h).E) = gelfandEdge K L h 2 := by
  obtain ⟨e, hs, ht⟩ := e
  rcases fin4_cases e with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd (by rw [← ht]; exact vertexClass_0 K L h) (star_ne_pm K L h)
  · exact Or.inr rfl
  · exact absurd (by rw [← ht]; exact vertexClass_2 K L h) (star_ne_pm K L h)

/-- The arrow `b₋ : ⋆ → −` as an element of `E_{{⋆},{±}}`. 
@census none (helper; R-ERR-4 relocation) -/
noncomputable def eStarPm : (GΓ K L h).edgeSet (starNode K L h) (pmNode K L h) :=
  ⟨gelfandEdge K L h 1, rfl, rfl⟩

/-- The arrow `a₋ : − → ⋆` as an element of `E_{{±},{⋆}}`. 
@census none (helper; R-ERR-4 relocation) -/
noncomputable def ePmStar : (GΓ K L h).edgeSet (pmNode K L h) (starNode K L h) :=
  ⟨gelfandEdge K L h 0, rfl, rfl⟩

omit [IsGalois K L] [FiniteDimensional K L] in
include h in
/-- The non-identity element of `Gal(L/K)`, from `Nat.card Gal(L/K) = 2`.
@census none (helper) -/
theorem exists_ne_one : ∃ z : Gal(L/K), z ≠ 1 := by
  obtain ⟨w, hw, -⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
  exact ⟨w, hw⟩

/-- `edgeOrbit_star_pm_subsingleton`.  @census none (helper; R-ERR-4 relocation) -/
theorem edgeOrbit_star_pm_subsingleton :
    Subsingleton ((GΓ K L h).EdgeOrbit (starNode K L h) (pmNode K L h)) := by
  obtain ⟨z, hz⟩ := exists_ne_one K L h
  refine ⟨Quotient.ind fun a => Quotient.ind fun b => Quotient.sound ?_⟩
  have key : ∀ x y : (GΓ K L h).edgeSet (starNode K L h) (pmNode K L h),
      ((x : (GΓ K L h).E) = gelfandEdge K L h 1 ∨ (x : (GΓ K L h).E) = gelfandEdge K L h 3) →
      ((y : (GΓ K L h).E) = gelfandEdge K L h 1 ∨ (y : (GΓ K L h).E) = gelfandEdge K L h 3) →
      x ∈ MulAction.orbit Gal(L/K) y := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact ⟨1, Subtype.ext (by rw [RationalQuiver.coe_smul_edgeSet, one_smul, hy, hx])⟩
    · exact ⟨z, Subtype.ext (by
        rw [RationalQuiver.coe_smul_edgeSet, hy, gelfand_smul_edge K L h hz, hx]; rfl)⟩
    · exact ⟨z, Subtype.ext (by
        rw [RationalQuiver.coe_smul_edgeSet, hy, gelfand_smul_edge K L h hz, hx]; rfl)⟩
    · exact ⟨1, Subtype.ext (by rw [RationalQuiver.coe_smul_edgeSet, one_smul, hy, hx])⟩
  exact key a b (edgeSet_star_pm K L h a) (edgeSet_star_pm K L h b)

/-- `edgeOrbit_pm_star_subsingleton`.  @census none (helper; R-ERR-4 relocation) -/
theorem edgeOrbit_pm_star_subsingleton :
    Subsingleton ((GΓ K L h).EdgeOrbit (pmNode K L h) (starNode K L h)) := by
  obtain ⟨z, hz⟩ := exists_ne_one K L h
  refine ⟨Quotient.ind fun a => Quotient.ind fun b => Quotient.sound ?_⟩
  have key : ∀ x y : (GΓ K L h).edgeSet (pmNode K L h) (starNode K L h),
      ((x : (GΓ K L h).E) = gelfandEdge K L h 0 ∨ (x : (GΓ K L h).E) = gelfandEdge K L h 2) →
      ((y : (GΓ K L h).E) = gelfandEdge K L h 0 ∨ (y : (GΓ K L h).E) = gelfandEdge K L h 2) →
      x ∈ MulAction.orbit Gal(L/K) y := by
    intro x y hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact ⟨1, Subtype.ext (by rw [RationalQuiver.coe_smul_edgeSet, one_smul, hy, hx])⟩
    · exact ⟨z, Subtype.ext (by
        rw [RationalQuiver.coe_smul_edgeSet, hy, gelfand_smul_edge K L h hz, hx]; rfl)⟩
    · exact ⟨z, Subtype.ext (by
        rw [RationalQuiver.coe_smul_edgeSet, hy, gelfand_smul_edge K L h hz, hx]; rfl)⟩
    · exact ⟨1, Subtype.ext (by rw [RationalQuiver.coe_smul_edgeSet, one_smul, hy, hx])⟩
  exact key a b (edgeSet_pm_star K L h a) (edgeSet_pm_star K L h b)

/-- `stabilizer_pm`.  @census none (helper; R-ERR-4 relocation) -/
theorem stabilizer_pm :
    MulAction.stabilizer Gal(L/K) ((GΓ K L h).vertexRep (pmNode K L h)) = ⊥ :=
  stabilizer_eq_bot_of_mem_orbit
    (MulAction.mem_orbit_symm.mp ((GΓ K L h).mem_orbit_vertexRep (gelfandVertex K L h 0)))
    (stabilizer_gelfandVertex_eq_bot K L h 0 (by decide))

/-- `stabilizer_star`.  @census none (helper; R-ERR-4 relocation) -/
theorem stabilizer_star :
    MulAction.stabilizer Gal(L/K) ((GΓ K L h).vertexRep (starNode K L h)) = ⊤ :=
  stabilizer_eq_top_of_mem_orbit
    (MulAction.mem_orbit_symm.mp ((GΓ K L h).mem_orbit_vertexRep (gelfandVertex K L h 1)))
    (stabilizer_gelfandVertex_star K L h)

/-- `edgeOrbitField_top`.  @census none (helper; R-ERR-4 relocation) -/
theorem edgeOrbitField_top {i j : (GΓ K L h).VertexOrbit} (ε : (GΓ K L h).EdgeOrbit i j) :
    (GΓ K L h).edgeOrbitField ε = ⊤ :=
  gelfand_edgeOrbitField K L h ε

end Gelfand

/-! ## The structure maps of `S(Γ)` at a single edge orbit, at a general `M`

`Examples/Basic.lean`'s `Concrete` section, generalised — and the generalisation is **away from the
Gelfand quiver**, not merely away from `ℚ ⊆ ℚ[√-1]`.  Each of the two shapes the Gelfand species
exhibits is proved here for an arbitrary `Γ`, with the Gelfand-specific input as a *hypothesis*:

* `f_uniqueOrbit_generator` — one edge orbit, **trivial** stabilizer at the target
  (`Γ_K`'s `{⋆} → {±}`);
* `f_twoTerm_generator` — one edge orbit, **full** stabilizer at the target and trivial edge
  stabilizers, over a quadratic Galois group (`Γ_K`'s `{±} → {⋆}`), giving the two Galois terms.

That is what makes the S9 aliases free: they instantiate `Γ := Γ_ℚ` and feed in S9's own
`stabilizer_pm` / `stabilizer_star` / `gelfand_stabilizer_E`, so nothing in the alias has to unfold
v1's `gelfandQ` (`Gelfand/Equivalence.lean`, deleted at WP-13, `ae9eda9`; since WP-10 the quiver is
`Gelfand.RationalStructure.gelfandQ` in `Gelfand/RationalStructure/Phi.lean`; 2026-10-21 note,
O-V2-6 round 2).

The two elaboration budgets are S9's, carried over verbatim and disclosed for the same reason: the
hot spot is the instance `Module ↥(stabField K L v) ↥(M.vertexFixed v)`.  They are *resource*
limits; the axiom closure is unaffected.
-/

section Concrete

open scoped Classical

open RationalQuiver MulAction

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]
  {Γ : RationalQuiver K L}

/-- The underlying vector of an element of `W_i`. 
@census none (helper; R-ERR-4 relocation) -/
def wv (M : RationalQuiver.FDRep Γ) (i : Γ.toSpecies.I)
    (w : ((RationalQuiver.FFunctor Γ).obj M).W i) : M.toRep.M (Γ.vertexRep i) :=
  (show ↥(M.toRep.vertexFixed (Γ.vertexRep i)) from w).val

/-- `wv_inj`.  @census none (helper; R-ERR-4 relocation) -/
theorem wv_inj (M : RationalQuiver.FDRep Γ) (i : Γ.toSpecies.I)
    {a b : ((RationalQuiver.FFunctor Γ).obj M).W i} (hab : wv M i a = wv M i b) : a = b :=
  Subtype.ext hab

/-- `wv_zero`.  @census none (helper; R-ERR-4 relocation) -/
theorem wv_zero (M : RationalQuiver.FDRep Γ) (i : Γ.toSpecies.I) :
    wv M i (0 : ((RationalQuiver.FFunctor Γ).obj M).W i) = 0 := rfl

/-- The balanced product `W_i ⊗_{L_i} {}_iM_j`. 
@census none (helper; R-ERR-4 relocation) -/
noncomputable abbrev Ten (M : RationalQuiver.FDRep Γ) (i j : Γ.toSpecies.I) : Type :=
  Γ.toSpecies.toSpecies.RepTensor i j (((RationalQuiver.FFunctor Γ).obj M).W i)

/-- The generator `w ⊗ m`. 
@census none (helper; R-ERR-4 relocation) -/
noncomputable abbrev tmk (M : RationalQuiver.FDRep Γ) (i j : Γ.toSpecies.I)
    (w : ((RationalQuiver.FFunctor Γ).obj M).W i) (m : Γ.toSpecies.toSpecies.M i j) :
    Ten M i j := Balanced.mk w m

/-! ### One orbit, trivial stabilizer at the target -/

/-- **`f_{ij}` when `E_{ij}` is a single orbit and `G_{v_j} = 1`**: one term, one coset.
This is `Γ_K`'s `{⋆} → {±}` map. 
@census none (helper; R-ERR-4 relocation) -/
theorem f_uniqueOrbit_generator (M : RationalQuiver.FDRep Γ) (i j : Γ.toSpecies.I)
    [Unique (Γ.EdgeOrbit i j)] [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε))]
    (hstab : MulAction.stabilizer Gal(L/K) (Γ.vertexRep j) = ⊥)
    (w : ((RationalQuiver.FFunctor Γ).obj M).W i) (m : Γ.toSpecies.toSpecies.M i j)
    (η₀ : EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j))) :
    wv M j (((RationalQuiver.FFunctor Γ).obj M).f i j (tmk M i j w m))
      = (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).τ⁻¹ ((m default : L))
          • phiComp M.toRep (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)) η₀ w := by
  haveI hsub := cosetIndex_subsingleton (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)) hstab
  have hh := edgeDescentOf_uniqueOrbit M.toRep i j w m
  rw [Finset.sum_eq_single η₀ (fun b _ hb => absurd (Subsingleton.elim b η₀) hb)
    (fun hb => absurd (Finset.mem_univ η₀) hb), rep_eq_one _ hstab η₀, one_mul] at hh
  exact hh

/-! ### One orbit, full stabilizer at the target -/

omit [IsGalois K L] in
/-- With `G_{v_j} = G`, every `σ ∈ G` fixes `v_j`. 
@census none (helper; R-ERR-4 relocation) -/
theorem stab_all_of_stab_top {j : Γ.VertexOrbit}
    (hstab : MulAction.stabilizer Gal(L/K) (Γ.vertexRep j) = ⊤) (σ : Gal(L/K)) :
    σ • Γ.vertexRep j = Γ.vertexRep j := by
  have hm : σ ∈ MulAction.stabilizer Gal(L/K) (Γ.vertexRep j) := by rw [hstab]; trivial
  exact hm

/-- `η ↦ rep η` is a bijection from the coset system onto `G` when `G_{v_j} = G` and the edge
stabilizers are trivial. 
@census none (helper; R-ERR-4 relocation) -/
theorem rep_bijective_of_stab_top {i j : Γ.VertexOrbit} {ε : Γ.EdgeOrbit i j}
    (ch : Γ.EdgeChoice ε)
    (hstab : MulAction.stabilizer Gal(L/K) (Γ.vertexRep j) = ⊤)
    (hedge : ∀ e : Γ.E, MulAction.stabilizer Gal(L/K) e = ⊥) :
    Function.Bijective (fun η : EdgeChoice.CosetIndex Γ ch => EdgeChoice.rep Γ ch η) := by
  constructor
  · intro a b hab
    exact Quotient.out_injective (Subtype.ext hab)
  · intro σ
    have hσ : σ ∈ MulAction.stabilizer Gal(L/K) (Γ.vertexRep j) := by rw [hstab]; trivial
    refine ⟨Quotient.mk _ ⟨σ, hσ⟩, ?_⟩
    have hrel := Quotient.mk_out (s := QuotientGroup.leftRel
      ((MulAction.stabilizer Gal(L/K) (ch.τ⁻¹ • Γ.edgeRep ε)).subgroupOf
        (MulAction.stabilizer Gal(L/K) (Γ.vertexRep j))))
      (⟨σ, hσ⟩ : MulAction.stabilizer Gal(L/K) (Γ.vertexRep j))
    rw [QuotientGroup.leftRel_apply] at hrel
    have hmem := Subgroup.mem_subgroupOf.mp hrel
    have hbot := hedge (ch.τ⁻¹ • Γ.edgeRep ε)
    rw [Subgroup.eq_bot_iff_forall] at hbot
    have h1 := hbot _ hmem
    show (EdgeChoice.rep Γ ch (Quotient.mk _
      (⟨σ, hσ⟩ : MulAction.stabilizer Gal(L/K) (Γ.vertexRep j)))) = σ
    exact inv_mul_eq_one.mp h1

/-- The vector `φ_{τ⁻¹} φ_e φ_σ (w)` in `M(v_j)` that the descended map traces. 
@census none (helper; R-ERR-4 relocation) -/
noncomputable def uPS (M : RationalQuiver.FDRep Γ) (i j : Γ.toSpecies.I)
    [Unique (Γ.EdgeOrbit i j)] (w : ((RationalQuiver.FFunctor Γ).obj M).W i) :
    M.toRep.M (Γ.vertexRep j) :=
  M.toRep.φ' (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).τ⁻¹
      (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).inv_smul_target
    (M.toRep.φEdge (Γ.edgeRep (default : Γ.EdgeOrbit i j))
      (M.toRep.φ' (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).σ
        (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).sourceVertex (wv M i w)))

/-- `uPS_def`.  @census none (helper; R-ERR-4 relocation) -/
theorem uPS_def (M : RationalQuiver.FDRep Γ) (i j : Γ.toSpecies.I)
    [Unique (Γ.EdgeOrbit i j)] (w : ((RationalQuiver.FFunctor Γ).obj M).W i) :
    uPS M i j w = M.toRep.φ' (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).τ⁻¹
        (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).inv_smul_target
      (M.toRep.φEdge (Γ.edgeRep (default : Γ.EdgeOrbit i j))
        (M.toRep.φ' (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).σ
          (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).sourceVertex (wv M i w))) := rfl

/-- **`f_{ij}` when `E_{ij}` is a single orbit, `G_{v_j} = G` of order two and the edge stabilizers
are trivial**: the two Galois terms.  This is `Γ_K`'s `{±} → {⋆}` map, and the shape of
`eq:gelfandspeciescomposite`. 
@census none (helper; R-ERR-4 relocation) -/
theorem f_twoTerm_generator (M : RationalQuiver.FDRep Γ) (i j : Γ.toSpecies.I)
    [Unique (Γ.EdgeOrbit i j)] [Fintype (Γ.EdgeOrbit i j)]
    [∀ ε : Γ.EdgeOrbit i j, Fintype (EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ ε))]
    [Fintype Gal(L/K)]
    (hstab : MulAction.stabilizer Gal(L/K) (Γ.vertexRep j) = ⊤)
    (hedge : ∀ e : Γ.E, MulAction.stabilizer Gal(L/K) e = ⊥)
    (hcard : Nat.card Gal(L/K) = 2) {z : Gal(L/K)} (hz : z ≠ 1)
    (w : ((RationalQuiver.FFunctor Γ).obj M).W i) (m : Γ.toSpecies.toSpecies.M i j) :
    wv M j (((RationalQuiver.FFunctor Γ).obj M).f i j (tmk M i j w m))
      = (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).τ⁻¹ ((m default : L))
          • uPS M i j w
        + z ((EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).τ⁻¹ ((m default : L)))
          • M.toRep.φ' z (stab_all_of_stab_top hstab z) (uPS M i j w) := by
  have hh := edgeDescentOf_uniqueOrbit M.toRep i j w m
  rw [Fintype.sum_bijective
      (fun η : EdgeChoice.CosetIndex Γ (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)) =>
        EdgeChoice.rep Γ (EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)) η)
      (rep_bijective_of_stab_top _ hstab hedge) _
      (fun σ : Gal(L/K) =>
        σ ((EdgeChoice.choose Γ (default : Γ.EdgeOrbit i j)).τ⁻¹ ((m default : L)))
          • M.toRep.φ' σ (stab_all_of_stab_top hstab σ) (uPS M i j w))
      (fun η => by
        rw [phiComp_split M.toRep _ η w (stab_all_of_stab_top hstab _), AlgEquiv.mul_apply]
        rfl),
    gal_univ_of_card_two hcard hz, Finset.sum_pair (Ne.symm hz)] at hh
  have h1 : M.toRep.φ' (1 : Gal(L/K)) (stab_all_of_stab_top hstab 1) (uPS M i j w)
      = uPS M i j w :=
    (M.toRep.φ'_one (stab_all_of_stab_top hstab 1) (uPS M i j w)).trans
      (M.toRep.eqCast_rfl _ (uPS M i j w))
  rw [h1] at hh
  exact hh

end Concrete

end GelfandDescent

end RationalQuivers
