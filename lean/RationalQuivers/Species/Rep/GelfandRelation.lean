import RationalQuivers.Species.Rep.GelfandDescent
import RationalQuivers.Species.Rep.Relations

/-!
# `R_Gelfand`, the species-side relation of `ex:gelfandspeciesrelation` (census `RQ2-2.37`)

Stage **S5**.  Added 2026-09-12 by the round-4 errata brief under coordinator ruling `R-ERR-4`, as
an `R-PROC-4` amendment of the frozen stage.

## What this module does

*(Retitled 2026-09-13, `R-PROC-4` amendment, `O-ERR-4`.  Until round 5 of the errata amendment,
2026-09-12, this heading read "What this module does, and what it does NOT do", and its second
half had a referent: clauses `C3` and `C4` were not yet proved here (the superseded paragraph
below quotes that wording).  Round 5 proved `C3` (`exists_beta`, `satisfies_RGelfand_iff_relation`)
and `C4` (`satisfies_RGelfand_iff_pair`, `RGelfand_genuine`) and added the coincidence theorem
(`repNilRel_RGelfand_iff`, landed at `daecc3f`), so the module now renders all four clauses and
the "does NOT do" half has no referent left — `R-PROC-1` layer-2 review 2b §7 item 5, second
instance (`V-ERR2b-3`).  The retitle is the whole repair; the paragraph below was already
corrected by round 5.)*

The author's **option-(b)** ruling on `AN-33(iii)` (2026-09-11) added two environments to §2.5.
`def:speciesrelations` (census `RQ2-2.36`) landed in round 3 as `Species/Rep/Relations.lean`.  This
module renders the second, `ex:gelfandspeciesrelation` (census `RQ2-2.37`), in two instalments —
round 4 (`C1`, `C2`) and round 5 (`C3`, `C4`, the coincidence theorem):

* **clause `C1`** — `{}_⋆M_p = {}_⋆M_± ⊗_{L_±} {}_±M_⋆ ≅ L`, a `K`-vector space of **dimension 2**.
  `thetaEquiv` is the identification and `finrank_pathBimod` the dimension.
* **clause `C2`** — `R_Gelfand`, the relation whose only non-zero member is the `K`-line
  `(R_Gelfand)_p := K·α ⊆ {}_⋆M_p` (`RGelfand`; `theta_relGen` says the line is `θ⁻¹(K·α)`).  At
  `K = ℚ`, `L = ℚ[√-1]`, `α = √-1` this is the source's `ℚ·√-1`.
* the condition `R_Gelfand` cuts out, `satisfies_RGelfand_iff`, which is what the proof of clause
  `C3` evaluates.

* **clause `C3`** — `eq:gelfandspeciescomposite` and the iff.  **Added 2026-09-12, round 5**
  (coordinator ruling `R-ERR-5`): `exists_beta` is the formula, read through the identification
  `β ∘ θ` for a single `β ∈ Gal(L/K)` fixed by the tree's choice of representatives, and
  `satisfies_RGelfand_iff_relation` is *"`F(M)` satisfies `R_Gelfand` iff `M` satisfies
  `a₋b₋ = a₊b₊`"*, stated exactly as printed.  It is the module's `@census RQ2-2.37` claimant.
* **clause `C4`** — `satisfies_RGelfand_iff_pair` (a single species relation for the pair of
  `c`-conjugate quiver relations) and `RGelfand_genuine` (a genuine condition: equivariance gives
  only the conjugacy, and a nilpotent `M` refutes the equality).
* **the coincidence theorem** `repNilRel_RGelfand_iff`: the intrinsic `Rep^nil(S(Γ_K), R_Gelfand)`
  is the category S8 had transported through `F`.  This is what let v1's S8 restate `RQ-5.06-C1`
  against the intrinsic target (`Gelfand/Corollaries.lean`, `species_equivalence_intrinsic`).
  *(2026-10-21, O-V2-6 round 2.)* That file was deleted with the v1 Q-chain at WP-13 (`ae9eda9`). On
  the v2 line `Gelfand.Species.repNilRel_RE_iff` (`Gelfand/Species/Equivalence.lean`) consumes the
  coincidence theorem, and `RQ2-5.06`'s claimant `Gelfand.Species.species_equivalence_intrinsic`
  (`Gelfand/Species/Rational.lean`) is stated against the intrinsic target.

**Superseded (round 4, 2026-09-12, same date, earlier):** *"Clause `C3` … is NOT proved here, and
neither is clause `C4`.  `RQ2-2.37` is therefore not claimed."*  Both are proved below and
`RQ2-2.37` is claimed with all four clauses cited; `stages/S5/DESIGN-NOTES.md` §72.4 is the record
of the goal state round 4 reached and §73 of how round 5 closed it.

## The identification, and why it carries a twist

`{}_⋆M_± = ∏_ε L(ε)` over the single `{⋆}→{±}` edge orbit, and every Gelfand edge-orbit field is
`L` (`gelfand_edgeOrbitField`); likewise `{}_±M_⋆`, while `L_± = L` and `L_⋆ = K`.  So all three
factors evaluate to `L`, and `{}_⋆M_p` is `L ⊗_L L ≅ L`.  The one thing that is **not** free is
that `L_±` acts on the right of `{}_⋆M_±` and on the left of `{}_±M_⋆` through two *different*
embeddings `L_± ↪ L` — `edgeComponentRight` and `edgeComponentLeft`, each carrying its own chosen
Galois element.  `GTw = ρX ∘ ρY⁻¹` is the automorphism of `L` that reconciles them, and
`thetaBil_bal` — the balanced condition — is exactly `GTw ∘ ρY = ρX`.
-/

namespace RationalQuivers

namespace GelfandRelation

open RationalQuiver RQuiver MulAction Examples GelfandDescent Species
open scoped Classical

section Transport

/-! ### Transport algebra — generic `eqCast` bookkeeping, proved by `subst`

Each lemma is stated at *variable* vertices so that `subst` closes it, and is then applied at the
tree's chosen representatives (`vertexRep`, `edgeRep`, `Quotient.out`-defined), which cannot be
substituted.  This is the whole cost of the source's *"choosing `−` as the representative …"*,
which the tree cannot make (`R-ERR-5`). -/

variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] {Γ : RationalQuiver K L}

omit [IsGalois K L] in
/-- `eqCast_trans`.  @census none (helper; RQ2-2.37 support) -/
theorem eqCast_trans (M : Rep Γ) {u v w : Γ.V} (h₁ : u = v) (h₂ : v = w) (m : M.M u) :
    M.eqCast h₂ (M.eqCast h₁ m) = M.eqCast (h₁.trans h₂) m := by
  subst h₁; subst h₂; rfl

omit [IsGalois K L] in
/-- `eqCast_symm_apply'`.  @census none (helper; RQ2-2.37 support) -/
theorem eqCast_symm_apply' (M : Rep Γ) {v w : Γ.V} (h : v = w) (m : M.M v) :
    M.eqCast h.symm (M.eqCast h m) = m := by subst h; rfl

omit [IsGalois K L] in
/-- `φEdge_eqCast`.  @census none (helper; RQ2-2.37 support) -/
theorem φEdge_eqCast (M : Rep Γ) (e : Γ.E) {a : Γ.V} (h : a = Γ.toRQuiver.source e)
    (m : M.M a) : M.φEdge e (M.eqCast h m) = M.φEdge' e h.symm rfl m := by subst h; rfl

omit [IsGalois K L] in
/-- `φ'_eqCast`.  @census none (helper; RQ2-2.37 support) -/
theorem φ'_eqCast (M : Rep Γ) (σ : Gal(L/K)) {u v w : Γ.V} (h : u = v) (hσ : σ • v = w)
    (hσ' : σ • u = w) (m : M.M u) : M.φ' σ hσ (M.eqCast h m) = M.φ' σ hσ' m := by subst h; rfl

omit [IsGalois K L] in
/-- `eqCast_φ'`.  @census none (helper; RQ2-2.37 support) -/
theorem eqCast_φ' (M : Rep Γ) (σ : Gal(L/K)) {u v w : Γ.V} (hσ : σ • u = v) (h : v = w)
    (hσ' : σ • u = w) (m : M.M u) : M.eqCast h (M.φ' σ hσ m) = M.φ' σ hσ' m := by subst h; rfl

omit [IsGalois K L] in
/-- `mem_vertexFixed_eqCast`.  @census none (helper; RQ2-2.37 support) -/
theorem mem_vertexFixed_eqCast (M : Rep Γ) {v w : Γ.V} (h : v = w) {m : M.M v}
    (hm : m ∈ M.vertexFixed v) : M.eqCast h m ∈ M.vertexFixed w := by subst h; exact hm

omit [IsGalois K L] in
/-- A `G_v`-fixed vector is moved by `φ'_σ` only through transport.
@census none (helper; RQ2-2.37 support) -/
theorem φ'_of_mem_vertexFixed (M : Rep Γ) {v w : Γ.V} {m : M.M v} (hm : m ∈ M.vertexFixed v)
    (σ : Gal(L/K)) (hσv : σ • v = v) (hσ : σ • v = w) :
    M.φ' σ hσ m = M.eqCast (hσv.symm.trans hσ) m := by
  have h1 : M.φ' σ hσv m = m := hm ⟨σ, hσv⟩
  subst hσ
  rw [Rep.φ'_rfl]
  have h2 := congrArg (M.eqCast hσv.symm) h1
  rw [Rep.φ'_apply, eqCast_symm_apply'] at h2
  exact h2

end Transport

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
  (h : Nat.card Gal(L/K) = 2)

/-- `ES`.  @census none (helper; RQ2-2.37 support) -/
noncomputable abbrev ES : RationalQuivers.EtaleSpecies K := (GΓ K L h).toSpecies
/-- `SG`.  @census none (helper; RQ2-2.37 support) -/
noncomputable abbrev SG : RationalQuivers.Species K := (GΓ K L h).toSpecies.toSpecies

/-- `nStar`.  @census none (helper; RQ2-2.37 support) -/
noncomputable abbrev nStar : (ES K L h).I := starNode K L h
/-- `nPm`.  @census none (helper; RQ2-2.37 support) -/
noncomputable abbrev nPm : (ES K L h).I := pmNode K L h

/-- `uSP`.  @census none (helper; RQ2-2.37 support) -/
noncomputable instance uSP : Unique ((GΓ K L h).EdgeOrbit (starNode K L h) (pmNode K L h)) :=
  @Unique.mk' _ ⟨Quotient.mk _ (eStarPm K L h)⟩ (edgeOrbit_star_pm_subsingleton K L h)

/-- `uPSo`.  @census none (helper; RQ2-2.37 support) -/
noncomputable instance uPSo : Unique ((GΓ K L h).EdgeOrbit (pmNode K L h) (starNode K L h)) :=
  @Unique.mk' _ ⟨Quotient.mk _ (ePmStar K L h)⟩ (edgeOrbit_pm_star_subsingleton K L h)

/-- evaluation of an edge algebra at an orbit, into `L`. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def evE {i j : (ES K L h).I} (ε : (GΓ K L h).EdgeOrbit i j) :
    (ES K L h).M i j →ₐ[K] L :=
  ((GΓ K L h).edgeOrbitField ε).val.comp (Pi.evalAlgHom K _ ε)

/-- the element of an edge algebra with every component `z`. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def cst {i j : (ES K L h).I} (z : L) : (ES K L h).M i j :=
  fun ε => ⟨z, by rw [edgeOrbitField_top K L h]; trivial⟩

/-- `cst_one`.  @census none (helper; RQ2-2.37 support) -/
theorem cst_one {i j : (ES K L h).I} : cst K L h (i := i) (j := j) (1 : L) = 1 := rfl

/-- `evE_cst`.  @census none (helper; RQ2-2.37 support) -/
theorem evE_cst {i j : (ES K L h).I} (ε : (GΓ K L h).EdgeOrbit i j) (z : L) :
    evE K L h ε (cst K L h z) = z := rfl

/-- `evE_bijective`.  @census none (helper; RQ2-2.37 support) -/
theorem evE_bijective {i j : (ES K L h).I} [Unique ((GΓ K L h).EdgeOrbit i j)] :
    Function.Bijective (evE K L h (default : (GΓ K L h).EdgeOrbit i j)) := by
  constructor
  · intro a b hab
    funext ε
    have hε : ε = default := Unique.eq_default ε
    subst hε
    exact Subtype.ext hab
  · intro z; exact ⟨cst K L h z, rfl⟩

/-- evaluation of a vertex field into `L`. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def evV (i : (ES K L h).I) : (ES K L h).L i →ₐ[K] L :=
  ((GΓ K L h).vertexOrbitField i).val

/-- `evV_pm_bijective`.  @census none (helper; RQ2-2.37 support) -/
theorem evV_pm_bijective : Function.Bijective (evV K L h (nPm K L h)) := by
  constructor
  · exact fun a b hab => Subtype.ext hab
  · intro z
    refine ⟨⟨z, ?_⟩, rfl⟩
    rw [show (GΓ K L h).vertexOrbitField (pmNode K L h) = ⊤ from
      gelfand_vertexOrbitField_pm K L h]
    trivial

/-- `L_± ≅ L`. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def eqVpm : (ES K L h).L (nPm K L h) ≃ₐ[K] L :=
  AlgEquiv.ofBijective (evV K L h (nPm K L h)) (evV_pm_bijective K L h)

/-- The `K`-algebra endomorphism of `L` by which `L_±` acts on the RIGHT of `{}_⋆M_{±}`. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def rhoX : L →ₐ[K] L :=
  (evE K L h (default : (GΓ K L h).EdgeOrbit (starNode K L h) (pmNode K L h))).comp
    (((ES K L h).right (nStar K L h) (nPm K L h)).comp (eqVpm K L h).symm.toAlgHom)

/-- The `K`-algebra endomorphism of `L` by which `L_±` acts on the LEFT of `{}_{±}M_⋆`. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def rhoY : L →ₐ[K] L :=
  (evE K L h (default : (GΓ K L h).EdgeOrbit (pmNode K L h) (starNode K L h))).comp
    (((ES K L h).left (nPm K L h) (nStar K L h)).comp (eqVpm K L h).symm.toAlgHom)

/-- `rhoXe`.  @census none (helper; RQ2-2.37 support) -/
noncomputable def rhoXe : L ≃ₐ[K] L := AlgEquiv.ofBijective (rhoX K L h) (rhoX K L h).bijective
/-- `rhoYe`.  @census none (helper; RQ2-2.37 support) -/
noncomputable def rhoYe : L ≃ₐ[K] L := AlgEquiv.ofBijective (rhoY K L h) (rhoY K L h).bijective

/-- The twist `G = ρX ∘ ρY⁻¹`. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def GTw : L ≃ₐ[K] L := (rhoYe K L h).symm.trans (rhoXe K L h)

/-- `GTw_rhoY`.  @census none (helper; RQ2-2.37 support) -/
theorem GTw_rhoY (t : L) : GTw K L h (rhoY K L h t) = rhoX K L h t := by
  show rhoXe K L h ((rhoYe K L h).symm (rhoYe K L h t)) = _
  rw [AlgEquiv.symm_apply_apply]; rfl


/-- The path `p = (⋆, ±, ⋆)`. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def idxG : ℕ → (SG K L h).I :=
  fun n => if n = 1 then pmNode K L h else starNode K L h

/-- `idxG_zero`.  @census none (helper; RQ2-2.37 support) -/
theorem idxG_zero : idxG K L h 0 = starNode K L h := rfl
/-- `idxG_one`.  @census none (helper; RQ2-2.37 support) -/
theorem idxG_one : idxG K L h 1 = pmNode K L h := rfl
/-- `idxG_two`.  @census none (helper; RQ2-2.37 support) -/
theorem idxG_two : idxG K L h 2 = starNode K L h := rfl

/-- `εSP`.  @census none (helper; RQ2-2.37 support) -/
noncomputable abbrev εSP : (GΓ K L h).EdgeOrbit (starNode K L h) (pmNode K L h) := default
/-- `εPS`.  @census none (helper; RQ2-2.37 support) -/
noncomputable abbrev εPS : (GΓ K L h).EdgeOrbit (pmNode K L h) (starNode K L h) := default

/-- `evE_left_pm`.  @census none (helper; RQ2-2.37 support) -/
theorem evE_left_pm (a : (ES K L h).L (nPm K L h)) :
    evE K L h (εPS K L h) ((ES K L h).left (nPm K L h) (nStar K L h) a)
      = rhoY K L h (evV K L h (nPm K L h) a) := by
  show _ = evE K L h (εPS K L h) ((ES K L h).left _ _ ((eqVpm K L h).symm
    (evV K L h (nPm K L h) a)))
  congr 2
  exact ((eqVpm K L h).symm_apply_apply a).symm

/-- `evE_right_pm`.  @census none (helper; RQ2-2.37 support) -/
theorem evE_right_pm (a : (ES K L h).L (nPm K L h)) :
    evE K L h (εSP K L h) ((ES K L h).right (nStar K L h) (nPm K L h) a)
      = rhoX K L h (evV K L h (nPm K L h) a) := by
  show _ = evE K L h (εSP K L h) ((ES K L h).right _ _ ((eqVpm K L h).symm
    (evV K L h (nPm K L h) a)))
  congr 2
  exact ((eqVpm K L h).symm_apply_apply a).symm

/-- The `K`-bilinear form behind the identification `{}_⋆M_p ≅ L`. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def thetaBil :
    (ES K L h).M (nPm K L h) (nStar K L h) →ₗ[K]
      (ES K L h).M (nStar K L h) (nPm K L h) →ₗ[K] L where
  toFun y :=
    { toFun := fun x => evE K L h (εSP K L h) x * GTw K L h (evE K L h (εPS K L h) y)
      map_add' := fun x x' => by rw [map_add, add_mul]
      map_smul' := fun c x => by
        rw [RingHom.id_apply, map_smul, smul_mul_assoc] }
  map_add' y y' := by
    ext x
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, map_add, mul_add]
  map_smul' c y := by
    ext x
    simp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk,
      map_smul, Algebra.mul_smul_comm]

/-- `thetaBil_bal`.  @census none (helper; RQ2-2.37 support) -/
theorem thetaBil_bal (a : (ES K L h).L (nPm K L h))
    (y : (ES K L h).M (nPm K L h) (nStar K L h))
    (x : (ES K L h).M (nStar K L h) (nPm K L h)) :
    thetaBil K L h (a • y) x = thetaBil K L h y (MulOpposite.op a • x) := by
  have e1 : (a • y) = (ES K L h).left (nPm K L h) (nStar K L h) a * y :=
    EtaleSpecies.smul_left_def _ _ _ a y
  have e2 : (MulOpposite.op a • x) = (ES K L h).right (nStar K L h) (nPm K L h) a * x :=
    EtaleSpecies.smul_right_def _ _ _ (MulOpposite.op a) x
  simp only [thetaBil, LinearMap.coe_mk, AddHom.coe_mk, e1, e2, map_mul, evE_left_pm,
    evE_right_pm, GTw_rhoY]
  ring

/-- **Clause `RQ2-2.37-C1`** (the identification), as a `K`-linear map. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def theta :
    RationalQuivers.Balanced K ((ES K L h).L (nPm K L h)) ((ES K L h).L (nStar K L h))
      ((ES K L h).M (nPm K L h) (nStar K L h))
      ((ES K L h).M (nStar K L h) (nPm K L h)) →ₗ[K] L :=
  Balanced.liftK (A := (ES K L h).L (nPm K L h)) (B := (ES K L h).L (nStar K L h))
    (thetaBil K L h) (thetaBil_bal K L h)

/-- `theta_mk`.  @census none (helper; RQ2-2.37 support) -/
theorem theta_mk (x : (ES K L h).M (nStar K L h) (nPm K L h))
    (y : (ES K L h).M (nPm K L h) (nStar K L h)) :
    theta K L h (Balanced.mk x y)
      = evE K L h (εSP K L h) x * GTw K L h (evE K L h (εPS K L h) y) := rfl

/-- The identification is defined on the path bimodule of `p = (⋆,±,⋆)`. -/
example : (RationalQuivers.Species.pathBimod (SG K L h) (idxG K L h) 1).carrier =
    RationalQuivers.Balanced K ((ES K L h).L (nPm K L h)) ((ES K L h).L (nStar K L h))
      ((ES K L h).M (nPm K L h) (nStar K L h))
      ((ES K L h).M (nStar K L h) (nPm K L h)) := rfl


/-- Every element of `X ⊗_A Y` is `x₀ ⊗ y` when `X` is generated over `A` by `x₀`. 
@census none (helper; RQ2-2.37 support) -/
theorem balanced_eq_mk {A B Y X : Type} [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    [AddCommGroup Y] [Module K Y] [Module A Y] [Module Bᵐᵒᵖ Y] [IsScalarTower K A Y]
    [IsScalarTower K Bᵐᵒᵖ Y] [SMulCommClass A Bᵐᵒᵖ Y]
    [AddCommGroup X] [Module K X] [Module Aᵐᵒᵖ X] [IsScalarTower K Aᵐᵒᵖ X]
    (x₀ : X) (hX : ∀ x : X, ∃ a : A, MulOpposite.op a • x₀ = x)
    (t : RationalQuivers.Balanced K A B Y X) : ∃ y : Y, t = Balanced.mk x₀ y := by
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective (balancedRel K A B Y X) t
  induction s with
  | zero => exact ⟨0, (Balanced.mk_zero_right' (A' := A) (B' := B) x₀).symm⟩
  | tmul y x =>
      obtain ⟨a, rfl⟩ := hX x
      exact ⟨a • y, Balanced.mk_smul (K := K) (B := B) a x₀ y⟩
  | add s t hs ht =>
      obtain ⟨y₁, h₁⟩ := hs
      obtain ⟨y₂, h₂⟩ := ht
      refine ⟨y₁ + y₂, ?_⟩
      show Submodule.Quotient.mk (p := balancedRel K A B Y X) s
        + Submodule.Quotient.mk (p := balancedRel K A B Y X) t = _
      rw [h₁, h₂, Balanced.mk_add_right]

/-- `evE_injective`.  @census none (helper; RQ2-2.37 support) -/
theorem evE_injective {i j : (ES K L h).I} [Unique ((GΓ K L h).EdgeOrbit i j)] :
    Function.Injective (evE K L h (default : (GΓ K L h).EdgeOrbit i j)) :=
  (evE_bijective K L h).1

/-- `right_surjective`.  @census none (helper; RQ2-2.37 support) -/
theorem right_surjective (x : (ES K L h).M (nStar K L h) (nPm K L h)) :
    ∃ a : (ES K L h).L (nPm K L h), (ES K L h).right (nStar K L h) (nPm K L h) a = x := by
  refine ⟨(eqVpm K L h).symm ((rhoXe K L h).symm (evE K L h (εSP K L h) x)), ?_⟩
  refine evE_injective K L h ?_
  rw [evE_right_pm]
  show rhoX K L h ((eqVpm K L h) ((eqVpm K L h).symm _)) = _
  rw [AlgEquiv.apply_symm_apply]
  show rhoXe K L h ((rhoXe K L h).symm _) = _
  rw [AlgEquiv.apply_symm_apply]

/-- `theta_bijective`.  @census none (helper; RQ2-2.37 support) -/
theorem theta_bijective : Function.Bijective (theta K L h) := by
  constructor
  · refine (injective_iff_map_eq_zero (theta K L h)).mpr fun t ht => ?_
    obtain ⟨y, rfl⟩ := balanced_eq_mk K (cst K L h (1 : L)) (fun x => by
      obtain ⟨a, ha⟩ := right_surjective K L h x
      exact ⟨a, by
        show (ES K L h).right (nStar K L h) (nPm K L h) a * cst K L h (1 : L) = x
        rw [cst_one, mul_one]; exact ha⟩) t
    rw [theta_mk, evE_cst, one_mul] at ht
    have hy : evE K L h (εPS K L h) y = 0 := by
      have := congrArg (GTw K L h).symm ht
      rwa [AlgEquiv.symm_apply_apply, map_zero] at this
    have hy0 : y = 0 := evE_injective K L h (by rw [hy, map_zero])
    rw [hy0]
    exact Balanced.mk_zero_right' (A' := (ES K L h).L (nPm K L h))
      (B' := (ES K L h).L (nStar K L h)) _
  · intro z
    obtain ⟨y, hy⟩ := (evE_bijective (i := nPm K L h) (j := nStar K L h) K L h).2
      ((GTw K L h).symm z)
    refine ⟨Balanced.mk (cst K L h (1 : L)) y, ?_⟩
    rw [theta_mk, evE_cst, one_mul, hy, AlgEquiv.apply_symm_apply]

/-- **Clause `RQ2-2.37-C1`**: `{}_⋆M_p ≅ L`. 
@census none (clause witness for `RQ2-2.37-C1`)
@clauses   RQ2-2.37-C1 -/
noncomputable def thetaEquiv :
    RationalQuivers.Balanced K ((ES K L h).L (nPm K L h)) ((ES K L h).L (nStar K L h))
      ((ES K L h).M (nPm K L h) (nStar K L h))
      ((ES K L h).M (nStar K L h) (nPm K L h)) ≃ₗ[K] L :=
  LinearEquiv.ofBijective (theta K L h) (theta_bijective K L h)

include h in
/-- `finrank_L`.  @census none (helper; RQ2-2.37 support) -/
theorem finrank_L : Module.finrank K L = 2 :=
  (IsGalois.card_aut_eq_finrank K L).symm.trans h


/-- **Clause `RQ2-2.37-C1`**, the dimension: `{}_⋆M_p` is a `K`-vector space of dimension 2. 
@census none (clause witness for `RQ2-2.37-C1`)
@clauses   RQ2-2.37-C1 -/
theorem finrank_pathBimod :
    Module.finrank K
      (RationalQuivers.Balanced K ((ES K L h).L (nPm K L h)) ((ES K L h).L (nStar K L h))
        ((ES K L h).M (nPm K L h) (nStar K L h))
        ((ES K L h).M (nStar K L h) (nPm K L h))) = 2 := by
  rw [(thetaEquiv K L h).finrank_eq, finrank_L K L h]


/-! ### `RQ2-2.37-C2` — the relation `R_Gelfand` -/

/-- `α ⊗ 1` in the path bimodule of the length-two path `(idx 0, idx 1, idx 2)`. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def relGen (α : L) (idx : ℕ → (SG K L h).I) :
    (RationalQuivers.Species.pathBimod (SG K L h) idx 1).carrier :=
  Balanced.mk (cst K L h (i := idx 0) (j := idx 1) α) (cst K L h (i := idx 1) (j := idx 2) 1)

/-- `θ(α ⊗ 1) = α`: the line of `RGelfand` is `θ⁻¹(K·α)`.
@census none (clause witness for `RQ2-2.37-C2`)
@clauses   RQ2-2.37-C2 -/
theorem theta_relGen (α : L) : theta K L h (relGen K L h α (idxG K L h)) = α := by
  show theta K L h (Balanced.mk (cst K L h α) (cst K L h 1)) = α
  rw [theta_mk, evE_cst, evE_cst, map_one, mul_one]

/-- every element of `L_⋆` comes from `K`. 
@census none (helper; RQ2-2.37 support) -/
theorem exists_algebraMap_star {i : (SG K L h).I} (hi : i = nStar K L h)
    (a : (SG K L h).L i) : ∃ k : K, algebraMap K ((SG K L h).L i) k = a := by
  have hF : (GΓ K L h).vertexOrbitField i = ⊥ := by
    rw [hi]; exact gelfand_vertexOrbitField_star K L h
  have hmem : ((show ↥((GΓ K L h).vertexOrbitField i) from a) : L)
      ∈ (⊥ : IntermediateField K L) := by
    rw [← hF]; exact (show ↥((GΓ K L h).vertexOrbitField i) from a).2
  obtain ⟨k, hk⟩ := (IntermediateField.mem_bot).mp hmem
  exact ⟨k, Subtype.ext hk⟩

/-- The member of `R_Gelfand` at a length-two path: the `K`-line `K·α` when the path is
`(⋆, ±, ⋆)`, and `0` otherwise. 
@census none (helper; RQ2-2.37 support) -/
noncomputable def RGelfandAt (α : L) (idx : ℕ → (SG K L h).I) :
    RationalQuivers.Species.SubBimod (RationalQuivers.Species.pathBimod (SG K L h) idx 1) :=
  if hp : idx 0 = nStar K L h ∧ idx 1 = nPm K L h ∧ idx 2 = nStar K L h then
    { toSubmodule := Submodule.span ((SG K L h).L (idx 0)) {relGen K L h α idx}
      smul_right_mem := fun b {x} hx => by
        obtain ⟨k, hk⟩ := exists_algebraMap_star K L h hp.2.2 (MulOpposite.unop b)
        have hb : b = algebraMap K ((SG K L h).L (idx 2))ᵐᵒᵖ k := by
          refine MulOpposite.unop_injective ?_
          rw [← hk]; rfl
        rw [hb, ← RationalQuivers.smul_K_of_tower (C' := (SG K L h).L (idx 2)) k x,
          show (k : K) • x = (algebraMap K ((SG K L h).L (idx 0)) k) • x from
            (algebraMap_smul _ k x).symm]
        exact Submodule.smul_mem _ _ hx }
  else RationalQuivers.Species.SubBimod.bot _

/-- `RGelfandAt_pos`.  @census none (helper; RQ2-2.37 support) -/
theorem RGelfandAt_pos (α : L) {idx : ℕ → (SG K L h).I}
    (hp : idx 0 = nStar K L h ∧ idx 1 = nPm K L h ∧ idx 2 = nStar K L h) :
    (RGelfandAt K L h α idx).toSubmodule
      = Submodule.span ((SG K L h).L (idx 0)) {relGen K L h α idx} := by
  rw [RGelfandAt, dif_pos hp]

/-- `RGelfandAt_neg`.  @census none (helper; RQ2-2.37 support) -/
theorem RGelfandAt_neg (α : L) {idx : ℕ → (SG K L h).I}
    (hp : ¬ (idx 0 = nStar K L h ∧ idx 1 = nPm K L h ∧ idx 2 = nStar K L h)) :
    (RGelfandAt K L h α idx).toSubmodule = ⊥ := by
  rw [RGelfandAt, dif_neg hp]; rfl

/-- **Clause `RQ2-2.37-C2`** — the relation `R_Gelfand`, whose only non-zero member is the
`K`-line `K·α` inside `{}_⋆M_p`. 
@census none (clause witness for `RQ2-2.37-C2`)
@clauses   RQ2-2.37-C2 -/
noncomputable def RGelfand (α : L) : RationalQuivers.Species.Relation (SG K L h) := fun idx n =>
  match n with
  | 1 => RGelfandAt K L h α idx
  | _ => RationalQuivers.Species.SubBimod.bot _

/-- `RGelfand_one`.  @census none (helper; RQ2-2.37 support) -/
theorem RGelfand_one (α : L) (idx : ℕ → (SG K L h).I) :
    RGelfand K L h α idx 1 = RGelfandAt K L h α idx := rfl

/-! ### The satisfaction condition cut out by `R_Gelfand` -/

/-- `f_p` on a length-two path, resolved into its two structure maps. 
@census none (helper; RQ2-2.37 support) -/
theorem pathHom_one_mk (S : RationalQuivers.Species K) (V : RationalQuivers.Species.Rep S)
    (idx : ℕ → S.I) (w : V.W (idx 0)) (x : S.M (idx 0) (idx 1)) (y : S.M (idx 1) (idx 2)) :
    RationalQuivers.Species.pathHom S V idx 1 (Balanced.mk w (Balanced.mk x y))
      = V.f (idx 1) (idx 2) (Balanced.mk (V.f (idx 0) (idx 1) (Balanced.mk w x)) y) := rfl

/-- **The condition `R_Gelfand` imposes.**  A representation of `S(Γ_K)` satisfies `R_Gelfand` if
and only if `f_p(w ⊗ α ⊗ 1) = 0` for every length-two path `(⋆, ±, ⋆)` and every `w ∈ W_⋆`. 
@census none (helper; RQ2-2.37 support) -/
theorem satisfies_RGelfand_iff (V : RationalQuivers.Species.Rep (SG K L h)) (α : L) :
    RationalQuivers.Species.Satisfies (SG K L h) V (RGelfand K L h α) ↔
      ∀ (idx : ℕ → (SG K L h).I), idx 0 = nStar K L h → idx 1 = nPm K L h →
        idx 2 = nStar K L h → ∀ w : V.W (idx 0),
          RationalQuivers.Species.pathHom (SG K L h) V idx 1
            (Balanced.mk w (relGen K L h α idx)) = 0 := by
  constructor
  · intro hsat idx h0 h1 h2 w
    refine hsat idx 1 w _ ?_
    show relGen K L h α idx ∈ (RGelfand K L h α idx 1).toSubmodule
    rw [RGelfand_one, RGelfandAt_pos K L h α ⟨h0, h1, h2⟩]
    exact Submodule.mem_span_singleton_self _
  · intro hcond idx n w r hr
    match n with
    | 0 =>
        rw [show (RGelfand K L h α idx 0).toSubmodule = ⊥ from rfl, Submodule.mem_bot] at hr
        rw [hr, Balanced.mk_zero_right' (A' := (SG K L h).L (idx 0))
          (B' := (SG K L h).L (idx 1)), map_zero]
    | (n + 2) =>
        rw [show (RGelfand K L h α idx (n + 2)).toSubmodule = ⊥ from rfl, Submodule.mem_bot] at hr
        rw [hr, Balanced.mk_zero_right' (A' := (SG K L h).L (idx 0))
          (B' := (SG K L h).L (idx (n + 3))), map_zero]
    | 1 =>
        by_cases hp : idx 0 = nStar K L h ∧ idx 1 = nPm K L h ∧ idx 2 = nStar K L h
        · rw [RGelfand_one, RGelfandAt_pos K L h α hp] at hr
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hr
          rw [← Balanced.mk_smul (K := K) (B := (SG K L h).L (idx 2)) a w
            (relGen K L h α idx)]
          exact hcond idx hp.1 hp.2.1 hp.2.2 _
        · rw [RGelfand_one, RGelfandAt_neg K L h α hp, Submodule.mem_bot] at hr
          rw [hr, Balanced.mk_zero_right' (A' := (SG K L h).L (idx 0))
            (B' := (SG K L h).L (idx 2)), map_zero]


/-! ### `RQ2-2.37-C3` — `eq:gelfandspeciescomposite`, and the iff with the quiver relation

**Added 2026-09-12, round 5** (coordinator ruling `R-ERR-5`, round-5 brief).  The two structure
maps of `S(Γ_K)` are `GelfandDescent.f_uniqueOrbit_generator` (`f_{⋆±}`, one Galois term) and
`GelfandDescent.f_twoTerm_generator` (`f_{±⋆}`, two Galois terms).  Composing them on
`w ⊗ z ⊗ 1` and pushing the semilinearity of every `φ'` to the front gives

  `f_p(w ⊗ z ⊗ 1) = β₀(z)·A(w) + c(β₀(z))·φ_{⋆,c}(A(w))`,

with `β₀ = τ₂⁻¹σ₂τ₁⁻¹ ∈ Gal(L/K)` built from the chosen `EdgeChoice`s and `A` a six-fold
composite of edge maps and Galois transports (`Araw`).  On the `G`-fixed `w` every transport is a
cast (`φ'_of_mem_vertexFixed`), `eq:koecheractiononrep` (`Rep.φEdge'_φ'`) moves the remaining
one across the first edge, and the chosen edge representatives are `a_∓` and `b_∓` for some
composable choice of signs (`chain_cases`).  The result is `eq:gelfandspeciescomposite` read
through the identification `β ∘ θ` for **one** `β ∈ Gal(L/K)` fixed by the tree's representatives
(`exists_beta`); since `β ∈ {1, c}` and `c(K·α) = K·α`, the relation is the printed one and the
iff (`satisfies_RGelfand_iff_relation`) closes exactly as the source closes it:
`M(⋆) = W_⋆ ⊗_K L` is `RationalQuiver.vertexDescentEquiv`. -/

section Composite

/-- `cosetG_fintype`.  A section-LOCAL instance: a global one would change which `Fintype`
instance downstream statements elaborate with (measured: S9's `gal_univ` changed its signature
hash under a global `Fintype Gal(L/K)` here).  @census none (helper; RQ2-2.37 support) -/
@[reducible] noncomputable def cosetG_fintype (i j : (GΓ K L h).VertexOrbit) :
    ∀ ε : (GΓ K L h).EdgeOrbit i j,
      Fintype (EdgeChoice.CosetIndex (GΓ K L h) (EdgeChoice.choose (GΓ K L h) ε)) :=
  fun ε => @Fintype.ofFinite _ (finite_cosetIndex (EdgeChoice.choose (GΓ K L h) ε))

/-- `galG_fintype`.  Section-local, for the reason `cosetG_fintype` gives.
@census none (helper; RQ2-2.37 support) -/
@[reducible] noncomputable def galG_fintype : Fintype Gal(L/K) := Fintype.ofFinite _

attribute [local instance] cosetG_fintype galG_fintype

omit [IsGalois K L] [FiniteDimensional K L] in
include h in
/-- Every element of the order-two Galois group is `1` or `c`.
@census none (helper; RQ2-2.37 support) -/
theorem eq_one_or_eq {c : Gal(L/K)} (hc : c ≠ 1) (σ : Gal(L/K)) : σ = 1 ∨ σ = c := by
  by_cases hσ : σ = 1
  · exact Or.inl hσ
  · obtain ⟨w, -, hu⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp h
    exact Or.inr ((hu σ hσ).trans (hu c hc).symm)

/-- `⋆` is fixed by every Galois element.  @census none (helper; RQ2-2.37 support) -/
theorem smul_star (σ : Gal(L/K)) : σ • gelfandStar K L h = gelfandStar K L h := by
  by_cases hσ : σ = 1
  · rw [hσ, one_smul]
  · exact gelfand_smul_star K L h hσ

/-- The chosen representative of `{⋆}` is `⋆`: the orbit is a point.
@census none (helper; RQ2-2.37 support) -/
theorem vertexRep_star : (GΓ K L h).vertexRep (starNode K L h) = gelfandStar K L h := by
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp
    ((GΓ K L h).mem_orbit_vertexRep (gelfandVertex K L h 1))
  exact MulAction.injective σ (hσ.trans (smul_star K L h σ).symm)

/-- The chosen `{⋆}→{±}` edge is `b₋` or `b₊`; either way its source is `⋆`.
@census none (helper; RQ2-2.37 support) -/
theorem source_edgeRep_SP :
    (GΓ K L h).toRQuiver.source ((GΓ K L h).edgeRep (εSP K L h)) = gelfandStar K L h := by
  have h1 := edgeSet_star_pm K L h (Quotient.out (εSP K L h))
  change (GΓ K L h).edgeRep (εSP K L h) = _ ∨ (GΓ K L h).edgeRep (εSP K L h) = _ at h1
  rcases h1 with h1 | h1 <;> rw [h1] <;> rfl

/-- The chosen `{±}→{⋆}` edge is `a₋` or `a₊`; either way its target is `⋆`.
@census none (helper; RQ2-2.37 support) -/
theorem target_edgeRep_PS :
    (GΓ K L h).toRQuiver.target ((GΓ K L h).edgeRep (εPS K L h)) = gelfandStar K L h := by
  have h1 := edgeSet_pm_star K L h (Quotient.out (εPS K L h))
  change (GΓ K L h).edgeRep (εPS K L h) = _ ∨ (GΓ K L h).edgeRep (εPS K L h) = _ at h1
  rcases h1 with h1 | h1 <;> rw [h1] <;> rfl

/-- The `EdgeChoice` at the `{⋆}→{±}` orbit.  @census none (helper; RQ2-2.37 support) -/
noncomputable abbrev chSP : (GΓ K L h).EdgeChoice (εSP K L h) :=
  EdgeChoice.choose (GΓ K L h) (εSP K L h)

/-- The `EdgeChoice` at the `{±}→{⋆}` orbit.  @census none (helper; RQ2-2.37 support) -/
noncomputable abbrev chPS : (GΓ K L h).EdgeChoice (εPS K L h) :=
  EdgeChoice.choose (GΓ K L h) (εPS K L h)

/-- `β₀ = τ₂⁻¹ σ₂ τ₁⁻¹`, the Galois element the two descent formulas pull out.
@census none (helper; RQ2-2.37 support) -/
noncomputable def beta0 : Gal(L/K) := (chPS K L h).τ⁻¹ * (chPS K L h).σ * (chSP K L h).τ⁻¹

/-- The vector `A(w) ∈ M(v_⋆)` traced by the two structure maps, before identification.
@census none (helper; RQ2-2.37 support) -/
noncomputable def Araw (M : FDRep (GΓ K L h))
    (w : ((FFunctor (GΓ K L h)).obj M).W (nStar K L h)) :
    M.toRep.M ((GΓ K L h).vertexRep (nStar K L h)) :=
  M.toRep.φ' (chPS K L h).τ⁻¹ (chPS K L h).inv_smul_target
    (M.toRep.φEdge ((GΓ K L h).edgeRep (εPS K L h))
      (M.toRep.φ' (chPS K L h).σ (chPS K L h).sourceVertex
        (uPS M (nStar K L h) (nPm K L h) w)))

/-- The element of `W_⋆ = M(v_⋆)^G` read in `M(⋆)`.  @census none (helper; RQ2-2.37 support) -/
noncomputable def toStar (M : FDRep (GΓ K L h))
    (w : ((FFunctor (GΓ K L h)).obj M).W (nStar K L h)) : M.toRep.M (gelfandStar K L h) :=
  M.toRep.eqCast (vertexRep_star K L h) (wv M (nStar K L h) w)

/-- `toStar_mem`.  @census none (helper; RQ2-2.37 support) -/
theorem toStar_mem (M : FDRep (GΓ K L h)) (w : ((FFunctor (GΓ K L h)).obj M).W (nStar K L h)) :
    toStar K L h M w ∈ M.toRep.vertexFixed (gelfandStar K L h) :=
  mem_vertexFixed_eqCast M.toRep (vertexRep_star K L h)
    (show wv M (nStar K L h) w ∈ M.toRep.vertexFixed _ from
      (show ↥(M.toRep.vertexFixed ((GΓ K L h).vertexRep (nStar K L h))) from w).2)

/-! ### Step 1: `f_{⋆±}` -/

/-- `f_{⋆±}(w ⊗ z) = τ₁⁻¹(z)·u`, the one-term formula at the Gelfand species.
@census none (helper; RQ2-2.37 support) -/
theorem f_SP_eq (M : FDRep (GΓ K L h)) (w : ((FFunctor (GΓ K L h)).obj M).W (nStar K L h))
    (z : L) :
    wv M (nPm K L h) (((FFunctor (GΓ K L h)).obj M).f (nStar K L h) (nPm K L h)
        (tmk M (nStar K L h) (nPm K L h) w (cst K L h z)))
      = (chSP K L h).τ⁻¹ z • uPS M (nStar K L h) (nPm K L h) w := by
  have η₀ : EdgeChoice.CosetIndex (GΓ K L h) (chSP K L h) := QuotientGroup.mk 1
  rw [f_uniqueOrbit_generator M (nStar K L h) (nPm K L h) (stabilizer_pm K L h) w
    (cst K L h z) η₀]
  show (chSP K L h).τ⁻¹ z • phiComp M.toRep (chSP K L h) η₀ w = _
  rw [phiComp_eq]
  congr 1
  exact M.toRep.φ'_congr (by rw [rep_eq_one _ (stabilizer_pm K L h) η₀, one_mul]) _ _ _

/-! ### Step 2: `f_{±⋆}` after `f_{⋆±}`, with the scalar out front -/

/-- `f_p(w ⊗ z ⊗ 1) = β₀(z)·A(w) + c(β₀(z))·φ_{⋆,c}(A(w))`: the two-term formula with the
scalar pushed out front through the semilinearity of every `φ'`.
@census none (helper; RQ2-2.37 support) -/
theorem composite_raw (M : FDRep (GΓ K L h)) {c : Gal(L/K)} (hc : c ≠ 1)
    (w : ((FFunctor (GΓ K L h)).obj M).W (nStar K L h)) (z : L) :
    wv M (nStar K L h) (((FFunctor (GΓ K L h)).obj M).f (nPm K L h) (nStar K L h)
        (tmk M (nPm K L h) (nStar K L h)
          (((FFunctor (GΓ K L h)).obj M).f (nStar K L h) (nPm K L h)
            (tmk M (nStar K L h) (nPm K L h) w (cst K L h z)))
          (cst K L h 1)))
      = beta0 K L h z • Araw K L h M w
        + c (beta0 K L h z)
          • M.toRep.φ' c (stab_all_of_stab_top (stabilizer_star K L h) c) (Araw K L h M w) := by
  rw [f_twoTerm_generator M (nPm K L h) (nStar K L h) (stabilizer_star K L h)
    (gelfand_stabilizer_E K L h) h hc]
  have hcst : ((cst K L h (i := nPm K L h) (j := nStar K L h) 1 default : L)) = 1 := rfl
  have hu : uPS M (nPm K L h) (nStar K L h)
      (((FFunctor (GΓ K L h)).obj M).f (nStar K L h) (nPm K L h)
        (tmk M (nStar K L h) (nPm K L h) w (cst K L h z)))
      = beta0 K L h z • Araw K L h M w := by
    rw [uPS_def]
    have hwv := f_SP_eq K L h M w z
    unfold wv at hwv ⊢
    rw [hwv, Rep.φ'_smul, map_smul, Rep.φ'_smul]
    rfl
  rw [hu, hcst, map_one, one_smul, map_one, one_smul, Rep.φ'_smul]

/-! ### Step 3: identify `A(w)` with the path composites at `⋆` -/

/-- `P_s`: `φ_{a₋}φ_{b₋}` for `s = true`, `φ_{a₊}φ_{b₊}` for `s = false`.
@census none (helper; RQ2-2.37 support) -/
noncomputable def Pof (M : Rep (GΓ K L h)) (s : Bool) :
    M.M (gelfandStar K L h) →ₗ[L] M.M (gelfandStar K L h) :=
  cond s (M.pathMap (gelfandPathMinus K L h)) (M.pathMap (gelfandPathPlus K L h))

/-- `φ_{⋆,c}` is an involution: `c² = 1`.  @census none (helper; RQ2-2.37 support) -/
theorem φ'_star_involutive (M : Rep (GΓ K L h)) {c : Gal(L/K)} (hc : c ≠ 1)
    (x : M.M (gelfandStar K L h)) :
    M.φ' c (gelfand_smul_star K L h hc) (M.φ' c (gelfand_smul_star K L h hc) x) = x := by
  have hmul : (c * c) • gelfandStar K L h = gelfandStar K L h := by
    rw [gal_sq_eq_one K L h hc, one_smul]
  rw [M.φ'_comp c c (gelfand_smul_star K L h hc) (gelfand_smul_star K L h hc) hmul,
    M.φ'_congr (gal_sq_eq_one K L h hc) hmul (one_smul _ _) x, M.φ'_one]
  exact M.eqCast_rfl _ x

/-- `φ_{⋆,c} ∘ P_s = P_{¬s} ∘ φ_{⋆,c}`: clause `RQ2-2.16-C3` in both directions.
@census none (helper; RQ2-2.37 support) -/
theorem φ'_Pof (M : Rep (GΓ K L h)) {c : Gal(L/K)} (hc : c ≠ 1) (s : Bool)
    (m : M.M (gelfandStar K L h)) :
    M.φ' c (gelfand_smul_star K L h hc) (Pof K L h M s m)
      = Pof K L h M (!s) (M.φ' c (gelfand_smul_star K L h hc) m) := by
  cases s
  · show M.φ' c _ (M.pathMap (gelfandPathPlus K L h) m)
      = M.pathMap (gelfandPathMinus K L h) (M.φ' c _ m)
    have := gelfand_relation_conjugate K L h hc M (M.φ' c (gelfand_smul_star K L h hc) m)
    rw [φ'_star_involutive K L h M hc] at this
    rw [← this, φ'_star_involutive K L h M hc]
  · exact gelfand_relation_conjugate K L h hc M m

/-- The two-edge chain, resolved by the case analysis on the representatives: with `e₂ ∈ {a₋, a₊}`
and `e₁' ∈ {b₋, b₊}` composable, the chain is `a₋b₋` or `a₊b₊`.  The two non-composable pairs are
excluded by their end vertices.  @census none (helper; RQ2-2.37 support) -/
theorem chain_cases (e₂ e₁' : (GΓ K L h).E)
    (h2 : e₂ = gelfandEdge K L h 0 ∨ e₂ = gelfandEdge K L h 2)
    (h1 : e₁' = gelfandEdge K L h 1 ∨ e₁' = gelfandEdge K L h 3)
    (hb' : (GΓ K L h).toRQuiver.target e₁' = (GΓ K L h).toRQuiver.source e₂) :
    ∃ s : Bool, ∀ (M : Rep (GΓ K L h)) {v : (GΓ K L h).V} (hv : v = gelfandStar K L h)
      (ha' : (GΓ K L h).toRQuiver.source e₁' = v)
      (hT : (GΓ K L h).toRQuiver.target e₂ = gelfandStar K L h) (x : M.M v),
      M.eqCast hT (M.φEdge e₂ (M.φEdge' e₁' ha' hb' x)) = Pof K L h M s (M.eqCast hv x) := by
  have h20 : gelfandVertex K L h 2 ≠ gelfandVertex K L h 0 := by
    intro hh
    have hh' := congrArg Fin.val hh
    change 2 = 0 at hh'
    exact absurd hh' (by decide)
  have h02 : gelfandVertex K L h 0 ≠ gelfandVertex K L h 2 := fun hh => h20 hh.symm
  rcases h2 with rfl | rfl <;> rcases h1 with rfl | rfl
  · refine ⟨true, fun M v hv ha' hT x => ?_⟩
    subst hv
    show _ = M.pathMap (gelfandPathMinus K L h) x
    rw [gelfand_pathMap_minus]
    rfl
  · exact absurd hb' h20
  · exact absurd hb' h02
  · refine ⟨false, fun M v hv ha' hT x => ?_⟩
    subst hv
    show _ = M.pathMap (gelfandPathPlus K L h) x
    rw [gelfand_pathMap_plus]
    rfl

/-- `A(w) = φ'_{τ₂⁻¹}(P_s(w))` for a sign `s` determined by the chosen representatives.
@census none (helper; RQ2-2.37 support) -/
theorem chain_eq : ∃ s : Bool, ∀ (M : FDRep (GΓ K L h))
    (w : ((FFunctor (GΓ K L h)).obj M).W (nStar K L h)),
    Araw K L h M w
      = M.toRep.eqCast (vertexRep_star K L h).symm
          (M.toRep.φ' (chPS K L h).τ⁻¹ (smul_star K L h _)
            (Pof K L h M.toRep s (toStar K L h M w))) := by
  set ρ : Gal(L/K) := (chPS K L h).σ * (chSP K L h).τ⁻¹ with hρdef
  set e₁ : (GΓ K L h).E := (GΓ K L h).edgeRep (εSP K L h) with he₁
  set e₂ : (GΓ K L h).E := (GΓ K L h).edgeRep (εPS K L h) with he₂
  have hstar : ∀ σ : Gal(L/K), σ • (GΓ K L h).vertexRep (nStar K L h)
      = (GΓ K L h).vertexRep (nStar K L h) := stab_all_of_stab_top (stabilizer_star K L h)
  have h₃ : ρ • (GΓ K L h).toRQuiver.target e₁ = (GΓ K L h).toRQuiver.source e₂ := by
    rw [hρdef, mul_smul, (chSP K L h).inv_smul_target, (chPS K L h).sourceVertex]
  have ha : (GΓ K L h).toRQuiver.source e₁ = (GΓ K L h).vertexRep (nStar K L h) := by
    rw [he₁, source_edgeRep_SP, vertexRep_star]
  have ha' : (GΓ K L h).toRQuiver.source (ρ • e₁) = (GΓ K L h).vertexRep (nStar K L h) := by
    rw [(GΓ K L h).source_smul, ha, hstar]
  have hb' : (GΓ K L h).toRQuiver.target (ρ • e₁) = (GΓ K L h).toRQuiver.source e₂ := by
    rw [(GΓ K L h).target_smul, h₃]
  have hT : (GΓ K L h).toRQuiver.target e₂ = gelfandStar K L h := target_edgeRep_PS K L h
  have h2 : e₂ = gelfandEdge K L h 0 ∨ e₂ = gelfandEdge K L h 2 :=
    edgeSet_pm_star K L h (Quotient.out (εPS K L h))
  have h1 : ρ • e₁ = gelfandEdge K L h 1 ∨ ρ • e₁ = gelfandEdge K L h 3 := by
    have := edgeSet_star_pm K L h (ρ • Quotient.out (εSP K L h))
    rwa [RationalQuiver.coe_smul_edgeSet] at this
  obtain ⟨s, hs⟩ := chain_cases K L h e₂ (ρ • e₁) h2 h1 hb'
  refine ⟨s, fun M w => ?_⟩
  -- the chain, before the case analysis
  have hchain : Araw K L h M w
      = M.toRep.φ' (chPS K L h).τ⁻¹ (chPS K L h).inv_smul_target
          (M.toRep.φEdge e₂ (M.toRep.φEdge' (ρ • e₁) ha' hb' (wv M (nStar K L h) w))) := by
    unfold Araw
    rw [uPS_def]
    have hw : wv M (nStar K L h) w ∈ M.toRep.vertexFixed ((GΓ K L h).vertexRep (nStar K L h)) :=
      (show ↥(M.toRep.vertexFixed ((GΓ K L h).vertexRep (nStar K L h))) from w).2
    rw [φ'_of_mem_vertexFixed M.toRep hw _ (hstar _) (chSP K L h).sourceVertex,
      φEdge_eqCast, M.toRep.φ'_comp (chPS K L h).σ (chSP K L h).τ⁻¹
        (chSP K L h).inv_smul_target (chPS K L h).sourceVertex h₃,
      ← M.toRep.φEdge'_φ' ρ (rfl : ρ • e₁ = ρ • e₁) _ rfl ha' hb' (hstar ρ) h₃,
      φ'_of_mem_vertexFixed M.toRep hw ρ (hstar ρ) (hstar ρ), M.toRep.eqCast_rfl]
  have hσ' : (chPS K L h).τ⁻¹ • (GΓ K L h).toRQuiver.target e₂ = gelfandStar K L h := by
    rw [hT]; exact smul_star K L h _
  rw [hchain]
  unfold toStar
  rw [← hs M.toRep (vertexRep_star K L h) ha' hT, φ'_eqCast M.toRep _ hT _ hσ',
    eqCast_φ' M.toRep _ hσ' _ (chPS K L h).inv_smul_target]

/-- `β₀ z · P_s + c(β₀ z) · P_{¬s}` is `β z · P₋ + c(β z) · P₊` for a single `β` (`β₀` or `cβ₀`).
@census none (helper; RQ2-2.37 support) -/
theorem formula_of_Pof {c : Gal(L/K)} (hc : c ≠ 1) (β₀ : Gal(L/K)) (s : Bool) :
    ∃ β : Gal(L/K), ∀ (M : Rep (GΓ K L h)) (y : M.M (gelfandStar K L h)) (z : L),
      β₀ z • Pof K L h M s y + c (β₀ z) • Pof K L h M (!s) y
        = β z • M.pathMap (gelfandPathMinus K L h) y
          + c (β z) • M.pathMap (gelfandPathPlus K L h) y := by
  cases s
  · refine ⟨c * β₀, fun M y z => ?_⟩
    have hcc : c (c (β₀ z)) = β₀ z := by
      rw [← AlgEquiv.mul_apply, gal_sq_eq_one K L h hc, AlgEquiv.one_apply]
    show β₀ z • M.pathMap (gelfandPathPlus K L h) y + c (β₀ z) • M.pathMap (gelfandPathMinus K L h) y = _
    rw [AlgEquiv.mul_apply, hcc, add_comm]
  · exact ⟨β₀, fun M y z => rfl⟩

/-- **Clause `RQ2-2.37-C3`, the formula `eq:gelfandspeciescomposite`.**  There is a single
`β ∈ Gal(L/K)`, determined by the tree's chosen representatives and independent of `M`, `w`, `z`,
with

  `f_p(w ⊗ z ⊗ 1) = β(z)·(φ_{a₋}∘φ_{b₋})(w) + c(β(z))·(φ_{a₊}∘φ_{b₊})(w)`

for every `M`, every `w ∈ W_⋆ = M(⋆)^G` and every `z ∈ L` — the printed identity read through the
identification `β ∘ θ : {}_⋆M_p ≅ L` instead of `θ`.  The source fixes `β = 1` by *choosing* `−`,
`a₋`, `b₋` as representatives; the tree's representatives are `Quotient.out`-defined and `β` is
what that choice costs (`R-ERR-5`).  `f_p` is written out as `f_{±⋆} ∘ (f_{⋆±} ⊗ 1)`
(`pathHom_one_mk`), and both sides are read in `M(⋆)` through `toStar`.

@census none (clause witness for `RQ2-2.37-C3`)
@clauses   RQ2-2.37-C3 -/
theorem exists_beta {c : Gal(L/K)} (hc : c ≠ 1) :
    ∃ β : Gal(L/K), ∀ (M : FDRep (GΓ K L h))
      (w : ((FFunctor (GΓ K L h)).obj M).W (nStar K L h)) (z : L),
      M.toRep.eqCast (vertexRep_star K L h)
        (wv M (nStar K L h) (((FFunctor (GΓ K L h)).obj M).f (nPm K L h) (nStar K L h)
          (tmk M (nPm K L h) (nStar K L h)
            (((FFunctor (GΓ K L h)).obj M).f (nStar K L h) (nPm K L h)
              (tmk M (nStar K L h) (nPm K L h) w (cst K L h z)))
            (cst K L h 1))))
        = β z • M.toRep.pathMap (gelfandPathMinus K L h) (toStar K L h M w)
          + c (β z) • M.toRep.pathMap (gelfandPathPlus K L h) (toStar K L h M w) := by
  obtain ⟨s, hs⟩ := chain_eq K L h
  -- `φ'_{τ₂⁻¹}` on the fixed vector is `P_s` or `P_{¬s}`
  have hτ : ∃ s' : Bool, ∀ (M : FDRep (GΓ K L h))
      (w : ((FFunctor (GΓ K L h)).obj M).W (nStar K L h)),
      M.toRep.φ' (chPS K L h).τ⁻¹ (smul_star K L h _) (Pof K L h M.toRep s (toStar K L h M w))
        = Pof K L h M.toRep s' (toStar K L h M w) := by
    rcases eq_one_or_eq K L h hc (chPS K L h).τ⁻¹ with hτ | hτ
    · refine ⟨s, fun M w => ?_⟩
      rw [M.toRep.φ'_congr hτ _ (one_smul _ _), M.toRep.φ'_one]
      exact M.toRep.eqCast_rfl _ _
    · refine ⟨!s, fun M w => ?_⟩
      rw [M.toRep.φ'_congr hτ _ (gelfand_smul_star K L h hc), φ'_Pof K L h M.toRep hc,
        φ'_of_mem_vertexFixed M.toRep (toStar_mem K L h M w) c (gelfand_smul_star K L h hc),
        M.toRep.eqCast_rfl]
  obtain ⟨s', hs'⟩ := hτ
  obtain ⟨β, hβ⟩ := formula_of_Pof K L h hc (beta0 K L h) s'
  refine ⟨β, fun M w z => ?_⟩
  have hc' : c • gelfandStar K L h = (GΓ K L h).vertexRep (nStar K L h) := by
    rw [vertexRep_star]; exact gelfand_smul_star K L h hc
  rw [composite_raw K L h M hc w z, map_add, map_smul, map_smul, hs M w, hs' M w,
    eqCast_symm_apply', φ'_eqCast M.toRep c (vertexRep_star K L h).symm _ hc',
    eqCast_φ' M.toRep c hc' (vertexRep_star K L h) (gelfand_smul_star K L h hc),
    φ'_Pof K L h M.toRep hc, φ'_of_mem_vertexFixed M.toRep (toStar_mem K L h M w) c
      (gelfand_smul_star K L h hc) (gelfand_smul_star K L h hc), M.toRep.eqCast_rfl, hβ]

/-- `exists_beta` at an arbitrary length-two path `(i, j, k) = (⋆, ±, ⋆)`, which is how
`Species.Satisfies` quantifies.  @census none (helper; RQ2-2.37 support) -/
theorem exists_beta_idx {c : Gal(L/K)} (hc : c ≠ 1) :
    ∃ β : Gal(L/K), ∀ (M : FDRep (GΓ K L h)) {i j k : (SG K L h).I}
      (_ : i = nStar K L h) (_ : j = nPm K L h) (_ : k = nStar K L h)
      (hvi : (GΓ K L h).vertexRep i = gelfandStar K L h)
      (hvk : (GΓ K L h).vertexRep k = gelfandStar K L h)
      (w : ((FFunctor (GΓ K L h)).obj M).W i) (z : L),
      M.toRep.eqCast hvk
        (wv M k (((FFunctor (GΓ K L h)).obj M).f j k
          (Balanced.mk (((FFunctor (GΓ K L h)).obj M).f i j
              (Balanced.mk w (cst K L h (i := i) (j := j) z)))
            (cst K L h (i := j) (j := k) 1))))
        = β z • M.toRep.pathMap (gelfandPathMinus K L h) (M.toRep.eqCast hvi (wv M i w))
          + c (β z) • M.toRep.pathMap (gelfandPathPlus K L h)
              (M.toRep.eqCast hvi (wv M i w)) := by
  obtain ⟨β, hβ⟩ := exists_beta K L h hc
  refine ⟨β, fun M i j k hi hj hk hvi hvk w z => ?_⟩
  subst hi; subst hj; subst hk
  exact hβ M w z

omit [IsGalois K L] [FiniteDimensional K L] in
include h in
/-- `c(β(α)) = -β(α)` when `c(α) = -α`: `Gal(L/K)` is abelian.
@census none (helper; RQ2-2.37 support) -/
theorem apply_neg_of_conj {c : Gal(L/K)} (hc : c ≠ 1) {α : L} (hα : c α = -α) (β : Gal(L/K)) :
    c (β α) = -(β α) := by
  rcases eq_one_or_eq K L h hc β with rfl | rfl
  · simpa using hα
  · rw [hα, map_neg, hα]

/-- **`RQ2-2.37` — `ex:gelfandspeciesrelation`.**  `F(M)` satisfies `R_Gelfand` **iff** `M`
satisfies the relation `a₋b₋ = a₊b₊` (clause `C3`'s conclusion; the formula is `exists_beta`).
Clauses `C1` (`thetaEquiv`, `finrank_pathBimod`), `C2` (`RGelfand`, `theta_relGen`) and `C4`
(`satisfies_RGelfand_iff_pair`, `RGelfand_genuine`) are the other declarations of this module.
*(2026-10-03, `R-FR-9`, final-release WP-16b.)* `C4`'s first half as re-synced by census r18 (the
descent form: satisfies iff `X = Y` on `W_⋆` iff `X` is `ℚ`-rational) is stated faithfully only by
`GelfandRelation.satisfies_RGelfand_iff_rational` (`Species/Rep/ReleaseAddenda.lean`, WP-16a);
`satisfies_RGelfand_iff_pair` states the retired "pair" reading, see its docstring.

At `K = ℚ`, `L = ℚ[√-1]`, `c` the conjugation and `α = √-1` the hypotheses `c(α) = -α`, `α ≠ 0`
were v1's `Gelfand.galConj_iQi` and `Gelfand.iQi_ne_zero` (S8; deleted with the v1 Q-chain at WP-13,
`ae9eda9`, 2026-10-21 note, O-V2-6 round 2), and the statement is the source's.
The proof is the source's: at `z = α` the right-hand side of `eq:gelfandspeciescomposite` is
`β(α)·(φ_{a₋}φ_{b₋} − φ_{a₊}φ_{b₊})(w)`, and `M(⋆) = W_⋆ ⊗_K L` (`vertexDescentEquiv`, the
source's `eq:WitoMvi`) extends the vanishing from `W_⋆` to `M(⋆)`.

@census    RQ2-2.37
@source    ex:gelfandspeciesrelation
@clauses   RQ2-2.37-C3
@imports   none
@divergence JUSTIFIED_REFORMULATION (the choice of representatives, coordinator ruling
`R-ERR-5`, 2026-09-12, round-5 brief).  The source chooses `−` as the representative of the orbit
`{+,−}` and `a₋`, `b₋` as the representatives of the two edge orbits, and states
`eq:gelfandspeciescomposite` against the identification `θ : {}_⋆M_p ≅ ℚ[√-1]` that those
choices induce.  The tree's representatives are `Quotient.out`- and `Classical.choose`-defined
(`vertexRep`, `edgeRep`, `EdgeChoice.choose`), so the identity holds against `β ∘ θ` for a single
`β ∈ Gal(L/K)` fixed by those choices (`exists_beta`) — the same formula, with the generic
identification.  Since `β ∈ {1, c}` and `c` preserves the line `K·α`, the relation `R_Gelfand`
(clause `C2`) is unaffected and this iff is stated exactly as printed.  The generalisation from
`ℚ ⊆ ℚ[√-1]` to a quadratic Galois `K ⊆ L` is the one `Species/Rep/GelfandDescent.lean` was
forced into (`R-ERR-4`); the printed case is `K = ℚ`, `L = ℚ[√-1]`, `α = √-1`. -/
theorem satisfies_RGelfand_iff_relation (M : FDRep (GΓ K L h)) {c : Gal(L/K)} (hc : c ≠ 1)
    {α : L} (hα : c α = -α) (hα0 : α ≠ 0) :
    Species.Satisfies (SG K L h) ((FFunctor (GΓ K L h)).obj M) (RGelfand K L h α) ↔
      SatisfiesGelfandRelation K L h M.toRep := by
  obtain ⟨β, hβ⟩ := exists_beta_idx K L h hc
  have hneg : c (β α) = -(β α) := apply_neg_of_conj K L h hc hα β
  have hβα : β α ≠ 0 := fun h0 => hα0 (β.injective (by rw [h0, map_zero]))
  constructor
  · intro hsat
    have key : ∀ w : ((FFunctor (GΓ K L h)).obj M).W (nStar K L h),
        M.toRep.pathMap (gelfandPathMinus K L h) (toStar K L h M w)
          = M.toRep.pathMap (gelfandPathPlus K L h) (toStar K L h M w) := by
      intro w
      have h0 := (satisfies_RGelfand_iff K L h _ α).mp hsat (idxG K L h) rfl rfl rfl w
      unfold relGen at h0
      rw [pathHom_one_mk] at h0
      have h1 := hβ M (i := idxG K L h 0) (j := idxG K L h 1) (k := idxG K L h 2) rfl rfl rfl
        (vertexRep_star K L h) (vertexRep_star K L h) w α
      rw [h0, wv_zero, map_zero, hneg, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h1
      exact sub_eq_zero.mp ((smul_eq_zero.mp h1.symm).resolve_left hβα)
    refine LinearMap.ext fun x => ?_
    obtain ⟨t, rfl⟩ := (vertexDescentEquiv M.toRep (gelfandStar K L h)).surjective x
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a m =>
        rw [vertexDescentEquiv_tmul, map_smul, map_smul]
        congr 1
        have hm : M.toRep.eqCast (vertexRep_star K L h).symm (m : M.toRep.M _)
            ∈ M.toRep.vertexFixed ((GΓ K L h).vertexRep (nStar K L h)) :=
          mem_vertexFixed_eqCast M.toRep _ m.2
        have := key ⟨_, hm⟩
        unfold toStar at this
        rwa [show wv M (nStar K L h) ⟨_, hm⟩ = M.toRep.eqCast (vertexRep_star K L h).symm m
          from rfl, M.toRep.eqCast_symm_apply] at this
    | add s t hs ht => rw [map_add, map_add, map_add, hs, ht]
  · intro hrel
    rw [satisfies_RGelfand_iff]
    intro idx h0 h1 h2 w
    unfold relGen
    rw [pathHom_one_mk]
    have hvk : (GΓ K L h).vertexRep (idx 2) = gelfandStar K L h := by
      rw [h2]; exact vertexRep_star K L h
    have hvi : (GΓ K L h).vertexRep (idx 0) = gelfandStar K L h := by
      rw [h0]; exact vertexRep_star K L h
    refine wv_inj M (idx 2) ?_
    rw [wv_zero]
    refine (M.toRep.eqCast hvk).injective ?_
    rw [map_zero, hβ M h0 h1 h2 hvi hvk w α, hneg, neg_smul,
      show M.toRep.pathMap (gelfandPathMinus K L h) = M.toRep.pathMap (gelfandPathPlus K L h)
        from hrel, add_neg_cancel]

/-! ### `RQ2-2.37-C4` -/

/-- **Clause `RQ2-2.37-C4`, first half, partial.** Under `F`, satisfying the one species relation is
satisfying **both** quiver relations `a₋b₋ = a₊b₊` and `a₊b₊ = a₋b₋`. `C3` makes the species
relation the quiver relation, and the second member is the symmetry of equality
(`gelfand_relation_iff_transpose`, first conjunct).

*(Amended 2026-10-03, docstring-only `R-PROC-4` amendment of frozen S5, coordinator ruling
`R-FR-9`, final-release WP-16b, stale item R8, `MISMATCH-TRIAGE.md` row #7.)* Until this amendment
this docstring quoted the clause as *"passing to the species has identified the two with one
another"*. Census r18 (FA-05) retired that reading. `C4`'s first half now says that `R_Gelfand` is
the **descent** of the `G`-stable relation set: `F(M)` satisfies `R_Gelfand` iff `X = Y` on `W_⋆`,
i.e. iff `X := φ_{a₋}φ_{b₋}` commutes with `φ_{⋆,c}` and is thus `ℚ`-rational. This theorem does
not state that. The faithful witness is
`RationalQuivers.GelfandRelation.satisfies_RGelfand_iff_rational`
(`Species/Rep/ReleaseAddenda.lean`, final-release WP-16a): `Satisfies ↔ (X = Y on W_⋆)`,
`↔ (X commutes with φ_{⋆,c})`, plus the conjugacy `φ_{⋆,c} ∘ X = Y ∘ φ_{⋆,c}`. This theorem keeps
its `@clauses` citation because `rqaudit clauses` binds a clause only to a claimant of its row or a
same-module helper of one, and the WP-16a witness lives in another module. The citation records
the retired reading. It is not a discharge of the r18 text.

@census none (clause witness for `RQ2-2.37-C4`)
@clauses   RQ2-2.37-C4 -/
theorem satisfies_RGelfand_iff_pair (M : FDRep (GΓ K L h)) {c : Gal(L/K)} (hc : c ≠ 1)
    {α : L} (hα : c α = -α) (hα0 : α ≠ 0) :
    Species.Satisfies (SG K L h) ((FFunctor (GΓ K L h)).obj M) (RGelfand K L h α) ↔
      (SatisfiesGelfandRelation K L h M.toRep ∧ SatisfiesGelfandRelationSwap K L h M.toRep) := by
  rw [satisfies_RGelfand_iff_relation K L h M hc hα hα0]
  exact ⟨fun hr => ⟨hr, (gelfand_relation_iff_transpose K L h hc M.toRep).1.mp hr⟩,
    fun hr => hr.1⟩

/-- `gelfandNilTwist` as a finite-dimensional representation: `L × L` at every vertex.
@census none (helper; RQ2-2.37 support) -/
noncomputable def nilTwistFD {c : Gal(L/K)} (hc : c ≠ 1) (α : L) : FDRep (GΓ K L h) where
  toRep := gelfandNilTwist K L h hc α
  finiteDimensional _ := inferInstanceAs (FiniteDimensional L (L × L))

/-- **Clause `RQ2-2.37-C4`, second half** — *"It is, however, a genuine condition on `(W,f)`, and
not one that `G`-equivariance already supplies: … equivariance guarantees only that the two
composites appearing in `eq:gelfandspeciescomposite` are `φ_{⋆,c}`-conjugate, whereas `R_Gelfand`
asserts their equality."*  First conjunct: the conjugacy, `RQ2-2.16-C3`
(`gelfand_relation_conjugate`).  Second conjunct: the condition is genuine, and genuinely so in
the nilpotent setting of `RQ-5.06` — `F` of the **nilpotent** `gelfandNilTwist` (`RQ2-2.16-C11`'s
witness, `gelfand_relation_not_consequence_nil`) does not satisfy `R_Gelfand`, by `C3`.

@census none (clause witness for `RQ2-2.37-C4`)
@clauses   RQ2-2.37-C4 -/
theorem RGelfand_genuine {c : Gal(L/K)} (hc : c ≠ 1) {α : L} (hα : c α = -α) (hα0 : α ≠ 0) :
    (∀ (M : Rep (GΓ K L h)) (m : M.M (gelfandStar K L h)),
        M.φ' c (gelfand_smul_star K L h hc) (M.pathMap (gelfandPathMinus K L h) m)
          = M.pathMap (gelfandPathPlus K L h) (M.φ' c (gelfand_smul_star K L h hc) m)) ∧
      ∃ M : FDRep (GΓ K L h), M.toRep.IsNilpotent ∧
        ¬ Species.Satisfies (SG K L h) ((FFunctor (GΓ K L h)).obj M) (RGelfand K L h α) := by
  refine ⟨fun M m => gelfand_relation_conjugate K L h hc M m, ?_⟩
  obtain ⟨α₀, hα₀⟩ := DFunLike.ne_iff.mp hc
  refine ⟨nilTwistFD K L h hc α₀, gelfandNilTwist_isNilpotent K L h hc α₀, ?_⟩
  rw [satisfies_RGelfand_iff_relation K L h _ hc hα hα0]
  exact gelfand_relation_not_consequence_nil K L h hc α₀ hα₀

/-! ### Transport across isomorphisms, and the coincidence theorem -/

/-- Satisfying `R_Gelfand` is invariant under isomorphism of species representations: on a
length-two path `f_p` is two structure maps (`pathHom_one_mk`), and a morphism intertwines each
(`Species.Rep.Hom.comm_mk`).  The shape is that of v1's S8 `satisfiesGelfandRelation_of_iso` (round
3; deleted with the v1 Q-chain at WP-13, `ae9eda9`, 2026-10-21 note, O-V2-6 round 2).
@census none (helper; the coincidence theorem) -/
theorem satisfies_RGelfand_of_iso {V V' : Species.Rep (SG K L h)} (e : V ≅ V') (α : L)
    (hV : Species.Satisfies (SG K L h) V (RGelfand K L h α)) :
    Species.Satisfies (SG K L h) V' (RGelfand K L h α) := by
  rw [satisfies_RGelfand_iff] at hV ⊢
  intro idx h0 h1 h2 w'
  have hw' : w' = (e.hom).ψ (idx 0) ((e.inv).ψ (idx 0) w') :=
    (congrArg (fun t : V' ⟶ V' => t.ψ (idx 0) w') e.inv_hom_id).symm
  rw [hw']
  unfold relGen
  rw [pathHom_one_mk, Species.Rep.Hom.comm_mk, Species.Rep.Hom.comm_mk, ← pathHom_one_mk]
  have := hV idx h0 h1 h2 ((e.inv).ψ (idx 0) w')
  unfold relGen at this
  rw [this, map_zero]

/-- **The coincidence theorem** (round-5 brief, task C).  The **intrinsic** category
`Rep^nil(S(Γ_K), R_Gelfand)` of `RQ2-2.36-C5` coincides with the **transported** one that S8's
`Gelfand/Corollaries.lean` stated `RQ-5.06-C1` against from the G2 repair round until 2026-09-12:
a species representation `W` is nilpotent and satisfies `R_Gelfand` **iff** it is nilpotent and
isomorphic to `F(M)` for a quiver representation `M` satisfying `a₋b₋ = a₊b₊`.  Essential
surjectivity of `F` is S5's own `species_equivalence_tree` (Theorem B at the tree's functors);
the relation moves across `F` by `C3` and across the isomorphism by `satisfies_RGelfand_of_iso`.
v1's S8 instantiated this at `ℚ ⊆ ℚ[√-1]`, `α = √-1` (`Gelfand.repNilRelSpeciesGelfand_iff`, deleted
with the v1 Q-chain at WP-13, `ae9eda9`); on the v2 line `Gelfand.Species.repNilRel_RE_iff`
instantiates it at `E ⊆ L_E`, `α = √-1`, for every `E ∌ √-1` (2026-10-21, O-V2-6 round 2).
@census none (helper; the coincidence theorem, consumed by `RQ-5.06-C1`) -/
theorem repNilRel_RGelfand_iff {c : Gal(L/K)} (hc : c ≠ 1) {α : L} (hα : c α = -α)
    (hα0 : α ≠ 0) (W : EtaleSpecies.Rep (ES K L h)) :
    Species.RepNilRel (SG K L h) (RGelfand K L h α) W ↔
      (W.IsNilpotent ∧ ∃ M : FDRep (GΓ K L h), SatisfiesGelfandRelation K L h M.toRep ∧
        Nonempty ((FFunctor (GΓ K L h)).obj M ≅ W)) := by
  constructor
  · rintro ⟨hnil, hsat⟩
    obtain ⟨WK, hWK, e, hF, -⟩ := species_equivalence_tree (GΓ K L h)
    have hiso : (FFunctor (GΓ K L h)).obj (e.inverse.obj W) ≅ W := hF ▸ e.counitIso.app W
    refine ⟨hnil, e.inverse.obj W, ?_, ⟨hiso⟩⟩
    rw [← satisfies_RGelfand_iff_relation K L h _ hc hα hα0]
    exact satisfies_RGelfand_of_iso K L h hiso.symm α hsat
  · rintro ⟨hnil, M, hrel, ⟨iso⟩⟩
    exact ⟨hnil, satisfies_RGelfand_of_iso K L h iso α
      ((satisfies_RGelfand_iff_relation K L h M hc hα hα0).mpr hrel)⟩

end Composite

end GelfandRelation

end RationalQuivers
