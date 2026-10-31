module

public import RationalQuivers.Gelfand.BaseChange.NNHC
public import RationalQuivers.HC.Normalization

@[expose] public section

/-!
# Unipotent stabilization commutes with base change (WP-15, T1 case (2), the canonicity step)

*Provenance.*  Relocated in stage T4 (WP-11) from `GF/BaseChangeNNStab.lean` (v1 `RationalQuivers.Gelfand.GF`) by `workflow/v2/stages/T4/VALIDATION/scripts/relocate_bc.py`: whole file, declarations moved from `GF.x` to `Gelfand.BaseChange.x` (renames in the T4 `DECL-ALLOWLIST.tsv`), references qualified, the imports of v1's `GF/Main`/`GF/Species` cut; statements and proofs otherwise unchanged.  The native statement on `HC ℓ E D`/`𝔼_E` (`prop:basechange`, `RQ2-5.14`) is in `Gelfand/BaseChange/Native.lean`.

*(2026-10-21, O-V2-6 round 2.)*  "The tree's own `seq_natural` / `lim_natural`
(`GF/Stabilization.lean`)" below is the v1 location.  Since WP-10 (`542ebf7`) these are
`RationalStructure.seq_natural` and `RationalStructure.lim_natural` in
`Gelfand/RationalStructure/Stabilization.lean`.

The rational structure of `𝔼_E(M)` is `φ_{v,c} = c ∘ φ^{(∞)}_v`, where `φ^{(∞)}_v` is the eventual
value of the deterministic recursion `φ^{(0)} = φ`, `φ^{(k+1)}_± = ½(φ^{(k)}_± + ((φ^{(k)}_∓)^τ)^{-1})`
of `cor:unipotentstabilization` (`StabInput.limPlus`).  This module proves that `φ^{(∞)}` commutes
with base change `E(√-1) → E''(√-1)`:

  `φ''^{(∞)}_v (1 ⊗ m) = 1 ⊗ φ^{(∞)}_v (m)`     (`limAt_bcNN`).

The proof is the semilinear version of the tree's own `seq_natural` / `lim_natural`
(`GF/Stabilization.lean`), where `f : M → M'` was `E(√-1)`-linear between two setups over the
**same** `(E, E(√-1))`.  Here `f : M_{E(√-1)} → M_{E''(√-1)}` is `E(√-1)`-linear into an
`E''(√-1)`-module (a scalar tower), between setups over `(E, E(√-1))` and `(E'', E''(√-1))`.  The
induction step uses only additivity, `f(½ x) = ½ f(x)`, the grading, `f ∘ c = c'' ∘ f` and the
uniqueness of two-sided inverses; both recursions stabilize (`stab_limit_spec`), so the limits
agree past the larger of the two exponents.  **No choice enters**: the stabilization is canonical,
and so it is compatible with base change.
-/

namespace RationalQuivers.Gelfand.BaseChange

open RationalQuivers.HC RationalQuivers.Unipotent RationalQuivers.Gelfand
open CategoryTheory
open scoped TensorProduct

section StabBC

variable {E : Type} [Field E] [CharZero E] {D : SqrtNegOneExt E}
variable {E'' : Type} [Field E''] [CharZero E''] {D'' : SqrtNegOneExt E''}
variable [Algebra D.carrier D''.carrier]
variable {ℓ : ℕ} {Mq Mi : Type} [AddCommGroup Mq] [Module E Mq] [AddCommGroup Mi]
  [Module D.carrier Mi]
variable {Mq'' Mi'' : Type} [AddCommGroup Mq''] [Module E'' Mq''] [AddCommGroup Mi'']
  [Module D''.carrier Mi''] [Module D.carrier Mi''] [IsScalarTower D.carrier D''.carrier Mi'']
variable {S : RationalSetupOver ℓ E D Mq Mi} {T : RationalSetupOver ℓ E'' D'' Mq'' Mi''}

variable (D'') in
/-- A scalar of `E(√-1)` acts on an `E''(√-1)`-module through `ι`.  @census none (helper; WP-15) -/
theorem smul_bc (r : D.carrier) (y : Mi'') : r • y = algebraMap D.carrier D''.carrier r • y :=
  (algebraMap_smul D''.carrier r y).symm

/-- A map commuting with `H`, `X`, `Y` commutes with the Casimir.  @census none (helper; WP-15) -/
theorem map_casimir_bc (f : Mi →ₗ[D.carrier] Mi'')
    (hH : ∀ v, f (S.weight.H v) = T.weight.H (f v))
    (hX : ∀ v, f (S.weight.X v) = T.weight.X (f v))
    (hY : ∀ v, f (S.weight.Y v) = T.weight.Y (f v)) (v : Mi) :
    f (S.weight.casimir v) = T.weight.casimir (f v) := by
  rw [S.weight.casimir_apply, T.weight.casimir_apply, map_add, map_add, map_sub, map_smul,
    map_smul, hH, hH, hX, hY, smul_bc D'' (2 : D.carrier), smul_bc D'' (4 : D.carrier),
    map_ofNat, map_ofNat]

/-- ... hence with every Casimir factor product.  @census none (helper; WP-15) -/
theorem map_casimirFactorProd_bc (f : Mi →ₗ[D.carrier] Mi'')
    (hH : ∀ v, f (S.weight.H v) = T.weight.H (f v))
    (hX : ∀ v, f (S.weight.X v) = T.weight.X (f v))
    (hY : ∀ v, f (S.weight.Y v) = T.weight.Y (f v)) :
    ∀ (k : ℤ) (m : ℕ) (v : Mi),
      f (casimirFactorProd S.weight.casimir k m v)
        = casimirFactorProd T.weight.casimir k m (f v)
  | _, 0, v => by simp [casimirFactorProd_zero]
  | k, (m + 1), v => by
      rw [casimirFactorProd_succ, casimirFactorProd_succ, Module.End.mul_apply,
        Module.End.mul_apply, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, map_sub, map_smul,
        map_casimir_bc f hH hX hY, map_casimirFactorProd_bc f hH hX hY (k - 2) m v, smul_bc D'',
        map_pow, map_intCast]

/-- ... hence with `T₋`.  @census none (helper; WP-15) -/
theorem map_tMinus_bc (f : Mi →ₗ[D.carrier] Mi'')
    (hH : ∀ v, f (S.weight.H v) = T.weight.H (f v))
    (hX : ∀ v, f (S.weight.X v) = T.weight.X (f v))
    (hY : ∀ v, f (S.weight.Y v) = T.weight.Y (f v)) (v : Mi) :
    f (Split.tMinus S.toQiSetup v) = Split.tMinus T.toQiSetup (f v) := by
  show f ((((4 : D.carrier) ^ (ℓ - 1) * Split.gammaStarF D.carrier ℓ ^ 2)⁻¹)
      • casimirFactorProd S.weight.casimir ((ℓ : ℤ) - 2) (ℓ - 1) v)
    = (((4 : D''.carrier) ^ (ℓ - 1) * Split.gammaStarF D''.carrier ℓ ^ 2)⁻¹)
      • casimirFactorProd T.weight.casimir ((ℓ : ℤ) - 2) (ℓ - 1) (f v)
  rw [map_smul, map_casimirFactorProd_bc f hH hX hY, smul_bc D'', map_inv₀, map_mul, map_pow, map_pow,
    map_ofNat, algebraMap_gammaStarF]

omit [Algebra D.carrier D''.carrier] [IsScalarTower D.carrier D''.carrier Mi''] in
/-- ... and with `X^r`.  @census none (helper; WP-15) -/
theorem map_pow_X_bc (f : Mi →ₗ[D.carrier] Mi'')
    (hX : ∀ v, f (S.weight.X v) = T.weight.X (f v)) :
    ∀ (r : ℕ) (v : Mi), f ((S.weight.X ^ r) v) = (T.weight.X ^ r) (f v)
  | 0, v => by simp
  | (r + 1), v => by
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply,
        map_pow_X_bc f hX r, hX]

/-- ... hence with `X⋆`.  @census none (helper; WP-15) -/
theorem map_xStar_bc (f : Mi →ₗ[D.carrier] Mi'')
    (hX : ∀ v, f (S.weight.X v) = T.weight.X (f v)) (v : Mi) :
    f (Split.xStar S.toQiSetup v) = Split.xStar T.toQiSetup (f v) := by
  show f (((Split.gammaStarF D.carrier ℓ)⁻¹ : D.carrier) • (S.weight.X ^ (ℓ - 1)) v)
    = ((Split.gammaStarF D''.carrier ℓ)⁻¹ : D''.carrier) • (T.weight.X ^ (ℓ - 1)) (f v)
  rw [map_smul, map_pow_X_bc f hX, smul_bc D'', map_inv₀, algebraMap_gammaStarF]

/-- **The iterates commute with base change** — `seq_natural` for an `E(√-1)`-linear
`f : M_{E(√-1)} → M_{E''(√-1)}`.  @census none (helper; WP-15) -/
theorem seq_natural_bc (CS : Gelfand.RationalStructure.StabInput S) (CT : Gelfand.RationalStructure.StabInput T) (f : Mi →ₗ[D.carrier] Mi'')
    (hmem : ∀ (n : ℤ) (v : Mi), v ∈ S.weight.comp n → f v ∈ T.weight.comp n)
    (hconj : ∀ v, f (S.conj v) = T.conj (f v))
    (hp : CT.idxPlus = CS.idxPlus) (hm : CT.idxMinus = CS.idxMinus)
    (hfp : ∀ v ∈ S.weight.comp CS.idxPlus, f (CS.phiPlus v) = CT.phiPlus (f v))
    (hfm : ∀ v ∈ S.weight.comp CS.idxMinus, f (CS.phiMinus v) = CT.phiMinus (f v))
    (hpS : HasInverse CS.phpT) (hmS : HasInverse CS.phmT)
    {nS : Module.End D.carrier (Gelfand.RationalStructure.Wc S CS.idxPlus)} (hnilS : IsNilpotent nS)
    (hnS : (twistConj Gelfand.RationalStructure.galConj_mul_self CS.phmT).comp CS.phpT = 1 + nS)
    (hpT : HasInverse CT.phpT) (hmT : HasInverse CT.phmT)
    {nT : Module.End D''.carrier (Gelfand.RationalStructure.Wc T CT.idxPlus)} (hnilT : IsNilpotent nT)
    (hnT : (twistConj Gelfand.RationalStructure.galConj_mul_self CT.phmT).comp CT.phpT = 1 + nT) :
    ∀ k, (∀ v ∈ S.weight.comp CS.idxPlus, f (CS.seqPlus k v) = CT.seqPlus k (f v)) ∧
      (∀ v ∈ S.weight.comp CS.idxMinus, f (CS.seqMinus k v) = CT.seqMinus k (f v)) := by
  intro k
  induction k with
  | zero =>
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [CS.seqPlus_zero_apply v hv,
        CT.seqPlus_zero_apply (f v) (by rw [hp]; exact hmem _ _ hv), hfp v hv]
    · rw [CS.seqMinus_zero_apply v hv,
        CT.seqMinus_zero_apply (f v) (by rw [hm]; exact hmem _ _ hv), hfm v hv]
  | succ k ih =>
    obtain ⟨h1S, h2S⟩ := CS.hasInverse_seqT hpS hmS hnilS hnS k
    obtain ⟨h1T, h2T⟩ := CT.hasInverse_seqT hpT hmT hnilT hnT k
    have hIP : ∀ v ∈ S.weight.comp CS.idxPlus,
        f (CS.seqInvPlus k v) = CT.seqInvPlus k (f v) := by
      intro v hv
      have hΨ : CS.seqInvPlus k v ∈ S.weight.comp (-CS.idxMinus) := CS.seqInvPlus_mem k v
      have hcΨ : S.conj (CS.seqInvPlus k v) ∈ S.weight.comp CS.idxMinus := Gelfand.RationalStructure.conj_comp' S hΨ
      have hfΨ : f (CS.seqInvPlus k v) ∈ T.weight.comp (-CT.idxMinus) := by
        rw [hm]; exact hmem _ _ hΨ
      have e1 := CS.seqInvPlus_right k h2S v hv
      have e2 := CT.seqInvPlus_left' k (hasInverse_of_twistConj _ h2T) _ hfΨ
      calc f (CS.seqInvPlus k v)
          = CT.seqInvPlus k (T.conj (CT.seqMinus k (T.conj (f (CS.seqInvPlus k v))))) := e2.symm
        _ = CT.seqInvPlus k (f v) := by
              rw [← hconj, ← ih.2 _ hcΨ, ← hconj, e1]
    have hIM : ∀ v ∈ S.weight.comp CS.idxMinus,
        f (CS.seqInvMinus k v) = CT.seqInvMinus k (f v) := by
      intro v hv
      have hΨ : CS.seqInvMinus k v ∈ S.weight.comp (-CS.idxPlus) := CS.seqInvMinus_mem k v
      have hcΨ : S.conj (CS.seqInvMinus k v) ∈ S.weight.comp CS.idxPlus := Gelfand.RationalStructure.conj_comp' S hΨ
      have hfΨ : f (CS.seqInvMinus k v) ∈ T.weight.comp (-CT.idxPlus) := by
        rw [hp]; exact hmem _ _ hΨ
      have e1 := CS.seqInvMinus_right k (h1S.twistConj _) v hv
      have e2 := CT.seqInvMinus_left' k h1T _ hfΨ
      calc f (CS.seqInvMinus k v)
          = CT.seqInvMinus k (T.conj (CT.seqPlus k (T.conj (f (CS.seqInvMinus k v))))) := e2.symm
        _ = CT.seqInvMinus k (f v) := by
              rw [← hconj, ← ih.1 _ hcΨ, ← hconj, e1]
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [CS.seqPlus_succ, CT.seqPlus_succ, LinearMap.smul_apply, LinearMap.smul_apply,
        LinearMap.add_apply, LinearMap.add_apply, map_smul, map_add, ih.1 v hv, hIP v hv, smul_bc D'',
        map_inv₀, map_ofNat]
    · rw [CS.seqMinus_succ, CT.seqMinus_succ, LinearMap.smul_apply, LinearMap.smul_apply,
        LinearMap.add_apply, LinearMap.add_apply, map_smul, map_add, ih.2 v hv, hIM v hv, smul_bc D'',
        map_inv₀, map_ofNat]

/-- **The limits commute with base change** — `lim_natural` for an `E(√-1)`-linear
`f : M_{E(√-1)} → M_{E''(√-1)}`, on `W₊`.  @census none (helper; WP-15) -/
theorem lim_natural_bc (CS : Gelfand.RationalStructure.StabInput S) (CT : Gelfand.RationalStructure.StabInput T) (f : Mi →ₗ[D.carrier] Mi'')
    (hmem : ∀ (n : ℤ) (v : Mi), v ∈ S.weight.comp n → f v ∈ T.weight.comp n)
    (hconj : ∀ v, f (S.conj v) = T.conj (f v))
    (hp : CT.idxPlus = CS.idxPlus) (hm : CT.idxMinus = CS.idxMinus)
    (hfp : ∀ v ∈ S.weight.comp CS.idxPlus, f (CS.phiPlus v) = CT.phiPlus (f v))
    (hfm : ∀ v ∈ S.weight.comp CS.idxMinus, f (CS.phiMinus v) = CT.phiMinus (f v))
    (hpS : HasInverse CS.phpT) (hmS : HasInverse CS.phmT)
    {nS : Module.End D.carrier (Gelfand.RationalStructure.Wc S CS.idxPlus)} (hnilS : IsNilpotent nS)
    (hnS : (twistConj Gelfand.RationalStructure.galConj_mul_self CS.phmT).comp CS.phpT = 1 + nS)
    (hpT : HasInverse CT.phpT) (hmT : HasInverse CT.phmT)
    {nT : Module.End D''.carrier (Gelfand.RationalStructure.Wc T CT.idxPlus)} (hnilT : IsNilpotent nT)
    (hnT : (twistConj Gelfand.RationalStructure.galConj_mul_self CT.phmT).comp CT.phpT = 1 + nT) :
    ∀ v ∈ S.weight.comp CS.idxPlus, f (CS.limPlus v) = CT.limPlus (f v) := by
  obtain ⟨eS, hconstS, hlimS, -, -, -, -⟩ := Gelfand.RationalStructure.stab_limit_spec CS hpS hmS hnilS hnS
  obtain ⟨eT, hconstT, hlimT, -, -, -, -⟩ := Gelfand.RationalStructure.stab_limit_spec CT hpT hmT hnilT hnT
  have hS : CS.limPlus = CS.seqPlus (max eS eT) := by
    show Gelfand.RationalStructure.toEnd S (CS.limT).1 = Gelfand.RationalStructure.toEnd S (CS.seqT (max eS eT)).1
    rw [hlimS, ← hconstS _ (le_max_left eS eT)]
  have hT : CT.limPlus = CT.seqPlus (max eS eT) := by
    show Gelfand.RationalStructure.toEnd T (CT.limT).1 = Gelfand.RationalStructure.toEnd T (CT.seqT (max eS eT)).1
    rw [hlimT, ← hconstT _ (le_max_right eS eT)]
  intro v hv
  rw [hS, hT]
  exact (seq_natural_bc CS CT f hmem hconj hp hm hfp hfm hpS hmS hnilS hnS hpT hmT hnilT hnT
    (max eS eT)).1 v hv

omit [Algebra D.carrier D''.carrier] [IsScalarTower D.carrier D''.carrier Mi''] in
/-- `lim_natural_bc` on the whole module, given that `f` commutes with the projection onto the
component `W₊`.  @census none (helper; WP-15) -/
theorem lim_natural_bc_all (CS : Gelfand.RationalStructure.StabInput S) (CT : Gelfand.RationalStructure.StabInput T) (f : Mi →ₗ[D.carrier] Mi'')
    (hproj : ∀ m, T.weight.proj CT.idxPlus (f m) = f (S.weight.proj CS.idxPlus m))
    (hnat : ∀ u ∈ S.weight.comp CS.idxPlus, f (CS.limPlus u) = CT.limPlus (f u)) (m : Mi) :
    f (CS.limPlus m) = CT.limPlus (f m) := by
  have h1 : CS.limPlus m = CS.limPlus (S.weight.proj CS.idxPlus m) :=
    Gelfand.RationalStructure.toEnd_apply_proj (CS.limT).1 m
  have h2 : CT.limPlus (f m) = CT.limPlus (T.weight.proj CT.idxPlus (f m)) :=
    Gelfand.RationalStructure.toEnd_apply_proj (CT.limT).1 _
  rw [h1, h2, hproj, hnat _ (S.weight.proj_mem CS.idxPlus m)]

end StabBC

/-! ## The three runs of `𝔼`, under the `nn` base change -/

section LimAt

variable {ℓ : ℕ}
variable {E : Type} [Field E] [CharZero E] {D : SqrtNegOneExt E}
variable {E'' : Type} [Field E''] [CharZero E''] {D'' : SqrtNegOneExt E''}
variable [Algebra E E''] [Algebra D.carrier D''.carrier] [Algebra E D''.carrier]
  [IsScalarTower E E'' D''.carrier] [IsScalarTower E D.carrier D''.carrier]

variable (D'') in
/-- `1 ⊗ −`, `E(√-1)`-linearly.  @census none (helper; WP-15) -/
noncomputable abbrev bcOne (A : HCEObj ℓ E D) : A.carrier →ₗ[D.carrier] D''.carrier ⊗[D.carrier] A.carrier :=
  TensorProduct.mk D.carrier D''.carrier A.carrier 1

theorem bcOne_mem (hι : ConjCompat D D'') (A : HCEObj ℓ E D) (n : ℤ) (x : A.carrier)
    (hx : x ∈ A.setup.weight.comp n) : bcOne D'' A x ∈ (A.bcNN hι).setup.weight.comp n :=
  Submodule.tmul_mem_baseChange_of_mem _ hx

theorem bcOne_conj (hι : ConjCompat D D'') (A : HCEObj ℓ E D) (x : A.carrier) :
    bcOne D'' A (A.setup.conj x) = (A.bcNN hι).setup.conj (bcOne D'' A x) := by
  show (1 : D''.carrier) ⊗ₜ[D.carrier] A.setup.conj x
    = conjBC hι A.setup.conj A.setup.conj_smul A.setup.conj_involutive (1 ⊗ₜ x)
  rw [conjBC_tmul, map_one]

theorem bcOne_H (hι : ConjCompat D D'') (A : HCEObj ℓ E D) (x : A.carrier) :
    bcOne D'' A (A.setup.weight.H x) = (A.bcNN hι).setup.weight.H (bcOne D'' A x) :=
  (LinearMap.baseChange_tmul _ _ _).symm

theorem bcOne_X (hι : ConjCompat D D'') (A : HCEObj ℓ E D) (x : A.carrier) :
    bcOne D'' A (A.setup.weight.X x) = (A.bcNN hι).setup.weight.X (bcOne D'' A x) :=
  (LinearMap.baseChange_tmul _ _ _).symm

theorem bcOne_Y (hι : ConjCompat D D'') (A : HCEObj ℓ E D) (x : A.carrier) :
    bcOne D'' A (A.setup.weight.Y x) = (A.bcNN hι).setup.weight.Y (bcOne D'' A x) :=
  (LinearMap.baseChange_tmul _ _ _).symm

theorem bcOne_proj (hι : ConjCompat D D'') (A : HCEObj ℓ E D) (n : ℤ) (x : A.carrier) :
    (A.bcNN hι).setup.weight.proj n (bcOne D'' A x) = bcOne D'' A (A.setup.weight.proj n x) :=
  WeightData.proj_baseChange_one_tmul (E'' := D''.carrier) A.setup.weight n x

set_option maxRecDepth 20000 in
/-- The limit of one run commutes with `1 ⊗ −`, on the whole module.
@census none (helper; WP-15) -/
theorem limPlus_bcNN (hι : ConjCompat D D'') (hℓ : 1 ≤ ℓ) (A : HCEObj ℓ E D)
    (CS : Gelfand.RationalStructure.StabInput A.setup) (CT : Gelfand.RationalStructure.StabInput (A.bcNN hι).setup)
    (CSmem : CS ∈ ({Gelfand.RationalStructure.inputPlus A.setup, Gelfand.RationalStructure.inputMinus A.setup, Gelfand.RationalStructure.inputStar A.setup hℓ} : Set _))
    (CTmem : CT ∈ ({Gelfand.RationalStructure.inputPlus (A.bcNN hι).setup, Gelfand.RationalStructure.inputMinus (A.bcNN hι).setup,
      Gelfand.RationalStructure.inputStar (A.bcNN hι).setup hℓ} : Set _))
    (hp : CT.idxPlus = CS.idxPlus) (hm : CT.idxMinus = CS.idxMinus)
    (hfp : ∀ v ∈ A.setup.weight.comp CS.idxPlus,
      bcOne D'' A (CS.phiPlus v) = CT.phiPlus (bcOne D'' A v))
    (hfm : ∀ v ∈ A.setup.weight.comp CS.idxMinus,
      bcOne D'' A (CS.phiMinus v) = CT.phiMinus (bcOne D'' A v)) (m : A.carrier) :
    bcOne D'' A (CS.limPlus m) = CT.limPlus (bcOne D'' A m) := by
  obtain ⟨hpS, hmS, nS, hnilS, hnS⟩ := Gelfand.RationalStructure.stab_prereq A.setup hℓ CS CSmem
  obtain ⟨hpT, hmT, nT, hnilT, hnT⟩ := Gelfand.RationalStructure.stab_prereq (A.bcNN hι).setup hℓ CT CTmem
  refine lim_natural_bc_all CS CT (bcOne D'' A) (fun x => ?_)
    (lim_natural_bc CS CT (bcOne D'' A) (bcOne_mem hι A) (bcOne_conj hι A) hp hm hfp hfm
      hpS hmS hnilS hnS hpT hmT hnilT hnT) m
  rw [hp]; exact bcOne_proj hι A _ x

set_option maxRecDepth 20000 in
/-- **`φ''^{(∞)}_v (1 ⊗ m) = 1 ⊗ φ^{(∞)}_v (m)`** at the three vertices: the unipotent
stabilization of the base change is the base change of the unipotent stabilization.
@census none (helper; WP-15; the canonicity step of T1 case (2)) -/
theorem limAt_bcNN (hι : ConjCompat D D'') (hℓ : 1 ≤ ℓ) (A : HCEObj ℓ E D) (v : Fin 3)
    (m : A.carrier) :
    Gelfand.RationalStructure.limAt hℓ (A.bcNN hι) v ((1 : D''.carrier) ⊗ₜ[D.carrier] m)
      = (1 : D''.carrier) ⊗ₜ[D.carrier] Gelfand.RationalStructure.limAt hℓ A v m := by
  have htM : ∀ x, bcOne D'' A (Split.tMinus A.setup.toQiSetup x)
      = Split.tMinus (A.bcNN hι).setup.toQiSetup (bcOne D'' A x) :=
    map_tMinus_bc (bcOne D'' A) (bcOne_H hι A) (bcOne_X hι A) (bcOne_Y hι A)
  have hxS : ∀ x, bcOne D'' A (Split.xStar A.setup.toQiSetup x)
      = Split.xStar (A.bcNN hι).setup.toQiSetup (bcOne D'' A x) :=
    map_xStar_bc (bcOne D'' A) (bcOne_X hι A)
  fin_cases v
  · exact (limPlus_bcNN hι hℓ A (Gelfand.RationalStructure.inputMinus A.setup) (Gelfand.RationalStructure.inputMinus (A.bcNN hι).setup) (Or.inr (Or.inl rfl))
      (Or.inr (Or.inl rfl)) rfl rfl (fun u _ => htM u) (fun _ _ => rfl) m).symm
  · exact (limPlus_bcNN hι hℓ A (Gelfand.RationalStructure.inputStar A.setup hℓ) (Gelfand.RationalStructure.inputStar (A.bcNN hι).setup hℓ) (Or.inr (Or.inr rfl))
      (Or.inr (Or.inr rfl)) rfl rfl (fun u _ => hxS u) (fun u _ => hxS u) m).symm
  · exact (limPlus_bcNN hι hℓ A (Gelfand.RationalStructure.inputPlus A.setup) (Gelfand.RationalStructure.inputPlus (A.bcNN hι).setup) (Or.inl rfl)
      (Or.inl rfl) rfl rfl (fun _ _ => rfl) (fun u _ => htM u) m).symm

end LimAt

end RationalQuivers.Gelfand.BaseChange
