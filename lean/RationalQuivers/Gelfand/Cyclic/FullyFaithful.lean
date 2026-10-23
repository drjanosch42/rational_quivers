import RationalQuivers.Gelfand.Cyclic.Rational

/-!
# the case `ℓ = 0`: full faithfulness (§5.3, Steps C-5a, C-6)

Engine `E9` over the `E`-form (`homQ`, with `c ∘ ψ ∘ c = ψ` by faithfulness, `map_conj_of_faithful`
(route fix F-B9, v2 T3-a1; the earlier chain computation `ExtDataC.map_conj_of` is kept off-path)); native `E_ECyc_faithful`, `E_Cyc_full`
(`c ∘ ψ ∘ c = ψ`, Galois descent of morphisms at the `EX-HC` boundary).

*Provenance.*  Relocated in stage T3 (WP-10) from `GF/Cyclic.lean (§CycFull, faithfulness)` (v1 `RationalQuivers.Gelfand.GF`, the
field-generic copy of S8) by `workflow/v2/stages/T3/VALIDATION/scripts/relocate.py`: declarations
moved from `GF.x` to `Gelfand.Cyclic.x` (renames recorded in the T3 `DECL-ALLOWLIST.tsv`), references
qualified; statements and proofs otherwise unchanged.  The engine is stated over the presentation
`RationalSetupOver`/`HCEObj` over a quadratic `D' : SqrtNegOneExt E`; `HC ℓ E D` reaches it through the
`R-V2-3` bridges (`RationalStructure/Bridge.lean`).  The carried docstrings keep v1's `ℚ` vocabulary:
read `ℚ` as `E`, `ℚ[√-1]` as `L_E`, `c`/`galConj` as `D'.conj`, `RQ-x.yy` as the v1 clause ids (the v2
rows are named where a declaration claims or cites one).

*(2026-10-21, O-V2-6 round 2.)*  Engines `E1` (`eq_of_eq_on_V3`) and `E4` (`exists_hom_of_edges`),
which the carried docstrings below place in S8's `Gelfand/Construction.lean`, are
`Split.eq_of_eq_on_V3` and `Split.exists_hom_of_edges` in `Gelfand/Split/Chains.lean` (stage T2).
v1's `Gelfand/Construction.lean` was deleted with the v1 Q-chain at WP-13 (`ae9eda9`).

@census none (module)
-/

namespace RationalQuivers.Gelfand.Cyclic

open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand

variable {E : Type} [Field E] [CharZero E] {Dq : SqrtNegOneExt E}
open scoped TensorProduct Classical

variable {Mi : Type} [AddCommGroup Mi] [Module Dq.carrier Mi]

section Functor

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)

/-! ### Engine `E9` — the `ℓ = 0` extension engine

`E4` (`Gelfand/Construction.lean`) extends a compatible **triple** of component maps to a morphism
of `HC_λ(𝔤,K)_{ℚ[√-1]}`, and it carries `1 ≤ ℓ`: its five-way case split degenerates at `ℓ = 0`,
where `map_X_comp`'s third disjunct `n = -(ℓ+1)` and its fifth `n = ℓ - 1` are the *same* index
`n = -1` and the fifth branch opens with the false hypothesis `0 ≤ -1`
(`stages/S8/DESIGN-NOTES.md` §20.5(1)).  Ruling **`R-S8-35`** directs a fresh `ℓ = 0` engine rather
than a restructuring of `E4`, on which `RQ-5.05`'s already-proved `E_Q_full` depends.

At `ℓ = 0` there are only **two** chains and **one** `X`-wall.  Since `λ = ℓ² = 0` the Casimir `C`
is nilpotent, so `4YX = C − (n+1)²·𝟏` is a unit on `M_n` for every `n ≠ -1` and `X : M_n → M_{n+2}`
is an isomorphism there; the chains are `M_1 → M_3 → ⋯` upwards and `M_{-1} → M_{-3} → ⋯`
downwards, joined at the wall `X : M_{-1} → M_1`.  The single `Y`-wall is `Y : M_1 → M_{-1}`.  The
two walls are exactly the two edges `a`, `b` of the cyclic quiver, which is why the engine's input
is a `RepNilCycQ`-morphism verbatim.  Everything below reuses `E4`'s chain machinery (`chainX`,
`ofComponents`, `eq_of_comp`) unchanged; only the region split is new. -/


/-! ### `RQ-5.07`, fullness — engine `E9` applied to the two edges of the cyclic quiver

The `conj`-compatibility half of fullness, which for `1 ≤ ℓ` needs the whole of engine `E5` (the
two `ℚ`-forms of `Hom`, `DESIGN-NOTES` §16.3), is **free at `ℓ = 0`**: `u.hom.rational` at
`σ = Dq.conj` says `ψ` commutes with `φ_{v,c}`, and `φ_{v,c} = c` there (`phiCyc_eq_conj`), so it
says `ψ` commutes with `c` on the nose.  `E5`'s circularity was that `φ_{v,c} = c ∘ φ^{(∞)}_v` is
not `c`; at `ℓ = 0` there is no stabilization (`φ^{(∞)}_v` is the identity by definition since the
v2 amendment T3-a1, route fix F-B11) and the difference is not there.  The extension commutes with
`c` by the tex's argument, faithfulness of `𝔼_{L_E}` applied to `c ∘ ψ ∘ c` (`map_conj_of_faithful`,
route fix F-B9). -/

section CycFull

/-- `c ∘ Y^k = X^k ∘ c`, the mirror of `conj_pow_X`.  @census none (helper) -/
theorem conj_pow_Y {ℓ : ℕ} {Mq : Type} [AddCommGroup Mq] [Module E Mq]
    (S : RationalSetupOver ℓ E Dq Mq Mi) (k : ℕ) (v : Mi) :
    S.conj ((S.weight.Y ^ k) v) = (S.weight.X ^ k) (S.conj v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, S.conj_Y']


/-- The extension commutes with every power of `Y`.  @census none (helper) -/
theorem _root_.RationalQuivers.Gelfand.Split.ExtDataC.map_pow_Y_eq {A B : Split.HCFObj Dq.carrier 0} (d : Split.ExtDataC A B) (k : ℕ) (v : A.carrier) :
    d.map ((A.weight.Y ^ k) v) = (B.weight.Y ^ k) (d.map v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, d.map_Y, ih]

/-- **The `ℓ = 0` extension commutes with `c`**, given the compatibility on `M_1` alone.  The `+`
chain is `X^k`-generated and `c ∘ X^k = Y^k ∘ c`; the `−` chain then follows because `c` is an
involution exchanging the two chains, and the even components are `⊥` by the central character.
@census none (helper) -/
theorem _root_.RationalQuivers.Gelfand.Split.ExtDataC.map_conj_of {A B : HCEObj 0 E Dq} (d : Split.ExtDataC A.toF B.toF)
    (hconj : ∀ m : A.carrier, m ∈ A.setup.weight.comp 1 →
      d.map (A.setup.conj m) = B.setup.conj (d.map m))
    (v : A.carrier) : d.map (A.setup.conj v) = B.setup.conj (d.map v) := by
  have pos : ∀ (n : ℤ), (1 : ℤ) ≤ n → ∀ m : A.carrier, m ∈ A.setup.weight.comp n →
      d.map (A.setup.conj m) = B.setup.conj (d.map m) := by
    intro n hn m hm
    by_cases hp : (n + 1) % 2 = 0
    · set k : ℕ := ((n - 1) / 2).toNat with hkdef
      have hnk : n = 1 + 2 * (k : ℤ) := by omega
      obtain ⟨u, hu, hmu⟩ := Split.chainX_surjective A.toF 1 k (Split.hjUpC k) k le_rfl (hnk ▸ hm)
      rw [← hmu, Gelfand.RationalStructure.conj_pow_X A.setup k u, d.map_pow_Y_eq k, hconj u hu, d.map_pow_X_eq k u,
        Gelfand.RationalStructure.conj_pow_X B.setup k (d.map u)]
    · have hbot : A.setup.weight.comp n = ⊥ := A.centralCharacter n (by omega)
      rw [hbot, Submodule.mem_bot] at hm
      rw [hm]
      simp only [map_zero]
  have key : ∀ (n : ℤ) (m : A.carrier), m ∈ A.setup.weight.comp n →
      d.map (A.setup.conj m) = B.setup.conj (d.map m) := by
    intro n m hm
    rcases (show (1 : ℤ) ≤ n ∨ (1 : ℤ) ≤ -n ∨ n = 0 by omega) with h | h | h
    · exact pos n h m hm
    · have hcm : A.setup.conj m ∈ A.setup.weight.comp (-n) := A.setup.conj_comp n m hm
      have h1 := pos (-n) h (A.setup.conj m) hcm
      rw [A.setup.conj_involutive m] at h1
      have h2 := congrArg B.setup.conj h1
      rw [B.setup.conj_involutive (d.map (A.setup.conj m))] at h2
      exact h2.symm
    · subst h
      have hbot : A.setup.weight.comp 0 = ⊥ := A.centralCharacter 0 (by decide)
      rw [hbot, Submodule.mem_bot] at hm
      rw [hm]
      simp only [map_zero]
  obtain ⟨s, -, hsum⟩ := A.setup.weight.exists_sum_proj v
  have e1 : A.setup.conj v = ∑ n ∈ s, A.setup.conj (A.setup.weight.proj n v) := by
    conv_lhs => rw [← hsum]
    exact map_sum _ _ _
  have e2 : d.map v = ∑ n ∈ s, d.map (A.setup.weight.proj n v) := by
    conv_lhs => rw [← hsum]
    exact map_sum _ _ _
  rw [e1, e2, map_sum, map_sum]
  exact Finset.sum_congr rfl fun n _ => key n _ (A.setup.weight.proj_mem n v)

/-- **`c ∘ ψ ∘ c = ψ` by faithfulness** (Step C-6, the tex's route): the same statement as
`Split.ExtDataC.map_conj_of`, proved as in the proof of `thm:cyclicEEequivalence` — "since `c`
intertwines `X` with `Y` and maps `M_n` to `M_{-n}`, also `c∘ψ∘c` is a morphism of `(𝔤,K)`-modules
(`Equivalence.isHCMap_conjHom`), and its restrictions to `A_{∓1}` are `c∘ψ_±∘c = ψ_∓`.  By
faithfulness of `𝔼_{L_E}` (`Split.E_CycSplit_faithful`), `c∘ψ∘c = ψ`."

v2 R-PROC-4 amendment T3-a1, route fix **F-B9** (C-6; WP-16 triage verdict FIX-LEAN): new helper,
wired into `ExtDataC.homQ` and `E_Cyc_full` in place of the chain computation `map_conj_of` (kept,
off-path).  @census none (helper; Step C-6)
@clauses   RQ2-5.13-S-C6 -/
theorem map_conj_of_faithful {A B : HCEObj 0 E Dq} (d : Split.ExtDataC A.toF B.toF)
    (hconj : ∀ m : A.carrier, m ∈ A.setup.weight.comp 1 →
      d.map (A.setup.conj m) = B.setup.conj (d.map m))
    (v : A.carrier) : d.map (A.setup.conj v) = B.setup.conj (d.map v) := by
  -- `ψ` is a morphism of `(𝔤,K)`-modules over `L_E`, and so is `c ∘ ψ ∘ c`
  have hu : Equivalence.IsHCMap (A := A) (B := B) d.map := ⟨d.map_H, d.map_X, d.map_Y, d.map_mem⟩
  have hT : Equivalence.IsHCMap (Equivalence.conjHom d.map) := Equivalence.isHCMap_conjHom hu
  -- their restrictions to `A_{∓1}` agree: `c ∘ ψ_± ∘ c = ψ_∓`
  have hres : ∀ (w : Fin 2) (m : A.carrier), m ∈ A.setup.weight.comp (cycIdx w) →
      Equivalence.conjHom d.map m = d.map m := by
    intro w m hm
    fin_cases w
    · have hcm : A.setup.conj m ∈ A.setup.weight.comp 1 := by
        have h := A.setup.conj_comp _ m hm
        simpa [cycIdx] using h
      have h := hconj (A.setup.conj m) hcm
      rw [A.setup.conj_involutive m] at h
      rw [Equivalence.conjHom_apply, h]
    · have hm1 : m ∈ A.setup.weight.comp 1 := by simpa [cycIdx] using hm
      rw [Equivalence.conjHom_apply, hconj m hm1, B.setup.conj_involutive]
  -- by faithfulness of `𝔼_{L_E}`, `c ∘ ψ ∘ c = ψ`
  have hE : (Split.E_CycSplitFunctor (F := Dq.carrier)).map (Equivalence.hcHom hT)
      = (Split.E_CycSplitFunctor (F := Dq.carrier)).map (Equivalence.hcHom hu) := by
    apply ObjectProperty.hom_ext
    refine RationalQuiver.Rep.Hom.ext (funext fun w => LinearMap.ext fun m => Subtype.ext ?_)
    exact hres w m.1 m.2
  have heq := congrArg Split.HCFHom.toLinearMap
    ((Split.E_CycSplit_faithful (F := Dq.carrier)).map_injective hE)
  have h := LinearMap.congr_fun heq (A.setup.conj v)
  change B.setup.conj (d.map (A.setup.conj (A.setup.conj v))) = d.map (A.setup.conj v) at h
  rw [A.setup.conj_involutive v] at h
  exact h.symm

/-- **Engine `E9` over `ℚ`**: the extension of a compatible pair that also commutes with `c` is a
morphism of `HC_0(𝔤,K)_ℚ`.  @census none (helper) -/
noncomputable def _root_.RationalQuivers.Gelfand.Split.ExtDataC.homQ {A B : HCEObj 0 E Dq} (d : Split.ExtDataC A.toF B.toF)
    (hconj : ∀ m : A.carrier, m ∈ A.setup.weight.comp 1 →
      d.map (A.setup.conj m) = B.setup.conj (d.map m)) : A ⟶ B where
  toLinearMap := d.map
  map_H := d.map_H
  map_X := d.map_X
  map_Y := d.map_Y
  map_comp := d.map_mem
  map_conj := map_conj_of_faithful d hconj


/-- Reading a component of a morphism of `𝔼_ℚ`-representations at a vertex named in two
definitionally different ways.  @census none (helper) -/
theorem psi_val_congr {A B : HCEObj 0 E Dq} {hA : ObjSpecC hcard A} {hB : ObjSpecC hcard B}
    (w : RationalQuiver.Rep.Hom (E_Cyc_rep hcard A hA) (E_Cyc_rep hcard B hB))
    {i j : Fin 2} (hij : i = j) (y : V2 A i) (y' : V2 A j)
    (hy : (y : A.carrier) = (y' : A.carrier)) :
    Subtype.val (w.ψ i y) = Subtype.val (w.ψ j y') := by
  subst hij
  exact congrArg (fun t : V2 A i => Subtype.val (w.ψ i t)) (Subtype.ext hy)

/-- `c` sends the `+` vertex of the cyclic quiver to the `−` vertex.  @census none (helper) -/
theorem galConj_smul_one : Dq.conj • vtxC hcard 1 = vtxC hcard 0 := by
  rw [cyclicQ_smul_vertex hcard 1]; rfl

/-- **The `conj`-compatibility of a morphism of `𝔼_ℚ`-representations at `ℓ = 0`**: the `rational`
field at `σ = Dq.conj`, read on values.  At `ℓ = 0` the semi-linear structure map `φ_{v,c}` **is**
`c` (`phiCyc_eq_conj`), so `ψ` commutes with `c` with no `ℚ`-form-of-`Hom` argument.
@census none (helper) -/
theorem cyc_psi_conjS {A B : HCEObj 0 E Dq} (hA : ObjSpecC hcard A) (hB : ObjSpecC hcard B)
    (w : RationalQuiver.Rep.Hom (E_Cyc_rep hcard A hA) (E_Cyc_rep hcard B hB))
    (m : A.carrier) (hm : m ∈ A.setup.weight.comp (cycIdx 1))
    (hcm : A.setup.conj m ∈ A.setup.weight.comp (cycIdx 0)) :
    Subtype.val (w.ψ (vtxC hcard 0) (⟨A.setup.conj m, hcm⟩ : V2 A 0))
      = B.setup.conj (Subtype.val (w.ψ (vtxC hcard 1) (⟨m, hm⟩ : V2 A 1))) := by
  have hr := w.rational Dq.conj (vtxC hcard 1) (⟨m, hm⟩ : V2 A 1)
  have hR : Subtype.val ((E_Cyc_rep hcard B hB).φ Dq.conj (vtxC hcard 1)
        (w.ψ (vtxC hcard 1) (⟨m, hm⟩ : V2 A 1)))
      = B.setup.conj (Subtype.val (w.ψ (vtxC hcard 1) (⟨m, hm⟩ : V2 A 1))) := by
    show galActC B Dq.conj 1 _ = _
    rw [galActC_of_ne B Gelfand.RationalStructure.galConj_ne_one]
    exact phiCyc_eq_conj B 1 _ (Subtype.property (w.ψ (vtxC hcard 1) (⟨m, hm⟩ : V2 A 1)))
  have hL : Subtype.val (w.ψ (Dq.conj • vtxC hcard 1)
        ((E_Cyc_rep hcard A hA).φ Dq.conj (vtxC hcard 1) (⟨m, hm⟩ : V2 A 1)))
      = Subtype.val (w.ψ (vtxC hcard 0) (⟨A.setup.conj m, hcm⟩ : V2 A 0)) := by
    refine psi_val_congr hcard w (galConj_smul_one hcard) _ _ ?_
    show galActC A Dq.conj 1 m = A.setup.conj m
    rw [galActC_of_ne A Gelfand.RationalStructure.galConj_ne_one]
    exact phiCyc_eq_conj A 1 m hm
  rw [← hL, ← hR, hr]

/-- Engine `E9`'s datum, read off a morphism of the cyclic quiver's representations: the two
component maps and the two edge equations, verbatim.  @census none (helper) -/
noncomputable def cycExtData {A B : HCEObj 0 E Dq} (hA : ObjSpecC hcard A) (hB : ObjSpecC hcard B)
    (w : RationalQuiver.Rep.Hom (E_Cyc_rep hcard A hA) (E_Cyc_rep hcard B hB)) :
    Split.ExtDataC A.toF B.toF where
  ψp := w.ψ (vtxC hcard 1)
  ψm := w.ψ (vtxC hcard 0)
  edgeX := fun m hm _ => congrArg Subtype.val (w.edge (edgeC hcard 0) ⟨m, hm⟩)
  edgeY := fun m hm _ => congrArg Subtype.val (w.edge (edgeC hcard 1) ⟨m, hm⟩)

/-- Engine `E9`'s extension of `cycExtData` restricts to the given morphism on both vertex
components.  @census none (helper) -/
theorem cycExtData_val {A B : HCEObj 0 E Dq} (hA : ObjSpecC hcard A) (hB : ObjSpecC hcard B)
    (w : RationalQuiver.Rep.Hom (E_Cyc_rep hcard A hA) (E_Cyc_rep hcard B hB))
    (v : Fin 2) (x : V2 A v) :
    (cycExtData hcard hA hB w).map ((x : A.carrier)) = Subtype.val (w.ψ v x) := by
  fin_cases v
  · exact (cycExtData hcard hA hB w).map_at_minus _ x.2
  · exact (cycExtData hcard hA hB w).map_at_plus _ x.2

/-- **`RQ-5.07`, fullness of `𝔼_ℚ` at `ℓ = 0`** — engine `E9`.  A morphism of the cyclic quiver's
rational representations is a pair of maps on `M_{-1}`, `M_1` commuting with `X`, `Y` and `c`, and
engine `E9` extends it along the two `X`-chains to a morphism of `HC_0(𝔤,K)_ℚ` whose image under
`𝔼_ℚ` is the given morphism on the nose.
@census none (helper; engine `E9`, ruling `R-S8-35`) -/
theorem E_Cyc_fullS (h : E_CycSpec hcard) : (E_CycFunctor hcard h).Full := by
  constructor
  intro A B u
  refine ⟨Split.ExtDataC.homQ (cycExtData hcard (h.1 A) (h.1 B) u.hom) (fun m hm => ?_), ?_⟩
  · have hcm : A.setup.conj m ∈ A.setup.weight.comp (-1) := A.setup.conj_comp 1 m hm
    rw [(cycExtData hcard (h.1 A) (h.1 B) u.hom).map_at_minus _ hcm,
      (cycExtData hcard (h.1 A) (h.1 B) u.hom).map_at_plus m hm]
    exact cyc_psi_conjS hcard (h.1 A) (h.1 B) u.hom m hm hcm
  · apply ObjectProperty.hom_ext
    refine RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun m => Subtype.ext ?_)
    exact cycExtData_val hcard (h.1 A) (h.1 B) u.hom v m

end CycFull

end Functor

section Functor

variable (hcard : Nat.card (Dq.carrier ≃ₐ[E] Dq.carrier) = 2)

/-! ### `RQ-5.07` — faithfulness, and the residue

`E1` (`eq_of_eq_on_V3`, `Gelfand/Construction.lean`) is stated for every `ℓ`, and **at `ℓ = 0` the
three indices `vtxIdx 0` names are `M_{-1}`, `M_{1}`, `M_{1}`** — exactly the two vertex spaces of
the cyclic quiver, each `cycIdx`-index appearing among them.  So `E1` gives the faithfulness of
`E_CycFunctor` with no `ℓ = 0` engine of its own (`star_case_obsolete`, read on morphisms).  What
`RQ-5.07` still needs is `E_CycSpec` itself, fullness (an `ℓ = 0` extension engine — `E4`'s
`exists_hom_of_edges` takes `1 ≤ ℓ` and cannot be used) and essential surjectivity;
`cyclic_E_Q_equivalence_of` isolates exactly those three.
`stages/S8/DESIGN-NOTES.md` §18.4. -/

/-- A morphism of `HC_0(𝔤,K)_ℚ` is determined by its restrictions to `M_{-1}` and `M_1` — `E1` at
`ℓ = 0`.  @census none (helper) -/
theorem cyc_eq_of_eq_on_V2 {A B : HCEObj 0 E Dq} (f g : A ⟶ B)
    (h : ∀ (v : Fin 2) (m : A.carrier), m ∈ A.setup.weight.comp (cycIdx v) →
      f.toLinearMap m = g.toLinearMap m) : f = g := by
  refine HCEHom.hom_ext (congrArg Split.HCFHom.toLinearMap
    (Split.eq_of_eq_on_V3 (A := A.toF) (B := B.toF) ((GF.baseChangeE 0 E Dq).map f) ((GF.baseChangeE 0 E Dq).map g)
      (fun v m hm => ?_)))
  fin_cases v
  · exact h 0 m hm
  · exact h 1 m hm
  · exact h 1 m hm

/-- **`RQ-5.07`, faithfulness of `𝔼_ℚ` at `ℓ = 0`.**  @census none (helper) -/
theorem E_Cyc_faithful (h : E_CycSpec hcard) : (E_CycFunctor hcard h).Faithful := by
  constructor
  intro A B f g hfg
  refine cyc_eq_of_eq_on_V2 f g (fun v m hm => ?_)
  have h1 : (E_Cyc_hom hcard (h.1 A) (h.1 B) f (h.2 _ _ f)).ψ
      = (E_Cyc_hom hcard (h.1 A) (h.1 B) g (h.2 _ _ g)).ψ :=
    congrArg (fun (u : (E_CycFunctor hcard h).obj A ⟶ (E_CycFunctor hcard h).obj B) => u.hom.ψ) hfg
  exact congrArg (fun (T : V2 A v →ₗ[Dq.carrier] V2 B v) => ((T ⟨m, hm⟩ : V2 B v) : B.carrier))
    (congrFun h1 v)


end Functor


/-! ## The native `𝔼_E` on `HC ℓ E D` (stage T3) -/

section NativeHC

set_option linter.unusedSectionVars false

variable {D : ImagUnit E}


theorem E_ECyc_faithful : (E_ECyc (D := D)).Faithful := by
  constructor
  intro A B f g hfg
  have h1 : (E_Cyc_homZ f).ψ = (E_Cyc_homZ g).ψ :=
    congrArg (fun (u : E_ECyc.obj A ⟶ E_ECyc.obj B) => u.hom.ψ) hfg
  have h2 : Split.E_CycSplitFunctor.map (HC.Hom.toF f) = Split.E_CycSplitFunctor.map (HC.Hom.toF g) := by
    apply ObjectProperty.hom_ext
    exact RationalQuiver.Rep.Hom.ext h1
  exact HC.Hom.ext' (congrArg Split.HCFHom.toLinearMap
    ((Split.E_CycSplit_faithful (F := D.L)).map_injective h2))

theorem psiZ_congr {A B : HC 0 E D} (w : RationalQuiver.Rep.Hom (E_Cyc_repZ A) (E_Cyc_repZ B))
    {i j : (RationalQuiver.cyclicOfSign E D.L D.chiHom).V} (hij : i = j) (y : V2Z A i)
    (y' : V2Z A j) (hy : (y : A.carrier) = (y' : A.carrier)) :
    Subtype.val (w.ψ i y) = Subtype.val (w.ψ j y') := by
  subst hij
  exact congrArg (fun t : V2Z A i => Subtype.val (w.ψ i t)) (Subtype.ext hy)

/-- **Step C-6**, the `c`-compatibility of a morphism of `𝔼_E`-representations at `ℓ = 0`: the
`rational` field at `σ = c`, read on values — `ψ_{−}(c m) = c ψ_{+}(m)` on `M_1`, since `φ_{•,c} = c`.
@census none (helper; Step C-6) -/
theorem cyc_psi_conj {A B : HC 0 E D} (u : E_ECyc.obj A ⟶ E_ECyc.obj B)
    {σ : D.L ≃ₐ[E] D.L} (hσ : D.chi σ = -1) (m : A.carrier) (hm : m ∈ A.weight.comp (cycIdx 1))
    (hcm : A.galAct σ m ∈ A.weight.comp (cycIdx 0)) :
    Subtype.val (u.hom.ψ (vtxZ D 0) ⟨A.galAct σ m, hcm⟩)
      = B.galAct σ (Subtype.val (u.hom.ψ (vtxZ D 1) ⟨m, hm⟩)) := by
  have hr := congrArg Subtype.val (u.hom.rational σ (vtxZ D 1) ⟨m, hm⟩)
  have hv : σ • vtxZ D 1 = vtxZ D 0 := by
    rw [vtxZ_smul]; unfold galVtxZ; rw [if_neg (by rw [hσ]; decide)]; rfl
  refine Eq.trans ?_ hr
  exact psiZ_congr u.hom hv.symm _ _ rfl

/-- **Step C-6**, Galois descent of morphisms: engine `E9`'s extension `d.map` of a compatible pair,
when it commutes with every `σ ∈ G_E`, is a morphism of `HC_0(𝔤,K)_E`.  @census none (helper; Step C-6) -/
noncomputable def homQ {A B : HC 0 E D} (d : Split.ExtDataC A.toF B.toF)
    (hgal : ∀ σ m, d.map (A.galAct σ m) = B.galAct σ (d.map m)) : A ⟶ B :=
  ⟨d.map, d.map_H, d.map_X, d.map_Y, d.map_mem, hgal⟩

/-- **Fullness, `ℓ = 0`** (Steps C-5a, C-6): engine `E9` extends a morphism of the cyclic quiver's
representations along the `X`-chains (`eq:Xbijectivecyclic`); `c ∘ ψ ∘ c = ψ` (`cyc_psi_conj`,
`map_conj_of_faithful`, by faithfulness of `𝔼_{L_E}`; route fix F-B9, T3-a1), so the extension
descends (`homQ`).  @census none (helper) -/
theorem E_Cyc_full : (E_ECyc (D := D)).Full := by
  constructor
  intro A B u
  let d : Split.ExtDataC A.toF B.toF :=
    { ψp := u.hom.ψ (vtxZ D 1)
      ψm := u.hom.ψ (vtxZ D 0)
      edgeX := fun m hm _ => congrArg Subtype.val (u.hom.edge (edgeZ D 0) ⟨m, hm⟩)
      edgeY := fun m hm _ => congrArg Subtype.val (u.hom.edge (edgeZ D 1) ⟨m, hm⟩) }
  have hval : ∀ (v : Fin 2) (x : V2Z A v), d.map (x : A.carrier) = Subtype.val (u.hom.ψ v x) := by
    intro v x
    fin_cases v
    · exact d.map_at_minus _ x.2
    · exact d.map_at_plus _ x.2
  have hgal : ∀ σ m, d.map (A.galAct σ m) = B.galAct σ (d.map m) := by
    intro σ m
    rcases D.chi_cases σ with hσ | hσ
    · rw [HC.galAct_of_chi_one _ hσ, HC.galAct_of_chi_one _ hσ]
    set hc : ∃ σ : D.L ≃ₐ[E] D.L, D.chi σ = -1 := ⟨σ, hσ⟩
    have key := map_conj_of_faithful (A := A.toHCEObj hc) (B := B.toHCEObj hc) d
      (fun m hm => by
        show d.map (A.galAct _ m) = B.galAct _ (d.map m)
        have hcm : A.galAct (D.sqrtExt hc).conj m ∈ A.weight.comp (-1) :=
          (A.compat_neg (D.chi_sqrtExt_conj hc)).1 1 m hm
        rw [d.map_at_minus _ hcm, d.map_at_plus m hm]
        exact cyc_psi_conj u (D.chi_sqrtExt_conj hc) m hm hcm) m
    rw [← A.setup_conj hc hσ, ← B.setup_conj hc hσ]
    exact key
  refine ⟨homQ d hgal, ?_⟩
  apply ObjectProperty.hom_ext
  refine RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun m => Subtype.ext ?_)
  exact hval v m


end NativeHC

end RationalQuivers.Gelfand.Cyclic
