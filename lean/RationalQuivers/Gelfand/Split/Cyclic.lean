module

public import RationalQuivers.Gelfand.Split.Chains

@[expose] public section

/-!
# The case `ℓ = 0` over a field containing `√-1` (tex §5.3, "The case `ℓ = 0`"; Steps C-1, C-3, C-5a…c)

For `ℓ = 0` the even weight spaces vanish and the vertex `⋆` is obsolete: `𝔼_F(M) =
(M_{−1}, M_1; X, Y)`, a representation of the cyclic quiver (Step C-1).  `eq:4XYcyclic`,
`eq:Xbijectivecyclic` (Step C-3); the equivalence over `F` (the paragraph "The equivalence over
`ℚ[√-1]`" of the proof of `thm:cyclicEEequivalence`): faithful and full along
`X : M_n → M_{n+2}` (Step C-5a), and essentially surjective by the explicit carrier `M_n = V(+)`
(`n ≥ 1` odd), `V(−)` (`n ≤ −1` odd), `0` (even), with `X = 1` up the `+` chain, `Y = 1` down the `−`
chain, `Y = ¼(4n_+ − (n−1)²)` (`n ≥ 3`), `X = ¼(4n_− − (n+1)²)` (`n ≤ −3`), `X|_{M_{−1}} = φ_a`,
`Y|_{M_1} = φ_b` — no square roots (Step C-5b) — and `𝔼(M) = V` on the nose, i.e. through the
canonical embeddings of the components with no scalar (Step C-5c, BLUEPRINT OQ-8).

## One `ℓ = 0` carrier (BLUEPRINT OQ-7, author-approved 2026-10-16)
The carrier `cz*` here is `c`-free and is the only `ℓ = 0` essential-surjectivity carrier: the
non-split `ℓ = 0` proof (v1 `GF/Cyclic.lean`, engine `E10`, relocated in T3) reads it and adds only
the `c`-clauses (Step C-7), as `GF.EssSurjData` extends `SplitEssSurjData` at `ℓ ≥ 1`.

## Provenance (v2 WP-9, stage T2; relocation)
v1's `Gelfand/GeneralField/CyclicCore.lean` (engine `E9`) and `Gelfand/GeneralField/CycSplit.lean`,
moved to the namespace `RationalQuivers.Gelfand.Split`.  Docstrings carry their v1 wording: read
`ℚ[√-1]` as `F`.

*(2026-10-21, O-V2-6 round 2.)*  Some v1 names in this module are no longer in the tree:
* `GF.EssSurjData` was relocated at WP-10 (`542ebf7`) as `Gelfand.EssSurj.EssSurjData`
  (`Gelfand/EssSurj/Construction.lean`), which still extends `SplitEssSurjData`.
* `E4` of v1's `Gelfand/Construction.lean` is `Split.exists_hom_of_edges` in
  `Gelfand/Split/Chains.lean`.  The v1 file and `spNatHom` were deleted with the v1 Q-chain at WP-13
  (`ae9eda9`).
* `E_E_equivalence_cyclic`, which cited `E_E_cyclic_split_equivalence` below, was deleted at WP-13
  (`44df340`).  On the v2 line `thm:cyclicEEequivalence` (`RQ2-5.13`) is claimed by
  `Gelfand.gelfand_equivalence_zero` (`Gelfand/Main.lean`).
-/

namespace RationalQuivers.Gelfand.Split


open RationalQuivers.HC RationalQuivers.Unipotent CategoryTheory
open RationalQuivers.Gelfand
open scoped TensorProduct Classical

variable {F : Type} [Field F] [CharZero F]

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

section E9

variable {A B : HCFObj F 0}

/-- The `+` chain's index hypothesis at `ℓ = 0`: every interior index is positive, hence non-zero.
@census none (helper) -/
theorem hjUpC (K : ℕ) : ∀ i : ℕ, i < K →
    ((((1 : ℤ) + 2 * (i : ℤ) + 1 : ℤ) : F)) ^ 2 ≠ (((0 : ℕ) : F)) ^ 2 :=
  fun i _ => sq_ne_sq_of (ℓ := 0) _ (sq_ne_sq_gt (ℓ := 0) _ (by omega))

/-- The `−` chain's index hypothesis at `ℓ = 0`: every interior index is negative.
@census none (helper) -/
theorem hjDownC (n : ℤ) (K : ℕ) (h : n + 2 * (K : ℤ) = -1) : ∀ i : ℕ, i < K →
    (((n + 2 * (i : ℤ) + 1 : ℤ) : F)) ^ 2 ≠ (((0 : ℕ) : F)) ^ 2 :=
  fun i hi => sq_ne_sq_of (ℓ := 0) _ (sq_ne_sq_lt (ℓ := 0) _ (by omega))

/-- The `+` region's component map at `ℓ = 0`: `X^k ∘ ψ₊ ∘ (X^k)^{-1}` on `M_{1 + 2k}`.
@census none (helper) -/
noncomputable def gUpC (ψp : A.weight.comp 1 →ₗ[F] B.weight.comp 1)
    (k : ℕ) (n : ℤ) (hn : n = 1 + 2 * (k : ℤ)) :
    A.weight.comp n →ₗ[F] B.weight.comp n :=
  (LinearEquiv.ofEq _ _ (congrArg B.weight.comp hn.symm)).toLinearMap ∘ₗ
    (chainX B 1 k (hjUpC k) k le_rfl).toLinearMap ∘ₗ ψp ∘ₗ
      (chainX A 1 k (hjUpC k) k le_rfl).symm.toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ (congrArg A.weight.comp hn)).toLinearMap

/-- `gUpC` reads off a chain preimage.  @census none (helper) -/
theorem gUpC_val (ψp : A.weight.comp 1 →ₗ[F] B.weight.comp 1)
    (k : ℕ) (n : ℤ) (hn : n = 1 + 2 * (k : ℤ))
    (u : A.weight.comp 1) {m : A.carrier} (hm : m ∈ A.weight.comp n)
    (hmu : (A.weight.X ^ k) (u : A.carrier) = m) :
    ((gUpC ψp k n hn ⟨m, hm⟩ : B.weight.comp n) : B.carrier)
      = (B.weight.X ^ k) ((ψp u : B.weight.comp 1) : B.carrier) := by
  have hu : chainX A 1 k (hjUpC k) k le_rfl u
      = (LinearEquiv.ofEq _ _ (congrArg A.weight.comp hn)) ⟨m, hm⟩ :=
    Subtype.ext (by rw [chainX_val, hmu]; rfl)
  show Subtype.val ((LinearEquiv.ofEq (B.weight.comp (1 + 2 * (k : ℤ)))
      (B.weight.comp n) (congrArg B.weight.comp hn.symm))
      (chainX B 1 k (hjUpC k) k le_rfl
        (ψp ((chainX A 1 k (hjUpC k) k le_rfl).symm
          ((LinearEquiv.ofEq (A.weight.comp n) (A.weight.comp (1 + 2 * (k : ℤ)))
            (congrArg A.weight.comp hn)) ⟨m, hm⟩))))) = _
  rw [← hu, LinearEquiv.symm_apply_apply]
  show ((chainX B 1 k (hjUpC k) k le_rfl (ψp u) :
    B.weight.comp (1 + 2 * (k : ℤ))) : B.carrier) = _
  rw [chainX_val]

/-- The `−` region's component map at `ℓ = 0`: the `X^k`-preimage of `ψ₋` on `M_{-1-2k}`.
@census none (helper) -/
noncomputable def gDownC (ψm : A.weight.comp (-1) →ₗ[F] B.weight.comp (-1))
    (k : ℕ) (n : ℤ) (hn : n + 2 * (k : ℤ) = -1) :
    A.weight.comp n →ₗ[F] B.weight.comp n :=
  (chainX B n k (hjDownC n k hn) k le_rfl).symm.toLinearMap ∘ₗ
      (LinearEquiv.ofEq _ _ (congrArg B.weight.comp hn.symm)).toLinearMap ∘ₗ ψm ∘ₗ
      (LinearEquiv.ofEq _ _ (congrArg A.weight.comp hn)).toLinearMap ∘ₗ
      (chainX A n k (hjDownC n k hn) k le_rfl).toLinearMap

/-- `gDownC` is characterised by `X^k ∘ gDownC = ψ₋ ∘ X^k`.  @census none (helper) -/
theorem gDownC_val (ψm : A.weight.comp (-1) →ₗ[F] B.weight.comp (-1))
    (k : ℕ) (n : ℤ) (hn : n + 2 * (k : ℤ) = -1)
    {m : A.carrier} (hm : m ∈ A.weight.comp n)
    (hXm : (A.weight.X ^ k) m ∈ A.weight.comp (-1)) :
    (B.weight.X ^ k) ((gDownC ψm k n hn ⟨m, hm⟩ : B.weight.comp n) : B.carrier)
      = ((ψm ⟨(A.weight.X ^ k) m, hXm⟩ : B.weight.comp (-1)) : B.carrier) := by
  have hA : (LinearEquiv.ofEq _ _ (congrArg A.weight.comp hn))
      (chainX A n k (hjDownC n k hn) k le_rfl ⟨m, hm⟩)
      = ⟨(A.weight.X ^ k) m, hXm⟩ := by
    refine Subtype.ext ?_
    show ((chainX A n k (hjDownC n k hn) k le_rfl ⟨m, hm⟩ :
      A.weight.comp (n + 2 * (k : ℤ))) : A.carrier) = (A.weight.X ^ k) m
    rw [chainX_val]
  show (B.weight.X ^ k) (Subtype.val
      ((chainX B n k (hjDownC n k hn) k le_rfl).symm
        ((LinearEquiv.ofEq (B.weight.comp (-1)) (B.weight.comp (n + 2 * (k : ℤ)))
              (congrArg B.weight.comp hn.symm))
          (ψm ((LinearEquiv.ofEq (A.weight.comp (n + 2 * (k : ℤ)))
                (A.weight.comp (-1)) (congrArg A.weight.comp hn))
            (chainX A n k (hjDownC n k hn) k le_rfl ⟨m, hm⟩)))))) = _
  rw [hA, ← chainX_val B n k (hjDownC n k hn) k le_rfl, LinearEquiv.apply_symm_apply]
  rfl

/-- The component map of the `ℓ = 0` extension, by region: `+` for `n ≥ 1`, `−` for `n ≤ -1`, and
`0` off the central character's parity class (where the component is `⊥`).  There is no third
region: at `ℓ = 0` the two walls are adjacent.  @census none (helper) -/
noncomputable def gcompC (ψp : A.weight.comp 1 →ₗ[F] B.weight.comp 1)
    (ψm : A.weight.comp (-1) →ₗ[F] B.weight.comp (-1)) (n : ℤ) :
    A.weight.comp n →ₗ[F] B.weight.comp n :=
  if hp : (n + 1) % 2 = 0 then
    if h1 : (1 : ℤ) ≤ n then gUpC ψp ((n - 1) / 2).toNat n (by omega)
    else gDownC ψm ((-1 - n) / 2).toNat n (by omega)
  else 0

/-- `gcompC` in the `+` region.  @census none (helper) -/
theorem gcompC_up (ψp : A.weight.comp 1 →ₗ[F] B.weight.comp 1)
    (ψm : A.weight.comp (-1) →ₗ[F] B.weight.comp (-1))
    (k : ℕ) (n : ℤ) (hn : n = 1 + 2 * (k : ℤ)) :
    gcompC ψp ψm n = gUpC ψp k n hn := by
  have hk : ((n - 1) / 2).toNat = k := by omega
  subst hk
  unfold gcompC
  rw [dif_pos (show (n + 1) % 2 = 0 by omega), dif_pos (show (1 : ℤ) ≤ n by omega)]

/-- `gcompC` in the `−` region.  @census none (helper) -/
theorem gcompC_down (ψp : A.weight.comp 1 →ₗ[F] B.weight.comp 1)
    (ψm : A.weight.comp (-1) →ₗ[F] B.weight.comp (-1))
    (k : ℕ) (n : ℤ) (hn : n + 2 * (k : ℤ) = -1) :
    gcompC ψp ψm n = gDownC ψm k n hn := by
  have hk : ((-1 - n) / 2).toNat = k := by omega
  subst hk
  unfold gcompC
  rw [dif_pos (show (n + 1) % 2 = 0 by omega), dif_neg (show ¬((1 : ℤ) ≤ n) by omega)]

/-- **The `ℓ = 0` extension of a compatible pair**, as a linear map on the carrier.
@census none (helper) -/
noncomputable def extendMapC (ψp : A.weight.comp 1 →ₗ[F] B.weight.comp 1)
    (ψm : A.weight.comp (-1) →ₗ[F] B.weight.comp (-1)) :
    A.carrier →ₗ[F] B.carrier :=
  ofComponents (fun n => (B.weight.comp n).subtype ∘ₗ gcompC ψp ψm n)

/-- `extendMapC` on a homogeneous element.  @census none (helper) -/
theorem extendMapC_apply (ψp : A.weight.comp 1 →ₗ[F] B.weight.comp 1)
    (ψm : A.weight.comp (-1) →ₗ[F] B.weight.comp (-1))
    {n : ℤ} {m : A.carrier} (hm : m ∈ A.weight.comp n) :
    extendMapC ψp ψm m = ((gcompC ψp ψm n ⟨m, hm⟩ : B.weight.comp n) : B.carrier) :=
  ofComponents_apply _ hm

/-- **Engine `E9`'s datum**: a pair of maps on the two vertex components of the cyclic quiver,
compatible with its two edges `X : M_{-1} → M_1` and `Y : M_1 → M_{-1}`.  @census none (helper)
@clauses   RQ2-5.13-S-C5a -/
structure ExtDataC (A B : HCFObj F 0) where
  /-- the component map at the `+` vertex, `M_1` -/
  ψp : A.weight.comp 1 →ₗ[F] B.weight.comp 1
  /-- the component map at the `−` vertex, `M_{-1}` -/
  ψm : A.weight.comp (-1) →ₗ[F] B.weight.comp (-1)
  /-- the edge `a`: `ψ₊ ∘ X = X ∘ ψ₋` on `M_{-1}` -/
  edgeX : ∀ (m : A.carrier) (hm : m ∈ A.weight.comp (-1))
      (h : A.weight.X m ∈ A.weight.comp 1),
    ((ψp ⟨A.weight.X m, h⟩ : B.weight.comp 1) : B.carrier)
      = B.weight.X ((ψm ⟨m, hm⟩ : B.weight.comp (-1)) : B.carrier)
  /-- the edge `b`: `ψ₋ ∘ Y = Y ∘ ψ₊` on `M_1` -/
  edgeY : ∀ (m : A.carrier) (hm : m ∈ A.weight.comp 1)
      (h : A.weight.Y m ∈ A.weight.comp (-1)),
    ((ψm ⟨A.weight.Y m, h⟩ : B.weight.comp (-1)) : B.carrier)
      = B.weight.Y ((ψp ⟨m, hm⟩ : B.weight.comp 1) : B.carrier)

namespace ExtDataC

variable (d : ExtDataC A B)

/-- The extension of `d`, as a linear map.  @census none (helper) -/
noncomputable def map : A.carrier →ₗ[F] B.carrier := extendMapC d.ψp d.ψm

theorem map_mem (n : ℤ) (m : A.carrier) (hm : m ∈ A.weight.comp n) :
    d.map m ∈ B.weight.comp n := by
  rw [ExtDataC.map, extendMapC_apply d.ψp d.ψm hm]
  exact Subtype.property _

/-- The value of the extension in the `+` region.  @census none (helper) -/
theorem map_up (k : ℕ) (n : ℤ) (hn : n = 1 + 2 * (k : ℤ))
    (u : A.weight.comp 1) {m : A.carrier} (hm : m ∈ A.weight.comp n)
    (hmu : (A.weight.X ^ k) (u : A.carrier) = m) :
    d.map m = (B.weight.X ^ k) ((d.ψp u : B.weight.comp 1) : B.carrier) := by
  rw [ExtDataC.map, extendMapC_apply d.ψp d.ψm hm, gcompC_up d.ψp d.ψm k n hn]
  exact gUpC_val d.ψp k n hn u hm hmu

/-- The characterisation of the extension in the `−` region.  @census none (helper) -/
theorem map_down (k : ℕ) (n : ℤ) (hn : n + 2 * (k : ℤ) = -1)
    {m : A.carrier} (hm : m ∈ A.weight.comp n)
    (hXm : (A.weight.X ^ k) m ∈ A.weight.comp (-1)) :
    (B.weight.X ^ k) (d.map m)
      = ((d.ψm ⟨(A.weight.X ^ k) m, hXm⟩ : B.weight.comp (-1)) : B.carrier) := by
  rw [ExtDataC.map, extendMapC_apply d.ψp d.ψm hm, gcompC_down d.ψp d.ψm k n hn]
  exact gDownC_val d.ψm k n hn hm hXm

/-- The extension restricts to `ψ₊` on `M_1`.  @census none (helper) -/
theorem map_at_plus (m : A.carrier) (hm : m ∈ A.weight.comp 1) :
    d.map m = ((d.ψp ⟨m, hm⟩ : B.weight.comp 1) : B.carrier) := by
  rw [d.map_up 0 1 (by norm_num) ⟨m, hm⟩ hm (by simp), pow_zero, Module.End.one_apply]

/-- The extension restricts to `ψ₋` on `M_{-1}`.  @census none (helper) -/
theorem map_at_minus (m : A.carrier) (hm : m ∈ A.weight.comp (-1)) :
    d.map m = ((d.ψm ⟨m, hm⟩ : B.weight.comp (-1)) : B.carrier) := by
  have h0 : (A.weight.X ^ (0 : ℕ)) m = m := by simp
  have hmem0 : (A.weight.X ^ (0 : ℕ)) m ∈ A.weight.comp (-1) := by rw [h0]; exact hm
  calc d.map m = (B.weight.X ^ (0 : ℕ)) (d.map m) := by rw [pow_zero]; rfl
    _ = ((d.ψm ⟨(A.weight.X ^ (0 : ℕ)) m, hmem0⟩ : B.weight.comp (-1)) : B.carrier) :=
        d.map_down 0 (-1) (by norm_num) hm hmem0
    _ = _ := congrArg (fun x => ((d.ψm x : B.weight.comp (-1)) : B.carrier))
        (Subtype.ext h0)

/-- **The extension commutes with `X`.**  Inside each of the two chains this is the definition;
at the single wall `n = -1` it is the edge equation `a`.  @census none (helper) -/
theorem map_X_comp (n : ℤ) (m : A.carrier) (hm : m ∈ A.weight.comp n) :
    d.map (A.weight.X m) = B.weight.X (d.map m) := by
  have hXm : A.weight.X m ∈ A.weight.comp (n + 2) := A.weight.X_mem n m hm
  by_cases hp : (n + 1) % 2 = 0
  · rcases (show (1 : ℤ) ≤ n ∨ n ≤ -3 ∨ n = -1 by omega) with h | h | h
    · -- `+` chain interior
      set k : ℕ := ((n - 1) / 2).toNat with hkdef
      have hnk : n = 1 + 2 * (k : ℤ) := by omega
      obtain ⟨u, hu, hmu⟩ := chainX_surjective A 1 k (hjUpC k) k le_rfl (hnk ▸ hm)
      have hmu' : (A.weight.X ^ (k + 1)) u = A.weight.X m := by
        rw [pow_succ', Module.End.mul_apply, hmu]
      rw [d.map_up k n hnk ⟨u, hu⟩ hm hmu,
        d.map_up (k + 1) (n + 2) (by push_cast; omega) ⟨u, hu⟩ hXm hmu', pow_succ',
        Module.End.mul_apply]
    · -- `−` chain interior
      obtain ⟨j, hnj⟩ : ∃ j : ℕ, n + 2 + 2 * (j : ℤ) = -1 := ⟨((-3 - n) / 2).toNat, by omega⟩
      have hnk : n + 2 * ((j + 1 : ℕ) : ℤ) = -1 := by push_cast; omega
      have hXjX : (A.weight.X ^ j) (A.weight.X m) = (A.weight.X ^ (j + 1)) m := by
        rw [← Module.End.mul_apply, ← pow_succ]
      have hmem1 : (A.weight.X ^ (j + 1)) m ∈ A.weight.comp (-1) := by
        have hv := chainX_val A n (j + 1) (hjDownC n (j + 1) hnk) (j + 1) le_rfl ⟨m, hm⟩
        have hp2 := (chainX A n (j + 1) (hjDownC n (j + 1) hnk) (j + 1) le_rfl ⟨m, hm⟩).2
        rw [hv, hnk] at hp2
        exact hp2
      have hmem2 : (A.weight.X ^ j) (A.weight.X m) ∈ A.weight.comp (-1) := by
        rw [hXjX]; exact hmem1
      have h1 := d.map_down (j + 1) n hnk hm hmem1
      have h2 := d.map_down j (n + 2) hnj hXm hmem2
      have h3 : (B.weight.X ^ j) (B.weight.X (d.map m)) = (B.weight.X ^ (j + 1)) (d.map m) := by
        rw [← Module.End.mul_apply, ← pow_succ]
      refine chainX_injective B (n + 2) j (hjDownC (n + 2) j hnj) j le_rfl
        (d.map_mem (n + 2) _ hXm) (B.weight.X_mem n _ (d.map_mem n m hm)) ?_
      rw [h2, h3, h1]
      exact congrArg (fun x => ((d.ψm x : B.weight.comp (-1)) : B.carrier))
        (Subtype.ext hXjX)
    · -- the single `X`-wall
      subst h
      have hXmem : A.weight.X m ∈ A.weight.comp 1 := by
        have h' := hXm; rwa [show (-1 : ℤ) + 2 = 1 by ring] at h'
      rw [d.map_at_minus m hm, d.map_at_plus _ hXmem]
      exact d.edgeX m hm hXmem
  · have hbot := A.centralCharacter n (by omega)
    rw [hbot, Submodule.mem_bot] at hm
    rw [hm]
    simp

/-- The extension commutes with `X`, globally.  @census none (helper) -/
theorem map_X (v : A.carrier) : d.map (A.weight.X v) = B.weight.X (d.map v) :=
  eq_of_comp (d.map.comp A.weight.X) (B.weight.X.comp d.map)
    (fun n m hm => d.map_X_comp n m hm) v

/-- The extension commutes with every power of `X`.  @census none (helper) -/
theorem map_pow_X_eq (k : ℕ) (v : A.carrier) :
    d.map ((A.weight.X ^ k) v) = (B.weight.X ^ k) (d.map v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, d.map_X, ih]

/-- The extension commutes with `H`.  @census none (helper) -/
theorem map_H (v : A.carrier) : d.map (A.weight.H v) = B.weight.H (d.map v) := by
  refine eq_of_comp (d.map.comp A.weight.H) (B.weight.H.comp d.map) (fun n m hm => ?_) v
  show d.map (A.weight.H m) = B.weight.H (d.map m)
  rw [A.weight.H_apply n m hm, map_smul, B.weight.H_apply n _ (d.map_mem n m hm)]

/-- The `Y`-wall — the edge equation `b`.  At `ℓ = 0` there is only one.  @census none (helper) -/
theorem map_Y_wall (m : A.carrier) (hm : m ∈ A.weight.comp 1) :
    d.map (A.weight.Y m) = B.weight.Y (d.map m) := by
  have hYm : A.weight.Y m ∈ A.weight.comp (-1) := by
    have h := A.weight.Y_mem _ m hm
    rwa [show (1 : ℤ) - 2 = -1 by ring] at h
  rw [d.map_at_minus _ hYm, d.map_at_plus m hm]
  exact d.edgeY m hm hYm

/-- `C`-equivariance at the `+` vertex: `4XY = C` there, because `λ = 0`.
@census none (helper) -/
theorem map_casimir_plus (m : A.carrier) (hm : m ∈ A.weight.comp 1) :
    d.map (A.weight.casimir m) = B.weight.casimir (d.map m) := by
  have hm0 : m ∈ A.weight.comp ((0 : ℤ) + 1) := by rwa [show (0 : ℤ) + 1 = 1 by ring]
  have hmB : d.map m ∈ B.weight.comp ((0 : ℤ) + 1) := by
    rw [show (0 : ℤ) + 1 = 1 by ring]; exact d.map_mem 1 m hm
  have hA := A.weight.four_X_Y_apply 0 m hm0
  have hB := B.weight.four_X_Y_apply 0 (d.map m) hmB
  have hYX : d.map (A.weight.X (A.weight.Y m)) = B.weight.X (B.weight.Y (d.map m)) := by
    rw [d.map_X, d.map_Y_wall m hm]
  have e1 : A.weight.casimir m
      = (4 : F) • A.weight.X (A.weight.Y m)
        + ((((0 : ℤ)) : F) ^ 2) • m := by
    rw [hA]; abel
  rw [e1, map_add, map_smul, map_smul, hYX, hB]
  abel

/-- `C`-equivariance at the `−` vertex: `4YX = C` there.  @census none (helper) -/
theorem map_casimir_minus (m : A.carrier) (hm : m ∈ A.weight.comp (-1)) :
    d.map (A.weight.casimir m) = B.weight.casimir (d.map m) := by
  have hm0 : m ∈ A.weight.comp (-((0 : ℤ) + 1)) := by rwa [show -((0 : ℤ) + 1) = -1 by ring]
  have hmB : d.map m ∈ B.weight.comp (-((0 : ℤ) + 1)) := by
    rw [show -((0 : ℤ) + 1) = -1 by ring]; exact d.map_mem (-1) m hm
  have hA := A.weight.four_Y_X_apply 0 m hm0
  have hB := B.weight.four_Y_X_apply 0 (d.map m) hmB
  have hXmem : A.weight.X m ∈ A.weight.comp 1 := by
    have h := A.weight.X_mem _ m hm
    rwa [show (-1 : ℤ) + 2 = 1 by ring] at h
  have hXY : d.map (A.weight.Y (A.weight.X m)) = B.weight.Y (B.weight.X (d.map m)) := by
    rw [d.map_Y_wall _ hXmem, d.map_X]
  have e1 : A.weight.casimir m
      = (4 : F) • A.weight.Y (A.weight.X m)
        + ((((0 : ℤ)) : F) ^ 2) • m := by
    rw [hA]; abel
  rw [e1, map_add, map_smul, map_smul, hXY, hB]
  abel

/-- **`C`-equivariance everywhere**, propagated along the two `X`-chains.  @census none (helper) -/
theorem map_casimir_comp (n : ℤ) (m : A.carrier) (hm : m ∈ A.weight.comp n) :
    d.map (A.weight.casimir m) = B.weight.casimir (d.map m) := by
  by_cases hp : (n + 1) % 2 = 0
  · rcases (show (1 : ℤ) ≤ n ∨ n ≤ -1 by omega) with h | h
    · set k : ℕ := ((n - 1) / 2).toNat with hkdef
      have hnk : n = 1 + 2 * (k : ℤ) := by omega
      obtain ⟨u, hu, hmu⟩ := chainX_surjective A 1 k (hjUpC k) k le_rfl (hnk ▸ hm)
      calc d.map (A.weight.casimir m)
          = d.map (A.weight.casimir ((A.weight.X ^ k) u)) := by rw [hmu]
        _ = d.map ((A.weight.X ^ k) (A.weight.casimir u)) := by rw [ExtData.casimir_pow_X]
        _ = (B.weight.X ^ k) (d.map (A.weight.casimir u)) := d.map_pow_X_eq _ _
        _ = (B.weight.X ^ k) (B.weight.casimir (d.map u)) := by rw [d.map_casimir_plus u hu]
        _ = B.weight.casimir ((B.weight.X ^ k) (d.map u)) := (ExtData.casimir_pow_X k _).symm
        _ = B.weight.casimir (d.map ((A.weight.X ^ k) u)) := by rw [d.map_pow_X_eq]
        _ = B.weight.casimir (d.map m) := by rw [hmu]
    · set k : ℕ := ((-1 - n) / 2).toNat with hkdef
      have hnk : n + 2 * (k : ℤ) = -1 := by omega
      have hXmem : (A.weight.X ^ k) m ∈ A.weight.comp (-1) := by
        have hv := chainX_val A n k (hjDownC n k hnk) k le_rfl ⟨m, hm⟩
        have hp2 := (chainX A n k (hjDownC n k hnk) k le_rfl ⟨m, hm⟩).2
        rw [hv, hnk] at hp2
        exact hp2
      refine chainX_injective B n k (hjDownC n k hnk) k le_rfl
        (d.map_mem n _ (casimir_mem_comp A.weight n m hm))
        (casimir_mem_comp B.weight n _ (d.map_mem n m hm)) ?_
      calc (B.weight.X ^ k) (d.map (A.weight.casimir m))
          = d.map ((A.weight.X ^ k) (A.weight.casimir m)) := (d.map_pow_X_eq k _).symm
        _ = d.map (A.weight.casimir ((A.weight.X ^ k) m)) := by rw [ExtData.casimir_pow_X]
        _ = B.weight.casimir (d.map ((A.weight.X ^ k) m)) := d.map_casimir_minus _ hXmem
        _ = B.weight.casimir ((B.weight.X ^ k) (d.map m)) := by rw [d.map_pow_X_eq]
        _ = (B.weight.X ^ k) (B.weight.casimir (d.map m)) := ExtData.casimir_pow_X k _
  · have hbot := A.centralCharacter n (by omega)
    rw [hbot, Submodule.mem_bot] at hm
    rw [hm]
    simp

/-- `C`-equivariance, globally.  @census none (helper) -/
theorem map_casimir (v : A.carrier) :
    d.map (A.weight.casimir v) = B.weight.casimir (d.map v) :=
  eq_of_comp (d.map.comp A.weight.casimir) (B.weight.casimir.comp d.map)
    (fun n m hm => d.map_casimir_comp n m hm) v

/-- **The extension commutes with `Y`.**  Away from the single `Y`-wall `n = 1` this is
`4XY = C − (n-1)²` plus `X`- and `C`-equivariance and the injectivity of `X` off `0`.
@census none (helper) -/
theorem map_Y_comp (n : ℤ) (m : A.carrier) (hm : m ∈ A.weight.comp n) :
    d.map (A.weight.Y m) = B.weight.Y (d.map m) := by
  by_cases hp : (n + 1) % 2 = 0
  · by_cases h1 : n = 1
    · subst h1; exact d.map_Y_wall m hm
    · have hj : ((n - 1) : ℤ) ^ 2 ≠ (((0 : ℕ)) : ℤ) ^ 2 := by
        have hne : n - 1 ≠ 0 := by omega
        simpa using pow_ne_zero 2 hne
      have hjq := sq_ne_sq_of (F := F) (ℓ := 0) (n - 1) hj
      have hm' : m ∈ A.weight.comp ((n - 1) + 1) := by rwa [show n - 1 + 1 = n by ring]
      have hA := A.weight.four_X_Y_apply (n - 1) m hm'
      have hB := B.weight.four_X_Y_apply (n - 1) (d.map m) (by
        have hmm := d.map_mem n m hm
        rwa [show n - 1 + 1 = n by ring])
      have hYmem : A.weight.Y m ∈ A.weight.comp (n - 2) := A.weight.Y_mem n m hm
      have e4 : (4 : F) • B.weight.X (d.map (A.weight.Y m))
          = (4 : F) • B.weight.X (B.weight.Y (d.map m)) := by
        calc (4 : F) • B.weight.X (d.map (A.weight.Y m))
            = (4 : F) • d.map (A.weight.X (A.weight.Y m)) := by rw [d.map_X]
          _ = d.map ((4 : F) • A.weight.X (A.weight.Y m)) := (map_smul _ _ _).symm
          _ = d.map (A.weight.casimir m - (((n - 1 : ℤ) : F) ^ 2) • m) := by rw [hA]
          _ = B.weight.casimir (d.map m) - (((n - 1 : ℤ) : F) ^ 2) • d.map m := by
              rw [map_sub, map_smul, d.map_casimir]
          _ = (4 : F) • B.weight.X (B.weight.Y (d.map m)) := hB.symm
      have e5 : B.weight.X (d.map (A.weight.Y m)) = B.weight.X (B.weight.Y (d.map m)) :=
        smul_right_injective B.carrier (by norm_num : (4 : F) ≠ 0) e4
      have h0 : B.weight.X (d.map (A.weight.Y m) - B.weight.Y (d.map m)) = 0 := by
        rw [map_sub, e5, sub_self]
      have hmem : d.map (A.weight.Y m) - B.weight.Y (d.map m) ∈ B.weight.comp (n - 1 - 1) := by
        rw [show n - 1 - 1 = n - 2 by ring]
        exact Submodule.sub_mem _ (d.map_mem _ _ hYmem) (B.weight.Y_mem n _ (d.map_mem n m hm))
      exact sub_eq_zero.mp (X_injective_on_comp (A := B) (n - 1) hjq _ hmem h0)
  · have hbot := A.centralCharacter n (by omega)
    rw [hbot, Submodule.mem_bot] at hm
    rw [hm]
    simp

/-- The extension commutes with `Y`, globally.  @census none (helper) -/
theorem map_Y (v : A.carrier) : d.map (A.weight.Y v) = B.weight.Y (d.map v) :=
  eq_of_comp (d.map.comp A.weight.Y) (B.weight.Y.comp d.map)
    (fun n m hm => d.map_Y_comp n m hm) v

/-- **Engine `E9`**: a compatible pair of component maps *is* the restriction of a morphism of
`HC_0(𝔤,K)_{ℚ[√-1]}`.  @census none (helper) -/
noncomputable def hom : A ⟶ B where
  toLinearMap := d.map
  map_H := d.map_H
  map_X := d.map_X
  map_Y := d.map_Y
  map_comp := d.map_mem

end ExtDataC

end E9



open RationalQuivers.HC RationalQuivers.RationalQuiver CategoryTheory
open RationalQuivers.Gelfand
open scoped TensorProduct

variable {F : Type} [Field F] [CharZero F]

section CycSplit

open RationalQuivers.Unipotent
open scoped Classical

/-- The vertices of the split cyclic quiver over `ℚ[√-1]`: `−`(=0), `+`(=1).
@census none (helper) -/
abbrev vtxS (v : Fin 2) : (cyclicSplit F).V := v

/-- The edges of the split cyclic quiver: `a : − → +`(=0), `b : + → −`(=1).
@census none (helper) -/
abbrev edgeS (e : Fin 2) : (cyclicSplit F).E := e

/-- The vertex family of `𝔼_{ℚ[√-1]}(M)` at `ℓ = 0`: `M(−) = M_{-1}`, `M(+) = M_1`.
@census none (helper) -/
abbrev V2i (A : HCFObj F 0) (v : Fin 2) : Type := ↥(A.weight.comp (cycIdx v))

/-- The edge maps at `ℓ = 0`, split: `a ↦ X : M_{-1} → M_1`, `b ↦ Y : M_1 → M_{-1}`.
@census none (helper) -/
noncomputable def E_CycSplit_edge (A : HCFObj F 0) :
    ∀ e : Fin 2, V2i A (RQuiver.cyclic.source e) →ₗ[F] V2i A (RQuiver.cyclic.target e)
  | 0 => A.weight.X.restrict fun _ hv => by
      have h := A.weight.X_mem _ _ hv
      exact (show (cycIdx (RQuiver.cyclic.source 0) + 2 : ℤ) = cycIdx (RQuiver.cyclic.target 0)
        by decide) ▸ h
  | 1 => A.weight.Y.restrict fun _ hv => by
      have h := A.weight.Y_mem _ _ hv
      exact (show (cycIdx (RQuiver.cyclic.source 1) - 2 : ℤ) = cycIdx (RQuiver.cyclic.target 1)
        by decide) ▸ h

/-- **`𝔼_{ℚ[√-1]}(M)` at `ℓ = 0`** as a representation of the split cyclic quiver: the two vertex
spaces `M_{∓1}`, the two edges `X`, `Y`, and the trivial `Gal(ℚ[√-1]/ℚ[√-1])`-structure.
@census none (helper) -/
noncomputable def E_CycSplit_rep (A : HCFObj F 0) : RationalQuiver.Rep (cyclicSplit F) :=
  RationalQuiver.Rep.ofFiniteDimensional (Γ := cyclicSplit F) (V2i A)
    (fun _ _ => AddEquiv.refl _)
    (fun σ _ a m => by rw [galSelf_apply]; rfl)
    (fun _ _ _ _ => rfl)
    (fun e => E_CycSplit_edge A e)
    (fun _ _ _ _ h => by
      cases h
      rfl)

/-! #### Nilpotency (the argument of `cyc_nilpotent`, read on `HCFObj F 0`) -/

/-- @census none (helper) -/
theorem cycS_casimir_mapsTo (A : HCFObj F 0) : ∀ v ∈ A.weight.comp (cycIdx 1),
    (A.weight.casimir - ((((0 : ℕ)) : F) ^ 2)
      • (1 : Module.End F A.carrier)) v ∈ A.weight.comp (cycIdx 1) :=
  fun _ hv => casimir_sub_sq_mem A.setup _ hv

/-- The loop at the `+` vertex: `X ∘ Y` on `M_1`.  @census none (helper) -/
noncomputable def cycSLoop (A : HCFObj F 0) : Module.End F (V2i A 1) :=
  (E_CycSplit_edge A 0).comp (E_CycSplit_edge A 1)

/-- `4·(X∘Y) = C` on `M_1` at `ℓ = 0`.  @census none (helper) -/
theorem four_smul_cycSLoop (A : HCFObj F 0) :
    (4 : F) • cycSLoop A
      = (A.weight.casimir - ((((0 : ℕ)) : F) ^ 2)
          • (1 : Module.End F A.carrier)).restrict (cycS_casimir_mapsTo A) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  obtain ⟨v, hv⟩ := x
  show (4 : F) • A.weight.X (A.weight.Y v)
    = A.weight.casimir v - ((((0 : ℕ)) : F) ^ 2) • v
  have h := four_X_Y_apply A.setup (cycIdx 1) v hv
  have hc : (((cycIdx 1 : ℤ) : F) - 1) ^ 2 = ((((0 : ℕ)) : F) ^ 2) := by
    norm_num [cycIdx]
  rwa [hc] at h

/-- The loop is nilpotent: at `λ = 0` the Casimir is.  @census none (helper) -/
theorem cycSLoop_pow_eq_zero (A : HCFObj F 0) : ∃ m : ℕ, (cycSLoop A) ^ m = 0 := by
  obtain ⟨m, hm⟩ := Module.End.isNilpotent.restrict (cycS_casimir_mapsTo A)
    A.setup.gic_nilpotent
  refine ⟨m, ?_⟩
  have h4 : ((4 : F) ^ m) ≠ 0 := pow_ne_zero _ (by norm_num)
  have heq : (4 : F) ^ m • (cycSLoop A) ^ m
      = (4 : F) ^ m • (0 : Module.End F (V2i A 1)) := by
    rw [smul_zero, ← smul_pow, four_smul_cycSLoop]
    exact hm
  exact smul_right_injective _ h4 heq

/-- An edge landing away from `+` starts at `+`.  @census none (helper) -/
theorem cycS_edge_dichotomy {x y : (cyclicSplit F).V} (g : x ⟶ y) (hy : y ≠ (vtxS (F := F) 1)) :
    x = (vtxS (F := F) 1) := by
  obtain ⟨k, hs, ht⟩ :=
    (g : {e : Fin 2 // RQuiver.cyclic.source e = x ∧ RQuiver.cyclic.target e = y})
  obtain ⟨kv, hkv⟩ := k
  interval_cases kv <;> first
    | exact absurd ht.symm hy
    | exact hs.symm

/-- No self-loop at `+`.  @census none (helper) -/
theorem cycS_no_selfloop {x : (cyclicSplit F).V} (g : x ⟶ (vtxS (F := F) 1)) : x ≠ (vtxS (F := F) 1) := by
  obtain ⟨k, hs, ht⟩ :=
    (g : {e : Fin 2 // RQuiver.cyclic.source e = x ∧ RQuiver.cyclic.target e = (vtxS (F := F) 1)})
  have hkey : ∀ e : Fin 2, RQuiver.cyclic.target e = (1 : Fin 2) →
      RQuiver.cyclic.source e ≠ (1 : Fin 2) := by decide
  rw [← hs]
  exact hkey k ht

/-- The path composite of the split `ℓ = 0` edge family.  @census none (helper) -/
noncomputable abbrev cycSPath (A : HCFObj F 0) {a b : (cyclicSplit F).V}
    (p : Quiver.Path a b) : V2i A a →ₗ[F] V2i A b :=
  RationalQuiver.pathCompose (Q := (cyclicSplit F).toRQuiver) (V2i A)
    (E_CycSplit_edge A) p

/-- A length-two window based at `+` is the loop.  @census none (helper) -/
theorem cycSLoop_arrow_comp (A : HCFObj F 0) {w : (cyclicSplit F).V}
    (g1 : ((vtxS (F := F) 1)) ⟶ w) (g2 : w ⟶ ((vtxS (F := F) 1))) :
    RationalQuiver.arrowCompose (Q := (cyclicSplit F).toRQuiver) (V2i A)
        (E_CycSplit_edge A) g2 ∘ₗ
        RationalQuiver.arrowCompose (Q := (cyclicSplit F).toRQuiver) (V2i A)
          (E_CycSplit_edge A) g1
      = cycSLoop A := by
  obtain ⟨k1, hs1, ht1⟩ :=
    (g1 : {e : Fin 2 // RQuiver.cyclic.source e = (1 : Fin 2) ∧ RQuiver.cyclic.target e = w})
  obtain ⟨k2, hs2, ht2⟩ :=
    (g2 : {e : Fin 2 // RQuiver.cyclic.source e = w ∧ RQuiver.cyclic.target e = (1 : Fin 2)})
  have hkey : ∀ e1 e2 : Fin 2, RQuiver.cyclic.source e1 = (1 : Fin 2) →
      RQuiver.cyclic.target e2 = (1 : Fin 2) →
      RQuiver.cyclic.target e1 = RQuiver.cyclic.source e2 → e1 = 1 ∧ e2 = 0 := by decide
  obtain ⟨rfl, rfl⟩ := hkey k1 k2 hs1 ht2 (ht1.trans hs2.symm)
  subst ht1
  rfl

/-- Peeling `2k` `+`-based windows off the end of a path landing at `+`.  @census none (helper) -/
theorem cycSLoop_path_peel (A : HCFObj F 0) :
    ∀ (k : ℕ) (a : (cyclicSplit F).V) (p : Quiver.Path a ((vtxS (F := F) 1))),
      2 * k ≤ p.length →
      ∃ q : Quiver.Path a ((vtxS (F := F) 1)), q.length = p.length - 2 * k ∧
        ∀ v, cycSPath A p v = ((cycSLoop A) ^ k) (cycSPath A q v) := by
  intro k
  induction k with
  | zero => intro a p _; exact ⟨p, by simp, fun v => by simp⟩
  | succ k ih =>
    intro a p hp
    cases p with
    | nil => simp [Quiver.Path.length] at hp
    | cons q1 g_last =>
      rename_i X
      have hXne : X ≠ (vtxS (F := F) 1) := cycS_no_selfloop g_last
      have hp1 : 2 * k + 1 ≤ q1.length := by
        simp only [Quiver.Path.length] at hp; omega
      cases q1 with
      | nil => simp at hp1
      | cons q2 g_prev =>
        rename_i Y
        have hY : Y = (vtxS (F := F) 1) := cycS_edge_dichotomy g_prev hXne
        subst hY
        have hp2 : 2 * k ≤ q2.length := by
          simp only [Quiver.Path.length] at hp1; omega
        obtain ⟨q, hqlen, hqeq⟩ := ih _ q2 hp2
        refine ⟨q, by simp only [Quiver.Path.length] at hqlen ⊢; omega, fun v => ?_⟩
        have hloop := cycSLoop_arrow_comp A g_prev g_last
        have hloop_apply : ∀ u : V2i A 1,
            RationalQuiver.arrowCompose (Q := (cyclicSplit F).toRQuiver) (V2i A)
                (E_CycSplit_edge A) g_last
                (RationalQuiver.arrowCompose (Q := (cyclicSplit F).toRQuiver) (V2i A)
                  (E_CycSplit_edge A) g_prev u)
              = cycSLoop A u := fun u => by
          exact LinearMap.congr_fun hloop u
        have step1 : cycSPath A ((q2.cons g_prev).cons g_last) v
            = RationalQuiver.arrowCompose (Q := (cyclicSplit F).toRQuiver) (V2i A)
                (E_CycSplit_edge A) g_last
                (RationalQuiver.arrowCompose (Q := (cyclicSplit F).toRQuiver) (V2i A)
                  (E_CycSplit_edge A) g_prev (cycSPath A q2 v)) := by
          have e1 := RationalQuiver.pathCompose_cons (Q := (cyclicSplit F).toRQuiver) (V2i A)
            (E_CycSplit_edge A) (q2.cons g_prev) g_last
          have e2 := RationalQuiver.pathCompose_cons (Q := (cyclicSplit F).toRQuiver) (V2i A)
            (E_CycSplit_edge A) q2 g_prev
          exact (LinearMap.congr_fun e1 v).trans
            (congrArg (RationalQuiver.arrowCompose (Q := (cyclicSplit F).toRQuiver) (V2i A)
              (E_CycSplit_edge A) g_last) (LinearMap.congr_fun e2 v))
        have hpow_apply : ∀ z : V2i A 1,
            (((cycSLoop A) ^ (k + 1)) z) = cycSLoop A (((cycSLoop A) ^ k) z) := by
          intro z
          rw [pow_succ', Module.End.mul_apply]
        rw [step1, hqeq, hloop_apply]
        exact (hpow_apply (cycSPath A q v)).symm

/-- **`𝔼_{ℚ[√-1]}(M)` is nilpotent at `ℓ = 0`.**  @census none (helper) -/
theorem E_CycSplit_isNilpotent (A : HCFObj F 0) : (E_CycSplit_rep A).IsNilpotent := by
  obtain ⟨m, hm⟩ := cycSLoop_pow_eq_zero A
  refine ⟨2 * m + 1, fun a b p hp => LinearMap.ext fun v => ?_⟩
  show cycSPath A p v = 0
  by_cases hb : b = (vtxS (F := F) 1)
  · subst hb
    obtain ⟨q, _, hq⟩ := cycSLoop_path_peel A m _ p (by omega)
    have hzero : ∀ z : V2i A 1, (0 : Module.End F (V2i A 1)) z = 0 := fun _ => rfl
    exact (hq v).trans (by rw [hm]; exact hzero _)
  · cases p with
    | nil => simp [Quiver.Path.length] at hp
    | cons q1 g_last =>
      rename_i c
      have hc : c = (vtxS (F := F) 1) := cycS_edge_dichotomy g_last hb
      subst hc
      have hp1 : 2 * m ≤ q1.length := by
        simp only [Quiver.Path.length] at hp; omega
      obtain ⟨q, _, hq⟩ := cycSLoop_path_peel A m _ q1 hp1
      have hzero : ∀ z : V2i A 1, (0 : Module.End F (V2i A 1)) z = 0 := fun _ => rfl
      have e1 := RationalQuiver.pathCompose_cons (Q := (cyclicSplit F).toRQuiver) (V2i A)
        (E_CycSplit_edge A) q1 g_last
      refine (LinearMap.congr_fun e1 v).trans ?_
      show RationalQuiver.arrowCompose (Q := (cyclicSplit F).toRQuiver) (V2i A)
        (E_CycSplit_edge A) g_last (cycSPath A q1 v) = 0
      refine (congrArg (RationalQuiver.arrowCompose (Q := (cyclicSplit F).toRQuiver) (V2i A)
        (E_CycSplit_edge A) g_last) (hq v)).trans ?_
      rw [hm]
      exact map_zero _

/-! #### The functor, its faithfulness (`E1`) and its fullness (`E9`) -/

/-- `𝔼_{ℚ[√-1]}(M)` at `ℓ = 0` as an object of `Rep^nil` of the split cyclic quiver.
@census none (helper) -/
noncomputable def E_CycSplit_obj (A : HCFObj F 0) :
    (RationalQuiver.RepNil (cyclicSplit F)).FullSubcategory :=
  ⟨⟨E_CycSplit_rep A, fun _ => A.admissible _⟩, E_CycSplit_isNilpotent A⟩

/-- The vertex components of `𝔼_{ℚ[√-1]}(f)` at `ℓ = 0`.  @census none (helper) -/
noncomputable def E_CycSplit_map_ψ {A B : HCFObj F 0} (f : A ⟶ B) (v : Fin 2) :
    V2i A v →ₗ[F] V2i B v :=
  f.toLinearMap.restrict fun _ hv => f.map_comp _ _ hv

/-- @census none (helper) -/
theorem E_CycSplit_map_edge {A B : HCFObj F 0} (f : A ⟶ B) :
    ∀ (e : Fin 2) (m : V2i A (RQuiver.cyclic.source e)),
      E_CycSplit_map_ψ f (RQuiver.cyclic.target e) (E_CycSplit_edge A e m)
        = E_CycSplit_edge B e (E_CycSplit_map_ψ f (RQuiver.cyclic.source e) m)
  | 0, _ => Subtype.ext (f.map_X _)
  | 1, _ => Subtype.ext (f.map_Y _)

/-- `𝔼_{ℚ[√-1]}(f)` at `ℓ = 0`.  @census none (helper) -/
noncomputable def E_CycSplit_hom {A B : HCFObj F 0} (f : A ⟶ B) :
    RationalQuiver.Rep.Hom (E_CycSplit_rep A) (E_CycSplit_rep B) where
  ψ v := E_CycSplit_map_ψ f v
  edge e m := E_CycSplit_map_edge f e m
  rational _ _ _ := rfl

/-- **`𝔼_{ℚ[√-1]}` at `ℓ = 0`**, `HC_0(𝔤,K)_{ℚ[√-1]} ⥤ Rep^nil(cyclic_{ℚ[√-1]})`, split.
@census none (helper) -/
noncomputable def E_CycSplitFunctor :
    HCF F 0 ⥤ (RationalQuiver.RepNil (cyclicSplit F)).FullSubcategory where
  obj A := E_CycSplit_obj A
  map f := ⟨E_CycSplit_hom f⟩
  map_id A := by
    apply ObjectProperty.hom_ext
    exact RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact RationalQuiver.Rep.Hom.ext (funext fun _ => rfl)

/-- Faithfulness — `E1` (`eq_of_eq_on_V3`) at `ℓ = 0`, as in `cyc_eq_of_eq_on_V2`.
@census none (helper) -/
theorem E_CycSplit_faithful : (E_CycSplitFunctor (F := F)).Faithful := by
  constructor
  intro A B f g hfg
  have h1 : (E_CycSplit_hom f).ψ = (E_CycSplit_hom g).ψ :=
    congrArg (fun (u : (E_CycSplitFunctor (F := F)).obj A ⟶ (E_CycSplitFunctor (F := F)).obj B) => u.hom.ψ) hfg
  have h : ∀ (v : Fin 2) (m : A.carrier), m ∈ A.weight.comp (cycIdx v) →
      f.toLinearMap m = g.toLinearMap m := fun v m hm =>
    congrArg (fun (T : V2i A v →ₗ[F] V2i B v) => ((T ⟨m, hm⟩ : V2i B v) : B.carrier))
      (congrFun h1 v)
  refine eq_of_eq_on_V3 f g (fun v m hm => ?_)
  fin_cases v
  · exact h 0 m hm
  · exact h 1 m hm
  · exact h 1 m hm

/-- Engine `E9`'s datum, read off a morphism of split cyclic representations.
@census none (helper) -/
noncomputable def cycSExtData {A B : HCFObj F 0}
    (w : RationalQuiver.Rep.Hom (E_CycSplit_rep A) (E_CycSplit_rep B)) : ExtDataC A B where
  ψp := w.ψ ((vtxS (F := F) 1))
  ψm := w.ψ ((vtxS (F := F) 0))
  edgeX := fun m hm _ => congrArg Subtype.val (w.edge ((edgeS (F := F) 0)) ⟨m, hm⟩)
  edgeY := fun m hm _ => congrArg Subtype.val (w.edge ((edgeS (F := F) 1)) ⟨m, hm⟩)

/-- Engine `E9`'s extension of `cycSExtData` restricts to the given morphism on both vertex
components.  @census none (helper) -/
theorem cycSExtData_val {A B : HCFObj F 0}
    (w : RationalQuiver.Rep.Hom (E_CycSplit_rep A) (E_CycSplit_rep B)) (v : Fin 2) (x : V2i A v) :
    (cycSExtData w).map ((x : A.carrier)) = Subtype.val (w.ψ v x) := by
  fin_cases v
  · exact (cycSExtData w).map_at_minus _ x.2
  · exact (cycSExtData w).map_at_plus _ x.2

/-- Fullness — engine `E9`.  @census none (helper) -/
theorem E_CycSplit_full : (E_CycSplitFunctor (F := F)).Full := by
  constructor
  intro A B u
  refine ⟨(cycSExtData u.hom).hom, ?_⟩
  apply ObjectProperty.hom_ext
  refine RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun m => Subtype.ext ?_)
  exact cycSExtData_val u.hom v m

section E10S

variable (V : (RationalQuiver.RepNil (cyclicSplit F)).FullSubcategory)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

/-! #### The vertex spaces, the two edges and the two loops -/

/-- The vertex spaces of a representation of the cyclic quiver, by index: `V(−)` at `0`, `V(+)` at
`1`.  @census none (helper; engine `E10`) -/
abbrev czVM (v : Fin 2) : Type := V.obj.toRep.M (vtxS v)

/-- `φ_a : V(−) → V(+)`, the first edge.  @census none (helper; engine `E10`) -/
noncomputable def czEdgeA : czVM V 0 →ₗ[F] czVM V 1 :=
  V.obj.toRep.φEdge ((edgeS (F := F) 0))

/-- `φ_b : V(+) → V(−)`, the second edge.  @census none (helper; engine `E10`) -/
noncomputable def czEdgeB : czVM V 1 →ₗ[F] czVM V 0 :=
  V.obj.toRep.φEdge ((edgeS (F := F) 1))

/-- `n_+ := φ_aφ_b`, the loop at the `+` vertex.  @census none (helper; engine `E10`) -/
noncomputable def czNPlus : Module.End F (czVM V 1) :=
  (czEdgeA V).comp (czEdgeB V)

/-- `n_- := φ_bφ_a`, the loop at the `−` vertex.  @census none (helper; engine `E10`) -/
noncomputable def czNMinus : Module.End F (czVM V 0) :=
  (czEdgeB V).comp (czEdgeA V)

/-- `φ_+ := 4n_+`; at `ℓ = 0` this is the whole of `φ_• = ℓ²·𝟏 + 4n_•`.
@census none (helper; engine `E10`) -/
noncomputable def czPhiPlus : Module.End F (czVM V 1) :=
  (4 : F) • czNPlus V

/-- `φ_- := 4n_-`.  @census none (helper; engine `E10`) -/
noncomputable def czPhiMinus : Module.End F (czVM V 0) :=
  (4 : F) • czNMinus V

/-- The arrow `b : + → −` of the cyclic quiver.  @census none (helper; engine `E10`) -/
def czArrowB : ((vtxS (F := F) 1)) ⟶ ((vtxS (F := F) 0)) := ⟨(edgeS (F := F) 1), rfl, rfl⟩

/-- The arrow `a : − → +` of the cyclic quiver.  @census none (helper; engine `E10`) -/
def czArrowA : ((vtxS (F := F) 0)) ⟶ ((vtxS (F := F) 1)) := ⟨(edgeS (F := F) 0), rfl, rfl⟩

/-- The loop `a ∘ b` at the `+` vertex, as a path.  @census none (helper; engine `E10`) -/
def czLoopPath : Quiver.Path ((vtxS (F := F) 1)) ((vtxS (F := F) 1)) :=
  (Quiver.Path.nil.cons (czArrowB)).cons (czArrowA)

/-- The path composite along the loop is `n_+`.  @census none (helper; engine `E10`) -/
theorem czPathMap_loop :
    V.obj.toRep.pathMap (a := (vtxS (F := F) 1)) (b := (vtxS (F := F) 1)) (czLoopPath)
      = czNPlus V := by
  rw [czLoopPath, RationalQuiver.Rep.pathMap_cons, RationalQuiver.Rep.pathMap_cons,
    RationalQuiver.Rep.pathMap_nil, LinearMap.comp_id]
  rfl

/-- `n_+` is nilpotent: it is the composite along a loop of length two in a nilpotent
representation.  @census none (helper; engine `E10`) -/
theorem czNPlus_isNilpotent : IsNilpotent (czNPlus V) := by
  rw [← czPathMap_loop V]
  exact isNilpotent_pathMap_loop _ V.property _ (by simp [czLoopPath, Quiver.Path.length])

/-- `n_-` is nilpotent.  @census none (helper; engine `E10`) -/
theorem czNMinus_isNilpotent : IsNilpotent (czNMinus V) :=
  isNilpotent_comp_swap (f := czEdgeA V) (g := czEdgeB V) (czNPlus_isNilpotent V)

/-- `φ_+` is nilpotent.  @census none (helper; engine `E10`) -/
theorem czPhiPlus_isNilpotent : IsNilpotent (czPhiPlus V) :=
  IsNilpotent.smul' (czNPlus_isNilpotent V) _

/-- `φ_-` is nilpotent.  @census none (helper; engine `E10`) -/
theorem czPhiMinus_isNilpotent : IsNilpotent (czPhiMinus V) :=
  IsNilpotent.smul' (czNMinus_isNilpotent V) _

/-! #### The graded carrier -/

/-- `T := V(+) × V(−)`, the ambient space every component sits in.
@census none (helper; engine `E10`) -/
abbrev czT : Type := czVM V 1 × czVM V 0

/-- `V(+) ↪ T`.  @census none (helper; engine `E10`) -/
noncomputable def czIotaPlus : czVM V 1 →ₗ[F] czT V := LinearMap.inl _ _ _
/-- `V(−) ↪ T`.  @census none (helper; engine `E10`) -/
noncomputable def czIotaMinus : czVM V 0 →ₗ[F] czT V := LinearMap.inr _ _ _
/-- `T → V(+)`.  @census none (helper; engine `E10`) -/
noncomputable def czPiPlus : czT V →ₗ[F] czVM V 1 := LinearMap.fst _ _ _
/-- `T → V(−)`.  @census none (helper; engine `E10`) -/
noncomputable def czPiMinus : czT V →ₗ[F] czVM V 0 := LinearMap.snd _ _ _

theorem czIotaPlus_inj : Function.Injective (czIotaPlus V) :=
  fun _ _ h => congrArg Prod.fst h
theorem czIotaMinus_inj : Function.Injective (czIotaMinus V) :=
  fun _ _ h => congrArg Prod.snd h

/-- `M_n` as a subspace of `T`: `V(+)` for `n ≥ 1`, `V(−)` for `n ≤ -1`, and `0` off the parity
class — so the central character holds by construction.  @census none (helper; engine `E10`) -/
noncomputable def czRegion (n : ℤ) : Submodule F (czT V) :=
  if (n + 1) % 2 ≠ 0 then ⊥
  else if (1 : ℤ) ≤ n then LinearMap.range (czIotaPlus V)
  else LinearMap.range (czIotaMinus V)

/-- The fibre of the graded carrier at `n`.  @census none (helper; engine `E10`) -/
abbrev czFib (n : ℤ) : Type := ↥(czRegion V n)

/-- **The carrier of the constructed module**, `M = ⨁_{n ∈ ℤ} M_n`.
@census none (helper; engine `E10`) -/
abbrev czCarrier : Type := DirectSum ℤ (czFib V)

/-- `M_n`, as a subspace of `M`.  @census none (helper; engine `E10`) -/
noncomputable def czComp (n : ℤ) : Submodule F (czCarrier V) :=
  LinearMap.range (DirectSum.lof F ℤ (czFib V) n)

theorem czRegion_eq_bot {n : ℤ} (hn : (n + 1) % 2 ≠ 0) : czRegion V n = ⊥ := by
  rw [czRegion, if_pos hn]

theorem czRegion_plus {n : ℤ} (hn : (n + 1) % 2 = 0) (h1 : (1 : ℤ) ≤ n) :
    czRegion V n = LinearMap.range (czIotaPlus V) := by
  rw [czRegion, if_neg (by simpa using hn), if_pos h1]

theorem czRegion_minus {n : ℤ} (hn : (n + 1) % 2 = 0) (h1 : n ≤ -1) :
    czRegion V n = LinearMap.range (czIotaMinus V) := by
  rw [czRegion, if_neg (by simpa using hn), if_neg (by omega : ¬((1 : ℤ) ≤ n))]

/-- Off the parity class the component is `⊥`.  @census none (helper; engine `E10`) -/
theorem czRegion_bot_apply {n : ℤ} (hn : (n + 1) % 2 ≠ 0) {x : czT V}
    (hx : x ∈ czRegion V n) : x = 0 := by
  rw [czRegion_eq_bot V hn, Submodule.mem_bot] at hx
  exact hx

/-- **`M = ⨁_n M_n`**.  @census none (helper; engine `E10`) -/
theorem czComp_isInternal : DirectSum.IsInternal (czComp V) :=
  isInternal_range_lof F ℤ (czFib V)

/-- **The central character, by construction**.  @census none (helper; engine `E10`) -/
theorem czComp_eq_bot {n : ℤ} (hn : (n + 1) % 2 ≠ 0) : czComp V n = ⊥ := by
  have hs : Subsingleton (czFib V n) := by
    show Subsingleton ↥(czRegion V n)
    rw [czRegion_eq_bot V hn]
    infer_instance
  rw [czComp, LinearMap.range_eq_bot]
  refine LinearMap.ext fun x => ?_
  rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]

/-- `M_n ≃` its fibre.  @census none (helper; engine `E10`) -/
noncomputable def czCompEquiv (n : ℤ) :
    czComp V n ≃ₗ[F] czFib V n :=
  (LinearEquiv.ofInjective (DirectSum.lof F ℤ (czFib V) n)
    (lof_injective F ℤ (czFib V) n)).symm

/-- `M_n ≃ V(+)` for `n ≥ 1`.  @census none (helper; engine `E10`) -/
noncomputable def czIsoPlus {n : ℤ} (hn : (n + 1) % 2 = 0) (h1 : (1 : ℤ) ≤ n) :
    czComp V n ≃ₗ[F] czVM V 1 :=
  (czCompEquiv V n).trans
    ((LinearEquiv.ofEq _ _ (czRegion_plus V hn h1)).trans
      (LinearEquiv.ofInjective (czIotaPlus V) (czIotaPlus_inj V)).symm)

/-- `M_n ≃ V(−)` for `n ≤ -1`.  @census none (helper; engine `E10`) -/
noncomputable def czIsoMinus {n : ℤ} (hn : (n + 1) % 2 = 0) (h1 : n ≤ -1) :
    czComp V n ≃ₗ[F] czVM V 0 :=
  (czCompEquiv V n).trans
    ((LinearEquiv.ofEq _ _ (czRegion_minus V hn h1)).trans
      (LinearEquiv.ofInjective (czIotaMinus V) (czIotaMinus_inj V)).symm)

/-- **Admissibility of the constructed module**: every component is finite-dimensional.
@census none (helper; engine `E10`) -/
theorem czComp_finiteDimensional (n : ℤ) :
    FiniteDimensional F ↥(czComp V n) := by
  by_cases hn : (n + 1) % 2 = 0
  · by_cases h1 : (1 : ℤ) ≤ n
    · exact LinearEquiv.finiteDimensional (czIsoPlus V hn h1).symm
    · exact LinearEquiv.finiteDimensional (czIsoMinus V hn (by omega)).symm
  · rw [czComp_eq_bot V hn]; infer_instance

/-! #### The operators, in the ambient `T`

`X` is the identity on the `+` chain and `¼(φ_- − (n+1)²·𝟏)` on the `−` chain; `Y` is the identity
on the `−` chain and `¼(φ_+ − (n−1)²·𝟏)` on the `+` chain; the two walls are the two edges of the
cyclic quiver.  Each is attached to the **source** degree, as in `E2`. -/

/-- `X : M_n → M_{n+2}`, in the ambient.  @census none (helper; engine `E10`)
@clauses   RQ2-5.13-S-C5b -/
noncomputable def czXAmb (n : ℤ) : czT V →ₗ[F] czT V :=
  if (1 : ℤ) ≤ n then (czIotaPlus V).comp (czPiPlus V)
  else if n ≤ -3 then
    (czIotaMinus V).comp
      ((((4 : F)⁻¹) • (czPhiMinus V
        - (((n + 1 : ℤ) : F) ^ 2) • 1)).comp (czPiMinus V))
  else if n = -1 then
    (czIotaPlus V).comp ((czEdgeA V).comp (czPiMinus V))
  else 0

/-- `Y : M_n → M_{n-2}`, in the ambient.  @census none (helper; engine `E10`) -/
noncomputable def czYAmb (n : ℤ) : czT V →ₗ[F] czT V :=
  if (3 : ℤ) ≤ n then
    (czIotaPlus V).comp
      ((((4 : F)⁻¹) • (czPhiPlus V
        - (((n - 1 : ℤ) : F) ^ 2) • 1)).comp (czPiPlus V))
  else if n ≤ -1 then (czIotaMinus V).comp (czPiMinus V)
  else if n = 1 then
    (czIotaMinus V).comp ((czEdgeB V).comp (czPiPlus V))
  else 0

theorem czXAmb_up {n : ℤ} (h : (1 : ℤ) ≤ n) (a : czVM V 1) :
    czXAmb V n (czIotaPlus V a) = czIotaPlus V a := by
  rw [czXAmb, if_pos h]; rfl

theorem czXAmb_dn {n : ℤ} (h1 : ¬((1 : ℤ) ≤ n)) (h : n ≤ -3) (a : czVM V 0) :
    czXAmb V n (czIotaMinus V a)
      = czIotaMinus V (((4 : F)⁻¹) • ((czPhiMinus V
          - (((n + 1 : ℤ) : F) ^ 2) • 1) a)) := by
  rw [czXAmb, if_neg h1, if_pos h]; rfl

theorem czXAmb_wall {n : ℤ} (h1 : ¬((1 : ℤ) ≤ n)) (h2 : ¬(n ≤ -3)) (h : n = -1)
    (a : czVM V 0) :
    czXAmb V n (czIotaMinus V a) = czIotaPlus V (czEdgeA V a) := by
  rw [czXAmb, if_neg h1, if_neg h2, if_pos h]; rfl

theorem czYAmb_up {n : ℤ} (h : (3 : ℤ) ≤ n) (a : czVM V 1) :
    czYAmb V n (czIotaPlus V a)
      = czIotaPlus V (((4 : F)⁻¹) • ((czPhiPlus V
          - (((n - 1 : ℤ) : F) ^ 2) • 1) a)) := by
  rw [czYAmb, if_pos h]; rfl

theorem czYAmb_dn {n : ℤ} (h1 : ¬((3 : ℤ) ≤ n)) (h : n ≤ -1) (a : czVM V 0) :
    czYAmb V n (czIotaMinus V a) = czIotaMinus V a := by
  rw [czYAmb, if_neg h1, if_pos h]; rfl

theorem czYAmb_wall {n : ℤ} (h1 : ¬((3 : ℤ) ≤ n)) (h2 : ¬(n ≤ -1)) (h : n = 1)
    (a : czVM V 1) :
    czYAmb V n (czIotaPlus V a) = czIotaMinus V (czEdgeB V a) := by
  rw [czYAmb, if_neg h1, if_neg h2, if_pos h]; rfl

/-- `X` carries `M_n` into `M_{n+2}`.  @census none (helper; engine `E10`) -/
theorem czXAmb_mem (n : ℤ) (x : czT V) (hx : x ∈ czRegion V n) :
    czXAmb V n x ∈ czRegion V (n + 2) := by
  by_cases hpar : (n + 1) % 2 = 0
  · have hpar2 : (n + 2 + 1) % 2 = 0 := by omega
    by_cases h1 : (1 : ℤ) ≤ n
    · rw [czXAmb, if_pos h1, czRegion_plus V hpar2 (by omega)]
      exact ⟨_, rfl⟩
    · by_cases h2 : n ≤ -3
      · rw [czXAmb, if_neg h1, if_pos h2, czRegion_minus V hpar2 (by omega)]
        exact ⟨_, rfl⟩
      · by_cases h3 : n = -1
        · rw [czXAmb, if_neg h1, if_neg h2, if_pos h3, czRegion_plus V hpar2 (by omega)]
          exact ⟨_, rfl⟩
        · exact absurd hpar (by omega)
  · rw [czRegion_bot_apply V hpar hx, map_zero]
    exact Submodule.zero_mem _

/-- `Y` carries `M_n` into `M_{n-2}`.  @census none (helper; engine `E10`) -/
theorem czYAmb_mem (n : ℤ) (x : czT V) (hx : x ∈ czRegion V n) :
    czYAmb V n x ∈ czRegion V (n - 2) := by
  by_cases hpar : (n + 1) % 2 = 0
  · have hpar2 : (n - 2 + 1) % 2 = 0 := by omega
    by_cases h1 : (3 : ℤ) ≤ n
    · rw [czYAmb, if_pos h1, czRegion_plus V hpar2 (by omega)]
      exact ⟨_, rfl⟩
    · by_cases h2 : n ≤ -1
      · rw [czYAmb, if_neg h1, if_pos h2, czRegion_minus V hpar2 (by omega)]
        exact ⟨_, rfl⟩
      · by_cases h3 : n = 1
        · rw [czYAmb, if_neg h1, if_neg h2, if_pos h3, czRegion_minus V hpar2 (by omega)]
          exact ⟨_, rfl⟩
        · exact absurd hpar (by omega)
  · rw [czRegion_bot_apply V hpar hx, map_zero]
    exact Submodule.zero_mem _

/-! #### The three arithmetic identities the operators need -/

/-- @census none (helper; engine `E10`) -/
theorem cz_quarter_diff {W : Type} [AddCommGroup W] [Module F W]
    (f : Module.End F W) (c₁ c₂ : F) (a : W) :
    ((4 : F)⁻¹) • ((f - c₁ • (1 : Module.End F W)) a)
      - ((4 : F)⁻¹) • ((f - c₂ • (1 : Module.End F W)) a)
      = (((4 : F)⁻¹) * (c₂ - c₁)) • a := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, smul_sub, smul_smul,
    mul_sub, sub_smul]
  abel

/-- @census none (helper; engine `E10`) -/
theorem cz_scalar_n (n : ℤ) :
    ((4 : F)⁻¹) * ((((n + 1 : ℤ) : F) ^ 2) - (((n - 1 : ℤ) : F) ^ 2))
      = ((n : ℤ) : F) := by
  push_cast
  field_simp
  ring

/-- @census none (helper; engine `E10`) -/
theorem cz_quarter_four_plus (a : czVM V 1) (c : F) (hc : c = 4) :
    ((4 : F)⁻¹) • ((czPhiPlus V
        - c • (1 : Module.End F (czVM V 1))) a)
      = czNPlus V a - a := by
  subst hc
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, czPhiPlus]
  rw [← smul_sub, smul_smul, inv_mul_cancel₀ (by norm_num : (4 : F) ≠ 0), one_smul]

/-- @census none (helper; engine `E10`) -/
theorem cz_quarter_four_minus (a : czVM V 0) (c : F) (hc : c = 4) :
    ((4 : F)⁻¹) • ((czPhiMinus V
        - c • (1 : Module.End F (czVM V 0))) a)
      = czNMinus V a - a := by
  subst hc
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, czPhiMinus]
  rw [← smul_sub, smul_smul, inv_mul_cancel₀ (by norm_num : (4 : F) ≠ 0), one_smul]

/-- @census none (helper; engine `E10`) -/
theorem cz_cas_calc {W : Type} [AddCommGroup W] [Module F W]
    (f : Module.End F W) (c c' : F) (hcc : c' = c) (a : W) :
    c • a
        + (4 : F) • (((4 : F)⁻¹)
            • ((f - c' • (1 : Module.End F W)) a))
      = f a := by
  subst hcc
  rw [smul_smul, mul_inv_cancel₀ (by norm_num : (4 : F) ≠ 0), one_smul]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
  abel

/-- **`[X,Y] = H` on `M_n`, read in the ambient `T`.**  Four cases: the two chain interiors, where
the two `¼(φ − j²)` factors differ by `¼((n+1)² − (n−1)²) = n`, and the two walls, where the
composite of the two edges is the loop `n_±` and the arithmetic collapses to `±1`.
@census none (helper; engine `E10`) -/
theorem czLie_ambient (n : ℤ) (x : czT V) (hx : x ∈ czRegion V n) :
    czXAmb V (n - 2) (czYAmb V n x)
      - czYAmb V (n + 2) (czXAmb V n x) = ((n : ℤ) : F) • x := by
  by_cases hpar : (n + 1) % 2 = 0
  case neg =>
    rw [czRegion_bot_apply V hpar hx, map_zero, map_zero, map_zero, map_zero, sub_zero,
      smul_zero]
  rcases (show (3 : ℤ) ≤ n ∨ n = 1 ∨ n = -1 ∨ n ≤ -3 by omega) with h | h | h | h
  · -- the `+` chain interior
    rw [czRegion_plus V hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [czYAmb_up V h a, czXAmb_up V (by omega) _,
      czXAmb_up V (by omega) a, czYAmb_up V (by omega) a,
      show n + 2 - 1 = n + 1 from by ring, ← map_sub, cz_quarter_diff, cz_scalar_n, map_smul]
  · -- the `Y`-wall `n = 1`
    subst h
    rw [czRegion_plus V hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [czYAmb_wall V (by omega) (by omega) rfl a,
      czXAmb_wall V (by omega) (by omega) (by ring) _,
      czXAmb_up V (by omega) a, czYAmb_up V (by omega) a,
      cz_quarter_four_plus V a _ (by norm_num), ← map_sub]
    have hkey : czEdgeA V (czEdgeB V a) - (czNPlus V a - a) = a := by
      show czNPlus V a - (czNPlus V a - a) = a
      abel
    rw [hkey]
    show _ = ((1 : ℤ) : F) • czIotaPlus V a
    rw [Int.cast_one, one_smul]
  · -- the `X`-wall `n = -1`
    subst h
    rw [czRegion_minus V hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [czYAmb_dn V (by omega) (by omega) a,
      czXAmb_dn V (by omega) (by omega) a,
      czXAmb_wall V (by omega) (by omega) rfl a,
      czYAmb_wall V (by omega) (by omega) (by ring) _,
      cz_quarter_four_minus V a _ (by norm_num), ← map_sub]
    have hkey : czNMinus V a - a - czEdgeB V (czEdgeA V a) = -a := by
      show czNMinus V a - a - czNMinus V a = -a
      abel
    rw [hkey]
    show _ = ((-1 : ℤ) : F) • czIotaMinus V a
    rw [map_neg, Int.cast_neg, Int.cast_one, neg_smul, one_smul]
  · -- the `−` chain interior
    rw [czRegion_minus V hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [czYAmb_dn V (by omega) (by omega) a,
      czXAmb_dn V (by omega) (by omega) a,
      czXAmb_dn V (by omega) (by omega) a,
      czYAmb_dn V (by omega) (by omega) _,
      show n - 2 + 1 = n - 1 from by ring, ← map_sub, cz_quarter_diff, cz_scalar_n, map_smul]

/-! #### The graded `𝔰𝔩₂`-module -/

/-- `X : M_n → M_{n+2}`, as a map of fibres.  @census none (helper; engine `E10`) -/
noncomputable def czXComp (n : ℤ) : czFib V n →ₗ[F] czFib V (n + 2) :=
  (czXAmb V n).restrict (czXAmb_mem V n)

/-- `Y : M_n → M_{n-2}`, as a map of fibres.  @census none (helper; engine `E10`) -/
noncomputable def czYComp (n : ℤ) : czFib V n →ₗ[F] czFib V (n - 2) :=
  (czYAmb V n).restrict (czYAmb_mem V n)

@[simp] theorem czXComp_val (n : ℤ) (a : czFib V n) :
    ((czXComp V n a : czFib V (n + 2)) : czT V)
      = czXAmb V n (a : czT V) := rfl
@[simp] theorem czYComp_val (n : ℤ) (a : czFib V n) :
    ((czYComp V n a : czFib V (n - 2)) : czT V)
      = czYAmb V n (a : czT V) := rfl

/-- `X` on `M = ⨁_n M_n`.  @census none (helper; engine `E10`) -/
noncomputable def czX : czCarrier V →ₗ[F] czCarrier V :=
  DirectSum.toModule F ℤ _ (fun n =>
    (DirectSum.lof F ℤ (czFib V) (n + 2)).comp (czXComp V n))

/-- `Y` on `M`.  @census none (helper; engine `E10`) -/
noncomputable def czY : czCarrier V →ₗ[F] czCarrier V :=
  DirectSum.toModule F ℤ _ (fun n =>
    (DirectSum.lof F ℤ (czFib V) (n - 2)).comp (czYComp V n))

/-- `H` on `M`: the scalar `n` on `M_n`.  @census none (helper; engine `E10`) -/
noncomputable def czH : czCarrier V →ₗ[F] czCarrier V :=
  DirectSum.toModule F ℤ _ (fun n =>
    (DirectSum.lof F ℤ (czFib V) n).comp
      ((n : F) • (LinearMap.id : czFib V n →ₗ[F] czFib V n)))

@[simp] theorem czX_lof (n : ℤ) (a : czFib V n) :
    czX V (DirectSum.lof F ℤ (czFib V) n a)
      = DirectSum.lof F ℤ (czFib V) (n + 2) (czXComp V n a) := by
  rw [czX, DirectSum.toModule_lof]; rfl

@[simp] theorem czY_lof (n : ℤ) (a : czFib V n) :
    czY V (DirectSum.lof F ℤ (czFib V) n a)
      = DirectSum.lof F ℤ (czFib V) (n - 2) (czYComp V n a) := by
  rw [czY, DirectSum.toModule_lof]; rfl

@[simp] theorem czH_lof (n : ℤ) (a : czFib V n) :
    czH V (DirectSum.lof F ℤ (czFib V) n a)
      = (n : F) • DirectSum.lof F ℤ (czFib V) n a := by
  rw [czH, DirectSum.toModule_lof]
  show DirectSum.lof F ℤ (czFib V) n ((n : F) • a) = _
  rw [map_smul]

theorem czX_mem (n : ℤ) (v : czCarrier V) (hv : v ∈ czComp V n) :
    czX V v ∈ czComp V (n + 2) := by
  obtain ⟨a, rfl⟩ := hv
  rw [czX_lof]
  exact ⟨_, rfl⟩

theorem czY_mem (n : ℤ) (v : czCarrier V) (hv : v ∈ czComp V n) :
    czY V v ∈ czComp V (n - 2) := by
  obtain ⟨a, rfl⟩ := hv
  rw [czY_lof]
  exact ⟨_, rfl⟩

theorem czH_apply (n : ℤ) (v : czCarrier V) (hv : v ∈ czComp V n) :
    czH V v = (n : F) • v := by
  obtain ⟨a, rfl⟩ := hv
  rw [czH_lof]

/-- The one degree transport of the layer.  @census none (helper; engine `E10`) -/
theorem czLof_congr {i j : ℤ} (h : i = j) (a : czFib V i) (b : czFib V j)
    (hab : (a : czT V) = (b : czT V)) :
    DirectSum.lof F ℤ (czFib V) i a
      = DirectSum.lof F ℤ (czFib V) j b := by
  subst h; exact congrArg _ (Subtype.ext hab)

/-- `[X,Y] = H` on a summand.  @census none (helper; engine `E10`) -/
theorem czLie_lof (n : ℤ) (a : czFib V n) :
    czX V (czY V (DirectSum.lof F ℤ (czFib V) n a))
      - czY V (czX V (DirectSum.lof F ℤ (czFib V) n a))
      = czH V (DirectSum.lof F ℤ (czFib V) n a) := by
  have hm1 : czXAmb V (n - 2) (czYAmb V n (a : czT V))
      ∈ czRegion V n := by
    have h := czXAmb_mem V (n - 2) _ (czYAmb_mem V n _ a.2)
    rwa [show n - 2 + 2 = n from by ring] at h
  have hm2 : czYAmb V (n + 2) (czXAmb V n (a : czT V))
      ∈ czRegion V n := by
    have h := czYAmb_mem V (n + 2) _ (czXAmb_mem V n _ a.2)
    rwa [show n + 2 - 2 = n from by ring] at h
  rw [czY_lof, czX_lof, czX_lof, czY_lof, czH_lof,
    czLof_congr V (show n - 2 + 2 = n from by ring) _ (⟨_, hm1⟩ : czFib V n) rfl,
    czLof_congr V (show n + 2 - 2 = n from by ring) _ (⟨_, hm2⟩ : czFib V n) rfl,
    ← map_sub, ← map_smul]
  exact congrArg _ (Subtype.ext (czLie_ambient V n _ a.2))

theorem czLie_H_X :
    czH V * czX V - czX V * czH V = (2 : F) • czX V := by
  refine DirectSum.linearMap_ext _ (fun n => LinearMap.ext fun a => ?_)
  show czH V (czX V (DirectSum.lof F ℤ (czFib V) n a))
      - czX V (czH V (DirectSum.lof F ℤ (czFib V) n a)) = _
  rw [czX_lof, czH_lof, czH_lof, map_smul, czX_lof, ← sub_smul]
  show _ = (2 : F) • czX V (DirectSum.lof F ℤ (czFib V) n a)
  rw [czX_lof]
  congr 1
  push_cast
  ring

theorem czLie_H_Y :
    czH V * czY V - czY V * czH V
      = -((2 : F) • czY V) := by
  refine DirectSum.linearMap_ext _ (fun n => LinearMap.ext fun a => ?_)
  show czH V (czY V (DirectSum.lof F ℤ (czFib V) n a))
      - czY V (czH V (DirectSum.lof F ℤ (czFib V) n a)) = _
  rw [czY_lof, czH_lof, czH_lof, map_smul, czY_lof, ← sub_smul]
  show _ = -((2 : F) • czY V (DirectSum.lof F ℤ (czFib V) n a))
  rw [czY_lof, ← neg_smul]
  congr 1
  push_cast
  ring

theorem czLie_X_Y :
    czX V * czY V - czY V * czX V = czH V := by
  refine DirectSum.linearMap_ext _ (fun n => LinearMap.ext fun a => ?_)
  exact czLie_lof V n a

/-- **The graded `𝔰𝔩₂`-module of the `ℓ = 0` construction.**  @census none (helper; engine `E10`) -/
noncomputable def czWeight : WeightData F (czCarrier V) where
  comp := czComp V
  isInternal := czComp_isInternal V
  H := czH V
  X := czX V
  Y := czY V
  H_apply := czH_apply V
  X_mem := czX_mem V
  Y_mem := czY_mem V
  lie_H_X := czLie_H_X V
  lie_H_Y := czLie_H_Y V
  lie_X_Y := czLie_X_Y V

theorem czWeight_H : (czWeight V).H = czH V := rfl
theorem czWeight_X : (czWeight V).X = czX V := rfl
theorem czWeight_Y : (czWeight V).Y = czY V := rfl

/-! #### The generalized infinitesimal character: `λ = 0` and `C = φ_±` -/

/-- The Casimir in the ambient: `φ_+` on the `+` chain, `φ_-` on the `−` chain.
@census none (helper; engine `E10`) -/
noncomputable def czCasAmb (n : ℤ) : czT V →ₗ[F] czT V :=
  if (1 : ℤ) ≤ n then (czIotaPlus V).comp ((czPhiPlus V).comp (czPiPlus V))
  else (czIotaMinus V).comp ((czPhiMinus V).comp (czPiMinus V))

theorem czCasAmb_mem (n : ℤ) (x : czT V) (hx : x ∈ czRegion V n) :
    czCasAmb V n x ∈ czRegion V n := by
  by_cases hpar : (n + 1) % 2 = 0
  · by_cases h1 : (1 : ℤ) ≤ n
    · rw [czCasAmb, if_pos h1, czRegion_plus V hpar h1]
      exact ⟨_, rfl⟩
    · rw [czCasAmb, if_neg h1, czRegion_minus V hpar (by omega)]
      exact ⟨_, rfl⟩
  · rw [czRegion_bot_apply V hpar hx, map_zero]
    exact Submodule.zero_mem _

/-- **`C = (n−1)²·𝟏 + 4XY` collapses to `φ_±` on every component** — the `ℓ = 0` uniformity that
makes the generalized infinitesimal character `λ = 0` free.  @census none (helper; engine `E10`) -/
theorem czCasimir_ambient (n : ℤ) (x : czT V) (hx : x ∈ czRegion V n) :
    ((((n - 1 : ℤ)) : F) ^ 2) • x
        + (4 : F) • czXAmb V (n - 2) (czYAmb V n x)
      = czCasAmb V n x := by
  by_cases hpar : (n + 1) % 2 = 0
  case neg =>
    rw [czRegion_bot_apply V hpar hx, map_zero, map_zero, map_zero, smul_zero, smul_zero,
      add_zero]
  rcases (show (3 : ℤ) ≤ n ∨ n = 1 ∨ n = -1 ∨ n ≤ -3 by omega) with h | h | h | h
  · rw [czRegion_plus V hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [czYAmb_up V h a, czXAmb_up V (by omega) _, czCasAmb, if_pos (by omega),
      ← map_smul, ← map_smul, ← map_add]
    exact congrArg (czIotaPlus V) (cz_cas_calc _ _ _ rfl a)
  · subst h
    rw [czRegion_plus V hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [czYAmb_wall V (by omega) (by omega) rfl a,
      czXAmb_wall V (by omega) (by omega) (by ring) _, czCasAmb, if_pos (by omega),
      ← map_smul, ← map_smul, ← map_add]
    refine congrArg (czIotaPlus V) ?_
    show ((((1 : ℤ) - 1 : ℤ)) : F) ^ 2 • a
        + (4 : F) • czEdgeA V (czEdgeB V a) = czPhiPlus V a
    rw [show ((((1 : ℤ) - 1 : ℤ)) : F) ^ 2 = 0 by norm_num, zero_smul, zero_add]
    rfl
  · subst h
    rw [czRegion_minus V hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [czYAmb_dn V (by omega) (by omega) a, czXAmb_dn V (by omega) (by omega) a,
      czCasAmb, if_neg (by omega), ← map_smul, ← map_smul, ← map_add]
    exact congrArg (czIotaMinus V) (cz_cas_calc _ _ _ (by norm_num) a)
  · rw [czRegion_minus V hpar (by omega)] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [czYAmb_dn V (by omega) (by omega) a, czXAmb_dn V (by omega) (by omega) a,
      czCasAmb, if_neg (by omega), ← map_smul, ← map_smul, ← map_add]
    exact congrArg (czIotaMinus V) (cz_cas_calc _ _ _ (by push_cast; ring) a)

/-- The Casimir as an endomorphism of the fibre.  @census none (helper; engine `E10`) -/
noncomputable def czCasComp (n : ℤ) : czFib V n →ₗ[F] czFib V n :=
  (czCasAmb V n).restrict (czCasAmb_mem V n)

set_option maxHeartbeats 1000000 in
/-- The Casimir acts summand by summand.  @census none (helper; engine `E10`) -/
theorem czCasimir_lof (n : ℤ) (a : czFib V n) :
    (czWeight V).casimir (DirectSum.lof F ℤ (czFib V) n a)
      = DirectSum.lof F ℤ (czFib V) n (czCasComp V n a) := by
  have hm : czXAmb V (n - 2) (czYAmb V n (a : czT V))
      ∈ czRegion V n := by
    have h := czXAmb_mem V (n - 2) _ (czYAmb_mem V n _ a.2)
    rwa [show n - 2 + 2 = n from by ring] at h
  rw [WeightData.casimir_apply, czWeight_H, czWeight_X, czWeight_Y, czH_lof, map_smul, czH_lof,
    czY_lof, czX_lof,
    czLof_congr V (show n - 2 + 2 = n from by ring) _ (⟨_, hm⟩ : czFib V n) rfl,
    smul_smul, ← map_smul, smul_smul, ← map_smul, ← map_smul, ← map_sub, ← map_add, ← map_add]
  refine congrArg _ (Subtype.ext ?_)
  show ((n : F) * (n : F)) • (a : czT V)
      - ((2 : F) * (n : F)) • (a : czT V)
      + (4 : F) • czXAmb V (n - 2) (czYAmb V n (a : czT V))
      + (a : czT V) = czCasAmb V n (a : czT V)
  rw [← czCasimir_ambient V n _ a.2,
    show ((((n - 1 : ℤ)) : F) ^ 2)
      = (n : F) * (n : F) - (2 : F) * (n : F) + 1 by
      push_cast; ring,
    add_smul, sub_smul, one_smul]
  abel

/-- @census none (helper; engine `E10`) -/
theorem czCasimir_pow_lof (m : ℕ) (n : ℤ) (a : czFib V n) :
    (((czWeight V).casimir) ^ m) (DirectSum.lof F ℤ (czFib V) n a)
      = DirectSum.lof F ℤ (czFib V) n (((czCasComp V n) ^ m) a) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, czCasimir_lof, pow_succ', Module.End.mul_apply]

/-- @census none (helper; engine `E10`) -/
theorem czCasComp_val (m : ℕ) (n : ℤ) (a : czFib V n) :
    ((((czCasComp V n) ^ m) a : czFib V n) : czT V)
      = ((czCasAmb V n) ^ m) (a : czT V) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      rfl

/-- A conjugate `i ∘ f ∘ p` with `p ∘ i = 𝟏` has `(i ∘ f ∘ p)^{m+1} = i ∘ f^{m+1} ∘ p`.
@census none (helper; engine `E10`) -/
theorem cz_iota_pow {W : Type} [AddCommGroup W] [Module F W]
    (i : W →ₗ[F] czT V) (p : czT V →ₗ[F] W)
    (hpi : ∀ w, p (i w) = w) (f : Module.End F W) (m : ℕ) (x : czT V) :
    ((i.comp (f.comp p)) ^ (m + 1)) x = i ((f ^ (m + 1)) (p x)) := by
  induction m with
  | zero => rw [pow_one, pow_one]; rfl
  | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      show i (f (p (i ((f ^ (m + 1)) (p x))))) = _
      rw [hpi]
      congr 1
      conv_rhs => rw [pow_succ', Module.End.mul_apply]

/-- @census none (helper; engine `E10`) -/
theorem czCasAmb_pow_eq_zero (m : ℕ) (hp : (czPhiPlus V) ^ (m + 1) = 0)
    (hm : (czPhiMinus V) ^ (m + 1) = 0) (n : ℤ) :
    ((czCasAmb V n) ^ (m + 1)) = 0 := by
  refine LinearMap.ext fun x => ?_
  by_cases h1 : (1 : ℤ) ≤ n
  · rw [czCasAmb, if_pos h1,
      cz_iota_pow V (czIotaPlus V) (czPiPlus V) (fun _ => rfl) _ m x, hp]
    simp
  · rw [czCasAmb, if_neg h1,
      cz_iota_pow V (czIotaMinus V) (czPiMinus V) (fun _ => rfl) _ m x, hm]
    simp

/-- **The generalized infinitesimal character `λ = 0`.**  At `ℓ = 0` the Casimir *is* the
nilpotent operator `φ_±`, so this is the nilpotency of `V` and nothing else.
@census none (helper; engine `E10`) -/
theorem czGIC : HasGeneralizedInfinitesimalCharacter (czWeight V) 0 := by
  obtain ⟨mp, hmp⟩ := czPhiPlus_isNilpotent V
  obtain ⟨mm, hmm⟩ := czPhiMinus_isNilpotent V
  have hp : (czPhiPlus V) ^ (mp + mm + 1) = 0 := pow_eq_zero_of_le (by omega) hmp
  have hm : (czPhiMinus V) ^ (mp + mm + 1) = 0 := pow_eq_zero_of_le (by omega) hmm
  refine ⟨mp + mm + 1, ?_⟩
  rw [show ((algebraMap ℚ F) ((((0 : ℕ)) : ℚ) ^ 2)) = 0 by norm_num, zero_smul, sub_zero]
  refine LinearMap.ext fun v => ?_
  induction v using DirectSum.induction_on with
  | zero => simp
  | of n a =>
      rw [← DirectSum.lof_eq_of (R := F), czCasimir_pow_lof,
        show ((czCasComp V n) ^ (mp + mm + 1)) a = 0 from
          Subtype.ext (by
            rw [czCasComp_val, czCasAmb_pow_eq_zero V (mp + mm) hp hm n]
            simp),
        map_zero, LinearMap.zero_apply]
  | add x y hx hy => rw [map_add, hx, hy]; simp

/-! #### Finite generation -/

/-- `X : M_n → M_{n+2}` is surjective for `n ≥ 1`: it is the identity of `V(+)` there.
@census none (helper; engine `E10`) -/
theorem czXComp_surjective_up {n : ℤ} (hn : (n + 1) % 2 = 0) (h : (1 : ℤ) ≤ n)
    (b : czFib V (n + 2)) : ∃ a : czFib V n, czXComp V n a = b := by
  have hb : (b : czT V) ∈ LinearMap.range (czIotaPlus V) :=
    le_of_eq (czRegion_plus V (show ((n + 2) + 1) % 2 = 0 by omega) (by omega)) b.2
  obtain ⟨c, hc⟩ := hb
  have hmem : (czIotaPlus V c) ∈ czRegion V n := by
    rw [czRegion_plus V hn h]; exact ⟨c, rfl⟩
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [czXComp_val]
  show czXAmb V n (czIotaPlus V c) = (b : czT V)
  rw [czXAmb_up V h c, hc]

/-- `Y : M_n → M_{n-2}` is surjective for `n ≤ -1`.  @census none (helper; engine `E10`) -/
theorem czYComp_surjective_dn {n : ℤ} (hn : (n + 1) % 2 = 0) (h : n ≤ -1)
    (b : czFib V (n - 2)) : ∃ a : czFib V n, czYComp V n a = b := by
  have hb : (b : czT V) ∈ LinearMap.range (czIotaMinus V) :=
    le_of_eq (czRegion_minus V (show ((n - 2) + 1) % 2 = 0 by omega) (by omega)) b.2
  obtain ⟨c, hc⟩ := hb
  have hmem : (czIotaMinus V c) ∈ czRegion V n := by
    rw [czRegion_minus V hn h]; exact ⟨c, rfl⟩
  refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [czYComp_val]
  show czYAmb V n (czIotaMinus V c) = (b : czT V)
  rw [czYAmb_dn V (by omega) h c, hc]

/-- The generating window `M_{-1} ⊕ M_0 ⊕ M_1`.  @census none (helper; engine `E10`) -/
noncomputable def czWindow : Submodule F (czCarrier V) :=
  ⨆ i : (Finset.Icc (-1 : ℤ) 1 : Finset ℤ), czComp V (i : ℤ)

/-- @census none (helper; engine `E10`) -/
theorem czWindow_finiteDimensional : FiniteDimensional F ↥(czWindow V) := by
  haveI : ∀ i : (Finset.Icc (-1 : ℤ) 1 : Finset ℤ),
      FiniteDimensional F ↥(czComp V (i : ℤ)) :=
    fun i => czComp_finiteDimensional V (i : ℤ)
  exact Submodule.finiteDimensional_iSup _

/-- @census none (helper; engine `E10`) -/
theorem czComp_le_csWindow {n : ℤ} (h1 : (-1 : ℤ) ≤ n) (h2 : n ≤ 1) :
    czComp V n ≤ czWindow V :=
  le_iSup (fun i : (Finset.Icc (-1 : ℤ) 1 : Finset ℤ) => czComp V (i : ℤ))
    ⟨n, Finset.mem_Icc.2 ⟨h1, h2⟩⟩

/-- **Finite generation of the constructed module**: the window `M_{-1} ⊕ M_1` generates, because
`X` is onto up the `+` chain and `Y` is onto down the `−` chain.  @census none (helper; `E10`) -/
theorem czFG : (czWeight V).IsFG := by
  obtain ⟨S, hS⟩ : (czWindow V).FG := by
    haveI := czWindow_finiteDimensional V
    exact Module.Finite.iff_fg.1 inferInstance
  refine ⟨S, gkSpanGraded_eq_top _ fun N hSN hop _ => ?_⟩
  have hW : czWindow V ≤ N := by
    rw [← hS]; exact Submodule.span_le.2 hSN
  have hmid : ∀ n : ℤ, (-1 : ℤ) ≤ n → n ≤ 1 → czComp V n ≤ N :=
    fun n h1 h2 => (czComp_le_csWindow V h1 h2).trans hW
  have hup : ∀ k : ℕ, czComp V (1 + 2 * (k : ℤ)) ≤ N := by
    intro k
    induction k with
    | zero => simpa using hmid 1 (by omega) (by omega)
    | succ k ih =>
        have hstep : (1 : ℤ) + 2 * ((k : ℕ) + 1 : ℕ) = (1 + 2 * (k : ℤ)) + 2 := by push_cast; ring
        rw [hstep]
        rintro _ ⟨b, rfl⟩
        obtain ⟨a, ha⟩ := czXComp_surjective_up V (n := 1 + 2 * (k : ℤ))
          (by omega) (by omega) b
        have hx : czX V
            (DirectSum.lof F ℤ (czFib V) (1 + 2 * (k : ℤ)) a)
            = DirectSum.lof F ℤ (czFib V) ((1 + 2 * (k : ℤ)) + 2) b := by
          rw [czX_lof, ha]
        rw [← hx]
        exact hop.2.1 _ (ih ⟨a, rfl⟩)
  have hdn : ∀ k : ℕ, czComp V (-1 - 2 * (k : ℤ)) ≤ N := by
    intro k
    induction k with
    | zero => simpa using hmid (-1) (by omega) (by omega)
    | succ k ih =>
        have hstep : (-1 : ℤ) - 2 * ((k : ℕ) + 1 : ℕ) = (-1 - 2 * (k : ℤ)) - 2 := by
          push_cast; ring
        rw [hstep]
        rintro _ ⟨b, rfl⟩
        obtain ⟨a, ha⟩ := czYComp_surjective_dn V (n := -1 - 2 * (k : ℤ))
          (by omega) (by omega) b
        have hy : czY V
            (DirectSum.lof F ℤ (czFib V) (-1 - 2 * (k : ℤ)) a)
            = DirectSum.lof F ℤ (czFib V) ((-1 - 2 * (k : ℤ)) - 2) b := by
          rw [czY_lof, ha]
        rw [← hy]
        exact hop.2.2 _ (ih ⟨a, rfl⟩)
  have hcomp : ∀ n : ℤ, czComp V n ≤ N := by
    intro n
    by_cases hpar : (n + 1) % 2 = 0
    · by_cases hgt : (1 : ℤ) < n
      · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 1 + 2 * (k : ℤ) := ⟨((n - 1) / 2).toNat, by omega⟩
        rw [hk]; exact hup k
      · by_cases hlt : n < -1
        · obtain ⟨k, hk⟩ : ∃ k : ℕ, n = -1 - 2 * (k : ℤ) := ⟨((-1 - n) / 2).toNat, by omega⟩
          rw [hk]; exact hdn k
        · exact hmid n (by omega) (by omega)
    · rw [czComp_eq_bot V hpar]; exact bot_le
  rw [eq_top_iff]
  intro x _
  induction x using DirectSum.induction_on with
  | zero => exact N.zero_mem
  | of n a =>
      refine hcomp n ⟨a, ?_⟩
      rw [DirectSum.lof_eq_of]
  | add x y hx hy => exact N.add_mem (hx trivial) (hy trivial)


/-- **The object of `HC_0(𝔤,K)_{ℚ[√-1]}` that engine `E10` constructs from a split `V`** —
`csHCQObj`'s `ℚ[√-1]`-part, with no conjugation and no `ℚ`-form.
@census none (helper; engine `E10`) -/
noncomputable def czHCQiObj : HCFObj F 0 where
  carrier := czCarrier V
  weight := czWeight V
  gic := czGIC V
  admissible := czComp_finiteDimensional V
  centralCharacter := fun n hn => czComp_eq_bot V (by omega)
  fg := czFG V

/-! #### The comparison isomorphism `𝔼_{ℚ[√-1]}(M) ≅ V`, split

As for `csNatIsoFD`, the comparison map is the canonical injection of a summand; with the trivial
Galois action its `rational` field is a transport along `1 • v = v` (as `spNatHom`). -/

/-- The fibre injection `V(+) → M_1`.  @census none (helper; engine `E10`) -/
noncomputable def czFibPlus : czVM V 1 →ₗ[F] czFib V 1 :=
  LinearMap.codRestrict _ (czIotaPlus V) (fun c => by
    rw [czRegion_plus V (by decide) (by decide)]; exact ⟨c, rfl⟩)

/-- The fibre injection `V(−) → M_{-1}`.  @census none (helper; engine `E10`) -/
noncomputable def czFibMinus : czVM V 0 →ₗ[F] czFib V (-1) :=
  LinearMap.codRestrict _ (czIotaMinus V) (fun c => by
    rw [czRegion_minus V (by decide) (by decide)]; exact ⟨c, rfl⟩)

/-- **The comparison map `V(v) → M(v)`**, the canonical injection of the summand.
@census none (helper; engine `E10`) -/
noncomputable def czEmb : ∀ v : Fin 2,
    czVM V v →ₗ[F] V2i (czHCQiObj V) v
  | 0 => LinearMap.codRestrict _
      ((DirectSum.lof F ℤ (czFib V) (-1)).comp (czFibMinus V))
      (fun _ => ⟨_, rfl⟩)
  | 1 => LinearMap.codRestrict _
      ((DirectSum.lof F ℤ (czFib V) 1).comp (czFibPlus V))
      (fun _ => ⟨_, rfl⟩)

theorem czEmb_val_zero (c : czVM V 0) :
    ((czEmb V 0 c : V2i (czHCQiObj V) 0) : (czHCQiObj V).carrier)
      = DirectSum.lof F ℤ (czFib V) (-1) (czFibMinus V c) := rfl

theorem czEmb_val_one (c : czVM V 1) :
    ((czEmb V 1 c : V2i (czHCQiObj V) 1) : (czHCQiObj V).carrier)
      = DirectSum.lof F ℤ (czFib V) 1 (czFibPlus V c) := rfl

/-- The comparison map is bijective at both vertices.  @census none (helper; engine `E10`) -/
theorem czEmb_bijective : ∀ v : Fin 2, Function.Bijective (czEmb V v)
  | 0 => by
      constructor
      · intro c c' hcc
        have h1 : DirectSum.lof F ℤ (czFib V) (-1) (czFibMinus V c)
            = DirectSum.lof F ℤ (czFib V) (-1) (czFibMinus V c') :=
          (czEmb_val_zero V c).symm.trans
            ((congrArg Subtype.val hcc).trans (czEmb_val_zero V c'))
        exact czIotaMinus_inj V (congrArg Subtype.val
          (lof_injective F ℤ (czFib V) (-1) h1))
      · intro y
        obtain ⟨a, ha⟩ := y.2
        obtain ⟨c, hc⟩ : (a : czT V) ∈ LinearMap.range (czIotaMinus V) :=
          le_of_eq (czRegion_minus V (by decide) (by decide)) a.2
        refine ⟨c, Subtype.ext ?_⟩
        rw [czEmb_val_zero, ← ha]
        exact czLof_congr V rfl _ _ hc
  | 1 => by
      constructor
      · intro c c' hcc
        have h1 : DirectSum.lof F ℤ (czFib V) 1 (czFibPlus V c)
            = DirectSum.lof F ℤ (czFib V) 1 (czFibPlus V c') :=
          (czEmb_val_one V c).symm.trans
            ((congrArg Subtype.val hcc).trans (czEmb_val_one V c'))
        exact czIotaPlus_inj V (congrArg Subtype.val
          (lof_injective F ℤ (czFib V) 1 h1))
      · intro y
        obtain ⟨a, ha⟩ := y.2
        obtain ⟨c, hc⟩ : (a : czT V) ∈ LinearMap.range (czIotaPlus V) :=
          le_of_eq (czRegion_plus V (by decide) (by decide)) a.2
        refine ⟨c, Subtype.ext ?_⟩
        rw [czEmb_val_one, ← ha]
        exact czLof_congr V rfl _ _ hc

/-- The comparison map as a linear equivalence.  @census none (helper; engine `E10`)
@clauses   RQ2-5.13-S-C5c -/
noncomputable def czEmbEquiv (v : Fin 2) :
    czVM V v ≃ₗ[F] V2i (czHCQiObj V) v :=
  LinearEquiv.ofBijective (czEmb V v) (czEmb_bijective V v)

/-- The comparison map intertwines the two edges of the cyclic quiver with `X` and `Y`.
@census none (helper; engine `E10`) -/
theorem czEmb_edge : ∀ (e : Fin 2) (m : czVM V (RQuiver.cyclic.source e)),
    czEmb V (RQuiver.cyclic.target e) (V.obj.toRep.φEdge (edgeS e) m)
      = E_CycSplit_edge (czHCQiObj V) e (czEmb V (RQuiver.cyclic.source e) m)
  | 0, m => by
      refine Subtype.ext ?_
      show DirectSum.lof F ℤ (czFib V) 1 (czFibPlus V (czEdgeA V m))
          = czX V (DirectSum.lof F ℤ (czFib V) (-1) (czFibMinus V m))
      rw [czX_lof]
      exact czLof_congr V (by norm_num) _ _
        (czXAmb_wall V (by norm_num) (by norm_num) rfl m).symm
  | 1, m => by
      refine Subtype.ext ?_
      show DirectSum.lof F ℤ (czFib V) (-1)
            (czFibMinus V (czEdgeB V m))
          = czY V (DirectSum.lof F ℤ (czFib V) 1 (czFibPlus V m))
      rw [czY_lof]
      exact czLof_congr V (by norm_num) _ _
        (czYAmb_wall V (by norm_num) (by norm_num) rfl m).symm

end E10S

/-- `Rep.Hom`'s `rational` field, read at a NAMED target vertex, for the split cyclic quiver.
@census none (helper; engine `E10`) -/
theorem czS_rational_of_phi' {M N : RationalQuiver.Rep (cyclicSplit F)}
    (psi : ∀ v : (cyclicSplit F).V, M.M v →ₗ[F] N.M v)
    {σ : Gal(F/F)} {v w : (cyclicSplit F).V} (hvw : σ • v = w)
    (m : M.M v) (H : psi w (M.φ' σ hvw m) = N.φ' σ hvw (psi v m)) :
    psi (σ • v) (M.φ σ v m) = N.φ σ v (psi v m) := by
  subst hvw; exact H

/-- A `Rep.Hom` with invertible vertex components has an inverse, for the split cyclic quiver.
@census none (helper; engine `E10`) -/
def czRepHomInv {M N : RationalQuiver.Rep (cyclicSplit F)}
    (f : RationalQuiver.Rep.Hom M N)
    (g : ∀ v : (cyclicSplit F).V, N.M v →ₗ[F] M.M v)
    (hgf : ∀ v x, g v (f.ψ v x) = x) (hfg : ∀ v y, f.ψ v (g v y) = y) :
    RationalQuiver.Rep.Hom N M where
  ψ := g
  edge e m := by
    have h := f.edge e (g _ m)
    rw [hfg] at h
    rw [← h, hgf]
  rational σ v m := by
    have h := f.rational σ v (g v m)
    rw [hfg] at h
    rw [← h, hgf]

section E10S2

variable (V : (RationalQuiver.RepNil (cyclicSplit F)).FullSubcategory)

set_option maxSynthPendingDepth 4
set_option synthInstance.maxHeartbeats 400000

/-- **The comparison map as a morphism of representations** `V → 𝔼_{ℚ[√-1]}(M)`.
@census none (helper; engine `E10`) -/
noncomputable def czNatHom :
    RationalQuiver.Rep.Hom V.obj.toRep (E_CycSplit_rep (czHCQiObj V)) where
  ψ v := czEmb V v
  edge e m := czEmb_edge V e m
  rational σ v m := by
    have hσ : σ = 1 := galSelf_eq_one σ
    subst hσ
    refine czS_rational_of_phi' (M := V.obj.toRep) (N := E_CycSplit_rep (czHCQiObj V))
      (fun u => czEmb V u) (one_smul _ v) m ?_
    rw [RationalQuiver.Rep.φ'_one, RationalQuiver.Rep.φ'_one]
    exact RationalQuiver.Rep.eqCast_natural (M := V.obj.toRep)
      (N := E_CycSplit_rep (czHCQiObj V)) (fun u => czEmb V u) _ m

/-- The inverse morphism.  @census none (helper; engine `E10`) -/
noncomputable def czNatHomInv :
    RationalQuiver.Rep.Hom (E_CycSplit_rep (czHCQiObj V)) V.obj.toRep :=
  czRepHomInv (czNatHom V) (fun v => (czEmbEquiv V v).symm.toLinearMap)
    (fun v x => (czEmbEquiv V v).symm_apply_apply x)
    (fun v y => (czEmbEquiv V v).apply_symm_apply y)

/-- **`𝔼_{ℚ[√-1]}(M) ≅ V`** for the split cyclic quiver.  @census none (helper; engine `E10`) -/
noncomputable def czNatIsoFD : (E_CycSplit_obj (czHCQiObj V)).obj ≅ V.obj where
  hom := czNatHomInv V
  inv := czNatHom V
  hom_inv_id := RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun x =>
    (czEmbEquiv V v).apply_symm_apply x)
  inv_hom_id := RationalQuiver.Rep.Hom.ext (funext fun v => LinearMap.ext fun y =>
    (czEmbEquiv V v).symm_apply_apply y)

end E10S2

/-- **Essential surjectivity of the split `ℓ = 0` functor** — engine `E10` over `ℚ[√-1]`.
@census none (helper; engine `E10`) -/
theorem E_CycSplit_essSurj : (E_CycSplitFunctor (F := F)).EssSurj where
  mem_essImage W :=
    ⟨czHCQiObj W, ⟨ObjectProperty.isoMk (RationalQuiver.RepNil (cyclicSplit F))
      (czNatIsoFD W)⟩⟩

/-- **`E_E_equivalence_cyclic`'s split conjunct, proved** (2026-10-02, R-PROC-4 amendment on
author decision A-3): `ℓ = 0`, split, over `E = ℚ[√-1]`.  `hcLambdaFEquiv F 0` followed by the
split `ℓ = 0` functor, which is full (`E9`), faithful (`E1`) and essentially surjective (`E10`).

@census none (the `ℓ = 0` split half of `RQ-5.08-C2`; cited by `E_E_equivalence_cyclic`) -/
theorem E_E_cyclic_split_equivalence :
    Nonempty (HCLambda 0 F ≌
      (RationalQuiver.RepNil (cyclicSplit F)).FullSubcategory) := by
  haveI := E_CycSplit_full (F := F)
  haveI := E_CycSplit_faithful (F := F)
  haveI := E_CycSplit_essSurj (F := F)
  haveI : (E_CycSplitFunctor (F := F)).IsEquivalence := { }
  exact ⟨(hcLambdaFEquiv F 0).trans (E_CycSplitFunctor (F := F)).asEquivalence⟩

end CycSplit


end RationalQuivers.Gelfand.Split
